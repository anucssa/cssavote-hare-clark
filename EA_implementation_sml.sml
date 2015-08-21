(***************************************************************

An implementation of Schedule 4, ACT Electoral Act 1992
written by Teresa Bradbury
    Version 1.0, January 2013

Implements "A HOL model of the Hare-Clark voting system"
    by Michael Norish
    Version 2.04, 10 May 2005
    http://users.cecs.anu.edu.au/~rpg/EVoting/evote_formalisation.html

Unless otherwise stated, the function 'nameImp' implements the
    function 'name' from the specification. For comments on the
    purpose of these functions, see the specification above.

Everything matches as closely as possible except:
    * all_candidates is a field of the state for efficiency reasons.
    * transfer values are rationals rather than reals to aid in the
        production of the preference tables.
    * IO versions of all the functions that may require a tiebreak
        by commissioner's lot have been added. These either ask
        for a selection from the user or choose the lowest numbered
        candidate depending on the value of 'allow_prompt'.
    * clause 9 required a major overhaul due to bugs in the spec. 

****************************************************************)

structure EA_implementation_sml = struct

open Intmap; open Intset; open TextIO;

(* Print verbose output. Changed by the command line options. *)
val verbose = ref false;
(* Allow prompts when there are ties for which surplus to distribute or
 *  candidate to exclude. Changed by the command line options. *)
val allow_prompt = ref false;

(* Various functions for formatting output *)
fun intsetToString set = if Intset.isEmpty set then "none" else 
    Intset.foldl (fn (x, s) => 
    s ^ (Int.toString x) ^ " ") "" set;

fun printList xs = 
    let
    fun printListA [] = print "]\n" |
        printListA [x] = print (Int.toString x ^ "]\n") |
        printListA (x::xs) = let val _ = print (Int.toString x ^ ",") in
            printListA xs end
    val _ = print "["
    in
    printListA xs
end;

fun surplusChoicePrompt cand_set = 
    "\nPlease select the relevant candidate from the " ^
    "following list:\n  (in accordance with clause 7(3)(c)(ii))\n\n" ^
    (intsetToString cand_set) ^ "\n\n";
fun toExcludePrompt cand_set =
    "\nPlease select the candidate to exclude from the " ^
    "following list:\n  (in accordance with clause b(2)(b))\n\n" ^
    (intsetToString cand_set) ^ "\n\n";



(****************************************************************)
(* Type definitions *)

type fracImp = int * int;

type candidateImp = int;
type ballotImp = candidateImp list;
type tbpImp = ballotImp * fracImp;

type cinfoImp = {
    count : int, 
    old_votes : tbpImp list, 
    latest_votes : tbpImp list};

type votePileImp = cinfoImp intmap;

type stateImp = {
    vote_pile : votePileImp,
    set_aside : tbpImp list,
    dead : intset,
    excluded : intset,
    done_successes : intset,
    quota : int,
    num_to_elect : int,
    all_candidates : intset};

type fullstateImp = stateImp * stateImp list;

exception partition_is_broken; (* should never happen *)
exception input_error; (* if user types something dumb *)


(****************************************************************)
(* Helper functions *)

(* functions for manipulating rational numbers *)
fun mult_f_int (a, b) n = (a*n, b);
fun real_f (a, b) = real a / (real b);
fun floor_f x = floor (real_f x);
fun less_f x y = Real.< (real_f x, real_f y);
fun compare_f (x, y) = Real.compare (real_f x, real_f y);
fun canonical (a, b) = 
  let fun gcd (0, y) = y |
        gcd (x, 0) = x |
        gcd (x, y) = if y <= x then gcd (x - y, y) else gcd (x, y - x)
    val g = gcd (a, b)
  in 
    (a div g, b div g)
end;
fun eq_f x y = canonical x = canonical y;
fun f_toString (a, b) = if b = 1 then Int.toString a 
    else Int.toString a ^ " / " ^ Int.toString b;

(* Implements the HOL term ``{x | x IN s /\ f x}`` *)
fun setFilter f set = Intset.foldl (fn (i, soFar) => if f i 
    then add(soFar, i) else soFar) Intset.empty set;

(* Implements ballot_is_for as a function rather than a relation *)
fun tbpIsFor ignore (([], tv) : tbpImp) = NONE
    | tbpIsFor ignore ((x::xs), tv) 
        = if member(ignore, x) then tbpIsFor ignore (xs,tv) else SOME x;

(* Implements tbp_bag_candidates *)
fun tbpListCandidates ((ballot, tv)::tbps : tbpImp list) : intset =
    addList (tbpListCandidates tbps, ballot) |
    tbpListCandidates [] = empty;

(* Implements cinfo_votebag *)
fun allcinfoVotes (ci : cinfoImp) =
        (#old_votes ci) @ (#latest_votes ci);

fun cinfoCandidatesImp cinfo = tbpListCandidates (allcinfoVotes cinfo);

fun pileCandidatesImp (vote_pile : votePileImp) =
    Intmap.foldl (fn (candidate, cinfo, setSoFar) => 
        union(setSoFar, cinfoCandidatesImp cinfo)) empty vote_pile;

(****************************************************************)
(* transfer_bundle *)

(* my_foldl matches the parameter order of ``ITBAG`` *)
fun my_foldl f [] initial = initial |
    my_foldl f (x::xs) initial = my_foldl f xs (f x initial); 

fun list_partition eq xs =
let
    fun partition_insert x [] = [[x]] |
    partition_insert x ((y::ys)::partitions) = if eq x y then
        (x::y::ys)::partitions else (y::ys)::partition_insert x partitions
    (* partitions should never contain an empty list *)
    | partition_insert x ([]::partitions) = raise partition_is_broken
in
    my_foldl partition_insert xs []
end;

(* Assumes all tbp in group have same transfer value 
 *  and next candidate *)
fun transfer_group (ballotFor : tbpImp -> candidateImp) 
    group (pile : votePileImp) =
let
    val (b,tv) = hd group
    val b_is_for = ballotFor (b, tv)
    val count = floor_f (mult_f_int tv (length group))
    (* val (count : int) = Real.floor(tv * real(length group)) *)
    val old_cinfo = peek (pile, b_is_for)
    val (old_count : int, old_old_votes, old_latest_votes) =
        case old_cinfo of NONE => (0, [], [])
        | SOME {count=n, old_votes=old, latest_votes=latest}
            => (n, old, latest)
    val all_old_votes = old_old_votes @ old_latest_votes
in
    insert (pile, b_is_for, {count = old_count + count,
        old_votes=all_old_votes, latest_votes = group})
end;

(* Assumes all tbp in bundle have same transfer value 
 *  and every ballot has a next candidate *)
fun transferBundleImp (bundle : tbpImp list) 
    (ballotFor : tbpImp -> candidateImp)
    (pile : votePileImp) = 
let
    fun ballotForEq (b1 : tbpImp) (b2 : tbpImp) 
        = (ballotFor b1 = ballotFor b2)
    val grouped_votes = list_partition ballotForEq bundle
in
    my_foldl (transfer_group ballotFor) grouped_votes pile
end;

(****************************************************************)
(* functions on the state *)

(* for efficiency purposes, all_candidates is a field of stateImp now.
 *  This is the definition according to the specification. *)
fun allCandidatesImpOld
    ({dead=dead, excluded=excluded, vote_pile=vote_pile,
      done_successes=done_successes, 
      set_aside=set_aside, ...} : stateImp) : intset =
    union ( union ( union ( union (
        pileCandidatesImp vote_pile, tbpListCandidates set_aside),
        dead), excluded), done_successes);

fun allCandidatesImp ({all_candidates, ...} : stateImp) =
    all_candidates;

fun candidateVotesImp (state : stateImp) candidate = 
let
    val cinfo_option = peek((#vote_pile state), candidate)
in
    case cinfo_option of NONE => 0 | SOME cinfo => #count cinfo
end;

fun successfulCandidatesImp
    (state as {done_successes=done, quota=quota, ...} : stateImp) : intset =
    let val candWithSurplus = setFilter (fn c => 
        quota <= candidateVotesImp state c) (allCandidatesImp state) in
    union(done, candWithSurplus)
end; 
    
fun ignoredCandidatesImp 
    (state as {dead=dead, excluded=excluded,...} : stateImp) : intset =
    union( union (dead, excluded), successfulCandidatesImp state);

fun continuingCandidatesImp (state : stateImp) : intset =
    difference(allCandidatesImp state, ignoredCandidatesImp state);

(****************************************************************)
(* The Algorithm *)

(****************************************************************)
(* CLAUSE 3 - primary votes *)

fun c3AddToPileImp dead ballot (fm : tbpImp list intmap) =
let
    val c = List.hd (List.filter (fn c => not (member(dead, c)))
        ballot);
    val oldVotes = case peek(fm,c) of SOME v => v | NONE => [];
in
    insert(fm, c, ((ballot, (1,1))::oldVotes))
end;

fun c3BuildPileImp dead ballots =
    my_foldl (c3AddToPileImp dead) ballots 
        (Intmap.empty() : tbpImp list intmap);

fun clause3Imp (ballots : ballotImp list, num_to_elect : int, 
        dead : intset) : fullstateImp =
let
    val _ = if !verbose then 
        print "Creating first preferences\n" else ()
    val initial_fm = c3BuildPileImp dead ballots;
    fun transform_f ballots : cinfoImp = 
        {count = length ballots, old_votes = [], 
        latest_votes = ballots}
    val vote_pile = transform transform_f initial_fm
    val init_s = 
        {vote_pile = vote_pile,
         set_aside = [],
         dead = dead,
         excluded = Intset.empty,
         done_successes = Intset.empty,
         num_to_elect = num_to_elect,
         quota = floor (real(length(ballots)) / 
            real(num_to_elect + 1)) + 1,
         all_candidates = union (pileCandidatesImp vote_pile, dead)
        }
    val _ = if !verbose then
        print ("Quota is: " ^ Int.toString(#quota init_s) ^ "\n") else ()
    val _ = if !verbose then 
        print ("Successful Candidates: " ^ 
        intsetToString (successfulCandidatesImp init_s) ^ "\n") else ()
in
    (init_s, [])
end;

(****************************************************************)
(* CLAUSE 4 - finished counting? *)

fun clause4ImpOld (s as {num_to_elect = n, quota=quota, ...} : stateImp) 
        : bool =
    let val successes = successfulCandidatesImp s in
    numItems successes = n orelse
    (numItems (continuingCandidatesImp s) + numItems successes = n andalso
    Intset.find (fn c => quota < candidateVotesImp s c) 
    successes = NONE)
end;

fun clause4Imp (s : stateImp) =
    numItems (successfulCandidatesImp s) = #num_to_elect s orelse
    (numItems (continuingCandidatesImp s)
        = #num_to_elect s - numItems (successfulCandidatesImp s) andalso
    Intset.find (fn c => #quota s < candidateVotesImp s c) 
        (successfulCandidatesImp s) = NONE);

fun winnersImp (s as {num_to_elect=n, ...} : stateImp) : intset =
    let val successes = successfulCandidatesImp s in
    if (numItems successes) = n then successes else
    union(successes, continuingCandidatesImp s)
end;

(****************************************************************)
(* CLAUSE 5 - surplus? *)

(* returns true if there is a candidate with a surplus *)
fun clause5ImpOld (s : stateImp) =
    Intset.find (fn c => #quota s < candidateVotesImp s c) 
    (successfulCandidatesImp s) <> NONE;

fun clause5Imp (s : stateImp) =
    not (isEmpty (setFilter 
        (fn c => #quota s < candidateVotesImp s c) 
        (successfulCandidatesImp s)));

(****************************************************************)
(* CLAUSE 6 - distribute surplus for given candidate *)
  
fun clause6Imp ((s as {vote_pile=vote_pile, quota=quota, ...}, 
        history) : fullstateImp, c : candidateImp) : fullstateImp = 
    let 
    val _ = if !verbose then print ("Distributing surplus for candidate " 
        ^ Int.toString c ^ "...\n") else ()
    val ignores
        = ignoredCandidatesImp s
    val {count=count, latest_votes=latest_votes, old_votes=old_votes}
        = retrieve(vote_pile, c)
    val surplus 
        = count - quota
    val (without_next_candidate, with_next_candidate)
        = List.partition (fn b => tbpIsFor ignores b = NONE) latest_votes
    val to_set_aside 
        = old_votes @ without_next_candidate
    val CP 
        = length with_next_candidate
    val _ = if !verbose then print ("Surplus: " ^ Int.toString surplus ^
        ", CP: " ^ Int.toString CP ^ "\n") else ()
    val _ = if CP = 0 then print 
        ("Trying to distribute surplus but there are no papers from the last "^
        "count with a next available preference.\n") else ()
    val base_tv
        = (surplus, CP)
    fun adjust_tv (b, tv)
        = if less_f tv base_tv then (b, tv) else (b, base_tv)
    val bundle 
        = List.map adjust_tv with_next_candidate
    fun bfor (b, tv) 
        = hd (List.filter (fn c => not (member(ignores, c))) b)
    val new_pile 
        = transferBundleImp bundle bfor vote_pile
    val _ = if !verbose then print ("Distributed surplus for candidate " 
        ^ Int.toString c ^ "\n") else ()
in
    ({done_successes = add(#done_successes s, c),
      set_aside      = #set_aside s @ to_set_aside,
      vote_pile      = #1 (remove(new_pile, c)),
      dead           = #dead s,
      excluded       = #excluded s,
      num_to_elect   = #num_to_elect s,
      quota          = #quota s,
      all_candidates = #all_candidates s}, 
    s::history)
end;

(****************************************************************)
(* CLAUSE 7 - which surplus? *)

fun timeOfSuccessImp c t [] = t |
    timeOfSuccessImp c t (s::ss) = if member(successfulCandidatesImp s, c)
    then timeOfSuccessImp c (t+1) ss else t;

fun maxImage f set : int = 
    Intset.foldl (fn (x,maxSoFar) => Int.max(f x, maxSoFar)) 0 set;

fun injective f set : bool = numItems set = numItems (
    Intset.foldl (fn (x,soFar) => add(soFar, f x)) Intset.empty set);

fun leastTInjective history candSet : int option =
    let fun leastTTail [] candSet acc = NONE |
        leastTTail (s::ss) candSet acc = 
        if injective (candidateVotesImp s) candSet
        then SOME acc else leastTTail ss candSet (acc + 1)
in
    leastTTail history candSet 0
end;

fun clause7SetImp ((s as {vote_pile, quota, ...}, h) : fullstateImp) : intset =
    let val dom_vote_pile = Intmap.foldl (fn (cand,_,soFar) => 
        add(soFar, cand)) Intset.empty vote_pile
    val possibles = setFilter (fn c => quota < candidateVotesImp s c) 
        dom_vote_pile
    val _ = if !verbose then print "Candidates with a surplus: " else ()
    val _ = if !verbose then print (intsetToString possibles ^ "\n")
        else ()
in
    if numItems possibles = 1 then possibles else
    let val maxTime = maxImage (fn c => timeOfSuccessImp c 0 h) possibles
    val earliest = setFilter (fn c => timeOfSuccessImp c 0 h = maxTime) 
        possibles
    val _ = if !verbose then print "Candidates with earliest surplus: " 
        else ()
    val _ = if !verbose then print (intsetToString earliest ^ "\n")
        else ()
in
    if numItems earliest = 1 then earliest (* 3(a) *) else
    let val maxSurplus = maxImage (candidateVotesImp s) earliest
    val greatest_surplus = setFilter 
        (fn c => candidateVotesImp s c = maxSurplus) earliest
    val _ = if !verbose then print "Candidates with maximal surplus: " 
        else ()
    val _ = if !verbose then print (intsetToString greatest_surplus ^ "\n")
        else ()
in
    if numItems greatest_surplus = 1 then greatest_surplus (* 3(b) *) else 
    case leastTInjective h greatest_surplus of SOME t => (* 3(c)(i) *)
        let val s0 = List.nth(h, t)
        val maxSurplus2 = maxImage (candidateVotesImp s0) greatest_surplus
        val result = setFilter (fn c => candidateVotesImp s0 c = maxSurplus2) 
            greatest_surplus
        val _ = if !verbose then print ("Candidate with most votes at last" ^
            " count when candidates had different votes: ") else ()
        val _ = if !verbose then print (intsetToString result ^ "\n") else ()
        in result end
    | NONE => greatest_surplus (* 3(c)(ii) *)
end
end
end;

fun clause7Imp (sh : fullstateImp, c: candidateImp) : candidateImp =
    let val possibles = clause7SetImp sh in
    if numItems possibles = 1 then hd (listItems possibles)
    else c
end;

fun clause7ImpIO (sh : fullstateImp) : candidateImp =
    let val possibles = clause7SetImp sh in
    if numItems possibles = 1 then hd (listItems possibles)
    else 
        if !allow_prompt then let
            val _ = print (surplusChoicePrompt possibles)
          in
            case (TextIO.inputLine TextIO.stdIn) of
              NONE => raise input_error | SOME s => case (Int.fromString s) of
                SOME c => c | NONE => raise input_error 
          end
        else let
            val _ = print 
                "Distributing surplus for default candidate from: "
            val _ = print (intsetToString possibles ^ "\n")
          in
            hd (listItems possibles)
          end
end;



(****************************************************************)
(* CLAUSE 8 - exclude who? *)

fun minImage f set : int = 
    Intset.foldl (fn (x,minSoFar) => Int.min(f x, minSoFar)) (valOf Int.maxInt) set;

fun clause8SetImp ((s : stateImp ,h : stateImp list) : fullstateImp) =
    let val least_votes = minImage (candidateVotesImp s) 
        (continuingCandidatesImp s)
    val with_least : intset = setFilter (fn c => candidateVotesImp s c = 
        least_votes) (continuingCandidatesImp s)
    val _ = if !verbose then print "Candidates with least votes: " else ()
    val _ = if !verbose then print (intsetToString with_least ^ "\n")
        else ()
in
    if numItems with_least = 1 then with_least (* 1 *) else
    case (leastTInjective h with_least) of SOME t => (* 2(a) *)
      let val s0 = List.nth(h, t)
        val least_votes0 = minImage (candidateVotesImp s0) with_least
        val result = setFilter 
            (fn c => candidateVotesImp s0 c = least_votes0) with_least
        val _ = if !verbose then print ("Candidate with least votes at last" ^
            " count when candidates had different votes: ") else ()
        val _ = if !verbose then print (intsetToString result ^ "\n") else ()
      in
         result
      end
    | NONE => with_least (* 2(b) *)
end;

fun clause8Imp (sh : fullstateImp, c : candidateImp) =
    let val possibles = clause8SetImp sh in
    if numItems possibles = 1 then hd (listItems possibles)
    else c
end;

fun clause8ImpIO (sh : fullstateImp) : candidateImp =
    let val possibles = clause8SetImp sh in
    if numItems possibles = 1 then hd (listItems possibles)
    else 
        if !allow_prompt then let
            val _ = print (toExcludePrompt possibles)
        in
            case (TextIO.inputLine TextIO.stdIn) of
              NONE => raise input_error | SOME s => case (Int.fromString s) of
                SOME c => c | NONE => raise input_error 
        end
        else let
            val _ = print "Excluding default candidate from: "
            val _ = print (intsetToString possibles ^ "\n")
        in
            hd (listItems possibles)
        end
end;

(****************************************************************)
(* CLAUSE 9 - exclude given candidate *)

(* Candidates that become successful cannot get more votes at later counts *)
fun clause9Imp ((s as {vote_pile=votes, ...}, h) : fullstateImp, 
        c : candidateImp) = 
  let 
    val _ = if !verbose then print ("Excluding candidate "
        ^ Int.toString c ^ "...\n") else ()
    val {count, old_votes, latest_votes} = retrieve(votes, c)
    val ballots = old_votes @ latest_votes
    fun tveq (b1, tv1) (b2, tv2) = eq_f tv1 tv2
    val tv_groups = list_partition tveq ballots
    fun group_tv gp = #2 (hd gp)
    (* This is the ordering to put the groups in DECREASING order *)
    fun ordering (gp1, gp2) = if group_tv gp1 = group_tv gp2 then EQUAL 
        else if less_f (group_tv gp1) (group_tv gp2) then GREATER else LESS
    val tv_groups_ordered = Listsort.sort ordering tv_groups

    fun do_one_count (gp, (s as {vote_pile, set_aside, dead, excluded, 
        done_successes, quota, num_to_elect, all_candidates}, h)
            : fullstateImp) =
      if clause4Imp s then (s, h) else
      let
        val ignores = add(ignoredCandidatesImp s, c)
        val (to_set_aside, has_next_candidate) = 
            List.partition (fn b => tbpIsFor ignores b = NONE) gp
        fun bfor (b, tv) = hd (List.filter 
            (fn c => not (member (ignores, c))) b)
        val pileTrans = transferBundleImp has_next_candidate bfor vote_pile
        val newVotePile = case peek(pileTrans, c) of
          NONE => pileTrans |
          SOME x => #1 (remove (pileTrans, c))
      in
        ({vote_pile      = newVotePile,
          set_aside      = to_set_aside @ set_aside,
          dead           = dead,
          excluded       = add(excluded, c),
          done_successes = done_successes,
          quota          = quota,
          num_to_elect   = num_to_elect,
          all_candidates = all_candidates}, s::h)
      end
    val (done_s, done_h) = List.foldl do_one_count (s, h) tv_groups_ordered
  in
    (done_s, done_h)
  end;


(****************************************************************)
(* RUN *)

(* HOL specification for running: 

val loop_once_def = Define `
  loop_once ((s, h) : fullstate, defaults) =
    if clause5 s then 
    (* transfer surplus *)
    let candidate_surp = clause7 ((s, h), HD defaults) in
    (clause6 ((s, h), candidate_surp), TL defaults)
    else
    (* excude candidate *)
    let candidate_exc = clause8 ((s, h), HD defaults) in
    (clause9 ((s, h), candidate_exc), TL defaults)`;

val Hare_Clark_count_def = Define `
  Hare_Clark_count (ballot_bag, num_to_elect, dead, 
    commLot : candidate list) : fullstate = 
    let initial_state = clause3 (ballot_bag, num_to_elect, dead) in
    FST (WHILE (\((s,h) : fullstate, comm : candidate list). ~(clause4 s)) 
        loop_once (initial_state, commLot))`;
*)

fun loopOnceImpIO (sh as (s,h) : fullstateImp) =
    let val (new_s, new_h) = 
        if clause5Imp s then
            let val candidate_surplus = clause7ImpIO sh in
            clause6Imp (sh, candidate_surplus) end
        else
            let val candidate_exclude = clause8ImpIO (s,h) in
            clause9Imp (sh, candidate_exclude) end
    val _ = if !verbose then
        print ("Successful Candidates: " ^ 
        intsetToString (successfulCandidatesImp new_s) ^ "\n") else ()
in
    (new_s, new_h)
end;

fun hareClarkCountImpIO (ballots, num_to_elect, dead) =
    let val initial_fullstate = clause3Imp (ballots, num_to_elect, dead)
    fun holWhile P g x = if P x then holWhile P g (g x) else x
    val result = holWhile (fn (s, h) => not (clause4Imp s)) loopOnceImpIO 
        initial_fullstate
    val _ = if !verbose then print ("Winners are: " ^
        intsetToString (winnersImp (#1 result)) ^ "\n") else ()
in
    result
end;

fun runAndGetWinnersIO (ballots, num_to_elect, dead) =
    let val (final_state,_) 
        = hareClarkCountImpIO (ballots, num_to_elect, dead)
in
    listItems (winnersImp final_state)
end;

end;


















