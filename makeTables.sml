(* use "EA_implementation_sml.sml";

(* creating the scrutineer tables *)
load "Binarymap"; load "Msp"; *)
open Msp;
open EA_implementation_sml;


val ballot_table_filename = "ballotTable.html";
val votes_table_filename = "votesTable.html";

val blank = td ($ "&nbsp;");

fun intString 0 = "&nbsp;"
    | intString x = if x < 0 then "-" ^ (intString (~x))
                    else Int.toString x;

fun int_td x = tda "align=right" ($ (intString x));
fun cand_td x = tda "width=30 align=right" ($ (Int.toString x));

fun surplus (newState : stateImp) (lastState : stateImp) =
    listItems (difference 
        (#done_successes newState, #done_successes lastState));

fun excluded (newState : stateImp) (lastState : stateImp) =
    listItems (difference(#excluded newState, #excluded lastState));

fun updateExcluded newState lastStateO lastEx =
  case lastStateO of 
    NONE => lastEx |
    SOME lastState => case excluded newState lastState of
      [] => lastEx |
      (x::xs) => SOME x;

fun comment (newState : stateImp) (lastStateO : stateImp option) lastEx =
  case lastStateO of
    NONE => "First preferences" |
    SOME lastState =>
      let
        val newSurplus = surplus newState lastState
        val newEx = excluded newState lastState
      in
        if not (null newSurplus) then
          "Distributing surplus for " ^ (Int.toString (hd newSurplus)) ^ "\n"
        else if not (null newEx) then
          "Excluding candidate " ^ (Int.toString (hd newEx)) ^ "\n"
        else
          "Still excluding candidate " ^ (Int.toString (valOf lastEx)) ^ "\n"
      end;

fun getNumExhausted newState lastStateO =
  case lastStateO of
    NONE => length (#set_aside newState) |
    SOME lastState =>
      let val newSurplus = surplus newState lastState in
      if not (null newSurplus)
      then 
        let val ignores = ignoredCandidatesImp lastState
        val {latest_votes, ...} = 
            retrieve(#vote_pile lastState, hd newSurplus)
        in
        length (List.filter (fn b => tbpIsFor ignores b = NONE) 
            latest_votes)
        end
      else length(#set_aside newState) - length(#set_aside lastState)
      end;

fun changed (lastStateO : stateImp option) c cinfo = case lastStateO of 
    NONE => true |
    SOME {vote_pile=lastVotes, ...} => 
        (case peek(lastVotes, c) of
        NONE => true | 
        SOME last_cinfo => not (cinfo = last_cinfo));

(* ignores order like the plague *)
fun listDiff xs ys = 
    let fun listDiffTail [] ys1 ys2 zs = zs |
    listDiffTail (x::xs) [] ys2 zs = listDiffTail xs ys2 [] (x::zs) |
    listDiffTail (x::xs) (y::ys1) ys2 zs = if x = y 
        then listDiffTail xs (ys1 @ ys2) [] zs
        else listDiffTail (x::xs) ys1 (y::ys2) zs
    in
    listDiffTail xs ys [] []
    end;

fun getTV newState lastStateO =
    let val tv = List.foldl 
        (fn (c, tv) => case peek(#vote_pile newState, c) of 
            NONE => tv | 
            SOME cinfo =>
              let 
                val cChanged = changed lastStateO c cinfo 
                val len = length (#latest_votes cinfo)
              in
                if not cChanged orelse len = 0 then tv else
                #2 (hd (#latest_votes cinfo)) 
              end)
        (0,1) (listItems (allCandidatesImp newState))
    in
    if less_f (0,1) tv then tv else #2 (hd (#set_aside newState))
    end;

fun getNumLatest newState lastStateO = 
    rev (List.foldl 
        (fn (c, xs) => case peek(#vote_pile newState, c) of 
            NONE => 0::xs | 
            SOME cinfo =>
              let 
                val cChanged = changed lastStateO c cinfo in
                if not cChanged then 0::xs else
                (length (#latest_votes cinfo))::xs end)
        [] (listItems (allCandidatesImp newState)));

fun getLastEx [x,y] = x | getLastEx (x::xs) = getLastEx xs |
    getLastEx [] = 0;

fun addVotes all_cands votemap tv ns = 
    let fun put ((c, n), map) =
    case Binarymap.peek(map, (c, tv)) of
        NONE => Binarymap.insert(map, (c,tv), n) |
        SOME x => Binarymap.insert(map, (c,tv), x + n)
    in
    List.foldl put votemap (ListPair.zip (listItems all_cands, ns))
end;

(* lastVotes is votes & exhausted & loss by fraction *)
fun makeRowVotes (newState as {set_aside, ...}, 
        (countId, lastVotesO, lastStateO, lastEx, lastExCount, votemap, 
         previousRows)) =
let
    val all_cands = allCandidatesImp newState
    val newEx = updateExcluded newState lastStateO lastEx
    val commentCell = tda "nowrap, valign=bottom" 
        ($ (comment newState lastStateO lastEx))
in
    case lastVotesO of 
    NONE =>
        (* First Preferences *)
      let 
        val voteCounts = List.map (candidateVotesImp newState) 
            (listItems all_cands)
        val numExhausted = length set_aside
        val lossByFraction = 0
        val newVotes = voteCounts @ [numExhausted, lossByFraction]
        val newVoteCells = prmap int_td newVotes 
        val thisRow = tra "valign=baseline" 
            (&& (&& (&& (int_td countId, newVoteCells), blank), commentCell))
        val newMap = addVotes all_cands votemap (1,1) voteCounts
      in
        ( countId + 1
        , SOME newVotes
        , SOME newState
        , newEx
        , lastExCount
        , newMap
        , && (previousRows, thisRow))
      end |
    SOME lastVotes =>
      let 
        val lastState = valOf lastStateO
        val tv = getTV newState lastStateO
        fun candVotes newS lastS c = if member(#done_successes newS, c) 
            then #quota newS
            else if null (surplus newS lastS) andalso c = valOf newEx
              then (* excluding c *)
                if null (excluded newS lastS) then
                  lastExCount - (Binarymap.find(votemap, (c, tv)))
                else candidateVotesImp lastS c - 
                  (Binarymap.find(votemap, (c, tv)))
              else candidateVotesImp newS c
        val voteCounts = List.map (candVotes newState lastState) 
            (listItems all_cands)
        val newExhausted = if surplus newState lastState = [] then
            floor_f (mult_f_int tv 
                (length set_aside - length (#set_aside lastState)))
            (*floor (real (length set_aside - length (#set_aside lastState)) 
                * tv)*)
            else 0
        val numExhausted = getLastEx lastVotes + newExhausted
        val total = List.foldl op+ 0 lastVotes
        val subTotal = List.foldl op+ 0 voteCounts + numExhausted
        val lossByFraction = total - subTotal
        val newVotes = voteCounts @ [numExhausted, lossByFraction]
        val diffs = ListPair.map op- (newVotes, lastVotes)
        fun pair_td (a,b) = 
            tda "align=right" (&& (&& ($ (intString a), br), $ (intString b)))
        val cells = prmap pair_td (ListPair.zip (lastVotes, diffs))
        val thisRow = tra "align=bottom" 
            (&& (&& (&& (int_td countId, cells), int_td total), commentCell))
        val extraVotes = List.take(diffs, numItems all_cands)
        val newMap = addVotes all_cands votemap tv extraVotes
        val newExCount = case newEx of NONE => lastExCount |
            SOME ex => candVotes newState lastState ex
      in
        ( countId + 1
        , SOME newVotes
        , SOME newState
        , newEx
        , newExCount
        , newMap
        , && (previousRows, thisRow))
      end
end;

fun makeRowBallots (newState, 
        (countId, lastStateO : stateImp option, lastEx, previousRows)) =
  let
    val all_cands = allCandidatesImp newState
    val numLatest = getNumLatest newState lastStateO
    val tv = getTV newState lastStateO
    val numExhausted = getNumExhausted newState lastStateO
    val total = List.foldl op+ 0 numLatest + numExhausted
    val numRow = [countId] @ numLatest @ [numExhausted, total] 
    val htmlRow = tr ( && (&& (prmap int_td numRow, 
        tda "align=right" ($ (f_toString tv))), 
        tda "nowrap" ($ (comment newState lastStateO lastEx)) ))
    val newEx = updateExcluded newState lastStateO lastEx
  in
    (countId + 1, SOME newState, newEx, && (previousRows, htmlRow))
  end;


fun printVotesTable (s, h) filePrefix =
let
    val _ = if !verbose then print "Making votes table...\n" else ()
    val all_cands = listItems (allCandidatesImp s)
    val candCells = prmap cand_td all_cands
    val firstRow = tr (List.foldr && Empty 
        [td ($ "Count"), candCells, td ($ "Votes Exhausted"),
        td ($ "Loss By Fraction"), td ($ "Total"), td ($ "Comments")])
    val inOrder = rev (s::h)
    fun ord ((c1, tv1), (c2, tv2)) : order = case Int.compare (c1, c2) of
        EQUAL => compare_f (tv1, tv2) |
        x => x
    val (_,finalVotesO,_,_,_,_,votesTableRows) = 
        List.foldl makeRowVotes 
        (1, NONE, NONE, NONE, 0, Binarymap.mkDict ord, firstRow) inOrder
    val finalVotes = valOf finalVotesO
    val finalTotal = List.foldl op+ 0 finalVotes
    val finalRow = 
        tr (&& (&& (&& (blank, prmap int_td finalVotes), int_td finalTotal),
            blank))
    val votesTableAllRows = && (votesTableRows, finalRow)
    val votesTable = tablea "border" votesTableAllRows
    val details = && ($ ("Quota = " ^ (Int.toString (#quota s)) ^
        ", Number of vacancies = " ^ (Int.toString (#num_to_elect s))), Nl)
    val title = $ "<H1><CENTER>Table 2 - Votes</CENTER></H1>"
    val votesHtml = htmldoc ($ "Table 2 - Votes")
        (&& (title, && (details, votesTable))) 
    
    val votesFile = openOut (filePrefix ^ votes_table_filename)
    val _ = output (votesFile, flatten votesHtml)
    val _ = flushOut votesFile
    val _ = closeOut votesFile
in
    ()
end;

fun printBallotsTable (s, h) filePrefix =
let
    val _ = if !verbose then print "Making ballots table...\n" else ()
    val all_cands = listItems (allCandidatesImp s)
    val candCells = prmap cand_td all_cands
    val firstRow = tr (List.foldr && Empty 
        [td ($ "Count"), candCells, td ($ "Papers Exhausted"),
        td ($ "Total"), td ($ "Transfer Value"), td ($ "Comments")])
    val inOrder = rev (s::h)
    val (_,_,_,ballotTableRows) = 
        List.foldl makeRowBallots (1, NONE, NONE, firstRow) inOrder
    val ballotsTable = tablea "border" ballotTableRows
    val details = && ($ ("Quota = " ^ (Int.toString (#quota s)) ^
        ", Number of vacancies = " ^ (Int.toString (#num_to_elect s))), Nl)
    val title = $ "<H1><CENTER>Table 1 - Ballot Papers</CENTER></H1>"
    val ballotsHtml = htmldoc ($ "Table 1 - Ballot Papers")
        (&& (title, && (details, ballotsTable))) 
    
    val ballotsFile = openOut (filePrefix ^ ballot_table_filename)
    val _ = output (ballotsFile, flatten ballotsHtml)
    val _ = flushOut ballotsFile
    val _ = closeOut ballotsFile
in
    ()
end;


