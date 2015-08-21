open TextIO;

exception parse_error;
fun tokenizeBLT s = String.tokens (fn c => c = #" " orelse c = #"\n") s;

fun tokenizeBLTSplit inFile = 
  let fun split tokens ints strs =
    case tokens of
        [] => (rev ints, rev strs) |
        (tok::rest) => case Int.fromString tok : int option of
            NONE => split rest ints (tok::strs) |
            SOME x => split rest (x::ints) strs
  in
    split (tokenizeBLT (inputAll inFile)) [] []
  end;

fun parseDead tokens acc = 
    case tokens of
        (tok::rest) => if tok < 0 then parseDead rest (Intset.add (acc, ~tok)) 
            else (acc, tokens) |
        [] => raise parse_error
        
fun replicate a n =
  let fun replicate2 a n acc =
    case n of
        0 => acc |
        _ => replicate2 a (n - 1) (a::acc)
  in
    replicate2 a n []
  end;

fun parseBLTBallots tokens num ballot ballots =
  case tokens of
    (tok::rest) => (case (num, tok) of
        (NONE, 0) => (ballots, rest) |
        (NONE, _) => parseBLTBallots rest (SOME tok) ballot ballots |
        (SOME n, 0) => parseBLTBallots rest NONE [] (ballots @ (replicate ballot n)) |
        _ => parseBLTBallots rest num (ballot @ [tok]) ballots) |
    [] => raise parse_error
    
fun removeEmpties ballots dead = List.filter
  (fn ballot => List.filter (fn c => not (Intset.member(dead, c))) ballot <> []) ballots
        
fun parseBLTFile filename = 
  let
    val _ = if !verbose then 
        print ("Loading file " ^ filename ^ 
            "\nThis may take some time...\n") else ()
    val inFile = openIn filename
    val (tokens, strTokens) = tokenizeBLTSplit inFile
    val (numCandidates, tokens) = (hd tokens, tl tokens)
    val (numSeats,      tokens) = (hd tokens, tl tokens)
    val (dead,          tokens) = parseDead tokens Intset.empty
    val (ballots,       tokens) = parseBLTBallots tokens NONE [] []
    val finalBallots = removeEmpties ballots dead
    (* TODO: Handle the names *)
  in
    (numCandidates, numSeats, dead, finalBallots)
  end;
  
