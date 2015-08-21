(* load "StringCvt"; load "Int"; load "String"; load "Binarymap";
load "Listsort";
load "TextIO";  *)
open TextIO;


fun tokenise s = String.tokens (fn c => c = #"," orelse c = #"\n"
    orelse c = #"\"") s;

fun pref xs = List.nth (xs, 2);
fun candCode xs = (List.nth (xs, 3), List.nth (xs, 4));
fun pairOrder ((a,b), (c,d)) = case Int.compare (a, c) of
    EQUAL => Int.compare (b,d) | x => x;

fun parseLine (continue, currentBallot, ballots, candMap, numCands, inFile) =
  let 
    val lineStr = case (inputLine inFile) of SOME s => s | NONE => raise input_error
    (*val _ = print lineStr*)
  in
    if lineStr = "" orelse lineStr = "\n"
    then
        (false, [], (rev currentBallot)::ballots, candMap, numCands, inFile)
    else
      let
        val line = List.map (valOf o Int.fromString) (tokenise lineStr);
        val candNumO = Binarymap.peek (candMap, candCode line)
        val candNum = case candNumO of
            NONE   => numCands | 
            SOME x => x
        val newCandMap = case candNumO of
            NONE   => Binarymap.insert 
                        (candMap, candCode line, numCands) |
            SOME _ => candMap
        val newNumCands = case candNumO of
            NONE   => numCands + 1 |
            SOME _ => numCands
        val newBallots = if pref line = 1 andalso not (currentBallot = [])
            then (rev currentBallot)::ballots
            else ballots
        val newCurrentBallot = if pref line = 1
            then [candNum]
            else candNum::currentBallot
      in
        (true, newCurrentBallot, newBallots, newCandMap, newNumCands, inFile)
      end
  end;


fun parseFile filename =
  let
    val _ = if !verbose then 
        print ("Loading file " ^ filename ^ 
            "\nThis may take some time...\n") else ()
    val inFile = openIn filename
    val _ = inputLine inFile     (* headers *)
    fun holWhile P g x = if P x then holWhile P g (g x) else x
    val (_,_,ballots, candMap, numCands,_) = holWhile (fn x => #1 x) 
        parseLine (true, [], [], Binarymap.mkDict pairOrder, 0, inFile)
  in
    (ballots, candMap, numCands)
  end;

fun parseFileDict dict filename =
  let
    val _ = if !verbose then 
        print ("Loading file " ^ filename ^ 
            "\nThis may take some time...\n") else ()
    val inFile = openIn filename
    val _ = inputLine inFile     (* headers *)
    fun holWhile P g x = if P x then holWhile P g (g x) else x
    val (_,_,ballots, candMap, numCands,_) = holWhile (fn x => #1 x) 
        parseLine (true, [], [], dict, Binarymap.numItems dict, inFile)
  in
    (ballots, candMap, numCands)
  end;

fun parseBallots dict filename =
    let val (ballots,_,_) = parseFileDict dict filename in ballots end

fun parseCandidateLine (continue, candBri, candGin, candMol, inFile) =
  let
    val lineStr = case (inputLine inFile) of SOME s => s | NONE => raise input_error
  in
    if lineStr = "" orelse lineStr = "\n"
    then
        (false, candBri, candGin, candMol, inFile)
    else
      let
        val strs = tokenise lineStr
        (* val _ = List.app (fn s => print (s ^ "\n")) strs *)
        val (ecodeStr,pcodeStr,ccodeStr,lname,fname) = case strs of
            [a,b,c,d,e] => (a,b,c,d,e) | _ => raise input_error
        val ecode = valOf (Int.fromString ecodeStr)
        val candId = (valOf (Int.fromString pcodeStr), 
                      valOf (Int.fromString ccodeStr))
        val name = lname ^ "," ^ fname
        val newCandBri = case ecode of
            1 => Binarymap.insert(candBri, candId, name) |
            x => candBri
        val newCandGin = case ecode of
            2 => Binarymap.insert(candGin, candId, name) |
            x => candGin
        val newCandMol = case ecode of
            3 => Binarymap.insert(candMol, candId, name) |
            x => candMol
      in
        (true, newCandBri, newCandGin, newCandMol, inFile)
      end
  end;

fun parseCandidates filename =
  let
    val inFile = openIn filename
    val _ = inputLine inFile     (* headers *)
    fun holWhile P g x = if P x then holWhile P g (g x) else x
    val (_,candBri, candGin, candMol,_) = holWhile (fn x => #1 x) 
        parseCandidateLine (true, Binarymap.mkDict pairOrder, 
        Binarymap.mkDict pairOrder, Binarymap.mkDict pairOrder, inFile)
  in
    (candBri, candGin, candMol)
  end;

val candBriOrd = 
  let val listing = 
    [(0,4), (0,0), (0,1), (0,3), (0,2), (1,0), (1,1), (2,1), (2,0), (2,4),
     (2,3), (2,2), (3,0), (3,1), (4,4), (4,1), (4,0), (4,3), (4,2)]
    val (dict, _) = List.foldl 
        (fn (x, (dict, n)) => (Binarymap.insert(dict, x, n), n+1)) 
        ((Binarymap.mkDict pairOrder, 0)) listing
  in
    dict
  end;

val candGinOrd = 
  let val listing = 
    [(0,2), (0,4), (0,1), (0,0), (0,3), (1,0), (1,3), (1,4), (1,2), (1,1),
     (2,0), (2,1), (2,2), (3,0), (3,1), (4,2), (4,3), (4,4), (4,1), (4,0),
     (5,1), (5,3), (5,0), (5,2), (6,2), (6,1), (6,0)]
    val (dict, _) = List.foldl 
        (fn (x, (dict, n)) => (Binarymap.insert(dict, x, n), n+1)) 
        ((Binarymap.mkDict pairOrder, 0)) listing
  in
    dict
  end;

val candMolOrd = 
  let val listing = 
    [(0,1), (0,2), (0,0), (1,2), (1,5), (1,6), (1,4), (1,3), (1,0), (1,1),
     (2,1), (2,3), (2,0), (2,2), (3,0), (3,1), (3,2), (4,4), (4,6), (4,5),
     (4,1), (4,3), (4,0), (4,2), (5,0), (5,1), (6,1), (6,2), (6,0), (7,0),
     (7,6), (7,3), (7,5), (7,4), (7,2), (7,1), (8,2), (8,3), (8,1), (8,0)]
    val (dict, _) = List.foldl 
        (fn (x, (dict, n)) => (Binarymap.insert(dict, x, n), n+1)) 
        ((Binarymap.mkDict pairOrder, 0)) listing
  in
    dict
  end;


fun zipCandMap mapa mapb =
    Listsort.sort (fn ((a,b),(c,d)) => Int.compare (a, c))
        (List.map (fn (a,b) => (b, Binarymap.find(mapa, a))) 
            (Binarymap.listItems mapb));









