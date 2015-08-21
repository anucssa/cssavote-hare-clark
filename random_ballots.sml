(*load "Random"; load "Time"; load "Timer"; *)
fun makeBallot gen numCandidates =
let
    fun stripRepeats [] ys = ys |
    stripRepeats (x::xs) ys = 
        if List.exists (fn a => a=x) ys then stripRepeats xs ys 
        else stripRepeats xs (x::ys)
in
    stripRepeats (Random.rangelist (0, numCandidates) 
        (numCandidates, gen)) []
end;

fun makeBallot2 gen numCandidates =
let
    fun makeSource x xs = if x < numCandidates 
        then makeSource (x+1) (x::xs) else xs
    val init_source = makeSource 0 []
    exception subscript
    fun set 0 (x::xs) y = y::xs |
        set n (x::xs) y = x::(set (n-1) xs y) |
        set n [] y = raise subscript
    fun get n xs = List.nth (xs, n)
    fun doSwitch a a_length (s::source) = 
          let val j = Random.range (0, a_length + 1) gen 
              val j2 = a_length - j - 1 in
          if j = a_length then doSwitch (s::a) (a_length + 1) source
          else doSwitch (set (j2 + 1) ((get j2 a)::a) s) 
            (a_length + 1) source end |
        doSwitch a a_length [] = a
    val full_ballot = doSwitch [] 0 init_source
    in
    List.take (full_ballot, Random.range(1, numCandidates+1) gen)
end;


fun makeRandomBallots gen numCandidates numBallots =
    if numBallots <= 0 then [] else
        (makeBallot2 gen numCandidates)
        ::(makeRandomBallots gen numCandidates (numBallots - 1))

fun timeCount rballots numToElect =
    let val startTime = Timer.startRealTimer()
    val sh as (s, h) 
        = hareClarkCountImpIO (rballots, numToElect, Intset.empty);
    (* val _ = print (intsetToString (winnersImp s)) *)
    val halfTime = Time.toString (Timer.checkRealTimer startTime)
    val _ = printVotesTable sh ""
    val _ = printBallotsTable sh ""
in
    (halfTime, Time.toString (Timer.checkRealTimer startTime))
end;

fun timeTables sh =
    let val startTime = Timer.startRealTimer()
    val _ = printBallotsTable sh ""
    val ballotsTime = Timer.checkRealTimer startTime
    val _ = printVotesTable sh ""
    val votesTime =  Time.- (Timer.checkRealTimer startTime, ballotsTime)
in
    List.map Time.toString [ballotsTime, votesTime]
end;

