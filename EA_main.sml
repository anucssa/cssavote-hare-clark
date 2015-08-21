val pathToBindabella  = "../data/BrindabellaTotal.txt"
val pathToGinninderra = "../data/GinninderraTotal.txt"
val pathToMolonglo    = "../data/MolongloTotal.txt"


val usage = "usage: EA [options]\n" ^
    "-Bri     : count the 2008 Brindabella election\n" ^
    "-Gin     : count the 2008 Ginninderra election\n" ^
    "-Mol     : count the 2008 Molonglo election\n" ^
    "-f file  : count the election represented in file in BLT File Format\n" ^
    "-r c b s : count a randomly generated election with \n" ^
    "             c candidates standing, b ballot papers and s seats\n" ^
    "-s x     : set the seed for the random number generator to x\n" ^
    "-o pre   : filename prefix for the generated tables\n" ^
    "-d c     : mark candidate c as dead (can be used multiple times\n" ^
    "             and candidates are numbered from zero)\n" ^
    "-v       : print verbose output\n" ^
    "-i       : ask for input when there are tie-breaks\n" ^
    "\n"
    
exception argument;
fun parseRandom c b s =
  let 
    val fromString = valOf o Int.fromString
    val rArg as (ci, bi, si) = (fromString c, fromString b, fromString s)
  in
    if ci <= 0 orelse bi <= 0 orelse ci <= 0 then
        let val _ = print "-r requires three positive integers\n" in
        raise argument end
    else rArg
  end
    handle Option => let val _ = 
        print "-r requires three positive integers\n" in
        raise argument end;

fun parseArguments() =
  let
    val args = CommandLine.arguments()
    val _ = case args of [] => raise argument | xs => ()
    fun parseA args (ballotsName, prefix, dead, rArg, seed, filename) = case args of
        [] => (ballotsName, prefix, dead, rArg, seed, filename) |
        ("-v"::rest) => let val _ = verbose := true in 
            parseA rest (ballotsName, prefix, dead, rArg, seed, filename) end |
        ("-Bri"::rest) => 
            parseA rest ("-Bri", prefix, dead, rArg, seed, filename) |
        ("-Gin"::rest) => 
            parseA rest ("-Gin", prefix, dead, rArg, seed, filename) |
        ("-Mol"::rest) => 
            parseA rest ("-Mol", prefix, dead, rArg, seed, filename) |
        ("-r"::c::b::s::rest) => 
            parseA rest ("-r", prefix, dead, parseRandom c b s, seed, filename) |
        ("-s"::s::rest) => (case Real.fromString s of
            NONE   => let val _ = print "-s requires a real number\n" in
                raise argument end |
            SOME x => parseA rest ("-r", prefix, dead, rArg, SOME x, filename)) |
        ("-o"::pre::rest) =>
            parseA rest (ballotsName, pre, dead, rArg, seed, filename) |
        ("-i"::rest) => let val _ = allow_prompt := true in
            parseA rest (ballotsName, prefix, dead, rArg, seed, filename) end |
        ("-d"::c::rest) => (case Int.fromString c of
            NONE => let 
            val _ = print ("-d requires a non-negative integer\n") in
                raise argument end |
            SOME x => if x < 0 then
                let val _ = print ("-d requires a non-negative integer\n") in
                    raise argument end
                else parseA rest 
                    (ballotsName, prefix, add(dead, x), rArg, seed, filename)) |
        ("-f"::file::rest) => 
            parseA rest ("-f", prefix, dead, rArg, seed, file) |
        (arg::rest) => let
            val _ = print ("Ignoring unexpected argument: " ^ arg ^ "\n") in
                parseA rest (ballotsName, prefix, dead, rArg, seed, filename) end
  in
    parseA args ("", "", Intset.empty, (0,0,0), NONE, "")
end;
    
fun main() = let
    val (ballotsName, prefix, dead, rArg, seed, file) = parseArguments() in
    if ballotsName = "" then let val _ =
        print "Must specify an election to count\n" in raise argument end
    else
        let
        val parsedFile = if ballotsName = "-f" then parseBLTFile file
            else (0,0,Intset.empty,[])
        val ballots = case ballotsName of
            "-Bri" => parseBallots candBriOrd pathToBindabella |
            "-Gin" => parseBallots candGinOrd pathToGinninderra |
            "-Mol" => parseBallots candMolOrd pathToMolonglo |
            "-r"   => let 
                val _ = if !verbose then print 
                    "Randomly generating ballots...\n" else ()
                val (numCand, numBallots,_) = rArg
                val gen = case seed of
                NONE   => Random.newgen() |
                SOME x => Random.newgenseed x in
                makeRandomBallots gen numCand numBallots end |
            "-f"   => #4 parsedFile |
            x      => raise argument
        val numToElect = case ballotsName of
            "-Bri" => 5 |
            "-Gin" => 5 |
            "-Mol" => 7 |
            "-r"   => let val (_,_,seats) = rArg in seats end |
            "-f"   => #2 parsedFile |
            x      => raise argument
        val allDead = Intset.union(dead, #3 parsedFile)
        val _ = if !verbose then print "Running election on ballots: \n" 
            else ()
        val _ = if !verbose then List.app printList ballots else ()
        val _ = if !verbose then print ("numToElect: " ^ Int.toString numToElect ^ "\n") else ()
        val _ = if !verbose then print "Dead candidates: \n" else ()
        val _ = if !verbose then printList (listItems allDead) else ()
        val sh = hareClarkCountImpIO (ballots, numToElect, allDead)
        val _ = printVotesTable sh prefix
        val _ = printBallotsTable sh prefix
        in () end
    end
    handle argument => print usage;

val _ = main();

