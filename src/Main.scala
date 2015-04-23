import at.searles.kart.coco.TPDBParser
import at.searles.kart.provers.{Termination, AFAlgorithms, GraphAlgorithms, DependencyPairs}
import at.searles.kart.terms.{TermList, Parsing, Rule}
import scala.io.Source

/**
 * Main program for experiments
 */
object Main extends scala.App {
	//println((0 until 0).forall(_ > 1))

	/*val trs = Parsing.trs(
			"+(x,0) -> x" +
			"+(x,s(y)) -> s(+(x,y))" +
			"-(s(x),s(y)) -> -(x,y)" +
			"-(x,0) -> x" +
			"*(x,0) -> 0" +
			"*(x,s(y)) -> +(x, *(x,y))" +
			"^(x,0) -> s(0)" +
			"^(x,s(y)) -> *(x, ^(x, y))" +
			"/(x,y) -> :(0,x) <= <(x, y) -> true()" +
			"/(x,y) -> :(s(q),r) <= <(x, y) -> false(), /(-(x, y),y) -> :(q,r)" +
			"<(s(x),s(y)) -> <(x,y)" +
			"<(0,s(y)) -> true()" +
			"<(x,0) -> false()"
	).get

	val trs2 = Parsing.trs(
			"+(x,0) -> x" +
			"+(x,s(y)) -> s(+(x,y))" +
			"*(x,0) -> 0" +
			"*(x,s(y)) -> +(x, *(x,y))" +
			"^(x,0) -> s(0)" +
			"^(x,s(y)) -> *(x, ^(x, y))"
	).get

	//println(Confluence.criticalpairs(trs) + ", " + Confluence.isWCR(trs))

	//val t = new TermList().term("/(^(s(s(s(s(s(0))))),s(s(s(s(s(s(0))))))),^(s(s(s(s(s(0))))),s(s(s(s(s(0)))))))").get
	//val t = new TermList().term("/(^(s(s(s(s(s(0))))),s(s(s(s(s(0)))))),^(s(s(s(s(s(0))))),s(s(s(s(0))))))").get
	//val t = new TermList().term("/(^(s(s(s(s(0)))),s(s(s(s(s(0)))))),^(s(s(s(s(0)))),s(s(s(s(0))))))").get
	//val t = new TermList().term("/(^(s(s(0)),s(s(0))),s(s(0)))").get;

	//val now = System.nanoTime()
	//println(t map trs)

	//val delay = System.nanoTime() - now
	//println(delay / 1000000.0)

	//println(t.subterms())

	//println(new DependencyPairs(trs2))

	// Termination proof
	val definedFuns = trs2.defined()
	val rules = trs2.rules.map{case r : Rule => r}

	val dps = rules.map(DependencyPairs.ruleToDP(_, definedFuns)).flatten

	val dpGraph = DependencyPairs.dpGraph(dps, definedFuns)

	val sccs = GraphAlgorithms.tarjan(dpGraph)

	val isTerminating = sccs.forall(scc => {
		AFAlgorithms.find(scc) match {
			case None => println("No AF found: " + scc); false
			case Some(af) => println(scc + " has AF " + af); true
		}
	})*/

	// for each file in trs.tag, read it
	val trsFiles = Source.fromFile("COCO-DB/tags/trs.tag").getLines()
	val terminatingFiles = Source.fromFile("COCO-DB/tags/terminating.tag").getLines().toSet

	var positive = List.empty[String]
	var negative = List.empty[String]

	// read each file and parse the trs
	trsFiles.foreach(filename => {
		val source = Source.fromFile("COCO-DB/" + filename).getLines().mkString("\n")
		val trs = TPDBParser.parse(TPDBParser.spec, source).get

		println("Checking " + filename + "...")
		val taggedTerminating = terminatingFiles.contains(filename)

		val isTerminating = Termination.terminationTest(trs)

		(isTerminating, taggedTerminating) match {
			case (true, true) => positive = filename :: positive; println("SUCCESS")
			case (false, true) => negative = filename :: negative; println("Terminating but could not be shown")
			case (true, false) =>
				sys.error("that is bad. \n\n" + source + "\n");
			case _ => println("not terminating")
		}


		(1 to 40).foreach { i => print("=") }
		println("\n\n")
	})

	println("termination could be shown of the following: " + positive)
	println("termination could not be shown of the following: " + negative)
}