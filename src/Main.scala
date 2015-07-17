import at.searles.kart.coco.TPDBParser
import at.searles.kart.provers._
import at.searles.kart.terms._
import at.searles.kart.terms.rewriting._
import scala.io.Source

/**
 * Main program for experiments
 */
object Main extends scala.App {

	def rwtest(): Unit = {
		val trs = CTRSParser.parse(
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

		val trs2 = TRSParser.parse(
			"+(x,0) -> x" +
				"+(x,s(y)) -> s(+(x,y))" +
				"*(x,0) -> 0" +
				"*(x,s(y)) -> +(x, *(x,y))" +
				"^(x,0) -> s(0)" +
				"^(x,s(y)) -> *(x, ^(x, y))"
		).get

		//trs.unravel().get.rules.foreach(println)

		//println(Confluence.criticalpairs(trs) + ", " + Confluence.isWCR(trs))

		//val t = new TermList().term("/(s(s(s(s(s(0))))), s(s(0)))")

		//val t = new TermList().term("/(^(s(s(s(s(s(0))))),s(s(s(s(s(s(0))))))),^(s(s(s(s(s(0))))),s(s(s(s(s(0)))))))").get
		val t = new TermList().term("/(^(s(s(s(s(s(0))))),s(s(s(s(s(0)))))),^(s(s(s(s(s(0))))),s(s(s(s(0))))))").get //[5283ms]
		//val t = new TermList().term("/(^(s(s(s(s(0)))),s(s(s(s(s(0)))))),^(s(s(s(s(0)))),s(s(s(s(0))))))").get
		//val t = new TermList().term("/(^(s(s(0)),s(s(0))),s(s(0)))").get;

		//val t = new TermList().term("+(s(0), s(0))").get

		val now = System.nanoTime()
		println(t.normalize(trs))

		val delay = System.nanoTime() - now
		println(delay / 1000000.0)
	}

	//rwtest()

	def cpTest(): Unit = {
		val trs = TRSParser.parse(
			"f(f(x)) -> g(x)"
		).get

		val cps = Confluence.criticalpairs(trs.rules)

		println("cps:")
		cps.foreach(println)
	}

	//cpTest()
	// developmentTest()

	def lambdatest(): Unit = {
		/*val tl = new TermList
		val z = Var("z", tl)

		val x = LambdaVar(0, tl)
		val y = LambdaVar(1, tl)

		val lxzx = Lambda(App(z,x, tl),tl)
		val lxzx2 = tl.expr("\\x.Z x").get
		val lyxy = Lambda(Lambda(y,tl), tl)
		val lyxy2 = tl.expr("\\y x.y").get



		println(lxzx)
		println(lyxy)
		println(lxzx2)
		println(lyxy2)*/
	}



	// Termination proof
	/*val definedFuns = trs2.defined()
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

	def trsConfCheck(): Unit = {
		// for each file in trs.tag, read it
		val trsFiles = Source.fromFile("COCO-DB/tags/trs.tag").getLines()
		val terminatingFiles = Source.fromFile("COCO-DB/tags/terminating.tag").getLines().toSet
		val confluentFiles = Source.fromFile("COCO-DB/tags/confluent.tag").getLines().toSet

		var positive = List.empty[String]
		var negative = List.empty[String]

		// read each file and parse the trs
		trsFiles.foreach(filename => {
			val source = Source.fromFile("COCO-DB/TRS/" + filename).getLines().mkString("\n")
			val trs = TPDBParser.parse(TPDBParser.trsspec, source).get

			println("Checking " + filename + "...")

			trs.rules.foreach(println)

			val isConf = Confluence.confluenceCheck(trs.rules)
			val taggedConf = confluentFiles.contains(filename)

			(isConf, taggedConf) match {
				case (Some(true), true) => positive = filename :: positive; println("SUCCESS, CONF")
				case (Some(false), true) => sys.error("WRONG! IT IS CONF")
				case (Some(true), false) => sys.error("WRONG! IT IS NOT CONF")
				case (Some(false), false) => positive = filename :: positive; println("SUCCESS, NOT CONF")
				case (None, true) => negative = filename :: negative; println("MISSING CONF")
				case (None, false) => negative = filename :: negative; println("MISSING NOT CONF")
				case _ => sys.error("unhandled case: " + isConf + ", " + taggedConf)
			}


			(1 to 40).foreach { i => print("=") }
			println("\n\n")
		})

		println("conf property could be shown of the following: " + positive)
		println("conf property could not be shown of the following: " + negative)
	}

	trsConfCheck()

	def ctrsCheck(): Unit = {
		val ctrsFiles = Source.fromFile("COCO-DB/tags/ctrs.tag").getLines()

		ctrsFiles.foreach(filename => {
			println("\n==========================================")
			println("Checking \"" + filename + "\"...")

			val source = Source.fromFile("COCO-DB/CTRS/" + filename).getLines().mkString("\n")
			val ctrs = TPDBParser.parse(TPDBParser.ctrsspec, source).get

			ctrs.rules.foreach(println)

			if(ctrs.isDeterministic) {
				// FIXME: Also check deterministic condition
				val cctrs = Transformations.toCtr(ctrs)
				val trs = Transformations.unravel(cctrs)
				println("------------------------------------------")
				trs.rules.foreach(println)

				val isTerminating = Termination.terminationTest(trs.rules)
				println("terminating " + isTerminating)
			}

			// FIXME: Confluence criteria:
			// 1. Orthogonality
			// 2. Confluence of transformed system
			// 2a. Joinable critical pairs

			println("------------------------------------------")
		})
	}

	//ctrsCheck()

	def transformCheck(): Unit = {
		val ctrs = CTRSParser.parse(
			"f(x, x) -> x <= x -> true()\n" +
			"f(x, x) -> false() <= x -> false()\n" +
			"g(s(x)) -> g(x)\n" +
			"a() -> b()"
		).get

		val transformedTRS = Transformations.unravel(ctrs)

		transformedTRS.rules.foreach(println)
	}

	//transformCheck()

	//ctrsCheck()

	def test(): Unit = {
		val t = new TermList().term("w(x)").get
		val u = new TermList().term("w(b())").get

		println(t.unification(u))

		t.ununify(u)

		println(t)
		println(u)

	}

	//test

	def modularityCheck(): Unit = {
		val ctrs = TRSParser.parse(
			"f(x, x) -> x\n" +
				"f(x, s()) -> false()\n" +
				"g(s(x)) -> g(x)\n" +
				"a() -> b()"
		).get

		println(Modularity.partNoSharing(ctrs.rules))
	}

	//modularityCheck
}