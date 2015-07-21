import at.searles.scart.coco.TPDBParser
import at.searles.scart.provers._
import at.searles.scart.terms._
import at.searles.scart.terms.rewriting._
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
		val blacklist = List("424.trs", "425.trs")
		val trsFiles = Source.fromFile("COCO-DB/tags/trs.tag").getLines().filter(!blacklist.contains(_))
		val terminatingFiles = Source.fromFile("COCO-DB/tags/terminating.tag").getLines().toSet
		val confluentFiles = Source.fromFile("COCO-DB/tags/confluent.tag").getLines().toSet
		val nonconfluentFiles = Source.fromFile("COCO-DB/tags/non_confluent.tag").getLines().toSet

		var positive = List.empty[String]
		var negative = List.empty[String]

		// read each file and parse the trs
		trsFiles.foreach(filename => {
			val source = Source.fromFile("COCO-DB/TRS/" + filename).getLines().mkString("\n")
			val trs = TPDBParser.parse(TPDBParser.trsspec, source).get

			println("Checking " + filename + "...")

			trs.rules.foreach(println)

			val isConf = Confluence.isConfluent(trs.rules).status
			val taggedConf =
					if(confluentFiles.contains(filename)) Some(true)
					else if(nonconfluentFiles.contains(filename)) Some(false)
					else None

			if(isConf == taggedConf) {
				println("SUCCESS: " + isConf)
				if(isConf.isDefined) positive = filename :: positive
			} else if(isConf.isDefined && taggedConf.isDefined) sys.error("WRONG RESULT: " + isConf + ", " + taggedConf)
			else {
				println("NO SUCCESS")
				negative = filename :: negative
			}

			(1 to 40).foreach { i => print("=") }
			println("\n\n")
		})

		println("conf property could be shown of the following: " + positive.length + " ==> " + positive.reverse)
		println("conf property could not be shown of the following: " + negative.length + " ==> " + negative.reverse)
	}

	// trsConfCheck()

	def ctrsCheck(): Unit = {
		val ctrsFiles = Source.fromFile("COCO-DB/tags/ctrs.tag").getLines().filter(_ != "313.trs")

		ctrsFiles.foreach(filename => {
			println("\n==========================================")
			println("Checking \"" + filename + "\"...")

			val source = Source.fromFile("COCO-DB/CTRS/" + filename).getLines().mkString("\n")
			val ctrs = TPDBParser.parse(TPDBParser.ctrsspec, source).get

			//ctrs.rules.foreach(println)

			if(ctrs.isDeterministic) {
				// FIXME: Also check deterministic condition
				val cctrs = Transformations.toCtr(ctrs)
				val trs0 = Transformations.structurePreserving(cctrs)
				val trs1 = Transformations.unravel(ctrs)
				val trs2 = Transformations.unravel(cctrs)

				//println("------------------------------------------")
				//ctrs.rules.foreach(println)

				val confs = List(trs0, trs1, trs2).map(trs => {
					//trs.rules.foreach(println)

					val isTerminating = Termination.isTerminating(trs.rules).status
					println("terminating " + isTerminating)

					val isConfluent = Confluence.isConfluent(trs.rules).status
					println("confluent " + isConfluent)

					isConfluent
				})

				if(confs.head != confs.tail.head || confs.head != confs.tail.tail.head) {
					println(filename + ": " + confs)
				}
			}

			// FIXME: Confluence criteria:
			// 1. Orthogonality
			// 2. Confluence of transformed system
			// 2a. Joinable critical pairs

			println("------------------------------------------")
		})
	}

	ctrsCheck()

	def transformCheck(): Unit = {
		val ctrs = CTRSParser.parse(
			"a() -> b() <= a() -> c()\n" +
			"a() -> c()"
		).get

		//val transformedTRS = Transformations.unravel(ctrs)

		//transformedTRS.rules.foreach(println)

		val trs2 = Transformations.structurePreserving(ctrs)

		trs2.rules.foreach(println)
	}

	//ransformCheck()

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