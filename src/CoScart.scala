import at.searles.scart.coco.TPDBParser
import at.searles.scart.provers.{CTRSConfluence, TRSConfluence, Confluence}
import at.searles.scart.terms.rewriting.Transformations

import scala.io.Source



/** Confluence prover for conditional term rewrite systems and
  * unconditional ones.
  * Supported are only deterministic CTRSs.
  */
object CoScart extends scala.App {

	// Step 1: Get argument
	if(args.length != 1) {
		sys.error("Usage: $0 filename.trs")
	}

	// read from file
	val filename = args(0)

	val trsString = Source.fromFile(filename).getLines().mkString("\n")

	val parsed = TPDBParser.parse(TPDBParser.trsOrCtrs, trsString)

	// parse
	if(!parsed.successful) sys.error("Could not parse system\n" + parsed)

	// get unconditional trs
	parsed.get match {
		case Left(rs) =>
			// check for confluence
			val proof = TRSConfluence.isConfluent(rs.rules)
			proof.show()
		case Right(ctrs) =>
			if(!ctrs.rules.forall(rule => rule.isOriented && rule.getType <= 3)) {
				println("UNSUPPORTED")
				System.exit(0)
			}

			val proof = CTRSConfluence.isConfluent(ctrs.rules)
			proof.show()
	}
}
