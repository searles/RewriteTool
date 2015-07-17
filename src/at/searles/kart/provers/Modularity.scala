package at.searles.kart.provers

import at.searles.kart.terms.rewriting.Rule

object Modularity {
	// for modularity properties
	// split into distinct symbols:
	// Step 1: combine rule + fun ==> List[(Rule, List[String]])
	// Step 2:
	// Step 2: Interpret as graph: If two items share one symbol they are connected
	// Step 3: Find
	def partNoSharing(rules: List[Rule]): List[List[Rule]] = {
		// we interpret the thing as a graph where two rules are connected if they share at least one symbol

		// takes a rule and a list of rules and
		// returns a list of all connected rules in rs and a list of
		// remaining rules
		def partBySyms(syms: Set[String], rs: List[Rule]): (List[Rule], List[Rule]) = {
			// _1 = all rules sharing symbols
			// _2 = all others
			val part = rs.partition(r => r.list.funs.exists(f => syms.contains(f) ))

			if (part._1.isEmpty || part._2.isEmpty) part
			else {
				// now, extend syms by all symbols in part._1
				val syms2 = part._1.foldRight(syms)((r, set) => set ++ r.list.funs)

				// filter out also those in part._2
				val part2 = partBySyms(syms2, part._2)

				// combine result
				(part._1 ++ part2._1, part2._2)
			}
		}

		def partAll(rs: List[Rule]): List[List[Rule]] = rs match {
			case h :: t =>
				val part = partBySyms(h.list.funs.toSet, t) // partition for head rule
				(h :: part._1) :: partAll(part._2)
			case _ => List.empty[List[Rule]]
		}

		partAll(rules)
	}

}