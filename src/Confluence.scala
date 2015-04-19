/**
 * Created by searles on 15.04.15.
 */
object Confluence {
	def criticalpairs(alpha: Rule, betaPrime: Rule): List[CP] = {
		// map of variables in others which should be renamed
		val sameVars = betaPrime.list.vars.filter(entry => alpha.list.vars.contains(entry._1))

		// next, for each variable find a new one such that it neither occurs in
		// this.list.vars, other.list.vars and the new mapping (sameVars is intersection of first two)
		val blacklist = new scala.collection.mutable.HashSet[String]
		blacklist ++= alpha.list.vars.keySet

		val beta = betaPrime.renaming(blacklist)

		def getCPs(lp: Term, pos: List[Int]): Option[CP] = lp match {
			case Var(_, _) => None
			case _ if(pos == Nil && alpha.eq(betaPrime)) => None // self overlap at root position
			case _ => if(lp.unification(beta.lhs)) {
				try {
					val cplist = new TermList
					val peak = cplist.insert(alpha.lhs)
					val lrp = peak.replace(beta.rhs, pos)
					val ralpha = cplist.insert(alpha.rhs)

					lp.ununify(beta.lhs)
					Some(new CP(peak, lrp, ralpha, pos == Nil))
				} catch {
					case e: OccurCheck => { lp.ununify(beta.lhs); None }
				}
			} else None

		}

		alpha.lhs.traverse(getCPs).flatten
	}

	def criticalpairs(trs: TRS): List[CP] =
		trs.rules.map{case alpha: Rule => trs.rules.map{case beta: Rule => criticalpairs(alpha, beta)}}.flatten.flatten

	// FIXME: could catch a stack overflow, since only one cp has to be false.
	def isWCR(trs: TRS): Boolean = criticalpairs(trs).forall(cp => {
		println(cp)
		val u = cp.lr2p.map(trs)
		val v = cp.r1.map(trs)
		println(u + " ==? " + v);
		u eq v
	})
}

class CP(val peak: Term, val lr2p: Term, val r1: Term, val isOverlay: Boolean) {
	override def toString(): String = peak + " -> [" + lr2p + "; "  + r1 + "]" + isOverlay
}