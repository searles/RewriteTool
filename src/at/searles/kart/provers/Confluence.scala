package at.searles.kart.provers

import at.searles.kart.terms.{Term, OccurCheck, TermList, Var}
import at.searles.kart.terms.rewriting.{CTRS, TRS, Rule}

import scala.annotation.tailrec

/**
 * Confluence proof:
 *
 * if terminating
 *     confluent = isWCR
 * else
 *     exploit modularity properties
 *
 *
 * Some results: Ohlebusch94: Confluence is modular for constructur-sharing if a shared constructor cannot
 * be lifted (ie, no rhs is rooted by a shared constructor and no rule is collapsing): Easy to implement.
 *
 * Weakly orthogonal TRSs are confluent (Huet91) [weakly: ll + all overlaps are trivial]
 *
 */
case class CP(peak: Term, lr2p: Term, r1: Term, isOverlay: Boolean) {
	override def toString: String = (if(isOverlay) "overlay{" else "overlap{") + peak + " -> [" + lr2p + " ; "  + r1 + "]" + "}"
}

object Confluence {
	def criticalpairs(alpha: Rule, betaPrime: Rule): List[CP] = {
		// rename betaPrime st it does not share variables with other terms
		val beta = betaPrime.renaming(alpha.list.vars.keySet)

		Logging.d("cps", alpha + " cps with " + beta + "?")

		def filterSelfOverlay(t: Term, p: List[Int]) = alpha.ne(betaPrime) || p.nonEmpty

		def toCP(t: Term, p: List[Int]): Option[CP] = t match {
			case v: Var => None
			case _ => if(t.unification(beta.lhs)) {
				Logging.d("cps", t + " unifiable with " + beta.lhs + " at " + p.reverse)
				try {
					val cplist = new TermList
					val peak = cplist.insert(alpha.lhs)
					val left = alpha.lhs.replace(cplist.insert(beta.rhs), p)
					val right = cplist.insert(alpha.rhs)

					t.ununify(beta.lhs)
					Some(new CP(peak, left, right, p.isEmpty))
				} catch {
					case e: OccurCheck =>
						Logging.d("cps", t + " occur check with " + beta.lhs)
						t ununify beta.lhs
						None
				}
			} else {
				Logging.d("cps", t + " not unifiable with " + beta.lhs)
				None
			}
		}

		alpha.lhs.filteredTraverse(toCP, filterSelfOverlay).flatten
	}

	def criticalpairs(rules: List[Rule]): List[CP] =
		rules.flatMap(alpha => rules.flatMap(beta => criticalpairs(alpha, beta)))

	// FIXME: Yes, No, Maybe
	def confluenceCheckNoModularity(rules: List[Rule]): Option[Boolean] = {
		val cps = criticalpairs(rules)

		Logging.d("conf", rules.mkString("; ") + " has cps " + cps.mkString("; "))

		// some properties
		val isOverlay = cps.forall(_.isOverlay)
		val isOverlapping = cps.nonEmpty
		val isTrivial = cps.forall(cp => cp.lr2p eq cp.r1)
		val isLL = rules.forall(_.isLL)
		val isLinear = rules.forall(rule => rule.isLL && rule.isRL)

		// FIXME: Idea confluence:
		//   Let T_p = { t | s|_p ->1 t }
		//   Then I can replace development relation by the following more general relation:
		//     s -#-> u if u = s[t1]_p1..[tn]_pn where t_i \in T_pi

		// FIXME: weak orthogonality/almost orthogonality

		// Test 1: Knuth-Bendix
		val isTerminating = Termination.terminationTest(rules)

		val trs = new TRS(rules)

		if(isTerminating.isDefined && isTerminating.get) {
			val conf = cps.forall(cp => {
				val n1 = cp.lr2p.normalize(trs)
				val n2 = cp.r1.normalize(trs)

				Logging.i("cps", cp + " has NFs " + n1 + ", " + n2)

				n1 eq n2
			})

			return Some(conf)
		}

		// FIXME: Test 2: Gramlich-Ohlebusch: Overlay TRS + innermost-terminating + innermost-joinability of CPs
		None
	}

	def confluenceCheck(rules: List[Rule]): Option[Boolean] = {
		// first, modularity.
		val conf = Modularity.partNoSharing(rules).map(confluenceCheckNoModularity)
		conf.fold(Some(true))((c0, c1) => if(c0.isDefined && c1.isDefined) Some(c0.get && c1.get) else None)
	}
}


