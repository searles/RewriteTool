package at.searles.scart.provers

import at.searles.scart.terms.{Term, OccurCheck, TermList, Var}
import at.searles.scart.terms.rewriting.{CTRS, TRS, Rule}

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
	override def toString: String = (if(isOverlay) "overlay: " else "overlap: ") + lr2p + " <-- " + peak + " --> " + r1
}

object Confluence {
	def criticalpairs(alpha: Rule, betaPrime: Rule): List[CP] = {
		// rename betaPrime st it does not share variables with other terms
		val beta = betaPrime.renaming(alpha.list.vars.keySet)

		//Logging.d("cps", alpha + " cps with " + beta + "?")

		def filterSelfOverlay(t: Term, p: List[Int]) = alpha.ne(betaPrime) || p.nonEmpty

		// FIXME strongly overlapping
		def toCP(t: Term, p: List[Int]): Option[CP] = t match {
			case v: Var => None
			case _ => if(t.unification(beta.lhs)) {
				//Logging.d("cps", t + " unifiable with " + beta.lhs + " at " + p.reverse)
				try {
					val cplist = new TermList
					val peak = cplist.insert(alpha.lhs)
					val left = alpha.lhs.replace(cplist.insert(beta.rhs), p)
					val right = cplist.insert(alpha.rhs)

					t.ununify(beta.lhs)
					Some(new CP(peak, left, right, p.isEmpty))
				} catch {
					case e: OccurCheck =>
						//Logging.d("cps", t + " occur check with " + beta.lhs)
						t ununify beta.lhs
						None
				}
			} else {
				//Logging.d("cps", t + " not unifiable with " + beta.lhs)
				None
			}
		}

		alpha.lhs.filteredTraverse(toCP, filterSelfOverlay).flatten
	}

	def criticalpairs(rules: List[Rule]): List[CP] =
		rules.flatMap(alpha => rules.flatMap(beta => criticalpairs(alpha, beta)))

	// FIXME: Yes, No, Maybe
	def isConfluentNoModularity(rules: List[Rule]): Proof = {
		val proof = new Proof

		proof.append("System: ")

		proof.append(rules.mkString("\n"))

		proof.nl()

		val cps = criticalpairs(rules)


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
		val terminationProof = Termination.isTerminating(rules)

		val trs = new TRS(rules)

		if(terminationProof.status == Some(true)) {
			proof.append("Terminating:")
			proof.subproof(terminationProof)

			proof.append("Knuth-Bendix:")

			val conf = cps.forall(cp => {
				val n1 = cp.lr2p.normalize(trs)
				val n2 = cp.r1.normalize(trs)

				if(n1 eq n2) {
					proof.append("cp " + cp + " has common nf " + n1)
					true
				} else {
					proof.append("cp " + cp + " has different nfs " + n1 + " and " + n2)
				}


				n1 eq n2
			})

			proof.setStatus(Some(conf))

			return proof
		}

		// FIXME: Test 2: Gramlich-Ohlebusch: Overlay TRS + innermost-terminating + innermost-joinability of CPs

		// Test 3: Left-linear TRS is confluent if overlaps are development-closed
		// includes orthogonal properties (van Oostrom)
		if(isLL) {
			proof.append("left-linearity")

			def developmentClosed(cp: CP): Boolean = cp match {
				case cp@CP(peak, l, r, ov) =>
					if(ov) {
						// l -*-> <-o- r?
						// For simplicity (it might be non-terminating) I use l -o-> <-o- r
						val rDevels = trs.develop(r)

						val lDevels = trs.develop(l)
						val commons = lDevels.intersect(rDevels)

						if(commons.isEmpty) {
							proof.append("no common successors found for cp " + cp)
							false
						} else {
							proof.append(cp + " has common successor(s) " + commons.mkString(" ; "))
							true
						}
					} else {
						// l -o-> r
						if(trs.develop(l).contains(r)) {
							proof.append(cp + " is development-closed")
							true
						} else {
							proof.append(cp + " is not development-closed")
							false
						}
					}
				}

			if(cps.forall(developmentClosed)) {
				proof.setStatus(Some(true))
				return proof
			}
		}

		proof.setStatus(None)
		proof
	}

	def isConfluent(rules: List[Rule]): Proof = {
		// first, modularity.
		val splitRules = Modularity.partNoSharing(rules)

		val conf = Modularity.partNoSharing(rules).map(isConfluentNoModularity)

		val count = conf.size

		if(count == 1) {
			// if no modularity, add this
			conf.head
		} else {
			val proof = new Proof

			val no = conf.filter(_.status == Some(false))
			val maybe = conf.filter(_.status == None)
			val yes = conf.filter(_.status == Some(true))

			if(no.nonEmpty) {
				proof.append("Sub-TRS is not confluent: ")
				proof.subproof(no.head)
				proof.setStatus(Some(false))
			} else if(maybe.nonEmpty) {
				proof.append("Confluence could not be shown of at least one sub-trs:")
				proof.subproof(maybe.head)
				proof.setStatus(None)
			} else {
				proof.append(count + " TRSs were shown to be confluent:")
				yes.foreach(proof.subproof)
				proof.setStatus(Some(true))
			}

			proof
		}
	}
}


