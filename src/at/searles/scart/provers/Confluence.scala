package at.searles.scart.provers

import at.searles.scart.terms.{Term, OccurCheck, TermList, Var}
import at.searles.scart.terms.rewriting._

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

object Confluence {
	def toGenericCP[A](alphaLhsP: Term, betaLhs: Term, factory: () => A): Option[A] = alphaLhsP match {
		case v: Var => None
		case _ => if(alphaLhsP.unification(betaLhs)) {
			//Logging.d("cps", t + " unifiable with " + beta.lhs + " at " + p.reverse)
			try {
				val ret = factory()
				alphaLhsP.ununify(betaLhs)
				Some(ret)
			} catch {
				case e: OccurCheck =>
					//Logging.d("cps", t + " occur check with " + beta.lhs)
					alphaLhsP ununify betaLhs
					None
			}
		} else {
			//Logging.d("cps", t + " not unifiable with " + beta.lhs)
			None
		}
	}
}

case class CP(peak: Term, lr2p: Term, r1: Term, p: List[Int]) {
	def isOverlay: Boolean = p.isEmpty
	override def toString: String = (if(isOverlay) "overlay: " else "overlap: ") + lr2p + " <-- " + peak + " --> " + r1
}

object TRSConfluence {
	def criticalpairs(alpha: Rule, betaPrime: Rule): List[CP] = {
		// rename betaPrime st it does not share variables with other terms
		val beta = betaPrime.renaming(alpha.list.vars.keySet)

		//Logging.d("cps", alpha + " cps with " + beta + "?")
		def filterSelfOverlay(t: Term, p: List[Int]) = alpha.ne(betaPrime) || p.nonEmpty

		def toCP(alphaLhsP: Term, p: List[Int]): Option[CP] = Confluence.toGenericCP[CP](alphaLhsP, beta.lhs, () => {
			val cplist = new TermList
			val peak = cplist.insert(alpha.lhs)
			val left = alpha.lhs.replace(cplist.insert(beta.rhs), p)
			val right = cplist.insert(alpha.rhs)

			CP(peak, left, right, p)
		})

		alpha.lhs.filteredTraverse(toCP, filterSelfOverlay).flatten
	}

	def criticalpairs(rules: List[Rule]): List[CP] = {
		// first: only overays


		rules.flatMap(alpha => rules.flatMap(beta => criticalpairs(alpha, beta)))
	}

	def isConfluentNoModularity(rules: List[Rule]): Proof = {
		val proof = new Proof

		proof.append("system: " + rules.mkString(" ; "))

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

			proof.append("termination proof:")
			proof.subproof(terminationProof)

			proof.append("system is terminating")

			val wcr = cps.forall(cp => {
				val n1 = cp.lr2p.normalize(trs)
				val n2 = cp.r1.normalize(trs)

				if(n1 eq n2) {
					proof.append("cp " + cp + " has common nf " + n1)
					true
				} else {
					proof.append("cp " + cp + " has different nfs " + n1 + " and " + n2)
					false
				}
			})

			if(wcr) {
				proof.append("system is locally confluent and terminating, hence confluent")
			} else {
				proof.append("system is not locally confluent, hence not confluent")
			}

			proof.setStatus(Some(wcr))

			return proof
		} /* else {
			// try to disprove confluence by disproving local confluence. set timeout for this.
			// FIXME: Not a good idea. Catching StackOverflow might corrupt data structures.
			// True story! I got some term lists corrupted that then changed a lot of things internally

			val wcr = cps.forall(cp => {
				try {
					val list = new TermList

					val t0 = list.insert(cp.lr2p)
					val t1 = list.insert(cp.r1)

					val n1 = t0.normalize(trs)
					val n2 = t1.normalize(trs)

					// FIXME: normalize might not return a normalform in non-terminating systems!
					list.clear() // unset all links (otherwise isNF does not work)

					if(n1.ne(n2) && trs.isNF(n1) && trs.isNF(n2)) {
						proof.append("cp " + cp + " has different nfs " + n1 + " and " + n2)
						false
					} else {
						true
					}
				} catch {
					case e: StackOverflowError => proof.append("could not (dis-)prove local confluence")
					// FIXME: Clean links in trs
					rules.foreach(_.list.clear())
					true
				}
			})

			// FIXME: wcr == true could also mean a stackoverflow

			if(!wcr) {
				proof.append("system is not locally confluent, hence not confluent")
				proof.setStatus(Some(false))
				return proof
			}
		}*/

		// FIXME: Test 2: Gramlich-Ohlebusch: Overlay TRS + innermost-terminating + innermost-joinability of CPs

		// FIXME: http://drops.dagstuhl.de/opus/volltexte/2011/3110/pdf/2.pdf
		// FIXME: http://link.springer.com/chapter/10.1007%2F978-3-642-12251-4_20
		// FIXME: http://link.springer.com/article/10.1007%2Fs10817-011-9238-x
		// FIXME: http://link.springer.com/chapter/10.1007%2F978-3-642-28717-6_21
		// FIXME: Aoto Toyama: A reduction-preserving completion for proving confluence of non-terminating term rewriting systems


		// Test 3: Left-linear TRS is confluent if overlaps are development-closed
		// includes orthogonal properties (van Oostrom)
		if(isLL) {
			proof.append("system is left-linear")

			// Huet91: Weakly orthogonal TRSs are confluent.
			val isWeaklyOrthogonal = cps.forall {
				case CP(_, t0, t1, _) => t0 eq t1
			}

			if(isWeaklyOrthogonal) {
				// HuetLevy91
				proof.append("all critical pairs are trivial")
				proof.append("system is weakly orthogonal, hence confluent")
				proof.setStatus(Some(true))
				return proof
			}

			def strongJoin(l: Term, r: Term): Set[Term] = {
				// l -*-> <-o- r?
				val rDevels = trs.develop(r)

				val startTime = System.currentTimeMillis()

				// FIXME: how many levels should I check?
				def aux(reducts: Set[Term], alreadyChecked: Set[Term]): Set[Term] = {
					// FIXME: Use cache.
					if(reducts.isEmpty) {
						Set.empty[Term]
					} else {
						val nextAlreadyChecked = reducts ++ alreadyChecked
						val nextReducts = reducts.flatMap(t => trs.applyAll(t, t.parent).filter(!nextAlreadyChecked.contains(_)))

						val commons = rDevels.intersect(nextReducts)

						if (commons.isEmpty) {
							val currentTime = System.currentTimeMillis()

							// FIXME: Timeout of 1 second
							if(currentTime - startTime < 500) {
								aux(nextReducts, nextAlreadyChecked)
							} else {
								// FIXME: Time-Out.
								// FIXME: Use different way for timeout.
								// e.g. create proof-object and timeout-object
								Set.empty[Term]
							}
						} else {
							commons
						}
					}
				}

				aux(Set(l), Set.empty[Term])
			}

			def developmentClosed(cp: CP): Boolean = cp match {
				case cp@CP(peak, l, r, ov) =>
					// FIXME: Overlays are there two times which is an overhead for Knuth-Bendix
					// FIXME: More sharing.
					if(cp.isOverlay) {
						// l -*-> <-o- r?
						val commons = strongJoin(l, r)

						if(commons.isEmpty) {
							proof.append("no common successors found for cp " + cp)
							false
						} else {
							proof.append(cp + " can be joined to -*-> t <-o- where t in {" + commons.mkString(" ; ") + "}")
							true
						}
					} else {
						// l -o-> r
						if(trs.develop(l).contains(r)) {
							proof.append(cp + " is development-closed ( -o-> )")
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

			proof.append("splitting trs into " + count + " trss")

			val no = conf.filter(_.status == Some(false))
			val maybe = conf.filter(_.status == None)
			val yes = conf.filter(_.status == Some(true))

			if(no.nonEmpty) {
				proof.append("subtrs is not confluent: ")
				proof.subproof(no.head)
				proof.setStatus(Some(false))
			} else if(maybe.nonEmpty) {
				proof.append("confluence could not be shown of at least one sub-trs:")
				proof.subproof(maybe.head)
				proof.setStatus(None)
			} else {
				proof.append(count + " trss were shown to be confluent:")
				yes.foreach(proof.subproof)
				proof.setStatus(Some(true))
			}

			proof
		}
	}

}

case class CCP(u: CP, cs: List[Condition]) {
	def isOverlay: Boolean = u.p.isEmpty
	override def toString: String = u.toString + " <= " + cs.mkString(" ; ")
}

// FIXME:
// class CTRSConfluenceProof(List[Rule])
//     val ccps = ...
//     val unraveling = ...
//     val type = ...

object CTRSConfluence {
	// For conditional rules it is almost the same.
	def criticalpairs(alpha: ConditionalRule, betaPrime: ConditionalRule): List[CCP] = {
		// rename betaPrime st it does not share variables with other terms
		val beta = betaPrime.renaming(alpha.u.list.vars.keySet)

		//Logging.d("cps", alpha + " cps with " + beta + "?")

		def filterSelfOverlay(t: Term, p: List[Int]) = alpha.ne(betaPrime) || p.nonEmpty

		// FIXME strongly overlapping
		def toCCP(alphaLhsP: Term, p: List[Int]): Option[CCP] = Confluence.toGenericCP[CCP](alphaLhsP, beta.u.lhs, () => {
			val cplist = new TermList
			val peak = cplist.insert(alpha.u.lhs)
			val left = alpha.u.lhs.replace(cplist.insert(beta.u.rhs), p)
			val right = cplist.insert(alpha.u.rhs)

			val cs = alpha.cs.map(c => c.copy(cplist)) ++ beta.cs.map(c => c.copy(cplist))

			CCP(CP(peak, left, right, p), cs)
		})

		alpha.u.lhs.filteredTraverse(toCCP, filterSelfOverlay).flatten
	}

	def criticalpairs(rules: List[ConditionalRule]): List[CCP] =
		rules.flatMap(alpha => rules.flatMap(beta => criticalpairs(alpha, beta)))

	def isInfeasible(ccp: CCP, ctrs: CTRS): Boolean = {
		// Check from ALS94:
		// http://cl-informatik.uibk.ac.at/users/ami/research/publications/proceedings/14rtatlca.pdf
		val list = new TermList
		val prefix = "ci#"

		def constify(t: Term): Term = {
			// replace every variable x by constant c#x
			val vars = t.vars

			vars.foreach(v => v.link = list.createFun(prefix + v.id, Array.empty[Term]))
			val ret = list.insert(t)
			vars.foreach(_.link = null)

			ret
		}

		// FIXME
		false
	}

	def isConfluent(rules: List[ConditionalRule]): Proof = {
		assert(rules.forall(rule => rule.isOriented && rule.getType <= 3))

		val proof = new Proof()

		proof.append("system: " + rules.mkString(" ; "))

		val ccps = criticalpairs(rules)
		val utrs = new TRS(rules.map(_.u))

		// First, level-confluence
		val isLL = rules.forall(_.u.lhs.isLinear)

		// FIXME: Maybe a simple infeasibility check?
		val ccpsTrivial = ccps.forall {
			case CCP(cp, cs) => cp match {
				case CP(_, t0, t1, p) => p.isEmpty && t0.eq(t1)
			}
		}

		val isAlmostOrthogonal = ccpsTrivial && isLL

		val isProperlyOriented = rules.forall(_.isProperlyOriented)
		val isRightStable = rules.forall(_.isRightStable(utrs))

		if(isAlmostOrthogonal && isProperlyOriented && isRightStable) {
			proof.append("CTRS is orthogonal, properly oriented and right stable, hence level-confluent")
			proof.setStatus(Some(true))

			return proof
		}

		// FIXME: A quasi-decreasing strongly irreducible deterministic 3-CTRS R is confluent if and only if all critical pairs of R are joinable.

		// otherwise, transform and check confluence
		val isDeterministic = rules.forall(_.isDeterministic)

		if(!isDeterministic) {
			proof.setStatus(None)
			return proof
		}

		proof.append("system is deterministic")

		var sound: Boolean = false

		if(rules.forall(_.isWLL)) {
			proof.append("system is weakly left-linear")
			sound = true
		}

		if(rules.forall(_.isWRL)) {
			proof.append("system is weakly right-linear")
			sound = true
		}

		if(!sound) {
			proof.append("transformation might not be sound")
			proof.setStatus(None)
			return proof
		}

		proof.append("transformation is sound")

		val rs = Transformations.structurePreserving(Transformations.toCtr(new CTRS(rules)))

		proof.append("transformed system: " + rs.rules.mkString(" ; "))

		val subproof = TRSConfluence.isConfluent(rs.rules)

		// switch no to maybe.
		if(subproof.status == Some(true)) {
			proof.subproof(subproof)
			proof.append("transformed system is confluent, transformation is sound, hence ctrs is confluent")
			proof.setStatus(Some(true))
		} else {
			proof.setStatus(None)
		}


		proof
	}
}

