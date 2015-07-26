package at.searles.scart.terms

import at.searles.scart.provers.Logging

import scala.annotation.tailrec
import scala.collection.immutable.TreeMap
import scala.collection.Iterable

class TermList extends Iterable[Term] {
	var headNode: Term = null
	var lastNode: Term = null
	var vars: Map[String, Var] = new TreeMap[String, Var]()

	/*override def ==(that: AnyRef) = sys.error("not allowed")
	override def !=(that: AnyRef) = sys.error("not allowed")*/

	override def equals(o: Any): Boolean = throw new IllegalArgumentException("not comparable")

	override def toString() = this.mkString(" -- ")

	def backup : Array[Term] = {
		val array = new Array[Term](lastNode.pos + 1)
		this.foreach(t => { array(t.pos) = t.link ; t.link = null })
		array
	}

	def restore(backup: Array[Term]) : Unit =
		this.foreach(t => { t.link = backup(t.pos) })

	def clear(): Unit = this.foreach(_.link = null)

	def iterator = new Iterator[Term]() {
		var i = headNode
		override def hasNext = i ne null
		override def next() = {
			val ret = i
			i = i.next
			ret
		}
	}

	// returns true if any variable has been renamed
	def renaming(blacklist: Set[String]): Map[Var, String] = {
		vars.foldLeft(Map.empty[Var, String])((m, entry) => {
			val id = entry._1
			if(blacklist.contains(id)) {
				// find first entry
				// FIXME would be nice to have a stream that returns the new name

				def newids(prefix: String) = new Iterator[String] {
					var i = 0

					override def hasNext = true
					override def next() = { i = i + 1; prefix + "#" + i }
				}

				// FIXME: Proof that this is in fact enough
				val newid = newids(id).find(
					newid => !blacklist.contains(newid) && !vars.contains(newid)
				).get

				m + (entry._2 -> newid)
			} else {
				m
			}
		})
	}

	// Generic version of renaming; can be used to rename rules, conditional rules etc...
	def renaming[A](blacklist: Set[String], original: A, factory: TermList => A): A = {
		// FIXME Bug in here!
		val sigma = renaming(blacklist)

		if (sigma.nonEmpty) {
			// create TermList, add variables and link them
			val newlist = new TermList
			sigma.foreach(entry => entry._1.link = newlist.createVar(entry._2))

			// now create rule
			val ret = factory(newlist)

			// and clean up
			sigma.foreach(entry => entry._1.link = null)
			ret
		} else {
			// no renaming necessary
			original
		}
	}

	// Parser stuff

	// parses a FO-term
	def term(str: String) : Option[Term] = {
		TermParsers.parseAll(TermParsers.term(this), str) match {
			case TermParsers.Success(t, _) => Some(t)
			case _ => None
		}
	}

	// parses an HO-term
	def expr(str: String): Option[Term] = {
		TermParsers.parseAll(TermParsers.expr(this, List.empty[String]), str) match {
			case TermParsers.Success(t, _) => Some(t)
			case _ => None
		}
	}

	def funs: List[String] = {
		this.foldRight(List.empty[String])((t, l) => t match {
			case Fun(f, _, _) => f :: l
			case _ => l
		})
	}

	// now intersting thing: inserting terms.
	def insert(t: Term) : Term = {
		val u = t merge this // fixme what if exception?
		t unsetIs()
		u
	}

	@tailrec private def createLambdaVar(index: Int, node: Term) : LambdaVar = node match {
		case null => LambdaVar(index, this)
		case (lv @ LambdaVar(index2, _)) if index == index2 => lv // found it
		case u => createLambdaVar(index, u.next)
	}

	def createLambdaVar(index: Int): LambdaVar = createLambdaVar(index, headNode)

	@tailrec private def createVar(id: String, node: Term) : Var = node match {
		case null => val v = Var(id, this) ; vars += (id -> v) ; v // add v to vars
		case (v @ Var(id2, _)) if id == id2 => v // found it
		case u => createVar(id, u.next)
	}

	def createVar(id: String): Var = createVar(id, headNode)

	@tailrec private def createFun(f: String, args: Array[Term], node: Term) : Fun = node match {
		case null => Fun(f, args, this)
		case (fun @ Fun(f2, args2, _)) if f == f2 &&
				args.length == args2.length &&
				args.indices.forall(i => args(i) eq args2(i))
			=> fun // found it
		case u => createFun(f, args, u.next)
	}

	def createFun(f: String, args: Array[Term]): Fun =
		if (args.isEmpty) createFun(f, args, headNode) // if no arguments start searching from top
		else {
			//Logging.d("createfun", "args = " + args.mkString(", "))
			val max = args.maxBy(_.pos)
			createFun(f, args, max.next) // otherwise find latest argument
		}


	@tailrec private def createApp(l: Term, r: Term, node: Term) : App = node match {
		case null => App(l, r, this)
		case (app @ App(l2, r2, _)) if l.eq(l2) && r.eq(r2) => app // found it
		case u => createApp(l, r, u.next)
	}

	def createApp(l: Term, r: Term): App = {
		val debruijnmax = l.debruijn max r.debruijn

		val lPrime = if(l.debruijn < debruijnmax) l.updateDebruijn(debruijnmax) else l
		val rPrime = if(r.debruijn < debruijnmax) r.updateDebruijn(debruijnmax) else r

		val max = if (lPrime.pos > rPrime.pos) lPrime else rPrime
		createApp(lPrime, rPrime, max.next)
	}

	@tailrec private def createLambda(t: Term, node: Term) : Lambda = node match {
		case null => Lambda(t, this)
		case (lambda @ Lambda(t2, _)) if t.eq(t2) => lambda // found it
		case u => createLambda(t, u.next)
	}

	def createLambda(t: Term): Lambda = createLambda(t, t.next)
}
