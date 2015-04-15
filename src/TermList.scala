import scala.annotation.tailrec
import scala.collection.immutable.TreeMap
import scala.collection.mutable

/**
 * Created by searles on 09.04.15.
 */
class TermList {
	var head: Term = null
	var last: Term = null
	var vars: Map[String, Var] = new TreeMap[String, Var]()

	def toList(): List[Term] = toList(head)

	private def toList(t: Term): List[Term] = if(t == null) Nil else t :: toList(t.next)

	@tailrec private def toString(s: String, t: Term): String = {
		if(t == null) s
		else toString(s + "; " + t, t.next)
	}

	override def toString() = if(head == null) "" else toString(head.toString, head.next)

	// backup link fields (reverse order)
	// fixme: possible speedup: in conditional rules, store in an order such that
	// all links are occupied from left to right
	@tailrec private def backup(node: Term, data: Array[Term]): Unit =
		if(node != null) {
			data(node.pos) = node.link
			node.link = null
			backup(node.next, data)
		}

	def backup : Array[Term] = {
		val array = new Array[Term](last.pos + 1)
		backup(head, array)
		array
	}

	@tailrec private def restore(node: Term, backup: Array[Term]): Unit = {
		if (node != null) {
			node.link = backup(node.pos)
			restore(node.next, backup)
		}
	}

	def restore(backup: Array[Term]) : Unit = restore(head, backup)

	def term(str: String) : Option[Term] = {
		TermParsers.parseAll(TermParsers.expr(this), str) match {
			case TermParsers.Success(t, _) => Some(t)
			case TermParsers.NoSuccess(_, _) => None
		}
	}

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

	def createLambdaVar(index: Int): LambdaVar = createLambdaVar(index, head)

	@tailrec private def createVar(id: String, node: Term) : Var = node match {
		case null => val v = Var(id, this) ; vars += (id -> v) ; v // add v to vars
		case (v @ Var(id2, _)) if id == id2 => v // found it
		case u => createVar(id, u.next)
	}

	def createVar(id: String): Var = createVar(id, head)

	@tailrec private def createFun(f: String, args: Array[Term], node: Term) : Fun = node match {
		case null => Fun(f, args, this)
		case (fun @ Fun(f2, args2, _)) if f == f2 &&
				args.length == args2.length &&
				(0 until args.length).forall(i => args(i) eq args2(i))
			=> fun // found it
		case u => createFun(f, args, u.next)
	}

	def createFun(f: String, args: Array[Term]): Fun =
		if (args.isEmpty) createFun(f, args, head)
		else {
			val max = args.maxBy(_.pos)
			createFun(f, args, max.next)
		}


	@tailrec private def createApp(l: Term, r: Term, node: Term) : App = node match {
		case null => App(l, r, this)
		case (app @ App(l2, r2, _)) if l.eq(l2) && r.eq(r2) => app // found it
		case u => createApp(l, r, u.next)
	}

	def createApp(l: Term, r: Term): App = {
		val max = if (l.pos > r.pos) l else r
		createApp(l, r, max.next)
	}

	@tailrec private def createLambda(t: Term, node: Term) : Lambda = t match {
		case null => Lambda(t, this)
		case (lambda @ Lambda(t2, _)) if t.eq(t2) => lambda // found it
		case u => createLambda(t, u.next)
	}

	def createLambda(t: Term): Lambda = createLambda(t, t.next)
}
