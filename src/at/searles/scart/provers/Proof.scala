package at.searles.scart.provers

class Proof {
	// FIXME: Convert to tree like proof trees!
	// FIXME: Termination then is an extension of proof, containing several subproofs!
	// FIXME: Allow multithreading!
	var proof = List.empty[String]
	var status: Option[Boolean] = None

	def append(line: String): Unit = proof = line :: proof
	def nl(): Unit = proof = "" :: proof

	def subproof(sub: Proof): Unit = {
		proof = sub.proof.foldRight(proof)((line, list) => ("\t" + line) :: list)
		append("\n")
	}

	def setStatus(status: Option[Boolean]) = this.status = status

	def show() = {
		status match {
			case None =>
				println("MAYBE")

				// FIXME: For debugging
				proof.reverse.foreach(println)
			case Some(state) =>
				println(if(state) "YES" else "NO")
				proof.reverse.foreach(println)
		}
	}

	override def toString = {
		proof.foldRight("")(_ + _ + "\n")
	}
}