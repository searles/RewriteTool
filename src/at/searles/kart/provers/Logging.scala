package at.searles.kart.provers

object Logging {
	var level = 0

	private def show(tag: String, msg: String): Unit = {
		println(tag + "\t" + msg)
	}

	def i(tag: String, msg: String): Unit = {
		if(level == 0) show(tag, msg)
	}

	def d(tag: String, msg: String): Unit = {
		if(level <= 1) show(tag, msg)
	}
}
