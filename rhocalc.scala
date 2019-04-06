/** Tiny interpreter of raw rho-calculus.
  *
  * No parser, rho-calculus terms must be entered using 
  * the EDSL, so that all "rho-calculus programs" actually
  * reside in this file.
  */
import scala.language.higherKinds
import scala.language.implicitConversions

sealed trait AstProc

case object AstZero extends AstProc {
  override def toString = "O"
}
case class AstSymbol(name: String) extends AstProc {
  override def toString = name
}
case class AstInput(
  channel: AstName,
  bound: AstName,
  body: AstProc
) extends AstProc {
  override def toString = s"${channel}(${bound}).${body}"
}
case class AstLift(channel: AstName, process: AstProc) extends AstProc {
  override def toString = s"${channel}\u2989${process}\u298A"
}
case class AstDrop(name: AstName) extends AstProc {
  override def toString = s"\u231D${name}\u231C"
}
case class AstPar(p: AstProc, q: AstProc) extends AstProc {
  override def toString = s"(${p}|${q})"
}

sealed trait AstName

case class AstQuote(process: AstProc) extends AstName {
  override def toString = s"\u231C${process}\u231D"
}

type Bag[X] = Map[X, Int]

sealed trait Proc

case class Symbol(name: String) extends Proc {
  override def toString = name
}
case class Input(channel: Name, body: Proc) extends Proc {
  override def toString = s"${channel}?${body}"
}
case class Lift(channel: Name, proc: Proc) extends Proc {
  override def toString = s"${channel}\u2989${proc}\u298A"
}
case class Drop(name: Name) extends Proc {
  override def toString = s"\u231D${name}\u231C"
}
case class Par(multiset: Bag[Proc]) extends Proc {
  override def toString = s"{${
    multiset
    .toList
    .map{ case (k, v) => (k.toString, v) }
    .sortBy(_._1)
    .flatMap {
      case (k, v) => {
        val s = k.toString
        List.fill(v)(s)
      }
    }
    .mkString("|")
  }}"
}

sealed trait Name {
  def apply(y: Name): Proc = Lift(this, Drop(y))
}

case class Quote(process: Proc) extends Name {
  override def toString = s"\u231C${process}\u231D"
}
case class Bound(deBruijnIdx: Int) extends Name {
  override def toString = s"\u2768${deBruijnIdx}\u2769"
}

object Quote {
  def normalized(p: Proc): Quote = p match {
    case Drop(q @ Quote(_)) => q
    case sthElse => Quote(p)
  }
}

/** Forms the union of two multisets represented by `Map`s. 
  * 
  * Pointwise addition, essentially.
  */
def multisetUnion[X](a: Bag[X], b: Bag[X]): Bag[X] = {
  (for (k <- (a.keys ++ b.keys)) yield {
    (k, a.getOrElse(k, 0) + b.getOrElse(k, 0))
  }).toMap
}

// helper method for unpacking multisets of parallel processes into flat lists
def multisetExplode[X](b: Bag[X]): List[X] = b.toList.flatMap {
  case (k, v) => Iterator.fill(v)(k)
}

def toMultiset[X](a: List[X]) = a.groupBy(identity).mapValues(_.size)

def structurallyNormalize(p: AstProc): Proc = {
  /** Recursive helper method that keeps track of the de-Bruijn depths of
    * the binders encountered so far, and of the current depth.
    */
  def rec(p: AstProc, binderDepth: Map[Name, Int], currDepth: Int): Proc = {

    /** Yet another helper that flattens binary `AstPar`s into a multiset. */
    def parToMultiset(p: AstProc): Map[Proc, Int] = p match {
      case AstZero => Map.empty
      case AstPar(x, y) => multisetUnion(parToMultiset(x), parToMultiset(y))
      case sthElse => Map(rec(sthElse, binderDepth, currDepth) -> 1)
    }
    
    /** Attempts to bind a name to a binder saved in the `binderDepth` context.
      * If there is no such binder, the name is returned as-is.
      */
    def bind(v: Name): Name = 
      binderDepth
      .get(v)
      .map{ d => Bound(currDepth - d) }
      .getOrElse(v)

    p match {
      case AstZero => Par(Map.empty)
      case AstSymbol(s) => Symbol(s)
      case AstInput(c, v, b) => {
        // we can ignore context here, quotation impervious to substitution,
        // cannot have any bound variables inside.
        val cNorm = structurallyNormalize(c)
        val vNorm = structurallyNormalize(v)
        val nextDepth = currDepth + 1
        val bNorm = rec(b, binderDepth.updated(vNorm, nextDepth), nextDepth)
        Input(bind(cNorm), bNorm)
      }
      case AstLift(c, msg) => {
        val cNorm = structurallyNormalize(c)
        val msgNorm = rec(msg, binderDepth, currDepth)
        Lift(bind(cNorm), msgNorm)
      }
      case AstDrop(v) => {
        val vNorm = structurallyNormalize(v)
        Drop(bind(vNorm))
      }
      case par @ AstPar(_, _) => Par(parToMultiset(par))
    }
  }

  rec(p, Map.empty, 0)
}

def structurallyNormalize(n: AstName): Name = n match {
  case AstQuote(AstDrop(m)) => structurallyNormalize(m)
  case AstQuote(p) => Quote(structurallyNormalize(p))
}

/** Transforms list of `AstProc`s into list of `Proc` terms.
  *
  * The list can be used as initial state of the virtual machine,
  * that is, this method is supposed to be used inside `Prog.initialState`
  * for building initial state by compiling `AstProc`s.
  *
  * If one `AstProc` term compiles to multiple `Proc`
  * terms, the initial justification (comment) is attached to all `Proc`s.
  */
def compile[F[+_]: Justification](ts: F[AstProc]*): List[F[Proc]] = {
  val j = implicitly[Justification[F]]
  import j._

  ts.flatMap { _.explode { astProc => structurallyNormalize(astProc) match {
    case Par(ps) => multisetExplode(ps)
    case sthElse => List(sthElse)
  }}}(collection.breakOut)
}

/** Explodes all `Par`s contained in the `bag`. */
def unpackPars(bag: Bag[Proc]): Bag[Proc] = {
  bag
  .iterator
  .map { 
    case (Par(subBag), v) => subBag.mapValues(_ * v)
    case (sthElse, v) => Map(sthElse -> v)
  }
  .foldLeft(Map.empty[Proc, Int])(multisetUnion[Proc](_, _))
}

object VM {

  def semanticSubstitution(p: Proc, byWhat: Quote, deBruijnDepth: Int = 0)
  : Proc = {
    def substName(n: Name): Name = n match {
      case Quote(_) => n // non-local name with quoted process, impervious!
      case Bound(idx) => if (idx == deBruijnDepth) byWhat else n
    }
  
    p match {
      case s @ Symbol(_) => s
      case Par(multiset) => Par(unpackPars(multiset.map {
        case (k, v) => (semanticSubstitution(k, byWhat, deBruijnDepth), v)
      }))
      case Input(c, body) => 
        Input(
          substName(c),
          semanticSubstitution(body, byWhat, deBruijnDepth + 1)
        )
      case Lift(c, body) => 
        Lift(substName(c), semanticSubstitution(body, byWhat, deBruijnDepth))
      case d @ Drop(x) => x match {
        case Quote(_) => d
        case Bound(idx) => if (idx == deBruijnDepth) byWhat.process else d
      }
    }
  }

  /*
  locally {
    println()
    println("Substitution example:")
    val x = AstQuote(AstSymbol("x"))
    val f = AstQuote(AstSymbol("f"))
    val P = AstSymbol("P")
    val Omega = AstInput(x, f, AstPar(AstPar(AstDrop(f), x(f)), P))
    val qOmega = AstQuote(Omega)
    
    val normOmega = structurallyNormalize(Omega)
    val Input(_, omegaBody) = normOmega
    val normQOmega: Quote = structurallyNormalize(qOmega) match {
      case q @ Quote(_) => q
      case _ => throw new Error("quote expected!")
    }
    val res = semanticSubstitution(omegaBody, normQOmega)
    println(res) // compare CS-XIVp153
  }
  */

  /** Executes a single round of transactions between the terms that can 
    * send / receive something to each other.
    *
    * Non-deterministic, deliberately randomized.
    * Does not attempt to reduce the term to the final form, it's just a single
    * round.
    *
    * @param s current state of the machine. Assumes that there are no `Par`s.
    * @return new state of the machine, number of new terms created in this
    * round.
    */
  def execTransactions[F[+_]]
    (s: List[F[Proc]])
    (implicit trace: Justification[F])
  : (List[F[Proc]], Int) = {
  
    import trace._
  
    // grouping terms according to the channels on which they can send / receive
    // messages. 
    //
    // Using mutable accumulators so we have to traverse the terms only once.
    import collection.mutable.{HashMap, HashSet}
    var inert = List.empty[F[Proc]]
    val channels = HashSet.empty[Name]
    val receiving = HashMap.empty[Name, List[F[Input]]]
    val sending = HashMap.empty[Name, List[F[Lift]]]
  
    s.foreach ( p => peek(p) match {
      case i @ Input(channelName, _) =>
        channels += channelName
        receiving(channelName) = 
          p.as[Input] :: receiving.getOrElseUpdate(channelName, Nil)
      case l @ Lift(channelName, _) => 
        channels += channelName
        sending(channelName) = 
          p.as[Lift] :: sending.getOrElseUpdate(channelName, Nil)
      case sthElse => inert ::= p
    })

    // perform all possible transactions in each pool
    val rnd = new util.Random
    val commResults: List[F[Proc]] = channels.iterator.flatMap({ chan => 
  
      val rcv = rnd.shuffle(receiving.get(chan).getOrElse(Nil))
      val snd = rnd.shuffle(sending.get(chan).getOrElse(Nil))
      val minSize = rcv.size min snd.size
      val (rcvActive, rcvIdle) = rcv.splitAt(minSize)
      val (sndActive, sndIdle) = snd.splitAt(minSize)
      val unchanged: List[F[Proc]] = if (rcvIdle.isEmpty) sndIdle else rcvIdle
      val newResults = 
        (rcvActive zip sndActive)
        .flatMap { case (rt, st) =>
          trace
          .map2(rt, st) { (r, s) =>
            semanticSubstitution(r.body, Quote.normalized(s.proc))
          }
          .explode {
            case Par(procs) => multisetExplode(procs)
            case sthElse => List(sthElse)
          }
        }
      unchanged ::: newResults
    }).toList
      
    val commResultsSize = commResults.size
    val inertSize = inert.size
    val newState: List[F[Proc]] = 
      if (inertSize < commResultsSize) inert ::: commResults
      else commResults ::: inert
    (newState, commResultsSize)
  }

  /** The core algorithm that runs a program to completion.
    * 
    * Repeatedly invokes `execTransactions` until the state does not change
    * any more, or until the number of iterations exceeds `maxIters`.
    *
    * Used in the implementation of various `Interpreter`s (use those to
    * set up the program and the VM and to run your programs).
    */
  def run[F[+_]: Justification](start: List[F[Proc]], maxIters: Int = 10000)
  : List[F[Proc]] = {
  
    var state = start
    for (i <- 0 until maxIters) {
      val (nextState, numNewTerms) = execTransactions(state)
      if (numNewTerms == 0) {
        return nextState // not `state`! Last step could collapse into `0`.
      }
      state = nextState
    }
  
    state
  }
}

/*
locally {
  println()
  println("Replication example:")
  val x = AstQuote(AstSymbol("x"))
  val f = AstQuote(AstSymbol("f"))
  val P = AstSymbol("P")
  val omega = AstInput(x, f, AstPar(AstPar(AstDrop(f), x(f)), P))
  val repP = AstPar(omega, AstLift(x, omega))

  // simulate few reduction steps
  var state = structurallyNormalize(repP)
  for (iter <- 0 until 10) {
    println(state)
    state = execTransactions(state)
  }
}

locally {
  println()
  println("Better, reusable replicator, independent of `P`:")
  val x = AstQuote(AstSymbol("x"))
  val y = AstQuote(AstSymbol("y"))
  val R = AstInput(x, y, AstPar(AstDrop(y), x(y)))
  val P = AstSymbol("P")
  val repP = AstPar(R, AstLift(x, AstPar(R, P)))

  var state = structurallyNormalize(repP)
  for (iter <- 0 until 10) {
    println(state)
    state = execTransactions(state)
  }
}

locally {
  println()
  println("Name normalization q-d-q-p -> qp experiment:")
  val P = AstSymbol("P")
  val x = AstQuote(AstSymbol("x"))
  val y = AstQuote(AstSymbol("y"))

  val t = AstPar(
    AstInput(x, y, AstLift(y, AstZero)),
    AstLift(x, AstDrop(AstQuote(P)))
  )

  val res = execTransactions(structurallyNormalize(t))
  println(res)
}

locally {
  println()
  println(
    "Reusable service that receives messages on port `p`" +
    " and then simply writes them to a fake `stdout` port:"
  )
  // CS-XIVp169
  def mkPort(name: String) = AstQuote(AstSymbol(name))
  val p = mkPort("p") // port on which the actual service listens
  val h = mkPort("h") // port on which service-respawner blocks and waits
  val r = mkPort("r") // internal usage of the respawner

  val m = mkPort("m") // local var used for "message" received by service
  val ign = mkPort("ign") // ignored local variable
  val y = mkPort("y") // local var used by the self-replicating `Q` below
  val stdout = mkPort("stdout") // fake stdout port to which service redirects

  val C = stdout(m) // the service simply redirects all requests to `stdout`
  val S = AstInput(p, m, C | h.lift(AstZero)) // listen, then serve & respawn
  val Q = AstInput(r, y, AstInput(h, ign, y.drop | r(y))) | S // paradoxical Q
  val R = AstInput(h, ign, Q | r.lift(Q))

  val server = S | R
  val requests = List(
    "hello, world",
    "hey, server",
    "what's up?"
  ).map(msg => p.lift(AstSymbol(msg))).reduce(_ | _)

  val t = requests | server

  var machineState = structurallyNormalize(t)
  println(machineState)
  for (i <- 0 until 30) {
    machineState = execTransactions(machineState)
  }
  println(machineState)
}
*/

object Edsl {
  implicit def string2symbol(s: String) = AstSymbol(s)

  private val rng = new util.Random

  /** Macro for generating fresh local variables. 
    *
    * It should be used everywhere a local var is needed to avoid any accidental 
    * capture by nested macros. Notice that it works only during compilation,
    * it's not suitable for producing new names at runtime, because at 
    * runtime all these random numbers are just frozen constants.
    *
    * Pure Rho-calculus can have names that correspond to random binary 
    * numbers, but it does not include any random number generators, so 
    * all the local variable names must be frozen before running the program.
    */
  def freshVar(suffix: String) = 
    &(rng.alphanumeric.take(10).mkString("","","$" + suffix))

  def &(p: AstProc): AstQuote = AstQuote(p)

  /** Same as `n.drop`. */
  def *(n: AstName): AstProc = AstDrop(n)

  implicit class AstProcOps(p: AstProc) {
    def | (q: AstProc): AstProc = AstPar(p, q)
  }

  val nil: AstProc = AstZero
  def __ = freshVar("ignored-local-variable")

  implicit class AstNameOps(n: AstName) {
    def receive(args: AstName*)(body: AstProc) = 
      if (args.size == 0) {
        body
      } else if (args.size == 1) {
        AstInput(n, args(0), body)
      } else {
        receiveMany(n, args.toList, body)
      }
    // TODO: cruft?
    // def receive(args: InputArgument*)(body: AstProc) = {
    //   receive(args.flatMap(_.receiveAsNames): _*)(body)
    // }
    /* Square brackets in the paper. */
    def sendName(y: AstName): AstProc = n ! *(y)
    /* Triangular chevron-like brackets in the paper. */
    def !(p: AstProc*): AstProc = 
      if (p.size == 1) {
        AstLift(n, p.head)
      } else if (p.size == 0) {
        nil
      } else {
        sendMany(n, p: _*)
      }
    // TODO: Cruft?
    // def !(args: Argument*): AstProc = this!(args.flatMap
    def drop: AstProc = AstDrop(n)
    /* Syntactic sugar for functional terms */
    def apply(args: FunctionalTerm*) = FunctionInvocation(n, args.toList)
  }

  /** Bunch of tiny processes that should be added to the initial soup
    * to enable a distributed "new-name" service.
    *
    * This is required for `_new` to work, which in turn is used by
    * contracts and functions and more or less everything else.
    */
  val news = "\u2780\u2781\u2782\u2783\u2784".map { c =>
    &("new") ! c.toString
  }.reduce(_ | _)

  // Same as the vararg-version, but shows more clearly what it does for a 
  // sigle name.
  //
  // def _new(x: AstName)(body: AstProc): AstProc = {
  //   &("new").receive(x){
  //     body | &("new") ! (x.drop | tallyMark)
  //   }
  // }

  /** Simulates the `new` construct from Pi calculus, creates fresh names
    * for multiple local variables.
    * 
    * Simply grabs one of the names that are being "sent" on the
    * `new` channel, immediately sends an updated name to the same channel,
    * and then proceeds with the next local variable.
    * Updating a name means adding a tally mark to it.
    */
  def _new(xs: AstName*)(body: AstProc): AstProc = {
    val tallyMark = AstSymbol("+")
    xs.foldLeft(body) { (inner, localVarName) =>
      &("new").receive(localVarName) {
        inner | &("new") ! (localVarName.drop | tallyMark)
      }
    }
  }

  private def sendMany(n: AstName, args: AstProc*): AstProc = {
    // CS-XVp66
    val c = freshVar("chan")
    val ack = freshVar("ack")
    _new(c) {
      n.sendName(c) | args.foldRight(nil) { (arg, inner) =>
        c.receive(ack) {
          ack ! (arg) |
          inner
        }
      }
    }
  }

  private def receiveMany(n: AstName, args: List[AstName], body: AstProc)
  : AstProc = {
    // CS-XVp66
    val c = freshVar("c")
    val a = freshVar("a")
    n.receive(c) {
      _new(a) {
        c.sendName(a) | args.foldRight(body) { (arg, inner) => 
          a.receive(arg) { inner }
        }
      }
    }
  }


  // TODO: failed "multi-name" arguments. Unclear what to do with them.
  // /** Base trait for derived entities that are sent as multiple ordered names.
  //   * 
  //   * Some derived constructs cannot be sent as a single name, they must be sent
  //   * as multiple names in a particular order. This trait helps create the 
  //   * illusion as if they are a single argument passed to functions / contracts.
  //   */
  // trait Argument {
  //   def sendAsProcs: List[AstProc]
  // }
  // 
  // trait InputArgument(name: List[AstName]) extends Argument {
  //   def receiveAsNames: List[AstName] = sendAsProcs.map(AstDrop(_))
  // }

  /** Registers a continuously running contract.
    * 
    * Can be used from inside other contracts and functions, but note that
    * these contracts never go away, and are not garbage collected.
    */
  def contract(port: AstName)(arg: AstName)(body: AstProc): AstProc = {
    // we need a fresh new port name for internal use by the replicator.
    // The replicator is a "paradoxically-spiraling" gizmo that continuously
    // reproduces the contract after every invocation.
    val r = freshVar("returnPort")
    _new(r) {
      val y = freshVar("y")                    // local variable for replicator
      val R = r.receive(y){ y.drop | r.sendName(y) } // replicator
      port.receive(arg){ body | R } | r !(port.receive(arg){body | R})
    }
  }

  /** Local variable name that should be captured by bodies of function 
    * definitions.
    */
  val Return = &("return")

  /** Declares a function.
    *
    * The name is `f`, `args` are the names of the arguments, `body` is the
    * function body. The last thing the function does should be sending the
    * result to channel `&("return")`, which is a local variable supplied by
    * this function definition macro.
    * 
    * The function stays forever as a contract in the global namespace.
    *
    * It should be called through the `call(f, args, cont)` method only,
    * don't try to invoke it on your own. Alternatively, use functional-term
    * syntactic sugar to construct more complex trees out of function invocations.
    */
  def fn(f: AstName)(args: AstName*)(body: AstProc): AstProc = {
    val fInvoc = freshVar("fInvoc")
    contract(f)(Return){
      _new(fInvoc) {
        args.foldRight(body){ (name, inner) => 
          Return.sendName(fInvoc) |
          fInvoc.receive(name){ inner }
        }
      }
    }
  }

  /** Calls function `f` with arguments `args` and then 
    * continues by sending the final result to `continuation`.
    *
    * The protocol is as follows:
    *
    * Communication with the function on channel `f` is initiated by
    * sending a fresh return channel `ret` to `f`. 
    * Then `f` responds by sending a fresh channel that corresponds 
    * to the concrete function invocation, call this channel `F`. 
    * To this `F`, arguments `a_1`, ..., `a_{n-1}` are sent synchronously,
    * and an acknowledgement sent back to `ret` after each 
    * argument.
    * After the last argument `a_{n}` is sent, the 
    * function invocation responds with the final result at `ret`.
    * The last thing the `ret` channel does is redirecting the final result 
    * to `continuation`.
    */
  def call(f: AstName, args: List[AstName], continuation: AstName): AstProc = {
    // CS-XVp55
    val ret = freshVar("ret")
    val result = freshVar("res")
    val argAcceptors = (1 to args.size).map(i => freshVar("F_" + i))
    _new(ret) {
      f.sendName(ret) |
      (args zip argAcceptors)
        .foldRight(ret.receive(result){ continuation.sendName(result) }) {
          case ((arg, argAcceptor), inner) => 
          ret.receive(argAcceptor) {
            argAcceptor.sendName(arg) | inner
          }
        }
    }
  }

  /** Syntactic sugar for a tree-like term of an embedded functional programming
    * language.
    *
    * Functional terms are things like for example `f(g(x, y), h(z))` where,
    * `f`, `g`, `h` are functions, and `x`, `y`, `z` are some values (which can
    * also be functions).
    *
    * A functional term on its own is not a process.
    * Only when combined with a return channel does it become a process.
    * The only thing a functional term can actually do is to send the evaluated
    * value to a channel - this is exactly what `returnTo` does. 
    */
  sealed trait FunctionalTerm {
    def returnTo(ret: AstName): AstProc
  }

  case class FunctionInvocation(f: AstName, args: List[FunctionalTerm])
  extends FunctionalTerm {
    /** Creates process that sends the result to the `ret` channel.
      */
    def returnTo(ret: AstName): AstProc = {
      // CS-XVp56
      val helperChannels: List[AstName] = (0 until args.size).map { i => 
        freshVar("$c-" + i)
      }(collection.breakOut)

      val helperVars: List[AstName] = (0 until args.size).map { i =>
        freshVar("$a-" + i)
      }(collection.breakOut)

      _new(helperChannels: _*) {
        val rcv = (helperChannels zip helperVars)
          .foldRight(call(f, helperVars, ret)) {
            case ((c, v), inner) => c.receive(v){inner}
          }
        val snd = (helperChannels zip args)
          .map { case (c, a) => a.returnTo(c) }
          .foldLeft(AstZero: AstProc)(_ | _)
        rcv | snd
      }
    }
  }

  case class ValueTerm(x: AstName) extends FunctionalTerm {
    def returnTo(ret: AstName): AstProc = ret.sendName(x)
  }

  implicit def nameAsValueTerm(n: AstName): FunctionalTerm = ValueTerm(n)

  // local helper variables for writing code with macros.
  // Immediately replaced by de Bruijn indices during compilation.
  private val X = &("x")
  private val Y = &("y")
  private val Z = &("z")

  // ============================================ Identity =====================
  val Identity = &("id")
  val IdentityFn = fn(Identity)(X) {
    Return.sendName(X)
  }

  // =========================================== Booleans ======================
  val True = &("true")
  val TrueFn = fn(True)(X, Y){ Return.sendName(X) }

  val False = &("false")
  val FalseFn = fn(False)(X, Y){ Return.sendName(Y) }

  val And = &("and")
  val AndFn = fn(And)(X, Y) { call(X, List(Y, False), Return) }
  val Or = &("or")
  val OrFn = fn(Or)(X, Y) { call(X, List(True, Y), Return) }
  val Not = &("not")
  val NotFn = fn(Not)(X) { call(X, List(False, True), Return) }

  val BooleanFns = TrueFn | FalseFn | AndFn | OrFn | NotFn

  implicit class ProcOps(p: Proc) {
    /** Helper method for dumping start/end state of the whole machine. */
    def toMultilineString: String = p match {
      case Par(procs) => 
        procs.map{ case (k, v) => s"${k} (${v}x)" }.toList.sorted.mkString("\n")
      case sthElse => sthElse.toString
    }
  }
}

def example[U](title: String)(body: => U): Unit = {
  println("\n" + title + ":")
  body
}

/** Helper method for inspecting final state of the simulation. 
  *
  */
def readoutChannel(state: List[Proc], plainName: String): List[Proc] = {
  state.collect{
    case Lift(Quote(Symbol(n)), x) if n == plainName => x
  }
}

def printBeforeAfter(s0: List[Proc], s1: List[Proc]): Unit = {
  import Edsl._
  println("-" * 50)
  s0 foreach println
  println("-" * 50)
  s1 foreach println
  println("results on `out`:")
  readoutChannel(s1, "out") foreach println
}

val Paper = "[Meredith, Radestock; 2005]"

/* All examples commented out for now, changing API everywhere.
example("printing the simplest names from Meredith's paper") {
  import Edsl._
  println(
    "Just printing some processes and names " +
    s"created from `O` (p.54 ${Paper}):"
  )
  val zeroName = &(nil)
  println(zeroName)
  val p2 = zeroName.sendName(zeroName)
  println(p2)
  val p3 = zeroName.receive(zeroName)(nil)
  println(p3)
  val n2 = &(p2)
  println(n2)
  val n3 = &(p3)
  println(n3)
}

example("Obtaining unique IDs from one of the `new`-pseudocontracts") {
  import Edsl._
  val requests = (1 to 11).map { i => 
    val x = &("x")
    _new(x) {
      &("req%02d".format(i)) ! x.drop
    }
  }.reduce(_ | _)
  val s0 = compile(news | requests)
  val s1 = simulate(s0)
  printBeforeAfter(s0, s1)
}

example("Simple Hello-World contract that" +
  " redirects everything to `out`-channel") {

  import Edsl._
  val name = mkPort("hello")
  val req = mkVar("req")
  val sysout = mkPort("out")

  // A contract that simply redirects all requests to `sysout`
  val c = contract(name)(req){ sysout.sendName(req) }
  val requests = 
    List("hello,", "world!", "za", "zb", "zz")
    .map(name ! _)
    .reduce(_ | _)
  val init = compile(news | c | requests)
  val fin = simulate(init)
  printBeforeAfter(init, fin)
}


example("Simple mutable cell with settable value " +
  "(with race condition on setter invocations)") {
  import Edsl._
  val cell = mkPort("cell") // state
  val set = mkPort("set")   // channel to which to send new value
  val writeAck = mkPort("writeAck")
  val v = mkVar("v")
  val initialCellState = cell ! nil

  val setter = contract(set)(v){
    cell.receive(__){ writeAck ! nil } | // erase old value
    writeAck.receive(__){ cell.sendName(v) }
  }

  val requests = List("42", "I win!", "racecond!")
    .map(set ! _)
    .reduce(_ | _)

  val s0 = compile(news | initialCellState | setter | requests)
  val s1 = simulate(s0)
  printBeforeAfter(s0, s1)
}

example("Call function that simply attaches 'tag' to its arguments") {
  import Edsl._
  val f = &("f")
  val x = &("x")
  val y = &("y")
  val fDef = fn(f)(x, y) {
    Return ! (x.drop | y.drop | "tag")
  }
  val fCall1 = call(f, List(&("foo"), &("bar")), &("out"))
  val fCall2 = call(f, List(&("hll"), &("wrl")), &("out"))
  val s0 = compile(news | fDef | fCall1 | fCall2)
  val s1 = simulate(s0)
  printBeforeAfter(s0, s1)
}

*/

/** Abstraction that allows to run simulations with different tracing modes,
  * from no tracing to full tracing of all predecessor terms.
  */
sealed trait Justification[F[+_]] { tc =>
  def root[X](x: X, cause: => String): F[X]
  def peek[X](fx: F[X]): X
  def comment[X](fx: F[X], comment: => String): F[X]
  /** This should be safe whenever `peek` returns element of `Y`. */
  def cast[X, Y <: X](fx: F[X]): F[Y] = fx.asInstanceOf[F[Y]]
  def map2[X, Y, Z](x: F[X], y: F[Y])(f: (X, Y) => Z): F[Z]

  // looks like sort of "cosequence", what is it, exactly?
  def explode[X, Y](fx: F[X])(e: X => List[Y]): List[F[Y]]

  implicit class JustificationOps[X](x: F[X]) {
    def peek = tc.peek(x)
    def comment(s: => String): F[X] = tc.comment(x, s)
    def as[Y <: X] = tc.cast[X, Y](x)
    def explode[Y](e: X => List[Y]): List[F[Y]] = tc.explode(x)(e)
  }
}

// `type Id[+X] = X` doesn't work.
// Funny looking type closure is workaround for this bug:
// https://issues.scala-lang.org/browse/SI-10140
implicit object NoJustification extends Justification[({ type I[+X] = X })#I] {
  def root[X](x: X, _ignored: => String): X = x
  def peek[X](fx: X): X = fx
  def comment[X](fx: X, _ignored: => String): X = fx
  def map2[X, Y, Z](x: X, y: Y)(f: (X, Y) => Z): Z = f(x, y)
  def explode[X, Y](fx: X)(e: X => List[Y]) = e(fx)
}

sealed trait Trace[+A]
case class RootCause[A](elem: A, cause: String) extends Trace[A]
case class Branch[A, X, Y](elem: A, fstCause: Trace[X], sndCause: Trace[Y]) 
  extends Trace[A]
case class Comment[A](comment: String, trace: Trace[A]) extends Trace[A]
case class Explode[A, B](
  elem: A,
  parent: Trace[B],
  childIdx: Int,
  numChildren: Int
) extends Trace[A]

implicit object Trace extends Justification[Trace] {
  def root[X](x: X, cause: => String): Trace[X] = RootCause(x, cause)
  def peek[X](tx: Trace[X]) = tx match {
    case RootCause(x, _) => x
    case Branch(x, _, _) => x
    case Comment(_, t) => peek(t)
    case Explode(x, _, _, _) => x
  }

  def comment[X](tx: Trace[X], comment: => String): Trace[X] =
    Comment(comment, tx)

  def map2[X, Y, Z](x: Trace[X], y: Trace[Y])(f: (X, Y) => Z): Trace[Z] =
    Branch(f(peek(x), peek(y)), x, y)

  def explode[X, Y](tx: Trace[X])(e: X => List[Y]): List[Trace[Y]] = {
    val cs = e(tx.peek)
    val numCs = cs.size
    cs.zipWithIndex.map { case (y, i) => Explode(y, tx, i, numCs) }
  }

  def dfsTraverse(roots: List[Trace[Any]])(
    onEnter: Trace[Any] => Unit,
    onExit: Trace[Any] => Unit,
    onPreviouslyVisited: Trace[Any] => Unit,
  ): Unit = {
    val visited = new java.util.IdentityHashMap[Trace[_], Unit]
    def dfs(t: Trace[_]): Unit = {
      if (visited.containsKey(t)) {
        onPreviouslyVisited(t)
      } else {
        visited.put(t, ())
        onEnter(t)
        t match {
          case RootCause(_, _) => { /* done */ }
          case Branch(_, a, b) => dfs(a); dfs(b)
          case Comment(_, x) => dfs(x)
          case Explode(_, p, _, _) => dfs(p)
        }
        onExit(t)
      }
    }
    for (r <- roots) dfs(r)
  }

  def renderAsHtml[X](
    traces: List[Trace[X]],
    renderLabel: Any => String = a => s"<code>${a.toString}</code>",
    extraHeadHtml: String = "",
    extraTailHtml: String = ""
  ): String = {
    val bldr = new StringBuilder
    bldr ++= """
      |<!DOCTYPE html>
      |<html>
      |<head>
      |  <meta charset="UTF-8">
      |  <style>
      |    div.node {
      |        display: block;
      |        margin: 1px;
      |        margin-left: 20px;
      |        border-color: #AAAAAA;
      |        border-width: 1px;
      |        border-style: solid;
      |        padding: 4px;
      |        background-color: #333333;
      |        color: #AAAACC;
      |    }
      |    div.label {
      |      background-color: black;
      |      color: white;
      |    }
      |    div.node:target > div.label {
      |      background-color: #AAFFBB;
      |    }
      |    .comment {
      |      color: #EEEEFF;
      |    }
      |    .daglink {
      |      color: #55FFFF;
      |    }
      |  </style>
      |  EXTRA_HEAD_HTML
      |</head>
      |<body>""".stripMargin.replaceAll("EXTRA_HEAD_HTML", extraHeadHtml)

    dfsTraverse(traces)(
      x => { 
        bldr ++= 
          s"<div class='node' id='${java.lang.System.identityHashCode(x)}'>"
        bldr ++= s"<div class='label'>${renderLabel(x.peek)}</div>"
        bldr ++= 
          "<p class='comment'>" + 
          (x match {
            case RootCause(_, c) => c
            case Branch(_, _, _) => "combine two"
            case Comment(_, c) => c
            case Explode(_, _, i, n) => 
              s"explode (${i + 1} out of ${n})"
          }) +
          "</p>"
      },
      x => { bldr ++= "</div>" },
      x => { 
        bldr ++= 
          "<div class='node'>" +
          s"""<a class='daglink' href='#${java.lang.System.identityHashCode(x)}'>""" +
          s"""<code>${x.peek}</code></a>""" +
          "(subtree already rendered)" +
          "</div>"
      }
    )

    bldr ++= """
      |</body>
      |EXTRA_TAIL_HTML
      |</html>""".stripMargin.replaceAll("EXTRA_TAIL_HTML", extraTailHtml)

    bldr.result
  }
}


trait Prog {
  def initialState[F[+_]](implicit justif: Justification[F]): List[F[Proc]]
  def run[F[+_]](i: Interpreter[F]): List[Proc] = {
    val s0 = initialState[F](i.justification)
    val s1 = i.interpret(s0)
    s1.map(i.justification.peek)
  }
}


/** Supplies `justification` to `Prog`, 
  * takes the constructed program, and runs it.
  */
trait Interpreter[F[+_]] {
  def justification: Justification[F]
  def interpret(s0: List[F[Proc]], maxIters: Int = 10000): List[F[Proc]]
}

object DefaultInterpreter extends Interpreter[({type I[+X] = X})#I] {
  def justification = NoJustification
  def interpret(s0: List[Proc], maxIters: Int = 10000): List[Proc] = {
    VM.run[({ type I[+X] = X })#I](s0, maxIters)(NoJustification)
  }
}

case class TracingInterpreter(traceFilePath: String = "/tmp/rhocalc_trace.html")
extends Interpreter[Trace] {
  def justification = Trace
  def interpret(
    s0: List[Trace[Proc]],
    maxIters: Int = 10000,
  ): List[Trace[Proc]] = {

    val traces = VM.run(s0, maxIters)

    // sort the `new`-"enzyme" so it appears later in the tree.
    val sortedProcesses = traces.sortBy { t => 
      justification.peek(t) match {
        case Lift(Quote(Symbol("out")), _) => 0
        case Lift(Quote(Symbol("new")), _) => 10
        case _ => 5
      }
    }

    val html = Trace.renderAsHtml[Proc](
      sortedProcesses,
      renderLabel = (a: Any) => {
        val code = a match {
          case p: Proc => RhocalcPrettyPrint.prettyPrint(p, 60)
          case sthElse => sthElse.toString
        }
        s"<pre><code>${code}</code></pre>"
      },
      extraHeadHtml = s"<title>${traceFilePath.split("/").last}</title>",
      extraTailHtml = RhocalcPrettyPrint.HighlightingJs
    )
    import java.nio.file.{Paths, Files}
    import java.nio.charset.StandardCharsets
    Files.write(
      Paths.get(traceFilePath),
      html.getBytes(StandardCharsets.UTF_8)
    )
    traces
  }
}

//   /** Same as `simulateDumpTrace`, but does not require any comments on
//     * the initial values (adds generic "start" comment to everything).
//     */
//   def simulateDumpTrace(
//     start: List[Proc],
//     iters: Int = 10000,
//     traceFilePath: String = "/tmp/rhocalc_trace.html",
//   ): List[Proc] = {
//     simulateDumpTrace(start.map(Trace.root(_, "start")), iters, traceFilePath)
//   }


/* Maybe reuse as tests...
locally {
  println()
  println("Examples of structurally normalized terms:")

  // some abbreviations
  val x = AstQuote(AstSymbol("x"))
  val y = AstQuote(AstSymbol("y"))
  val z = AstQuote(AstSymbol("z"))
  val P = AstSymbol("P")

  for (ex <- List(
    AstInput(x, y, AstPar(AstDrop(y), AstPar(x(y), P))),
    AstInput(x, z, AstPar(AstPar(P, AstDrop(z)), AstPar(x(z), AstZero))),
    AstInput(x, y, AstInput(x, z, AstPar(y(z), AstInput(z, z, y(z)))))
  )) {
    println(f"${ex}%40s -> ${structurallyNormalize(ex)}")
  }
}
*/

/*==============================================================================
                Pretty boring pretty printing & highlighting
==============================================================================*/
trait PrettyPrintable {
  def singleLineApparentWidth: Int
  def headerApparentWidth: Int

  /** Starting in column `col` of code at indent level `indent`, tries to
    * print the text in such a way that the apparent width does not exceed
    * `width`.
    *
    * @return layed out text, zero-based column index where the last line ends
    */
  def prettyPrint(col: Int, indent: Int, width: Int): (String, Int)

  def asSingleLine: String
}

object PrettyPrintable {
  val Tab = 2
  case class Atom(s: String, apparentWidth: Option[Int] = None)
  extends PrettyPrintable {
    def singleLineApparentWidth = apparentWidth.getOrElse(s.size)
    def headerApparentWidth = singleLineApparentWidth
    def prettyPrint(col: Int, _i: Int, _w: Int) = 
      (s, singleLineApparentWidth + col)
    def asSingleLine = s
  }
  case class DelimitedList(
    start: String,
    content: List[PrettyPrintable],
    end: String,
    apparentStartWidth: Option[Int] = None,
    apparentEndWidth: Option[Int] = None,
  ) extends PrettyPrintable {
    lazy val startWidth = apparentStartWidth.getOrElse(start.size)
    lazy val endWidth = apparentEndWidth.getOrElse(end.size)
    def singleLineApparentWidth = 
      startWidth + endWidth + content.map(_.singleLineApparentWidth).sum

    def asSingleLine = content.map(_.asSingleLine).mkString(start, "", end)

    def prettyPrint(col: Int, indent: Int, width: Int): (String, Int) = {
      val remaining = width - col
      if (remaining >= singleLineApparentWidth) {
        (asSingleLine, col + singleLineApparentWidth)
      } else {
        val lastLineApparentWidth = indent + endWidth
        val resultString = content.map(x => {
          " " * (indent + Tab) +
          x.prettyPrint(indent + Tab, indent + Tab, width)._1
        }).mkString(start + "\n", "\n", "\n" + " " * indent + end)

        (resultString, lastLineApparentWidth)
      }
    }

    def headerApparentWidth = startWidth
  }
  case class Juxtaposition(text: List[PrettyPrintable])
  extends PrettyPrintable {

    require(text.nonEmpty)

    def asSingleLine = text.map(_.asSingleLine).mkString
    def singleLineApparentWidth = text.map(_.singleLineApparentWidth).sum
    def prettyPrint(col: Int, indent: Int, width: Int): (String, Int) = {
      val bldr = new StringBuilder
      var currCol = col
      for (s <- text) {
        val w = s.singleLineApparentWidth
        if (currCol + w > width) {
          if (currCol + s.headerApparentWidth > width) {
            bldr += '\n'
            bldr ++= " " * indent
            val (pp, c) = s.prettyPrint(indent, indent, width)
            bldr ++= pp
            currCol = c
          } else {
            val (pp, c) = s.prettyPrint(currCol, indent, width)
            bldr ++= pp
            currCol = c
          }
        } else {
          // TODO: merge two branches?
          val (pp, c) = s.prettyPrint(currCol, indent, width)
          bldr ++= pp
          currCol = c
        }
      }
      (bldr.result, currCol)
    }
    def headerApparentWidth = text.head.headerApparentWidth
  }
}

object RhocalcPrettyPrint {

  private var globalGroupCounter = 0L
  private def nextGrp(): Long = { globalGroupCounter += 1; globalGroupCounter }

  import PrettyPrintable._

  def procToPrettyPrintable(p: Proc, grpEnv: List[Long] = Nil): PrettyPrintable = {
    p match {
      case Symbol(s) => Atom(s)
      case Input(chan, body) => {
        val binderGrp = nextGrp()

        val chanPP = nameToPrettyPrintable(chan, grpEnv)
        val binderPP = Atom(highlightSpan(binderGrp, "(?)."), Some(4))
        val bodyPP = procToPrettyPrintable(body, binderGrp :: grpEnv)
        Juxtaposition(List(chanPP, binderPP, bodyPP))
      }
      case Lift(chan, msg) => {
        val parenGrp = nextGrp()
        val chanPP = nameToPrettyPrintable(chan, grpEnv)
        val leftParPP = Atom(highlightSpan(parenGrp, "\u2989"), Some(1))
        val msgPP = procToPrettyPrintable(msg, grpEnv)
        val rightParPP = Atom(highlightSpan(parenGrp, "\u298A"), Some(1))
        Juxtaposition(List(chanPP, leftParPP, msgPP, rightParPP))
      }
      case Drop(n) => {
        val quoteGrp = nextGrp()
        val openQuote = Atom(highlightSpan(quoteGrp, "\u231D"), Some(1))
        val closeQuote = Atom(highlightSpan(quoteGrp, "\u231C"), Some(1))
        val content = nameToPrettyPrintable(n, grpEnv)
        Juxtaposition(List(openQuote, content, closeQuote))
      }
      case Par(bag) => {
        val childPPs = multisetExplode(bag).map{
          p => procToPrettyPrintable(p, grpEnv)
        }
        val separatedPPs = childPPs.head :: childPPs.tail.map { c =>
          Juxtaposition(List(Atom("|"), c))
        }
        val curlyGrp = nextGrp()
        DelimitedList(
          highlightSpan(curlyGrp, "{"),
          separatedPPs,
          highlightSpan(curlyGrp, "}"),
          apparentStartWidth = Some(1),
          apparentEndWidth = Some(1)
        )
      }
    }
  }

  def nameToPrettyPrintable(n: Name, grpEnv: List[Long] = Nil)
  : PrettyPrintable = {
    n match {
      case q @ Quote(p) => {
        val quoteGrp = nextGrp()
        val openQuote = Atom(highlightSpan(quoteGrp, "\u231C"), Some(1))
        val closeQuote = Atom(highlightSpan(quoteGrp, "\u231D"), Some(1))
        val content = procToPrettyPrintable(p)
        Juxtaposition(List(openQuote, content, closeQuote))
      }
      case b @ Bound(dbi) => {
        val visible = b.toString
        Atom(highlightSpan(grpEnv(dbi), visible), Some(visible.size))
      }
    }
  }

  /** JS snippet that highlights all elements with same `grp_N hovergrp` class 
    * whenever the mouse hovers over one of the elements belonging to
    * the group.
    */
  val HighlightingJs = """
    |<script>
    |  var groups = {};
    |  var hovergrp = document.getElementsByClassName("hovergrp"); 
    |  for (var i = 0; i < hovergrp.length; i++) {
    |    var e = hovergrp.item(i);
    |    var eClasses = e.classList;
    |    for (var j = 0; j < eClasses.length; j++) {
    |      var c = eClasses[j];
    |      if (c.startsWith("grp_")) {
    |        if (!groups[c]) {
    |          groups[c] = [];
    |        }
    |        groups[c].push(e);
    |        e.onmouseover = (function(c_capture) {
    |          return function(_event) {
    |            highlightGroup(c_capture, "#FFAA55");
    |          };
    |        })(c);
    |        e.onmouseout = (function(c_capture) {
    |          return function(_event) {
    |            highlightGroup(c_capture, "transparent");
    |          };
    |        })(c);
    |        break;
    |      }
    |    }
    |  }
    |  
    |  function highlightGroup(groupName, color) {
    |    var g = groups[groupName];
    |    for (var i = 0; i < g.length; i++) {
    |      g[i].style.backgroundColor = color;
    |    }
    |  }
    |
    |</script>
    |""".stripMargin

  def highlightSpan(grpIdx: Long, content: String): String = {
    val r = "%02x".format(20 + (grpIdx * 17 % 235))
    val g = "%02x".format(20 + ((grpIdx + 127) * 103 % 235))
    val b = "%02x".format(20 + ((grpIdx + 64) * 37 % 235))
    val color = s"#$r$g$b"
    s"<span class='grp_${grpIdx} hovergrp'" + 
    s" style='color: ${color};'>${content}</span>"
  }

  def prettyPrint(p: Proc, width: Int): String = {
    procToPrettyPrintable(p).prettyPrint(0, 0, width)._1
  }
}

/*==============================================================================
                          Examples
==============================================================================*/

example("True in isolation") {
  val p = new Prog {
    def initialState[F[+_]](implicit j: Justification[F]) = {
      import j._
      import Edsl._
      val c = call(True, List(&("a"), &("b")), &("out"))
      compile(
        root(news, "distributed `new` service, present at start"),
        root(TrueFn, "true function def, present at start"),
        root(c, "original function call `True(a, b)`"),
      )
    }
  }
  val finalState = p.run(TracingInterpreter("/tmp/true_isolation_trace.html"))
  readoutChannel(finalState, "out") foreach println
}

example("Boolean function application `Not False`") {
  val p = new Prog {
    def initialState[F[+_]](implicit j: Justification[F]) = {
      import Edsl._
      import j._
      val functionCall = Not(False).returnTo(&("out"))
      compile(
        root(news, "`new` service"),
        root(NotFn, "`Not` definition"),
        root(TrueFn, "`True` definition"),
        root(FalseFn, "`False` definition"),
        root(functionCall, "initial (Not(True)) function call")
      )
    }
  }
  // val s1 = p.run(TracingInterpreter("/tmp/not_false_trace.html"))
  val s1 = p.run[({type I[+X] = X})#I](DefaultInterpreter)
  readoutChannel(s1, "out") foreach println
}

example("Applying identity function twice") {
  val p = new Prog {
    def initialState[F[+_]](implicit j: Justification[F]) = {
      import Edsl._
      import j._
      val functionCall = Identity(Identity(&("42"))).returnTo(&("out"))
      compile(
        root(news, "news service"),
        root(IdentityFn, "Identity def"),
        root(functionCall, "initial function call I(I(42))")
      )
    }
  }
  // val s1 = p.run(TracingInterpreter("/tmp/id_id.html"))
  val s1 = p.run[({type I[+X] = X})#I](DefaultInterpreter)
  readoutChannel(s1, "out") foreach println
}

example("Boolean function, double negation `Not (Not True)`") {
  val p = new Prog {
    def initialState[F[+_]](implicit j: Justification[F]) = {
      import Edsl._
      import j._
      val functionCall = Not(Not(True)).returnTo(&("out"))
      compile(
        root(news, "`new` service"),
        root(NotFn, "`Not` definition"),
        root(TrueFn, "`True` definition"),
        root(FalseFn, "`False` definition"),
        root(functionCall, "initial function call")
      )
    }
  }
  //val s1 = p.run(TracingInterpreter("/tmp/double_neg_trace.html"))
  val s1 = p.run[({type I[+X] = X})#I](DefaultInterpreter)
  readoutChannel(s1, "out") foreach println
}

example("Boolean function `And(Not(False), True)`") {
  val p = new Prog {
    def initialState[F[+_]](implicit j: Justification[F]) = {
      import Edsl._
      import j._
      val functionCall = And(Not(False), True).returnTo(&("out"))
      compile(
        root(news, "`new` service"),
        root(BooleanFns, "boolean functions 'package'"),
        root(functionCall, "initial function call")
      )
    }
  }
  //val s1 = p.run(TracingInterpreter("/tmp/double_neg_trace.html"))
  val s1 = p.run[({type I[+X] = X})#I](DefaultInterpreter)
  readoutChannel(s1, "out") foreach println
}

example("Boolean function `And(Or(False, True), Or(And(False, True), True))`") {
  val p = new Prog {
    def initialState[F[+_]](implicit j: Justification[F]) = {
      import Edsl._
      import j._
      val functionCall = 
        And(Or(False, True), Or(And(False, True), True)).returnTo(&("out"))
      compile(
        root(news, "`new` service"),
        root(BooleanFns, "boolean functions 'package'"),
        root(functionCall, "initial function call")
      )
    }
  }
  val s1 = p.run(TracingInterpreter("/tmp/andorftorandftt.html"))
  // val s1 = p.run[({type I[+X] = X})#I](DefaultInterpreter)
  readoutChannel(s1, "out") foreach println
}
