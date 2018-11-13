import scala.collection.mutable.ListBuffer
import scala.tools.nsc._

class FBound[A <: FBound[A]]

class Bounded[A <: String, B <: A]

class Bounded1[A <: Bounded[_, _]]

trait Foo1[M <: String, P <: Foo1[M, _]]
trait Foo2[M <: String, P <: Foo2[M, P]]

class Entity[A] {

  class Inner

  type C = Option[Inner]
}

object ScratchMain {
  def main(args: Array[String]): Unit = {
    new Scratch().test()
  }
}

class Scratch {
  val global = new Global(new Settings)
  import global._

  global.settings.usejavacp.value = true
  new Run

  val infer = analyzer.newTyper(analyzer.NoContext).infer
  def check(expected: String, tp: Type): Unit = {
    val approximated = approximate(tp)
    if (expected != approximated.toString())
      throw new AssertionError(s"Expected $expected, found $approximated")
    // Perform the same bounds checking as refchecks
    checkAllBounds(approximated)
  }

  def test(): Unit = {
    exitingTyper {
      check("Bounded[String,String]", typeOf[Bounded[_, _]])
      check("Bounded1[Bounded[String,String]]", typeOf[Bounded1[_]])
      check("FBound[FBound[_0]] forSome { type _0 }", symbolOf[FBound[_]].initialize.tpe_*)
      check("Foo1[String,Foo1[String,_0]] forSome { type _0 }", typeOf[Foo1[_, _]])
      check("Foo2[String,Foo2[String,Foo2[String,_0]]] forSome { type _0 }", typeOf[Foo2[_, _]])


      check("Bounded[String,String]", symbolOf[Bounded[_, _]].initialize.tpe_*)
      check("Option[Entity[Any]#Inner]", typeOf[Entity[Any]].decl(TypeName("C")).info)

      check("Foo1[String,Foo1[String,_0]] forSome { type _0 }", symbolOf[Foo1[_, _]].initialize.tpe_*)
      check("Foo2[String,Foo2[String,_0]] forSome { type _0 }", symbolOf[Foo2[_, _]].initialize.tpe_*)
    }
    assert(!reporter.hasErrors)
  }

  def approximate(tp: Type): Type = {
    val newExistentials = collection.mutable.LinkedHashMap[Symbol, Symbol]()
    var eid: Int = 0

    def newExistentialFor(sym: Symbol): Symbol = {
      newExistentials.get(sym) match {
        case Some(esym) => esym
        case _ =>
          val existential = NoSymbol.newExistential("_" + eid).setInfo(TypeBounds.empty)
          eid += 1
          newExistentials(sym) = existential
          existential
      }
    }

    val map = new TypeMap(trackVariance = true) {

      case class AppliedParam(pre: Type, tparam: Symbol, arg: Type, detectedFBound: Boolean)

      val tparamStack = collection.mutable.ArrayStack[AppliedParam]()
      val abstractTypeStack = collection.mutable.ArrayStack[(Type, Symbol)]()
      val eliminatedExistentials = collection.mutable.Set[Symbol]()

      override def apply(tp: Type): Type = tp match {
        case TypeRef(ThisType(parentSym), sym, args) if !parentSym.isStaticOwner =>
          // Convert `Hidden.this.Inner` to `Hidden#Inner`
          apply(TypeRef(parentSym.tpe, sym, args))
        case tr@TypeRef(pre, sym, Nil) if sym.isExistential && tr.bounds.isEmptyBounds =>
          tparamStack.headOption match {
            case Some(AppliedParam(pre, tparam, `tr`, detectedFBound)) =>
              eliminatedExistentials += sym
              if (detectedFBound) TypeRef(NoPrefix, newExistentialFor(tparam), Nil)
              else {
                val bound = if (variance.isContravariant) tparam.info.bounds.lo else tparam.info.bounds.hi
                val tp1 = bound.asSeenFrom(pre, tparam.owner)
                if (tp1 ne tr) apply(tp1) else tp1
              }
            case _ =>
              mapOver(tr)
          }
        case tr@TypeRef(pre, sym, Nil) if sym.isAbstractType =>
          abstractTypeStack.find(_._2 eq sym) match {
            case Some((pre, sym)) =>
              TypeRef(NoPrefix, newExistentialFor(sym), Nil)
            case None =>
              abstractTypeStack.push((pre, sym))
              try {
                val bound = if (variance.isContravariant) sym.info.bounds.lo else sym.info.bounds.hi
                val tp1 = bound.asSeenFrom(pre, sym.owner)
                if (tp1 ne tr) apply(tp1) else tp1
              } finally abstractTypeStack.pop()
          }
        case tr@TypeRef(pre, sym, args) =>
          val pre1 = apply(pre)
          val args1 = mapOverArgs(pre, args, sym.typeParams)
          if ((pre1 eq pre) && (args1 eq args)) tp
          else copyTypeRef(tp, pre1, tr.coevolveSym(pre1), args1)
        case ExistentialType(qs, underlying) =>
          mapOver(tp) match {
            case ExistentialType(qs1, underlying1) if qs1.exists(eliminatedExistentials.contains) =>
              // Clean up the resulting type by removing existential quantifers that are not referenced in the underlying type.
              existentialAbstraction(qs1, underlying1)
            case tp => tp
          }
        case _ => mapOver(tp)
      }
      private def mapOverArgs(pre: Type, args: List[Type], tparams: List[Symbol]): List[Type] = {
        map2Conserve(args, tparams) { (arg, tparam) =>
          val detectedFBound = tparamStack.exists(_.tparam eq tparam)
          tparamStack.push(AppliedParam(pre, tparam, arg, detectedFBound))
          try withVariance(variance * tparam.variance)(this (arg))
          finally tparamStack.pop()
        }
      }
    }
    val approximated = map(tp)
    // Wrap the approximated result in an ExistentialType if fresh quantified symbols have been created.
    // Note that the `newExistentialType` constructor collapses `ExistentialType(ExistentialType(...)`.
    newExistentialType(newExistentials.valuesIterator.toList, approximated)
  }

  // START COPY/PASTE from refchecks
  def checkAllBounds(tp: Type): Unit = {
    val existentialParams = new ListBuffer[Symbol]
    var skipBounds = false
    // check all bounds, except those that are existential type parameters
    // or those within typed annotated with @uncheckedBounds
    tp foreach {
      case tp@ExistentialType(tparams, tpe) =>
        existentialParams ++= tparams
      case tp: TypeRef =>
        val tpWithWildcards = deriveTypeWithWildcards(existentialParams.toList)(tp)
        checkTypeRef(tpWithWildcards, EmptyTree, skipBounds)
      case _ =>
    }
  }

  private def checkTypeRef(tp: Type, tree: Tree, skipBounds: Boolean) = tp match {
    case TypeRef(pre, sym, args) =>
      if (sym.isJavaDefined)
        sym.typeParams foreach (_.cookJavaRawInfo())
      if (!tp.isHigherKinded && !skipBounds)
        infer.checkBounds(tree, pre, sym.owner, sym.typeParams, args, "")
    case _ =>
  }

  // END COPY/PASTE from refchecks

}
