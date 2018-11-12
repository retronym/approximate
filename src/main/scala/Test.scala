import scala.collection.mutable.ListBuffer
import scala.tools.nsc._

class FBound[A <: FBound[A]]

class Bounded[A <: String, B <: A]

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
  def assertEquals(expected: String, tp: Type): Unit = {
    if (expected != tp.toString()) throw new AssertionError(s"Expected $expected, found $tp")
  }

  def test(): Unit = {
    exitingTyper {
      assertEquals("FBound[FBound[_0]] forSome { type _0 }", packAndApproximate(symbolOf[FBound[_]].initialize.tpe_*, symbolOf[FBound[_]]))
      assertEquals("Bounded[String,String]", packAndApproximate(symbolOf[Bounded[_, _]].initialize.tpe_*, symbolOf[Bounded[_, _]]))
      assertEquals("Option[Entity[A]#Inner]", packAndApproximate(typeOf[Entity[Any]].decl(TypeName("C")).info, symbolOf[Entity[_]]))
    }
    assert(!reporter.hasErrors)
  }

  /**
    * Compute an existential type from hidden symbols that have `owner` as a transtive owner and type `tp`.
    * @param ownerOfHidden    The symbol enclosing the symbols that must be existentially abstracted
    * @param tp               The original type
    */

  def pack(tp: Type, ownerOfHidden: Symbol) = {
    var hidden: List[Symbol] = Nil
    val seen = collection.mutable.Set[Symbol]()
    for (t <- tp) {
      val bts = t.baseTypeSeq.toList
      for (b <- bts) {
        for (t <- b) {
          val sym = t.typeSymbolDirect
          if (sym.hasTransOwner(ownerOfHidden) && sym != ownerOfHidden) {
            if (!seen(sym)) {
              seen += sym
              hidden ::= sym
            }
          }
        }
      }
    }
    packSymbols(hidden, tp)
  }

  def packAndApproximate(tp: Type, hiddenOwner: Symbol): Type = {
    val packed = pack(tp, hiddenOwner)
    val newExistentials = collection.mutable.LinkedHashMap[Symbol, Symbol]()
    var eid: Int = 0
    def newExistentialFor(sym: Symbol): Symbol ={
      newExistentials.get(sym) match {
        case Some(esym) => esym
        case _ =>
          val existential = NoSymbol.newExistential("_" + eid).setInfo(TypeBounds.empty)
          eid += 1
          newExistentials(sym) = existential
          existential
      }
    }
    // Approximate existentials by the variance-appropriate bound. F-Bounded existentials are unpeeled
    // once before resorting to a fresh, unbounded existential argument.
    val approximateExistentials: TypeMap = new TypeMap(trackVariance = true) {
      var boundStack: List[Symbol] = Nil
      override def apply(tp: Type): Type = tp match {
        case TypeRef(ThisType(parentSym), sym, args) if parentSym.hasTransOwner(hiddenOwner) =>
          // Convert `Hidden.this.Inner` to `Hidden#Inner`
          apply(TypeRef(parentSym.tpe, sym, args))
        case tr: TypeRef if tr.sym.isExistential =>
          if (boundStack.contains(tr.sym)) {
            TypeRef(NoPrefix, newExistentialFor(tr.sym), Nil)
          } else {
            boundStack ::= tr.sym
            try {
              val bound = if (variance.isContravariant) tp.bounds.lo else tp.bounds.hi
              mapOver(bound)
            } finally
              boundStack = boundStack.tail
          }
        case _ => mapOver(tp)
      }
    }
    val approximated = approximateExistentials.apply(packed)
    // Wrap the approximated result in an ExistentialType if fresh quantified symbols have been created.
    // Note that the `newExistentialType` constructor collapses `ExistentialType(ExistentialType(...)`.
    val wrapped = newExistentialType(newExistentials.valuesIterator.toList, approximated)
    val result = wrapped match {
      case et: ExistentialType =>
        // Clean up the resulting type by removing existential quantifers that are not referenced in the underlying
        // type.
        existentialAbstraction(et.quantified, et.underlying)
      case tp => tp
    }
    checkAllBounds(result)
    result
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
