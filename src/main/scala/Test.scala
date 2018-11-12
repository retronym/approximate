import scala.tools.nsc._
import scala.collection.mutable.ListBuffer

class FBound[A <: FBound[A]]

object ScratchMain {
  def main(args: Array[String]): Unit = {
    new Scratch().test()
  }
}

class Scratch {
  val global = new Global(new Settings)
  import global._

  global.settings.usejavacp.value = true
  global.settings.debug.value = true
  new Run

  val infer = analyzer.newTyper(analyzer.NoContext).infer

  def test(): Unit = {
    exitingTyper {
      val symbol = symbolOf[FBound[_]]
      symbol.initialize
      val input = symbol.tpe_*
      println(input)
      val result = new AbstractToBoundsMap(symbol.asClass).apply(input)
      checkAllBounds(result)
    }
    assert(!reporter.hasErrors)
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
      if(sym.isJavaDefined)
        sym.typeParams foreach (_.cookJavaRawInfo())
      if (!tp.isHigherKinded && !skipBounds)
        infer.checkBounds(tree, pre, sym.owner, sym.typeParams, args, "")
    case _ =>
  }
  // END COPY/PASTE from refchecks


  private class AbstractToBoundsMap(eeSym: ClassSymbol) extends TypeMap(trackVariance = true) {
    import scala.collection.mutable

    // the (prefix, type param symbol) that correspond to encountered existential quantifiers
    private val existentialTparams = mutable.HashMap[Symbol, (Type, Symbol)]()
    // prevent infinite recursion over recursive types
    private val seen = mutable.HashMap[Symbol, Type]()

    private val newExistentials = mutable.HashMap[Symbol, Symbol]()

    override def apply(tp: Type): Type = {
      val newType = tp match {
        case tr@TypeRef(pre, sym, args) =>
          foreach2(sym.typeParams, args) { (tparam, arg) =>
            if (arg.typeSymbolDirect.isExistential)
              existentialTparams(arg.typeSymbolDirect) = (pre, tparam)
          }

          if (sym.isAbstractType || sym.isExistential) {
            seen.get(sym) match {
              case None =>
                // we've not seen this symbol before
                seen(sym) = NoType

                def boundOf(tp: Type): Type = if (variance.isContravariant) tp.bounds.lo else tp.bounds.hi

                val bound = if (sym.isExistential && existentialTparams.contains(sym)) {
                  val (pre, tparam) = existentialTparams(sym) // TODO probably limit this to the case when tparam.info.bounds = (Nothing, Any)
                  boundOf(tparam.info).asSeenFrom(pre, tparam.owner)
                } else boundOf(tp)

                val ret =
                  if (bound ne tp) apply(bound) // recurse to unpeel layers of abstract types
                  else mapOver(project(bound))

                // memoise the result of this type transformation
                seen(sym) = ret
                ret
              case Some(NoType) =>
                // we're in the middle of recursing over this type, so short-circuit to avoid infinite recursion
                newExistentials
                  .getOrElseUpdate(sym, {
                    sym.owner.freshExistential("", newExistentials.size).setInfo(TypeBounds.empty)
                  })
                  .tpe
              case Some(t) =>
                // we've seen (and fully resolved) this type before, so just return the memoised result
                t
            }

          } else mapOver(tr)
        case t =>
          mapOver(t)
      }

      // if we've short circuited lower down, then we need to wrap all the way back up with ExistentialType
      if (newExistentials.nonEmpty && !newType.typeSymbol.isExistential) {
        newType match {
          case ExistentialType(quantified, underlying) =>
            ExistentialType((quantified ::: newExistentials.values.toList).distinct, underlying)
          case t =>
            ExistentialType(newExistentials.values.toList, t)
        }
      } else {
        newType
      }
    }

    // Convert MyEntity.this.Inner to MyEntity#Inner
    private def project(tp: Type) = tp match {
      case TypeRef(ThisType(parentSym), sym, args) if parentSym.ownerChain.contains(eeSym) =>
        TypeRef(parentSym.tpe, sym, args)
      case _ =>
        tp
    }
  }
}
