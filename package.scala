/**
  * *****************************************************************************
  * OscaR is free software: you can redistribute it and/or modify
  * it under the terms of the GNU Lesser General Public License as published by
  * the Free Software Foundation, either version 2.1 of the License, or
  * (at your option) any later version.
  *
  * OscaR is distributed in the hope that it will be useful,
  * but WITHOUT ANY WARRANTY; without even the implied warranty of
  * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  * GNU Lesser General Public License  for more details.
  *
  * You should have received a copy of the GNU Lesser General Public License along with OscaR.
  * If not, see http://www.gnu.org/licenses/lgpl-3.0.en.html
  * ****************************************************************************
  */

package oscar
import oscar.algo.search.{DFSLinearizer, DFSearchListener, DFSearchNode}
import oscar.algo.reversible.{ReversibleInt, ReversibleSparseBitSet}
import oscar.cp.CPIntVarOps
import oscar.cp.constraints.InSet
import oscar.cp.core.{CPPropagStrength, CPStore, Constraint}
import oscar.cp.constraints.ModuloLHS
import oscar.cp.constraints.tables.TableCT
import oscar.cp.core.variables.{CPBoolVarImpl, CPIntVar, CPIntVarViewMinus}
import oscar.cp.modeling.Branchings
import oscar.cp.modeling.CPSolverUtils
import oscar.cp.modeling.Constraints
import oscar.cp.modeling.ElementBuilder
import oscar.cp.modeling.LNSRelaxations
import oscar.util.selectMin

import scala.collection.mutable.ArrayBuffer

/**
  * The `cp` package provides useful functionalities to model problem using
  * the OscaR Constraint Programming Library.
  *
  * === Commonly Used Types ===
  * This package provides type aliases for types which are commonly used,
  * such as `CPSolver`, `CPIntVar`, or `CPIntervalVar`.
  *
  * === Implicit Conversions ===
  * A number of commonly applied implicit conversions are also defined here.
  * Implicit conversions provide additional higher-order functions to core classes
  * such as `CPIntVar`, `CPIntervalVar`, or `CPSolver`. Implicit conversion also provide
  * simple and natural modeling functionalities for sum and element constraints.
  *
  * === CPModel ===
  * The `CPModel` trait is also defined in this package and provides users with an
  * implicit `CPSolver` named solver. The use of `CPModel` allows users to model
  * problems without considering the underlying solver.
  *
  * @author Pierre Schaus pschaus@gmail.com
  * @author Renaud Hartert ren.hartert@gmail.com
  */
package object cp extends Constraints with Branchings with ElementBuilder with CPSolverUtils with LNSRelaxations {
  // Alias to useful classes and companion objects

  type CPIntVar = oscar.cp.core.variables.CPIntVar
  final val CPIntVar = oscar.cp.core.variables.CPIntVar

  type CPBoolVar = oscar.cp.core.variables.CPBoolVar
  final val CPBoolVar = oscar.cp.core.variables.CPBoolVar

  type CPSetVar = oscar.cp.core.variables.CPSetVar
  final val CPSetVar = oscar.cp.core.variables.CPSetVar

  type CPGraphVar = oscar.cp.core.variables.CPGraphVar
  final val CPGraphVar = oscar.cp.core.variables.CPGraphVar

  type CPStore = oscar.cp.core.CPStore
  final val CPStore = oscar.cp.core.CPStore

  type CPSolver = oscar.cp.core.CPSolver
  final val CPSolver = oscar.cp.core.CPSolver

  type Constraint = oscar.cp.core.Constraint

  type NoSolutionException = oscar.cp.core.NoSolutionException

  trait CPModel { implicit val solver: CPSolver = CPSolver() }

  /**
    * Filtering power can be specified for some of the constraints.
    * The default filtering is Weak.
    */
  val Strong = CPPropagStrength.Strong
  val Medium = CPPropagStrength.Medium
  val Weak = CPPropagStrength.Weak

  object TightenType extends Enumeration {
    val WeakTighten = Value("weak tighten")
    val StrongTighten = Value("strong tighten")
    val NoTighten = Value("no tighten")
    val MaintainTighten = Value("maintain tighten")
  }
  import TightenType._

  // TODO Dangerous implicits
  implicit def convert2(vals: IndexedSeq[Int]) = vals.toArray[Int]
  implicit def indexed2Array(x: IndexedSeq[CPIntVar]) = x.toArray[CPIntVar]
  implicit def args2Array(x: CPIntVar*) = x.toArray[CPIntVar]
  implicit def indexed2ArrayBool(x: IndexedSeq[CPBoolVar]) = x.toArray[CPBoolVar]
  implicit def args2ArrayBool(x: CPBoolVar*) = x.toArray[CPBoolVar]

  // TODO Should move to oscar.cp.util
  implicit def arrayVar2IterableVarOps(s: Array[CPIntVar]) = new IterableVarOps(s)
  implicit class IterableVarOps(val seq: Iterable[CPIntVar]) extends AnyVal {
    /** @return true is all the variables are bound */
    def areBound: Boolean = seq.forall(_.isBound)

    /** @return one unbound variable with minimum domain (randomly chosen is several of them) */
    def minDomNotBound: CPIntVar = {
      val res: Option[(CPIntVar, Int)] = selectMin(seq.zipWithIndex)(x => !x._1.isBound)(y => (y._1.size, y._2))
      res match {
        case Some((x, i)) => x
        case None         => throw new java.util.NoSuchElementException("no unbound var")
      }
    }

    /** @return the maximum value taken a bound variable or v if no variable is bound */
    def maxBoundOrElse(v: Int): Int = {
      val res: Option[CPIntVar] = selectMin(seq)(_.isBound)(-_.value)
      res match {
        case Some(x) => x.value
        case None    => v
      }
    }
  }

  //class LeSymbolic(val x: CPIntVarOps,val y : CPIntVarOps)

  //implicit def LeSymbolicToConstraint(cons: LeSymbolic): Constraint =  new oscar.cp.constraints.Le(cons.x.x, cons.y.x)

  //implicit def LeSymbolicToBoolean(cons: LeSymbolic): CPBoolVar =  cons.x.x.isLeEq(cons.y.x - 1)

  object CPIntVarOps {
    var mapcount = scala.collection.mutable.Map[Int, scala.collection.mutable.Map[Int, Array[Int]]]()
    var mapVarVal = scala.collection.mutable.Map[Int, Int]()
    var mapVarSD = scala.collection.mutable.Map[Int, Float]()
  }


  //  mapsup foreach (mapsup => print(" map : " + mapsup._1+ "==>" + mapsup._2.toList + "\n") )
  //  mapCons foreach (mapCons => print(" cons: " + mapCons._1 + " ==> " + mapCons._2.toList+ "\n"))
  implicit class CPIntVarOps(val x: CPIntVar) {
    def changeCount(supCount: Array[Int], idvar:Int, idconst:Int): Unit ={
      print("supcount : " + supCount.toList + " idvar : " + idvar + " idconst : " + idconst )
      CPIntVarOps.mapVarSD.remove(idvar)
      CPIntVarOps.mapVarVal.remove(idvar)
      var mapCons = scala.collection.mutable.Map[Int, Array[Int]]()
        // if the variable key exists
        if(CPIntVarOps.mapcount.get(idvar) != None ) {
          mapCons = CPIntVarOps.mapcount (idvar)
        }
        mapCons = mapCons + (idconst -> supCount)
        mapCons foreach (mapCons => print(" cons: " + mapCons._1 + " ==> " + mapCons._2.toList + "\n"))
        CPIntVarOps.mapcount = CPIntVarOps.mapcount + (idvar -> mapCons)  //save the map created in CPIntVarOps
    }

//        def changeCount(supCount: Array[Int], idvar:Int, idconst:Int): Unit ={
////          print(" changeCount " + supCount.toList)
//          if(!supCount.isEmpty){
//            var mapsup = scala.collection.mutable.Map[Int, Array[Int]]()
//            var mapCons = CPIntVarOps.mapcount
//            // if the constraint key exist
//            if(CPIntVarOps.mapcount.get(idconst) != None ) {
//              mapsup = CPIntVarOps.mapcount (idconst)
//            }
//            mapsup = mapsup + (idvar -> supCount)
//            mapCons = mapCons + (idconst -> mapsup)
////            mapsup foreach (mapsup => print(" map : " + mapsup._1+ "==>" + mapsup._2.toList + "\n") )
////            mapCons foreach (mapCons => print(" cons: " + mapCons._1 + " ==> " + mapCons._2 + "\n"))
//            CPIntVarOps.mapcount = mapCons  //save the map created in CPIntVarOps
//          }
//        }

//        def varCountSearchSD: Float = {
//          var sumSC = 0
//          var sumSC1 = 0
//          var SD = 0f
//          var SDTest = 0f
//          var maxCount = -1
//          var maxCount1 = -1 // initialization of the maxcount
//          var mapCons = CPIntVarOps.mapcount                                  // map of constraint to (map of variable to supcount)
//          mapCons foreach (mapCons => {                                       // loop on every constraints
//            var supCount = mapCons._2.getOrElse (x.hashCode(), Array ())    // get the correct supcount (empty if doesn't exist)
////            print(" mapCons._1 " + mapCons._1)
//            print(" variable_hash-code " + x.hashCode() + " variable " + x.toList + " support count " + supCount.toList)
//            if (!supCount.isEmpty && supCount.max >= maxCount) {
////              print(" %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% " +"\n")
//              maxCount = (x.toArray collect supCount).max
//              sumSC = (x.toArray collect supCount).sum
//              maxCount1 = supCount.max
//              sumSC1 = supCount.sum
//              if(sumSC !=sumSC1){
//
//                print(" sumsc " + sumSC + sumSC1 +" $$$$$$$$$$$$$$ " +"\n")
//              }
//              SDTest = maxCount.toFloat / sumSC.toFloat                    // probability to search on this var
//              if (SDTest > SD) {                                              // condition to find the maximum
//                SD = SDTest                                                   // assign the maximum
//                CPIntVarOps.mapVarVal = CPIntVarOps.mapVarVal + (x.hashCode () -> supCount.indexOf(maxCount)) // change the map of var to constraint
//                CPIntVarOps.mapVarCons = CPIntVarOps.mapVarCons + (x.hashCode() -> mapCons._1)
//              }
//            }
//          })
//          print(" variable_hash-code " + x.hashCode()+ " solution_density " + SD + "\n")
//          SD                                                                  // return the probability
//        }

    def varCountSearchSD: Float = {
      var SD = 0f
      var SDTest = 0f
//      var maxCount = -1
      var mapCons = CPIntVarOps.mapcount.getOrElse(x.hashCode(),scala.collection.mutable.Map[Int, Array[Int]]() )
      // map of variable to (map of constraint to supcount)
      mapCons foreach (mapCons => {                                       // loop on every variable
        val supCount = mapCons._2                                         // get the correct supcount
//        print(" variable_hash-code " + x.hashCode() + " variable " + x.toList + " support count " + supCount.toList + "\n")
          SDTest = supCount.max.toFloat / supCount.sum.toFloat                    // probability to search on this var
          if (SDTest > SD) {                                              // condition to find the maximum
            SD = SDTest                                                   // assign the maximum
            CPIntVarOps.mapVarVal = CPIntVarOps.mapVarVal + (x.hashCode () -> supCount.indexOf(supCount.max)) // change the map of var to constraint
            CPIntVarOps.mapVarSD = CPIntVarOps.mapVarSD + (x.hashCode() -> SD)
          }
      })
      if(SD == 0f){
        SD = CPIntVarOps.mapVarSD.getOrElse(x.hashCode(),0f)
      }
//      print(" variable_hash-code " + x.hashCode()+ " solution_density " + SD + "\n")
      SD                                                                  // return the probability
    }

    //              if(supCount.filter(_!=0).size != x.size){
    ////               print(" ----------------------------------------------- \n")
    //                  sumSC = (x.toArray collect supCount).sum
    //               }
    //              else{
    //                 sumSC = supCount.sum
    //              }
//        def varCountSearchSumSD: Float = {
//          var sumSC = 0
//          var SD = 0f
//          var maxProb = 0f
//          var mapConsave = 0
//          var mapCons = CPIntVarOps.mapcount                                  // map of constraint to (map of variable to supcount)
////          print(" hashcode " + x.hashCode() +"\n" )
//          for (vi <- x) {                                                     // loop on every values
//            var sumSD = 0f
//            var numcons = 0
//            mapCons foreach (mapCons => {                                     // loop on every constraints
//              val supCount = mapCons._2.getOrElse (x.hashCode(), Array())    // get the correct supcount (empty if doesn't exist)
//              //!supCount.isEmpty for the variables are not in the constraints
//              //supCount(vi)>0) for some cases like: variable List is: (9, 3, 5, 7, 2, 0, 4) and supCount List is :(3, 0, 0, 0, 2),
//              // the value 9 is not in the domain anymore
//              if(!supCount.isEmpty){                        // var inside the constraint and value inside the constraint
////                print(" supCount(vi) " + supCount(vi))
//                sumSC = supCount.sum
////                print(" supcount " + supCount.toList + " variable_Domain " + x.toList  + " new_supcount " + (x.toArray collect supCount).toList + " sum using collect method " + (x.toArray collect supCount).sum + " sum using supCount.sum " + supCount.sum+ "\n")
//                print(" Variable hashcode " + x.hashCode() + " consID " + mapCons._1 + " variable " + x.toList + " supcount " + supCount.toList + " sumSC " + sumSC +"\n")
////                print(" variable " + x.toList + " supCount " + supCount.toList+"\n")
//                if( vi > supCount.size - 1){
//                  SD = 0
//                }
//                else{
//                  SD = supCount(vi).toFloat / sumSC.toFloat
//                }
//                sumSD += SD
//                numcons += 1
//                mapConsave = mapCons._1                                       //save constraints hashcode
//              }
//              else{
//                print(" OUT : variable " + x.toList + " supCount " + supCount.toList+"\n")
//              }
//            })
//            var Probvi = sumSD / numcons.toFloat
////            print("++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ \n")
////            print(" For value " + vi +", the solution density is " + Probvi + "\n")
////            print("++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ \n")
//            if (Probvi >= maxProb){
//              maxProb = Probvi
//              CPIntVarOps.mapVarVal = CPIntVarOps.mapVarVal + (x.hashCode() -> vi)
//              CPIntVarOps.mapVarCons = CPIntVarOps.mapVarCons + (x.hashCode() -> mapConsave)
//            }
//          }
////          print(" ---------------------------------------------------------------"+"\n")
//          print(" The variable " + "(hashcode: "+ x.hashCode()+ ")" + ", and its domain "  + x.toList + ", and the biggest solution density of this variable is " + maxProb + "\n")
////          print(" ---------------------------------------------------------------"+"\n")
//          maxProb
//        }

    def varCountSearchSumSD: Float = {
      var sumSC = 0
      var SD = 0f
      var maxProb = 0f
      var mapCons = CPIntVarOps.mapcount.getOrElse(x.hashCode(),scala.collection.mutable.Map[Int, Array[Int]]())
      // map of constraint to (map of variable to supcount)
      for (vi <- x) {                                                     // loop on every values
        var sumSD = 0f
        var numcons = 0
        mapCons foreach (mapCons => {                                     // loop on every constraints
          val supCount = mapCons._2                                       // get the correct supcount (empty if doesn't exist)
          sumSC = supCount.sum
          if( vi > supCount.size - 1){                                    // check if the supcount has the vi value inside (may be removed through propagate)
            SD = 0
          }
          else{
            SD = supCount(vi).toFloat / sumSC.toFloat
          }
          sumSD += SD
          numcons += 1
          print(" vi " + vi)
        })
        var Probvi = sumSD / numcons.toFloat
        print("sumsd " + sumSD +" numcons " + numcons + "\n")
        if (Probvi > maxProb){
          maxProb = Probvi
          CPIntVarOps.mapVarVal = CPIntVarOps.mapVarVal + (x.hashCode() -> vi)
          CPIntVarOps.mapVarSD = CPIntVarOps.mapVarSD + (x.hashCode() -> maxProb)
        }
      }
      if(maxProb == 0f){
        maxProb = CPIntVarOps.mapVarSD.getOrElse(x.hashCode(),0f)
      }
      print(" variable_hash-code " + x.hashCode()+ " solution_density " + maxProb + "\n")
      maxProb
    }



    def varCountSearchProdSD: Float = {
      var sumSC = 0
      var SD = 0f
      var maxProb = 0f
      var mapCons = CPIntVarOps.mapcount.getOrElse(x.hashCode(),scala.collection.mutable.Map[Int, Array[Int]]())
      // map of constraint to (map of variable to supcount)
      for (vi <- x) {                                                     // loop on every values
        var prodSD = 0f
        var numcons = 0
        mapCons foreach (mapCons => {                                     // loop on every constraints
          val supCount = mapCons._2                                       // get the correct supcount (empty if doesn't exist)
          sumSC = supCount.sum
          if( vi > supCount.size - 1){                                    // check if the supcount has the vi value inside (may be removed through propagate)
            SD = 0
          }
          else {
            SD = supCount (vi).toFloat / sumSC.toFloat
          }
//          print(" SD " + SD)
          prodSD += (- math.log10(SD).toFloat)
          numcons += 1
//          print(" vi " + vi)
        })
        var Probvi = prodSD / numcons.toFloat
//        print("prodSD " + prodSD +" numcons " + numcons + "\n")
        if (Probvi > maxProb){
          maxProb = Probvi
          CPIntVarOps.mapVarVal = CPIntVarOps.mapVarVal + (x.hashCode() -> vi)
          CPIntVarOps.mapVarSD = CPIntVarOps.mapVarSD + (x.hashCode() -> maxProb)
        }
      }
      if(maxProb == 0f){
        maxProb = CPIntVarOps.mapVarSD.getOrElse(x.hashCode(),0f)
      }
//      print(" variable_hash-code " + x.hashCode()+ " solution_density " + maxProb + "\n")
      maxProb
    }

    //        def varCountSearchProdSD: Float = {
//          var sumSC = 0
//          var SD = 1f
//          var SDmax = 0f
//          var maxProb = 0f
//          var mapConsave = 0
//          var mapCons = CPIntVarOps.mapcount                                    // map of constraint to (map of variable to supcount)
//          for(vi <- x) {
//            var prodSD = 1f
//            var numcons = 0f
//            mapCons foreach (mapCons => {                                       // loop on every constraints
//              val supCount = mapCons._2.getOrElse (x.hashCode (), Array ())   // get the correct supcount (empty if doesn't exist)
//              if(!supCount.isEmpty && supCount(vi) > 0){
//                sumSC = supCount.sum
////                sumSC = (x.toArray collect supCount).sum
//                SD = supCount(vi).toFloat / sumSC.toFloat
//                prodSD=SD * prodSD * 10000
//                numcons += 1
//                mapConsave = mapCons._1                                          //save constraints hashcode
//              }
//                prodSD= prodSD /10000
//            })
//              val Probvi = scala.math.pow(prodSD , 1/numcons).toFloat              // return the probability
//              if (Probvi > maxProb){
//                maxProb = Probvi
//                CPIntVarOps.mapVarVal = CPIntVarOps.mapVarVal + (x.hashCode() -> vi)
//                CPIntVarOps.mapVarCons = CPIntVarOps.mapVarCons + (x.hashCode() -> mapConsave)
//              }
//          }
//          maxProb
//        }

//        def valCountSearch(bound:String): Int ={
//          var mapCons = CPIntVarOps.mapcount                                  // map of constraint to (map of variable to supcount)
//          var valuereturn = 0                                                 // index to return at the end
//          var idconst = 0
//          idconst = CPIntVarOps.mapVarCons.getOrElse(x.hashCode(), -1)
//          if(idconst == -1){
//            return x.min
//          }
//          val supCount = mapCons(idconst).getOrElse(x.hashCode(), Array())
//          if (supCount.isEmpty && bound == "min"){                                   // if the var was outside the TableCT and we decide to get the min
//            valuereturn = x.min
//          }
//          else if(supCount.isEmpty && bound == "max"){                               // if the var was outside the TableCT and we decide to get the max
//            valuereturn = x.max
//          }
//          else {
//            valuereturn = CPIntVarOps.mapVarVal(x.hashCode())
//          }
////          CPIntVarOps.mapVarCons.clear()
////          CPIntVarOps.mapVarVal.clear()
////          CPIntVarOps.mapcount.clear()
//          //once one variable is bounded, the propagate will be trigger, then mapcount will be refilled
//          valuereturn                                                               // return the correct index
//        }

    def valCountSearch(bound:String): Int ={
      var mapCons = CPIntVarOps.mapcount                                  // map of constraint to (map of variable to supcount)
      var valuereturn = CPIntVarOps.mapVarVal.getOrElse(x.hashCode(), -1)                                                 // index to return at the end
      if (valuereturn<0 && bound == "min"){                                   // if the var was outside the TableCT and we decide to get the min
        valuereturn = x.min
      }
      else if(valuereturn<0 && bound == "max"){                               // if the var was outside the TableCT and we decide to get the max
        valuereturn = x.max
      }
      //          CPIntVarOps.mapVarCons.clear()
//                CPIntVarOps.mapVarVal.clear()
      print( "valuereturn" + valuereturn + "mapvarval" + CPIntVarOps.mapVarVal.toList + "mapvarsd" + CPIntVarOps.mapVarSD.toList + "IDvar" + x.hashCode() + "\n")
      CPIntVarOps.mapcount.clear()                                   // even if the SD is 0 the previous best value is stored in mapVar
      CPIntVarOps.mapVarSD.remove(x.hashCode())                      //remove the choosen variable hashcode
      CPIntVarOps.mapVarVal.remove(x.hashCode())
      //once one variable is bounded, the propagate will be trigger, then mapcount will be refilled
      valuereturn                                                               // return the correct index
    }




    //    //update support count
    //    def changeCount(supportCount: Array[Int], idvar:Int, idconst:Int): Unit ={
    //      var sumSC = supportCount.sum
    //      //      print(" sumSC " + sumSC)
    //      if(sumSC != 0){
    //        var mapsup = scala.collection.mutable.Map[Int, Array[Int]]()
    //        var mapCons = CPIntVarOps.mapcount
    //        // if the constraint key exist
    //        if(CPIntVarOps.mapcount.get(idconst) != None ) {
    //          mapsup = CPIntVarOps.mapcount (idconst)
    //        }
    //        mapsup = mapsup + (idvar -> supportCount)
    //        mapCons = mapCons + (idconst -> mapsup)
    //        CPIntVarOps.mapcount = mapCons  //save the map created in CPIntVarOps
    //        //  mapsup foreach (mapsup => print(" map : " + mapsup._1+ "==>" + mapsup._2.toList + "\n") )
    //        //  mapCons foreach (mapCons => print(" cons: " + mapCons._1 + " ==> " + mapCons._2.toList+ "\n"))
    //      }
    //    }
    //
    //    def varCountSearchSD: Float = { // TODO modify to keep the best value not best constraint
    //      // saveMaxCount
    //      var sumSC = 0
    //      var SD = 0f
    //      var SDTest = 0f
    //      var maxCount = -1                                                   // initialization of the maxcount
    //      var mapCons = CPIntVarOps.mapcount                                  // map of constraint to (map of variable to supcount)
    //      mapCons foreach (mapCons => {                                       // loop on every constraints
    //        var supCount = mapCons._2.getOrElse (x.hashCode (), Array (-1))   // get the correct supcount (-1 if doesn't exist)
    //        // print(" x "+ x.toList +" sc " + supCount.toList)
    //        if (supCount.max >= maxCount && supCount.max > 0) {
    //          maxCount = supCount.max
    //          sumSC = supCount.sum
    //          SDTest = (maxCount.toFloat / sumSC.toFloat) // probability to search on this var
    //          //          print(" maxCount " + maxCount)
    //          //          print(" sumSC " + sumSC)
    //          //          print(" SDTest " + SDTest)
    //          if (SDTest > SD) { // condition to find the maximum
    //            SD = SDTest // assign the maximum
    //            CPIntVarOps.mapVarVal = CPIntVarOps.mapVarVal + (x.hashCode () -> supCount.indexOf(supCount.max)) // change the map of var to constraint
    //            CPIntVarOps.mapVarCons = CPIntVarOps.mapVarCons + (x.hashCode() -> mapCons._1)
    //          }
    //        }
    //      })
    //      //      print(" SD " + SD +"\n")
    //      SD                                                                  // return the probability
    //    }
    //
    //
//        def varCountSearchSumSD: Float = {
//          // saveMaxCount
//          var sumSC = 0
//          var SD = 0f
//          var SDmax = 0f
//          var maxProb = 0f
//          var mapConsave = 0
//          var mapCons = CPIntVarOps.mapcount                                  // map of constraint to (map of variable to supcount)
//          for (vi <- x) {                                                     // loop on every values
//            var sumSD = 0f
//            var numcons = 0
//            mapCons foreach (mapCons => {                                     // loop on every constraints
//              var supCount = mapCons._2.getOrElse (x.hashCode (), Array (-1)) // get the correct supcount (-1 if doesn't exist)
//              if (supCount.max >= 0 && supCount(vi) > 0) {                    // var inside the constraint and value inside the constraint
//                sumSC = supCount.sum
//                SD = supCount(vi).toFloat / sumSC.toFloat
//                sumSD += SD
//                numcons += 1
//                mapConsave = mapCons._1                                     //save constraints hashcode
////                print( " x " + x.toList + x.hashCode()+ " vi " + vi + " sumSC " + sumSC + " supCount " + supCount(vi) + " SD " + SD + " sumSD " + sumSD + " numcons " + numcons + " mapConsave " + mapConsave +"\n")
//              }
//            })
//            var Probvi = sumSD / numcons.toFloat
////            print(" probvi " + Probvi + "\n")
//            if (Probvi > maxProb){
//              maxProb = Probvi
//              CPIntVarOps.mapVarVal = CPIntVarOps.mapVarVal + (x.hashCode() -> vi)
//              CPIntVarOps.mapVarCons = CPIntVarOps.mapVarCons + (x.hashCode() -> mapConsave)
//            }
//          }
//          //      print(" maxProb " + maxProb + "\n")
//          maxProb
//        }

//
//    def varCountSearchSumSD: Float = {
//      var sumSC = 0
//      var SD = 0f
//      var maxProb = 0f
//      var mapConsave = 0
//      var mapCons = CPIntVarOps.mapcount                                  // map of constraint to (map of variable to supcount)
//      for (vi <- x) {                                                     // loop on every values
//        var sumSD = 0f
//        var numcons = 0
//        mapCons foreach (mapCons => {                                     // loop on every constraints
//          var supCount = mapCons._2.getOrElse (x.hashCode (), Array())    // get the correct supcount (empty if doesn't exist)
//          if(!supCount.isEmpty && supCount(vi)>0){                        // var inside the constraint and value inside the constraint
//            //                if(supCount.filter(_!=0).size != x.size){
//            ////                  print(" ----------------------------------------------- \n")
//            //                  sumSC = (x.toArray collect supCount).sum
//            //                }
//            //                else{
//            sumSC = supCount.sum
//            //                }
//            //                print(" supcount " + supCount.toList + " variable_Domain " + x.toList  + " new_supcount " + (x.toArray collect supCount).toList + " sum using collect method " + (x.toArray collect supCount).sum + " sum using supCount.sum " + supCount.sum+ "\n")
//            SD = supCount(vi).toFloat / sumSC.toFloat
//            sumSD += SD
//            numcons += 1
//            mapConsave = mapCons._1                                       //save constraints hashcode
//          }
//        })
//        var Probvi = sumSD / numcons.toFloat
//        //            print("++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ \n")
//        //            print(" For value " + vi + ", the solution density is " + Probvi + "\n")
//        //            print("++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ \n")
//        if (Probvi > maxProb){
//          maxProb = Probvi
//          CPIntVarOps.mapVarVal = CPIntVarOps.mapVarVal + (x.hashCode() -> vi)
//          CPIntVarOps.mapVarCons = CPIntVarOps.mapVarCons + (x.hashCode() -> mapConsave)
//        }
//      }
//      //          print(" ---------------------------------------------------------------"+"\n")
//      //          print(" The variable " + "(hashcode: "+ x.hashCode()+ ")" + ", and its domain "  + x.toList + ", and the biggest solution density of this variable is " + maxProb + "\n")
//      //          print(" ---------------------------------------------------------------"+"\n")
//      maxProb
//    }
    //
    //    def varCountSearchProdSD: Float = {
    //      // saveMaxCount
    //      var sumSC = 0
    //      var SD = 0f
    //      var SDmax = 0f
    //      var maxProb = 0f
    //      var mapConsave = 0
    //      var mapCons = CPIntVarOps.mapcount                                    // map of constraint to (map of variable to supcount)
    //      for(vi <- x) {
    //        var prodSD = 1f
    //        var numcons = 0f
    //        mapCons foreach (mapCons => {                                       // loop on every constraints
    //          var supCount = mapCons._2.getOrElse (x.hashCode (), Array (-1))   // get the correct supcount (-1 if doesn't exist)
    //          if(supCount.max >= 0 && supCount(vi) > 0){
    //            sumSC = supCount.sum
    //            SD = supCount(vi).toFloat / sumSC.toFloat
    //            prodSD*=SD
    //            numcons += 1
    //            mapConsave = mapCons._1                                          //save constraints hashcode
    //            //   print( " x " + x.toList + x.hashCode() + " vi " + vi + " sumSC " + sumSC + " supCount " + supCount(vi) + " SD " + SD + " probSD " + prodSD + " numcons " + numcons + " mapConsave " + mapConsave +"\n")
    //          }
    //        })
    //        val Probvi = scala.math.pow(prodSD , 1/numcons).toFloat              // return the probability
    //        // print(" probvi " + Probvi + "\n")
    //        if (Probvi > maxProb){
    //          maxProb = Probvi
    //          CPIntVarOps.mapVarVal = CPIntVarOps.mapVarVal + (x.hashCode() -> vi)
    //          CPIntVarOps.mapVarCons = CPIntVarOps.mapVarCons + (x.hashCode() -> mapConsave)
    //        }
    //      }
    //      maxProb
    //    }
    //
    //    def valCountSearch(bound:String): Int ={
    //      var mapCons = CPIntVarOps.mapcount                                  // map of constraint to (map of variable to supcount)
    //      var valuereturn = 0                                                 // index to return at the end
    //      var maxCount = -1
    //      var idconst = 0
    //      idconst = CPIntVarOps.mapVarCons (x.hashCode ())
    //      var supCount = mapCons(idconst).getOrElse(x.hashCode(), Array(-1))
    //      maxCount = supCount.max
    //      if (maxCount < 1 && bound == "min"){                                 // if the var was outside the TableCT and we decide to get the min
    //        valuereturn = x.min
    //      }
    //      else if(maxCount < 1 && bound == "max"){                              // if the var was outside the TableCT and we decide to get the max
    //        valuereturn = x.max
    //      }
    //      else {
    //        valuereturn = CPIntVarOps.mapVarVal(x.hashCode())
    //        print(valuereturn)
    //      }
    //      valuereturn                                                          // return the correct index
    //    }

    /**
      * @return difference between second smallest and smallest value in the domain, Int.MaxInt if variable is bound
      */
    def regret: Int = {
      if (x.isBound) Int.MaxValue
      else {
        val min = x.min
        x.valueAfter(min) - min
      }
    }

    def maxRegret(costs: Array[Int]): Int = {
      val values = x.toArray
      var min1 = costs(values(0))
      var min2 = Int.MaxValue
      var i = values.length
      while (i > 1) {
        i -= 1
        val value = values(i)
        val cost = costs(value)
        if (cost <= min1) {
          min2 = min1
          min1 = cost
        } else if (cost < min2) min2 = cost
      }
      min2 - min1
    }

    def maxRegret(costFunction: Int => Int): Int = {
      val values = x.toArray
      var min1 = costFunction(values(0))
      var min2 = Int.MaxValue
      var i = values.length
      while (i > 1) {
        i -= 1
        val value = values(i)
        val cost = costFunction(value)
        if (cost <= min1) {
          min2 = min1
          min1 = cost
        } else if (cost < min2) min2 = cost
      }
      min2 - min1
    }

    def minBy(costs: Array[Int]): Int = {
      val values = x.toArray
      var i = values.length
      var minValue = values(0)
      var minCost = costs(minValue)
      while (i > 1) {
        i -= 1
        val value = values(i)
        val cost = costs(value)
        if (cost < minCost) {
          minValue = value
          minCost = cost
        }
      }
      minValue
    }

    /**
      * @return The median value of the domain of the variable
      */
    def median: Int = {
      val vals = x.toArray.sortBy(i => i)
      print(vals.toList)
      vals(vals.length / 2)
    }

    /**
      *  Returns the value assigned to the variable.
      *  Throws an Exception if the variable is not assigned.
      */
    def value: Int = {
      if (x.isBound) x.min
      else throw new NoSuchElementException("the variable is not bound")
    }



    /**
      * -x
      */
    def unary_-() = new CPIntVarViewMinus(x)
    /**
      * x+y
      */
    def +(y: CPIntVar) = plus(x, y)
    /**
      * x-y
      */
    def -(y: CPIntVar) = minus(x, y)
    /**
      * x+y
      */
    def +(y: Int) = plus(x, y)
    /**
      * x-y
      */
    def -(y: Int) = minus(x, y)

    def +(s: String) = s"$x$s"

    /**
      * x*y
      */
    def *(y: CPIntVar): CPIntVar = {
      if (y.isBound) x * (y.value)
      else mul(x, y)
    }
    /**
      * x*y
      */
    def *(y: Int): CPIntVar = mul(x, y)

    def abs = absolute(x)

    /**
      * Reified constraint
      *
      * @param y a variable
      * @return a boolean variable b in the same store linked to x by the relation x == y <=> b == true
      */
    def isEq(y: CPIntVar): CPBoolVar = {
      val b = CPBoolVar()(x.store)
      x.store.post(new oscar.cp.constraints.EqReifVar(x, y, b))
      b
    }



    /**
      * x must take a value from set
      */
    def in(set: Set[Int]): Constraint = new InSet(x, set)

    /**
      * x<y
      */
    def <(y: CPIntVar) = new oscar.cp.constraints.Le(x, y)
    /**
      * x<y
      */
    def <(y: Int) = new oscar.cp.constraints.Le(x, y)
    /**
      * x>y
      */
    def >(y: CPIntVar) = new oscar.cp.constraints.Gr(x, y)
    /**
      * x>y
      */
    def >(y: Int) = new oscar.cp.constraints.Gr(x, y)
    /**
      * x<=y
      */
    def <=(y: CPIntVar) = new oscar.cp.constraints.LeEq(x, y)
    /**
      * x<=y
      */
    def <=(y: Int) = new oscar.cp.constraints.LeEq(x, y)
    /**
      * x>=y
      */
    def >=(y: CPIntVar) = new oscar.cp.constraints.GrEq(x, y)
    /**
      * x>=y
      */
    def >=(y: Int) = new oscar.cp.constraints.GrEq(x, y)

    /**
      * x == v
      */
    def ===(v: Int) = x.eq(v)

    /**
      * x == y
      */
    def ===(y: CPIntVar) = x.eq(y)

    /**
      * x != v
      */
    def !==(v: Int) = x.diff(v)

    /**
      * x == y
      */
    def !==(y: CPIntVar) = x.diff(y)



    def %(y: Int) = ModuloLHS(x, y)

    def mod(y: Int) = modulo(x, y)

    // New experimental function names for reification

    /**
      * b <=> x == v
      */
    def ?=== (v: Int) = x.isEq(v)

    /**
      * b <=> x == y
      */
    def ?=== (y: CPIntVar) = x.isEq(y)

    /**
      * b <=> x!= y
      */
    def ?!== (y: CPIntVar) = x.isDiff(y)

    /**
      * b <=> x!= y
      */
    def ?!== (y: Int) = x.isDiff(y)

    /**
      * b <=> x >= y
      */
    def ?>= (y: Int) = x.isGrEq(y)

    /**
      * b <=> x >= y
      */
    def ?>= (y: CPIntVar) = x.isGrEq(y)

    /**
      * b <=> x > y
      */
    def ?> (y: Int) = x.isGr(y)

    /**
      * b <=> x > y
      */
    def ?> (y: CPIntVar) = x.isGr(y)

    /**
      * b <=> x >= y
      */
    def ?<= (y: Int) = x.isLeEq(y)

    /**
      * b <=> x >= y
      */
    def ?<= (y: CPIntVar) = x.isLeEq(y)

    /**
      * b <=> x > y
      */
    def ?< (y: Int) = x.isLe(y)

    /**
      * b <=> x > y
      */
    def ?< (y: CPIntVar) = x.isLe(y)
  }

  implicit class CPBoolVarOps(val variable: CPBoolVar) extends AnyVal {

    /** Logical or */
    def or(y: CPBoolVar): CPBoolVar = {
      val b = CPBoolVarImpl(variable.store, "")
      variable.store.post(new oscar.cp.constraints.OrReif2(Array(variable, y), b))
      b
    }

    /** Logical and */
    def and(y: CPBoolVar): CPBoolVar = {
      val res = plus(variable, y)
      res.isEq(2)
    }

    def implies(y: CPBoolVar) = {
      val b = CPBoolVarImpl(variable.store, "")
      variable.store.post(new oscar.cp.constraints.Implication(variable, y, b))
      b
    }

    /** !b */
    def unary_!(): CPBoolVar = variable.not

    /** x | y */
    def |(y: CPBoolVar) = or(y)

    /** x || y */
    def ||(y: CPBoolVar) = or(y)

    /** x & y */
    def &(y: CPBoolVar) = and(y)

    /** x && y */
    def &&(y: CPBoolVar) = and(y)

    /** x ==> y */
    def ==>(y: CPBoolVar) = implies(y)
  }

  def allBounds(vars: Iterable[_ <: CPIntVar]) = vars.asInstanceOf[Iterable[CPIntVar]].forall(_.isBound)
}

