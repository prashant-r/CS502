package l3
package test

import org.junit.Test
import l3.test.infrastructure.CPSOptTest

/** Greybox testing for entire program outputs:
 *    - much like blackbox tests, but can access the internal state of the interpreter
 *    - they can query how many instructions or primitives have been executed for example */
class CPSOptimizer_Greybox extends CPSOptTest {

  // ETA REDUCTION
  @Test def testEtaReduction =
    testCPSOptEarly("""
      (letrec ((f (fun (x) x)) (g (fun (y) (f y))) (h (fun (z) (g z))))
        (@ + (@ + (@ + (@ + (@ + (@ + (@ + (@ + (g 1) (g 2))
        (g 3)) (h 1)) (h 2)) (h 3)) (f 1)) (f 2)) (f 3)))
    """, _.getFuncs <= 2)

  @Test def testEtaReductionInfintelyRecursiveFunction = // needs to keep the resulting infinitely-recursive function
    testCPSOptEarly("""(letrec ((f (fun (x) (g x))) (g (fun (x) (f x)))) (if (@ = (@byte-read) -1) (g 3) #u))""", _.getFuncs == 1)

  // DEAD CODE ELIMINATION
  @Test def testDCEFunsSimple =
    testCPSOptEarly("(letrec ((f (fun (x) (f x)))) #u)", _.getFuncs == 0)

  @Test def testDCEFunsRecursive1 =
    testCPSOptEarly("(letrec ((f (fun (x) (@ + (g x) 1))) (g (fun (y) (@ + (f y) 1)))) #u)", _.getFuncs == 0)

  @Test def testDCEFunsRecursive2 =
    testCPSOptEarly("(letrec ((f (fun (x) (@ + (g x) 1))) (g (fun (y) (@ + (f y) 1))) (h (fun (z) z))) #u)", _.getFuncs == 0)

  @Test def testDCEFunsRecursive3WithEtaReduction =
    testCPSOptEarly("(letrec ((f (fun (x) (if (@ = x 0) 0 (g (@ - x 1))))) (g (fun (y) (f y))) (h (fun (z) z))) (@ + (@ + (f 0) (f 0)) (f 0)))", _.getFuncs <= 1)

  @Test def testDCELetLiteral =
    testCPSBothSeq("(let ((u 1)) #u)", _.get(LetL) == 1)

  @Test def testDCELetPrimitive =
    testCPSOptEarly("(let ((x (@int->char 80))) #u)", _.get(LetP) == 1)


  // INLINING
  @Test def testFunInlining =
    testCPSOptEarly("(letrec ((f (fun (x) x))) (f 1))", _.get(AppF) == 0)

  @Test def testFunInliningInsideFunctionBodySameLetRec =
    testCPSOptEarly("(letrec ((f (fun (x) x)) (g (fun (x) (f x)))) (g 1))", _.get(AppF) == 0)

  @Test def testFunInliningInsideFunctionBodyDifferentLetRecs =
    testCPSOptEarly("(letrec ((f (fun (x) x))) (letrec ((g (fun (x) (f x)))) (g 1)))", _.get(AppF) == 0)

// heuristics are changed in the new optimizer:
//  @Test def testFunInliningHeuristics =
//    testCPSOptEarly("(letrec ((f (fun (x) x))) (@ + (@ + (f 1) (f 2)) (f 3)))", _.get(AppF) == 3)

  @Test def testFunInliningCrasher =
    testCPSOptEarly("(letrec ((f (fun (x) (if (@ = x 0) 0 (g (@ - x 1))))) (g (fun (y) (f y))) (h (fun (z) z))) (f 0))", _.get(AppF) == 0)

  @Test def testFunInliningRecursiveTrick =
    testCPSOptEarly("(letrec ((f (fun (x) (g x))) (g (fun (y) (f y))) (h (fun (z) z))) (h 3))", _.get(AppF) == 0)

  @Test def testContInlining =
    testCPSOptEarly("(let ((x 1)) x)", _.get(AppK) == 0)

  @Test def testContInliningInsideContBody =
    testCPSOptEarly("(let ((x 1) (y 2)) (@ + x y))", _.get(AppK) == 0)


  // CONSTANT FOLDING
// heuristics are changed in the new optimizer:
//  @Test def testContInliningHeuristics = // This test needs to give some input to the program
//    testCPSOptStats("(if (@ = (@ char-read) (@int->char 3)) #u #u)", _.get(AppK) == 1, earlyOpt = true, lateOpt = false, input = " ")

  @Test def testConstantFoldingIntP =
    testCPSOptLate("(let ((x (@ int? 1))) #u)", stats => stats.get(LetP) == 0 && stats.get(If) == 0)

  @Test def testConstantFoldingIntPNot =
    testCPSOptLate("(let ((x (@ int? #u))) #u)", stats => stats.get(LetP) == 0 && stats.get(If) == 0)

  @Test def testConstantFoldingPlus =
    testCPSOptLate("(@ + 2 1)", stats => stats.get(LetP) == 0)

  @Test def testConstantFoldingMinus =
    testCPSOptLate("(@ - 2 1)", stats => stats.get(LetP) == 0)

  @Test def testConstantFoldingTimes =
    testCPSOptLate("(@ * 2 1)", stats => stats.get(LetP) == 0)

  @Test def testConstantFoldingDiv =
    testCPSOptLate("(@ / 2 1)", stats => stats.get(LetP) == 0)

  @Test def testConstantFoldingMod =
    testCPSOptLate("(@ % 2 1)", stats => stats.get(LetP) == 0)

  @Test def testConstantFoldingIntChar =
    testCPSOptLate("(@int->char 10)", stats => stats.get(LetP) == 0)

  @Test def testConstantFoldingCharInt =
    testCPSOptLate("(@int->char 10)", stats => stats.get(LetP) == 0)

  @Test def testConstantFoldingTypePrims = {
    for (prim <- List("bool?", "unit?", "int?"))
      for (value <- List("#t", "#f", "2", "#u", "'x'"))
        // The early optimizer should be enough to
        // eliminate these simple type primitives:
        testCPSOptEarly(s"(@ $prim $value)",
            stats => stats.get(LetP) == 1 && stats.get(If) == 0)
  }

  @Test def testConstantFoldingBooleanAnd =
    testCPSOptEarly("(and #t #f)", stats => stats.get(LetP) == 1 && stats.get(If) == 0)

  @Test def testConstantFoldingBooleanOr =
    testCPSOptEarly("(or #t #f)", stats => stats.get(LetP) == 1 && stats.get(If) == 0)

  @Test def testConstantFoldDCEContinuations =
    testCPSOptEarly("(if #t 1)", _.get(LetK) == 0)

  // CONSTANT PROPAGATION
  @Test def testConstantPropagationSimple =
    testCPSBothSeq("(@byte-write (@ / (@ / (@ / (@byte-read) 3) 3) 3))", _.get(LetL) <= 4)

//  not supported by current optimizer: FIXME: Update to latest l3!
//
//  @Test def testConstantCapturingInFunction1 =
//    testCPSBothSeq("(let ((a 1) (b 2) (c 3)) (letrec ((f (fun (x) (@ + (@ + (@ + x a) b) c)))) (@ char-print (@int->char (@ + (@ + (f (@ char->int (@ char-read))) (f 1)) (f 1))))))", _.get(BlockSet) == 1)
//
//  @Test def testConstantCapturingInFunction2 =
//    testCPSBothSeq("(let ((one 1)) (letrec ((f (fun (x) (@ + x one)))) (@ + (@+ (@ + (f 1) (f 2)) (f 3)) one)))", _.get(BlockSet) == 1)
//
//  @Test def testConstantCapturingInFunctionFixpoint =
//    testCPSBothSeq("(let ((a 3)) (letrec ((f (fun (x) (@char-print x) (@char-print a) (if (@ > x 0) (f (@ - x 1)))))) (f a)))", _.get(BlockSet) == 1)


  // NEUTRAL ELEMENTS
  @Test def testNeutralElementsAddZero1 =
    testCPSBothSeq("(let ((u (@int->char (@byte-read)))) (@byte-write (@char->int (@ + u 0))))", _.get(Add) == 0)

  @Test def testNeutralElementsAddZero2 =
    testCPSBothSeq("(let ((u (@int->char (@byte-read)))) (@byte-write (@char->int (@ + 0 u))))", _.get(Add) == 0)

  @Test def testNeutralElementsSubZero =
    testCPSBothSeq("(let ((u (@int->char (@byte-read)))) (@byte-write (@char->int (@ - u 0))))", _.get(Sub) == 0)

  @Test def testNeutralElementsSubItself =
    testCPSBothSeq("(let ((u (@int->char (@byte-read)))) (@byte-write (@char->int (@ - u u))))", _.get(Sub) == 0)

  @Test def testNeutralElementsMulOne1 =
    testCPSBothSeq("(let ((u (@int->char (@byte-read)))) (@byte-write (@char->int (@ * u 1))))", _.get(Mul) == 0)

  @Test def testNeutralElementsMulOne2 =
    testCPSBothSeq("(let ((u (@int->char (@byte-read)))) (@byte-write (@char->int (@ * 1 u))))", _.get(Mul) == 0)

  @Test def testNeutralElementsMulZero1 =
    testCPSBothSeq("(let ((u (@int->char (@byte-read)))) (@byte-write (@char->int (@ * u 0))))", _.get(Mul) == 0)

  @Test def testNeutralElementsMulZero2 =
    testCPSBothSeq("(let ((u (@int->char (@byte-read)))) (@byte-write (@char->int (@ * 0 u))))", _.get(Mul) == 0)

  @Test def testNeutralElementsDivOne =
    testCPSBothSeq("(let ((u (@int->char (@byte-read)))) (@byte-write (@char->int (@ / u 1))))", _.get(Div) == 0)

  // this optimization is incorrect (0/0 should throw div by zero): FIXME: Update to latest l3!
  // @Test def testNeutralElementsDivMemeChose =
  //   testCPSBothSeq("(let ((u (@ char->int (@ char-read)))) (@ char-print (@int->char (@ / u u))))", _.get(Div) == 0)

  // this optimization is disabled because it requires too many changes to the optimizer and is not worth it:
  // @Test def testNeutralElementsModOne =
  //   testCPSBothSeq("(let ((u (@ char->int (@ char-read)))) (@ char-print (@int->char (@ % u 1))))", _.get(Mod) == 0)


  // COMMON SUBEXPRESSION ELIMINATION
  @Test def testCommonSubexpressionEliminationSimpleBlockTag =
    testCPSBothSeq("(let ((b (@ block-alloc-3 2))) (@byte-write (@ + (@ block-tag b) (@ block-tag b))))", _.get(BlockTag) <= 1)

  @Test def testCommonSubexpressionEliminationComplexBlockTag =
    testCPSBothSeq("(let ((b (@ block-alloc-3 300)) (p (@byte-write (@byte-read)))) (@byte-write (@ + (@ + p (@ block-tag b)) (@ + p (@ block-tag b)))))", _.get(BlockTag) <= 1)


  // USE MULTIPLE MICROPHASES
  @Test def testFunInlingAndDCE =
    testCPSOptEarly("(letrec ((f (fun (x) x)) (g (fun (y z) (f z)))) g)", _.getFuncs == 0)

  // Yes, it's possible only with inlining, constant folding and DCE:
  @Test def testInliningConstantFoldingDCE =
    testCPSOptTreeEquality(
      """ (def byte-write (fun (c) (@byte-write c)))
          (def function-compose
               (fun (f g)
                    (fun (x) (f (g x)))))
          (def + (fun (x y) (@+ x y)))
          (def succ (fun (x) (+ x 1)))
          (def twice (fun (x) (+ x x)))
          (byte-write ((function-compose succ twice) 39))
          (byte-write ((function-compose succ succ) 73))
          (byte-write ((function-compose twice succ) 4))""",
      """ (let* ((v$1 79)
                 (v$2 (@byte-write v$1))
                 (v$3 75)
                 (v$4 (@byte-write v$3))
                 (v$5 10)
                 (v$6 (@byte-write v$5))
                 (v$7 0))
             (halt v$7))"""
    )
}
