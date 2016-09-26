package l3.test

import l3.test.infrastructure.CPSHighTest
import org.junit.Test

/** Whitebox testing for entire program outputs */
class CL3ToCPS_Whitebox_NonTail extends CPSHighTest {

  // TODO: Test recursive functions

  @Test def testNonTailLiteral =
    testCPSHighTreeEquality("3", "(let* ((v$1 3) (v$2 0)) (halt v$2))")

  @Test def testNonTailMultiLet =
    testCPSHighTreeEquality("(let ((x 1) (y 2)) y)",
        "(let* ((v$1 1) (v$2 (@id v$1)) (v$3 2) (v$4 (@id v$3)) (v$5 0)) (halt v$5))")

  @Test def testNonTailSingleLetRec =
    testCPSHighTreeEquality("(fun (x) x)", "(let* ((v$1 (fun (v$2 v$3) (v$2 v$3))) (v$4 0)) (halt v$4))")

  @Test def testNonTailMultiLetRec =
    testCPSHighTreeEquality("(letrec ((f (fun (x) x)) (g (fun (y z) z))) g)",
        """(let* ((v$1 (fun (v$3 v$4) (v$3 v$4)))
          |       (v$2 (fun (v$5 v$6 v$7) (v$5 v$7)))
          |       (v$8 0))
          |  (halt v$8))""".stripMargin
    )

  @Test def testNonTailSingleLetRecAndApp =
    testCPSHighTreeEquality("((fun (x) x) 1)",
        """(let* ((v$1 (fun (v$2 v$3) (v$2 v$3)))
          |       (v$4 1)
          |       (v$5 (cnt (v$6) (let ((v$7 0)) (halt v$7)))))
          |  (v$1 v$5 v$4))""".stripMargin
    )

  @Test def testNonTailMultiLetRecAndApp =
    testCPSHighTreeEquality("((fun (x y) y) 1 2)",
        """(let* ((v$1 (fun (v$2 v$3 v$4) (v$2 v$4)))
          |       (v$5 1)
          |       (v$6 2)
          |       (v$7 (cnt (v$8) (let ((v$9 0)) (halt v$9)))))
          |  (v$1 v$7 v$5 v$6))""".stripMargin
    )


  @Test def testNonTailIf =
    testCPSHighTreeEquality("(if #t 1 2)",
          """(let* ((v$1 (cnt (v$2) (let ((v$3 0)) (halt v$3))))
            |       (v$4 (cnt () (let ((v$5 1)) (v$1 v$5))))
            |       (v$6 (cnt () (let ((v$7 2)) (v$1 v$7))))
            |       (v$8 #t)
            |       (v$9 #f))
            |  (if (@!= v$8 v$9) v$4 v$6))""".stripMargin
    )

  @Test def testNonTailTestPrimitive =
    testCPSHighTreeEquality("(@ > 1 2)",
        """(let* ((v$1 (cnt (v$2) (let ((v$3 0)) (halt v$3))))
          |       (v$4 (cnt () (let ((v$5 #t)) (v$1 v$5))))
          |       (v$6 (cnt () (let ((v$7 #f)) (v$1 v$7))))
          |       (v$8 1)
          |       (v$9 2))
          |  (if (@> v$8 v$9) v$4 v$6))""".stripMargin
    )

  @Test def testNonTailValuePrimitive =
    testCPSHighTreeEquality("(@ + 1 2)", "(let* ((v$1 1) (v$2 2) (v$3 (@+ v$1 v$2)) (v$4 0)) (halt v$4))")
}
