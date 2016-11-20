package l3.test

import l3.test.infrastructure.CPSHighTest
import org.junit.Test

/** Whitebox testing for entire program outputs */
class CL3ToCPS_Whitebox_Cond extends CPSHighTest {

  @Test def testCondNestedTrueTrue =
    testCPSHighTreeEquality(
      "(if (if (@ = 3 4) #t #t) 1 2)",
      """(let* ((v$1 (cnt (v$2) (let ((v$3 0)) (halt v$3))))
        |       (v$4 (cnt () (let ((v$5 1)) (v$1 v$5))))
        |       (v$6 (cnt () (let ((v$7 2)) (v$1 v$7))))
        |       (v$8 3)
        |       (v$9 4))
        |  (if (@= v$8 v$9) v$4 v$4))""".stripMargin
    )

  @Test def testCondNestedFalseFalse =
    testCPSHighTreeEquality(
      "(if (if (@ = 3 4) #f #f) 1 2)",
      """(let* ((v$1 (cnt (v$2) (let ((v$3 0)) (halt v$3))))
        |       (v$4 (cnt () (let ((v$5 1)) (v$1 v$5))))
        |       (v$6 (cnt () (let ((v$7 2)) (v$1 v$7))))
        |       (v$8 3)
        |       (v$9 4))
        |  (if (@= v$8 v$9) v$6 v$6))""".stripMargin
    )

  @Test def testCondNestedTrueFalse =
    testCPSHighTreeEquality("(if (if (@ = 3 4) #t #f) 1 2)",
      """(let* ((v$1 (cnt (v$2) (let ((v$3 0)) (halt v$3))))
        |       (v$4 (cnt () (let ((v$5 1)) (v$1 v$5))))
        |       (v$6 (cnt () (let ((v$7 2)) (v$1 v$7))))
        |       (v$8 3)
        |       (v$9 4))
        |  (if (@= v$8 v$9) v$4 v$6))""".stripMargin
    )

  @Test def testCondNestedFalseTrue =
    testCPSHighTreeEquality(
      "(if (if (@ = 3 4) #f #t) 1 2)",
      """(let* ((v$1 (cnt (v$2) (let ((v$3 0)) (halt v$3))))
        |       (v$4 (cnt () (let ((v$5 1)) (v$1 v$5))))
        |       (v$6 (cnt () (let ((v$7 2)) (v$1 v$7))))
        |       (v$8 3)
        |       (v$9 4))
        |  (if (@= v$8 v$9) v$6 v$4))""".stripMargin
    )

  @Test def testCondNestedTrueExpr =
    testCPSHighTreeEquality("(if (if (@ = 3 4) #t (if (@ = 3 4) #t #f)) 1 2)",
      """(let* ((v$1 (cnt (v$2) (let ((v$3 0)) (halt v$3))))
        |       (v$4 (cnt () (let ((v$5 1)) (v$1 v$5))))
        |       (v$6 (cnt () (let ((v$7 2)) (v$1 v$7))))
        |       (v$8 (cnt () (let* ((v$9 3) (v$10 4)) (if (@= v$9 v$10) v$4 v$6))))
        |       (v$11 3)
        |       (v$12 4))
        |  (if (@= v$11 v$12) v$4 v$8))""".stripMargin
    )

  @Test def testCondNestedFalseExpr =
    testCPSHighTreeEquality(
      "(if (if (@ = 3 4) #f (if (@ = 3 4) #t #f)) 1 2)",
      """(let* ((v$1 (cnt (v$2) (let ((v$3 0)) (halt v$3))))
        |       (v$4 (cnt () (let ((v$5 1)) (v$1 v$5))))
        |       (v$6 (cnt () (let ((v$7 2)) (v$1 v$7))))
        |       (v$8 (cnt () (let* ((v$9 3) (v$10 4)) (if (@= v$9 v$10) v$4 v$6))))
        |       (v$11 3)
        |       (v$12 4))
        |  (if (@= v$11 v$12) v$6 v$8))""".stripMargin
    )

  @Test def testCondNestedExprFalse =
    testCPSHighTreeEquality("(if (if (@ = 3 4) (if (@ = 3 4) #t #f) #f) 1 2)",
      """(let* ((v$1 (cnt (v$2) (let ((v$3 0)) (halt v$3))))
        |       (v$4 (cnt () (let ((v$5 1)) (v$1 v$5))))
        |       (v$6 (cnt () (let ((v$7 2)) (v$1 v$7))))
        |       (v$8 (cnt () (let* ((v$9 3) (v$10 4)) (if (@= v$9 v$10) v$4 v$6))))
        |       (v$11 3)
        |       (v$12 4))
        |  (if (@= v$11 v$12) v$8 v$6))""".stripMargin
    )

  @Test def testCondNestedExprTrue =
    testCPSHighTreeEquality(
      "(if (if (@ = 3 4) (if (@ = 3 4) #t #f) #t) 1 2)",
      """(let* ((v$1 (cnt (v$2) (let ((v$3 0)) (halt v$3))))
         |      (v$4 (cnt () (let ((v$5 1)) (v$1 v$5))))
         |      (v$6 (cnt () (let ((v$7 2)) (v$1 v$7))))
         |      (v$8 (cnt () (let* ((v$9 3) (v$10 4)) (if (@= v$9 v$10) v$4 v$6))))
         |      (v$11 3)
         |      (v$12 4))
         | (if (@= v$11 v$12) v$8 v$4))""".stripMargin
    )
}
