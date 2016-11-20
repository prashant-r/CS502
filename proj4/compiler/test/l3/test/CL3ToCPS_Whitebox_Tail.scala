package l3.test

import l3.test.infrastructure.CPSHighTest
import org.junit.Test

/** Whitebox testing for entire program outputs */
class CL3ToCPS_Whitebox_Tail extends CPSHighTest {

  @Test def testTailUselessContinuations =
    testCPSHighTreeEquality("(letrec ((f (fun (g) (g)))) f)", "(let* ((v$1 (fun (v$2 v$3) (v$3 v$2))) (v$4 0)) (halt v$4))")

  @Test def testTailIfInsideLetRec =
    testCPSHighTreeEquality("(fun (x y) (if #t x y))",
        """(let* ((v$1
          |        (fun (v$2 v$3 v$4)
          |          (let* ((v$5 (cnt () (v$2 v$3)))
          |                 (v$6 (cnt () (v$2 v$4)))
          |                 (v$7 #t)
          |                 (v$8 #f))
          |            (if (@!= v$7 v$8) v$5 v$6))))
          |       (v$9 0))
          |  (halt v$9))""".stripMargin)

  @Test def testTailNestedIf =
    testCPSHighTreeEquality("""
      |(let ( (n (@< 2 3)) )
      |  (if (@= n #t)
      |    (@byte-write (@char->int 'O'))
      |    (@byte-write (@char->int 'N'))
      |  )
      |)""".stripMargin,

      """(let* ((v$1
        |        (cnt (v$2)
        |          (let* ((v$3 (@id v$2))
        |                 (v$4 (cnt (v$5) (let ((v$6 0)) (halt v$6))))
        |                 (v$7
        |                  (cnt ()
        |                    (let* ((v$8 'O')
        |                           (v$9 (@char->int v$8))
        |                           (v$10 (@byte-write v$9)))
        |                      (v$4 v$10))))
        |                 (v$11
        |                  (cnt ()
        |                    (let* ((v$12 'N')
        |                           (v$13 (@char->int v$12))
        |                           (v$14 (@byte-write v$13)))
        |                      (v$4 v$14))))
        |                 (v$15 #t))
        |            (if (@= v$3 v$15) v$7 v$11))))
        |       (v$16 (cnt () (let ((v$17 #t)) (v$1 v$17))))
        |       (v$18 (cnt () (let ((v$19 #f)) (v$1 v$19))))
        |       (v$20 2)
        |       (v$21 3))
        |  (if (@< v$20 v$21) v$16 v$18))""".stripMargin)
}
