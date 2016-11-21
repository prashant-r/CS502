package l3
package test.ok
import org.junit.Test

trait ConstructsOKTests extends MainHelper {
  this: AllOKTests =>

  @Test def testAppOrder =
    compileAndInterpretWithLib("""
      (letrec ((int-fun-gen (fun () (let ((x (@byte-write (@char->int 'O')))) (fun (i) (@+ i 1))))))
	    (letrec ((int-gen (fun () (let ((y (@byte-write (@char->int 'K')))) 0))))
    	((int-fun-gen) (int-gen))))
    """)

  @Test def testLetrec =
    compileAndInterpretWithLib("""
      (letrec ((f (fun (x) (if (@> x 0) (g x) x)))
    		  (g (fun (x) (f (@- x 1)))))
      (@byte-write (@char->int 'O'))
      (if (@= (f 5) 0) (@byte-write (@char->int 'K')) (@byte-write (@char->int 'O'))))
    """)

}
