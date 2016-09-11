package l3
package test.ok

import l3.L3FileReader.expandModules
import org.junit.Test

trait LibraryOKTests extends MainHelper {
  this: AllOKTests =>

  // TODO: This is dangerous, the students can inject an infinite loop via the library:
  lazy val library: String = {
    val fs = java.nio.file.FileSystems.getDefault
    val inFiles = expandModules(fs.getPath(""), Seq("../library/lib.ml3")).distinct
    val inSource = inFiles.map({ f => scala.io.Source.fromFile(f.toString).mkString }).mkString("\n")
    inSource
  }
  def compileAndInterpretWithLib: String => Unit = (source: String) => compileAndInterpret(library + "\n" + source)

  @Test def testLibFunctions1 =
    compileAndInterpretWithLib("""
      (char-print (if (function? function?) 'O' 'K'))
      (char-print (if (function? 42) 'O' 'K'))
      (newline-print)
    """)

  @Test def testLibFunctions2 =
    compileAndInterpretWithLib("""
      (char-print (if (@block? function?) 'O' 'K'))
      (char-print (if (= (@block-tag function?) 202) 'K' 'O'))
      (newline-print)
    """)

  @Test def testLibFunctions3 =
    compileAndInterpretWithLib("""
      (def succ (fun (x) (+ x 1)))
      (def twice (fun (x) (+ x x)))
      (char-print (@int->char ((function-compose succ twice) 39)))
      (char-print (@int->char ((function-compose succ succ) 73)))
      (char-print (@int->char ((function-compose twice succ) 4)))
    """)

  @Test def testLibLists1 =
    compileAndInterpretWithLib("""
      (char-print (if (list? list-empty) 'O' 'K'))
      (char-print (if (list? (list-make 42)) 'K' 'O'))
      (char-print (if (list? 42) '*' newline))
    """)

  @Test def testLibLists2 =
    compileAndInterpretWithLib("""
      (let ((l (list-make 'O' 'K' newline)))
      (char-print (list-head l))
      (char-print (list-head (list-tail l)))
      (char-print (list-head (list-tail (list-tail l)))))
    """)

  @Test def testLibLists3 =
    compileAndInterpretWithLib("""
      (let ((l (list-make 'O' 'K' newline)))
        (list-for-each char-print l))
    """)

  @Test def testLibLists4 =
    compileAndInterpretWithLib("""
      (def int-print-as-char (function-compose char-print int->char))
      (let ((l (list-make 78 74 9)))
        (list-for-each int-print-as-char (list-map (fun (x) (+ x 1)) l)))
    """)

  @Test def testLibLists5 =
    compileAndInterpretWithLib("""
      (def int-print-as-char (function-compose char-print int->char))
      (let ((o (list-make 79))
            (k (list-make 3 5 5))
            (nl (list-make 2 5))
            (prod (fun (l) (list-fold-left * 1 l))))
        (int-print-as-char (prod o))
        (int-print-as-char (prod k))
        (int-print-as-char (prod nl)))
    """)

  @Test def testLibLists6 =
    compileAndInterpretWithLib("""
      (def int-print-as-char (function-compose char-print int->char))
      (let ((o (list-make 79))
            (k (list-make 3 5 5))
            (nl (list-make 2 5))
            (prod (fun (l) (list-fold-right * 1 l))))
        (int-print-as-char (prod o))
        (int-print-as-char (prod k))
        (int-print-as-char (prod nl)))
    """)

  @Test def testLibLists7 =
    compileAndInterpretWithLib("""
      (def int-print-as-char (function-compose char-print int->char))
      (let ((l (list-make 1 79 2 3 1 75 10 2)))
        (list-for-each int-print-as-char (list-filter (fun (x) (>= x 10)) l)))
    """)

  @Test def testLibLists8 =
    compileAndInterpretWithLib("""
      (def int-print-as-char (function-compose char-print int->char))
      (let* ((l (list-make 75 10 79))
             (y/n (list-partition (fun (c) (< c 79)) l)))
        (list-for-each int-print-as-char (pair-snd y/n))
        (list-for-each int-print-as-char (pair-fst y/n)))
    """)

  @Test def testLibLists9 =
    compileAndInterpretWithLib("""
      (def int-print-as-char (function-compose char-print int->char))
      (let ((l (list-make 'O' 'K' newline 'K' 'O' newline)))
        (list-for-each char-print (list-take l 3)))
    """)

  @Test def testLibLists10 =
    compileAndInterpretWithLib("""
      (let ((l (list-make 'K' 'O' newline 'O' 'K' newline)))
        (list-for-each char-print (list-drop l 3)))
    """)

  @Test def testLibLists11 =
    compileAndInterpretWithLib("""
      (def int-print-as-char (function-compose char-print int->char))
      (let ((l5 (list-make 0 0 0 0 0))
            (l9 (list-make 0 0 0 0 0 0 0 0 0)))
        (int-print-as-char (+ 70 (list-length l9)))
        (int-print-as-char (+ 70 (list-length l5)))
        (int-print-as-char (- 10 (list-length list-empty))))
    """)

  @Test def testLibLists12 =
    compileAndInterpretWithLib("""
      (let ((l (list-make newline 'K' 'O')))
        (list-for-each char-print (list-reverse l)))
    """)

  @Test def testLibLists13 =
    compileAndInterpretWithLib("""
      (let ((l1 (list-make 'O' 'K'))
            (l2 (list-make newline)))
        (list-for-each char-print (list-append l1 l2)))
    """)

  @Test def testLibStrings1 =
    compileAndInterpretWithLib("""
      (char-print (if (string? "ok") 'O' 'K'))
      (char-print (if (string? 1337) 'O' 'K'))
      (newline-print)
    """)

  @Test def testLibStrings2 =
    compileAndInterpretWithLib("""
      (string-print "OK")
      (newline-print)
    """)

  @Test def testLibStrings3 =
    compileAndInterpretWithLib("""
      (let ((s "KO"))
        (char-print (string-get s 1))
        (char-print (string-get s 0))
        (newline-print))
    """)

  @Test def testLibStrings4 =
    compileAndInterpretWithLib("""
      (char-print (int->char (string-length "OOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOO")))
      (char-print (int->char (string-length "KKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKK")))
      (char-print (int->char (string-length "1111100000")))
    """)
}
