;;; Set Language to Full Swindle

;;; ps2.scm ; BRD/PS 2022

(require racket/base) ;;This allows the type system to work.

(require rnrs/mutable-pairs-6)

(define square

  (lambda ((n <number>))

    (* n n)))



;; ----- Data type definitions -----



;; Keys are implemented as simple pairs

(define <key> <pair>)



;; Constructors and accessors for RSA keys:

(define make-key

  (lambda ((exponent <integer>) (modulus <integer>))

    (cons exponent modulus)))



(define key-exponent car)

(define key-modulus  cdr)



;; A key pair is just a pair whose head is the public key and

;; whose tail is the private key

(define <key-pair> <pair>)



;; Constructor and accessors for key pairs

(define make-key-pair

  (lambda ((public <key>) (private <key>))

    (cons public private)))



(define key-pair-public  car)

(define key-pair-private cdr)



;; A message is a list of integers, the blocks of the message

(define <message> <list>)



;; A signed message consists of a message + a signature

(define <signed-message> <pair>)



;; Constructor and accessors for signed messages

(define make-signed-message

  (lambda ((message <message>) (signature <integer>))

    (cons message signature)))



(define signed-message-body car)

(define signed-message-signature cdr)



;; ----- The RSA transformation -----



(define rsa-transform

  (lambda ((number <integer>) (key <key>))

    (exptmod number 

	     (key-exponent key) 

	     (key-modulus key))))



(define rsa-convert-list

  (lambda ((lst <list>) (key <key>))

    (let ((n (key-modulus key)))

      (let loop ((rst lst) (prev 0))

	(cond ((null? rst) rst)

	      (else

	       (let ((cur (rsa-transform (modulo (+ (car rst) prev) n) key)))

		 (cons cur 

		       (loop (cdr rst) cur)))))))))

			     



(define rsa-encrypt

  (lambda ((msg <string>) (key <key>))

    (rsa-convert-list (string->intlist msg) key)))



(define rsa-decrypt

  (lambda ((msg <message>) (key <key>))

    (intlist->string (rsa-unconvert-list msg key))))



;; ----- RSA key generation functions -----



;; (choose-prime smallest range)

;; Find an odd prime by sequential search, beginning at a random

;; point within 'range' of 'smallest'



(define choose-prime

  (lambda ((smallest <integer>) (range <integer>))

    (let ((start (+ smallest (bigrand range))))

      (search-prime

       (if (even? start) 

	   (+ start 1) 

	   start)))))



;; Sequentially search for an odd prime beginning at 'guess'

;; Assumes 'guess' is odd

(define search-prime

  (lambda ((guess <integer>))

    (cond ((divisible-by-primes? guess)

	   (search-prime (+ guess 2)))

	  ((fast-prime? guess)

           guess)

          (else

           (search-prime (+ guess 2))))))



;; Uses Fermat's theorem to quickly test if a number is composite

;; Returns #f if 'candidate' is definitely composite, #t if it may

;; be prime.

(define fermat-test

  (lambda ((candidate <integer>) (witness <integer>))

    (= (exptmod witness candidate candidate) witness)))



;; Uses fermat-test to test whether a candidate is prime

;; Returns #f if candidate is definitely composite, #t if it may 

;; be prime.

(define fast-prime?

  (lambda ((candidate <integer>))

    (and (fermat-test candidate 2)

         (fermat-test candidate 3)

         (fermat-test candidate 5)

         (fermat-test candidate 7))))



;; Test whether candidate is divisible by some small known primes.

;; This eliminates a lot of candidates quickly, and avoids the more

;; expensive fermat-test (this is important when you are generating

;; big keys!  It also helps avoid Carmichael numbers.



(define *small-primes* (list 2 3 5 7 11 13 17 23))



(define divisible-by-primes?

  (lambda ((candidate <integer>))

    (let loop ((primes *small-primes*))

      (cond ((null? primes) #f)

	    ((divides? (car primes) candidate) (car primes))

	    (else

	     (loop (cdr primes)))))))



;; Generate an RSA key pair with a modulus of 'bits' significant bits.

(define generate-rsa-key-pair

  (lambda ((bits <integer>))

    (let* ((base (expt 2 (quotient bits 2)))

           (p (choose-prime base base))

           (q (choose-prime base base)))

      (if (= p q)   ; Try again if we choose the same prime twice

          (generate-rsa-key-pair bits)

          (let* ((n (* p q))        ; key modulus

                 (m (- n p q -1))   ; m = (p - 1)(q - 1) = n - p - q + 1

                 (z (select-exponents m)) ; choose e and d

                 (e (car z))

                 (d (cdr z)))

            (make-key-pair (make-key e n)

                           (make-key d n)))))))



;; Choose a random encryption exponent and compute the corresponding

;; decryption exponent, given phi(n) = (p - 1)(q - 1)

(define select-exponents

  (lambda ((m <integer>))

    (let* ((e (random (expt 2 15)))

           (z (euclid e m))

           (g (caddr z)))

      (if (= g 1)

          (cons e (modulo (car z) m))

          (select-exponents m)))))  ; try again if e doesn't work



;; ----- Encoding and decoding messages -----

;;

;; These procedures convert between strings and lists of integers in

;; the range 0 .. 2^14.  You don't need to study this code; you can

;; just use it as is.



(define (make-string-padder size)

  (lambda ((str <string>))

    (let ((rem (modulo (string-length str) size)))

      (if (zero? rem)

	  str

	  (string-append str (make-string (- size rem)))))))



(define (make-string-to-intlist-func bits)

  (let* ((size (quotient (+ bits 6) 7))

	 (pad (make-string-padder size)))

    (lambda ((str <string>))

      (let loop ((in (map char->integer (string->list (pad str))))

		 (out '()))

	(cond ((null? in) (reverse out))

	      (else

	       (let-values (((firstk rest) (first-k in size)))

		  (let ((value

			 (let accum ((tot 0) (lst firstk))

			   (cond ((null? lst) tot)

				 (else

				  (accum (+ (* tot 128) (car lst))

					 (cdr lst)))))))

		    (loop rest (cons value out))))))))))



(define (make-intlist-to-string-func bits)

  (define (split-val val size)

    (cond ((zero? size) '())

	  (else 

	   (cons (modulo val 128) 

		 (split-val (quotient val 128) 

			    (- size 1))))))

  (let* ((size (quotient (+ bits 6) 7)))

    (lambda ((lst <list>))

      (let loop ((in lst) (out '()))

	(cond ((null? in)

	       (list->string

		(map integer->char

		     (filter (lambda (c) (not (zero? c))) (reverse out)))))

	      (else

	       (loop (cdr in)

		     (append (split-val (car in) size) out))))))))



;; Convert a string to a list of numbers 

(define string->intlist (make-string-to-intlist-func 14))



;; Convert a list of numbers to a string

(define intlist->string (make-intlist-to-string-func 14))



;; Returns two values, the first k elements of the list, and the rest

;; of the list

(define (first-k lst k)

  (let loop ((n k) (out '()) (rst lst))

    (cond ((or (null? rst)

	       (zero? n))

	   (values (reverse out) rst))

	  (else

	   (loop (- n 1)

		 (cons (car rst) out)

		 (cdr rst))))))



;; ----- Useful mathematical functions -----



;; (bigrand value) - returns a pseudorandom number in the range

;; 0 .. value-1.

(define bigrand

  (lambda ((value <integer>))

    (let loop ((cur 0))

      (cond ((> cur value)

             (modulo cur value))

            (else

             (loop (+ (* cur 256) (random 256))))))))



;; (divides? a m)

;; Returns true iff a divides m

(define divides?

  (lambda ((a <integer>) (m <integer>))

    (zero? (modulo m a))))



;; (exptmod b e m)

;; Compute b to the e power, modulo m (i.e., b^e (mod m))

(define exptmod

  (lambda ((b <integer>) (e <integer>) (m <integer>))

    (cond ((zero? e) 1)

          ((even? e)

           (modulo (square (exptmod b (quotient e 2) m)) m))

          (else

           (modulo (* b (exptmod b (- e 1) m)) m)))))



;; (euclid a m)

;; Computes the greatest common divisor of a and m using 

;; an extension of Euclid's algorithm.  Returns a list 

;; (s t g) where g = (a, m) and s, t are constants satisfying

;; Bezout's identity (sa + tm = g)

(define euclid

  (lambda ((a <integer>) (m <integer>))

    (cond ((zero? m) (list 1 0 a))

          (else

           (let* ((q (quotient a m))

                  (r (modulo a m))

                  (z (euclid m r))

                  (u (car z))

                  (v (cadr z))

                  (g (caddr z)))

             (list v (- u (* q v)) g))))))



;; (smallest-divisor n)

;; Finds the smallest divisor d > 1 of n by trial division



(define smallest-divisor

  (lambda ((n <integer>))

    (if (even? n)

	2

	(let ((sqrt-n (floor (sqrt n))))

	  (let loop ((try 3))

	    (cond ((> try sqrt-n) n)        ; stop if we get to sqrt(n)

		  ((divides? try n) try)    ; stop if we find a divisor

		  (else

		   (loop (+ try 2)))))))))  ; try the next odd divisor



;; ----- Compression (hash) function -----



;; Returns a compression function for values up to the specified size

;;

;; Each value is squared and multiplied by the index of its position

;; in the sequence, modulo a suitable prime.  The output is the

;; modular sum of these over all elements of the sequence.



(define (make-compression-func bits)

  ;; Find the first prime less than or equal to start (assumed odd)

  (define (find-modulus start)

    (cond ((or (divisible-by-primes? start)

	       (not (fast-prime? start)))

	   (find-modulus (- start 2)))

	  (else start)))



  (let* ((start (- (expt 2 bits) 1))

	 (modulus (find-modulus start)))



    (lambda ((lst <list>) (key <key>))

      (define (nexthash prev x i m)

	(modulo (+ prev (* x x i) i) m))



      (let loop ((index 1) (hash 0) (rst lst))

	(cond ((null? rst) (modulo hash (key-modulus key)))

	      (else

	       (loop (+ index 1)

		     (nexthash hash (car rst) index modulus)

		     (cdr rst))))))))



;; A compion function suitable for 18-bit integers

(define compress (make-compression-func 18));





;; ----- Test data and sample keys -----



;; Public keys

;; Change these keys every year

(define Ellie (make-key 32455 108371))

(define Jacob (make-key 30529 216221))

(define Paige (make-key 28859 135659))

(define Kyle  (make-key 28559 171967))

(define Rhea  (make-key 27089 89701))



;; Key pairs for testing purposes

(define test-key-1

  (make-key-pair 

   (make-key 2587 573193) 

   (make-key 28947 573193)))



(define test-key-2

  (make-key-pair

   (make-key 13889 557983)

   (make-key 269249 557983)))



(define big-key-1

  (make-key-pair

   (make-key 19307 43565950551638075623)

   (make-key 35440349052136018387 43565950551638075623)))



(define big-key-2

  (make-key-pair 

   (make-key 22059 30199096579027135423)

   (make-key 22743442190663818579 30199096579027135423)))



(define secret-message

	(make-signed-message

		'(3174 38202 77138 71385 81038 71311 26466 45345 64330 63743 41048 5249 55422

                       84941 13614 23637 76535 68461 81164 31479 69731 86306 21687 89307 57745

                       31010 71640 21027 30303 73381 13543 41338 85082 72323 23270 70995 25730

                       26285 80156 7293 75716 7665 86421 51686 20951 48544 49062 27938 36311

                       31950 65006 24797 37764 77038 31377 11571 51867 6239)

		53503))

(define result-1

     (rsa-encrypt "test message" (key-pair-public test-key-1)))

result-1

;;; Returns a decrypted message from an RSA-encrypted list, given the private key and ciphertext.

(define rsa-unconvert-list
  (λ ((lst <list>) (key <key>))
    (let ((n (key-modulus key)))
      (let loop ((rst lst) (prev 0) (oldlst (cons 0 lst)))
            (if (null? rst)
                rst
                (let ((cur (if (zero? prev)
                               (rsa-transform (car rst) key)
                               (modulo (- (rsa-transform (car rst) key) (car oldlst)) n))))
                  (cons cur
                        (loop (cdr rst) cur (cdr oldlst)))))))))


(display "Problem 1 Test Cases\n")
(rsa-unconvert-list result-1 (key-pair-private test-key-1))

(define test-message-long 

   (rsa-encrypt 

        "Cryptography plays an important role in establishing and maintaining privacy in a world that increasingly relies on digital records and communication. Whereas once, encryption was the sole province of powerful government and military institutions, today it is an essential tool for virtually every citizen of a modern nation." 
 

    (car test-key-2)))

(rsa-decrypt test-message-long (cdr test-key-2))

(define short-test
  (rsa-encrypt "Testing testing 1 2 3" (car test-key-1)))

(rsa-decrypt short-test (cdr test-key-1))

(define short-test
  (rsa-encrypt "Testing testing 1 2 3" (car test-key-2)))

(rsa-decrypt short-test (cdr test-key-2))

(define longer-test
  (rsa-encrypt "In a hole in the ground there lived a hobbit. Not a nasty, dirty, wet hole, filled with the ends of worms and an oozy smell, nor yet a dry, bare, sandy hole with nothing in it to sit down on or to eat: it was a hobbit-hole, and that means comfort."
               (car test-key-2)))
(rsa-decrypt longer-test (cdr test-key-2))

(define longer-test
  (rsa-encrypt "In a hole in the ground there lived a hobbit. Not a nasty, dirty, wet hole, filled with the ends of worms and an oozy smell, nor yet a dry, bare, sandy hole with nothing in it to sit down on or to eat: it was a hobbit-hole, and that means comfort."
               (car test-key-2)))
(rsa-decrypt longer-test (cdr test-key-2))

;outputs
;(14949 14836 4205 13043 14817 13285)
;Cryptography plays an important role in establishing and maintaining privacy in a world that increasingly relies on digital records and communication. Whereas once, encryption was the sole province of powerful government and military institutions, today it is an essential tool for virtually every citizen of a modern nation."
;"Testing testing 1 2 3"
;"Testing testing 1 2 3"
;"In a hole in the ground there lived a hobbit. Not a nasty, dirty, wet hole, filled with the ends of worms and an oozy smell, nor yet a dry, bare, sandy hole with nothing in it to sit down on or to eat: it was a hobbit-hole, and that means comfort."
;"In a hole in the ground there lived a hobbit. Not a nasty, dirty, wet hole, filled with the ends of worms and an oozy smell, nor yet a dry, bare, sandy hole with nothing in it to sit down on or to eat: it was a hobbit-hole, and that means comfort."


;;; Problem 2
(define encrypt-and-sign
  (λ ((str <string>) (rec <key>) (send <key>))
    (let ((h (rsa-encrypt str rec)))
      (cons h
            (rsa-transform (compress h send) send)))))

(define result-2

     (encrypt-and-sign "Test message from User 1 to User 2"

                       (key-pair-public test-key-2)

                       (key-pair-private test-key-1)))


(display "Problem 2 Encrypt Test Cases\n")
(signed-message-body result-2)
(signed-message-signature result-2)

(define decrypt-and-verify
  (λ ((mess <signed-message>) (rec <key>) (send <key>))
    (let* ((sig (signed-message-signature mess))
           (ciph (signed-message-body mess))
           (h (rsa-transform
              sig
              send))
           (tst (compress ciph send)))
      (if (equals? h tst)
          (rsa-decrypt ciph rec)
          #f))))

(display "Problem 2 Encrypt Test Cases\n")
(decrypt-and-verify result-2 

                     (key-pair-private test-key-2)

                     (key-pair-public test-key-1))
            
(decrypt-and-verify result-2

                     (key-pair-private test-key-1)

                     (key-pair-public test-key-2))

(define result-3 (encrypt-and-sign "In a hole in the ground there lived a hobbit. Not a nasty, dirty, wet hole, filled with the ends of worms and an oozy smell, nor yet a dry, bare, sandy hole with nothing in it to sit down on or to eat: it was a hobbit-hole, and that means comfort."
                  (key-pair-public big-key-1)
                  (key-pair-private big-key-2)))

(decrypt-and-verify result-3
                    (key-pair-private big-key-1)
                    (key-pair-public big-key-2))


;outputs 
;(141024 48674 204177 339709 317361 307215 225252 330769 134147 215314 540102 3551 396788 42331 536293 214006 171543)
;163298
;"Test message from User 1 to User 2"
;#f
;"In a hole in the ground there lived a hobbit. Not a nasty, dirty, wet hole, filled with the ends of worms and an oozy smell, nor yet a dry, bare, sandy hole with nothing in it to sit down on or to eat: it was a hobbit-hole, and that means comfort."

;;; Problem 3

(define crack-rsa
  (λ ((key <key>))
    (let* ((n (key-modulus key))
           (p (smallest-divisor n))
           (q (/ n p))
           (m (* (- p 1) (- q 1))))
          (cons (modulo (car (euclid (key-exponent key) m)) ;;; The value of a originally created in determining e
                        m)
                n))))

(display "Problem 3 test cases\n")
(crack-rsa (key-pair-public test-key-1)) ;; Test cases to check RSA crack is working
(key-pair-private test-key-1)  ;;; Expect: (28947 . 573193)

(crack-rsa (key-pair-public test-key-2))
(key-pair-private test-key-2) ;;; Expect: (269249 . 557983)

(display "Problem 3 requested outputs\n")
(crack-rsa (make-key 1763 132731)) ;;; Requested outputs

(crack-rsa (make-key 19883 159197))

(crack-rsa (make-key 25639 210281))

;outputs
;Problem 3 test cases
;(28947 . 573193)
;(28947 . 573193)
;(269249 . 557983)
;(269249 . 557983)

;Problem 3 requested outputs
;(42827 . 132731)
;(81347 . 159197)
;(168151 . 210281)

;;; Problem 4

(define names&keys (list (cons "Ellie" (list Ellie))
                         (cons "Jacob" (list Jacob))
                         (cons "Paige" (list Paige))
                         (cons "Kyle" (list Kyle))
                         (cons "Rhea" (list Rhea))
                         ))



(define E_pr (crack-rsa Ellie))
(define J_pr (crack-rsa Jacob))
(define P_pr (crack-rsa Paige))
(define K_pr (crack-rsa Kyle))
(define R_pr (crack-rsa Rhea))

(decrypt-and-verify secret-message (crack-rsa Ellie) Paige)

(display "Ellie/Jacob\n")
(decrypt-and-verify secret-message E_pr Jacob) 
(decrypt-and-verify secret-message J_pr Ellie)

(display "Ellie/Paige\n")
(decrypt-and-verify secret-message E_pr Paige) 
(decrypt-and-verify secret-message P_pr Ellie)

(display "Ellie/Kyle\n")
(decrypt-and-verify secret-message E_pr Kyle) 
(decrypt-and-verify secret-message K_pr Ellie)

(display "Ellie/Rhea\n")
(decrypt-and-verify secret-message E_pr Rhea) 
(decrypt-and-verify secret-message R_pr Ellie)

(display "Jacob/Paige\n")
(decrypt-and-verify secret-message J_pr Paige) 
(decrypt-and-verify secret-message P_pr Jacob)

(display "Jacob/Kyle\n")
(decrypt-and-verify secret-message J_pr Kyle) 
(decrypt-and-verify secret-message K_pr Jacob)

(display "Jacob/Rhea\n")
(decrypt-and-verify secret-message J_pr Rhea) 
(decrypt-and-verify secret-message R_pr Jacob)

(display "Paige/Kyle\n")
(decrypt-and-verify secret-message P_pr Kyle) 
(decrypt-and-verify secret-message K_pr Paige)

(display "Paige/Rhea\n")
(decrypt-and-verify secret-message P_pr Rhea) 
(decrypt-and-verify secret-message R_pr Paige)

(display "Kyle/Rhea\n")
(decrypt-and-verify secret-message K_pr Rhea) 
(decrypt-and-verify secret-message R_pr Kyle)


;;; Problem 5

(define pollard
  (λ ((n <integer>) (b <integer>) (max <integer>))
    (pollard-iter 1 n b max)))

(define pollard-iter
  (λ ((k <integer>) (n <integer>) (b <integer>) (max <integer>))
    (if (< max k)
        #f
        (let* ((r (exptmod b k n))
              (d (gcd (- r 1) n)))
         (if (or (= d 1) (= d n))
             (pollard-iter (+ k 1)
                           n
                           r
                           max)
             d)))))

(display "Problem 5 test cases\n")
(pollard 29958343 2 20) ; Expected: 4861
(pollard 13549648109 3 150) ; Expected : 122081
(pollard 5157437 2 7)  ; Expected: #f
(pollard 5157437 2 9)  ; Expected: 2269 
(pollard 34297190193172563733 3 35000) ; Expected: 5217557483

(display "Problem 5 Requested outputs\n")
(pollard 39173679876983836729 3 3000)
(pollard 2278570691794489592002651 2 27000)

(define crack-rsa-2
  (λ ((key <key>) (b <integer>) (max <integer>))
    (if (equals? #f
                (pollard (key-modulus key) b max))
        #f
        (let* ((n (key-modulus key))
           (p (pollard n b max))
           (q (/ n p))
           (m (* (- p 1) (- q 1))))
          (cons (modulo (car (euclid (key-exponent key) m)) ;;; The value of a originally created in determining e
                        m)
                n)))))

(crack-rsa-2 (key-pair-public big-key-1) 2 10000)
'(35440349052136018387 . 43565950551638075623)
(crack-rsa-2 (key-pair-public big-key-2) 2 10000)
(crack-rsa-2 (key-pair-public big-key-2) 2 20000)
'(22743442190663818579 . 30199096579027135423)

(display "Outputs for EC")
  (crack-rsa-2 (make-key 37 9709644929798597233) 2 15000)

  (crack-rsa-2 (make-key 3841 15873420455170035847) 2 10000)

  (crack-rsa-2 (make-key 17333 47126568369600710999) 2 10000)
          
;(3673919700704867653 . 9709644929798597233)
;(1735703355329074561 . 15873420455170035847)
;#f

;; ------------------------------------------------------------------------

;; here there be dragons