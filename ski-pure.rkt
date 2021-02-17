#lang racket
(require data/gvector)

(define idx-to-term (gvector 'I 'K 'S 'bot))
(define term-to-idx (make-hash '[(I . 0) (K . 1) (S . 2) (bot . 3)]))
(define reductions (gvector 0 1 2 3))

(define (reset)
  (set! idx-to-term (gvector 'I 'K 'S 'bot))
  (set! term-to-idx (make-hash '[(I . 0) (K . 1) (S . 2) (bot . 3)]))
  (set! reductions (gvector 0 1 2 3)))

(define (show-state)
  (display "idx-to-term: ") (display idx-to-term) (newline)
  (display "term-to-idx: ") (display term-to-idx) (newline)
  (display "reductions: ") (display reductions) (newline))

; need to reason about joint state of term-to-idx and reductions
; step is run when idx-to-term and term-to-idx have been updated, but reductions haven't

(define (step term gas) ; (step 10)
  (match (gvector-ref idx-to-term term)
    [(cons 0 x) x]
    [(cons a z)
     (match (gvector-ref idx-to-term a)
       [(cons 1 x) x]
       [(cons c y)
        (match (gvector-ref idx-to-term c)
          [(cons 2 x) (scons (scons x z (- gas 1))
                             (scons y z (- gas 1))
                             (- gas 1))]
          [_ term])]
       [_ term])]
    [_ term]))

; invariant: never lookup a number that is in term-to-idx but not in reductions
; invariant': if a number is in term-to-idx but not in reductions then some subtree evaluates to the original term
(define (lookup term gas)
  ; (lookup (cons 1 2) gas) ; (lookup 1 gas)
  (let ([found (hash-ref term-to-idx term #f)])
    (if found
        (let ([red-found (hash-ref reductions found #f)]) ;not terminating program
          (if red-found red-found
              (let ([idx (if (pair? term) (hash-ref term-to-idx term) term)])
                (hash-set! reductions idx idx)
                idx)))
        (if (number? term) (hash-ref reductions term)
            (let* ([t1 (hash-ref reductions (car term))]
                   [t2 (hash-ref reductions (cdr term))])
              (let ([new-id (gvector-count idx-to-term)])
                (gvector-add! idx-to-term term)
                (hash-set! term-to-idx term new-id)
                (if (= 0 gas) (let () (hash-set! reductions new-id 3) 3)
                    (let ([stepped (step new-id (- gas 1))])
                      (hash-set! reductions new-id stepped)
                      (let ([stepped-rec (lookup stepped (- gas 1))])
                        (hash-set! reductions new-id stepped-rec)
                        stepped-rec)))))))))


(define (scons t1 t2 gas)
  (lookup (cons t1 t2) gas))

; (share (cons 'S 'S))
(define (share term gas)
  (match term
    [(cons a b) (scons (share a (- gas 1))
                       (share b (- gas 1))
                       (- gas 1))]
    [x (lookup x (- gas 1))]))

(define (rand-ski) (list-ref '(I K S) (random 3)))
(define (rand-term p decay)
  (if (> (random) p)
      (rand-ski)
      (cons (rand-term (* p decay) decay) (rand-term (* p decay) decay))))


; the question is big step or small
; if big step then don't change reductions in step
#|
(show-state)
(scons 0 1) ; 1 ; I . K
(show-state)
(scons 0 1) ; 1
(show-state); unchanged hashes
(scons 0 3) ; 1 ; I I . K
(show-state); unchanged hashes

(scons (scons (scons 2 0) 0) 0) ; 0
(share '(((S . (K . I)) . I) . I)) ; 0

(to-ski (share '(((((I K (I . I) . S) . I) . I)
   (((((((S S . K) . I) . S) . I) . I) . K) . I)
   ((S . I) ((S . I) K . K) . S)
   (K . I)
   .
   K)
  ((((I . K) . S) S . K) ((I I . I) . S) . I)
  K
  (((K . K) ((K (S . S) . I) K . I) . S) . K)
  ((K . K) S . K)
  I
  .
  I)))

'(K . K)

'((((((I (S . S) (K . K) S K . K) I . K) (((K (S . S) . K) . K) . S) . S)
    (I (S . S) . S)
    (S S K (K . S) . S)
    ((S (S . I) . S) . K)
    K
    K
    ((S . I) . I)
    .
    K)
   .
   I)
  K
  .
  I)
0
(share (cons b 'S)) -> 2
(share (cons b 'K)) -> 1


(to-ski (share '(((S . I) . I).((S . I) . I))))
'(((S . I) . I) (S . I) . I)

racket@ski-pure.rkt> (to-ski (share a))
'(S (S S (S . S) . S) . I)
racket@ski-pure.rkt> a
'(S
  (((K I I . K) . K) (S ((K . S) . S) ((S I K S . S) (K . I) S . I) . S) . I)
  I
  I
  ((S S I . K) . I)
  .
  I)


|#

(define (tree-size t)
  (if (not (pair? t)) 1 (+ 1 (tree-size (car t)) (tree-size (cdr t)))))

(define (to-ski n)
  (let ([r (hash-ref reductions n)])
    (if (eq? r n)
        (let ([t (gvector-ref idx-to-term n)])
          (if (not (pair? t)) t (cons (to-ski (car t)) (to-ski (cdr t)))))
        (to-ski r))))

(define b
'((((I . S) . I) K (S S (I . I) (I . S) S (((K . S) . S) . I) . I) . K)
  (S . K)
  (((((K . I) . K) S ((K S . I) . S) K . S) . I) K S . S)
  ((K . S) . S)
  S
  ((I . S) I . I)
  .
  I))

(define c
  '((((I . S) ((S . I) . I) ((((I . I) . K) S S . I) . K) . S)
     (S . K)
     S
     K
     (K . K)
     .
     S)
    I
    .
    S))


#|

(to-ski (share b))
'((S S S S (S . I) . I) . K)

'((((I . S) . I) K (S S (I . I) (I . S) S (((K . S) . S) . I) . I) . K)
  (S . K)
  (((((K . I) . K) S ((K S . I) . S) K . S) . I) K S . S)
  ((K . S) . S)
  S
  ((I . S) I . I)
  .
  I)

(why does (share '(S I I . I)) ->  '(S . I)

one term of 297 that takes time
'((((((I
       (((S . I) ((K ((I . K) ((S . K) . K) . I) . I) S . S) S . K)
        (S I ((I . S) . I) . S)
        ((S (K . S) (K I . S) . I) . K)
        (K . I)
        .
        S)
       (((I . S) ((S . I) . I) ((((I . I) . K) S S . I) . K) . S)
        (S . K)
        S
        K
        (K . K)
        .
        S)
       I
       .
       S)
      ((S . I) . S)
      K
      .
      K)
     (K ((I . K) . K) (I I . S) . S)
     I
     I
     .
     S)
    .
    I)
   .
   K)
  (S
   S
   (((S . K) S K K . S)
    (((K . K) . K)
     S
     K
     (K ((((S I . S) (I . K) . K) (I . S) . K) S S . K) . I)
     ((((I . I) I . S) . K) . I)
     S
     (((S . K) . K) . S)
     .
     S)
    (K
     S
     ((I S . I) (K . S) . S)
     I
     ((I I . I) S ((I . I) . S) K . I)
     (I . S)
     .
     S)
    .
    I)
   S
   (((S K I (S . I) . I) I (((K . I) . S) . I) . I) . I)
   .
   I)
  .
  I

(share (caar a)) ; size 141
hash-ref: no value found for key
  key: 27

Tiny subpiece that causes problems -- non term
size 43
'((((I . S) ((S . I) . I) ((((I . I) . K) S S . I) . K) . S)
   (S . K)
   S
   K
   (K . K)
   .
   S)
  I
  .
  S)

Either subpiece (car + cdr) evaluates instantly

Once caches are polluted, all next evaluations are slow regardless of size

. 2830) (696 . 2830) (654 . 2830) (605 . 2830) (608 . 2830) (569 . 2830)
(523 . 2830) (526 . 2830) (490 . 2830) (447 . 2830) (450 . 2830) (417 . 2830)
(377 . 2830) (380 . 2830) (350 . 2830) (313 . 2830) (316 . 2830) (289 . 2830)
(255 . 2830) (258 . 2830) (234 . 2830) (203 . 2830) (206 . 2830) (185 . 2830)
(157 . 2830) (160 . 2830) (142 . 2830) (117 . 2830) (120 . 2830) (105 . 2830)
(83 . 2830) (86 . 2830) (74 . 2830) (60 . 2830) (69 . 2830) (50 . 2830) (46 . 2830)
(16 . 2830) (2 . 2830) (2912 . 2913) (11 . 2913) (4 . 2913) (2 . 2913) (2916 . 2917)
(0 . 2917) (2913 . 2917) (2917 . 2920) (2830 . 2913) (2733 . 2913) (2736 . 2913)
(2649 . 2913) (2555 . 2913) (2558 . 2913) (2474 . 2913) (2383 . 2913) (2386 . 2913)
(2305 . 2913) (2217 . 2913) (2220 . 2913) (2142 . 2913) (2057 . 2913) (2060 . 2913)
(1985 . 2913) (1903 . 2913) (1906 . 2913) (1834 . 2913) (1755 . 2913) (1758 . 2913)
(1689 . 2913) (1613 . 2913) (1616 . 2913) (1550 . 2913) (1477 . 2913) (1480 . 2913) (1417 . 2913) (1347 .


|#
