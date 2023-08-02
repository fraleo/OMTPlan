(define (problem mprime-x-25)
   (:domain mystery-prime-typed)
   (:objects wurst tuna pistachio chicken - food
             expectation rest - pleasure
             depression angina - pain
)
   (:init
(eats wurst chicken)
          (eats tuna pistachio)
          (craves angina chicken)
          (eats chicken pistachio)
          (craves rest pistachio)
(= (locale tuna) 2)
          (eats chicken wurst)
(= (harmony expectation) 1)

          (craves expectation tuna)

          (craves depression wurst)
          (eats pistachio wurst)


          (eats tuna wurst)
(= (locale wurst) 2)
          (eats pistachio tuna)

          (eats wurst tuna)
(= (harmony rest) 3)

          (eats wurst pistachio)
          (eats pistachio chicken)


(= (locale chicken) 2)
(= (locale pistachio) 5))
   (:goal (and (craves depression chicken))))
