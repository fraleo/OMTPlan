(define (problem mprime-x-27)
   (:domain mystery-prime-typed)
   (:objects wurst guava muffin pork onion popover scallion - food
             triumph love satisfaction - pleasure
             abrasion anxiety dread loneliness grief boils - pain
)
   (:init
(= (locale wurst) 10)
          (craves abrasion wurst)

          (eats wurst guava)
          (eats pork muffin)

          (eats scallion muffin)
(= (locale onion) 12)
          (craves anxiety wurst)
          (eats scallion popover)
          (craves boils scallion)
(= (harmony satisfaction) 2)
          (eats muffin scallion)
(= (locale scallion) 5)
          (eats onion wurst)
          (eats scallion guava)

          (eats muffin pork)
          (craves triumph onion)
          (eats wurst onion)
          (craves dread wurst)
(= (harmony love) 2)



(= (locale popover) 9)
(= (harmony triumph) 3)


(= (locale guava) 9)
(= (locale muffin) 2)

          (eats muffin onion)
          (craves satisfaction scallion)
          (eats popover onion)
          (eats onion muffin)
          (eats popover scallion)

          (eats guava scallion)
          (eats onion pork)

          (eats guava wurst)

          (eats onion popover)
          (eats pork onion)

          (craves love popover)
          (craves loneliness scallion)
(= (locale pork) 5)
          (craves grief scallion)

)
   (:goal (and (craves grief guava)
               (craves boils guava))))
