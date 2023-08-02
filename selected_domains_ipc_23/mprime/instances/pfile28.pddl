(define (problem mprime-x-28)
   (:domain mystery-prime-typed)
   (:objects wurst shrimp muffin broccoli lamb - food
             intoxication - pleasure
             loneliness anxiety hangover anger angina boils grief - pain
)
   (:init
(craves hangover shrimp)

          (craves anger muffin)
          (eats lamb shrimp)
          (eats shrimp wurst)
          (eats wurst muffin)
          (craves intoxication wurst)

          (eats broccoli lamb)
          (eats wurst lamb)
          (eats muffin wurst)
          (craves boils broccoli)
(= (locale shrimp) 6)

          (eats broccoli muffin)
(= (locale lamb) 7)

          (eats shrimp lamb)

          (craves anxiety shrimp)
(= (locale broccoli) 7)
(= (harmony intoxication) 2)
          (craves grief lamb)
(= (locale wurst) 1)

          (eats wurst shrimp)
(= (locale muffin) 2)

          (eats lamb wurst)

          (eats lamb broccoli)
          (craves angina muffin)
          (craves loneliness wurst)
          (eats muffin broccoli)
)
   (:goal (and (craves anger lamb)
               (craves boils lamb))))
