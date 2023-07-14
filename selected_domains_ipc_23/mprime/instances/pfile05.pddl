(define (problem mprime-x-5)
   (:domain mystery-prime-typed)
   (:objects broccoli chocolate turkey tuna sweetroll shrimp cherry
             scallop - food
             satisfaction excitement intoxication lubricity - pleasure
             sciatica anxiety grief boils depression abrasion prostatitis
             angina jealousy laceration anger grief-2 dread loneliness
             hangover - pain
)
   (:init
(eats scallop cherry)
          (craves satisfaction broccoli)
(= (harmony excitement) 3)
          (craves jealousy shrimp)
          (eats tuna broccoli)
          (eats sweetroll scallop)
          (craves grief broccoli)

          (craves intoxication tuna)

          (eats cherry shrimp)

          (eats shrimp sweetroll)
(= (locale tuna) 3)
          (eats cherry scallop)
          (craves hangover scallop)
(= (harmony lubricity) 2)
          (craves excitement turkey)
          (craves loneliness scallop)
          (eats broccoli chocolate)
          (craves depression turkey)
          (eats tuna turkey)
          (eats chocolate shrimp)
          (craves lubricity sweetroll)
(= (locale cherry) 1)
          (eats turkey chocolate)

          (eats shrimp cherry)
          (craves dread scallop)
          (craves grief-2 scallop)
          (craves angina shrimp)
(= (harmony satisfaction) 2)
          (eats chocolate turkey)
          (eats chocolate broccoli)

          (craves laceration shrimp)
          (craves anxiety broccoli)
(= (locale scallop) 0)
          (craves prostatitis turkey)
          (craves boils broccoli)
(= (locale shrimp) 1)
          (eats sweetroll shrimp)
(= (locale turkey) 1)
(= (locale broccoli) 3)
          (eats broccoli tuna)
          (craves abrasion turkey)
(= (locale chocolate) 2)
          (eats scallop sweetroll)
(= (harmony intoxication) 2)
          (eats shrimp chocolate)
          (craves anger cherry)
(= (locale sweetroll) 0)
          (craves sciatica broccoli)

          (eats turkey tuna))
   (:goal (and (craves loneliness shrimp)
               (craves grief shrimp))))
