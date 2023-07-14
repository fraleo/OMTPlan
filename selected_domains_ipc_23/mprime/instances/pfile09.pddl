(define (problem mprime-x-9)
   (:domain mystery-prime-typed)
   (:objects apple flounder haroset hamburger wurst hotdog guava
             - food
             entertainment intoxication curiosity excitement - pleasure
             dread sciatica abrasion prostatitis loneliness anger
             hangover anxiety laceration boils jealousy angina grief - pain
)
   (:init
(eats apple guava)
          (eats guava apple)
(= (locale hotdog) 1)
(= (locale wurst) 1)
          (craves hangover haroset)
          (craves loneliness haroset)
          (eats hamburger haroset)
(= (harmony intoxication) 1)
          (craves laceration wurst)
          (craves anxiety wurst)
          (eats flounder hamburger)
(= (locale hamburger) 0)
(= (harmony excitement) 1)
          (craves anger haroset)
          (craves curiosity hotdog)
          (craves dread flounder)

(= (harmony entertainment) 3)
          (craves intoxication haroset)
          (eats hamburger flounder)
          (craves angina guava)
          (eats haroset guava)

          (eats hotdog wurst)
          (eats guava haroset)
          (eats hotdog apple)
          (craves excitement guava)
          (craves jealousy guava)
          (craves sciatica flounder)
          (craves grief guava)
          (eats flounder wurst)
          (craves boils guava)
          (eats apple hotdog)
          (eats wurst flounder)
          (craves entertainment flounder)


(= (locale haroset) 2)
          (eats wurst hotdog)
(= (harmony curiosity) 1)

          (craves prostatitis haroset)

          (craves abrasion haroset)
(= (locale flounder) 2)
(= (locale guava) 4)

(= (locale apple) 2)
          (eats haroset hamburger))
   (:goal (and (craves sciatica hamburger)
               (craves jealousy wurst))))
