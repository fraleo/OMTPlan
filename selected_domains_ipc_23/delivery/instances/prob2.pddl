(define (problem delivery-x-2)
   (:domain delivery)
   (:objects rooma roomb roomc - room
             item6 item5 item4 item3 item2 item1 - item
             bot1 bot2 - bot
             left1 right1 left2 right2 - arm)
   (:init (= (weight item6) 1)
          (= (weight item5) 1)
          (= (weight item4) 1)
          (= (weight item3) 1)
          (= (weight item2) 1)
          (= (weight item1) 1)

          (at item6 rooma)
          (at item5 rooma)
          (at item4 rooma)
          (at item3 rooma)
          (at item2 rooma)
          (at item1 rooma)
          
          (at-bot bot1 rooma)
          (at-bot bot2 rooma)
          (free left1)
          (free right1)
          (free left2)
          (free right2)
          (mount left1 bot1)
          (mount right1 bot1)
          (mount left2 bot2)
          (mount right2 bot2)
          
          (door rooma roomb)
          (door roomb rooma)
          (door rooma roomc)
          (door roomc rooma)
          
          (= (current_load bot1) 0)
          (= (load_limit bot1) 4)
          (= (current_load bot2) 0)
          (= (load_limit bot2) 4)
          (= (cost) 0))  
          
          
   (:goal (and (at item6 roomb)
               (at item5 roomb)
               (at item4 roomb)
               (at item3 roomb)
               (at item2 roomc)
               (at item1 roomc)))
               
   (:metric minimize (cost))
)
