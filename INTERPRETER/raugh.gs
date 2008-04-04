data Sumbool = Left
             | Right

data Process chnl a = INJ (Guarded chnl a)
                    | PAR (Process chnl a) (Process chnl a)

data Guarded chnl a = TALK chnl a (Process chnl a) chnl (a -> Process chnl a)
                    | LISTEN chnl (a -> Process chnl a)

data Signal chnl a = Noise
                   | Clear a

data List a = Nil
            | Cons a (List a)

data Pointer = Succ
             | Fail
             | Left0 Pointer
             | Right0 Pointer

data Result chnl a = Tuple chnl (Signal chnl a) (Process chnl a)
                   | Error

data Trace chnl a = Stop (Process chnl a)
                | Evolve Pointer (List Pointer) chnl (Process chnl a) 
                          (Process chnl a) (Signal chnl a) (Trace chnl a)
                | Refuse Pointer (List Pointer) (Process chnl a) (Trace chnl a)

listen compare =
  let { listen p =
    case p of
      INJ g ->
        (case g of
           TALK c1 a0 p0 c2 f ->
             (\c0 -> case compare c2 c0 of
                       Left -> (\v -> f v)
                       Right -> (\v -> INJ (TALK c1 a0 p0 c2 f)))
           LISTEN c p0 ->
             (\c0 -> case compare c c0 of
                       Left -> (\v -> p0 v)
                       Right -> (\v -> INJ (LISTEN c p0))))
      PAR p0 p1 -> (\c v -> PAR (listen p0 c v) (listen p1 c v)) }
  in listen

say compare =
  let { say o p =
    case p of
      INJ g ->
        (case g of
           TALK x3 x2 x1 x0 x ->
             (case o of
                Succ -> Tuple x3 Noise x1
                Fail -> Tuple x3 (Clear x2) x1
                Left0 p0 -> Error
                Right0 p0 -> Error)
           LISTEN c p0 -> Error)
      PAR x0 x ->
        (case o of
           Succ -> Error
           Fail -> Error
           Left0 ol0 ->
             (case say ol0 x0 of
                Tuple c w x1 ->
                  (case w of
                     Noise -> Tuple c Noise (PAR x1 x)
                     Clear a1 ->
                       Tuple c (Clear a1) (PAR x1 (listen compare x c
                                                    a1)))
                Error -> Error)
           Right0 or_ren0 ->
             (case say or_ren0 x of
                Tuple c w x1 ->
                  (case w of
                     Noise -> Tuple c Noise (PAR x0 x1)
                     Clear a1 ->
                       Tuple c (Clear a1) (PAR (listen compare x0 c a1) x1))
                Error -> Error)) }
  in say

simulator compare =
  let { simulator x p =
    case x of
      Nil -> Stop p
      Cons o y ->
        (case say compare o p of
           Tuple c w q -> Evolve o y c p q w (simulator y q)
           Error -> Refuse o y p (simulator y p)) }
  in simulator

