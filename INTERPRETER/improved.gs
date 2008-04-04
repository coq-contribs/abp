data List    a   = Nil  | Cons a (List a)
data Signal    b = Noise | Clear b
data Pointer     = Succ  | Fail | Left Pointer | Right Pointer
data Result  a b = Error | Tuple a (Signal b) (Process a b) 
data Trace   a b = Stop | Refuse (Trace a b) | Evolve a (Signal b) (Trace a b)
data Process a b = TALK   a b (Process a b) a (b -> Process a b)
                 | LISTEN a (b -> Process a b)
                 | PAR    (Process a b) (Process a b)

listen compare =
 let {listen_rec p c0 v =
  case p of
    TALK c1 a0 p0 c2 f -> if (compare c2 c0) then (f v) else (TALK c1 a0 p0 c2 f)
    LISTEN c f         -> if (compare c  c0) then (f v) else (LISTEN c f)
    PAR p0 p1          -> PAR (listen_rec p0 c0 v) (listen_rec p1 c0 v) }
 in listen_rec

speak compare  =
  let { speak_rec o p =
    case p of
      TALK x3 x2 x1 x0 x ->
                  (case o of
                     Succ     -> Tuple x3 (Clear x2) x1
                     Fail     -> Tuple x3 Noise x1
                     _        -> Error)
      LISTEN c f     -> Error
      PAR x0 x       ->
        (case o of
           Left ol   ->
             (case (speak_rec ol x0) of
                Tuple c0 w0 x0 ->
                  (case w0 of
                     Noise    -> Tuple c0 Noise (PAR x0 x)
                     Clear a1 -> Tuple c0 (Clear a1) (PAR x0 (listen compare x c0 a1)))
                Error         -> Error)
           Right or   ->
             (case (speak_rec or x) of
                Tuple c w x1   ->
                  (case w of
                     Noise    -> Tuple c Noise (PAR x0 x1)
                     Clear a0 -> Tuple c (Clear a0) (PAR (listen compare x0 c a0) x1))
                Error         -> Error)
           _         -> Error) }
  in speak_rec

simulator compare =
  let { simulator_rec x p =
    case x of
      Nil      -> Stop
      Cons o y -> (case (speak compare o p) of
                     Tuple c w q -> Evolve c w (simulator_rec y q)
                     Error       -> Refuse     (simulator_rec y p)) }
  in simulator_rec


