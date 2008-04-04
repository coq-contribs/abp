say c v p      = (TALK c v p c (\v -> (say c v p)))
data Channel   = Ch1
decide Ch1 Ch1 = True
decide Ch2 Ch2 = True
decide Ch1 Ch2 = False
decide Ch2 Ch1 = False
ack            = (LISTEN Ch1   (\v -> (say Ch1 (v+1) ack)))
system         = (PAR (say Ch1 0 ack) ack)

