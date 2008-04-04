lexer ('L':x)      = (case (lexer x) of (w,y)-> ((Left   w),y))
lexer ('R':x)      = (case (lexer x) of (w,y)-> ((Right  w),y))
lexer ('S':'\n':x) = (Succ,x)
lexer ('F':'\n':x) = (Fail,x)
lexer (_:x)        = lexer x

parser [] = Nil
parser x  = (case (lexer x) of (w,y) -> (Cons w (parser y)))

printer (Evolve c Noise t) = 
  "A message was lost.\n "++(printer t)
 
printer (Evolve c (Clear v) t) = 
  "The following message is heard: "++
   (primPrint 1 c ("!"++(primPrint 0 v ("\n"++(printer t)))))
 
printer (Refuse  t)    = 
  "Bad choice! Try again ...\n"++(printer t)

printer Stop  = 
  "Good bye.\n"

go  :: (a->a->Bool)->(Process a b)->Dialogue
go  f example ~(read:s)  = [ReadChan stdin, AppendChan stdout result]
 where result = case read of 
      Str  contents -> (printer  (simulator f (parser contents) example ))
      Failure _     -> "Can't open stdin"
