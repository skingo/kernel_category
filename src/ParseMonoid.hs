
module ParseMonoid where

import Text.Parsec
import Text.Parsec.String

import Control.Monad

type Cong = ((Int, Int), Int)
type Element = (Int,String)

--  monoid :: Parser ([Element], [(String, [String])])
monoid :: Parser ([Element], Cong)
monoid = do
   let   element  = many1 (choice [letter, digit, oneOf "_-+"])
         eol      = choice [try (string "\r\n"), try (string "\n\r"), string "\n", string "\r"]
         spaces'  = many (oneOf " \t")
         spaces1' = many1 (oneOf " \t")
         eol'     = spaces' >> eol
         equivLine   = spaces' >> (,) <$> element <* spaces' <* char '|' <* spaces' <*> sepBy element spaces1'
   spaces
   elems <- fmap (zip [0..]) (sepBy element spaces1')
   eol'
   spaces' >> many1 (char '-') >> eol'
   equivLines <- endBy equivLine eol'
   return (elems,((0,0),0))
   --  return (elems, equivLines)

-- parseFromFile (monoid >>= (eof >>) . return) "test.file"


