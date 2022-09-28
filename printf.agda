module printf where

open import Agda.Builtin.String
open import Agda.Builtin.Int
open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.Float
open import Agda.Builtin.Char
open import Agda.Builtin.Bool

record Show A : Set where
  field
    show : A → String

open Show ⦃...⦄

instance
  ShowString : Show String
  ShowString .show = λ x → x

  ShowNat : Show Nat
  ShowNat .show = primShowNat

  ShowInt : Show Int
  ShowInt .show = primShowInteger

  ShowFloat : Show Float
  ShowFloat .show = primShowFloat

data _×_ (L R : Set) : Set where
  _,_ : L → R → L × R

toList : String → List Char
toList = primStringToList

toString : List Char → String
toString = primStringFromList

_<>_ : String → String → String
_<>_ = primStringAppend

reverse : {A : Set} → List A → List A
reverse xs = revHelper xs []
  where
    revHelper : {A : Set} → List A → List A → List A
    revHelper [] accum = accum
    revHelper (x ∷ xs) accum = revHelper xs (x ∷ accum)

data Chunk : Set where
  lit : String → Chunk
  %s : Chunk
  %u : Chunk
  %d : Chunk
  %f : Chunk

toLit : List Char → Chunk
toLit xs = lit (toString (reverse xs))

parseFormatList : List Char → List Char → List Chunk → List Chunk
parseFormatList []                 []       chunkAccum = reverse chunkAccum
parseFormatList []                 strAccum chunkAccum = parseFormatList []   []             (toLit strAccum ∷ chunkAccum)
parseFormatList ('%' ∷ 's' ∷ rest) []       chunkAccum = parseFormatList rest []             (%s ∷ chunkAccum)
parseFormatList ('%' ∷ 's' ∷ rest) strAccum chunkAccum = parseFormatList rest []             (%s ∷ toLit strAccum ∷ chunkAccum)
parseFormatList ('%' ∷ 'u' ∷ rest) []       chunkAccum = parseFormatList rest []             (%u ∷ chunkAccum)
parseFormatList ('%' ∷ 'u' ∷ rest) strAccum chunkAccum = parseFormatList rest []             (%u ∷ toLit strAccum ∷ chunkAccum)
parseFormatList ('%' ∷ 'd' ∷ rest) []       chunkAccum = parseFormatList rest []             (%d ∷ chunkAccum)
parseFormatList ('%' ∷ 'd' ∷ rest) strAccum chunkAccum = parseFormatList rest []             (%d ∷ toLit strAccum ∷ chunkAccum)
parseFormatList ('%' ∷ 'f' ∷ rest) []       chunkAccum = parseFormatList rest []             (%f ∷ chunkAccum)
parseFormatList ('%' ∷ 'f' ∷ rest) strAccum chunkAccum = parseFormatList rest []             (%f ∷ toLit strAccum ∷ chunkAccum)
parseFormatList (x ∷ xs)           strAccum chunkAccum = parseFormatList xs   (x ∷ strAccum) chunkAccum

parseFormat : String → List Chunk
parseFormat str = parseFormatList (toList str) [] []

ChunkType : List Chunk → Set
ChunkType [] = String
ChunkType (lit x ∷ chunks) = ChunkType chunks
ChunkType (%s ∷ chunks) = String → ChunkType chunks
ChunkType (%u ∷ chunks) = Nat → ChunkType chunks
ChunkType (%d ∷ chunks) = Int → ChunkType chunks
ChunkType (%f ∷ chunks) = Float → ChunkType chunks

PrintfType : String → Set
PrintfType format = ChunkType (parseFormat format)

printfHelper : (format : List Chunk) → String → ChunkType format
printfHelper [] accum = accum
printfHelper (lit x ∷ fmt) accum = printfHelper fmt (accum <> x)
printfHelper (%s ∷ fmt) accum str = printfHelper fmt (accum <> show str)
printfHelper (%u ∷ fmt) accum nat = printfHelper fmt (accum <> show nat)
printfHelper (%d ∷ fmt) accum int = printfHelper fmt (accum <> show int)
printfHelper (%f ∷ fmt) accum float = printfHelper fmt (accum <> show float)

printf : (format : String) → PrintfType format
printf format = printfHelper (parseFormat format) ""

example1 : String
example1 = printf "Who is a naughty boy? %s %s is a naughty boy, who is %u years old." "Erik" "Brink" 35

helloName : String → String
helloName = printf "Hello, %s!"

{-

format for above: %s ∷ lit " " ∷ %s ∷ lit " is a naughty boy, who is " ∷ %u ∷ lit " years old." ∷ []
PrintfType should then be: String → String → Nat → String

printf "%d is a Int, %u is a Nat" (negsuc 5) 5

class Show a where
  show :: a -> String

instances = HashMap Type ShowInstance

show x

getShow <$> lookup (typeOf x) instances

-}
