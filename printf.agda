module printf where

open import Agda.Builtin.String

PrintfType : String → Set
PrintfType format = {!!}

printf : (format : String) → PrintfType format
printf format = {!!}
