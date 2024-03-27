module untyped.value where

open import Data.List

open import untyped.inst

data MachineValue : Set where
  ⟨⟩ : MachineValue
  _,_ : MachineValue → MachineValue → MachineValue
  cur : List Inst → MachineValue → MachineValue
