/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.CategoryTheory.Aut.Conjugation
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

/-!
# Checks for conjugation of automorphisms

In the category of types, the automorphisms of `Fin 3` form the noncommutative group `S₃`.
Conjugating the transposition `(1 2)` by `(0 1)` gives `(0 2)`, while conjugating it by the
identity gives `(1 2)`. So conjugation along the identity and along `(0 1)` differ, and the
commutativity hypothesis of `Aut.autMulEquivOfIso_eq_of_commute` cannot be dropped.
-/

open CategoryTheory

-- Conjugating `(1 2)` by `(0 1)` gives `(0 2)`.
example :
    (Aut.autMulEquivOfIso (Equiv.swap (0 : Fin 3) 1).toIso
      (.of (Equiv.swap (1 : Fin 3) 2).toIso)).asIso = (Equiv.swap (0 : Fin 3) 2).toIso := by
  ext k
  fin_cases k <;> rfl

-- Conjugation along the identity and along `(0 1)` differ on `Aut (Fin 3)`.
example :
    Aut.autMulEquivOfIso (Iso.refl (Fin 3)) ≠
      Aut.autMulEquivOfIso (Equiv.swap (0 : Fin 3) 1).toIso := by
  intro h
  have h' := congrArg (fun b : Aut (Fin 3) ↦ b.asIso.hom 1)
    (DFunLike.congr_fun h (.of (Equiv.swap (1 : Fin 3) 2).toIso))
  revert h'
  decide
