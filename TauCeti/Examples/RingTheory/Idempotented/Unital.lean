/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Idempotented.Unital
import Mathlib.Algebra.Algebra.Unitization

/-!
# Checks for nondegenerate modules over a unital algebra

* For `H = A` unital, `NondegMod A A ≌ ModuleCat A`.
* The unitization `ℤ ⊕ ℤ`, as a module over itself, is not nondegenerate: `1 ∈ H` sends the unit
  `(1, 0)` to `(0, 1)`. So `NondegMod A H` is a proper subcategory of the modules over `A ⊕ H`.
-/

open CategoryTheory TauCeti

-- For `H = A`, nondegenerate modules over `A ⊕ A` are the `A`-modules.
noncomputable example (A : Type) [CommRing A] : NondegMod.{0} A A ≌ ModuleCat.{0} A :=
  nondegModEquivModuleCat A A

-- The regular module of `ℤ ⊕ ℤ` is not nondegenerate.
example : ¬IsNondegenerate ℤ ℤ (Unitization ℤ ℤ) := by
  rw [isNondegenerate_iff_one_smul]
  intro h
  have h1 := congrArg (fun x : Unitization ℤ ℤ ↦ x.fst) (h 1)
  simp at h1
