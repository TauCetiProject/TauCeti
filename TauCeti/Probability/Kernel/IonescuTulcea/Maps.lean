/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.IonescuTulcea.Maps

/-!
# Splitting off the last coordinate of a prefix

A prefix through time `n + 1` of a dependent sequence is its prefix through time `n` together
with its last coordinate. `MeasurableEquiv.IicProdSucc` is this splitting, built from Mathlib's
`MeasurableEquiv.IicProdIoc`.
-/

public section

open Finset Preorder

namespace MeasurableEquiv

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]

/-- A prefix through time `n + 1` is a prefix through time `n` together with its last
coordinate. -/
def IicProdSucc (n : ℕ) : ((i : Iic n) → X i) × X (n + 1) ≃ᵐ ((i : Iic (n + 1)) → X i) :=
  (prodCongr (refl _) (piSingleton n)).trans (IicProdIoc n.le_succ)

/-- The inverse of `MeasurableEquiv.IicProdSucc` splits off the last coordinate. -/
theorem coe_IicProdSucc_symm (n : ℕ) :
    ⇑(IicProdSucc (X := X) n).symm =
      fun x ↦ (frestrictLe₂ n.le_succ x, x ⟨n + 1, mem_Iic.2 le_rfl⟩) := (rfl)

/-- Splitting the prefix through time `n + 1` of a trajectory gives its prefix through time `n`
and its coordinate at time `n + 1`. -/
theorem IicProdSucc_symm_comp_frestrictLe (n : ℕ) :
    (IicProdSucc (X := X) n).symm ∘ frestrictLe (n + 1) =
      fun x ↦ (frestrictLe n x, x (n + 1)) := (rfl)

end MeasurableEquiv
