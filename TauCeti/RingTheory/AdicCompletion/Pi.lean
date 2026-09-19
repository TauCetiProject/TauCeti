/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-!
# Adic completeness of finite products

For an ideal `I` of a commutative ring `R` and a finite family of `R`-modules `M i`, the product
`∀ i, M i` is `I`-adically Hausdorff, precomplete, or complete as soon as every factor is. The
proofs go through Mathlib's identification `AdicCompletion.piEquivOfFintype` of the completion of
a finite product with the product of the completions.

## Main results

* `IsHausdorff.pi`, `IsPrecomplete.pi`, `IsAdicComplete.pi`: the three properties pass to finite
  products.
-/

public section

open AdicCompletion

variable {R : Type*} [CommRing R] (I : Ideal R) {ι : Type*} (M : ι → Type*)
  [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- The canonical map from a finite product to its adic completion, followed by the
identification of that completion with the product of the completions, is the product of the
canonical maps of the factors. -/
private theorem pi_of (x : ∀ i, M i) (j : ι) :
    AdicCompletion.pi I M (of I (∀ i, M i) x) j = of I (M j) (x j) := by
  simp [AdicCompletion.pi, map_of]

/-- A finite product of `I`-adically Hausdorff modules is `I`-adically Hausdorff. -/
instance IsHausdorff.pi [Finite ι] [∀ i, IsHausdorff I (M i)] : IsHausdorff I (∀ i, M i) := by
  classical
  have := Fintype.ofFinite ι
  refine of_injective_iff.mp fun x y hxy ↦ _root_.funext fun j ↦ (of_injective I (M j)) ?_
  rw [← pi_of, ← pi_of, hxy]

/-- A finite product of `I`-adically precomplete modules is `I`-adically precomplete. -/
instance IsPrecomplete.pi [Finite ι] [∀ i, IsPrecomplete I (M i)] : IsPrecomplete I (∀ i, M i) := by
  classical
  have := Fintype.ofFinite ι
  refine of_surjective_iff.mp fun y ↦ ?_
  choose x hx using fun j ↦ of_surjective I (M j) (AdicCompletion.pi I M y j)
  refine ⟨x, (piEquivOfFintype I M).injective (_root_.funext fun j ↦ ?_)⟩
  rw [piEquivOfFintype_apply, piEquivOfFintype_apply, pi_of, hx]

/-- A finite product of `I`-adically complete modules is `I`-adically complete. -/
instance IsAdicComplete.pi [Finite ι] [∀ i, IsAdicComplete I (M i)] :
    IsAdicComplete I (∀ i, M i) where
