/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Ring.Idempotent

/-!
# Ranges of orthogonal idempotent endomorphisms

Two idempotent endomorphisms `P` and `Q` of a module with `P * Q = 0` and `Q * P = 0` split the
range of their sum: the range of `P + Q` is the sum of the ranges of `P` and `Q`, and these ranges
are independent. This is how ranks of spectral projections add over disjoint parts of the
spectrum.

## Main results

* `IsIdempotentElem.disjoint_range_of_mul_eq_zero`: if `P` is idempotent and `P * Q = 0`, the
  ranges of `P` and `Q` meet only in `0`.
* `IsIdempotentElem.range_add_of_mul_eq_zero`: if `P` and `Q` are idempotent with `Q * P = 0` and
  `P * Q = 0`, the range of `P + Q` is the sum of their ranges.
-/

public section

namespace IsIdempotentElem

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {P Q : Module.End R M}

/-- If `P` is idempotent and `P * Q = 0`, the ranges of `P` and `Q` meet only in `0`. -/
theorem disjoint_range_of_mul_eq_zero (hP : IsIdempotentElem P) (hPQ : P * Q = 0) :
    Disjoint (LinearMap.range P) (LinearMap.range Q) := by
  rw [Submodule.disjoint_def]
  rintro _ ⟨v, rfl⟩ ⟨w, hw⟩
  have h₁ : P (Q w) = 0 := congr($hPQ w)
  have h₂ : P (P v) = P v := congr($hP v)
  rw [← h₂, ← hw, h₁]

/-- If `P` and `Q` are idempotent with `Q * P = 0` and `P * Q = 0`, the range of `P + Q` is the
sum of the ranges of `P` and `Q`. -/
theorem range_add_of_mul_eq_zero (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (hQP : Q * P = 0) (hPQ : P * Q = 0) :
    LinearMap.range (P + Q) = LinearMap.range P ⊔ LinearMap.range Q := by
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · rintro _ ⟨v, rfl⟩
    exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
  · rintro _ ⟨v, rfl⟩
    refine ⟨P v, ?_⟩
    have h₁ : P (P v) = P v := congr($hP v)
    have h₂ : Q (P v) = 0 := congr($hQP v)
    simp [h₁, h₂]
  · rintro _ ⟨v, rfl⟩
    refine ⟨Q v, ?_⟩
    have h₁ : Q (Q v) = Q v := congr($hQ v)
    have h₂ : P (Q v) = 0 := congr($hPQ v)
    simp [h₁, h₂]

end IsIdempotentElem
