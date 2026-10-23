/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.RingOpNorm.Banach

/-!
# Ranges of idempotent operators close to a factored compression

Let `E` be a complete normed module over Tate scalars and `e` an idempotent endomorphism of `E`.
Suppose the compression `e ∘ c ∘ e` of `e` by an operator `c` lies within operator-norm distance
less than one of `e`, and that `c = b ∘ a` factors through an `R`-module `P` along linear maps
`a : E → P` and `b : P → E`. Then the range of `e` is a direct summand of `P`
(`ContinuousLinearMap.exists_comp_eq_id_of_isIdempotentElem`): there are linear maps
`f : P → range e` and `g : range e → P` with `f ∘ g = id`. The inverse of `1 - (e - e ∘ c ∘ e)`
is the Neumann series (`ContinuousLinearMap.oneSub`), so no basis of the range and no division by
nonunits of the scalars is involved, and the statement holds over coefficient rings with
nilpotents.

Applied with `P` finite free and `c` the projection of a model space `C₀(I, R)` onto finitely many
coordinates, it shows that row-compact idempotents have finitely generated projective range.

## Main results

* `ContinuousLinearMap.exists_comp_eq_id_of_isIdempotentElem`: if `‖e - e ∘ c ∘ e‖ < 1` and `c`
  factors through `P`, the range of the idempotent `e` is a direct summand of `P`.
-/

public section

namespace ContinuousLinearMap

open scoped TauCeti.RingOpNorm

variable {R E P : Type*} [SeminormedRing R] [TauCeti.NormedRing.IsTate R]
  [NormedAddCommGroup E] [Module R E] [IsBoundedSMul R E] [CompleteSpace E]
  [AddCommMonoid P] [Module R P]

/-- Over Tate scalars, let `e` be an idempotent endomorphism of a complete normed module whose
compression `e ∘ c ∘ e` satisfies `‖e - e ∘ c ∘ e‖ < 1`, where `c = b ∘ a` factors through an
`R`-module `P`. Then the range of `e` is a direct summand of `P`: there are linear maps
`f : P → range e` and `g : range e → P` with `f ∘ g = id`. -/
theorem exists_comp_eq_id_of_isIdempotentElem {e c : E →L[R] E} (he : IsIdempotentElem e)
    (a : E →ₗ[R] P) (b : P →ₗ[R] E) (hc : (c : E →ₗ[R] E) = b ∘ₗ a) (h : ‖e - e * c * e‖ < 1) :
    ∃ (f : P →ₗ[R] LinearMap.range (e : E →ₗ[R] E)) (g : LinearMap.range (e : E →ₗ[R] E) →ₗ[R] P),
      f ∘ₗ g = .id := by
  set t := e - e * c * e
  set w : E →L[R] E := ((oneSub t h).symm : E →L[R] E)
  -- `e * t = t` since `e` is idempotent, so `e * (1 - t) = e * c * e`, and `1 - t` has the
  -- inverse `w`.
  have hew : e * c * e * w = e := by
    have het : e * t = t := by simp only [t, mul_sub, ← mul_assoc, he.eq]
    have hw : (1 - t) * w = 1 := by
      rw [← coe_oneSub t h]
      ext x
      exact (oneSub t h).apply_symm_apply x
    calc e * c * e * w = e * (1 - t) * w := by rw [mul_sub, mul_one, het, sub_sub_cancel]
      _ = e := by rw [mul_assoc, hw, mul_one]
  refine ⟨LinearMap.codRestrict _ ((e : E →ₗ[R] E) ∘ₗ b) fun y ↦
    LinearMap.mem_range_self (e : E →ₗ[R] E) (b y),
    a ∘ₗ ((e * w : E →L[R] E) : E →ₗ[R] E) ∘ₗ (LinearMap.range (e : E →ₗ[R] E)).subtype, ?_⟩
  ext ⟨_, x, rfl⟩
  have hee : e (e x) = e x := congr($he.eq x)
  have hx := congr($hew (e x))
  simp only [mul_apply_eq_comp, hee] at hx
  simpa [← LinearMap.comp_apply b a, ← hc] using hx

end ContinuousLinearMap
