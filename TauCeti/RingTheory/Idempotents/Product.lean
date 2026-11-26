/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.RingTheory.Idempotents

/-!
# Computation in the product decomposition defined by an idempotent

The inverse of `B ≃ B/(1-e) × B/(e)` on the first factor is multiplication by `e`.

For an idempotent `f` and an element `e` commuting with it, the ideals `(1 - e)` and `(1 - f)`
generate `(1 - e f)` (`IsIdempotentElem.span_one_sub_sup_span_one_sub`); in a commutative ring
this identifies `R ⧸ (1 - e) ⊗ R ⧸ (1 - f)` with `R ⧸ (1 - e f)`.
-/

public section

/-- The first summand of the idempotent quotient decomposition is `e B`. -/
lemma AlgEquiv.prodQuotientOfIsIdempotentElem_symm_mk_zero {R B : Type*}
    [CommRing R] [CommRing B] [Algebra R B] {e : B} (he : IsIdempotentElem e) (c : B) :
    (AlgEquiv.prodQuotientOfIsIdempotentElem R he.one_sub he
      (sub_add_cancel 1 e) he.one_sub_mul_self).symm
        (Ideal.Quotient.mk (Ideal.span {1 - e}) c, 0) = e * c := by
  rw [AlgEquiv.symm_apply_eq, AlgEquiv.prodQuotientOfIsIdempotentElem_apply]
  refine Prod.ext ?_ ?_
  · exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr ⟨c, by ring⟩)
  · exact ((Ideal.Quotient.eq_zero_iff_mem).mpr
      (Ideal.mem_span_singleton.mpr ⟨c, by ring⟩)).symm

/-- For an idempotent `f` of a ring and an element `e` commuting with it, the left ideals
`(1 - e)` and `(1 - f)` generate `(1 - e f)`: `1 - e f = (1 - e) + e (1 - f)`,
`1 - f = (1 - f) (1 - e f)` and `1 - e = (1 - e f) - e (1 - f)`. -/
theorem IsIdempotentElem.span_one_sub_sup_span_one_sub {R : Type*} [Ring R] {e f : R}
    (hf : IsIdempotentElem f) (hef : Commute e f) :
    Ideal.span {1 - e} ⊔ Ideal.span {1 - f} = Ideal.span {1 - e * f} := by
  have hf' : 1 - f ∈ Ideal.span {1 - e * f} :=
    Ideal.mem_span_singleton'.mpr ⟨1 - f, by simp [hef.eq, sub_mul, mul_sub, ← mul_assoc, hf.eq]⟩
  refine le_antisymm (sup_le ?_ ((Ideal.span_singleton_le_iff_mem _).mpr hf'))
    (Ideal.span_singleton_le_iff_mem _ |>.mpr ?_)
  · rw [Ideal.span_singleton_le_iff_mem, show 1 - e = (1 - e * f) - e * (1 - f) by simp [mul_sub]]
    exact sub_mem (Ideal.mem_span_singleton_self _) (Ideal.mul_mem_left _ _ hf')
  · rw [show 1 - e * f = (1 - e) + e * (1 - f) by simp [mul_sub]]
    exact add_mem (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
