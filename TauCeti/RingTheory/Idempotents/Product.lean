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
