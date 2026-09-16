/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
public import TauCeti.AlgebraicGeometry.EllipticCurve.SingularPointCount

/-!
# The Frobenius trace of a reduction, and the local polynomial

Over the fraction field of a discrete valuation ring with finite residue field, the reduction of a
minimal Weierstrass equation is a Weierstrass model over a finite field, so it has a Frobenius
trace `a = q + 1 − #W(k)`, counted with its singular point. This file evaluates that trace at bad
reduction: it is `1` at split multiplicative, `-1` at nonsplit multiplicative, and `0` at additive
reduction. At good reduction it is the classical trace `q + 1 − #E(k)` of the smooth reduction.

These are exactly the coefficients of `T` in Mathlib's `WeierstrassCurve.localPolynomial`, which
is defined by cases on the reduction type. Read through the trace, the case split collapses: the
local polynomial is `1 − a T + q T²` at good reduction and `1 − a T` otherwise.

## Main results

* `WeierstrassCurve.reduction_Δ_eq_zero_iff`,
  `WeierstrassCurve.HasMultiplicativeReduction.reduction_c₄_ne_zero` and
  `WeierstrassCurve.HasAdditiveReduction.reduction_c₄_eq_zero`: the reduction types read on the
  invariants of the reduced model.
* `WeierstrassCurve.HasMultiplicativeReduction.splits_nodePolynomial_reduction_iff`: a
  multiplicative reduction is split exactly when the reduced model's node polynomial splits.
* `WeierstrassCurve.HasSplitMultiplicativeReduction.frobeniusTrace_reduction_eq_one`,
  `WeierstrassCurve.HasMultiplicativeReduction.frobeniusTrace_reduction_eq_neg_one` and
  `WeierstrassCurve.HasAdditiveReduction.frobeniusTrace_reduction_eq_zero`: the trace of the
  reduction is `1`, `-1` and `0` at split multiplicative, nonsplit multiplicative and additive
  reduction.
* `WeierstrassCurve.localPolynomial_eq_of_hasGoodReduction` and
  `WeierstrassCurve.localPolynomial_eq_of_not_hasGoodReduction`: the local polynomial is
  `1 − a T + q T²` at good reduction and `1 − a T` at bad reduction, with `a` the trace of the
  reduction.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.5 and Appendix C.16.
-/

public section

namespace WeierstrassCurve

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum Polynomial

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {W : WeierstrassCurve K}

/-- An element of `R` dies in the residue field exactly when its image in `K` has valuation
below `1`. -/
private theorem residue_eq_zero_iff_valuation_lt_one (r : R) :
    IsLocalRing.residue R r = 0 ↔ valuation K (maximalIdeal R) (algebraMap R K r) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, valuation_lt_one_iff_mem]
  -- `(maximalIdeal R).asIdeal` is by definition `IsLocalRing.maximalIdeal R`
  rfl

/-- **The reduction is singular exactly when it is bad.** -/
theorem reduction_Δ_eq_zero_iff [IsMinimal R W] :
    (W.reduction R).Δ = 0 ↔ ¬ W.HasGoodReduction R := by
  rw [hasGoodReduction_iff_isElliptic_reduction, isElliptic_iff, isUnit_iff_ne_zero, not_not]

/-- **A multiplicative reduction has `c₄ ≠ 0`**: its singular point is a node. -/
theorem HasMultiplicativeReduction.reduction_c₄_ne_zero (h : W.HasMultiplicativeReduction R) :
    (W.reduction R).c₄ ≠ 0 := by
  rw [reduction, map_c₄, Ne, residue_eq_zero_iff_valuation_lt_one R (K := K),
    integralModel_c₄_eq R W, h.multiplicativeReduction]
  exact lt_irrefl 1

/-- **An additive reduction has `c₄ = 0`**: its singular point is a cusp. -/
theorem HasAdditiveReduction.reduction_c₄_eq_zero (h : W.HasAdditiveReduction R) :
    (W.reduction R).c₄ = 0 := by
  rw [reduction, map_c₄, residue_eq_zero_iff_valuation_lt_one R (K := K), integralModel_c₄_eq R W]
  exact h.additiveReduction

/-- **A multiplicative reduction is split exactly when the node polynomial of the reduced model
splits**, which is `HasSplitMultiplicativeReduction` read on the reduced model. -/
theorem HasMultiplicativeReduction.splits_nodePolynomial_reduction_iff
    (h : W.HasMultiplicativeReduction R) :
    (W.reduction R).nodePolynomial.Splits ↔ W.HasSplitMultiplicativeReduction R := by
  rw [hasSplitMultiplicativeReduction_iff, reduction, map_nodePolynomial, nodePolynomial_def,
    IsLocalRing.ResidueField.algebraMap_eq]
  exact ⟨fun hs ↦ ⟨h, hs⟩, fun ⟨_, hs⟩ ↦ hs⟩

variable [Finite (IsLocalRing.ResidueField R)]

/-- **The Frobenius trace of a split multiplicative reduction is `1`.** -/
theorem HasSplitMultiplicativeReduction.frobeniusTrace_reduction_eq_one
    (h : W.HasSplitMultiplicativeReduction R) : (W.reduction R).frobeniusTrace = 1 :=
  frobeniusTrace_eq_one_of_splits _
    ((reduction_Δ_eq_zero_iff R).2 (h.not_hasGoodReduction R))
    (h.reduction_c₄_ne_zero R)
    ((h.splits_nodePolynomial_reduction_iff R).2 h)

/-- **The Frobenius trace of a nonsplit multiplicative reduction is `-1`.** -/
theorem HasMultiplicativeReduction.frobeniusTrace_reduction_eq_neg_one
    (h : W.HasMultiplicativeReduction R) (hs : ¬ W.HasSplitMultiplicativeReduction R) :
    (W.reduction R).frobeniusTrace = -1 :=
  frobeniusTrace_eq_neg_one_of_not_splits _
    ((reduction_Δ_eq_zero_iff R).2 (h.not_hasGoodReduction R))
    (h.reduction_c₄_ne_zero R)
    (mt (h.splits_nodePolynomial_reduction_iff R).1 hs)

/-- **The Frobenius trace of an additive reduction is `0`.** -/
theorem HasAdditiveReduction.frobeniusTrace_reduction_eq_zero (h : W.HasAdditiveReduction R) :
    (W.reduction R).frobeniusTrace = 0 :=
  frobeniusTrace_eq_zero_of_c₄_eq_zero _
    ((reduction_Δ_eq_zero_iff R).2 (h.not_hasGoodReduction R))
    (h.reduction_c₄_eq_zero R)

/-- **At good reduction the local polynomial is `1 − a T + q T²`**, with `a` the Frobenius trace
of the reduction and `q` the size of the residue field. -/
theorem localPolynomial_eq_of_hasGoodReduction (W : WeierstrassCurve K)
    (h : (W.minimal R).HasGoodReduction R) :
    W.localPolynomial R = 1 - C ((W.minimal R).reduction R).frobeniusTrace * X +
      C (Nat.card (IsLocalRing.ResidueField R) : ℤ) * X ^ 2 := by
  have : ((W.minimal R).reduction R).IsElliptic :=
    (hasGoodReduction_iff_isElliptic_reduction R).1 h
  rw [localPolynomial, ite_eq_left h, frobeniusTrace_eq_card_point]

/-- **At bad reduction the local polynomial is `1 − a T`**, with `a` the Frobenius trace of the
reduction. This one formula covers the split multiplicative, nonsplit multiplicative and additive
cases of the definition. -/
theorem localPolynomial_eq_of_not_hasGoodReduction (W : WeierstrassCurve K)
    (h : ¬ (W.minimal R).HasGoodReduction R) :
    W.localPolynomial R = 1 - C ((W.minimal R).reduction R).frobeniusTrace * X := by
  rw [localPolynomial, ite_eq_right h]
  rcases hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction R
    (W := W.minimal R) with hg | hm | ha
  · exact absurd hg h
  · by_cases hs : (W.minimal R).HasSplitMultiplicativeReduction R
    · rw [ite_eq_left hs, hs.frobeniusTrace_reduction_eq_one R, C_1, one_mul]
    · rw [ite_eq_right hs, ite_eq_left hm, hm.frobeniusTrace_reduction_eq_neg_one R hs, C_neg,
        C_1, neg_one_mul, sub_neg_eq_add]
  · rw [ite_eq_right fun hs ↦ ha.not_hasMultiplicativeReduction R hs.toHasMultiplicativeReduction,
      ite_eq_right (ha.not_hasMultiplicativeReduction R), ha.frobeniusTrace_reduction_eq_zero R,
      C_0, zero_mul, sub_zero]

end WeierstrassCurve
