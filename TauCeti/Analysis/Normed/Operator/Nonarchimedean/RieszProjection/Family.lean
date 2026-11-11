/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszProjection.Multiplicity
import TauCeti.Algebra.Ring.Commute

/-!
# Simultaneous Riesz splittings at finitely many zeros

Riesz projectors at scalars whose differences are units are orthogonal. Consequently a
finite family of such zeros cuts out a single finite projective spectral summand. Its
Fredholm factor is the product of the individual factors, and the Fredholm series splits
as this product times the series on the common complement. Over a field the separation
condition is just distinctness; over a coefficient ring it is stronger.

The orthogonality assertion uses only the nilpotence bounds of the projectors, not a
multiplicity hypothesis on the Fredholm series. Good-zero orders are needed only to
identify the factors. Empty families and projectors of order zero are included.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §7.
* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math.
  **127** (1997), 417–479, Appendix A4.
-/

public section

open scoped ZeroAtInfty TauCeti.RingOpNorm

namespace ContinuousLinearMap

variable {I R : Type*} [TopologicalSpace I]
  [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  {u : C₀(I, R) →L[R] C₀(I, R)}
  {ι : Type*} {a : ι → R} {h : ι → ℕ} {E : ι → C₀(I, R) →L[R] C₀(I, R)}

section Complete

variable [DiscreteTopology I] [DecidableEq I]
  [IsUltrametricDist R] [CompleteSpace R]

/-- The spectral block cut out by finitely many separated Riesz projectors is finitely
generated. No Noetherian hypothesis is required. -/
theorem IsRowCompact.finite_range_sum_of_isRieszProjection (hu : u.IsRowCompact)
    (s : Finset ι) (hE : ∀ i ∈ s, IsRieszProjection u (a i) (h i) (E i))
    (ha : (s : Set ι).Pairwise fun i j ↦ IsUnit (a i - a j)) :
    Module.Finite R (∑ i ∈ s, E i).range :=
  (IsRowCompact.sum fun i hi ↦ (hE i hi).isRowCompact hu).finite_range_of_isIdempotentElem
    (isIdempotentElem_sum_of_isRieszProjection s hE ha)

/-- The spectral block cut out by finitely many separated Riesz projectors is projective;
it need not be free over a coefficient ring. -/
theorem IsRowCompact.projective_range_sum_of_isRieszProjection (hu : u.IsRowCompact)
    (s : Finset ι) (hE : ∀ i ∈ s, IsRieszProjection u (a i) (h i) (E i))
    (ha : (s : Set ι).Pairwise fun i j ↦ IsUnit (a i - a j)) :
    Module.Projective R (∑ i ∈ s, E i).range :=
  (IsRowCompact.sum fun i hi ↦ (hE i hi).isRowCompact hu).projective_range_of_isIdempotentElem
    (isIdempotentElem_sum_of_isRieszProjection s hE ha)

/-- The common complementary Fredholm factor is a unit at every selected parameter.
Thus removing several spectral summands does not leave any of their zeros behind. -/
theorem IsRowCompact.isUnit_evalAt_charPowerSeries_complement_sum_of_isRieszProjection
    (hu : u.IsRowCompact) (s : Finset ι)
    (hE : ∀ i ∈ s, IsRieszProjection u (a i) (h i) (E i))
    (ha : (s : Set ι).Pairwise fun i j ↦ IsUnit (a i - a j)) {i : ι} (hi : i ∈ s) :
    IsUnit ((u * (1 - ∑ j ∈ s, E j)).matrixCoeff.charPowerSeries.evalAt (a i)) := by
  let S := ∑ j ∈ s, E j
  have he := isIdempotentElem_sum_of_isRieszProjection s hE ha
  have hiS : E i * S = E i := mul_sum_of_isRieszProjection s hE ha hi
  have hCS : Commute (1 - a i • u) S :=
    Commute.sum_right s E _ fun j hj ↦
      Commute.one_sub_smul_left (A := C₀(I, R) →L[R] C₀(I, R)) (hE j hj).commute (a i)
  have hremove : (1 - E i) * (1 - S) = 1 - S := by
    -- Specialise the ring laws to match continuous-linear-map subtraction.
    simp only [sub_mul (α := C₀(I, R) →L[R] C₀(I, R)), one_mul,
      mul_sub (α := C₀(I, R) →L[R] C₀(I, R)), mul_one, hiS, sub_self,
      sub_zero (1 - S)]
  -- Restrict the i-th complementary inverse to the smaller common complement.
  have hw : (1 - a i • u) * ((hE i hi).inverse * (1 - S)) = 1 - S := by
    rw [← mul_assoc, (hE i hi).one_sub_smul_mul_inverse, hremove]
  have hCS' : Commute (1 - a i • u) (1 - S) :=
    Commute.sub_right (R := C₀(I, R) →L[R] C₀(I, R))
      (Commute.one_right (1 - a i • u)) hCS
  have hw' : (hE i hi).inverse * (1 - S) * (1 - a i • u) = 1 - S := by
    rw [mul_assoc, ← hCS'.eq, ← mul_assoc, (hE i hi).inverse_mul_one_sub_smul, hremove]
  have hunit := he.isUnit_add_mul_one_sub
    (A := C₀(I, R) →L[R] C₀(I, R)) hw hw'
  apply (hu.comp_clm (1 - S)).isUnit_evalAt_charPowerSeries_of_isUnit_one_sub_smul
  convert hunit using 1
  ext x : 1
  simp only [sub_apply, one_apply_eq_self, smul_apply, mul_apply_eq_comp, add_apply,
    comp_apply, map_sub]
  module

/-- The Fredholm factor on a finite union of separated good-zero summands is the product
of the corresponding normalised linear factors, with their good-zero orders. -/
theorem IsRowCompact.charPowerSeries_matrixCoeff_mul_sum_eq_prod_of_isRieszProjection
    (hu : u.IsRowCompact) (s : Finset ι)
    (hE : ∀ i ∈ s, IsRieszProjection u (a i) (h i) (E i))
    (ha : (s : Set ι).Pairwise fun i j ↦ IsUnit (a i - a j))
    (hH : ∀ i ∈ s, u.matrixCoeff.charPowerSeries.IsGoodZero (a i) (h i)) :
    (u * ∑ i ∈ s, E i).matrixCoeff.charPowerSeries =
      ∏ i ∈ s, (1 - PowerSeries.C (Ring.inverse (a i)) * PowerSeries.X) ^ h i := by
  rw [Finset.mul_sum (R := C₀(I, R) →L[R] C₀(I, R))]
  rw [charPowerSeries_matrixCoeff_sum_of_mul_eq_zero (u := fun i ↦ u * E i)
    (fun i _ ↦ by simpa only [mul_def] using hu.comp_clm (E i))]
  · exact Finset.prod_congr rfl fun i hi ↦
      (hE i hi).charPowerSeries_matrixCoeff_mul_eq_pow hu (hH i hi)
  · intro i hi j hj hij
    calc
      (u * E i) * (u * E j) = (u * u) * (E i * E j) :=
        (hE i hi).commute.symm.mul_mul_mul_comm u (E j)
      _ = 0 := by simp only [(hE i hi).mul_eq_zero (hE j hj) (ha hi hj hij), mul_zero]

/-- Simultaneously split off finitely many separated Fredholm zeros. The remaining factor
is the determinant of the operator on the common complementary summand. -/
theorem IsRowCompact.charPowerSeries_matrixCoeff_eq_prod_mul_of_isRieszProjection
    (hu : u.IsRowCompact) (s : Finset ι)
    (hE : ∀ i ∈ s, IsRieszProjection u (a i) (h i) (E i))
    (ha : (s : Set ι).Pairwise fun i j ↦ IsUnit (a i - a j))
    (hH : ∀ i ∈ s, u.matrixCoeff.charPowerSeries.IsGoodZero (a i) (h i)) :
    u.matrixCoeff.charPowerSeries =
      (∏ i ∈ s, (1 - PowerSeries.C (Ring.inverse (a i)) * PowerSeries.X) ^ h i) *
        (u * (1 - ∑ i ∈ s, E i)).matrixCoeff.charPowerSeries := by
  have he := isIdempotentElem_sum_of_isRieszProjection s hE ha
  rw [hu.charPowerSeries_matrixCoeff_eq_mul_of_commute he
    (Commute.sum_right s E u fun i hi ↦ (hE i hi).commute),
    hu.charPowerSeries_matrixCoeff_mul_sum_eq_prod_of_isRieszProjection s hE ha hH]

end Complete

end ContinuousLinearMap
