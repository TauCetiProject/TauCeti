/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszProjection.Intertwining
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
  {u E F : C₀(I, R) →L[R] C₀(I, R)} {a b : R} {h k : ℕ}

namespace IsRieszProjection

/-- Riesz projectors at parameters separated by a unit annihilate each other. -/
theorem mul_eq_zero (hE : IsRieszProjection u a h E) (hF : IsRieszProjection u b k F)
    (hab : IsUnit (a - b)) : E * F = 0 := by
  have hEF := hE.commute_of_commute hF.commute.symm
  ext x : 1
  apply (Submodule.disjoint_def.mp (hE.disjoint_range hF hab))
  · exact ⟨F x, rfl⟩
  · exact ⟨E x, congr($(hEF.eq) x)⟩

end IsRieszProjection

variable {ι : Type*} {a : ι → R} {h : ι → ℕ}
  {E : ι → C₀(I, R) →L[R] C₀(I, R)}

/-- Riesz projectors at pairwise unit-separated parameters form a family of orthogonal
idempotents, in the native ring-theoretic sense. -/
theorem orthogonalIdempotents_of_isRieszProjection
    (hE : ∀ i, IsRieszProjection u (a i) (h i) (E i))
    (ha : Pairwise fun i j ↦ IsUnit (a i - a j)) : OrthogonalIdempotents E :=
  ⟨fun i ↦ (hE i).isIdempotentElem, fun i j hij ↦ (hE i).mul_eq_zero (hE j) (ha hij)⟩

section Complete

variable [DiscreteTopology I] [DecidableEq I] [NormOneClass R]
  [IsUltrametricDist R] [CompleteSpace R]

omit [NormOneClass R] [CompleteSpace R] in
/-- A finite sum of Riesz projectors of a row-compact operator is row compact.
No separation hypothesis is needed for this assertion. -/
theorem IsRowCompact.isRowCompact_sum_rieszProjection (hu : u.IsRowCompact)
    (hE : ∀ i, IsRieszProjection u (a i) (h i) (E i)) (s : Finset ι) :
    (∑ i ∈ s, E i).IsRowCompact := by
  exact Finset.sum_induction E (fun w : C₀(I, R) →L[R] C₀(I, R) ↦ w.IsRowCompact)
    (fun _ _ ↦ IsRowCompact.add) isRowCompact_zero fun i _ ↦ (hE i).isRowCompact hu

omit [NormOneClass R] in
/-- The spectral block cut out by finitely many separated Riesz projectors is finitely
generated. No Noetherian hypothesis is required. -/
theorem IsRowCompact.finite_range_sum_rieszProjection (hu : u.IsRowCompact)
    (hE : ∀ i, IsRieszProjection u (a i) (h i) (E i))
    (ha : Pairwise fun i j ↦ IsUnit (a i - a j)) (s : Finset ι) :
    Module.Finite R (∑ i ∈ s, E i).range :=
  (hu.isRowCompact_sum_rieszProjection hE s).finite_range_of_isIdempotentElem
    (orthogonalIdempotents_of_isRieszProjection hE ha).isIdempotentElem_sum

omit [NormOneClass R] in
/-- The spectral block cut out by finitely many separated Riesz projectors is projective;
it need not be free over a coefficient ring. -/
theorem IsRowCompact.projective_range_sum_rieszProjection (hu : u.IsRowCompact)
    (hE : ∀ i, IsRieszProjection u (a i) (h i) (E i))
    (ha : Pairwise fun i j ↦ IsUnit (a i - a j)) (s : Finset ι) :
    Module.Projective R (∑ i ∈ s, E i).range :=
  (hu.isRowCompact_sum_rieszProjection hE s).projective_range_of_isIdempotentElem
    (orthogonalIdempotents_of_isRieszProjection hE ha).isIdempotentElem_sum

/-- The common complementary Fredholm factor is a unit at every selected parameter.
Thus removing several spectral summands does not leave any of their zeros behind. -/
theorem IsRowCompact.isUnit_evalAt_charPowerSeries_complement_sum_rieszProjection
    (hu : u.IsRowCompact) (hE : ∀ i, IsRieszProjection u (a i) (h i) (E i))
    (ha : Pairwise fun i j ↦ IsUnit (a i - a j)) (s : Finset ι) {i : ι} (hi : i ∈ s) :
    IsUnit ((u * (1 - ∑ j ∈ s, E j)).matrixCoeff.charPowerSeries.evalAt (a i)) := by
  let S := ∑ j ∈ s, E j
  have he := orthogonalIdempotents_of_isRieszProjection hE ha
  have hiS : E i * S = E i := he.mul_sum_of_mem hi
  have hCS : Commute (1 - a i • u) S :=
    Commute.sum_right s E _ fun j _ ↦
      Commute.one_sub_smul_left (A := C₀(I, R) →L[R] C₀(I, R)) (hE j).commute (a i)
  have hremove : (1 - E i) * (1 - S) = 1 - S := by
    rw [sub_mul (α := C₀(I, R) →L[R] C₀(I, R)), one_mul,
      mul_sub (α := C₀(I, R) →L[R] C₀(I, R)), mul_one, hiS, sub_self]
    exact sub_zero (1 - S)
  -- Restrict the i-th complementary inverse to the smaller common complement.
  have hw : (1 - a i • u) * ((hE i).inverse * (1 - S)) = 1 - S := by
    rw [← mul_assoc, (hE i).one_sub_smul_mul_inverse, hremove]
  have hCS' : Commute (1 - a i • u) (1 - S) :=
    Commute.sub_right (R := C₀(I, R) →L[R] C₀(I, R))
      (Commute.one_right (1 - a i • u)) hCS
  have hw' : (hE i).inverse * (1 - S) * (1 - a i • u) = 1 - S := by
    rw [mul_assoc, ← hCS'.eq, ← mul_assoc, (hE i).inverse_mul_one_sub_smul, hremove]
  have hunit := he.isIdempotentElem_sum.isUnit_add_mul_one_sub
    (A := C₀(I, R) →L[R] C₀(I, R)) hw hw'
  apply (hu.comp_clm (1 - S)).isUnit_evalAt_charPowerSeries_of_isUnit_one_sub_smul
  convert hunit using 1
  ext x : 1
  simp only [sub_apply, one_apply_eq_self, smul_apply, mul_apply_eq_comp, add_apply,
    comp_apply, map_sub]
  module

/-- The Fredholm factor on a finite union of separated good-zero summands is the product
of the corresponding normalised linear factors, with their good-zero orders. -/
theorem IsRowCompact.charPowerSeries_matrixCoeff_mul_sum_rieszProjection
    (hu : u.IsRowCompact) (hE : ∀ i, IsRieszProjection u (a i) (h i) (E i))
    (ha : Pairwise fun i j ↦ IsUnit (a i - a j))
    (hH : ∀ i, u.matrixCoeff.charPowerSeries.IsGoodZero (a i) (h i)) (s : Finset ι) :
    (u * ∑ i ∈ s, E i).matrixCoeff.charPowerSeries =
      ∏ i ∈ s, (1 - PowerSeries.C (Ring.inverse (a i)) * PowerSeries.X) ^ h i := by
  rw [Finset.mul_sum (R := C₀(I, R) →L[R] C₀(I, R))]
  rw [charPowerSeries_matrixCoeff_sum_of_mul_eq_zero (u := fun i ↦ u * E i)
    (fun i _ ↦ by simpa only [mul_def] using hu.comp_clm (E i))]
  · exact Finset.prod_congr rfl fun i _ ↦
      (hE i).charPowerSeries_matrixCoeff_mul_eq_pow hu (hH i)
  · intro i _ j _ hij
    rw [mul_assoc, ← mul_assoc (E i), ← (hE i).commute.eq, mul_assoc u (E i),
      (hE i).mul_eq_zero (hE j) (ha hij), mul_zero, mul_zero]

/-- Simultaneously split off finitely many separated Fredholm zeros. The remaining factor
is the determinant of the operator on the common complementary summand. -/
theorem IsRowCompact.charPowerSeries_matrixCoeff_eq_prod_mul_of_isRieszProjection
    (hu : u.IsRowCompact) (hE : ∀ i, IsRieszProjection u (a i) (h i) (E i))
    (ha : Pairwise fun i j ↦ IsUnit (a i - a j))
    (hH : ∀ i, u.matrixCoeff.charPowerSeries.IsGoodZero (a i) (h i)) (s : Finset ι) :
    u.matrixCoeff.charPowerSeries =
      (∏ i ∈ s, (1 - PowerSeries.C (Ring.inverse (a i)) * PowerSeries.X) ^ h i) *
        (u * (1 - ∑ i ∈ s, E i)).matrixCoeff.charPowerSeries := by
  have he := orthogonalIdempotents_of_isRieszProjection hE ha
  rw [hu.charPowerSeries_matrixCoeff_eq_mul_of_commute he.isIdempotentElem_sum
    (Commute.sum_right s E u fun i _ ↦ (hE i).commute),
    hu.charPowerSeries_matrixCoeff_mul_sum_rieszProjection hE ha hH]

end Complete

end ContinuousLinearMap
