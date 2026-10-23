/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.CharPowerSeries.GaussContinuity
public import Mathlib.RingTheory.PowerSeries.PiTopology

/-!
# Finite compressions of principal-minor series

The determinants of finite coordinate compressions of a matrix converge to its principal-minor
series when the rows have a common bound tending to zero. Convergence holds coefficientwise
and in every positive-radius Gauss norm. Thus the infinite determinant can be recovered from
finite determinants without choosing an enumeration of the coordinates.

Finite compression means restriction to the same finite set of input and output coordinates.
For an operator with finite output support this is its determinant after removing the zero
complement. No decay of input tails is assumed.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§4–5.
-/

public section

namespace TauCeti

open Filter Finset Matrix Polynomial Topology
open scoped PowerSeries.WithPiTopology

variable {ι R : Type*} [DecidableEq ι]

/-- The `n`-th coefficient of `det (1 - X A_S)` for a finite compression `A_S` is `(-1) ^ n`
times the sum of the size-`n` principal minors of `A` supported in `S`. -/
theorem coeff_charpolyRev_finiteCompression [CommRing R] {A : Matrix ι ι R}
    (S : Finset ι) (n : ℕ) :
    (A.submatrix (Subtype.val : S → ι) Subtype.val).charpolyRev.coeff n =
      (-1) ^ n * ∑ s ∈ S.powersetCard n, A.principalMinor s := by
  rw [Matrix.coeff_charpolyRev]
  congr 1
  refine sum_bij (fun s _ ↦ s.map (Function.Embedding.subtype (· ∈ S))) ?_ ?_ ?_ ?_
  · intro s hs
    exact mem_powersetCard.mpr ⟨fun i hi ↦ property_of_mem_map_subtype s hi,
      by simpa using (mem_powersetCard.mp hs).2⟩
  · intro s hs t ht h
    exact Finset.map_injective _ h
  · intro s hs
    have hsub := (mem_powersetCard.mp hs).1
    refine ⟨s.subtype (· ∈ S), ?_, subtype_map_of_mem hsub⟩
    exact mem_powersetCard.mpr ⟨subset_univ _, by
      rw [← card_map (Function.Embedding.subtype (· ∈ S)), subtype_map_of_mem hsub]
      exact (mem_powersetCard.mp hs).2⟩
  · intro s hs
    let e : s ≃ s.map (Function.Embedding.subtype (· ∈ S)) :=
      Finset.equivMap (Function.Embedding.subtype (· ∈ S)) s
    rw [principalMinor_def, ← det_submatrix_equiv_self e, submatrix_submatrix,
      submatrix_submatrix]
    -- `equivMap` sends each index to its image under the subtype embedding, so both
    -- reindexing functions reduce to the original index after the subtype values are taken.
    congr 1

/-- If the size-`n` principal minors are summable, the corresponding coefficients of finite
compressions converge to the coefficient of the principal-minor series. -/
theorem tendsto_coeff_charpolyRev_finiteCompression [CommRing R] [TopologicalSpace R]
    [ContinuousNeg R] {A : Matrix ι ι R} (n : ℕ)
    (hA : Summable fun s : {s : Finset ι // s.card = n} ↦ A.principalMinor s) :
    Tendsto (fun S : Finset ι ↦
      (A.submatrix (Subtype.val : S → ι) Subtype.val).charpolyRev.coeff n)
      atTop (𝓝 (A.charCoeff n)) := by
  have hcofinal : Tendsto
      (fun S : Finset ι ↦ (S.powersetCard n).subtype (fun s ↦ s.card = n)) atTop atTop := by
    convert (tendsto_finset_preimage_atTop_atTop
      (Subtype.val_injective (p := fun s : Finset ι ↦ s.card = n))).comp
        tendsto_finset_powerset_atTop_atTop using 1
    ext S s
    simp [mem_powersetCard, s.2]
  have h : Tendsto (fun S : Finset ι ↦
      ∑ s ∈ (S.powersetCard n).subtype (fun s ↦ s.card = n), A.principalMinor s.1)
      atTop (𝓝 (∑' s : {s : Finset ι // s.card = n}, A.principalMinor s)) :=
    hA.hasSum.comp hcofinal
  simp only [sum_subtype_of_mem _ (fun s hs ↦ (mem_powersetCard.mp hs).2)] at h
  rcases neg_one_pow_eq_or R n with hn | hn
  · simpa only [coeff_charpolyRev_finiteCompression, Matrix.charCoeff_def, hn, one_mul] using h
  · simpa only [coeff_charpolyRev_finiteCompression, Matrix.charCoeff_def, hn, neg_one_mul]
      using h.neg

/-- Finite compressions converge coefficientwise to the principal-minor series whenever
all the defining families of minors are summable. -/
theorem tendsto_charpolyRev_finiteCompression [CommRing R] [TopologicalSpace R]
    [ContinuousNeg R] {A : Matrix ι ι R}
    (hA : ∀ n, Summable fun s : {s : Finset ι // s.card = n} ↦ A.principalMinor s) :
    Tendsto (fun S : Finset ι ↦
      ((A.submatrix (Subtype.val : S → ι) Subtype.val).charpolyRev : PowerSeries R))
      atTop (𝓝 A.charPowerSeries) := by
  rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  simpa only [Polynomial.coeff_coe, Matrix.coeff_charPowerSeries] using
    tendsto_coeff_charpolyRev_finiteCompression n (hA n)

/-- The principal-minor series of an output truncation is the polynomial determinant on
the retained coordinates. No convergence or row-decay hypothesis on the original matrix is
needed for this finite-support identity. -/
theorem charPowerSeries_outputTruncation [CommRing R] [TopologicalSpace R]
    {A : Matrix ι ι R} (S : Finset ι) :
    Matrix.charPowerSeries (Matrix.of fun i j ↦ if i ∈ S then A i j else 0) =
      ((A.submatrix (Subtype.val : S → ι) Subtype.val).charpolyRev : PowerSeries R) := by
  let C : Matrix ι ι R := Matrix.of fun i j ↦ if i ∈ S then A i j else 0
  have hminor (s : Finset ι) : C.principalMinor s =
      if s ⊆ S then A.principalMinor s else 0 := by
    rw [principalMinor_def]
    split_ifs with hs
    · rw [principalMinor_def]
      congr 1
      ext i j
      simp [submatrix_apply, C, hs i.2]
    · obtain ⟨i, hi, hiS⟩ := Finset.not_subset.mp hs
      exact det_eq_zero_of_row_eq_zero ⟨i, hi⟩ fun j ↦ by simp [C, submatrix_apply, hiS]
  ext n
  rw [Polynomial.coeff_coe, coeff_charpolyRev_finiteCompression,
    Matrix.coeff_charPowerSeries, Matrix.charCoeff_def]
  congr 1
  rw [tsum_eq_sum (s := (S.powersetCard n).subtype (fun s ↦ s.card = n))]
  · rw [sum_subtype_of_mem _ (fun s hs ↦ (mem_powersetCard.mp hs).2)]
    exact sum_congr rfl fun s hs ↦ by rw [hminor, ite_eq_left (mem_powersetCard.mp hs).1]
  · intro s hs
    rw [hminor, ite_eq_right]
    simpa only [mem_subtype, mem_powersetCard, s.2, and_true] using hs

section Ultrametric

variable [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R]
  {A : Matrix ι ι R} {r : ι → ℝ}

/-- Finite coordinate determinants converge in every positive-radius Gauss norm to the
principal-minor series of a matrix whose row bounds tend to zero. The finite sets are ordered
by inclusion, so this limit does not depend on an enumeration of the index type. -/
theorem tendsto_gaussNorm_charpolyRev_finiteCompression_sub_charPowerSeries [CompleteSpace R]
    (hA : ∀ i j, ‖A i j‖ ≤ r i) (hr : Tendsto r cofinite (𝓝 0))
    {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun S : Finset ι ↦
      (((A.submatrix (Subtype.val : S → ι) Subtype.val).charpolyRev : PowerSeries R) -
        A.charPowerSeries).gaussNorm norm ρ) atTop (𝓝 0) := by
  let B : Finset ι → Matrix ι ι R := fun S ↦ Matrix.of fun i j ↦ if i ∈ S then A i j else 0
  have hB (S : Finset ι) (i j : ι) : ‖B S i j‖ ≤ r i := by
    dsimp [B]
    split_ifs
    · exact hA i j
    · simpa only [norm_zero] using (norm_nonneg (A i i)).trans (hA i i)
  have hcoeff (n : ℕ) :
      Tendsto (fun S ↦ (B S).charCoeff n) atTop (𝓝 (A.charCoeff n)) := by
    simpa only [← Matrix.coeff_charPowerSeries, B, charPowerSeries_outputTruncation,
      Polynomial.coeff_coe] using
      tendsto_coeff_charpolyRev_finiteCompression n (Matrix.summable_principalMinor hA hr n)
  simpa only [B, charPowerSeries_outputTruncation] using
    tendsto_gaussNorm_charPowerSeries_sub_charPowerSeries_of_common_majorant hB hA hr hcoeff hρ

end Ultrametric

end TauCeti
