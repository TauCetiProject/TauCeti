/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.CharPowerSeries
public import Mathlib.RingTheory.PowerSeries.GaussNorm

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

variable {ι R : Type*} [DecidableEq ι]

/-- The coefficients of a finite compression are the sums of the principal minors supported
on its coordinate set. -/
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

/-- The uniform coefficient tail bound for a matrix also bounds every finite compression,
with the same constants and exceptional coordinate set. -/
theorem norm_coeff_charpolyRev_finiteCompression_mul_pow_le
    (hA : ∀ i j, ‖A i j‖ ≤ r i) {ρ q B : ℝ} (hρ : 0 < ρ)
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (hB : 1 ≤ B) (T : Finset ι)
    (hT : ∀ i ∉ T, ρ * r i ≤ q) (hrB : ∀ i, ρ * r i ≤ B)
    (S : Finset ι) (n : ℕ) :
    ‖(A.submatrix (Subtype.val : S → ι) Subtype.val).charpolyRev.coeff n‖ * ρ ^ n ≤
      B ^ T.card * q ^ (n - T.card) := by
  have hcard : (T.subtype (· ∈ S)).card ≤ T.card := by
    rw [card_subtype]
    exact card_filter_le _ _
  have h := Matrix.norm_charCoeff_mul_pow_le
    (A := A.submatrix (Subtype.val : S → ι) Subtype.val) (fun i j ↦ hA i j)
    hρ hq₀ hq₁ hB (T.subtype (· ∈ S))
    (fun i hi ↦ hT i (by simpa using hi)) (fun i ↦ hrB i) n
  rw [Matrix.charCoeff_eq_coeff_charpolyRev] at h
  refine h.trans (mul_le_mul ?_ ?_ (pow_nonneg hq₀ _) (pow_nonneg (by linarith) _))
  · exact pow_le_pow_right₀ hB hcard
  · exact pow_le_pow_of_le_one hq₀ hq₁ (by omega)

/-- Finite coordinate determinants converge in every positive-radius Gauss norm to the
principal-minor series of a matrix whose row bounds tend to zero. The finite sets are ordered
by inclusion, so this limit does not depend on an enumeration of the index type. -/
theorem tendsto_gaussNorm_charpolyRev_finiteCompression [CompleteSpace R]
    (hA : ∀ i j, ‖A i j‖ ≤ r i) (hr : Tendsto r cofinite (𝓝 0))
    {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun S : Finset ι ↦
      (((A.submatrix (Subtype.val : S → ι) Subtype.val).charpolyRev : PowerSeries R) -
        A.charPowerSeries).gaussNorm norm ρ) atTop (𝓝 0) := by
  -- Choose one geometric tail controlling every compression and the limit series.
  obtain ⟨M, hM⟩ := hr.bddAbove_range_of_cofinite
  have hfinite : {i | ¬ρ * r i ≤ 1 / 2}.Finite := by
    refine eventually_cofinite.mp ?_
    exact ((hr.const_mul ρ).eventually
      (gt_mem_nhds (by norm_num : ρ * 0 < 1 / 2))).mono fun _ hi ↦ hi.le
  let T := hfinite.toFinset
  let B := max 1 (ρ * M)
  have hB : 1 ≤ B := le_max_left _ _
  have hT (i : ι) (hi : i ∉ T) : ρ * r i ≤ 1 / 2 := by
    simpa [T] using hi
  have hrB (i : ι) : ρ * r i ≤ B :=
    (mul_le_mul_of_nonneg_left (hM ⟨i, rfl⟩) hρ.le).trans (le_max_right _ _)
  let b := fun n : ℕ ↦ B ^ T.card * (1 / 2 : ℝ) ^ (n - T.card)
  have hb (n : ℕ) : ‖A.charCoeff n‖ * ρ ^ n ≤ b n :=
    Matrix.norm_charCoeff_mul_pow_le hA hρ (by norm_num) (by norm_num) hB T hT hrB n
  have hbS (S : Finset ι) (n : ℕ) :
      ‖(A.submatrix (Subtype.val : S → ι) Subtype.val).charpolyRev.coeff n‖ * ρ ^ n ≤ b n :=
    norm_coeff_charpolyRev_finiteCompression_mul_pow_le hA hρ
      (by norm_num) (by norm_num) hB T hT hrB S n
  have hlim : Tendsto b atTop (𝓝 0) := by
    simpa [b] using ((tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ))
      (by norm_num) (by norm_num)).comp (tendsto_sub_atTop_nat T.card)).const_mul (B ^ T.card)
  let F := fun S : Finset ι ↦
    ((A.submatrix (Subtype.val : S → ι) Subtype.val).charpolyRev : PowerSeries R) -
      A.charPowerSeries
  have hbound (S : Finset ι) (n : ℕ) : ‖(F S).coeff n‖ * ρ ^ n ≤ 2 * b n := by
    simp only [F, map_sub, Polynomial.coeff_coe, Matrix.coeff_charPowerSeries]
    calc ‖(A.submatrix (Subtype.val : S → ι) Subtype.val).charpolyRev.coeff n -
          A.charCoeff n‖ * ρ ^ n
        ≤ (‖(A.submatrix (Subtype.val : S → ι) Subtype.val).charpolyRev.coeff n‖ +
          ‖A.charCoeff n‖) * ρ ^ n :=
            mul_le_mul_of_nonneg_right (norm_sub_le _ _) (pow_nonneg hρ.le _)
      _ ≤ 2 * b n := by nlinarith [hb n, hbS S n]
  -- Small degrees converge by summability; large degrees are uniformly small.
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((hlim.const_mul 2).eventually (gt_mem_nhds
      (by simpa using (half_pos hε) : 2 * (0 : ℝ) < ε / 2)))
  have hlow : ∀ᶠ S : Finset ι in atTop, ∀ n ∈ range N,
      ‖(F S).coeff n‖ * ρ ^ n < ε / 2 := by
    refine (Finset.eventually_all _).mpr fun n hn ↦ ?_
    have hcoeff := tendsto_coeff_charpolyRev_finiteCompression n
      (Matrix.summable_principalMinor hA hr n)
    have hzero : Tendsto (fun S : Finset ι ↦ ‖(F S).coeff n‖ * ρ ^ n) atTop (𝓝 0) := by
      simpa [F] using ((hcoeff.sub_const (A.charCoeff n)).norm.mul_const (ρ ^ n))
    exact hzero.eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [hlow] with S hS
  rw [Real.dist_eq, sub_zero, abs_of_nonneg
    (PowerSeries.gaussNorm_nonneg norm ρ (F S) norm_nonneg)]
  refine lt_of_le_of_lt ?_ (half_lt_self hε)
  rw [PowerSeries.gaussNorm_eq]
  refine ciSup_le fun n ↦ ?_
  by_cases hn : n < N
  · exact (hS n (mem_range.mpr hn)).le
  · exact (hbound S n).trans (hN n (by omega)).le

end Ultrametric

end TauCeti
