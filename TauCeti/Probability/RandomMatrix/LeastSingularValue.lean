/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Codex
-/
module

public import TauCeti.Probability.RandomMatrix.Compressible
public import TauCeti.Probability.RandomMatrix.InvertibilityViaDistance
public import TauCeti.Analysis.InnerProductSpace.SingularValues.Least
import TauCeti.Probability.RandomMatrix.ColumnDistance

/-!
# Reduction for the least singular value

The lower tail of the last source-indexed singular value is bounded by the sum of the
compressible-vector exceptional probability and the average of the column-to-span lower
tails, up to a constant depending only on the entry variance proxy. The reduction applies
to square and tall real matrices with independent sub-Gaussian entries and a uniform
second-moment lower bound.

## References

* M. Rudelson and R. Vershynin, *The Littlewood–Offord problem and invertibility of random
  matrices*, Advances in Mathematics 218 (2008), §3 and §5.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Metric Matrix Set
open scoped NNReal

namespace TauCeti.Probability

private theorem leastSingularValue_event_subset
    {Ω m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] [Nonempty n]
    {A : Ω → Matrix m n ℝ} {k : ℕ} {ρ : ℝ≥0} {t u : ℝ} (htu : t ≤ u) :
    {ω | (toEuclideanLin (A ω)).singularValues (Fintype.card n - 1) < t} ⊆
      {ω | ∃ x, TauCeti.IsCompressibleVector k ρ x ∧ ‖toEuclideanLin (A ω) x‖ < u} ∪
      {ω | ∃ x, TauCeti.IsIncompressibleVector k ρ x ∧ ‖toEuclideanLin (A ω) x‖ < t} := by
  intro ω hω
  have hmin := (toEuclideanLin (A ω)).isLeast_norm_image_sphere
  rw [finrank_euclideanSpace] at hmin
  obtain ⟨x, hx, heq⟩ := hmin.1
  have hnorm : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
  have hsmall : ‖toEuclideanLin (A ω) x‖ < t := by
    have heq' : ‖toEuclideanLin (A ω) x‖ =
        (toEuclideanLin (A ω)).singularValues (Fintype.card n - 1) := heq
    rw [heq']
    exact hω
  rcases TauCeti.isCompressibleVector_or_isIncompressibleVector_iff.mpr hnorm with h | h
  · exact Or.inl ⟨x, h, hsmall.trans_le htu⟩
  · exact Or.inr ⟨x, h, hsmall⟩

/-- The least source-indexed singular value of a square or tall real random matrix has
a lower tail bounded by an exponentially small error plus a multiple of the mean
column-distance probability. Here `ε` is the threshold for column distances and
`ρ * ε / √(card n)` is the singular-value threshold for the unnormalized matrix. The bound
applies whenever the singular-value threshold is at most `√(card m) / 4`. -/
theorem exists_measureReal_singularValues_card_sub_one_lt_le (K : ℝ≥0) :
    ∃ ρ : ℝ≥0, 0 < ρ ∧ ρ ≤ 1 / 4 ∧ ∃ a C : ℝ, 0 < a ∧ 0 < C ∧
      ∀ {Ω m n : Type*} [MeasurableSpace Ω] [Fintype m] [Fintype n] [DecidableEq n]
        {P : Measure Ω} {A : Ω → Matrix m n ℝ},
        iIndepFun (fun ij : m × n ↦ fun ω ↦ A ω ij.1 ij.2) P →
        (∀ i j, HasSubgaussianMGF (fun ω ↦ A ω i j) K P) →
        (∀ i j, 1 ≤ ∫ ω, (A ω i j) ^ 2 ∂P) →
        Fintype.card n ≤ Fintype.card m →
        ∀ {ε : ℝ}, (ρ : ℝ) / Real.sqrt (Fintype.card n) * ε ≤ Real.sqrt (Fintype.card m) / 4 →
          P.real {ω | (toEuclideanLin (A ω)).singularValues (Fintype.card n - 1) <
            (ρ : ℝ) / Real.sqrt (Fintype.card n) * ε} ≤
              4 * Real.exp (-a * Fintype.card m) +
                C * ((∑ i, P.real {ω | infDist (WithLp.toLp 2 fun r ↦ A ω r i)
                  (Submodule.span ℝ (range fun j : {j // j ≠ i} ↦
                    WithLp.toLp 2 fun r ↦ A ω r j) : Set (EuclideanSpace ℝ m)) < ε}) /
                  Fintype.card n) := by
  obtain ⟨δ, hδ, _, ρ, hρ, hρ₁, a, ha, hcomp⟩ :=
    exists_measureReal_exists_isCompressibleVector_norm_toEuclideanLin_lt_le K
  refine ⟨ρ, hρ, hρ₁, a, δ⁻¹, ha, inv_pos.mpr hδ, ?_⟩
  intro Ω m n _ _ _ _ P A hind hA hmom hdim ε hε
  by_cases hn₀ : Fintype.card n = 0
  · simp only [hn₀, Nat.cast_zero, Real.sqrt_zero, div_zero, zero_mul,
      not_lt.mpr (LinearMap.singularValues_nonneg _ _), Set.ofPred_false, measureReal_empty]
    positivity
  have : Nonempty n := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hn₀)
  have : IsProbabilityMeasure P := hind.isProbabilityMeasure
  let k := ⌊δ * Fintype.card n⌋₊
  have hcomp' := hcomp hind hA hmom hdim
  have hinc := TauCeti.measureReal_exists_isIncompressibleVector_norm_toEuclideanLin_lt_le
    (P := P) (k := k) (ε := ε) ρ.coe_nonneg A
  have hsum : 0 ≤ ∑ i, P.real {ω | infDist (WithLp.toLp 2 fun r ↦ A ω r i)
      (Submodule.span ℝ (range fun j : {j // j ≠ i} ↦
        WithLp.toLp 2 fun r ↦ A ω r j) : Set (EuclideanSpace ℝ m)) < ε} :=
    Finset.sum_nonneg fun _ _ ↦ measureReal_nonneg
  have hk : δ * (Fintype.card n : ℝ) ≤ k + 1 := (Nat.lt_floor_add_one _).le
  have hn : 0 < (Fintype.card n : ℝ) := by exact_mod_cast Fintype.card_pos
  calc
    _ ≤ _ := (measureReal_mono (leastSingularValue_event_subset (A := A) (k := k) hε)
      (measure_ne_top _ _)).trans (measureReal_union_le _ _)
    _ ≤ _ := add_le_add hcomp' hinc
    _ ≤ _ := by
      gcongr
      rw [← div_eq_inv_mul, div_div, mul_comm (Fintype.card n : ℝ)]
      exact div_le_div_of_nonneg_left hsum (mul_pos hδ hn) hk

/-- A dimension-dependent lower tail for the least singular value of a square or tall
random matrix. In addition to the compressible-vector error that decays exponentially in
the row count, the bound has an error that decays exponentially in the excess number of rows.
The threshold is proportional to the square root of the minimal column-span codimension
divided by the square root of the column count. -/
theorem exists_measureReal_singularValues_card_sub_one_lt_le_of_card_le (K : ℝ≥0) :
    ∃ ρ a C : ℝ, 0 < ρ ∧ 0 < a ∧ 0 < C ∧
      ∀ {Ω m n : Type*} [MeasurableSpace Ω] [Fintype m] [Fintype n] [DecidableEq n]
        {P : Measure Ω} {A : Ω → Matrix m n ℝ},
        iIndepFun (fun ij : m × n ↦ fun ω ↦ A ω ij.1 ij.2) P →
        (∀ i j, HasSubgaussianMGF (fun ω ↦ A ω i j) K P) →
        (∀ i j, 1 ≤ ∫ ω, (A ω i j) ^ 2 ∂P) →
        Fintype.card n ≤ Fintype.card m →
        ∀ {ε : ℝ}, 0 ≤ ε →
          let d := Fintype.card m - (Fintype.card n - 1)
          P.real {ω | (toEuclideanLin (A ω)).singularValues (Fintype.card n - 1) <
            ρ / Real.sqrt (Fintype.card n) * ((1 - ε) * Real.sqrt d)} ≤
              4 * Real.exp (-a * Fintype.card m) +
                2 * C * Real.exp (-(ε ^ 2 * d) / (3200 * (K : ℝ) ^ 2)) := by
  obtain ⟨ρ, hρ, hρ₄, a, C, ha, hC, htail⟩ := exists_measureReal_singularValues_card_sub_one_lt_le K
  refine ⟨ρ, a, C, by exact_mod_cast hρ, ha, hC, ?_⟩
  intro Ω m n _ _ _ _ P A hind hA hmom hdim ε hε d
  by_cases hn₀ : Fintype.card n = 0
  · simp only [hn₀, Nat.cast_zero, Real.sqrt_zero, div_zero, zero_mul,
      not_lt.mpr (LinearMap.singularValues_nonneg _ _), Set.ofPred_false, measureReal_empty]
    positivity
  have : Nonempty n := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hn₀)
  have hρ' : (ρ : ℝ) ≤ 1 / 4 := by exact_mod_cast hρ₄
  have hcard : (1 : ℝ) ≤ Fintype.card n := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn₀))
  have hn : 1 ≤ Real.sqrt (Fintype.card n) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hcard
  have hd : Real.sqrt d ≤ Real.sqrt (Fintype.card m) :=
    Real.sqrt_le_sqrt (by exact_mod_cast Nat.sub_le (Fintype.card m) (Fintype.card n - 1))
  have hsmall : (1 - ε) * Real.sqrt d ≤ Real.sqrt (Fintype.card m) :=
    (mul_le_of_le_one_left (by positivity) (by linarith)).trans hd
  have hs : (ρ : ℝ) / Real.sqrt (Fintype.card n) ≤ 1 / 4 :=
    (div_le_self ρ.coe_nonneg hn).trans hρ'
  have hthreshold : (ρ : ℝ) / Real.sqrt (Fintype.card n) * ((1 - ε) * Real.sqrt d) ≤
      Real.sqrt (Fintype.card m) / 4 := by
    calc
      _ ≤ (ρ : ℝ) / Real.sqrt (Fintype.card n) * Real.sqrt (Fintype.card m) :=
        mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ ≤ (1 / 4) * Real.sqrt (Fintype.card m) := mul_le_mul_of_nonneg_right hs (by positivity)
      _ = _ := by ring
  have hmeas : AEMeasurable A P :=
    .of_eval fun i ↦ .of_eval fun j ↦ (hA i j).aemeasurable
  have hcol (i : n) := hind.measureReal_infDist_col_span_lt_one_sub_mul_sqrt_le
    hmeas i (fun r ↦ hA r i) (fun r ↦ hmom r i) hε
  refine (htail hind hA hmom hdim hthreshold).trans ?_
  rw [mul_comm (2 : ℝ) C, mul_assoc]
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hC.le)
  refine (div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ ↦ hcol i)
    (by positivity)).trans_eq ?_
  have hc : (Fintype.card n : ℝ) ≠ 0 := by positivity
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [mul_div_cancel_left₀ _ hc]

end TauCeti.Probability
