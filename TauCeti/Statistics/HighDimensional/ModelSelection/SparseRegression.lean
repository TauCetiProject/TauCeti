/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.InformationTheory.Hamming
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import TauCeti.Analysis.Matrix.ColumnSpan
public import TauCeti.Statistics.HighDimensional.ModelSelection.Penalized
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Data.Finset.Powerset
import TauCeti.Analysis.SpecialFunctions.Log.Choose

/-!
# Sparse regression upper bound via penalized model selection

For a fixed real design matrix `X : Matrix α ι ℝ`, we equip column-subset models
`m ↦ X.columnSpan m` (`m : Finset ι`) with the dyadic weights
`subsetWeight m = 2 ^ (-(m.card + 1)) / C(|ι|, m.card)`, summing to `1 - 2 ^ (-(|ι| + 1)) ≤ 1`.
Specializing `penalized_model_selection` (`κ > 4`) gives `sparse_regression_upper`: for
`1 ≤ D ≤ |ι|` and `hammingNorm (WithLp.ofLp β) ≤ D`,

`𝔼 ‖(X.columnSpan (mh (Xβ + σξ))).starProjection (Xβ + σξ) - Xβ‖ ^ 2 ≤`
`  (6 * κ ^ 2 / (κ - 4)) * σ ^ 2 * D * log (e * |ι| / D)`.

## References

* C. Giraud, *Introduction to High-Dimensional Statistics*, 2nd ed., CRC Press (2022), §3.3, (3.16),
  p. 67 (by the same argument, with geometric-type weights in place of `2 ^ (-|m| - 1)`).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter

namespace TauCeti

/-! ### Dyadic subset weights -/

section SubsetWeight

variable {ι : Type*} [Fintype ι]

/-- Model weights `π_m = 2 ^ (-(m.card + 1)) / C(|ι|, m.card)` over `m : Finset ι`. -/
def subsetWeight (m : Finset ι) : ℝ :=
  (2 : ℝ)⁻¹ ^ (m.card + 1) / ((Fintype.card ι).choose m.card)

/-- Unfolding lemma for `subsetWeight`. -/
theorem subsetWeight_def (m : Finset ι) :
    subsetWeight m = (2 : ℝ)⁻¹ ^ (m.card + 1) / ((Fintype.card ι).choose m.card) := (rfl)

/-- The weight of the empty subset is `1 / 2`. -/
@[simp]
theorem subsetWeight_empty : subsetWeight (∅ : Finset ι) = 2⁻¹ := by simp [subsetWeight_def]

/-- The weight of the full subset `Finset.univ` is `2 ^ (-(|ι| + 1))`. -/
@[simp]
theorem subsetWeight_univ :
    subsetWeight (Finset.univ : Finset ι) = (2 : ℝ)⁻¹ ^ (Fintype.card ι + 1) := by
  simp [subsetWeight_def]

/-- Every subset weight is strictly positive. -/
theorem subsetWeight_pos (m : Finset ι) : 0 < subsetWeight m :=
  div_pos (by positivity) (Nat.cast_pos.mpr (Nat.choose_pos m.card_le_univ))

/-- Every subset weight is nonnegative. -/
theorem subsetWeight_nonneg (m : Finset ι) : 0 ≤ subsetWeight m := (subsetWeight_pos m).le

/-- The subset weights sum to `1 - 2 ^ (-(|ι| + 1))`. -/
theorem sum_subsetWeight_eq :
    ∑ m : Finset ι, subsetWeight m = 1 - (2 : ℝ)⁻¹ ^ (Fintype.card ι + 1) := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun m _ ↦ Finset.mem_range.mpr (Nat.lt_succ_of_le m.card_le_univ))]
  have hfiber (k : ℕ) (hk : k ∈ Finset.range (Fintype.card ι + 1)) :
      ∑ m ∈ Finset.univ.filter (fun m : Finset ι ↦ m.card = k), subsetWeight m =
        (2 : ℝ)⁻¹ ^ (k + 1) := by
    have hset : Finset.univ.filter (fun m : Finset ι ↦ m.card = k) =
        Finset.powersetCard k (Finset.univ : Finset ι) := by ext m; simp
    rw [hset, Finset.sum_congr rfl fun m hm ↦ by
      rw [subsetWeight_def, (Finset.mem_powersetCard.mp hm).2], Finset.sum_const,
      Finset.card_powersetCard, Finset.card_univ, nsmul_eq_mul]
    exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr
      (Nat.choose_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))).ne')
  rw [Finset.sum_congr rfl hfiber]
  simp_rw [pow_succ']
  rw [← Finset.mul_sum, geom_sum_eq (by norm_num : (2 : ℝ)⁻¹ ≠ 1)]; ring

/-- The sum of the subset weights is at most `1`. -/
theorem sum_subsetWeight_le_one : ∑ m : Finset ι, subsetWeight m ≤ 1 := by
  rw [sum_subsetWeight_eq]; exact sub_le_self 1 (by positivity)

/-- Exact `tsum` form of `sum_subsetWeight_eq`. -/
theorem tsum_subsetWeight_eq :
    ∑' m : Finset ι, subsetWeight m = 1 - (2 : ℝ)⁻¹ ^ (Fintype.card ι + 1) := by
  rw [tsum_fintype, sum_subsetWeight_eq]

/-- The `tsum` of the subset weights is at most `1`. -/
theorem tsum_subsetWeight_le_one : ∑' m : Finset ι, subsetWeight m ≤ 1 := by
  rw [tsum_fintype]; exact sum_subsetWeight_le_one

/-- Exact logarithmic complexity of `subsetWeight m`. -/
theorem log_one_div_subsetWeight (m : Finset ι) : Real.log (1 / subsetWeight m) =
    (m.card + 1 : ℝ) * Real.log 2 + Real.log ((Fintype.card ι).choose m.card) := by
  have hinv : 1 / subsetWeight m =
      (2 : ℝ) ^ (m.card + 1) * ((Fintype.card ι).choose m.card : ℝ) := by
    rw [subsetWeight_def, one_div_div, inv_pow, div_inv_eq_mul, mul_comm]
  rw [hinv, Real.log_mul (by positivity)
    (Nat.cast_ne_zero.mpr (Nat.choose_pos m.card_le_univ).ne'), Real.log_pow]
  push_cast; ring

/-- Logarithmic upper bound for `1 / subsetWeight m`, valid for every `m : Finset ι` (including
`m = ∅`). -/
theorem log_one_div_subsetWeight_le (m : Finset ι) : Real.log (1 / subsetWeight m) ≤
    (m.card + 1 : ℝ) * Real.log 2 + m.card * Real.log (Real.exp 1 * Fintype.card ι / m.card) := by
  rw [log_one_div_subsetWeight]; gcongr; exact Real.log_choose_le m.card_le_univ

end SubsetWeight

/-! ### Penalized sparse regression upper bound -/

section SparseRegression

variable {α : Type*} [Fintype α]

/-- Since `Finset ι` is finite, a measurable minimizer of `penalizedCriterion X.columnSpan pen`
exists for every penalty function `pen : Finset ι → ℝ`. -/
theorem exists_measurable_sparseRegression_selector {ι : Type*} [Finite ι] (X : Matrix α ι ℝ)
    (pen : Finset ι → ℝ) :
    ∃ mh : EuclideanSpace ℝ α → Finset ι, Measurable mh ∧
      ∀ Y m, penalizedCriterion X.columnSpan pen Y (mh Y) ≤
        penalizedCriterion X.columnSpan pen Y m :=
  exists_measurable_penalizedSelector_of_tendsto X.columnSpan pen
    (by rw [Filter.cofinite_eq_bot]; exact Filter.tendsto_bot)

/-- Integrability of the squared prediction error for any measurable penalized selector over
column subsets with penalty dominating
`κ * σ ^ 2 * (finrank (X.columnSpan m) + log (1 / subsetWeight m)) / Fintype.card α` and
`κ > 4`. -/
theorem integrable_sq_norm_sparseRegression {ι : Type*} [Fintype ι] (X : Matrix α ι ℝ)
    (pen : Finset ι → ℝ) {κ : ℝ} (σ : ℝ) (f : EuclideanSpace ℝ α)
    (mh : EuclideanSpace ℝ α → Finset ι) (hκ : 4 < κ)
    (hpen : ∀ m, κ * σ ^ 2 *
        (Module.finrank ℝ (X.columnSpan m) + Real.log (1 / subsetWeight m)) /
          Fintype.card α ≤ pen m)
    (hmh : Measurable mh)
    (hmin : ∀ Y m, penalizedCriterion X.columnSpan pen Y (mh Y) ≤
      penalizedCriterion X.columnSpan pen Y m) :
    Integrable (fun ξ ↦
        ‖(X.columnSpan (mh (f + σ • ξ))).starProjection (f + σ • ξ) - f‖ ^ 2)
      (stdGaussian (EuclideanSpace ℝ α)) :=
  integrable_sq_norm_starProjection_sub X.columnSpan subsetWeight pen σ f mh hκ
    subsetWeight_pos (hasSum_fintype _).summable
    (fun m ↦ by simpa [finrank_euclideanSpace] using hpen m) hmh hmin

omit [Fintype α] in
/-- For a subset `m₁` of cardinality `D` (`1 ≤ D ≤ |ι|`), the combined dimension, log-weight, and
remainder terms in the oracle bound are at most `6 * D * log (e * |ι| / D)`. -/
private theorem sparseRegression_complexity_le {ι : Type*} [Fintype ι] (X : Matrix α ι ℝ)
    {D : ℕ} (hD1 : 1 ≤ D) (hDp : D ≤ Fintype.card ι) {m₁ : Finset ι} (hm₁ : m₁.card = D) :
    (Module.finrank ℝ (X.columnSpan m₁) : ℝ) +
        Real.log (1 / subsetWeight m₁) + (1 + ∑' m : Finset ι, subsetWeight m) ≤
      6 * D * Real.log (Real.exp 1 * Fintype.card ι / D) := by
  set L : ℝ := Real.log (Real.exp 1 * Fintype.card ι / D)
  have hD_pos : (0 : ℝ) < D := Nat.cast_pos.mpr (by omega)
  have hL_ge_one : 1 ≤ L := by
    rw [← Real.log_exp 1]
    refine Real.log_le_log (Real.exp_pos 1) ?_
    rw [le_div_iff₀ hD_pos]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hDp) (Real.exp_pos 1).le
  have hlog2 : Real.log 2 ≤ 1 := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (by positivity) (by linarith [Real.add_one_le_exp (1 : ℝ)])
  have hfin_le : (Module.finrank ℝ (X.columnSpan m₁) : ℝ) ≤ D := by
    exact_mod_cast hm₁ ▸ X.finrank_columnSpan_le m₁
  have hlogw : Real.log (1 / subsetWeight m₁) ≤ (D + 1 : ℝ) * Real.log 2 + D * L := by
    simpa [hm₁, L] using log_one_div_subsetWeight_le m₁
  have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  nlinarith [tsum_subsetWeight_le_one (ι := ι)]

/-- **Upper bound for sparse regression by penalized selection over column subsets** (Giraud,
(3.16), by the same argument): for `κ > 4`, `1 ≤ D ≤ |ι|`, any `σ : ℝ`, any measurable minimizer
`mh` of the penalized criterion with penalty
`m ↦ κ * σ ^ 2 * (finrank (X.columnSpan m) + log (1 / subsetWeight m)) / |α|`, and every
`D`-sparse vector `β` (`hammingNorm (WithLp.ofLp β) ≤ D`), the squared prediction risk satisfies
`𝔼 ‖f̂ - Xβ‖ ^ 2 ≤ (6 * κ ^ 2 / (κ - 4)) * σ ^ 2 * D * log (e * |ι| / D)`. -/
theorem sparse_regression_upper {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix α ι ℝ)
    {κ : ℝ} (σ : ℝ) {D : ℕ}
    (mh : EuclideanSpace ℝ α → Finset ι)
    (hκ : 4 < κ) (hD1 : 1 ≤ D) (hDp : D ≤ Fintype.card ι) (hmh : Measurable mh)
    (hmin : ∀ Y m,
      penalizedCriterion X.columnSpan
        (fun m ↦ κ * σ ^ 2 * (Module.finrank ℝ (X.columnSpan m) +
          Real.log (1 / subsetWeight m)) / Fintype.card α) Y (mh Y) ≤
      penalizedCriterion X.columnSpan
        (fun m ↦ κ * σ ^ 2 * (Module.finrank ℝ (X.columnSpan m) +
          Real.log (1 / subsetWeight m)) / Fintype.card α) Y m)
    (β : EuclideanSpace ℝ ι) (hβ : hammingNorm (WithLp.ofLp β) ≤ D) :
    ∫ ξ, ‖(X.columnSpan (mh (Matrix.toEuclideanLin X β + σ • ξ))).starProjection
        (Matrix.toEuclideanLin X β + σ • ξ) - Matrix.toEuclideanLin X β‖ ^ 2
      ∂stdGaussian (EuclideanSpace ℝ α) ≤
      6 * κ ^ 2 / (κ - 4) * σ ^ 2 * D * Real.log (Real.exp 1 * Fintype.card ι / D) := by
  set n : ℕ := Fintype.card α
  set L : ℝ := Real.log (Real.exp 1 * Fintype.card ι / D)
  have : 0 < κ - 4 := by linarith
  -- Handle the degenerate `|α| = 0` case directly.
  rcases Nat.eq_zero_or_pos n with hn0 | hn_pos
  · have hD_pos : (0 : ℝ) < D := Nat.cast_pos.mpr (by omega)
    have hL_nonneg : 0 ≤ L := Real.log_nonneg <| (le_div_iff₀ hD_pos).mpr <| by
      simpa only [one_mul] using
        mul_le_mul (by linarith [Real.add_one_le_exp (1 : ℝ)] : (1 : ℝ) ≤ Real.exp 1)
          ((Nat.cast_le (α := ℝ)).mpr hDp) hD_pos.le (Real.exp_pos 1).le
    have : IsEmpty α := Fintype.card_eq_zero_iff.mp hn0
    have hzero (ξ : EuclideanSpace ℝ α) :
        ‖(X.columnSpan (mh (Matrix.toEuclideanLin X β + σ • ξ))).starProjection
          (Matrix.toEuclideanLin X β + σ • ξ) - Matrix.toEuclideanLin X β‖ ^ 2 = 0 := by
      rw [Subsingleton.elim ((X.columnSpan _).starProjection _) _, sub_self]; simp
    simp only [hzero, integral_zero]; positivity
  -- Enlarge `supp β` to a subset `m₁` of size `D` so `Xβ ∈ X.columnSpan m₁`, then apply the oracle
  -- inequality at `m₁` and bound the complexity bracket by `6 * D * L`.
  obtain ⟨m₁, hsupp_sub, hm₁_card⟩ := Finset.exists_superset_card_eq
    (s := Finset.univ.filter (fun j ↦ WithLp.ofLp β j ≠ 0)) hβ hDp
  set f : EuclideanSpace ℝ α := Matrix.toEuclideanLin X β
  have hf_mem : f ∈ X.columnSpan m₁ := X.toEuclideanLin_mem_columnSpan fun j hj ↦
    hsupp_sub (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
  let pen : Finset ι → ℝ := fun m ↦
    κ * σ ^ 2 * (Module.finrank ℝ (X.columnSpan m) + Real.log (1 / subsetWeight m)) / n
  have horacle := penalized_model_selection X.columnSpan subsetWeight pen σ f mh hκ
    subsetWeight_pos (hasSum_fintype _).summable
    (fun m ↦ by simp [pen, n, finrank_euclideanSpace]) hmh hmin
  simp only [finrank_euclideanSpace] at horacle
  rw [integral_div] at horacle
  have hinf_le : (⨅ m : Finset ι,
      (‖f - (X.columnSpan m).starProjection f‖ ^ 2 / (n : ℝ) + pen m)) ≤ pen m₁ :=
    (ciInf_le (Set.finite_range _).bddBelow m₁).trans_eq
      (by simp [Submodule.starProjection_eq_self_iff.mpr hf_mem])
  have hn_pos' : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
  have hmul : ∫ ξ, ‖(X.columnSpan (mh (f + σ • ξ))).starProjection (f + σ • ξ) - f‖ ^ 2
      ∂stdGaussian (EuclideanSpace ℝ α) ≤
      κ / (κ - 4) * (κ * σ ^ 2 *
        (Module.finrank ℝ (X.columnSpan m₁) + Real.log (1 / subsetWeight m₁) +
          (1 + ∑' m : Finset ι, subsetWeight m))) := by
    have hstep : _ / (n : ℝ) ≤ κ / (κ - 4) *
        (pen m₁ + κ * (1 + ∑' m : Finset ι, subsetWeight m) * σ ^ 2 / (n : ℝ)) :=
      horacle.trans (by dsimp only [n] at hinf_le ⊢; gcongr)
    refine ((div_le_iff₀ hn_pos').mp hstep).trans_eq ?_
    have : (n : ℝ) ≠ 0 := hn_pos'.ne'
    dsimp only [pen]; field_simp
  have hbracket := sparseRegression_complexity_le X hD1 hDp hm₁_card
  calc
    _ ≤ κ / (κ - 4) * (κ * σ ^ 2 * (6 * D * L)) := hmul.trans (by gcongr)
    _ = 6 * κ ^ 2 / (κ - 4) * σ ^ 2 * D * L := by ring

end SparseRegression

end TauCeti
