/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.InformationTheory.Hamming
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import TauCeti.Statistics.HighDimensional.Design
public import TauCeti.Statistics.HighDimensional.ModelSelection.Penalized
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Data.Finset.Powerset
import TauCeti.Analysis.SpecialFunctions.Log.Choose

/-!
# Sparse regression upper bound via penalized model selection

For a fixed real design matrix `X : Matrix α ι ℝ` on finite index types `α` and `ι`, consider the
collection of column-subset models `m ↦ X.columnSpan m` indexed by `m : Finset ι`, equipped with
the dyadic subset prior weights

`subsetWeight m = 2 ^ (-(m.card + 1)) / C(|ι|, m.card)`.

These weights are strictly positive, satisfy `∑ m, subsetWeight m = 1 - 2 ^ (-(|ι| + 1)) ≤ 1`,
and satisfy the logarithmic complexity bound

`log (1 / subsetWeight m) ≤ (m.card + 1) * log 2 + m.card * log (e * |ι| / m.card)`.

Specializing the oracle inequality `penalized_model_selection` to the penalty
`pen m = κ * σ ^ 2 * (finrank (X.columnSpan m) + log (1 / subsetWeight m)) / |α|` with `κ > 4`
gives the sparse regression prediction-risk upper bound: for every `1 ≤ D ≤ |ι|` and every
`D`-sparse vector `β` (`hammingNorm (WithLp.ofLp β) ≤ D`), any measurable minimizer `mh` satisfies

`𝔼 ‖(X.columnSpan (mh (Xβ + σξ))).starProjection (Xβ + σξ) - Xβ‖ ^ 2 ≤`
`  (6 * κ ^ 2 / (κ - 4)) * σ ^ 2 * D * log (e * |ι| / D)`.

## Main definitions

* `TauCeti.subsetWeight`: the model weights `2 ^ (-(m.card + 1)) / C(|ι|, m.card)` over
  `m : Finset ι`.

## Main results

* `TauCeti.sum_subsetWeight_eq`: `∑ m : Finset ι, subsetWeight m = 1 - (2 : ℝ)⁻¹ ^ (|ι| + 1)`.
* `TauCeti.log_one_div_subsetWeight`: exact formula for `Real.log (1 / subsetWeight m)`.
* `TauCeti.log_one_div_subsetWeight_le`: logarithmic upper bound using `Real.log_choose_le`.
* `TauCeti.exists_measurable_sparseRegression_selector`: existence of a measurable selector
  over `Finset ι` for any penalty function.
* `TauCeti.integrable_sq_norm_sparseRegression`: integrability of the squared estimation error
  for the penalized sparse regression estimator.
* `TauCeti.sparse_regression_upper`: the explicit non-asymptotic risk upper bound with constant
  `6 * κ ^ 2 / (κ - 4)` for any `κ > 4`.

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

/-- The model weights `π_m = 2 ^ (-(m.card + 1)) / C(|ι|, m.card)` over finite subsets
`m : Finset ι`. Grouping by cardinality cancels the binomial coefficient and yields a geometric
sum strictly below `1`. -/
def subsetWeight (m : Finset ι) : ℝ :=
  (2 : ℝ)⁻¹ ^ (m.card + 1) / ((Fintype.card ι).choose m.card)

/-- Unfolding lemma for `subsetWeight`. -/
theorem subsetWeight_def (m : Finset ι) :
    subsetWeight m = (2 : ℝ)⁻¹ ^ (m.card + 1) / ((Fintype.card ι).choose m.card) :=
  (rfl)

/-- The weight of the empty subset is `1 / 2`. -/
@[simp]
theorem subsetWeight_empty : subsetWeight (∅ : Finset ι) = 2⁻¹ := by
  simp [subsetWeight_def]

/-- The weight of the full subset `Finset.univ` is `2 ^ (-(|ι| + 1))`. -/
@[simp]
theorem subsetWeight_univ :
    subsetWeight (Finset.univ : Finset ι) = (2 : ℝ)⁻¹ ^ (Fintype.card ι + 1) := by
  simp [subsetWeight_def]

/-- Every subset weight is strictly positive. -/
theorem subsetWeight_pos (m : Finset ι) : 0 < subsetWeight m := by
  rw [subsetWeight_def]
  have hch : 0 < ((Fintype.card ι).choose m.card : ℝ) :=
    Nat.cast_pos.mpr (Nat.choose_pos m.card_le_univ)
  positivity

/-- Every subset weight is nonnegative. -/
theorem subsetWeight_nonneg (m : Finset ι) : 0 ≤ subsetWeight m :=
  (subsetWeight_pos m).le

/-- The subset weights sum to `1 - 2 ^ (-(|ι| + 1))`. -/
theorem sum_subsetWeight_eq :
    ∑ m : Finset ι, subsetWeight m = 1 - (2 : ℝ)⁻¹ ^ (Fintype.card ι + 1) := by
  have hmaps : ∀ m ∈ (Finset.univ : Finset (Finset ι)),
      m.card ∈ Finset.range (Fintype.card ι + 1) := fun m _ ↦
    Finset.mem_range.mpr (Nat.lt_succ_of_le m.card_le_univ)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfiber (k : ℕ) (hk : k ∈ Finset.range (Fintype.card ι + 1)) :
      ∑ m ∈ Finset.univ.filter (fun m : Finset ι ↦ m.card = k), subsetWeight m =
        (2 : ℝ)⁻¹ ^ (k + 1) := by
    have hkle : k ≤ Fintype.card ι := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hset : Finset.univ.filter (fun m : Finset ι ↦ m.card = k) =
        Finset.powersetCard k (Finset.univ : Finset ι) := by
      ext m
      simp
    rw [hset]
    have hconst : ∀ m ∈ Finset.powersetCard k (Finset.univ : Finset ι),
        subsetWeight m = (2 : ℝ)⁻¹ ^ (k + 1) / ((Fintype.card ι).choose k) := by
      intro m hm
      rw [subsetWeight_def, (Finset.mem_powersetCard.mp hm).2]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_powersetCard,
      Finset.card_univ, nsmul_eq_mul]
    have hne : ((Fintype.card ι).choose k : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.choose_pos hkle).ne'
    exact mul_div_cancel₀ _ hne
  rw [Finset.sum_congr rfl hfiber]
  have hgeom : ∑ k ∈ Finset.range (Fintype.card ι + 1), (2 : ℝ)⁻¹ ^ (k + 1) =
      (2 : ℝ)⁻¹ * ∑ k ∈ Finset.range (Fintype.card ι + 1), (2 : ℝ)⁻¹ ^ k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    ring
  rw [hgeom, geom_sum_eq (by norm_num : (2 : ℝ)⁻¹ ≠ 1)]
  ring

/-- The sum of the subset weights is at most `1`. -/
theorem sum_subsetWeight_le_one : ∑ m : Finset ι, subsetWeight m ≤ 1 := by
  rw [sum_subsetWeight_eq]
  exact sub_le_self 1 (by positivity)

/-- Exact `tsum` form of `sum_subsetWeight_eq`. -/
theorem tsum_subsetWeight_eq :
    ∑' m : Finset ι, subsetWeight m = 1 - (2 : ℝ)⁻¹ ^ (Fintype.card ι + 1) := by
  rw [tsum_fintype, sum_subsetWeight_eq]

/-- The `tsum` of the subset weights is at most `1`. -/
theorem tsum_subsetWeight_le_one : ∑' m : Finset ι, subsetWeight m ≤ 1 := by
  rw [tsum_fintype]
  exact sum_subsetWeight_le_one

/-- Exact logarithmic complexity of `subsetWeight m`. -/
theorem log_one_div_subsetWeight (m : Finset ι) :
    Real.log (1 / subsetWeight m) =
      (m.card + 1 : ℝ) * Real.log 2 + Real.log ((Fintype.card ι).choose m.card) := by
  have hch_pos : (0 : ℝ) < ((Fintype.card ι).choose m.card : ℝ) :=
    Nat.cast_pos.mpr (Nat.choose_pos m.card_le_univ)
  have hinv : 1 / subsetWeight m =
      (2 : ℝ) ^ (m.card + 1) * ((Fintype.card ι).choose m.card : ℝ) := by
    rw [subsetWeight_def, one_div_div, inv_pow, div_inv_eq_mul, mul_comm]
  rw [hinv, Real.log_mul (by positivity) hch_pos.ne', Real.log_pow]
  push_cast
  ring

/-- Logarithmic upper bound for `1 / subsetWeight m`, valid for every `m : Finset ι` (including
`m = ∅`). -/
theorem log_one_div_subsetWeight_le (m : Finset ι) :
    Real.log (1 / subsetWeight m) ≤
      (m.card + 1 : ℝ) * Real.log 2 +
        m.card * Real.log (Real.exp 1 * Fintype.card ι / m.card) := by
  rw [log_one_div_subsetWeight]
  gcongr
  exact Real.log_choose_le m.card_le_univ

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
  exists_measurable_penalizedSelector_of_tendsto X.columnSpan pen (by
    rw [Filter.cofinite_eq_bot]
    exact Filter.tendsto_bot)

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
      (stdGaussian (EuclideanSpace ℝ α)) := by
  refine integrable_sq_norm_starProjection_sub X.columnSpan subsetWeight pen σ f mh hκ
    subsetWeight_pos (hasSum_fintype _).summable ?_ hmh hmin
  intro m
  simpa [finrank_euclideanSpace] using hpen m

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
  set p : ℕ := Fintype.card ι
  set n : ℕ := Fintype.card α
  set L : ℝ := Real.log (Real.exp 1 * p / D)
  have : 0 < κ - 4 := by linarith
  have hD_pos : (0 : ℝ) < D := Nat.cast_pos.mpr (by omega)
  have hD_ge : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  have hDp_real : (D : ℝ) ≤ p := by exact_mod_cast hDp
  have hL_ge_one : 1 ≤ L := by
    have hge : Real.exp 1 ≤ Real.exp 1 * p / D := by
      rw [le_div_iff₀ hD_pos]
      exact mul_le_mul_of_nonneg_left hDp_real (Real.exp_pos 1).le
    calc
      (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (Real.exp 1 * p / D) := Real.log_le_log (Real.exp_pos 1) hge
  -- Handle `n = 0` separately: the ambient Euclidean space is a subsingleton.
  rcases Nat.eq_zero_or_pos n with hn0 | hn_pos
  · have : IsEmpty α := Fintype.card_eq_zero_iff.mp hn0
    have hzero : ∀ ξ : EuclideanSpace ℝ α,
        ‖(X.columnSpan (mh (Matrix.toEuclideanLin X β + σ • ξ))).starProjection
          (Matrix.toEuclideanLin X β + σ • ξ) - Matrix.toEuclideanLin X β‖ ^ 2 = 0 := by
      intro ξ
      rw [Subsingleton.elim ((X.columnSpan _).starProjection _) (Matrix.toEuclideanLin X β),
        sub_self, norm_zero, zero_pow two_ne_zero]
    simp only [hzero, integral_zero]
    positivity
  -- For `n > 0`, inflate the support of `β` to a subset `m₁` of exact cardinality `D`.
  let supp : Finset ι := Finset.univ.filter (fun j ↦ WithLp.ofLp β j ≠ 0)
  have hsupp_card : supp.card ≤ D := hβ
  obtain ⟨m₁, hsupp_sub, hm₁_card⟩ := Finset.exists_superset_card_eq hsupp_card hDp
  set f : EuclideanSpace ℝ α := Matrix.toEuclideanLin X β
  have hf_mem : f ∈ X.columnSpan m₁ := by
    refine X.toEuclideanLin_mem_columnSpan fun j hj ↦ hsupp_sub ?_
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
  -- Apply the oracle inequality `penalized_model_selection`.
  let pen : Finset ι → ℝ := fun m ↦
    κ * σ ^ 2 * (Module.finrank ℝ (X.columnSpan m) + Real.log (1 / subsetWeight m)) / n
  have hpen_lb : ∀ m, κ * σ ^ 2 *
      (Module.finrank ℝ (X.columnSpan m) + Real.log (1 / subsetWeight m)) /
        Module.finrank ℝ (EuclideanSpace ℝ α) ≤ pen m := by
    intro m
    simp [pen, n, finrank_euclideanSpace]
  have horacle := penalized_model_selection X.columnSpan subsetWeight pen σ f mh hκ
    subsetWeight_pos (hasSum_fintype _).summable hpen_lb hmh hmin
  simp only [finrank_euclideanSpace] at horacle
  rw [integral_div] at horacle
  have hbdd : BddBelow (Set.range fun m : Finset ι ↦
      ‖f - (X.columnSpan m).starProjection f‖ ^ 2 / (n : ℝ) + pen m) :=
    (Set.finite_range _).bddBelow
  have hinf_le : (⨅ m : Finset ι,
      (‖f - (X.columnSpan m).starProjection f‖ ^ 2 / (n : ℝ) + pen m)) ≤ pen m₁ := by
    refine (ciInf_le hbdd m₁).trans_eq ?_
    rw [Submodule.starProjection_eq_self_iff.mpr hf_mem, sub_self, norm_zero,
      zero_pow two_ne_zero, zero_div, zero_add]
  have hsum_le : ∑' m : Finset ι, subsetWeight m ≤ 1 := tsum_subsetWeight_le_one
  have hn_real_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
  have hmul : ∫ ξ, ‖(X.columnSpan (mh (f + σ • ξ))).starProjection (f + σ • ξ) - f‖ ^ 2
      ∂stdGaussian (EuclideanSpace ℝ α) ≤
      κ / (κ - 4) * (κ * σ ^ 2 *
        (Module.finrank ℝ (X.columnSpan m₁) + Real.log (1 / subsetWeight m₁) +
          (1 + ∑' m : Finset ι, subsetWeight m))) := by
    have hstep : (∫ ξ, ‖(X.columnSpan (mh (f + σ • ξ))).starProjection (f + σ • ξ) - f‖ ^ 2
        ∂stdGaussian (EuclideanSpace ℝ α)) / (n : ℝ) ≤
        κ / (κ - 4) * (pen m₁ + κ * (1 + ∑' m : Finset ι, subsetWeight m) * σ ^ 2 / (n : ℝ)) := by
      refine horacle.trans ?_
      gcongr
    have hmul' := (div_le_iff₀ hn_real_pos).mp hstep
    refine hmul'.trans_eq ?_
    dsimp only [pen]
    have : (n : ℝ) ≠ 0 := hn_real_pos.ne'
    field_simp
  -- Bound the bracketed complexity factor by `6 * D * L`.
  have hlog2 : Real.log 2 ≤ 1 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      Real.log 2 ≤ Real.log (Real.exp 1) := Real.log_le_log (by positivity) h2
      _ = 1 := Real.log_exp 1
  have hfin_le : (Module.finrank ℝ (X.columnSpan m₁) : ℝ) ≤ D := by
    have : Module.finrank ℝ (X.columnSpan m₁) ≤ D := hm₁_card ▸ X.finrank_columnSpan_le m₁
    exact_mod_cast this
  have hlogw : Real.log (1 / subsetWeight m₁) ≤ (D + 1 : ℝ) * Real.log 2 + D * L := by
    simpa [hm₁_card, p, L] using log_one_div_subsetWeight_le m₁
  have hDL_ge_D : (D : ℝ) ≤ D * L := by
    nlinarith
  have hbracket : (Module.finrank ℝ (X.columnSpan m₁) : ℝ) +
      Real.log (1 / subsetWeight m₁) + (1 + ∑' m : Finset ι, subsetWeight m) ≤
      6 * D * L := by
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h1 : ((D : ℝ) + 1) * Real.log 2 ≤ 2 * D := by nlinarith
    nlinarith
  calc
    ∫ ξ, ‖(X.columnSpan (mh (f + σ • ξ))).starProjection (f + σ • ξ) - f‖ ^ 2
        ∂stdGaussian (EuclideanSpace ℝ α)
        ≤ κ / (κ - 4) * (κ * σ ^ 2 *
          (Module.finrank ℝ (X.columnSpan m₁) + Real.log (1 / subsetWeight m₁) +
            (1 + ∑' m : Finset ι, subsetWeight m))) := hmul
    _ ≤ κ / (κ - 4) * (κ * σ ^ 2 * (6 * D * L)) := by
        gcongr
    _ = 6 * κ ^ 2 / (κ - 4) * σ ^ 2 * D * L := by
        ring

end SparseRegression

end TauCeti
