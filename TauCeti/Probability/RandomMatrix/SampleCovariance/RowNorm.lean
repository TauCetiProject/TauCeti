/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.HasLaw
import TauCeti.Probability.StrongLaw.DoubleArray

/-!
# Uniform squared row and column norms of data arrays

Let `x` be an array, indexed by `ℕ × ℕ`, whose entries have a common law `ν` with finite fourth
moment. Bai and Yin's strong law for double arrays
(`TauCeti.Probability.ae_eventually_forall_abs_sum_div_sub_integral_le`), applied to the squared
norms of the entries, gives the uniform behaviour of the squared row and column norms of the
normalized `p(n) × n` corners `Xₙ / √n` when `p(n) / n → y > 0`: almost surely they tend to
`E‖x‖²` and to `y E‖x‖²`, uniformly over the rows and over the columns. The rows need independence
within each row and the columns independence within each column. These are the degree bounds in
Bai and Yin's analysis of the smallest eigenvalue of the sample covariance matrix `Xₙ Xₙᴴ / n`.

## Main results

The results are filed under `TauCeti.Probability.SampleCovariance`, next to the other estimates
on the corners of data arrays.

* `SampleCovariance.ae_eventually_forall_abs_sum_norm_sq_div_sub_integral_le`: the squared row
  norms of the normalized corners tend to `E‖x‖²`, uniformly over the rows.
* `SampleCovariance.ae_eventually_forall_abs_sum_norm_sq_div_sub_mul_integral_le`: the squared
  column norms of the normalized corners tend to `y E‖x‖²`, uniformly over the columns.

## References

* Z. D. Bai and Y. Q. Yin, *Limit of the smallest eigenvalue of a large dimensional sample
  covariance matrix*, Ann. Probab. 21 (1993), 1275–1294, Lemma 2.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Real
open scoped Topology ENNReal NNReal

namespace TauCeti.Probability.SampleCovariance

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

section Norms

variable {E : Type*} [SeminormedAddGroup E] [MeasurableSpace E] {x : ℕ × ℕ → Ω → E}
  {ν : Measure E}

/-- **Squared row norms.** Let the array have entries with a common law `ν` of finite fourth
moment, independent within each row, and let `ℓ(n) → ∞` and `r(n) ≤ K ℓ(n)` eventually. Then
almost surely, for every `ε > 0`, eventually every row of the `r(n) × ℓ(n)` corner has mean
squared norm `ℓ(n)⁻¹ ∑ⱼ ‖xᵢⱼ‖²` within `ε` of `∫ ‖z‖ ^ 2 ∂ν`. For `ℓ(n) = n` these are the
squared row norms of the normalized corners `Xₙ / √n`. -/
theorem ae_eventually_forall_abs_sum_norm_sq_div_sub_integral_le (hx : ∀ ij, HasLaw (x ij) ν P)
    (hrow : ∀ i, iIndepFun (fun j ↦ x (i, j)) P) (h4 : Integrable (fun z ↦ ‖z‖ ^ 4) ν)
    {r ℓ : ℕ → ℕ} {K : ℝ} (hℓ : Tendsto ℓ atTop atTop) (hr : ∀ᶠ n in atTop, (r n : ℝ) ≤ K * ℓ n) :
    ∀ᵐ ω ∂P, ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ i : Fin (r n),
      |(∑ j : Fin (ℓ n), ‖x (i, j) ω‖ ^ 2) / ℓ n - ∫ z, ‖z‖ ^ 2 ∂ν| ≤ ε := by
  -- The squared norm is a.e. measurable as the square root of `‖·‖ ^ 4`.
  have hf : AEMeasurable (fun z : E ↦ ‖z‖ ^ 2) ν :=
    h4.aemeasurable.sqrt.congr (.of_forall fun z ↦ by
      dsimp only
      rw [show ‖z‖ ^ 4 = (‖z‖ ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)])
  -- The squared norms have the law `ν.map (‖·‖ ^ 2)`, with finite second moment.
  have h2 : MemLp id 2 (ν.map fun z ↦ ‖z‖ ^ 2) := by
    rw [memLp_map_measure_iff aestronglyMeasurable_id hf, Function.id_comp,
      memLp_two_iff_integrable_sq hf.aestronglyMeasurable]
    simpa only [← pow_mul] using h4
  have hmean : ∫ z, z ∂(ν.map fun z ↦ ‖z‖ ^ 2) = ∫ z, ‖z‖ ^ 2 ∂ν :=
    integral_map hf (by fun_prop)
  rw [← hmean]
  exact ae_eventually_forall_abs_sum_div_sub_integral_le (ξ := fun ij ω ↦ ‖x ij ω‖ ^ 2)
    (fun ij ↦ (hasLaw_map hf).fun_comp (hx ij))
    (fun i ↦ (hrow i).comp₀ (fun _ z ↦ ‖z‖ ^ 2) (fun _ ↦ (hx _).aemeasurable) fun _ ↦ by
      rwa [(hx _).map_eq]) h2 hℓ hr

/-- **Squared column norms of the corners.** Let the array have entries with a common law `ν` of
finite fourth moment, independent within each column, and let `p(n) / n → y > 0`. Then almost
surely, for every `ε > 0`, eventually every column of the normalized `p(n) × n` corner `Xₙ / √n`
has squared norm `n⁻¹ ∑ᵢ ‖xᵢⱼ‖²` within `ε` of `y ∫ ‖z‖ ^ 2 ∂ν`. -/
theorem ae_eventually_forall_abs_sum_norm_sq_div_sub_mul_integral_le
    (hx : ∀ ij, HasLaw (x ij) ν P) (hcol : ∀ j, iIndepFun (fun i ↦ x (i, j)) P)
    (h4 : Integrable (fun z ↦ ‖z‖ ^ 4) ν) {p : ℕ → ℕ} {y : ℝ} (hy : 0 < y)
    (hp : Tendsto (fun n ↦ (p n : ℝ) / n) atTop (𝓝 y)) :
    ∀ᵐ ω ∂P, ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ j : Fin n,
      |(∑ i : Fin (p n), ‖x (i, j) ω‖ ^ 2) / n - y * ∫ z, ‖z‖ ^ 2 ∂ν| ≤ ε := by
  set m := ∫ z, ‖z‖ ^ 2 ∂ν
  -- Eventually `p(n) ≥ y n / 2`, so the columns are the rows of a corner of the transpose.
  have hhalf : ∀ᶠ n : ℕ in atTop, y / 2 * n ≤ p n := by
    filter_upwards [hp.eventually (le_mem_nhds (half_lt_self hy)), eventually_gt_atTop 0]
      with n hn hn₀
    exact (le_div_iff₀ (by exact_mod_cast hn₀)).1 hn
  have hpℓ : Tendsto p atTop atTop := by
    refine tendsto_natCast_atTop_iff.1 (tendsto_atTop_mono' atTop hhalf ?_)
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (half_pos hy)
  have hnp : ∀ᶠ n : ℕ in atTop, (n : ℝ) ≤ 2 / y * p n :=
    hhalf.mono fun n hn ↦ by
      rw [div_mul_eq_mul_div, le_div_iff₀ hy]
      linarith
  have hrows := ae_eventually_forall_abs_sum_norm_sq_div_sub_integral_le (r := fun n ↦ n)
    (x := fun ij ↦ x ij.swap) (fun _ ↦ hx _) hcol h4 hpℓ hnp
  filter_upwards [hrows] with ω hω ε hε
  -- Rescale the column averages by `p(n) / n → y`.
  set δ := min 1 (ε / (2 * y))
  have hδ : 0 < δ := lt_min one_pos (by positivity)
  have hη : 0 < ε / (2 * (|m| + 1)) := by positivity
  filter_upwards [hω δ hδ, Metric.tendsto_nhds.1 hp _ hη, hpℓ.eventually (eventually_gt_atTop 0)]
    with n hn hpn hp₀ j
  set A := (∑ i : Fin (p n), ‖x (i, j) ω‖ ^ 2) / p n
  have hA : |A - m| ≤ δ := hn j
  have hAbs : |A| ≤ |m| + 1 := by
    have := abs_sub_abs_le_abs_sub A m
    linarith [min_le_left 1 (ε / (2 * y))]
  have hsplit : (∑ i : Fin (p n), ‖x (i, j) ω‖ ^ 2) / n - y * m =
      ((p n : ℝ) / n - y) * A + y * (A - m) := by
    have : (p n : ℝ) ≠ 0 := by exact_mod_cast hp₀.ne'
    simp only [A]
    field_simp
    ring
  rw [hsplit]
  calc
    _ ≤ |(p n : ℝ) / n - y| * |A| + y * |A - m| := by
      refine (abs_add_le _ _).trans_eq ?_
      rw [abs_mul, abs_mul, abs_of_pos hy]
    _ ≤ ε / (2 * (|m| + 1)) * (|m| + 1) + y * (ε / (2 * y)) := by
      gcongr
      · exact (Real.dist_eq _ _ ▸ hpn).le
      · exact hA.trans (min_le_right _ _)
    _ = ε := by field_simp; ring

end Norms

end TauCeti.Probability.SampleCovariance
