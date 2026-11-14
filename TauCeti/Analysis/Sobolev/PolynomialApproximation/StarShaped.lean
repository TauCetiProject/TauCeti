/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.Analysis.Convex.Topology
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

/-!
# Domains star-shaped with respect to a ball and normalized ball cutoffs

A domain `Ω` in a real normed space `E` is star-shaped with respect to a ball `B = Metric.ball x₀ ρ`
when `∀ y ∈ Metric.ball x₀ ρ, StarConvex ℝ y Ω` (Brenner–Scott, Definition 4.2.2). Every segment
from a center `y` in the concentric closed ball `Metric.closedBall x₀ r` (`r < ρ`) to any `x ∈ Ω`
lies in `Ω`, and in a proper space the entire closed cone
`closure (convexHull ℝ (insert x (Metric.closedBall x₀ r)))` stays inside `Ω`
(`TauCeti.closure_convexHull_insert_closedBall_subset_of_forall_starConvex`,
`TauCeti.closure_convexHull_insert_ball_subset_of_forall_starConvex`).

To average Taylor polynomials over `B`, `TauCeti.ballCutoff μ x₀ hρ` normalizes a radial smooth bump
`TauCeti.ballBump x₀ hρ` with inner radius `ρ / 4` and outer radius `ρ / 2`: it is smooth,
nonnegative, radially symmetric around `x₀`, has topological support
`Metric.closedBall x₀ (ρ / 2) ⊆ Metric.ball x₀ ρ`, integrates to `1` with respect to `μ`, and on a
finite-dimensional Haar space satisfies the scale-sharp pointwise bound
`‖ballCutoff μ x₀ hρ y‖ ≤ C * ρ ^ (-finrank ℝ E)` with an explicit dimension-and-Haar constant `C`
independent of `x₀` and `ρ` (`TauCeti.norm_ballCutoff_le`).

## Main definitions

* `TauCeti.ballBump`: smooth bump at `x₀` with `rIn = ρ / 4` and `rOut = ρ / 2`.
* `TauCeti.ballCutoff`: `ballBump` normalized so that `∫ y, ballCutoff μ x₀ hρ y ∂μ = 1`.

## Main results

* `TauCeti.closure_convexHull_insert_ball_subset_of_forall_starConvex`: for `r < ρ` and `x ∈ Ω`,
  the closed convex hull of `insert x (Metric.ball x₀ r)` lies in `Ω`.
* `TauCeti.tsupport_ballCutoff`, `TauCeti.integral_ballCutoff`, `TauCeti.setIntegral_ballCutoff`,
  `TauCeti.setIntegral_ballCutoff_halfSpace`: support, unit-mass, and half-space symmetry properties
  of `ballCutoff`.
* `TauCeti.norm_ballCutoff_le`, `TauCeti.exists_norm_ballCutoff_le`: `O(ρ ^ (-finrank ℝ E))`
  pointwise bound on `ballCutoff` with respect to an additive Haar measure.

## References

* Susanne C. Brenner and L. Ridgway Scott, *The Mathematical Theory of Finite Element Methods*,
  3rd ed., Springer (2008), Chapter 4, §§4.1–4.2.
-/

public section

noncomputable section

open MeasureTheory Metric Module Set
open scoped ContDiff Topology

namespace TauCeti

section StarShaped

/-- If `Ω` is star-shaped with respect to every point of `Metric.ball x₀ ρ`, then for any `r < ρ`,
any `x ∈ Ω`, and any `y ∈ Metric.closedBall x₀ r`, the closed segment from `y` to `x` lies in
`Ω`. -/
theorem add_smul_sub_mem_of_mem_closedBall_of_forall_starConvex
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set E} {x y x₀ : E} {r ρ t : ℝ} (hr : r < ρ) (hx : x ∈ Ω)
    (hy : y ∈ closedBall x₀ r) (ht : t ∈ Icc (0 : ℝ) 1)
    (hstar : ∀ z ∈ ball x₀ ρ, StarConvex ℝ z Ω) :
    y + t • (x - y) ∈ Ω :=
  (hstar y (closedBall_subset_ball hr hy)).add_smul_sub_mem hx ht.1 ht.2

/-- In a proper real normed space, if `Ω` is star-shaped with respect to every point of
`Metric.ball x₀ ρ`, then for every `x ∈ Ω` and `r < ρ` the closed convex hull of
`insert x (Metric.closedBall x₀ r)` is contained in `Ω`. -/
theorem closure_convexHull_insert_closedBall_subset_of_forall_starConvex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {Ω : Set E} {x x₀ : E} {r ρ : ℝ} (hr : r < ρ) (hx : x ∈ Ω)
    (hstar : ∀ y ∈ ball x₀ ρ, StarConvex ℝ y Ω) :
    closure (convexHull ℝ (insert x (closedBall x₀ r))) ⊆ Ω :=
  (isCompact_closedBall x₀ r).closure_convexHull_insert_subset_of_forall_starConvex
    (convex_closedBall x₀ r) Subset.rfl hx fun y hy ↦ hstar y (closedBall_subset_ball hr hy)

/-- In a proper real normed space, if `Ω` is star-shaped with respect to every point of
`Metric.ball x₀ ρ`, then for every `x ∈ Ω` and `r < ρ` the closed convex hull of
`insert x (Metric.ball x₀ r)` is contained in `Ω`. -/
theorem closure_convexHull_insert_ball_subset_of_forall_starConvex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {Ω : Set E} {x x₀ : E} {r ρ : ℝ} (hr : r < ρ) (hx : x ∈ Ω)
    (hstar : ∀ y ∈ ball x₀ ρ, StarConvex ℝ y Ω) :
    closure (convexHull ℝ (insert x (ball x₀ r))) ⊆ Ω :=
  (isCompact_closedBall x₀ r).closure_convexHull_insert_subset_of_forall_starConvex
    (convex_closedBall x₀ r) ball_subset_closedBall hx
    fun y hy ↦ hstar y (closedBall_subset_ball hr hy)

end StarShaped

section BallCutoff

/-- Smooth radial bump parameters centered at `x₀` with inner radius `ρ / 4` and outer radius
`ρ / 2`, so `Metric.closedBall x₀ (ρ / 2)` sits strictly inside `Metric.ball x₀ ρ`. -/
def ballBump {E : Type*} (x₀ : E) {ρ : ℝ} (hρ : 0 < ρ) : ContDiffBump x₀ :=
  ⟨ρ / 4, ρ / 2, by positivity, by linarith⟩

@[simp]
theorem ballBump_rIn {E : Type*} (x₀ : E) {ρ : ℝ} (hρ : 0 < ρ) :
    (ballBump x₀ hρ).rIn = ρ / 4 :=
  (rfl)

@[simp]
theorem ballBump_rOut {E : Type*} (x₀ : E) {ρ : ℝ} (hρ : 0 < ρ) :
    (ballBump x₀ hρ).rOut = ρ / 2 :=
  (rfl)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]
  [MeasurableSpace E] (μ : Measure E)

/-- Smooth cutoff supported in `Metric.closedBall x₀ (ρ / 2) ⊆ Metric.ball x₀ ρ` and normalized to
have unit integral with respect to `μ`. -/
def ballCutoff (x₀ : E) {ρ : ℝ} (hρ : 0 < ρ) : E → ℝ :=
  (ballBump x₀ hρ).normed μ

theorem ballCutoff_def (x₀ : E) {ρ : ℝ} (hρ : 0 < ρ) :
    ballCutoff μ x₀ hρ = (ballBump x₀ hρ).normed μ :=
  (rfl)

theorem nonneg_ballCutoff (x₀ : E) {ρ : ℝ} (hρ : 0 < ρ) (y : E) :
    0 ≤ ballCutoff μ x₀ hρ y :=
  (ballBump x₀ hρ).nonneg_normed y

theorem contDiff_ballCutoff (x₀ : E) {ρ : ℝ} (hρ : 0 < ρ) {n : ℕ∞} :
    ContDiff ℝ n (ballCutoff μ x₀ hρ) :=
  (ballBump x₀ hρ).contDiff_normed

theorem continuous_ballCutoff (x₀ : E) {ρ : ℝ} (hρ : 0 < ρ) :
    Continuous (ballCutoff μ x₀ hρ) :=
  (ballBump x₀ hρ).continuous_normed

/-- `ballCutoff` is symmetric under reflection through its center `x₀`. -/
theorem ballCutoff_sub (x₀ : E) {ρ : ℝ} (hρ : 0 < ρ) (v : E) :
    ballCutoff μ x₀ hρ (x₀ - v) = ballCutoff μ x₀ hρ (x₀ + v) :=
  (ballBump x₀ hρ).normed_sub v

/-- Centered at the origin, `ballCutoff` is an even function. -/
@[simp]
theorem ballCutoff_neg {ρ : ℝ} (hρ : 0 < ρ) (v : E) :
    ballCutoff μ (0 : E) hρ (-v) = ballCutoff μ (0 : E) hρ v :=
  (ballBump (0 : E) hρ).normed_neg v

section LocallyFinite

variable [BorelSpace E] [FiniteDimensional ℝ E] [IsLocallyFiniteMeasure μ]

theorem integrable_ballCutoff (x₀ : E) {ρ : ℝ} (hρ : 0 < ρ) :
    Integrable (ballCutoff μ x₀ hρ) μ :=
  (ballBump x₀ hρ).integrable_normed

variable [μ.IsOpenPosMeasure]

@[simp]
theorem support_ballCutoff (x₀ : E) {ρ : ℝ} (hρ : 0 < ρ) :
    Function.support (ballCutoff μ x₀ hρ) = ball x₀ (ρ / 2) :=
  (ballBump x₀ hρ).support_normed_eq

@[simp]
theorem tsupport_ballCutoff (x₀ : E) {ρ : ℝ} (hρ : 0 < ρ) :
    tsupport (ballCutoff μ x₀ hρ) = closedBall x₀ (ρ / 2) :=
  (ballBump x₀ hρ).tsupport_normed_eq

theorem tsupport_ballCutoff_subset_ball (x₀ : E) {ρ : ℝ} (hρ : 0 < ρ) :
    tsupport (ballCutoff μ x₀ hρ) ⊆ ball x₀ ρ := by
  rw [tsupport_ballCutoff]
  exact closedBall_subset_ball (half_lt_self hρ)

theorem hasCompactSupport_ballCutoff (x₀ : E) {ρ : ℝ} (hρ : 0 < ρ) :
    HasCompactSupport (ballCutoff μ x₀ hρ) :=
  (ballBump x₀ hρ).hasCompactSupport_normed

@[simp]
theorem integral_ballCutoff (x₀ : E) {ρ : ℝ} (hρ : 0 < ρ) :
    ∫ y, ballCutoff μ x₀ hρ y ∂μ = 1 :=
  (ballBump x₀ hρ).integral_normed

/-- Integrating `ballCutoff μ x₀ hρ` over any set `s` containing `Metric.closedBall x₀ (ρ / 2)`
gives `1`. -/
theorem setIntegral_ballCutoff (x₀ : E) {ρ : ℝ} (hρ : 0 < ρ) {s : Set E}
    (hs : closedBall x₀ (ρ / 2) ⊆ s) :
    ∫ y in s, ballCutoff μ x₀ hρ y ∂μ = 1 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact integral_ballCutoff μ x₀ hρ
  · intro y hys
    have hy : y ∉ tsupport (ballCutoff μ x₀ hρ) := by
      rw [tsupport_ballCutoff]
      exact fun h ↦ hys (hs h)
    exact image_eq_zero_of_notMem_tsupport hy

end LocallyFinite

section AddHaar

variable [BorelSpace E] [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure]

/-- Explicit `O(ρ ^ (-finrank ℝ E))` pointwise bound on `ballCutoff` with respect to an additive
Haar measure `μ`, uniform in the center `x₀`, radius `ρ > 0`, and evaluation point `y`. -/
theorem norm_ballCutoff_le (x₀ : E) {ρ : ℝ} (hρ : 0 < ρ) (y : E) :
    ‖ballCutoff μ x₀ hρ y‖ ≤
      (4 ^ finrank ℝ E / μ.real (closedBall (0 : E) 1)) * ρ ^ (-(finrank ℝ E : ℝ)) := by
  rw [Real.norm_of_nonneg (nonneg_ballCutoff μ x₀ hρ y)]
  have hle := (ballBump x₀ hρ).normed_le_div_measure_closedBall_rOut μ 2
    (by simp; linarith) y
  rw [ballBump_rOut, Measure.addHaar_real_closedBall' μ x₀ (by positivity)] at hle
  refine hle.trans (le_of_eq ?_)
  have hpow : (2 : ℝ) ^ finrank ℝ E * 2 ^ finrank ℝ E = 4 ^ finrank ℝ E := by
    rw [← mul_pow]
    norm_num
  rw [Real.rpow_neg hρ.le, Real.rpow_natCast, div_pow, div_mul_eq_mul_div, div_div_eq_mul_div,
    hpow]
  ring

/-- Existential form of `norm_ballCutoff_le`: there is a nonnegative constant `C`, depending only on
the ambient space and Haar measure `μ`, such that
`‖ballCutoff μ x₀ hρ y‖ ≤ C * ρ ^ (-finrank ℝ E)`. -/
theorem exists_norm_ballCutoff_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x₀ : E) {ρ : ℝ} (hρ : 0 < ρ) (y : E),
      ‖ballCutoff μ x₀ hρ y‖ ≤ C * ρ ^ (-(finrank ℝ E : ℝ)) :=
  ⟨4 ^ finrank ℝ E / μ.real (closedBall (0 : E) 1), by positivity, norm_ballCutoff_le μ⟩

/-- By radial symmetry around `0` and Haar nullity of proper hyperplanes, integrating
`ballCutoff μ 0 hρ` over the closed half-space `{y : E | 0 ≤ L y}` defined by any nonzero continuous
linear functional `L : E →L[ℝ] ℝ` yields `1 / 2`. -/
theorem setIntegral_ballCutoff_halfSpace {ρ : ℝ} (hρ : 0 < ρ) {L : E →L[ℝ] ℝ} (hL : L ≠ 0) :
    ∫ y in {y : E | 0 ≤ L y}, ballCutoff μ 0 hρ y ∂μ = (1 : ℝ) / 2 := by
  set φ := ballCutoff μ (0 : E) hρ
  let P : Set E := {y | 0 ≤ L y}
  let N : Set E := {y | L y < 0}
  let Ppos : Set E := {y | 0 < L y}
  let Z : Submodule ℝ E := LinearMap.ker L.toLinearMap
  have hNm : MeasurableSet N := (isOpen_lt L.continuous continuous_const).measurableSet
  have hZm : MeasurableSet (Z : Set E) := (isClosed_eq L.continuous continuous_const).measurableSet
  have hPpos_m : MeasurableSet Ppos := (isOpen_lt continuous_const L.continuous).measurableSet
  have hZ_ne_top : Z ≠ ⊤ := by
    obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp hL
    intro htop
    have hvZ : v ∈ Z := htop ▸ Submodule.mem_top
    exact hv hvZ
  have hZ_null : μ (Z : Set E) = 0 := Measure.addHaar_submodule μ Z hZ_ne_top
  have hsum : ∫ y in P, φ y ∂μ + ∫ y in N, φ y ∂μ = 1 := by
    have hdisj : Disjoint P N :=
      Set.disjoint_left.mpr fun y (hyP : 0 ≤ L y) (hyN : L y < 0) ↦ not_lt_of_ge hyP hyN
    have hunion : P ∪ N = univ := by
      ext y
      simp [P, N, le_or_gt]
    rw [← setIntegral_union hdisj hNm (integrable_ballCutoff μ 0 hρ).integrableOn
      (integrable_ballCutoff μ 0 hρ).integrableOn, hunion, setIntegral_univ]
    exact integral_ballCutoff μ 0 hρ
  have heq_PN : ∫ y in P, φ y ∂μ = ∫ y in N, φ y ∂μ := by
    have hP_diff : P = Ppos ∪ (Z : Set E) := by
      ext y
      simp [P, Ppos, Z, le_iff_lt_or_eq, eq_comm]
    have hdisjZ : Disjoint Ppos (Z : Set E) :=
      Set.disjoint_left.mpr fun y (hy1 : 0 < L y) (hy2 : L y = 0) ↦ hy1.ne' hy2
    rw [hP_diff, setIntegral_union hdisjZ hZm (integrable_ballCutoff μ 0 hρ).integrableOn
      (integrable_ballCutoff μ 0 hρ).integrableOn, setIntegral_measure_zero _ hZ_null, add_zero,
      ← integral_indicator hPpos_m, ← integral_indicator hNm]
    conv_lhs => rw [← integral_neg_eq_self]
    congr 1
    ext y
    by_cases hy : L y < 0
    · have h1 : -y ∈ Ppos := by simpa [Ppos] using hy
      have h2 : y ∈ N := hy
      simp [h1, h2, φ]
    · have h1 : -y ∉ Ppos := by simpa [Ppos] using hy
      have h2 : y ∉ N := hy
      simp [h1, h2]
  linarith

end AddHaar

end BallCutoff

end TauCeti
