/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Complex.Schwarz
import TauCeti.Analysis.Normed.Group.Basic

/-!
# Quadrature error for kernel-weighted holomorphic integrals

Given a scalar kernel `κ : V → ℂ` and a Banach-valued holomorphic map `f : V → E` on a ball
`ball ζ r` in a complex normed space `V`, approximating the cell integral `∫ y in A, κ y • f y ∂μ`
over a finite-measure subset `A ⊆ ball ζ δ` (`δ ≤ r`) by the one-point value
`μ.real A • (κ ζ • f ζ)` incurs an error controlled by the oscillation of `κ` on `A` and the
supremum of `‖f‖` on `ball ζ r` (`TauCeti.norm_setIntegral_smul_sub_measureReal_smul_le`).

Summing this cell bound across a measurable small-ball partition turns integral representations of
holomorphic functions (such as the Cauchy or Cauchy–Pompeiu formulas) into uniform finite-rank
point-evaluation approximations, as in `TauCeti/Analysis/Complex/Runge/Operator.lean`.

## Main results

* `TauCeti.norm_setIntegral_smul_sub_measureReal_smul_le`: if `A ⊆ ball ζ δ` has finite measure
  with `δ ≤ r`, `‖κ y - κ ζ‖ ≤ ε` on `A`, and `f` is holomorphic and bounded in norm by `B` on
  `ball ζ r`, then
  `‖(∫ y in A, κ y • f y ∂μ) - μ.real A • (κ ζ • f ζ)‖ ≤ μ.real A * ((ε + 2 * ‖κ ζ‖ * δ / r) * B)`.
* `TauCeti.norm_setIntegral_smul_sub_sum_measureReal_smul_le`: summing the single-cell bound across
  a finite measurable partition `⋃ j, A j = s` with `A j ⊆ ball (ζ j) δ` (`δ ≤ r`) and
  `‖κ (ζ j)‖ ≤ M` bounds
  `‖(∫ y in s, κ y • f y ∂μ) - ∑ j, μ.real (A j) • (κ (ζ j) • f (ζ j))‖` by
  `μ.real s * ((ε + 2 * M * δ / r) * B)`.
-/

public section

open Function MeasureTheory Metric Set
open scoped ENNReal

namespace TauCeti

/-- **One-point quadrature error for a kernel-weighted holomorphic map.** If `A ⊆ ball ζ δ` has
finite measure with `δ ≤ r`, `κ` varies by at most `ε` from `κ ζ` on `A`, and `f` is holomorphic
and bounded in norm by `B` on `ball ζ r`, then replacing `∫ y in A, κ y • f y ∂μ` by
`μ.real A • (κ ζ • f ζ)` incurs error at most `μ.real A * ((ε + 2 * ‖κ ζ‖ * δ / r) * B)`. -/
theorem norm_setIntegral_smul_sub_measureReal_smul_le
    {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [MeasurableSpace V]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {μ : Measure V} {A : Set V} {κ : V → ℂ} {f : V → E} {ζ : V} {δ r ε B : ℝ}
    (hA : μ A < ∞) (hA_ball : A ⊆ ball ζ δ) (hδr : δ ≤ r)
    (hint : IntegrableOn (fun y ↦ κ y • f y) A μ)
    (hκ : ∀ y ∈ A, ‖κ y - κ ζ‖ ≤ ε)
    (hf : DifferentiableOn ℂ f (ball ζ r))
    (hfB : ∀ u ∈ ball ζ r, ‖f u‖ ≤ B) :
    ‖(∫ y in A, κ y • f y ∂μ) - μ.real A • (κ ζ • f ζ)‖ ≤
      μ.real A * ((ε + 2 * ‖κ ζ‖ * δ / r) * B) := by
  rw [← setIntegral_const, ← integral_sub hint (integrableOn_const hA.ne), mul_comm (μ.real A)]
  refine norm_setIntegral_le_of_norm_le_const hA fun y hy ↦ ?_
  have hy_δ : y ∈ ball ζ δ := hA_ball hy
  have hy_r : y ∈ ball ζ r := ball_subset_ball hδr hy_δ
  have hr : 0 < r := nonempty_ball.mp ⟨y, hy_r⟩
  have hfyB : ‖f y‖ ≤ B := hfB y hy_r
  have hB : 0 ≤ B := (norm_nonneg _).trans hfyB
  have hf_diff : ‖f y - f ζ‖ ≤ 2 * B / r * δ := by
    have hsch := Complex.dist_le_div_mul_dist_of_mapsTo_ball hf
      (mapsTo_closedBall_of_forall_norm_le hfB (mem_ball_self hr)) hy_r
    rw [dist_eq_norm] at hsch
    exact hsch.trans (mul_le_mul_of_nonneg_left (mem_ball.mp hy_δ).le (by positivity))
  have hsplit : κ y • f y - κ ζ • f ζ = (κ y - κ ζ) • f y + κ ζ • (f y - f ζ) := by
    rw [sub_smul, smul_sub, sub_add_sub_cancel]
  calc ‖κ y • f y - κ ζ • f ζ‖
      = ‖(κ y - κ ζ) • f y + κ ζ • (f y - f ζ)‖ := by rw [hsplit]
    _ ≤ ‖(κ y - κ ζ) • f y‖ + ‖κ ζ • (f y - f ζ)‖ := norm_add_le _ _
    _ = ‖κ y - κ ζ‖ * ‖f y‖ + ‖κ ζ‖ * ‖f y - f ζ‖ := by rw [norm_smul, norm_smul]
    _ ≤ ε * B + ‖κ ζ‖ * (2 * B / r * δ) :=
        add_le_add (mul_le_mul (hκ y hy) hfyB (norm_nonneg _) ((norm_nonneg _).trans (hκ y hy)))
          (mul_le_mul_of_nonneg_left hf_diff (norm_nonneg _))
    _ = (ε + 2 * ‖κ ζ‖ * δ / r) * B := by ring

/-- **Partition quadrature error for a kernel-weighted holomorphic map.** For a finite measurable
partition `⋃ j, A j = s` of a finite-measure set `s` with each cell `A j ⊆ ball (ζ j) δ` (`δ ≤ r`),
if `κ` varies by at most `ε` from `κ (ζ j)` on `A j`, `‖κ (ζ j)‖ ≤ M`, and `f` is holomorphic and
bounded in norm by `B` on each `ball (ζ j) r`, then replacing `∫ y in s, κ y • f y ∂μ` by
`∑ j, μ.real (A j) • (κ (ζ j) • f (ζ j))` incurs error at most
`μ.real s * ((ε + 2 * M * δ / r) * B)`. -/
theorem norm_setIntegral_smul_sub_sum_measureReal_smul_le
    {ι V E : Type*} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℂ V] [MeasurableSpace V]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {μ : Measure V} {s : Set V} {A : ι → Set V} {ζ : ι → V}
    {κ : V → ℂ} {f : V → E} {δ r ε M B : ℝ}
    (hs : μ s < ∞) (hAm : ∀ j, MeasurableSet (A j))
    (hAdisj : Pairwise (Disjoint on A)) (hAunion : ⋃ j, A j = s)
    (hA_ball : ∀ j, A j ⊆ ball (ζ j) δ) (hδr : δ ≤ r)
    (hint : IntegrableOn (fun y ↦ κ y • f y) s μ)
    (hκ : ∀ j, ∀ y ∈ A j, ‖κ y - κ (ζ j)‖ ≤ ε)
    (hκM : ∀ j, ‖κ (ζ j)‖ ≤ M)
    (hf : ∀ j, DifferentiableOn ℂ f (ball (ζ j) r))
    (hfB : ∀ j, ∀ u ∈ ball (ζ j) r, ‖f u‖ ≤ B) :
    ‖(∫ y in s, κ y • f y ∂μ) - ∑ j, μ.real (A j) • (κ (ζ j) • f (ζ j))‖ ≤
      μ.real s * ((ε + 2 * M * δ / r) * B) := by
  have hAs : ∀ j, A j ⊆ s := fun j ↦ hAunion ▸ subset_iUnion A j
  have hcell : ∀ j,
      ‖(∫ y in A j, κ y • f y ∂μ) - μ.real (A j) • (κ (ζ j) • f (ζ j))‖ ≤
        μ.real (A j) * ((ε + 2 * M * δ / r) * B) := fun j ↦ by
    rcases (A j).eq_empty_or_nonempty with hAj | ⟨y₀, hy₀⟩
    · simp [hAj]
    have hy₀_δ : y₀ ∈ ball (ζ j) δ := hA_ball j hy₀
    have hδ0 : 0 < δ := nonempty_ball.mp ⟨y₀, hy₀_δ⟩
    have hr0 : 0 < r := hδ0.trans_le hδr
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hfB j y₀ (ball_subset_ball hδr hy₀_δ))
    refine (norm_setIntegral_smul_sub_measureReal_smul_le
      ((measure_mono (hAs j)).trans_lt hs) (hA_ball j) hδr (hint.mono_set (hAs j))
      (hκ j) (hf j) (hfB j)).trans ?_
    have hM : ‖κ (ζ j)‖ ≤ M := hκM j
    gcongr
  rw [← hAunion, integral_iUnion_fintype hAm hAdisj (fun j ↦ hint.mono_set (hAs j)),
    ← Finset.sum_sub_distrib]
  calc ‖∑ j, ((∫ y in A j, κ y • f y ∂μ) - μ.real (A j) • (κ (ζ j) • f (ζ j)))‖
      ≤ ∑ j, ‖(∫ y in A j, κ y • f y ∂μ) - μ.real (A j) • (κ (ζ j) • f (ζ j))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ j, μ.real (A j) * ((ε + 2 * M * δ / r) * B) :=
        Finset.sum_le_sum fun j _ ↦ hcell j
    _ = (∑ j, μ.real (A j)) * ((ε + 2 * M * δ / r) * B) := (Finset.sum_mul _ _ _).symm
    _ = μ.real (⋃ j, A j) * ((ε + 2 * M * δ / r) * B) := by
        rw [measureReal_iUnion_fintype hAdisj hAm fun j ↦ ((measure_mono (hAs j)).trans_lt hs).ne]

end TauCeti
