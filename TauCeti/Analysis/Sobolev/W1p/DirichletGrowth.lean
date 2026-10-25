/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.W1p
public import TauCeti.MeasureTheory.Function.Campanato
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.Topology.MetricSpace.Holder.Basic

/-!
# Morrey's Dirichlet growth theorem

Let `u ∈ W^{1,p}(Ω)`, `1 ≤ p`, on an open subset `Ω` of a finite-dimensional real inner product
space of dimension `n`, and let `0 < α`. **Morrey's Dirichlet growth theorem** says that if the
gradient of `u` grows on balls like

`∫_{B(x, r)} ‖∇u‖ ≤ M r^(n - 1 + α)`,

then `u` is `α`-Hölder continuous, with Hölder constant a multiple of `M` depending only on `n`,
`α` and `μ(B(0, 1))`. More precisely the Hölder continuous function is the precise representative
`TauCeti.MeasureTheory.preciseRepresentative` of `u`, the limit of its averages over shrinking
balls, which agrees with `u` almost everywhere on `Ω` by
`TauCeti.W1p.ae_eq_preciseRepresentative`.

This is the form in which energy estimates deliver Hölder regularity. A Caccioppoli inequality
together with a comparison argument typically bounds `∫_{B(x, r)} ‖∇u‖²` by `r^(n - 2 + 2α)`; by
the Cauchy–Schwarz inequality on the ball this gives the growth condition above. In the
Campanato approach to the Schauder estimates the same theorem, applied to the derivatives of a
solution, gives Hölder continuity of the gradient.

The proof combines two results. The Poincaré–Wirtinger inequality on balls
(`TauCeti.W1p.setIntegral_abs_value_sub_setAverage_le_of_ball_subset`) bounds the mean
oscillation of `u` on a ball of radius `r` by `2^(n + 1) r` times the average of `‖∇u‖` over the
ball, so the growth condition makes the mean oscillation `O(r^α)`. Campanato's theorem
(`TauCeti.MeasureTheory.dist_preciseRepresentative_le_of_setAverage_norm_sub_le`) turns such a
bound into a Hölder estimate for the precise representative.

The growth condition only needs to hold for balls centred at the points under consideration and
for radii up to a multiple of their distance, so the theorem applies to interior estimates.

## Main declarations

* `TauCeti.W1p.setAverage_norm_value_sub_setAverage_closedBall_le`: the mean oscillation of `u` on
  `closedBall x r` is at most `2^(n + 1) r` times the average of `‖∇u‖` over `ball x r`.
* `TauCeti.W1p.dist_preciseRepresentative_le_of_setIntegral_norm_gradient_le`: the pointwise
  Hölder estimate between two points.
* `TauCeti.W1p.holderOnWith_preciseRepresentative_of_setIntegral_norm_gradient_le`: **Morrey's
  Dirichlet growth theorem** on a subset of `Ω`.
* `TauCeti.W1p.holderWith_preciseRepresentative_of_setIntegral_norm_gradient_le`: the same on the
  whole space.

## References

* C. B. Morrey, *Multiple Integrals in the Calculus of Variations*, Theorem 3.5.2.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 7.19.
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, Theorem 5.7.
-/

public section

noncomputable section

open Metric Set MeasureTheory Module TopologicalSpace TauCeti.MeasureTheory
open scoped ENNReal NNReal

namespace TauCeti

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Poincaré's inequality for the mean oscillation on a closed ball.** If `u ∈ W^{1,p}(Ω)` and
`B(x, r) ⊆ Ω`, the mean oscillation `⨍_{closedBall x r} |u - u_{x,r}|` of `u` is at most
`2^(n + 1) r` times the average of `‖∇u‖` over `B(x, r)`. -/
theorem W1p.setAverage_norm_value_sub_setAverage_closedBall_le {x : E} {r : ℝ} (hr : 0 < r)
    (hball : ball x r ⊆ (Omega : Set E)) (u : W1p mu Omega p) :
    ⨍ y in closedBall x r, ‖W1p.value u y - ⨍ z in closedBall x r, W1p.value u z ∂mu‖ ∂mu ≤
      2 ^ (finrank ℝ E + 1) * r * ⨍ y in ball x r, ‖W1p.gradient u y‖ ∂mu := by
  rw [Measure.restrict_congr_set (mu.addHaar_closedBall_ae_eq_ball_of_ne_zero x r hr.ne')]
  set m := ⨍ z in ball x r, W1p.value u z ∂mu
  rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul, mul_left_comm]
  simp_rw [Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (W1p.setIntegral_abs_value_sub_setAverage_le_of_ball_subset hr hball u)
    (inv_nonneg.2 measureReal_nonneg)

/-- The growth condition `∫_{B(x, r)} ‖∇u‖ ≤ M r^(n - 1 + α)` makes the mean oscillation of `u`
on `closedBall x r` at most `2^(n + 1) / ω · M r^α`, where `ω` is the measure of the unit
ball. -/
private theorem setAverage_norm_value_sub_setAverage_closedBall_le_of_setIntegral_le
    {x : E} {r α M : ℝ} (hr : 0 < r) (hball : ball x r ⊆ (Omega : Set E)) (u : W1p mu Omega p)
    (hgrowth : ∫ y in ball x r, ‖W1p.gradient u y‖ ∂mu ≤ M * r ^ ((finrank ℝ E : ℝ) - 1 + α)) :
    ⨍ y in closedBall x r, ‖W1p.value u y - ⨍ z in closedBall x r, W1p.value u z ∂mu‖ ∂mu ≤
      2 ^ (finrank ℝ E + 1) / mu.real (ball (0 : E) 1) * M * r ^ α := by
  have hω : 0 < mu.real (ball (0 : E) 1) :=
    ENNReal.toReal_pos (measure_ball_pos mu 0 one_pos).ne' measure_ball_lt_top.ne
  -- The measure of `B(x, r)` is `r^n ω`.
  have hmeas : mu.real (ball x r) = r ^ finrank ℝ E * mu.real (ball (0 : E) 1) :=
    mu.addHaar_real_ball_of_pos x hr
  have hpow : r * r ^ ((finrank ℝ E : ℝ) - 1 + α) = r ^ finrank ℝ E * r ^ α := by
    calc r * r ^ ((finrank ℝ E : ℝ) - 1 + α) = r ^ (1 : ℝ) * r ^ ((finrank ℝ E : ℝ) - 1 + α) := by
          rw [Real.rpow_one]
      _ = r ^ ((finrank ℝ E : ℝ) + α) := by rw [← Real.rpow_add hr]; ring_nf
      _ = r ^ finrank ℝ E * r ^ α := by rw [Real.rpow_add hr, Real.rpow_natCast]
  refine (W1p.setAverage_norm_value_sub_setAverage_closedBall_le hr hball u).trans ?_
  rw [setAverage_eq, smul_eq_mul, hmeas]
  calc 2 ^ (finrank ℝ E + 1) * r *
        ((r ^ finrank ℝ E * mu.real (ball (0 : E) 1))⁻¹ * ∫ y in ball x r, ‖W1p.gradient u y‖ ∂mu)
      ≤ 2 ^ (finrank ℝ E + 1) * r *
          ((r ^ finrank ℝ E * mu.real (ball (0 : E) 1))⁻¹ *
            (M * r ^ ((finrank ℝ E : ℝ) - 1 + α))) := by gcongr
    _ = 2 ^ (finrank ℝ E + 1) * ((r ^ finrank ℝ E * mu.real (ball (0 : E) 1))⁻¹ *
          (M * (r * r ^ ((finrank ℝ E : ℝ) - 1 + α)))) := by ring
    _ = 2 ^ (finrank ℝ E + 1) / mu.real (ball (0 : E) 1) * M * r ^ α := by
        rw [hpow]
        field_simp

/-- **The pointwise Morrey estimate.** Let `u ∈ W^{1,p}(Ω)`, `α > 0`, `d = dist x y`, and
suppose that `closedBall x (2 d) ⊆ Ω` and that the gradient of `u` satisfies the growth condition
`∫_{B(z, r)} ‖∇u‖ ≤ M r^(n - 1 + α)` for `z = x`, `0 < r ≤ 2 d` and for `z = y`, `0 < r ≤ d`.
Then the precise representative `u*` of `u` satisfies

`|u*(x) - u*(y)| ≤ 2 · 2^α · 2ⁿ / (1 - 2^(-α)) · 2^(n + 1) / ω · M d^α`,

where `ω` is the measure of the unit ball. -/
theorem W1p.dist_preciseRepresentative_le_of_setIntegral_norm_gradient_le {α M : ℝ}
    (hα : 0 < α) (u : W1p mu Omega p) {x y : E}
    (hxy : closedBall x (2 * dist x y) ⊆ (Omega : Set E))
    (hx : ∀ r, 0 < r → r ≤ 2 * dist x y →
      ∫ z in ball x r, ‖W1p.gradient u z‖ ∂mu ≤ M * r ^ ((finrank ℝ E : ℝ) - 1 + α))
    (hy : ∀ r, 0 < r → r ≤ dist x y →
      ∫ z in ball y r, ‖W1p.gradient u z‖ ∂mu ≤ M * r ^ ((finrank ℝ E : ℝ) - 1 + α)) :
    dist (preciseRepresentative mu (W1p.value u) x) (preciseRepresentative mu (W1p.value u) y) ≤
      2 * 2 ^ α * (2 ^ finrank ℝ E / (1 - 2 ^ (-α))) *
        (2 ^ (finrank ℝ E + 1) / mu.real (ball (0 : E) 1) * M * dist x y ^ α) := by
  have : IsFiniteMeasure (mu.restrict (closedBall x (2 * dist x y))) :=
    isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
  have hint : IntegrableOn (W1p.value u) (closedBall x (2 * dist x y)) mu :=
    ((Lp.memLp (W1p.value u)).mono_measure (Measure.restrict_mono hxy le_rfl)).integrable
      Fact.out
  -- `closedBall y d ⊆ closedBall x (2 d)`.
  have hyx : closedBall y (dist x y) ⊆ closedBall x (2 * dist x y) := fun z hz ↦ by
    rw [mem_closedBall] at hz ⊢
    linarith [dist_triangle z y x, dist_comm x y]
  have hball : ∀ z r, closedBall z r ⊆ closedBall x (2 * dist x y) →
      ball z r ⊆ (Omega : Set E) := fun z r h ↦ (ball_subset_closedBall.trans h).trans hxy
  refine dist_preciseRepresentative_le_of_setAverage_norm_sub_le hα hint (fun r hr hr' ↦ ?_)
    (fun r hr hr' ↦ ?_)
  · exact setAverage_norm_value_sub_setAverage_closedBall_le_of_setIntegral_le hr
      (hball x r (closedBall_subset_closedBall hr')) u (hx r hr hr')
  · exact setAverage_norm_value_sub_setAverage_closedBall_le_of_setIntegral_le hr
      (hball y r ((closedBall_subset_closedBall hr').trans hyx)) u (hy r hr hr')

/-- **Morrey's Dirichlet growth theorem.** Let `u ∈ W^{1,p}(Ω)` and `α > 0`, and let `K` be a set
of diameter at most `R` whose closed `2R`-thickening lies in `Ω`. If the gradient of `u`
satisfies the growth condition

`∫_{B(x, r)} ‖∇u‖ ≤ M r^(n - 1 + α)` for every `x ∈ K` and `0 < r ≤ 2R`,

then the precise representative of `u` is `α`-Hölder continuous on `K`, with Hölder constant
`2 · 2^α · 2ⁿ / (1 - 2^(-α)) · 2^(n + 1) / ω · M`, where `ω` is the measure of the unit ball. -/
theorem W1p.holderOnWith_preciseRepresentative_of_setIntegral_norm_gradient_le {α : ℝ≥0}
    (hα : 0 < α) {M R : ℝ} (u : W1p mu Omega p) {K : Set E}
    (hKR : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ R) (hK : cthickening (2 * R) K ⊆ (Omega : Set E))
    (hgrowth : ∀ x ∈ K, ∀ r, 0 < r → r ≤ 2 * R →
      ∫ z in ball x r, ‖W1p.gradient u z‖ ∂mu ≤ M * r ^ ((finrank ℝ E : ℝ) - 1 + α)) :
    HolderOnWith (2 * 2 ^ (α : ℝ) * (2 ^ finrank ℝ E / (1 - 2 ^ (-(α : ℝ)))) *
        (2 ^ (finrank ℝ E + 1) / mu.real (ball (0 : E) 1) * M)).toNNReal α
      (preciseRepresentative mu (W1p.value u)) K := by
  refine HolderOnWith.of_dist_le fun x hx y hy ↦ ?_
  have hd := hKR x hx y hy
  refine (W1p.dist_preciseRepresentative_le_of_setIntegral_norm_gradient_le (NNReal.coe_pos.2 hα)
    u ((closedBall_subset_closedBall (by linarith)).trans
      ((closedBall_subset_cthickening hx _).trans hK))
    (fun r hr hr' ↦ hgrowth x hx r hr (by linarith))
    (fun r hr hr' ↦ hgrowth y hy r hr (by linarith))).trans ?_
  rw [← mul_assoc, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _)
    (Real.rpow_nonneg dist_nonneg _)

/-- **Morrey's Dirichlet growth theorem on the whole space.** Let `u ∈ W^{1,p}` of the whole
space and `α > 0`. If `∫_{B(x, r)} ‖∇u‖ ≤ M r^(n - 1 + α)` for every ball `B(x, r)`, then the
precise representative of `u` is `α`-Hölder continuous, with Hölder constant
`2 · 2^α · 2ⁿ / (1 - 2^(-α)) · 2^(n + 1) / ω · M`, where `ω` is the measure of the unit ball. -/
theorem W1p.holderWith_preciseRepresentative_of_setIntegral_norm_gradient_le {α : ℝ≥0}
    (hα : 0 < α) {M : ℝ} (u : W1p mu ⊤ p)
    (hgrowth : ∀ x r, 0 < r →
      ∫ z in ball x r, ‖W1p.gradient u z‖ ∂mu ≤ M * r ^ ((finrank ℝ E : ℝ) - 1 + α)) :
    HolderWith (2 * 2 ^ (α : ℝ) * (2 ^ finrank ℝ E / (1 - 2 ^ (-(α : ℝ)))) *
        (2 ^ (finrank ℝ E + 1) / mu.real (ball (0 : E) 1) * M)).toNNReal α
      (preciseRepresentative mu (W1p.value u)) := by
  refine holderOnWith_univ.1 <| HolderOnWith.of_dist_le fun x _ y _ ↦ ?_
  refine (W1p.dist_preciseRepresentative_le_of_setIntegral_norm_gradient_le (NNReal.coe_pos.2 hα)
    u (subset_univ _) (fun r hr _ ↦ hgrowth x r hr) (fun r hr _ ↦ hgrowth y r hr)).trans ?_
  rw [← mul_assoc, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _)
    (Real.rpow_nonneg dist_nonneg _)

end TauCeti
