/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Convex.Star
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Topology.MetricSpace.Holder

import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.Normed.Module.Ball
import TauCeti.Analysis.Sobolev.Poincare.Potential
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Integral.RieszPotential.Bounded
import TauCeti.MeasureTheory.Measure.OpenPos
import TauCeti.Topology.MetricSpace.Holder

/-!
# Morrey's inequality for `C¹` functions

Let `E` be a finite-dimensional real normed space of dimension `n`, let `μ` be an additive Haar
measure on `E`, and let `p > n`. This file proves Morrey's inequality: a `C¹` function whose
derivative lies in `Lᵖ` is Hölder continuous of exponent `1 - n / p`, with

`‖u x - u y‖ ≤ C(n, p, μ) * ‖x - y‖ ^ (1 - n / p) * ‖Du‖_{Lᵖ}`.

The constant is explicit. Writing `ω = μ(B(0, 1))` and `K = n ω (p - 1) / (p - n)`, it is
`C = 2 ^ (n + 1) / (n ω) * K ^ (1 - 1 / p) * 2 ^ (1 - n / p)`. For `n ≥ 2` it blows up as
`p ↓ n`, as it must, since the embedding fails in the borderline case `p = n`. For `n = 1` one has
`K = ω` independently of `p`, and no blow-up occurs.

The proof starts from the pointwise potential estimate behind the Poincaré–Wirtinger inequality
(`TauCeti.enorm_sub_setAverage_le_of_starConvex`), which bounds the deviation of `u x` from a mean
of `u` by the Riesz potential `∫ ‖Du y‖ ‖x - y‖ ^ (1 - n) dy`. For `p > n`, Hölder's inequality
bounds that potential by `‖Du‖_{Lᵖ}`, because the conjugate power `‖x - y‖ ^ ((1 - n) p')` of
the kernel is integrable near the pole exactly when `p > n`. Comparing `u x` and `u y` with the
mean of `u` over a ball containing both points gives the Hölder estimate. Comparing `u x` with
its mean over the part of a star-convex domain near `x`, and bounding that mean by Hölder's
inequality, bounds `u` itself by its `W^{1,p}` norm.

## Main declarations

* `TauCeti.setLIntegral_mul_enorm_sub_rpow_one_sub_finrank_le`: for `p > n`, the Riesz potential
  of order one of `g`, over a set of radius `D` about the pole, is at most
  `K ^ (1 - 1 / p) * D ^ (1 - n / p) * ‖g‖_{Lᵖ}`.
* `TauCeti.enorm_sub_setAverage_le_of_starConvex_of_finrank_lt`: the deviation of `u x` from the
  mean of `u` over a subset of a star-convex domain, bounded by `‖Du‖_{Lᵖ}`.
* `TauCeti.enorm_sub_setAverage_le_of_convex_of_finrank_lt`: the same on a bounded convex domain.
* `TauCeti.exists_enorm_le_mul_eLpNorm_add_eLpNorm_fderiv`: the value of a `C¹` function at a
  point about which its open domain is star-convex is bounded by its `W^{1,p}` norm. For a fixed
  space, Haar measure, exponent and radius `r`, the constant is uniform over all domains whose
  intersection with the ball of radius `r` about that point has measure at least a given `m`.
* `TauCeti.exists_eLpNorm_top_le_mul_eLpNorm_add_eLpNorm_fderiv`: on the whole space,
  `‖u‖_∞ ≤ C (‖u‖_{Lᵖ} + ‖Du‖_{Lᵖ})` for every `C¹` function `u`.
* `TauCeti.enorm_sub_le_of_mem_ball_of_finrank_lt`: Morrey's inequality on a ball.
* `TauCeti.enorm_sub_le_of_contDiffOn_ball_midpoint_of_finrank_lt`: Morrey's inequality between
  two points, for `u` that is `C¹` on the ball of radius `‖x - y‖` about their midpoint.
* `TauCeti.dist_le_of_contDiffOn_ball_midpoint_of_finrank_lt`: the same as a real-valued bound,
  given a bound `N` on that `Lᵖ` norm, with the factor `2 ^ (1 - n / p)` in the constant.
* `TauCeti.edist_le_of_contDiffOn_cthickening_of_finrank_lt`: Morrey's inequality between a point
  `x` of a set `S` and a point `y` with `2 ‖x - y‖ ≤ δ`, for `u` that is `C¹` on the closed
  `δ`-thickening of `S`, in terms of the `Lᵖ` norm of the derivative on that thickening.
* `TauCeti.exists_edist_le_of_contDiffOn_cthickening_of_two_lt`: the same in the plane `ℂ`, with
  exponent `1 - 2 / p` and a constant depending only on `p`.
* `TauCeti.enorm_sub_le_of_contDiff_of_finrank_lt`: Morrey's inequality on the whole space.
* `TauCeti.holderWith_of_contDiff_of_finrank_lt`: a `C¹` function with derivative in `Lᵖ`,
  `p > n`, is Hölder continuous of exponent `1 - n / p`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 7.17.
* L. C. Evans, *Partial Differential Equations*, §5.6.2, Theorem 4.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Set Module
open scoped ENNReal NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} [μ.IsAddHaarMeasure] {u : E → F} {Ω S : Set E} {x : E} {D : ℝ} {p : ℝ≥0}

/-- **The Riesz potential of order one is bounded on `Lᵖ` for `p > n`.** If `Ω` lies in
`closedBall x D` and `p` exceeds the dimension `n` of the space, then the Riesz potential at `x`
of a function `g` on `Ω` is at most `K ^ (1 - 1 / p) * D ^ (1 - n / p)` times the `Lᵖ(Ω)` norm of
`g`, where `K = n μ(B(0, 1)) (p - 1) / (p - n)`. -/
theorem setLIntegral_mul_enorm_sub_rpow_one_sub_finrank_le (hD : Ω ⊆ closedBall x D)
    {g : E → ℝ≥0∞} (hg : AEMeasurable g (μ.restrict Ω)) (hp : (finrank ℝ E : ℝ≥0) < p) :
    ∫⁻ y in Ω, g y * ‖x - y‖ₑ ^ (1 - (finrank ℝ E : ℝ)) ∂μ ≤
      ENNReal.ofReal ((finrank ℝ E * μ.real (ball 0 1) * (p - 1) / (p - finrank ℝ E)) ^
          (1 - 1 / (p : ℝ)) * D ^ (1 - finrank ℝ E / (p : ℝ))) *
        (∫⁻ y in Ω, g y ^ (p : ℝ) ∂μ) ^ (1 / (p : ℝ)) := by
  set n := finrank ℝ E with hn_def
  rcases subsingleton_or_nontrivial E with hE | hE
  · have hzero : ∀ y, g y * ‖x - y‖ₑ ^ (1 - (n : ℝ)) = 0 := fun y => by
      simp [n, Subsingleton.elim x y, finrank_zero_of_subsingleton]
    simp [hzero]
  have hn : (1 : ℝ≥0) ≤ n := mod_cast finrank_pos
  have hp1 : (1 : ℝ≥0∞) ≤ (p : ℝ≥0∞) := mod_cast hn.trans hp.le
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast zero_le.trans_lt hp
  have hpn : (n : ℝ) * ((p : ℝ≥0∞).toReal)⁻¹ < 1 := by
    rw [ENNReal.coe_toReal, ← div_eq_mul_inv, div_lt_one hp_pos]
    exact_mod_cast hp
  have hbound := rieszPotential_restrict_le_of_subset_closedBall (μ := μ) (α := 1)
    (p := (p : ℝ≥0∞)) hD hp1 (Or.inl hpn) g
  have hlhs : ∫⁻ y in Ω, g y * ‖x - y‖ₑ ^ (1 - (n : ℝ)) ∂μ =
      rieszPotential (μ.restrict Ω) 1 g x := by
    simp [rieszPotential_def, n, mul_comm]
  have hconst : rieszDiamConst μ 1 (p : ℝ≥0∞) ∞ =
      ((n : ℝ) * μ.real (ball 0 1) * (p - 1) / (p - n)) ^ (1 - 1 / (p : ℝ)) := by
    rw [rieszDiamConst_def, ← hn_def]
    simp only [ENNReal.coe_toReal, ENNReal.toReal_top, inv_zero, sub_zero, one_div]
    congr 1
    field_simp
  rw [hlhs]
  refine hbound.trans_eq ?_
  rw [hconst, ← hn_def, ENNReal.coe_toReal, ← div_eq_mul_inv,
    eLpNorm_nnreal_eq_lintegral (zero_le.trans_lt hp).ne' hg.aestronglyMeasurable]
  simp only [eNorm_eq_self]

/-- **The Morrey potential estimate for the mean.** If `u` is `C¹` on an open set `Ω` which is
star-convex about `x` and contained in `closedBall x D`, and `p` exceeds the dimension `n` of the
space, then for every `S ⊆ Ω` of positive measure the deviation of `u x` from the mean of `u`
over `S` is at most `D ^ n / (n μ(S)) * K ^ (1 - 1 / p) * D ^ (1 - n / p)` times the `Lᵖ(Ω)`
norm of the derivative of `u`, where `K = n μ(B(0, 1)) (p - 1) / (p - n)`. -/
theorem enorm_sub_setAverage_le_of_starConvex_of_finrank_lt [CompleteSpace F] (hΩ : IsOpen Ω)
    (hu : ContDiffOn ℝ 1 u Ω) (hx : StarConvex ℝ x Ω) (hD : Ω ⊆ closedBall x D) (hS : S ⊆ Ω)
    (hS₀ : μ S ≠ 0) (hp : (finrank ℝ E : ℝ≥0) < p) :
    ‖u x - ⨍ y in S, u y ∂μ‖ₑ ≤
      ENNReal.ofReal (D ^ finrank ℝ E / finrank ℝ E) / μ S *
        ENNReal.ofReal ((finrank ℝ E * μ.real (ball 0 1) * (p - 1) / (p - finrank ℝ E)) ^
          (1 - 1 / (p : ℝ)) * D ^ (1 - finrank ℝ E / (p : ℝ))) *
        eLpNorm (fderiv ℝ u) p (μ.restrict Ω) := by
  have hcont := hu.continuousOn_fderiv_of_isOpen hΩ le_rfl
  rw [eLpNorm_nnreal_eq_lintegral (zero_le.trans_lt hp).ne'
    (hcont.aestronglyMeasurable hΩ.measurableSet), mul_assoc]
  refine (enorm_sub_setAverage_le_of_starConvex hΩ hu hx hD hS hS₀).trans ?_
  gcongr
  exact setLIntegral_mul_enorm_sub_rpow_one_sub_finrank_le hD
    (hcont.eNorm.aemeasurable hΩ.measurableSet) hp

/-- **The Morrey potential estimate on a convex domain.** If `u` is `C¹` on a bounded convex
open set `Ω`, `x ∈ Ω`, and `p` exceeds the dimension `n` of the space, then for every `S ⊆ Ω`
of positive measure the deviation of `u x` from the mean of `u` over `S` is at most
`d ^ n / (n μ(S)) * K ^ (1 - 1 / p) * d ^ (1 - n / p)` times the `Lᵖ(Ω)` norm of the derivative
of `u`, where `d = diam Ω` and `K = n μ(B(0, 1)) (p - 1) / (p - n)`. -/
theorem enorm_sub_setAverage_le_of_convex_of_finrank_lt [CompleteSpace F] (hΩ : IsOpen Ω)
    (hΩc : Convex ℝ Ω) (hb : Bornology.IsBounded Ω) (hu : ContDiffOn ℝ 1 u Ω) (hx : x ∈ Ω)
    (hS : S ⊆ Ω) (hS₀ : μ S ≠ 0) (hp : (finrank ℝ E : ℝ≥0) < p) :
    ‖u x - ⨍ y in S, u y ∂μ‖ₑ ≤
      ENNReal.ofReal (diam Ω ^ finrank ℝ E / finrank ℝ E) / μ S *
        ENNReal.ofReal ((finrank ℝ E * μ.real (ball 0 1) * (p - 1) / (p - finrank ℝ E)) ^
          (1 - 1 / (p : ℝ)) * diam Ω ^ (1 - finrank ℝ E / (p : ℝ))) *
        eLpNorm (fderiv ℝ u) p (μ.restrict Ω) :=
  enorm_sub_setAverage_le_of_starConvex_of_finrank_lt hΩ hu (hΩc.starConvex hx)
    (fun _ hy => mem_closedBall.2 (dist_le_diam_of_mem hb hy hx)) hS hS₀ hp

/-- The Morrey potential estimate for the mean
(`TauCeti.enorm_sub_setAverage_le_of_starConvex_of_finrank_lt`) with its coefficient separated
into a finite factor `A`, depending only on `n`, `p`, `μ` and `D`, and the inverse measure of the
set `S` of the mean. -/
private theorem exists_enorm_sub_setAverage_le_mul_inv [CompleteSpace F]
    (hp : (finrank ℝ E : ℝ≥0) < p) (D : ℝ) :
    ∃ A : ℝ≥0∞, A ≠ ∞ ∧ ∀ (Ω S : Set E) (u : E → F) (x : E), IsOpen Ω → ContDiffOn ℝ 1 u Ω →
      StarConvex ℝ x Ω → Ω ⊆ closedBall x D → S ⊆ Ω → μ S ≠ 0 →
      ‖u x - ⨍ y in S, u y ∂μ‖ₑ ≤ A * (μ S)⁻¹ * eLpNorm (fderiv ℝ u) p (μ.restrict Ω) :=
  ⟨_, ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    fun _ _ _ _ hΩ hu hx hD hS hS₀ =>
      (enorm_sub_setAverage_le_of_starConvex_of_finrank_lt hΩ hu hx hD hS hS₀ hp).trans_eq (by
        rw [div_eq_mul_inv, mul_right_comm (ENNReal.ofReal _)])⟩

/-- **Morrey's supremum bound.** Let `p ≥ 1` exceed the dimension `n` of the space, and let
`r : ℝ` and `m ≠ 0`. There is a constant `C`, depending only on `n`, `p`, `μ`, `r` and `m`, such
that `‖u x‖ ≤ C (‖u‖_{Lᵖ(Ω)} + ‖Du‖_{Lᵖ(Ω)})` whenever `u` is `C¹` on an open set `Ω` that is
star-convex about `x` and `m ≤ μ (Ω ∩ ball x r)`.

So on a convex open set all of whose intersections with balls of radius `r` about its points have
measure at least `m`, the supremum of a `C¹` function is bounded by its `W^{1,p}` norm, with a
constant that does not depend on the size of the set. Long rectangles of fixed width are such
sets (`TauCeti.ofReal_mul_ofReal_le_volume_Ioo_prod_Ioo_inter_ball`). -/
theorem exists_enorm_le_mul_eLpNorm_add_eLpNorm_fderiv [CompleteSpace F] (hp1 : 1 ≤ p)
    (hp : (finrank ℝ E : ℝ≥0) < p) (r : ℝ) {m : ℝ≥0∞} (hm : m ≠ 0) :
    ∃ C : ℝ≥0, ∀ (Ω : Set E) (u : E → F) (x : E), IsOpen Ω → StarConvex ℝ x Ω →
      ContDiffOn ℝ 1 u Ω → m ≤ μ (Ω ∩ ball x r) →
      ‖u x‖ₑ ≤ C * (eLpNorm u p (μ.restrict Ω) + eLpNorm (fderiv ℝ u) p (μ.restrict Ω)) := by
  obtain ⟨A, hA, hAu⟩ := exists_enorm_sub_setAverage_le_mul_inv (μ := μ) (F := F) hp r
  set C₀ : ℝ≥0∞ := A * m⁻¹ + m ^ (-(p : ℝ)⁻¹)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast zero_lt_one.trans_le hp1
  have hC₀ : C₀ ≠ ∞ := by
    refine ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hA (ENNReal.inv_ne_top.2 hm), fun h => ?_⟩
    rcases ENNReal.rpow_eq_top_iff.1 h with h | h
    · exact hm h.1
    · linarith [h.2, inv_pos.2 hp0]
  refine ⟨C₀.toNNReal, fun Ω u x hΩ hΩx hu hm' => ?_⟩
  rw [ENNReal.coe_toNNReal hC₀]
  set Ω' := Ω ∩ ball x r
  have hS₀ : μ Ω' ≠ 0 := (pos_iff_ne_zero.2 hm |>.trans_le hm').ne'
  -- The radius is positive, since `Ω'` is not empty.
  have hr : 0 < r := by
    by_contra! h
    exact hS₀ (by simp [Ω', ball_eq_empty.2 h])
  have hmono : μ.restrict Ω' ≤ μ.restrict Ω := Measure.restrict_mono inter_subset_left le_rfl
  -- The deviation of `u x` from the mean of `u` over `Ω'`, by the Morrey potential estimate.
  have h₁ := hAu Ω' Ω' u x (hΩ.inter isOpen_ball) (hu.mono inter_subset_left)
    (hΩx.inter ((convex_ball x r).starConvex (mem_ball_self hr)))
    (fun _ hy => ball_subset_closedBall hy.2) subset_rfl hS₀
  -- The mean itself, by Hölder's inequality.
  have h₂ := enorm_setAverage_le (f := u) (mu := μ) (s := Ω') (p := p) (by exact_mod_cast hp1)
  rw [ENNReal.coe_toReal] at h₂
  have hinv : (μ Ω')⁻¹ ≤ m⁻¹ := ENNReal.inv_le_inv.2 hm'
  have hpow : μ Ω' ^ (-(p : ℝ)⁻¹) ≤ m ^ (-(p : ℝ)⁻¹) :=
    by rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
       exact ENNReal.inv_le_inv.2 (ENNReal.rpow_le_rpow hm' (inv_pos.2 hp0).le)
  calc ‖u x‖ₑ = ‖(u x - ⨍ y in Ω', u y ∂μ) + ⨍ y in Ω', u y ∂μ‖ₑ := by rw [sub_add_cancel]
    _ ≤ ‖u x - ⨍ y in Ω', u y ∂μ‖ₑ + ‖⨍ y in Ω', u y ∂μ‖ₑ := eNorm_add_le _ _
    _ ≤ A * m⁻¹ * eLpNorm (fderiv ℝ u) p (μ.restrict Ω) +
        m ^ (-(p : ℝ)⁻¹) * eLpNorm u p (μ.restrict Ω) := by
      gcongr
      · exact h₁.trans (by gcongr)
      · exact h₂.trans (by gcongr)
    _ ≤ C₀ * eLpNorm (fderiv ℝ u) p (μ.restrict Ω) + C₀ * eLpNorm u p (μ.restrict Ω) := by
      gcongr
      · exact le_self_add
      · exact le_add_self
    _ = C₀ * (eLpNorm u p (μ.restrict Ω) + eLpNorm (fderiv ℝ u) p (μ.restrict Ω)) := by ring

/-- **The supremum of a `C¹` function is bounded by its `W^{1,p}` norm for `p > n`.** There is a
constant `C`, depending only on `n`, `p` and `μ`, such that every `C¹` function `u` on the whole
space satisfies `‖u‖_∞ ≤ C (‖u‖_{Lᵖ} + ‖Du‖_{Lᵖ})`. -/
theorem exists_eLpNorm_top_le_mul_eLpNorm_add_eLpNorm_fderiv [CompleteSpace F] (hp1 : 1 ≤ p)
    (hp : (finrank ℝ E : ℝ≥0) < p) :
    ∃ C : ℝ≥0, ∀ u : E → F, ContDiff ℝ 1 u →
      eLpNorm u ∞ μ ≤ C * (eLpNorm u p μ + eLpNorm (fderiv ℝ u) p μ) := by
  -- Every ball of radius one has the measure of the unit ball about the origin.
  obtain ⟨C, hC⟩ := exists_enorm_le_mul_eLpNorm_add_eLpNorm_fderiv (μ := μ) (F := F) hp1 hp 1
    (measure_ball_pos μ (0 : E) one_pos).ne'
  refine ⟨C, fun u hu ↦ ?_⟩
  rw [eLpNorm_exponent_top hu.continuous.aestronglyMeasurable]
  refine eLpNormEssSup_le_of_ae_eNorm_bound (ae_of_all _ fun x ↦ ?_)
  simpa only [Measure.restrict_univ] using hC univ u x isOpen_univ (starConvex_univ x)
    hu.contDiffOn (by rw [univ_inter, Measure.addHaar_ball_center μ x 1])

/-- **Morrey's inequality on a ball.** If `u` is `C¹` on `ball z r` and `p` exceeds the dimension
`n` of the space, then for all `x, y` in the ball, `‖u x - u y‖` is at most
`2 ^ (n + 1) / (n ω) * K ^ (1 - 1 / p) * (2 r) ^ (1 - n / p)` times the `Lᵖ` norm of the
derivative of `u` on the ball, where `ω = μ(B(0, 1))` and `K = n ω (p - 1) / (p - n)`. -/
theorem enorm_sub_le_of_mem_ball_of_finrank_lt [CompleteSpace F] {z : E} {r : ℝ}
    (hu : ContDiffOn ℝ 1 u (ball z r)) {x y : E} (hx : x ∈ ball z r) (hy : y ∈ ball z r)
    (hp : (finrank ℝ E : ℝ≥0) < p) :
    ‖u x - u y‖ₑ ≤
      ENNReal.ofReal (2 ^ (finrank ℝ E + 1) / (finrank ℝ E * μ.real (ball 0 1)) *
        (finrank ℝ E * μ.real (ball 0 1) * (p - 1) / (p - finrank ℝ E)) ^ (1 - 1 / (p : ℝ)) *
          (2 * r) ^ (1 - finrank ℝ E / (p : ℝ))) *
        eLpNorm (fderiv ℝ u) p (μ.restrict (ball z r)) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · simp [Subsingleton.elim x y]
  set n := finrank ℝ E
  set ω := μ.real (ball (0 : E) 1) with hω_def
  set K : ℝ := n * ω * (p - 1) / (p - n)
  set N := eLpNorm (fderiv ℝ u) p (μ.restrict (ball z r))
  have hr : 0 < r := pos_of_mem_ball hx
  have hball₀ : μ (ball z r) ≠ 0 := (measure_ball_pos μ z hr).ne'
  -- Each point of the ball sees the whole ball within distance `2 r`.
  have hmean : ∀ w ∈ ball z r, ‖u w - ⨍ v in ball z r, u v ∂μ‖ₑ ≤
      ENNReal.ofReal ((2 * r) ^ n / n) / μ (ball z r) *
        ENNReal.ofReal (K ^ (1 - 1 / (p : ℝ)) * (2 * r) ^ (1 - n / (p : ℝ))) * N :=
    fun w hw => enorm_sub_setAverage_le_of_starConvex_of_finrank_lt isOpen_ball hu
      ((convex_ball z r).starConvex hw) (fun v hv => mem_closedBall.2 (by
        linarith [dist_triangle v z w, mem_ball.1 hv, mem_ball'.1 hw])) subset_rfl hball₀ hp
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast finrank_pos
  have hpn : (n : ℝ) < p := by exact_mod_cast hp
  have hK : 0 ≤ K := div_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith)
  have hω : 0 < ω := Metric.measureReal_ball_pos μ 0 one_pos
  -- The constant: the mean-value factor `(2 r) ^ n / (n μ(ball z r))` is `2 ^ n / (n ω)`.
  have hmeasure : μ (ball z r) = ENNReal.ofReal (r ^ n * ω) := by
    rw [Measure.addHaar_ball_of_pos μ z hr, ← ofReal_measureReal measure_ball_lt_top.ne,
      ← hω_def, ← ENNReal.ofReal_mul (pow_nonneg hr.le _)]
  have hmeanFactor : ENNReal.ofReal ((2 * r) ^ n / n) / μ (ball z r) =
      ENNReal.ofReal ((2 * r) ^ n / n / (r ^ n * ω)) := by
    rw [hmeasure, ← ENNReal.ofReal_div_of_pos (mul_pos (pow_pos hr _) hω)]
  have hconst : ENNReal.ofReal ((2 * r) ^ n / n) / μ (ball z r) *
      ENNReal.ofReal (K ^ (1 - 1 / (p : ℝ)) * (2 * r) ^ (1 - n / (p : ℝ))) * N +
      ENNReal.ofReal ((2 * r) ^ n / n) / μ (ball z r) *
      ENNReal.ofReal (K ^ (1 - 1 / (p : ℝ)) * (2 * r) ^ (1 - n / (p : ℝ))) * N =
      ENNReal.ofReal (2 ^ (n + 1) / (n * ω) * K ^ (1 - 1 / (p : ℝ)) *
        (2 * r) ^ (1 - n / (p : ℝ))) * N := by
    have hX : 0 ≤ (2 * r) ^ n / n / (r ^ n * ω) := by
      have := hr.le
      positivity
    have hY : 0 ≤ K ^ (1 - 1 / (p : ℝ)) * (2 * r) ^ (1 - n / (p : ℝ)) :=
      mul_nonneg (Real.rpow_nonneg hK _) (Real.rpow_nonneg (by linarith) _)
    have hreal :
        (2 * r) ^ n / n / (r ^ n * ω) *
              (K ^ (1 - 1 / (p : ℝ)) * (2 * r) ^ (1 - n / (p : ℝ))) +
            (2 * r) ^ n / n / (r ^ n * ω) *
              (K ^ (1 - 1 / (p : ℝ)) * (2 * r) ^ (1 - n / (p : ℝ))) =
          2 ^ (n + 1) / (n * ω) * K ^ (1 - 1 / (p : ℝ)) *
            (2 * r) ^ (1 - n / (p : ℝ)) := by
      rw [mul_pow, pow_succ]
      field_simp
      ring
    rw [hmeanFactor, ← ENNReal.ofReal_mul hX, ← add_mul,
      ← ENNReal.ofReal_add (mul_nonneg hX hY) (mul_nonneg hX hY), hreal]
  calc
    ‖u x - u y‖ₑ ≤ ‖u x - ⨍ v in ball z r, u v ∂μ‖ₑ + ‖u y - ⨍ v in ball z r, u v ∂μ‖ₑ := by
      simpa only [eDist_eq_eNorm_sub] using edist_triangle_right (u x) (u y) _
    _ ≤ _ := add_le_add (hmean x hx) (hmean y hy)
    _ = _ := hconst

/-- **Morrey's inequality between two points.** If `u` is `C¹` on the ball of radius `‖x - y‖`
about the midpoint of `x` and `y`, and `p` exceeds the dimension `n` of the space, then
`‖u x - u y‖` is at most `2 ^ (n + 1) / (n ω) * K ^ (1 - 1 / p) * (2 ‖x - y‖) ^ (1 - n / p)` times
the `Lᵖ` norm of the derivative of `u` on that ball, where `ω = μ(B(0, 1))` and
`K = n ω (p - 1) / (p - n)`. -/
theorem enorm_sub_le_of_contDiffOn_ball_midpoint_of_finrank_lt [CompleteSpace F] {x y : E}
    (hu : ContDiffOn ℝ 1 u (ball (midpoint ℝ x y) ‖x - y‖)) (hp : (finrank ℝ E : ℝ≥0) < p) :
    ‖u x - u y‖ₑ ≤
      ENNReal.ofReal (2 ^ (finrank ℝ E + 1) / (finrank ℝ E * μ.real (ball 0 1)) *
        (finrank ℝ E * μ.real (ball 0 1) * (p - 1) / (p - finrank ℝ E)) ^ (1 - 1 / (p : ℝ)) *
          (2 * ‖x - y‖) ^ (1 - finrank ℝ E / (p : ℝ))) *
        eLpNorm (fderiv ℝ u) p (μ.restrict (ball (midpoint ℝ x y) ‖x - y‖)) := by
  rcases eq_or_ne x y with rfl | hxy
  · simp
  -- Both points lie in the ball of radius `‖x - y‖` about their midpoint.
  have hpos : 0 < dist x y := dist_pos.2 hxy
  have hx : x ∈ ball (midpoint ℝ x y) ‖x - y‖ := by
    rw [mem_ball, dist_left_midpoint, ← dist_eq_norm]
    norm_num
    linarith
  have hy : y ∈ ball (midpoint ℝ x y) ‖x - y‖ := by
    rw [mem_ball, dist_right_midpoint, ← dist_eq_norm]
    norm_num
    linarith
  exact enorm_sub_le_of_mem_ball_of_finrank_lt (μ := μ) hu hx hy hp

/-- **Morrey's inequality.** If `u` is `C¹` on the whole space and `p` exceeds the dimension `n`
of the space, then `‖u x - u y‖` is at most
`2 ^ (n + 1) / (n ω) * K ^ (1 - 1 / p) * (2 ‖x - y‖) ^ (1 - n / p)` times the `Lᵖ` norm of the
derivative of `u`, where `ω = μ(B(0, 1))` and `K = n ω (p - 1) / (p - n)`. -/
theorem enorm_sub_le_of_contDiff_of_finrank_lt [CompleteSpace F] (hu : ContDiff ℝ 1 u) (x y : E)
    (hp : (finrank ℝ E : ℝ≥0) < p) :
    ‖u x - u y‖ₑ ≤
      ENNReal.ofReal (2 ^ (finrank ℝ E + 1) / (finrank ℝ E * μ.real (ball 0 1)) *
        (finrank ℝ E * μ.real (ball 0 1) * (p - 1) / (p - finrank ℝ E)) ^ (1 - 1 / (p : ℝ)) *
          (2 * ‖x - y‖) ^ (1 - finrank ℝ E / (p : ℝ))) *
        eLpNorm (fderiv ℝ u) p μ := by
  refine (enorm_sub_le_of_contDiffOn_ball_midpoint_of_finrank_lt (μ := μ) hu.contDiffOn hp).trans
    ?_
  gcongr
  exact Measure.restrict_le_self

/-- The Hölder constant of Morrey's inequality is nonnegative. -/
private theorem morreyConstant_nonneg (n : ℕ) (m : ℝ) (p : ℝ≥0) (hm : 0 ≤ m)
    (hp : (n : ℝ≥0) < p) :
    0 ≤ 2 ^ (n + 1) / (n * m) * (n * m * (p - 1) / (p - n)) ^ (1 - 1 / (p : ℝ)) *
      2 ^ (1 - n / (p : ℝ)) := by
  have hK : 0 ≤ (n * m * (p - 1) / (p - n) : ℝ) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [hn]
    have hpn : (n : ℝ) < p := by exact_mod_cast hp
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact div_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith)
  exact mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hK _)) (by positivity)

/-- **Morrey's inequality between two points, real form.** If `u` is `C¹` on the ball of radius
`‖x - y‖` about the midpoint of `x` and `y`, `p` exceeds the dimension `n` of the space, and the
`Lᵖ` norm of the derivative of `u` on that ball is at most `N`, then `dist (u x) (u y)` is at most
`2 ^ (n + 1) / (n ω) * K ^ (1 - 1 / p) * 2 ^ (1 - n / p) * N * dist x y ^ (1 - n / p)`, where
`ω = μ(B(0, 1))` and `K = n ω (p - 1) / (p - n)`. -/
theorem dist_le_of_contDiffOn_ball_midpoint_of_finrank_lt [CompleteSpace F] {x y : E} {N : ℝ≥0}
    (hu : ContDiffOn ℝ 1 u (ball (midpoint ℝ x y) ‖x - y‖)) (hp : (finrank ℝ E : ℝ≥0) < p)
    (hN : eLpNorm (fderiv ℝ u) p (μ.restrict (ball (midpoint ℝ x y) ‖x - y‖)) ≤ N) :
    dist (u x) (u y) ≤
      2 ^ (finrank ℝ E + 1) / (finrank ℝ E * μ.real (ball 0 1)) *
        (finrank ℝ E * μ.real (ball 0 1) * (p - 1) / (p - finrank ℝ E)) ^ (1 - 1 / (p : ℝ)) *
          2 ^ (1 - finrank ℝ E / (p : ℝ)) * N * dist x y ^ (1 - finrank ℝ E / (p : ℝ)) := by
  have hC := morreyConstant_nonneg _ (μ.real (ball 0 1)) p measureReal_nonneg hp
  rw [dist_eq_norm, ← ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_nonneg hC N.coe_nonneg)
    (by positivity)), ofReal_norm]
  refine ((enorm_sub_le_of_contDiffOn_ball_midpoint_of_finrank_lt (μ := μ) hu hp).trans
    (mul_le_mul_right hN _)).trans_eq ?_
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul' N.coe_nonneg,
    Real.mul_rpow zero_le_two (norm_nonneg _), ← dist_eq_norm]
  congr 1
  ring

/-- **Morrey's inequality near a set.** If `u` is `C¹` on the closed `δ`-thickening of a set `S`,
`p` exceeds the dimension `n` of the space, `x ∈ S` and `2 ‖x - y‖ ≤ δ`, then `edist (u x) (u y)`
is at most `2 ^ (n + 1) / (n ω) * K ^ (1 - 1 / p) * 2 ^ (1 - n / p) * edist x y ^ (1 - n / p)`
times the `Lᵖ` norm of the derivative of `u` on that thickening, where `ω = μ(B(0, 1))` and
`K = n ω (p - 1) / (p - n)`. -/
theorem edist_le_of_contDiffOn_cthickening_of_finrank_lt [CompleteSpace F] {S : Set E} {δ : ℝ}
    {y : E} (hu : ContDiffOn ℝ 1 u (cthickening δ S)) (hp : (finrank ℝ E : ℝ≥0) < p) (hx : x ∈ S)
    (hxy : 2 * dist x y ≤ δ) :
    edist (u x) (u y) ≤
      ENNReal.ofReal (2 ^ (finrank ℝ E + 1) / (finrank ℝ E * μ.real (ball 0 1)) *
        (finrank ℝ E * μ.real (ball 0 1) * (p - 1) / (p - finrank ℝ E)) ^ (1 - 1 / (p : ℝ)) *
          2 ^ (1 - finrank ℝ E / (p : ℝ))) * edist x y ^ (1 - finrank ℝ E / (p : ℝ)) *
        eLpNorm (fderiv ℝ u) p (μ.restrict (cthickening δ S)) := by
  have hball := ball_midpoint_subset_cthickening hx hxy
  have hα : 0 ≤ 1 - finrank ℝ E / (p : ℝ) :=
    sub_nonneg.2 ((div_le_one (zero_le.trans_lt hp)).2 (by exact_mod_cast hp.le))
  rw [eDist_eq_eNorm_sub]
  refine (enorm_sub_le_of_contDiffOn_ball_midpoint_of_finrank_lt (μ := μ) (hu.mono hball)
    hp).trans ?_
  -- The factor `(2 ‖x - y‖) ^ (1 - n / p)` splits off `‖x - y‖ ^ (1 - n / p)`.
  rw [Real.mul_rpow zero_le_two (norm_nonneg _), ← mul_assoc,
    ENNReal.ofReal_mul' (Real.rpow_nonneg (norm_nonneg _) _), ← dist_eq_norm,
    ← ENNReal.ofReal_rpow_of_nonneg dist_nonneg hα, ← edist_dist]
  gcongr
  rwa [dist_eq_norm]

/-- **Morrey's inequality near a set in the plane.** Let `2 < p`. There is a constant `c` such
that for every set `S ⊆ ℂ`, every map `u` that is `C¹` on the closed `δ`-thickening of `S`, with
values in a real Banach space, and all `x ∈ S` and `y` with `2 |x - y| ≤ δ`,

`‖u x - u y‖ ≤ c |x - y| ^ (1 - 2 / p) ‖Du‖_{Lᵖ}`,

the `Lᵖ` norm being taken over that thickening. -/
theorem exists_edist_le_of_contDiffOn_cthickening_of_two_lt [CompleteSpace F] (hp : 2 < p) :
    ∃ c : ℝ≥0, ∀ {S : Set ℂ} {δ : ℝ} {u : ℂ → F} {x y : ℂ},
      ContDiffOn ℝ 1 u (cthickening δ S) → x ∈ S → 2 * dist x y ≤ δ →
      edist (u x) (u y) ≤ c * edist x y ^ ((1 - 2 / p : ℝ≥0) : ℝ) *
        eLpNorm (fderiv ℝ u) p (volume.restrict (cthickening δ S)) := by
  have hp₂ : (finrank ℝ ℂ : ℝ≥0) < p := by simpa using hp
  have hα : ((1 - 2 / p : ℝ≥0) : ℝ) = 1 - (finrank ℝ ℂ : ℝ) / (p : ℝ) := by
    rw [Complex.finrank_real_complex, NNReal.coe_sub ((div_le_one₀ (zero_lt_two.trans hp)).2
      hp.le), NNReal.coe_div]
    norm_num
  have hC := morreyConstant_nonneg _ ((volume : Measure ℂ).real (ball 0 1)) p measureReal_nonneg
    hp₂
  -- The constant is Morrey's constant for `ℂ`, packaged with its nonnegativity.
  refine ⟨NNReal.mk _ hC, fun hu hx hxy ↦ ?_⟩
  rw [hα, ← ENNReal.ofReal_eq_coe_nnreal hC]
  exact edist_le_of_contDiffOn_cthickening_of_finrank_lt hu hp₂ hx hxy

/-- **Morrey's inequality, Hölder form.** If `u` is `C¹` on the whole space, `p` exceeds the
dimension `n` of the space, and the derivative of `u` lies in `Lᵖ`, then `u` is Hölder continuous
of exponent `1 - n / p`, with constant
`2 ^ (n + 1) / (n ω) * K ^ (1 - 1 / p) * 2 ^ (1 - n / p) * ‖Du‖_{Lᵖ}`, where `ω = μ(B(0, 1))`
and `K = n ω (p - 1) / (p - n)`. -/
theorem holderWith_of_contDiff_of_finrank_lt [CompleteSpace F] (hu : ContDiff ℝ 1 u)
    (hp : (finrank ℝ E : ℝ≥0) < p) (hDu : eLpNorm (fderiv ℝ u) p μ ≠ ∞) :
    HolderWith (Real.toNNReal (2 ^ (finrank ℝ E + 1) / (finrank ℝ E * μ.real (ball 0 1)) *
        (finrank ℝ E * μ.real (ball 0 1) * (p - 1) / (p - finrank ℝ E)) ^ (1 - 1 / (p : ℝ)) *
          2 ^ (1 - finrank ℝ E / (p : ℝ))) * (eLpNorm (fderiv ℝ u) p μ).toNNReal)
      (1 - finrank ℝ E / p) u := by
  set n := finrank ℝ E
  have hα : (((1 - n / p : ℝ≥0)) : ℝ) = 1 - n / (p : ℝ) := by
    rw [NNReal.coe_sub ((div_le_one (zero_le.trans_lt hp)).2 hp.le), NNReal.coe_one,
      NNReal.coe_div, NNReal.coe_natCast]
  have hC := morreyConstant_nonneg n (μ.real (ball 0 1)) p measureReal_nonneg hp
  refine holderOnWith_univ.1 (HolderOnWith.of_dist_le fun x _ y _ ↦ ?_)
  rw [NNReal.coe_mul, Real.coe_toNNReal _ hC, hα]
  exact dist_le_of_contDiffOn_ball_midpoint_of_finrank_lt (μ := μ) hu.contDiffOn hp
    ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans (ENNReal.coe_toNNReal hDu).ge)

end TauCeti
