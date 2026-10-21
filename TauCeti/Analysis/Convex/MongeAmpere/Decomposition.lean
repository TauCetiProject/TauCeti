/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.MongeAmpere.Basic
public import TauCeti.Analysis.Convex.Alexandrov
import TauCeti.Analysis.Convex.Extrema
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.Analysis.Calculus.Gradient
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Lebesgue decomposition of the Monge–Ampère measure

Let `E` be a finite-dimensional real inner product space with an additive Haar measure `μ`, and
let `f : E → EReal` be convex (convex real epigraph, never `⊥`), with `D` the interior of its
effective domain and `F x = (f x).toReal`. By Alexandrov's theorem, at almost every `x ∈ D` the
subdifferential of `f` is differentiable, with a positive derivative `H x`, the Alexandrov Hessian
of `f` at `x`: every subgradient `y'` at a point `x'` near `x` satisfies
`y' = ∇F x + H x (x' - x) + o(‖x' - x‖)`. This file shows that the Alexandrov Hessian determines
exactly the absolutely continuous part of the Monge–Ampère measure `MA_{f, g μ}` weighted by a
measurable density `g`, `MA_{f, g μ}(s) = ∫_{∂f(s ∩ D)} g dμ`:

  `MA_{f, g μ} = (MA_{f, g μ})ˢ + g (∇F x) det (H x) dx` on `D`,

where `(MA_{f, g μ})ˢ` is singular with respect to `μ`. For `g = 1` this is the decomposition
`MA_f = (MA_f)ˢ + det (H x) dx` of the Aleksandrov measure. So `MA_f = h dx` gives `det (H x) = h x`
almost everywhere: an Aleksandrov solution of the Monge–Ampère equation `det D²f = h` solves it
almost everywhere. The converse fails, because the singular part is invisible to the Alexandrov
Hessian: a cone has Alexandrov Hessian determinant `0` almost everywhere, yet its Monge–Ampère
measure is a positive multiple of a Dirac mass (`TauCeti.mongeAmpereMeasure_mul_norm_sub`).

For weighted measures this is the Jacobian equation of optimal transport. If the Monge–Ampère
measure of `f` weighted by `ν₁ = g₁ dx` is `ν₀ = g₀ dx`, which is what it means for `f` to be a
weak (Brenier) solution of the transport problem from `ν₀` to `ν₁`
(`TauCeti.mongeAmpereMeasure_eq_of_hasLaw`), then `g₀ x = g₁ (∇F x) det (H x)` for almost every
`x ∈ D`.

The decomposition is proved by the change of variables formula. Off a null set of `D`, the
subdifferential of `f` at `x` is the single gradient `∇F x`, and the gradient map has derivative
`H x` within that set. If two such points `x₁ ≠ x₂` have the same gradient `y`, then `y` is a
subgradient along the segment between them, so `H x₁ (x₂ - x₁) = 0`
(`TauCeti.apply_sub_eq_zero_of_forall_mem_subdifferential_norm_sub_le`). So the gradient is
injective where `det (H x) ≠ 0`, where Mathlib's change of variables formula computes the weighted
measure of its image, and it maps the set where `det (H x) = 0` to a null set
(`TauCeti.withDensity_image_gradient_eq_setLIntegral`). The remaining part
of `MA_{f, g μ}` lives on a `μ`-null subset of `D`, hence is singular.

Separately, the density is identified pointwise: `MA_f(closedBall x r) / μ(closedBall x r) → det A`
as `r → 0⁺` at every `x ∈ D` where the subdifferential has derivative `A`. Up to `o(r)`, the
subgradients at points of `closedBall x r` lie in `∇F x + r • A (closedBall 0 1)`, which gives the
upper bound. For the lower bound, `A` is coercive when `det A ≠ 0`, so for `s < 1` and small `r`
the second-order expansion of `F` shows that, for each `p ∈ ∇F x + r • A (closedBall 0 s)`, the
convex function `F - ⟪·, p⟫` is smaller somewhere in the ball than on its sphere; its minimum over
the ball is then attained inside, where `p` is a subgradient.

## Main statements

* `TauCeti.tendsto_mongeAmpereMeasure_closedBall_div` — the density of `MA_f` at a point where
  the subdifferential is differentiable with derivative `A` is `det A`;
* `TauCeti.rnDeriv_mongeAmpereMeasure_withDensity_ae_eq` and
  `TauCeti.rnDeriv_mongeAmpereMeasure_ae_eq` — the Radon–Nikodym derivative of `MA_{f, g μ}` is
  `g (∇F x) det (H x)` on `D`, and `0` off `D`; for `g = 1` it is `det (H x)`;
* `TauCeti.mongeAmpereMeasure_withDensity_eq_singularPart_add_withDensity`,
  `TauCeti.mongeAmpereMeasure_eq_singularPart_add_withDensity` and
  `TauCeti.exists_mongeAmpereMeasure_eq_singularPart_add_withDensity` — **the Lebesgue
  decomposition** `MA_{f, g μ} = (MA_{f, g μ})ˢ + g (∇F x) det (H x) dx`, and its case
  `MA_f = (MA_f)ˢ + det (H x) dx`;
* `TauCeti.ae_eq_indicator_ofReal_det_of_mongeAmpereMeasure_eq_withDensity` — an Aleksandrov
  solution of `det D²f = g` satisfies `det (H x) = g x` almost everywhere;
* `TauCeti.rnDeriv_ae_eq_indicator_ofReal_det_mul_rnDeriv_of_mongeAmpereMeasure_eq` — **the
  Jacobian equation**: a weak solution of the transport problem from `g₀ dx` to `g₁ dx` satisfies
  `g₀ x = g₁ (∇F x) det (H x)` almost everywhere.

## References

* C. E. Gutiérrez, *The Monge–Ampère Equation*, 2nd ed., Progress in Nonlinear Differential
  Equations and Their Applications 89, Birkhäuser, 2016, §1.1, for the Monge–Ampère measure.
* A. Figalli, *The Monge–Ampère Equation and Its Applications*, Zurich Lectures in Advanced
  Mathematics, EMS, 2017, §2.1.
* L. C. Evans and R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised ed.,
  CRC Press, 2015, §6.4, for Alexandrov's theorem and the splitting of the Hessian measure of a
  convex function into absolutely continuous and singular parts.
* R. J. McCann, *A convexity principle for interacting gases*, Adv. Math. 128 (1997), 153–179,
  Theorem 4.4, for the Jacobian equation of a transport map given by a convex gradient.
* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer, 2009, Chapter 11.
-/

public section

namespace TauCeti

open MeasureTheory Measure Set Filter Metric Module Asymptotics
open scoped Topology ENNReal InnerProductSpace Pointwise Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal}

omit [FiniteDimensional ℝ E] in
/-- If the subgradients of `f` at the points of `closedBall x r` follow `y + A (x' - x)` up to
`ε ‖x' - x‖`, then the subgradient image of the ball lies in `y + r • (A (closedBall 0 1))_ε`. -/
private theorem subgradientImage_closedBall_subset {x y : E} {A : E →L[ℝ] E} {ε r : ℝ}
    (hε : 0 ≤ ε) (hr : 0 < r)
    (h : ∀ x' ∈ closedBall x r, ∀ y' ∈ subdifferential (innerₗ E) f x',
      ‖y' - y - A (x' - x)‖ ≤ ε * ‖x' - x‖) :
    subgradientImage (innerₗ E) f (closedBall x r) ⊆
      (fun w => y + r • w) '' cthickening ε (A '' closedBall 0 1) := by
  intro y' hy'
  obtain ⟨x', hx', hy'⟩ := (mem_subgradientImage_iff _).1 hy'
  have hx'r : ‖x' - x‖ ≤ r := by rwa [mem_closedBall, dist_eq_norm] at hx'
  refine ⟨r⁻¹ • (y' - y), ?_, by simp [smul_smul, hr.ne']⟩
  refine mem_cthickening_of_dist_le _ (A (r⁻¹ • (x' - x))) _ _ (mem_image_of_mem _ ?_) ?_
  · rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
    exact inv_mul_le_one_of_le₀ hx'r hr.le
  · rw [dist_eq_norm, map_smul, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr,
      sub_sub]
    calc r⁻¹ * ‖y' - (y + A (x' - x))‖ ≤ r⁻¹ * (ε * r) := by
          gcongr
          rw [← sub_sub]
          exact (h x' hx' y' hy').trans (by gcongr)
      _ = ε := by field_simp

/-- Let `f` be convex, with real representative `F`, and let `closedBall x r` lie in the interior
of its effective domain. If `F - ⟪·, p⟫` takes at some point of the ball a value smaller than at
every point of the sphere, then `p` is a subgradient of `f` at a point of the ball. -/
private theorem mem_subgradientImage_closedBall_of_forall_lt
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥) {x p x₀ : E} {r : ℝ}
    (hKD : closedBall x r ⊆ interior {x | f x ≠ ⊤}) (hx₀ : x₀ ∈ closedBall x r)
    (hlt : ∀ x' ∈ closedBall x r \ ball x r,
      (f x₀).toReal - ⟪x₀, p⟫_ℝ < (f x').toReal - ⟪x', p⟫_ℝ) :
    p ∈ subgradientImage (innerₗ E) f (closedBall x r) := by
  -- `F - ⟪·, p⟫` attains its minimum over the closed ball at a point `x₁` of the open ball.
  have hcont : ContinuousOn (fun x' => (f x').toReal - ⟪x', p⟫_ℝ) (closedBall x r) :=
    ((convexOn_toReal hf hbot).continuousOn_interior.mono hKD).sub
      (continuous_id.inner continuous_const).continuousOn
  obtain ⟨x₁, hx₁, hmin⟩ := (isCompact_closedBall x r).exists_isMinOn_mem_subset hcont hx₀ hlt
  -- A local minimum of the convex function `F - ⟪·, p⟫` is a global one, so `p ∈ ∂f(x₁)`.
  have hx₁D : x₁ ∈ interior {x | f x ≠ ⊤} := hKD (ball_subset_closedBall hx₁)
  have hloc : ∀ᶠ x' in 𝓝[{x | f x ≠ ⊤}] x₁,
      (f x₁).toReal + (innerₗ E).flip p (x' - x₁) ≤ (f x').toReal := by
    refine nhdsWithin_le_nhds (mem_of_superset (isOpen_ball.mem_nhds hx₁) fun x' hx' => ?_)
    have := isMinOn_iff.1 hmin x' (ball_subset_closedBall hx')
    have hℓ : (innerₗ E).flip p (x' - x₁) = ⟪x', p⟫_ℝ - ⟪x₁, p⟫_ℝ := by
      rw [LinearMap.flip_apply, innerₗ_apply_apply, inner_sub_left]
    simp only [mem_ofPred_eq, hℓ]
    linarith
  have hglob := (convexOn_toReal hf hbot).add_le_of_eventually_add_le
    (interior_subset hx₁D) _ hloc
  refine (mem_subgradientImage_iff _).2 ⟨x₁, ball_subset_closedBall hx₁, ?_⟩
  exact (mem_subdifferential_iff_forall_toReal_add_le (innerₗ E) hbot (interior_subset hx₁D)).2
    fun x' hx' => by
      have := hglob x' hx'
      rwa [LinearMap.flip_apply] at this

/-- Let `f` be convex, finite near `x`, with a second-order expansion
`F x' = F x + ⟪y, x' - x⟫ + ⟪A (x' - x), x' - x⟫ / 2 + o(‖x' - x‖ ^ 2)` for a positive `A` with
nonzero determinant. Then for every `s < 1` and every small `r > 0`, the set
`y + r • A (closedBall 0 s)` consists of subgradients of `f` at points of `closedBall x r`. -/
private theorem eventually_image_subset_subgradientImage_closedBall
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥) {x y : E}
    (hx : x ∈ interior {x | f x ≠ ⊤}) {A : E →L[ℝ] E} (hA : A.IsPositive) (hdet : A.det ≠ 0)
    (hT : (fun x' => (f x').toReal - (f x).toReal - ⟪y, x' - x⟫_ℝ - ⟪A (x' - x), x' - x⟫_ℝ / 2)
      =o[𝓝 x] fun x' => ‖x' - x‖ ^ 2) {s : ℝ} (hs : s < 1) :
    ∀ᶠ r in 𝓝[>] 0, (fun w => y + r • w) '' (A '' closedBall 0 s) ⊆
      subgradientImage (innerₗ E) f (closedBall x r) := by
  obtain ⟨c, hc, hcA⟩ := ((ContinuousLinearMap.isPositive_toLinearMap_iff A).2
    hA).exists_pos_mul_norm_sq_le_re_inner
      (not_not.1 (mt LinearMap.det_eq_zero_iff_ker_ne_bot.2 hdet))
  simp only [RCLike.re_to_real, ContinuousLinearMap.coe_coe] at hcA
  set η := 1 - s
  have hη : 0 < η := sub_pos.2 hs
  set δ := c * η ^ 2 / 8
  have hδ : 0 < δ := by positivity
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1
    ((hT.bound hδ).and (isOpen_interior.mem_nhds hx))
  filter_upwards [Ioo_mem_nhdsGT hρ] with r hr
  rintro _ ⟨_, ⟨z', hz', rfl⟩, rfl⟩
  set z := r • z'
  set p := y + A z
  have hpz : y + r • A z' = p := by simp [p, z]
  dsimp only
  rw [hpz]
  have hz : ‖z‖ ≤ s * r := by
    rw [mem_closedBall, dist_zero_right] at hz'
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, mul_comm]
    exact mul_le_mul_of_nonneg_right hz' hr.1.le
  have hsr : s * r ≤ r := by nlinarith [hr.1, norm_nonneg z]
  have hKD : closedBall x r ⊆ interior {x | f x ≠ ⊤} := fun x' hx' =>
    (hball ((mem_closedBall.1 hx').trans_lt hr.2)).2
  -- The increment of `g = F - ⟪·, p⟫` from `x` to `x + h` is
  -- `⟪A (h - z), h - z⟫ / 2 - ⟪A z, z⟫ / 2` up to `δ ‖h‖ ^ 2`.
  set g : E → ℝ := fun x' => (f x').toReal - ⟪x', p⟫_ℝ
  have hincr : ∀ x' ∈ closedBall x r, |g x' - g x - (⟪A (x' - x - z), x' - x - z⟫_ℝ / 2 -
      ⟪A z, z⟫_ℝ / 2)| ≤ δ * ‖x' - x‖ ^ 2 := by
    intro x' hx'
    have hb := (hball ((mem_closedBall.1 hx').trans_lt hr.2)).1
    rw [norm_pow, norm_norm, Real.norm_eq_abs] at hb
    have hsym : ⟪A z, x' - x⟫_ℝ = ⟪A (x' - x), z⟫_ℝ := by
      rw [hA.inner_left_eq_inner_right, real_inner_comm]
    have hexp : ⟪A (x' - x - z), x' - x - z⟫_ℝ =
        ⟪A (x' - x), x' - x⟫_ℝ - 2 * ⟪A (x' - x), z⟫_ℝ + ⟪A z, z⟫_ℝ := by
      generalize x' - x = h at hsym ⊢
      rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right, hsym]
      ring
    have hpx : ⟪x', p⟫_ℝ - ⟪x, p⟫_ℝ = ⟪y, x' - x⟫_ℝ + ⟪A (x' - x), z⟫_ℝ := by
      rw [← inner_sub_left, inner_add_right, ← hsym, real_inner_comm y, real_inner_comm (A z)]
    simp only [g]
    convert hb using 2
    linarith
  -- On the sphere `g` exceeds its value at `x + z`.
  have hlt : ∀ x' ∈ closedBall x r \ ball x r, g (x + z) < g x' := by
    rintro x' ⟨hx', hx'b⟩
    have hnorm : ‖x' - x‖ = r := by
      rw [← dist_eq_norm]
      exact le_antisymm (mem_closedBall.1 hx') (not_lt.1 hx'b)
    have hzr : x + z ∈ closedBall x r := by
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
      exact hz.trans hsr
    have h₁ := hincr _ hzr
    have h₂ := hincr x' hx'
    rw [add_sub_cancel_left, sub_self, map_zero, inner_zero_left, zero_div, zero_sub] at h₁
    have hηr : η * r ≤ ‖x' - x - z‖ := by
      have := norm_sub_norm_le (x' - x) z
      rw [hnorm] at this
      simp only [η]
      linarith
    have hq := hcA (x' - x - z)
    have hq' : c * (η * r) ^ 2 ≤ c * ‖x' - x - z‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_pos hη hr.1).le hηr 2) hc.le
    have hzr' : ‖z‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hz.trans hsr) 2
    have hδz : δ * ‖z‖ ^ 2 ≤ δ * r ^ 2 := mul_le_mul_of_nonneg_left hzr' hδ.le
    have hδr : δ * r ^ 2 = c * (η * r) ^ 2 / 8 := by simp only [δ]; ring
    have hpos : 0 < c * (η * r) ^ 2 := by have := hr.1; positivity
    rw [abs_le] at h₁ h₂
    rw [hnorm] at h₂
    linarith [h₁.2, h₂.1]
  exact mem_subgradientImage_closedBall_of_forall_lt hf hbot hKD
    (mem_closedBall.2 (by rw [dist_eq_norm, add_sub_cancel_left]; exact hz.trans hsr)) hlt

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **The density of the Monge–Ampère measure at a point of second-order differentiability.** Let
`f : E → EReal` be convex (convex real epigraph, never `⊥`) and `x` an interior point of its
effective domain at which the subdifferential has the first-order expansion
`y' = y + A (x' - x) + o(‖x' - x‖)`, uniformly over the subgradients `y'` at points `x'` near
`x`. Then for every additive Haar measure `μ`, the Aleksandrov Monge–Ampère measure of `f` has
density `det A` at `x`: `MA_f(closedBall x r) / μ(closedBall x r) → det A` as `r → 0⁺`. -/
theorem tendsto_mongeAmpereMeasure_closedBall_div (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2})
    (hbot : ∀ x, f x ≠ ⊥) {x y : E} (hx : x ∈ interior {x | f x ≠ ⊤}) {A : E →L[ℝ] E}
    (hA : ∀ ε > 0, ∀ᶠ x' in 𝓝 x, ∀ y' ∈ subdifferential (innerₗ E) f x',
      ‖y' - y - A (x' - x)‖ ≤ ε * ‖x' - x‖) :
    Tendsto (fun r => mongeAmpereMeasure μ f (closedBall x r) / μ (closedBall x r)) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal A.det)) := by
  have hne := eventually_nonempty_subdifferential hf hbot (mem_interior_iff_mem_nhds.1 hx)
  have hpos := isPositive_of_forall_mem_subdifferential_norm_sub_le hne hA
  have hdet0 : 0 ≤ A.det := ((ContinuousLinearMap.isPositive_toLinearMap_iff A).2 hpos).det_nonneg
  have hB0 : μ (closedBall (0 : E) 1) ≠ 0 := (measure_closedBall_pos μ 0 one_pos).ne'
  have hBtop : μ (closedBall (0 : E) 1) ≠ ∞ := measure_closedBall_lt_top.ne
  have hMA : ∀ r, mongeAmpereMeasure μ f (closedBall x r) =
      μ (subgradientImage (innerₗ E) f (closedBall x r ∩ interior {x | f x ≠ ⊤})) := fun r =>
    mongeAmpereMeasure_apply μ hf hbot AbsolutelyContinuous.rfl measurableSet_closedBall
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · -- Lower bound: `y + r • A (closedBall 0 s)` consists of subgradients at points of the ball.
    have hdet : A.det ≠ 0 := fun h => by simp [h] at ha
    have hlim : Tendsto (fun s : ℝ => ENNReal.ofReal (A.det * s ^ finrank ℝ E)) (𝓝[<] 1)
        (𝓝 (ENNReal.ofReal A.det)) := by
      have hc : Continuous fun s : ℝ => ENNReal.ofReal (A.det * s ^ finrank ℝ E) :=
        ENNReal.continuous_ofReal.comp (continuous_const.mul (continuous_pow _))
      simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
    obtain ⟨s, hsa, hs⟩ := ((hlim.eventually (lt_mem_nhds ha)).and
      (Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1))).exists
    have hT := isLittleO_of_forall_mem_subdifferential_norm_sub_le hne hA
    obtain ⟨ρ, hρ, hρD⟩ := nhds_basis_closedBall.mem_iff.1 (isOpen_interior.mem_nhds hx)
    filter_upwards [eventually_image_subset_subgradientImage_closedBall hf hbot hx hpos hdet
      hT hs.2, Ioo_mem_nhdsGT hρ] with r hsub hr
    have hK : μ (A '' closedBall 0 s) / μ (closedBall 0 1) =
        ENNReal.ofReal (A.det * s ^ finrank ℝ E) := by
      rw [addHaar_image_continuousLinearMap, addHaar_closedBall' μ 0 hs.1.le,
        abs_of_nonneg hdet0, ← mul_assoc, ← ENNReal.ofReal_mul hdet0,
        ENNReal.mul_div_cancel_right hB0 hBtop]
    calc a < ENNReal.ofReal (A.det * s ^ finrank ℝ E) := hsa
      _ = μ ((fun w => y + r • w) '' (A '' closedBall 0 s)) / μ (closedBall x r) := by
        rw [addHaar_image_add_smul_div_addHaar_closedBall μ x y hr.1, hK]
      _ ≤ mongeAmpereMeasure μ f (closedBall x r) / μ (closedBall x r) := by
        rw [hMA, inter_eq_left.2 ((closedBall_subset_closedBall hr.2.le).trans hρD)]
        exact ENNReal.div_le_div_right (measure_mono hsub) _
  · -- Upper bound: the subgradient image of the ball lies in `y + r • (A (closedBall 0 1))_ε`.
    set K := A '' closedBall (0 : E) 1
    have hK : IsCompact K := (isCompact_closedBall 0 1).image A.continuous
    have hμK : μ K / μ (closedBall 0 1) = ENNReal.ofReal A.det := by
      rw [addHaar_image_continuousLinearMap, abs_of_nonneg hdet0,
        ENNReal.mul_div_cancel_right hB0 hBtop]
    have hlim : Tendsto (fun ε => μ (cthickening ε K) / μ (closedBall 0 1)) (𝓝[>] 0)
        (𝓝 (ENNReal.ofReal A.det)) := by
      rw [← hμK]
      exact (ENNReal.Tendsto.div_const (tendsto_measure_cthickening_of_isCompact hK)
        (Or.inr hB0)).mono_left nhdsWithin_le_nhds
    obtain ⟨ε, hεb, hε⟩ := ((hlim.eventually (gt_mem_nhds hb)).and self_mem_nhdsWithin).exists
    obtain ⟨ρ, hρ, hρA⟩ := Metric.eventually_nhds_iff.1 (hA ε hε)
    filter_upwards [Ioo_mem_nhdsGT hρ] with r hr
    calc mongeAmpereMeasure μ f (closedBall x r) / μ (closedBall x r)
        ≤ μ ((fun w => y + r • w) '' cthickening ε K) / μ (closedBall x r) := by
          rw [hMA]
          refine ENNReal.div_le_div_right (measure_mono
            ((subgradientImage_mono _ inter_subset_left).trans ?_)) _
          exact subgradientImage_closedBall_subset (le_of_lt hε) hr.1 fun x' hx' =>
            hρA ((mem_closedBall.1 hx').trans_lt hr.2)
      _ = μ (cthickening ε K) / μ (closedBall 0 1) :=
          addHaar_image_add_smul_div_addHaar_closedBall μ x y hr.1 _
      _ < b := hεb

/-- If almost every point `x` of the interior `D` of the effective domain has a first-order
expansion of the subdifferential with derivative `H x`, then there is a measurable `S ⊆ D` of full
measure in `D` on which the subdifferential is the single gradient, with the expansion centred at
the gradient and `H x` positive, and on which `H` agrees with a measurable map. -/
theorem exists_measurableSet_ae_eq_interior_subdifferential_eq_gradient
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥) {H : E → E →L[ℝ] E}
    (hH : ∀ᵐ x ∂μ, x ∈ interior {x | f x ≠ ⊤} → ∃ y, ∀ ε > 0, ∀ᶠ x' in 𝓝 x,
      ∀ y' ∈ subdifferential (innerₗ E) f x', ‖y' - y - H x (x' - x)‖ ≤ ε * ‖x' - x‖) :
    ∃ S, MeasurableSet S ∧ S ⊆ interior {x | f x ≠ ⊤} ∧ interior {x | f x ≠ ⊤} =ᵐ[μ] S ∧
      (∀ x ∈ S, subdifferential (innerₗ E) f x = {(∇ fun x' => (f x').toReal) x} ∧
        (H x).IsPositive ∧ ∀ ε > 0, ∀ᶠ x' in 𝓝 x, ∀ y' ∈ subdifferential (innerₗ E) f x',
          ‖y' - (∇ fun x' => (f x').toReal) x - H x (x' - x)‖ ≤ ε * ‖x' - x‖) ∧
      ∃ H' : E → E →L[ℝ] E, Measurable H' ∧ ∀ x ∈ S, H x = H' x := by
  set D := interior {x | f x ≠ ⊤}
  -- Remove from `D` a measurable null set `N` containing the points without an expansion.
  set P : Set E := {x | x ∈ D ∧ ∃ y, ∀ ε > 0, ∀ᶠ x' in 𝓝 x,
    ∀ y' ∈ subdifferential (innerₗ E) f x', ‖y' - y - H x (x' - x)‖ ≤ ε * ‖x' - x‖}
  set N := toMeasurable μ (D \ P)
  have hN : μ N = 0 := by
    rw [measure_toMeasurable]
    exact measure_eq_zero_iff_ae_notMem.2 (hH.mono fun x hx hx' => hx'.2 ⟨hx'.1, hx hx'.1⟩)
  have hS₀m : MeasurableSet (D \ N) := measurableSet_interior.diff (measurableSet_toMeasurable _ _)
  have hS₀ : ∀ x ∈ D \ N, subdifferential (innerₗ E) f x = {(∇ fun x' => (f x').toReal) x} ∧
      (H x).IsPositive ∧ ∀ ε > 0, ∀ᶠ x' in 𝓝 x, ∀ y' ∈ subdifferential (innerₗ E) f x',
        ‖y' - (∇ fun x' => (f x').toReal) x - H x (x' - x)‖ ≤ ε * ‖x' - x‖ := fun x hx => by
    obtain ⟨-, y, hy⟩ : x ∈ P :=
      by_contra fun h => hx.2 (subset_toMeasurable _ _ ⟨hx.1, h⟩)
    have hne := eventually_nonempty_subdifferential hf hbot (mem_interior_iff_mem_nhds.1 hx.1)
    obtain rfl := (hasGradientAt_toReal_of_forall_mem_subdifferential_norm_sub_le hne hy).gradient
    exact ⟨subdifferential_eq_singleton_gradient_of_forall_mem_subdifferential_norm_sub_le hne hy,
      isPositive_of_forall_mem_subdifferential_norm_sub_le hne hy, hy⟩
  -- `H` is the derivative of the gradient within `D \ N`, so it is a.e.-measurable there; remove
  -- a further measurable null set `M` off which it agrees with a measurable map `H'`.
  have hHm := aemeasurable_fderivWithin μ hS₀m fun x hx =>
    hasFDerivWithinAt_gradient_toReal_of_forall_mem_subdifferential_norm_sub_le
      (fun x' hx' => by rw [(hS₀ x' hx').1]; exact mem_singleton _) (hS₀ x hx).2.2
  set M := toMeasurable μ {x | x ∈ D \ N ∧ H x ≠ hHm.mk H x}
  have hM : μ M = 0 := by
    rw [measure_toMeasurable]
    exact measure_eq_zero_iff_ae_notMem.2 (((ae_restrict_iff' hS₀m).1 hHm.ae_eq_mk).mono
      fun x hx hx' => hx'.2 (hx hx'.1))
  have hSD : (D \ N) \ M ⊆ D := sdiff_subset.trans sdiff_subset
  have hDS : D \ ((D \ N) \ M) ⊆ N ∪ M := fun x hx => by
    by_cases hxN : x ∈ N
    · exact Or.inl hxN
    · exact Or.inr (by_contra fun h => hx.2 ⟨⟨hx.1, hxN⟩, h⟩)
  refine ⟨(D \ N) \ M, hS₀m.diff (measurableSet_toMeasurable _ _), hSD,
    ae_eq_set.2 ⟨measure_mono_null hDS (measure_union_null hN hM),
      by rw [sdiff_eq_empty.2 hSD, measure_empty]⟩,
    fun x hx => hS₀ x hx.1, hHm.mk H, hHm.measurable_mk,
    fun x hx => by_contra fun h => hx.2 (subset_toMeasurable _ _ ⟨hx.1, h⟩)⟩

/-- The weighted Monge–Ampère measure `MA_{f, g μ}` is the sum of a measure singular with respect
to `μ` and of `μ` with the a.e.-measurable density `det (H x) * g (∇F x)` on the interior `D` of
the effective domain. Off a measurable set `S` of full measure in `D`, `MA_{f, g μ}` is carried by
the null set `D \ S`; on `S` it is computed by `withDensity_image_gradient_eq_setLIntegral`. -/
private theorem exists_mongeAmpereMeasure_withDensity_eq_add_withDensity
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥) {H : E → E →L[ℝ] E}
    (hH : ∀ᵐ x ∂μ, x ∈ interior {x | f x ≠ ⊤} → ∃ y, ∀ ε > 0, ∀ᶠ x' in 𝓝 x,
      ∀ y' ∈ subdifferential (innerₗ E) f x', ‖y' - y - H x (x' - x)‖ ≤ ε * ‖x' - x‖)
    {g : E → ℝ≥0∞} (hg : Measurable g) :
    ∃ s : Measure E, s ⟂ₘ μ ∧
      AEMeasurable ((interior {x | f x ≠ ⊤}).indicator fun x =>
        ENNReal.ofReal (H x).det * g ((∇ fun x' => (f x').toReal) x)) μ ∧
      mongeAmpereMeasure (μ.withDensity g) f = s + μ.withDensity
        ((interior {x | f x ≠ ⊤}).indicator fun x =>
          ENNReal.ofReal (H x).det * g ((∇ fun x' => (f x').toReal) x)) := by
  set D := interior {x | f x ≠ ⊤}
  set G := ∇ fun x' => (f x').toReal
  set φ : E → ℝ≥0∞ := fun x => ENNReal.ofReal (H x).det * g (G x)
  set ν := μ.withDensity g
  have hν : ν ≪ μ := withDensity_absolutelyContinuous μ g
  obtain ⟨S, hSm, hSD, hDS, hS, H', hH'm, hHS⟩ :=
    exists_measurableSet_ae_eq_interior_subdifferential_eq_gradient μ hf hbot hH
  have hdet : Measurable fun x => (H' x).det :=
    ContinuousLinearMap.continuous_det.measurable.comp hH'm
  have hφ : AEMeasurable (D.indicator φ) μ := by
    refine (aemeasurable_indicator_iff measurableSet_interior).2 ?_
    rw [restrict_congr_set hDS]
    refine ((ENNReal.measurable_ofReal.comp hdet).mul
      (hg.comp (measurable_gradient fun x' => (f x').toReal))).aemeasurable.congr ?_
    filter_upwards [ae_restrict_mem hSm] with x hx
    simp only [φ, G, Pi.mul_apply, Function.comp_apply, hHS x hx]
  -- On `S` the Monge–Ampère measure has density `φ`.
  have hmain : (mongeAmpereMeasure ν f).restrict S = (μ.restrict S).withDensity φ := by
    ext s hs
    have ht : MeasurableSet (s ∩ S) := hs.inter hSm
    have himage : subgradientImage (innerₗ E) f (s ∩ S ∩ D) = G '' (s ∩ S) := by
      rw [inter_eq_left.2 (inter_subset_right.trans hSD)]
      ext y
      simp only [mem_subgradientImage_iff, mem_image]
      refine exists_congr fun x => and_congr_right fun hx => ?_
      rw [(hS x hx.2).1, mem_singleton_iff, eq_comm]
    have htZ : s ∩ S ∩ {x | (H x).det ≠ 0} = s ∩ S ∩ {x | (H' x).det ≠ 0} := by
      ext x
      simp only [mem_inter_iff, mem_ofPred_eq]
      exact and_congr_right fun hx => by rw [hHS x hx.2]
    rw [restrict_apply hs, mongeAmpereMeasure_apply ν hf hbot hν ht, himage,
      withDensity_apply _ hs, restrict_restrict hs]
    exact withDensity_image_gradient_eq_setLIntegral μ hf ht
      (htZ ▸ ht.inter ((measurableSet_singleton 0).compl.preimage hdet))
      (fun x hx => hS x hx.2) g
  -- Off `S`, the Monge–Ampère measure is carried by the `μ`-null set `D \ S`.
  refine ⟨(mongeAmpereMeasure ν f).restrict Sᶜ, ⟨S ∪ Dᶜ, hSm.union measurableSet_interior.compl,
    ?_, ?_⟩, hφ, ?_⟩
  · rw [restrict_apply (hSm.union measurableSet_interior.compl)]
    exact measure_mono_null (fun x hx => hx.1.resolve_left hx.2)
      (mongeAmpereMeasure_compl_interior ν)
  · rw [compl_union, compl_compl, inter_comm, ← Set.sdiff_eq]
    exact (ae_eq_set.1 hDS).1
  · rw [withDensity_indicator measurableSet_interior, restrict_congr_set hDS, ← hmain, add_comm,
      restrict_add_restrict_compl hSm]

/-- **The density of the weighted Monge–Ampère measure.** Let `f : E → EReal` be convex (convex
real epigraph, never `⊥`) with `D` the interior of its effective domain and real representative
`F`, and let `H x` be, for almost every `x ∈ D`, a first-order expansion of the subdifferential of
`f` at `x`: `y' = y + H x (x' - x) + o(‖x' - x‖)` for some `y`, uniformly over the subgradients
`y'` at points `x'` near `x`. By Alexandrov's theorem such `H` exists, and `H x` is then the
Alexandrov Hessian of `f` at `x`. For every additive Haar measure `μ` and measurable `g`, the
Radon–Nikodym derivative of the Monge–Ampère measure `MA_{f, g μ}(s) = ∫_{∂f(s ∩ D)} g dμ` with
respect to `μ` is `det (H x) * g (∇F x)` on `D` and `0` off `D`, almost everywhere. -/
theorem rnDeriv_mongeAmpereMeasure_withDensity_ae_eq (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2})
    (hbot : ∀ x, f x ≠ ⊥) {H : E → E →L[ℝ] E}
    (hH : ∀ᵐ x ∂μ, x ∈ interior {x | f x ≠ ⊤} → ∃ y, ∀ ε > 0, ∀ᶠ x' in 𝓝 x,
      ∀ y' ∈ subdifferential (innerₗ E) f x', ‖y' - y - H x (x' - x)‖ ≤ ε * ‖x' - x‖)
    {g : E → ℝ≥0∞} (hg : Measurable g) :
    (mongeAmpereMeasure (μ.withDensity g) f).rnDeriv μ =ᵐ[μ]
      (interior {x | f x ≠ ⊤}).indicator fun x =>
        ENNReal.ofReal (H x).det * g ((∇ fun x' => (f x').toReal) x) := by
  obtain ⟨s, hs, hφ, hadd⟩ :=
    exists_mongeAmpereMeasure_withDensity_eq_add_withDensity μ hf hbot hH hg
  exact (eq_rnDeriv₀ hφ hs hadd).symm

/-- **The density of the Monge–Ampère measure is the determinant of the Alexandrov Hessian.** Let
`f : E → EReal` be convex (convex real epigraph, never `⊥`), and let `H x` be, for almost every
`x` in the interior `D` of the effective domain, a first-order expansion of the subdifferential of
`f` at `x`: `y' = y + H x (x' - x) + o(‖x' - x‖)` for some `y`, uniformly over the subgradients
`y'` at points `x'` near `x`. By Alexandrov's theorem such `H` exists, and `H x` is then the
Alexandrov Hessian of `f` at `x`. For every additive Haar measure `μ`, the Radon–Nikodym
derivative of the Aleksandrov Monge–Ampère measure `MA_f` with respect to `μ` is `det (H x)` on
`D` and `0` off `D`, almost everywhere. This is the case `g = 1` of
`rnDeriv_mongeAmpereMeasure_withDensity_ae_eq`. -/
theorem rnDeriv_mongeAmpereMeasure_ae_eq (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2})
    (hbot : ∀ x, f x ≠ ⊥) {H : E → E →L[ℝ] E}
    (hH : ∀ᵐ x ∂μ, x ∈ interior {x | f x ≠ ⊤} → ∃ y, ∀ ε > 0, ∀ᶠ x' in 𝓝 x,
      ∀ y' ∈ subdifferential (innerₗ E) f x', ‖y' - y - H x (x' - x)‖ ≤ ε * ‖x' - x‖) :
    (mongeAmpereMeasure μ f).rnDeriv μ =ᵐ[μ]
      (interior {x | f x ≠ ⊤}).indicator fun x => ENNReal.ofReal (H x).det := by
  simpa [withDensity_one] using
    rnDeriv_mongeAmpereMeasure_withDensity_ae_eq μ hf hbot hH (g := 1) measurable_const

/-- **Lebesgue decomposition of the weighted Monge–Ampère measure.** Let `f : E → EReal` be convex
(convex real epigraph, never `⊥`) with `D` the interior of its effective domain and real
representative `F`, and let `H x` be, for almost every `x ∈ D`, a first-order expansion of the
subdifferential of `f` at `x` (the Alexandrov Hessian, see
`rnDeriv_mongeAmpereMeasure_withDensity_ae_eq`). Then for every additive Haar measure `μ` and
measurable `g`, the Monge–Ampère measure weighted by `g μ` splits as
`MA_{f, g μ} = (MA_{f, g μ})ˢ + det (H x) g (∇F x) dx` on `D`, where `(MA_{f, g μ})ˢ` is the part
singular with respect to `μ`. -/
theorem mongeAmpereMeasure_withDensity_eq_singularPart_add_withDensity
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥) {H : E → E →L[ℝ] E}
    (hH : ∀ᵐ x ∂μ, x ∈ interior {x | f x ≠ ⊤} → ∃ y, ∀ ε > 0, ∀ᶠ x' in 𝓝 x,
      ∀ y' ∈ subdifferential (innerₗ E) f x', ‖y' - y - H x (x' - x)‖ ≤ ε * ‖x' - x‖)
    {g : E → ℝ≥0∞} (hg : Measurable g) :
    mongeAmpereMeasure (μ.withDensity g) f =
      (mongeAmpereMeasure (μ.withDensity g) f).singularPart μ +
        (μ.restrict (interior {x | f x ≠ ⊤})).withDensity fun x =>
          ENNReal.ofReal (H x).det * g ((∇ fun x' => (f x').toReal) x) := by
  obtain ⟨s, hs, hφ, hadd⟩ :=
    exists_mongeAmpereMeasure_withDensity_eq_add_withDensity μ hf hbot hH hg
  rw [withDensity_congr_ae hφ.ae_eq_mk] at hadd
  rw [← withDensity_indicator measurableSet_interior, withDensity_congr_ae hφ.ae_eq_mk,
    ← eq_singularPart hφ.measurable_mk hs hadd]
  exact hadd

/-- **Lebesgue decomposition of the Monge–Ampère measure.** Let `f : E → EReal` be convex
(convex real epigraph, never `⊥`) with `D` the interior of its effective domain, and let `H x` be,
for almost every `x ∈ D`, a first-order expansion of the subdifferential of `f` at `x` (the
Alexandrov Hessian, see `rnDeriv_mongeAmpereMeasure_ae_eq`). Then for every additive Haar measure
`μ`, the Aleksandrov Monge–Ampère measure splits as `MA_f = (MA_f)ˢ + det (H x) dx` on `D`, where
`(MA_f)ˢ` is the part singular with respect to `μ`. So the Alexandrov Hessian determines exactly
the absolutely continuous part of `MA_f`. This is the case `g = 1` of
`mongeAmpereMeasure_withDensity_eq_singularPart_add_withDensity`. -/
theorem mongeAmpereMeasure_eq_singularPart_add_withDensity
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥) {H : E → E →L[ℝ] E}
    (hH : ∀ᵐ x ∂μ, x ∈ interior {x | f x ≠ ⊤} → ∃ y, ∀ ε > 0, ∀ᶠ x' in 𝓝 x,
      ∀ y' ∈ subdifferential (innerₗ E) f x', ‖y' - y - H x (x' - x)‖ ≤ ε * ‖x' - x‖) :
    mongeAmpereMeasure μ f = (mongeAmpereMeasure μ f).singularPart μ +
      (μ.restrict (interior {x | f x ≠ ⊤})).withDensity fun x => ENNReal.ofReal (H x).det := by
  simpa [withDensity_one] using
    mongeAmpereMeasure_withDensity_eq_singularPart_add_withDensity μ hf hbot hH (g := 1)
      measurable_const

/-- **Lebesgue decomposition of the Monge–Ampère measure, with the Alexandrov Hessian.** For a
convex `f : E → EReal` (convex real epigraph, never `⊥`) and an additive Haar measure `μ`, there is
a map `H` giving, at almost every point `x` of the effective domain, the positive derivative of the
subdifferential of `f`, `y' = ∇F x + H x (x' - x) + o(‖x' - x‖)` with `F x = (f x).toReal`
(Alexandrov's theorem), and for any such `H` the Aleksandrov Monge–Ampère measure is
`MA_f = (MA_f)ˢ + det (H x) dx` on the interior of the effective domain. -/
theorem exists_mongeAmpereMeasure_eq_singularPart_add_withDensity
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥) :
    ∃ H : E → E →L[ℝ] E, (∀ᵐ x ∂μ, f x ≠ ⊤ → (H x).IsPositive ∧ ∀ ε > 0, ∀ᶠ x' in 𝓝 x,
      ∀ y' ∈ subdifferential (innerₗ E) f x',
        ‖y' - gradient (fun x' => (f x').toReal) x - H x (x' - x)‖ ≤ ε * ‖x' - x‖) ∧
      mongeAmpereMeasure μ f = (mongeAmpereMeasure μ f).singularPart μ +
        (μ.restrict (interior {x | f x ≠ ⊤})).withDensity fun x => ENNReal.ofReal (H x).det := by
  classical
  set P : E → (E →L[ℝ] E) → Prop := fun x A => A.IsPositive ∧ ∀ ε > 0, ∀ᶠ x' in 𝓝 x,
    ∀ y' ∈ subdifferential (innerₗ E) f x',
      ‖y' - gradient (fun x' => (f x').toReal) x - A (x' - x)‖ ≤ ε * ‖x' - x‖
  set H : E → E →L[ℝ] E := fun x => if h : ∃ A, P x A then h.choose else 0
  have hH : ∀ᵐ x ∂μ, f x ≠ ⊤ → P x (H x) := by
    filter_upwards [ae_existsUnique_isPositive_forall_mem_subdifferential_norm_sub_le
      (μ := μ) hf hbot] with x hx hfx
    have h : ∃ A, P x A := (hx hfx).exists
    simpa only [H, dite_eq_left h] using h.choose_spec
  refine ⟨H, hH, mongeAmpereMeasure_eq_singularPart_add_withDensity μ hf hbot ?_⟩
  filter_upwards [hH] with x hx hxD
  exact ⟨_, (hx (interior_subset hxD)).2⟩

/-- **An Aleksandrov solution solves the equation almost everywhere.** If the Aleksandrov
Monge–Ampère measure of a convex `f : E → EReal` (convex real epigraph, never `⊥`) is absolutely
continuous with an a.e.-measurable density `g`, that is, `f` is an Aleksandrov solution of
`det D²f = g`, then `det (H x) = g x` for almost every `x` in the interior `D` of the effective
domain, where `H` is the Alexandrov Hessian as in `rnDeriv_mongeAmpereMeasure_ae_eq`, and `g = 0`
almost everywhere off `D`. The converse fails: a cone has Alexandrov Hessian determinant `0` almost
everywhere but singular Monge–Ampère measure (`mongeAmpereMeasure_mul_norm_sub`). -/
theorem ae_eq_indicator_ofReal_det_of_mongeAmpereMeasure_eq_withDensity
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥) {H : E → E →L[ℝ] E}
    (hH : ∀ᵐ x ∂μ, x ∈ interior {x | f x ≠ ⊤} → ∃ y, ∀ ε > 0, ∀ᶠ x' in 𝓝 x,
      ∀ y' ∈ subdifferential (innerₗ E) f x', ‖y' - y - H x (x' - x)‖ ≤ ε * ‖x' - x‖)
    {g : E → ℝ≥0∞} (hg : AEMeasurable g μ) (hMA : mongeAmpereMeasure μ f = μ.withDensity g) :
    g =ᵐ[μ] (interior {x | f x ≠ ⊤}).indicator fun x => ENNReal.ofReal (H x).det := by
  have h := rnDeriv_withDensity₀ μ hg
  rw [← hMA] at h
  exact h.symm.trans (rnDeriv_mongeAmpereMeasure_ae_eq μ hf hbot hH)

/-- **The Monge–Ampère equation of a transport potential holds almost everywhere.** Let
`f : E → EReal` be convex (convex real epigraph, never `⊥`) with `D` the interior of its effective
domain and real representative `F`, and let `H x` be, for almost every `x ∈ D`, a first-order
expansion of the subdifferential of `f` at `x` (the Alexandrov Hessian, see
`rnDeriv_mongeAmpereMeasure_withDensity_ae_eq`). Let `μ` be an additive Haar measure, and let
`ν₁ ≪ μ` have a Lebesgue decomposition with respect to `μ` (for instance, be σ-finite). If the
Monge–Ampère measure of `f` weighted by `ν₁` is `ν₀`, that is, `f` is a weak solution of the
transport equation from `ν₀` to `ν₁`, then the densities `g₀ = dν₀/dμ` and `g₁ = dν₁/dμ`
satisfy the Jacobian equation `g₀ x = g₁ (∇F x) * det (H x)` for almost every `x ∈ D`, and
`g₀ = 0` almost everywhere off `D`. -/
theorem rnDeriv_ae_eq_indicator_ofReal_det_mul_rnDeriv_of_mongeAmpereMeasure_eq
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥) {H : E → E →L[ℝ] E}
    (hH : ∀ᵐ x ∂μ, x ∈ interior {x | f x ≠ ⊤} → ∃ y, ∀ ε > 0, ∀ᶠ x' in 𝓝 x,
      ∀ y' ∈ subdifferential (innerₗ E) f x', ‖y' - y - H x (x' - x)‖ ≤ ε * ‖x' - x‖)
    {ν₀ ν₁ : Measure E} [ν₁.HaveLebesgueDecomposition μ] (hν₁ : ν₁ ≪ μ)
    (hMA : mongeAmpereMeasure ν₁ f = ν₀) :
    ν₀.rnDeriv μ =ᵐ[μ] (interior {x | f x ≠ ⊤}).indicator fun x =>
      ENNReal.ofReal (H x).det * ν₁.rnDeriv μ ((∇ fun x' => (f x').toReal) x) := by
  have h := rnDeriv_mongeAmpereMeasure_withDensity_ae_eq μ hf hbot hH (measurable_rnDeriv ν₁ μ)
  rwa [withDensity_rnDeriv_eq ν₁ μ hν₁, hMA] at h

end TauCeti
