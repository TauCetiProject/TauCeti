/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Differentiability
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Convex functions with the same derivative differ by a constant

Two differentiable functions with the same derivative on a connected open set differ by a
constant there (`IsOpen.exists_eq_add_of_fderiv_eq`). This file proves the analogue for convex
functions, which are only differentiable almost everywhere: if two extended-real convex
functions `u v : E → EReal` are finite on a connected open set `Ω` and have the same derivative at
almost every point of `Ω`, then `u = v + c` on `Ω` for a real constant `c`.

This is the uniqueness of the convex potential in Brenier's theorem: the optimal transport map
`∇ u` determines `u` up to an additive constant on every connected open set carrying the source
law, as soon as that law charges every Lebesgue-positive subset of it.

The proof restricts `u` and `v` to lines. Where both functions have a common derivative `f'`, the
one-variable convexity inequalities along a line in direction `h` give
`slope u a b ≤ f' h ≤ slope v b c` for parameters `a < b < c`, and by continuity this cross-slope
inequality persists at every point of the closure of the common-derivative set. Letting the
slopes shrink, the right derivatives of the two restrictions agree, so their difference has
right derivative zero and is constant along the line. The difference is therefore locally
constant, hence constant on the connected set `Ω`. Only density of the common-derivative set is
used; in finite dimension Rademacher's theorem for convex functions
(`TauCeti.ae_eventually_ne_top_and_differentiableAt_toReal`) supplies it from an almost
everywhere hypothesis.

As elsewhere, a convex function `f : E → EReal` is one with convex real epigraph
`{(x, r) | f x ≤ r}` that never takes the value `⊥`, and its derivative is that of the real
representative `x ↦ (f x).toReal`.

## Main statements

* `IsOpen.exists_eq_add_of_subset_closure_hasFDerivAt_eq` — on a real normed space, convex
  functions finite and continuous on a connected open set `Ω` that have a common derivative on a
  dense subset of `Ω` differ by a constant on `Ω`;
* `IsOpen.exists_eq_add_of_fderiv_ae_eq` — in finite dimension, convex functions finite on a
  connected open set `Ω` whose derivatives agree `μ`-almost everywhere, for a measure `μ` with
  respect to which Lebesgue measure on `Ω` is absolutely continuous, differ by a constant on `Ω`;
* `IsOpen.exists_eq_add_of_gradient_ae_eq` — the same statement for gradients on a
  finite-dimensional real inner product space.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton Mathematical Series 28, 1970, §24 (one-sided
  derivatives of convex functions) and Theorem 25.5 (almost-everywhere differentiability).
* C. Villani, *Topics in Optimal Transportation*, Graduate Studies in Mathematics 58, 2003,
  Theorem 2.12, for the uniqueness of the Brenier potential.
-/

public section

namespace TauCeti

open Filter MeasureTheory Set
open scoped Topology Gradient

section OneDimensional

variable {φ ψ : ℝ → ℝ} {I : Set ℝ}

/-- If no slope of `φ` on an interval `[a, b]` exceeds a slope of `ψ` on an adjacent interval
`[b, c]`, then the right derivative of `φ` is at most that of `ψ`. -/
private theorem rightDeriv_le_of_slope_le (hI : IsOpen I) (hφ : ConvexOn ℝ I φ)
    (hψ : ConvexOn ℝ I ψ)
    (h : ∀ a b c, a ∈ I → c ∈ I → a < b → b < c → slope φ a b ≤ slope ψ b c) {b : ℝ}
    (hb : b ∈ I) : derivWithin φ (Ioi b) b ≤ derivWithin ψ (Ioi b) b := by
  have hbi : b ∈ interior I := hI.interior_eq.symm ▸ hb
  have hφd := hφ.hasDerivWithinAt_rightDeriv_of_mem_interior hbi
  have hψd := hψ.hasDerivWithinAt_rightDeriv_of_mem_interior hbi
  rw [hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi] at hφd hψd
  -- The right derivative of `φ` at `b` is at most every slope of `ψ` starting at `b`.
  refine ge_of_tendsto hψd ?_
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hI.mem_nhds hb), self_mem_nhdsWithin]
    with c hc (hbc : b < c)
  have hψc : ContinuousAt ψ b := (hψ.continuousOn hI).continuousAt (hI.mem_nhds hb)
  have hcont : Tendsto (fun b' => slope ψ b' c) (𝓝[>] b) (𝓝 (slope ψ b c)) := by
    simp only [slope_def_field]
    exact ((continuousAt_const.sub hψc).div (continuousAt_const.sub continuousAt_id)
      (sub_ne_zero.2 hbc.ne')).tendsto.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto_of_tendsto hφd hcont ?_
  filter_upwards [Ioo_mem_nhdsGT hbc] with b' hb'
  exact h b b' c hb hc hb'.1 hb'.2

/-- Two convex functions on an open interval whose slopes interlace in both directions differ by a
constant. -/
private theorem sub_eq_sub_of_slope_le (hI : IsOpen I) (hφ : ConvexOn ℝ I φ)
    (hψ : ConvexOn ℝ I ψ)
    (h₁ : ∀ a b c, a ∈ I → c ∈ I → a < b → b < c → slope φ a b ≤ slope ψ b c)
    (h₂ : ∀ a b c, a ∈ I → c ∈ I → a < b → b < c → slope ψ a b ≤ slope φ b c)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) (hst : s ≤ t) : φ t - ψ t = φ s - ψ s := by
  have hsub : Icc s t ⊆ I := hφ.1.ordConnected.out hs ht
  refine constant_of_has_deriv_right_zero
    (((hφ.continuousOn hI).sub (hψ.continuousOn hI)).mono hsub) (fun x hx => ?_) t ⟨hst, le_rfl⟩
  have hxI := hsub (Ico_subset_Icc_self hx)
  have hxi : x ∈ interior I := hI.interior_eq.symm ▸ hxI
  have hd := (hφ.hasDerivWithinAt_rightDeriv_of_mem_interior hxi).sub
    (hψ.hasDerivWithinAt_rightDeriv_of_mem_interior hxi)
  rw [le_antisymm (rightDeriv_le_of_slope_le hI hφ hψ h₁ hxI)
    (rightDeriv_le_of_slope_le hI hψ hφ h₂ hxI), sub_self] at hd
  exact hasDerivWithinAt_Ioi_iff_Ici.1 hd

end OneDimensional

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {u v : E → EReal} {Ω : Set E}

/-- The restriction of a convex function to the line `t ↦ y + t • h` is convex on the set of
parameters where it is finite. -/
private theorem convexOn_toReal_comp_line (hu : Convex ℝ {p : E × ℝ | u p.1 ≤ p.2})
    (hbot : ∀ x, u x ≠ ⊥) (y h : E) :
    ConvexOn ℝ {t : ℝ | u (y + t • h) ≠ ⊤} fun t => (u (y + t • h)).toReal := by
  have hline : (AffineMap.lineMap y (y + h) : ℝ → E) = fun t => y + t • h := by
    funext t
    rw [AffineMap.lineMap_apply_module', add_sub_cancel_left, add_comm]
  have := (convexOn_toReal hu hbot).comp_affineMap (AffineMap.lineMap y (y + h))
  rw [hline] at this
  exact this

/-- **The cross-slope inequality.** Let `u` and `v` be convex functions, finite and continuous on
an open set `Ω`, and suppose every point of `Ω` is a limit of points at which `u` and `v` have a
common derivative. Along a line `t ↦ x + t • h`, every slope of `u` on `[a, b]` is at most every
slope of `v` on `[b, c]`, provided the three points lie in `Ω`. -/
private theorem slope_le_slope_of_subset_closure (hu : Convex ℝ {p : E × ℝ | u p.1 ≤ p.2})
    (hubot : ∀ x, u x ≠ ⊥) (hv : Convex ℝ {p : E × ℝ | v p.1 ≤ p.2}) (hvbot : ∀ x, v x ≠ ⊥)
    (hΩ : IsOpen Ω) (huΩ : ∀ x ∈ Ω, u x ≠ ⊤) (hvΩ : ∀ x ∈ Ω, v x ≠ ⊤)
    (huc : ContinuousOn (fun x => (u x).toReal) Ω) (hvc : ContinuousOn (fun x => (v x).toReal) Ω)
    (hD : Ω ⊆ closure {x | ∃ f' : E →L[ℝ] ℝ, HasFDerivAt (fun x => (u x).toReal) f' x ∧
      HasFDerivAt (fun x => (v x).toReal) f' x})
    {x h : E} {a b c : ℝ} (ha : x + a • h ∈ Ω) (hb : x + b • h ∈ Ω) (hc : x + c • h ∈ Ω)
    (hab : a < b) (hbc : b < c) :
    slope (fun t => (u (x + t • h)).toReal) a b ≤ slope (fun t => (v (x + t • h)).toReal) b c := by
  -- Approach `x + b • h` through points `z` with a common derivative, moving the base point
  -- `x` to `z - b • h`.
  have := mem_closure_iff_nhdsWithin_neBot.1 (hD hb)
  have hz : Tendsto (fun z => z - b • h) (𝓝[{x | ∃ f' : E →L[ℝ] ℝ,
      HasFDerivAt (fun x => (u x).toReal) f' x ∧ HasFDerivAt (fun x => (v x).toReal) f' x}]
      (x + b • h)) (𝓝 x) := by
    have := (continuous_sub_right (b • h)).tendsto (x + b • h)
    rw [add_sub_cancel_right] at this
    exact this.mono_left nhdsWithin_le_nhds
  -- Both slopes are continuous in the base point.
  have hcont {w : E → EReal} (hwc : ContinuousOn (fun x => (w x).toReal) Ω) {t : ℝ}
      (ht : x + t • h ∈ Ω) :
      Tendsto (fun y => (w (y + t • h)).toReal) (𝓝 x) (𝓝 (w (x + t • h)).toReal) :=
    (ContinuousAt.comp (g := fun x => (w x).toReal) (f := fun y => y + t • h)
      (hwc.continuousAt (hΩ.mem_nhds ht))
      (continuous_id.add continuous_const).continuousAt).tendsto
  have hF : Tendsto (fun y => slope (fun t => (u (y + t • h)).toReal) a b) (𝓝 x)
      (𝓝 (slope (fun t => (u (x + t • h)).toReal) a b)) := by
    simp only [slope_def_field]
    exact ((hcont huc hb).sub (hcont huc ha)).div_const _
  have hG : Tendsto (fun y => slope (fun t => (v (y + t • h)).toReal) b c) (𝓝 x)
      (𝓝 (slope (fun t => (v (x + t • h)).toReal) b c)) := by
    simp only [slope_def_field]
    exact ((hcont hvc hc).sub (hcont hvc hb)).div_const _
  have hmem {t : ℝ} (ht : x + t • h ∈ Ω) : ∀ᶠ y in 𝓝 x, y + t • h ∈ Ω :=
    (continuous_id.add continuous_const).continuousAt.preimage_mem_nhds (hΩ.mem_nhds ht)
  refine le_of_tendsto_of_tendsto (hF.comp hz) (hG.comp hz) ?_
  filter_upwards [self_mem_nhdsWithin, hz.eventually (hmem ha), hz.eventually (hmem hb),
    hz.eventually (hmem hc)] with z ⟨f', hfu, hfv⟩ hza hzb hzc
  -- At the base point `y = z - b • h`, both restrictions are differentiable at `b` with
  -- derivative `f' h`, which separates the two slopes.
  have hzb' : z - b • h + b • h = z := sub_add_cancel z (b • h)
  have hline : HasDerivAt (fun t : ℝ => z - b • h + t • h) h b := by
    simpa using ((hasDerivAt_id b).smul_const h).const_add (z - b • h)
  rw [← hzb'] at hfu hfv
  have hdu : HasDerivAt (fun t => (u (z - b • h + t • h)).toReal) (f' h) b :=
    HasFDerivAt.comp_hasDerivAt (l := fun x => (u x).toReal) b hfu hline
  have hdv : HasDerivAt (fun t => (v (z - b • h + t • h)).toReal) (f' h) b :=
    HasFDerivAt.comp_hasDerivAt (l := fun x => (v x).toReal) b hfv hline
  exact ((convexOn_toReal_comp_line hu hubot _ h).slope_le_of_hasDerivAt (huΩ _ hza)
    (huΩ _ hzb) hab hdu).trans ((convexOn_toReal_comp_line hv hvbot _ h).le_slope_of_hasDerivAt
      (hvΩ _ hzb) (hvΩ _ hzc) hbc hdv)

/-- **Convex functions with the same derivative on a dense set differ by a constant.** Let
`u v : E → EReal` be convex functions (convex real epigraph, never `⊥`) on a real normed space,
finite on a connected open set `Ω`, with real representatives continuous on `Ω`. If every point of
`Ω` is a limit of points at which the real representatives of `u` and `v` have a common derivative,
then `u = v + c` on `Ω` for some real constant `c`. -/
theorem _root_.IsOpen.exists_eq_add_of_subset_closure_hasFDerivAt_eq (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hu : Convex ℝ {p : E × ℝ | u p.1 ≤ p.2}) (hubot : ∀ x, u x ≠ ⊥)
    (hv : Convex ℝ {p : E × ℝ | v p.1 ≤ p.2}) (hvbot : ∀ x, v x ≠ ⊥)
    (huΩ : ∀ x ∈ Ω, u x ≠ ⊤) (hvΩ : ∀ x ∈ Ω, v x ≠ ⊤)
    (huc : ContinuousOn (fun x => (u x).toReal) Ω) (hvc : ContinuousOn (fun x => (v x).toReal) Ω)
    (hD : Ω ⊆ closure {x | ∃ f' : E →L[ℝ] ℝ, HasFDerivAt (fun x => (u x).toReal) f' x ∧
      HasFDerivAt (fun x => (v x).toReal) f' x}) :
    ∃ c : ℝ, Ω.EqOn u fun x => v x + c := by
  have hD' : Ω ⊆ closure {x | ∃ f' : E →L[ℝ] ℝ, HasFDerivAt (fun x => (v x).toReal) f' x ∧
      HasFDerivAt (fun x => (u x).toReal) f' x} := by
    simpa only [and_comm] using hD
  -- The difference of the real representatives is locally constant on `Ω`: on a ball around `x`
  -- it is constant along each segment from `x`.
  have hloc : ∀ x ∈ Ω, ∀ᶠ y in 𝓝 x,
      (u y).toReal - (v y).toReal = (u x).toReal - (v x).toReal := by
    intro x hx
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hΩ x hx
    filter_upwards [Metric.ball_mem_nhds x hr] with y hy
    have hline : (AffineMap.lineMap x y : ℝ → E) = fun t => x + t • (y - x) := by
      funext t
      rw [AffineMap.lineMap_apply_module', add_comm]
    set I := {t : ℝ | x + t • (y - x) ∈ Metric.ball x r}
    have hIo : IsOpen I := Metric.isOpen_ball.preimage (by fun_prop)
    have hIc : Convex ℝ I := by
      have := (convex_ball x r).affine_preimage (AffineMap.lineMap x y)
      rwa [hline] at this
    have hIΩ {t : ℝ} (ht : t ∈ I) : x + t • (y - x) ∈ Ω := hball ht
    have hφ := (convexOn_toReal_comp_line hu hubot x (y - x)).subset
      (fun t ht => huΩ _ (hIΩ ht)) hIc
    have hψ := (convexOn_toReal_comp_line hv hvbot x (y - x)).subset
      (fun t ht => hvΩ _ (hIΩ ht)) hIc
    have hmid {a b c : ℝ} (ha : a ∈ I) (hc : c ∈ I) (hab : a < b) (hbc : b < c) : b ∈ I :=
      hIc.ordConnected.out ha hc ⟨hab.le, hbc.le⟩
    have key := sub_eq_sub_of_slope_le hIo hφ hψ
      (fun a b c ha hc hab hbc => slope_le_slope_of_subset_closure hu hubot hv hvbot hΩ huΩ hvΩ
        huc hvc hD (hIΩ ha) (hIΩ (hmid ha hc hab hbc)) (hIΩ hc) hab hbc)
      (fun a b c ha hc hab hbc => slope_le_slope_of_subset_closure hv hvbot hu hubot hΩ hvΩ huΩ
        hvc huc hD' (hIΩ ha) (hIΩ (hmid ha hc hab hbc)) (hIΩ hc) hab hbc)
      (s := 0) (t := 1) (by simpa [I] using hr) (by simpa [I, dist_eq_norm] using hy) zero_le_one
    simpa using key
  -- A locally constant function on a preconnected set is constant.
  rcases Ω.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨0, fun x hx => hx.elim⟩
  have := isPreconnected_iff_preconnectedSpace.1 hΩc
  have hlc : IsLocallyConstant fun x : Ω => (u x).toReal - (v x).toReal :=
    (IsLocallyConstant.iff_eventually_eq _).2 fun x =>
      (continuous_subtype_val.tendsto x).eventually (hloc x x.2)
  refine ⟨(u x₀).toReal - (v x₀).toReal, fun x hx => ?_⟩
  have hconst : (u x).toReal - (v x).toReal = (u x₀).toReal - (v x₀).toReal :=
    hlc.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨x₀, hx₀⟩
  dsimp only
  rw [← hconst]
  calc u x = ((v x).toReal + ((u x).toReal - (v x).toReal) : ℝ) := by
        rw [add_sub_cancel, EReal.coe_toReal (huΩ x hx) (hubot x)]
    _ = v x + ((u x).toReal - (v x).toReal : ℝ) := by
        rw [EReal.coe_add, EReal.coe_toReal (hvΩ x hx) (hvbot x)]

/-- **Convex functions with almost everywhere equal derivatives differ by a constant.** Let
`u v : E → EReal` be convex functions (convex real epigraph, never `⊥`) on a finite-dimensional
real normed space, finite on a connected open set `Ω`. Let `ρ` be an additive Haar measure and `μ`
a measure such that the restriction of `ρ` to `Ω` is absolutely continuous with respect to `μ`, as
when `μ` restricted to `Ω` is equivalent to Lebesgue measure on `Ω`. If the derivatives of the real
representatives of `u` and `v` agree `μ`-almost everywhere, then `u = v + c` on `Ω` for some real
constant `c`. -/
theorem _root_.IsOpen.exists_eq_add_of_fderiv_ae_eq [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] {ρ μ : Measure E} [ρ.IsAddHaarMeasure] (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hu : Convex ℝ {p : E × ℝ | u p.1 ≤ p.2}) (hubot : ∀ x, u x ≠ ⊥)
    (hv : Convex ℝ {p : E × ℝ | v p.1 ≤ p.2}) (hvbot : ∀ x, v x ≠ ⊥)
    (huΩ : ∀ x ∈ Ω, u x ≠ ⊤) (hvΩ : ∀ x ∈ Ω, v x ≠ ⊤) (hμ : ρ.restrict Ω ≪ μ)
    (h : fderiv ℝ (fun x => (u x).toReal) =ᵐ[μ] fderiv ℝ (fun x => (v x).toReal)) :
    ∃ c : ℝ, Ω.EqOn u fun x => v x + c := by
  refine hΩ.exists_eq_add_of_subset_closure_hasFDerivAt_eq hΩc hu hubot hv hvbot huΩ hvΩ
    ((convexOn_toReal hu hubot).continuousOn_interior.mono (hΩ.subset_interior_iff.2 huΩ))
    ((convexOn_toReal hv hvbot).continuousOn_interior.mono (hΩ.subset_interior_iff.2 hvΩ))
    fun x hx => ?_
  -- By Rademacher's theorem, almost every point of `Ω` carries a common derivative; such points
  -- are dense in `Ω` because nonempty open sets have positive Haar measure.
  have hae : ∀ᵐ y ∂ρ.restrict Ω, ∃ f' : E →L[ℝ] ℝ, HasFDerivAt (fun x => (u x).toReal) f' y ∧
      HasFDerivAt (fun x => (v x).toReal) f' y := by
    filter_upwards [ae_restrict_mem hΩ.measurableSet,
      ae_restrict_of_ae (ae_eventually_ne_top_and_differentiableAt_toReal (μ := ρ) hu hubot),
      ae_restrict_of_ae (ae_eventually_ne_top_and_differentiableAt_toReal (μ := ρ) hv hvbot),
      hμ.ae_le h] with y hy hdu hdv hyeq
    exact ⟨_, (hdu (huΩ y hy)).2.hasFDerivAt, hyeq ▸ (hdv (hvΩ y hy)).2.hasFDerivAt⟩
  rw [mem_closure_iff_nhds]
  intro t ht
  obtain ⟨s, hst, hso, hxs⟩ := mem_nhds_iff.1 ht
  obtain ⟨y, hy, hyD⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    ((hso.inter hΩ).measure_ne_zero ρ ⟨x, hxs, hx⟩)
    (ae_restrict_of_ae_restrict_of_subset inter_subset_right hae)
  exact ⟨y, hst hy.1, hyD⟩

end Normed

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ρ μ : Measure E} [ρ.IsAddHaarMeasure] {u v : E → EReal}
  {Ω : Set E}

/-- **Uniqueness of a convex potential up to a constant.** Let `u v : E → EReal` be convex
functions (convex real epigraph, never `⊥`) on a finite-dimensional real inner product space,
finite on a connected open set `Ω`, and let `μ` be a measure with respect to which Lebesgue measure
on `Ω` (any additive Haar measure `ρ` restricted to `Ω`) is absolutely continuous. If the gradients
of the real representatives of `u` and `v` agree `μ`-almost everywhere, then `u = v + c` on `Ω` for
some real constant `c`. In particular a Brenier map `∇ u` determines its convex potential `u` up to
an additive constant on such a set. -/
theorem _root_.IsOpen.exists_eq_add_of_gradient_ae_eq (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hu : Convex ℝ {p : E × ℝ | u p.1 ≤ p.2}) (hubot : ∀ x, u x ≠ ⊥)
    (hv : Convex ℝ {p : E × ℝ | v p.1 ≤ p.2}) (hvbot : ∀ x, v x ≠ ⊥)
    (huΩ : ∀ x ∈ Ω, u x ≠ ⊤) (hvΩ : ∀ x ∈ Ω, v x ≠ ⊤) (hμ : ρ.restrict Ω ≪ μ)
    (h : (∇ fun x => (u x).toReal) =ᵐ[μ] ∇ fun x => (v x).toReal) :
    ∃ c : ℝ, Ω.EqOn u fun x => v x + c :=
  hΩ.exists_eq_add_of_fderiv_ae_eq hΩc hu hubot hv hvbot huΩ hvΩ hμ <| h.mono fun _ hx =>
    (InnerProductSpace.toDual ℝ E).symm.injective hx

end InnerProduct

end TauCeti
