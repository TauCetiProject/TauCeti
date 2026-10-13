/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.MorseSmale.Perturbation
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Dynamics.Flow.Variational

/-!
# Admissible perturbations move the end of an orbit in every direction

Let `f` be a `C²` function with globally Lipschitz gradient on a finite-dimensional real inner
product space `E`, `φ` its negative-gradient flow, `x` a point that is not a critical point of `f`,
and `T > 0`. Perturbing `f` by functions vanishing near its critical points moves the point
`φ_T x` in every direction transverse to the orbit: there is a finite family `h` of admissible
perturbations such that the derivative at `s = 0` of `s ↦ φ^{f + ∑ sᵢ hᵢ}_T x`, together with
the flow direction `∇f(φ_T x)`, spans `E`.

The flow direction cannot be dropped: a perturbation supported away from the critical points does
not move the end of an orbit along the orbit to first order. Since the flow direction is tangent
to both the unstable and the stable sets of the critical points joined by the orbit, this
surjectivity is what the transversality of these sets for a generic perturbation needs.

## Main results

* `TauCeti.exists_admissible_range_fderiv_perturbedFlow_sup_span_eq_top`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014
  (transversality of the unstable and stable manifolds of a Morse function by perturbation).
* S. Smale, *On gradient dynamical systems*, Ann. of Math. **74** (1961), 199--206.
-/

public section

open Set Filter Topology InnerProductSpace
open scoped Gradient NNReal RealInnerProductSpace

namespace TauCeti

section Bump

/-- If `∫₀ᵀ b(σ) ψ(F σ) dσ = 0` for every smooth bump `ψ` centred at `F σ₀`, with `F` continuous
and strictly antitone and `b` continuous, then `b σ₀ ≤ 0` for `σ₀ ∈ (0, T)`. -/
private theorem nonpos_of_forall_integral_bump {b F : ℝ → ℝ} (hb : Continuous b)
    (hF : Continuous F) (hFa : StrictAnti F) {T σ₀ : ℝ} (hσ : σ₀ ∈ Ioo 0 T)
    (h : ∀ ψ : ContDiffBump (F σ₀), ∫ σ in (0 : ℝ)..T, b σ * ψ (F σ) = 0) : b σ₀ ≤ 0 := by
  by_contra hpos
  rw [not_le] at hpos
  -- `b` is positive on a neighbourhood of `σ₀` inside `(0, T)`.
  obtain ⟨ε, hε, hεb⟩ :=
    Metric.eventually_nhds_iff.1 (hb.continuousAt.eventually (lt_mem_nhds hpos))
  set δ := min ε (min σ₀ (T - σ₀)) with hδ
  have hδpos : 0 < δ := lt_min hε (lt_min hσ.1 (by linarith [hσ.2]))
  have hbpos : ∀ σ, |σ - σ₀| < δ → 0 < b σ := fun σ hσ' ↦
    hεb (by rw [Real.dist_eq]; exact hσ'.trans_le (min_le_left _ _))
  -- A bump around `F σ₀` small enough that `ψ ∘ F` lives in `(σ₀ - δ / 2, σ₀ + δ / 2)`.
  set c := F σ₀
  have h1 : c < F (σ₀ - δ / 2) := hFa (by linarith)
  have h2 : F (σ₀ + δ / 2) < c := hFa (by linarith)
  set r := min (F (σ₀ - δ / 2) - c) (c - F (σ₀ + δ / 2)) with hr
  have hrpos : 0 < r := lt_min (by linarith) (by linarith)
  let ψ : ContDiffBump c := ⟨r / 2, r, by positivity, by linarith⟩
  have hψ0 : ∀ σ, δ / 2 ≤ |σ - σ₀| → ψ (F σ) = 0 := fun σ hσ' ↦ by
    refine ψ.zero_of_le_dist ?_
    rw [Real.dist_eq]
    rcases le_abs'.1 hσ' with h' | h'
    · have : F (σ₀ - δ / 2) ≤ F σ := hFa.antitone (by linarith)
      rw [abs_of_nonneg (by linarith)]
      exact ((min_le_left _ _).trans (by linarith) : r ≤ F σ - c)
    · have : F σ ≤ F (σ₀ + δ / 2) := hFa.antitone (by linarith)
      rw [abs_of_nonpos (by linarith)]
      exact ((min_le_right _ _).trans (by linarith) : r ≤ -(F σ - c))
  have hg : Continuous fun σ ↦ b σ * ψ (F σ) := hb.mul (ψ.continuous.comp hF)
  have hnonneg : ∀ σ, 0 ≤ b σ * ψ (F σ) := fun σ ↦ by
    by_cases hσ' : |σ - σ₀| < δ / 2
    · exact mul_nonneg (hbpos σ (by linarith)).le ψ.nonneg
    · rw [hψ0 σ (not_lt.1 hσ'), mul_zero]
  -- Near `σ₀` the integrand is positive.
  have hψc : 0 < ψ (F σ₀) := ψ.pos_of_mem_ball (by rw [Metric.mem_ball, dist_self]; exact hrpos)
  obtain ⟨η, hη, hηψ⟩ := Metric.eventually_nhds_iff.1
    ((ψ.continuous.comp hF).continuousAt.eventually (lt_mem_nhds hψc))
  set η' := min η (δ / 2)
  have hη' : 0 < η' := lt_min hη (by linarith)
  have hηδ : η' ≤ δ / 2 := min_le_right _ _
  have hpos' : ∀ σ ∈ Ioo (σ₀ - η') (σ₀ + η'), 0 < b σ * ψ (F σ) := fun σ hσ' ↦ by
    have hd : |σ - σ₀| < η' := abs_sub_lt_iff.2 ⟨by linarith [hσ'.2], by linarith [hσ'.1]⟩
    exact mul_pos (hbpos σ (hd.trans_le ((min_le_right _ _).trans (by linarith))))
      (hηψ (by rw [Real.dist_eq]; exact hd.trans_le (min_le_left _ _)))
  have hδσ : δ ≤ σ₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hδT : δ ≤ T - σ₀ := (min_le_right _ _).trans (min_le_right _ _)
  have hint : ∀ a b' : ℝ, IntervalIntegrable (fun σ ↦ b σ * ψ (F σ)) MeasureTheory.volume a b' :=
    fun a b' ↦ hg.intervalIntegrable a b'
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hint 0 (σ₀ - η'))
    (hint (σ₀ - η') (σ₀ + η'))
  have hsplit' := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hint 0 (σ₀ + η'))
    (hint (σ₀ + η') T)
  have hA := intervalIntegral.integral_nonneg (μ := MeasureTheory.volume) (a := 0) (b := σ₀ - η')
    (by linarith)
    (fun σ _ ↦ hnonneg σ)
  have hB := intervalIntegral.intervalIntegral_pos_of_pos_on (hint (σ₀ - η') (σ₀ + η')) hpos'
    (by linarith)
  have hC := intervalIntegral.integral_nonneg (μ := MeasureTheory.volume) (a := σ₀ + η') (b := T)
    (by linarith)
    (fun σ _ ↦ hnonneg σ)
  have := h ψ
  linarith

/-- If `∫₀ᵀ a(σ) ψ(F σ) dσ = 0` for every smooth bump `ψ` centred at `F σ₀`, with `F` continuous
and strictly antitone and `a` continuous, then `a σ₀ = 0` for `σ₀ ∈ (0, T)`. -/
private theorem eq_zero_of_forall_integral_bump {a F : ℝ → ℝ} (ha : Continuous a)
    (hF : Continuous F) (hFa : StrictAnti F) {T σ₀ : ℝ} (hσ : σ₀ ∈ Ioo 0 T)
    (h : ∀ ψ : ContDiffBump (F σ₀), ∫ σ in (0 : ℝ)..T, a σ * ψ (F σ) = 0) : a σ₀ = 0 := by
  refine le_antisymm (nonpos_of_forall_integral_bump ha hF hFa hσ h) ?_
  have := nonpos_of_forall_integral_bump (b := fun σ ↦ -a σ) ha.neg hF hFa hσ fun ψ ↦ by
    simp only [neg_mul, intervalIntegral.integral_neg, h ψ, neg_zero]
  linarith

end Bump

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → ℝ} {K : ℝ≥0}

section Orbit

/-- The orbit of `y` under the negative-gradient flow has velocity `-∇ f`. -/
private theorem hasDerivAt_negativeGradientFlow_orbit (hf : LipschitzWith K (∇ f)) (y : E)
    (t : ℝ) :
    HasDerivAt (fun s ↦ negativeGradientFlow f hf s y)
      (-∇ f (negativeGradientFlow f hf t y)) t :=
  (isNegativeGradient_negativeGradientFlow f hf).isIntegralCurve y t

/-- The derivative of the negative-gradient flow carries the gradient along the orbit. -/
private theorem fderiv_negativeGradientFlow_apply_gradient (hfs : ContDiff ℝ 2 f)
    (hf : LipschitzWith K (∇ f)) (t : ℝ) (x : E) :
    fderiv ℝ (negativeGradientFlow f hf t) x (∇ f x) = ∇ f (negativeGradientFlow f hf t x) := by
  have hv : ∀ y, HasDerivAt (fun s ↦ negativeGradientFlow f hf s y) (-∇ f y) 0 := fun y ↦ by
    have := hasDerivAt_negativeGradientFlow_orbit hf y 0
    rwa [Flow.map_zero_apply] at this
  have := fderiv_flow_apply_of_hasDerivAt hv
    ((contDiff_negativeGradientFlow_apply f hf hfs t).differentiable one_ne_zero x)
  rwa [map_neg, neg_inj] at this

/-- An orbit through a non-critical point meets no critical point. -/
private theorem gradient_negativeGradientFlow_ne_zero (hf : LipschitzWith K (∇ f)) {x : E}
    (hx : ∇ f x ≠ 0) (t : ℝ) : ∇ f (negativeGradientFlow f hf t x) ≠ 0 := by
  intro h0
  have hfix := (forall_negativeGradientFlow_eq_self_iff f hf _).2 h0 (-t)
  rw [← Flow.map_add, neg_add_cancel, Flow.map_zero_apply] at hfix
  exact hx (hfix ▸ h0)

/-- Along an orbit through a non-critical point, `f` is strictly decreasing. -/
private theorem strictAnti_comp_negativeGradientFlow (hfs : ContDiff ℝ 2 f)
    (hf : LipschitzWith K (∇ f)) {x : E} (hx : ∇ f x ≠ 0) :
    StrictAnti fun σ ↦ f (negativeGradientFlow f hf σ x) := by
  refine strictAnti_of_deriv_neg fun σ ↦ ?_
  have hd : HasDerivAt (fun σ ↦ f (negativeGradientFlow f hf σ x))
      (fderiv ℝ f (negativeGradientFlow f hf σ x) (-∇ f (negativeGradientFlow f hf σ x))) σ :=
    ((hfs.differentiable (by norm_num)) _).hasFDerivAt.comp_hasDerivAt σ
      (hasDerivAt_negativeGradientFlow_orbit hf x σ)
  rw [hd.deriv, map_neg, ← inner_gradient_left, real_inner_self_eq_norm_sq, neg_lt_zero]
  exact pow_pos (norm_pos_iff.2 (gradient_negativeGradientFlow_ne_zero hf hx σ)) 2

/-- The inverse `Dφ_{-σ}(φ_σ x)` of the derivative of the flow along an orbit is continuous in
`σ`. -/
private theorem continuous_fderiv_negativeGradientFlow_neg (hfs : ContDiff ℝ 2 f)
    (hf : LipschitzWith K (∇ f)) (x : E) :
    Continuous fun σ ↦
      fderiv ℝ (negativeGradientFlow f hf (-σ)) (negativeGradientFlow f hf σ x) := by
  have hφd : ∀ t, Differentiable ℝ (negativeGradientFlow f hf t) := fun t ↦
    (contDiff_negativeGradientFlow_apply f hf hfs t).differentiable one_ne_zero
  have hinv : ∀ σ, Ring.inverse (fderiv ℝ (negativeGradientFlow f hf σ) x) =
      fderiv ℝ (negativeGradientFlow f hf (-σ)) (negativeGradientFlow f hf σ x) := fun σ ↦
    ring_inverse_fderiv_flow (hφd _ _) (hφd σ x)
  simp_rw [← hinv]
  refine continuous_iff_continuousAt.2 fun σ ↦ ?_
  let U : (E →L[ℝ] E)ˣ := ⟨_, _, fderiv_flow_comp_neg (hφd (-σ) _) (hφd σ x),
    fderiv_flow_neg_comp (hφd (-σ) _) (hφd σ x)⟩
  exact (NormedRing.inverse_continuousAt U).comp_of_eq
    (hasDerivAt_fderiv_negativeGradientFlow f hf hfs x σ).continuousAt rfl

end Orbit

/-- The integral `∫₀ᵀ Dφ_{-σ}(φ_σ x) (∇g(φ_σ x)) dσ` that an admissible perturbation `g` contributes
to the parameter derivative of the flow. -/
private noncomputable def contribution (f : E → ℝ) (hf : LipschitzWith K (∇ f)) (x : E) (T : ℝ)
    (g : E → ℝ) : E :=
  ∫ σ in (0 : ℝ)..T,
    fderiv ℝ (negativeGradientFlow f hf (-σ)) (negativeGradientFlow f hf σ x)
      (∇ g (negativeGradientFlow f hf σ x))

/-- **The contributions of admissible perturbations and the gradient span `E`.** -/
private theorem span_insert_gradient_range_contribution_eq_top (hfs : ContDiff ℝ 2 f)
    (hf : LipschitzWith K (∇ f)) {x : E} (hx : ∇ f x ≠ 0) {T : ℝ} (hT : 0 < T) :
    Submodule.span ℝ (insert (∇ f x)
      (range fun g : {g : E → ℝ // IsAdmissiblePerturbation f g} ↦
        contribution f hf x T g.1)) = ⊤ := by
  set φ := negativeGradientFlow f hf
  set N : ℝ → E →L[ℝ] E := fun σ ↦ fderiv ℝ (φ (-σ)) (φ σ x)
  have hφd : ∀ t, Differentiable ℝ (φ t) := fun t ↦
    (contDiff_negativeGradientFlow_apply f hf hfs t).differentiable one_ne_zero
  have hγ : Continuous fun σ ↦ φ σ x :=
    (contDiff_negativeGradientFlow f hf hfs).continuous.comp
      (continuous_id.prodMk continuous_const)
  have hN : Continuous N := continuous_fderiv_negativeGradientFlow_neg hfs hf x
  by_contra hV
  obtain ⟨y, hyV, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    fun h0 ↦ hV (Submodule.orthogonal_eq_bot_iff.1 h0)
  have hyx : ⟪∇ f x, y⟫ = 0 :=
    Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (mem_insert _ _)) hyV
  have hyk : ∀ g : {g : E → ℝ // IsAdmissiblePerturbation f g},
      ⟪contribution f hf x T g.1, y⟫ = 0 := fun g ↦
    Submodule.inner_right_of_mem_orthogonal
      (Submodule.subset_span (mem_insert_of_mem _ (mem_range_self g))) hyV
  -- The covectors `⟪y, N σ ·⟫`, as vectors.
  set m : ℝ → E := fun σ ↦ ContinuousLinearMap.adjoint (N σ) y
  have hm : Continuous m :=
    ((ContinuousLinearMap.adjoint (𝕜 := ℝ)).continuous.comp hN).clm_apply continuous_const
  -- They annihilate the flow direction.
  have hmgrad : ∀ σ, fderiv ℝ f (φ σ x) (m σ) = 0 := fun σ ↦ by
    have hNg : N σ (∇ f (φ σ x)) = ∇ f x := by
      have := fderiv_negativeGradientFlow_apply_gradient hfs hf (-σ) (φ σ x)
      rwa [← Flow.map_add, neg_add_cancel, Flow.map_zero_apply] at this
    rw [← inner_gradient_left, ContinuousLinearMap.adjoint_inner_right, hNg, hyx]
  -- A bump around a point of the orbit, inside a region without critical points.
  set σ₀ := T / 2 with hσdef
  have hσ₀ : σ₀ ∈ Ioo 0 T := ⟨by rw [hσdef]; positivity, by rw [hσdef]; linarith⟩
  set z := φ σ₀ x
  have hgradc : Continuous (∇ f) := (hfs.gradient_right (m := 1) (by norm_num)).continuous
  obtain ⟨ρ, hρ, hρz⟩ := Metric.eventually_nhds_iff.1
    (hgradc.continuousAt.eventually_ne (gradient_negativeGradientFlow_ne_zero hf hx σ₀))
  let θ : ContDiffBump z := ⟨ρ / 4, ρ / 2, by positivity, by linarith⟩
  have hθr : θ.rOut = ρ / 2 := rfl
  have hθz : θ z = 1 := θ.one_of_mem_closedBall (Metric.mem_closedBall_self θ.rIn_pos.le)
  have hθ'z : fderiv ℝ θ z = 0 := by
    rw [θ.eventuallyEq_one.fderiv_eq]
    exact fderiv_const_apply _
  -- The test perturbations `θ (ψ ∘ f) ⟪w, ·⟫`.
  have hkey : ∀ w : E, ∀ ψ : ContDiffBump (f z),
      ∫ σ in (0 : ℝ)..T, (θ (φ σ x) * ⟪w, m σ⟫ + ⟪w, φ σ x⟫ * fderiv ℝ θ (φ σ x) (m σ)) *
        ψ (f (φ σ x)) = 0 := by
    intro w ψ
    set g : E → ℝ := fun p ↦ θ p * (ψ (f p) * ⟪w, p⟫)
    have hgC : ContDiff ℝ 2 g :=
      θ.contDiff.mul ((ψ.contDiff.comp hfs).mul (innerSL ℝ w).contDiff)
    have hgs : HasCompactSupport g := θ.hasCompactSupport.mul_right
    have hgd : Disjoint (tsupport g) {p | fderiv ℝ f p = 0} := by
      refine Set.disjoint_left.2 fun p hp hp0 ↦ ?_
      have hpθ : p ∈ tsupport (θ : E → ℝ) := tsupport_mul_subset_left hp
      rw [θ.tsupport_eq] at hpθ
      refine hρz (Metric.mem_closedBall.1 hpθ |>.trans_lt (by rw [hθr]; linarith)) ?_
      simp [gradient, show fderiv ℝ f p = 0 from hp0]
    have hk := hyk ⟨g, ⟨hgC, hgs, hgd⟩⟩
    have hint : IntervalIntegrable (fun σ ↦ N σ (∇ g (φ σ x))) MeasureTheory.volume 0 T :=
      (hN.clm_apply (((hgC.gradient_right (m := 1) (by norm_num)).continuous).comp
        hγ)).intervalIntegrable 0 T
    have hcomm : ∫ σ in (0 : ℝ)..T, ⟪y, N σ (∇ g (φ σ x))⟫ =
        ⟪y, ∫ σ in (0 : ℝ)..T, N σ (∇ g (φ σ x))⟫ := by
      simpa using ContinuousLinearMap.intervalIntegral_comp_comm (innerSL ℝ y) hint
    have hk' : ⟪y, ∫ σ in (0 : ℝ)..T, N σ (∇ g (φ σ x))⟫ = 0 := by
      rw [real_inner_comm]
      exact hk
    refine Eq.trans (intervalIntegral.integral_congr (μ := MeasureTheory.volume)
      (g := fun σ ↦ ⟪y, N σ (∇ g (φ σ x))⟫) fun σ _ ↦ ?_) (hcomm.trans hk')
    dsimp only
    set p := φ σ x
    have hfd : DifferentiableAt ℝ f p := (hfs.differentiable (by norm_num)) p
    have hgder : HasFDerivAt g
        (θ p • ((ψ (f p)) • innerSL ℝ w +
          ⟪w, p⟫ • (fderiv ℝ ψ (f p)).comp (fderiv ℝ f p)) +
          (ψ (f p) * ⟪w, p⟫) • fderiv ℝ θ p) p :=
      ((θ.contDiff (n := 1)).differentiable one_ne_zero p).hasFDerivAt.mul
        ((((ψ.contDiff (n := 1)).differentiable one_ne_zero (f p)).hasFDerivAt.comp p
          hfd.hasFDerivAt).mul (innerSL ℝ w).hasFDerivAt)
    have hR : ⟪y, N σ (∇ g p)⟫ = fderiv ℝ g p (m σ) := by
      rw [real_inner_comm, ← ContinuousLinearMap.adjoint_inner_right, inner_gradient_left]
    have hp0 : fderiv ℝ f p (m σ) = 0 := hmgrad σ
    rw [hR, hgder.fderiv]
    simp [hp0]
    ring
  -- Hence `⟪w, m σ₀⟫ = 0` for every `w`.
  have hm0 : m σ₀ = 0 := by
    have hF : Continuous fun σ ↦ f (φ σ x) := hfs.continuous.comp hγ
    have h0 := eq_zero_of_forall_integral_bump
      (a := fun σ ↦ θ (φ σ x) * ⟪m σ₀, m σ⟫ + ⟪m σ₀, φ σ x⟫ * fderiv ℝ θ (φ σ x) (m σ))
      ((θ.continuous.comp hγ).mul (continuous_const.inner hm) |>.add
        ((continuous_const.inner hγ).mul
          ((((θ.contDiff (n := 1)).continuous_fderiv one_ne_zero).comp hγ).clm_apply hm)))
      hF (strictAnti_comp_negativeGradientFlow hfs hf hx) hσ₀ (hkey (m σ₀))
    have hθz' : θ (φ σ₀ x) = 1 := hθz
    have hθ'z' : fderiv ℝ θ (φ σ₀ x) = 0 := hθ'z
    simpa [hθz', hθ'z'] using h0
  -- And so `y = 0`.
  apply hy0
  have hNM : ∀ v, N σ₀ (fderiv ℝ (φ σ₀) x v) = v :=
    fderiv_flow_neg_apply_fderiv_flow (hφd _ _) (hφd σ₀ x)
  have := ContinuousLinearMap.adjoint_inner_right (N σ₀) (fderiv ℝ (φ σ₀) x y) y
  rw [hNM] at this
  rw [← inner_self_eq_zero (𝕜 := ℝ), ← this]
  simp [m, hm0]

/-- **Admissible perturbations move the end of an orbit in every direction transverse to it.** For
a point `x` that is not critical and a time `T > 0`, there is a finite family `h` of admissible
perturbations of `f` such that the derivative at the parameter `0` of
`s ↦ φ^{f + ∑ sᵢ hᵢ}_T x`, together with the flow direction `∇f(φ_T x)`, spans `E`. -/
theorem exists_admissible_range_fderiv_perturbedFlow_sup_span_eq_top (hfs : ContDiff ℝ 2 f)
    (hf : LipschitzWith K (∇ f)) {x : E} (hx : ∇ f x ≠ 0) {T : ℝ} (hT : 0 < T) :
    ∃ (n : ℕ) (h : Fin n → E → ℝ) (hh : ∀ i, IsAdmissiblePerturbation f (h i)),
      LinearMap.range (((ContinuousLinearMap.fst ℝ E (EuclideanSpace ℝ (Fin n))).comp
          ((fderiv ℝ (perturbedFlow f h hf hh T) (x, 0)).comp
            (ContinuousLinearMap.inr ℝ E (EuclideanSpace ℝ (Fin n))))) :
            EuclideanSpace ℝ (Fin n) →ₗ[ℝ] E) ⊔
        (ℝ ∙ ∇ f (negativeGradientFlow f hf T x)) = ⊤ := by
  set φ := negativeGradientFlow f hf
  set S := range fun g : {g : E → ℝ // IsAdmissiblePerturbation f g} ↦ contribution f hf x T g.1
  obtain ⟨v, hvS, hvspan, -⟩ := Submodule.exists_fun_fin_finrank_span_eq ℝ S
  choose g hg using hvS
  refine ⟨_, fun i ↦ (g i).1, fun i ↦ (g i).2, ?_⟩
  set MT := fderiv ℝ (φ T) x
  set L : EuclideanSpace ℝ (Fin (Module.finrank ℝ (Submodule.span ℝ S))) →ₗ[ℝ] E :=
    ContinuousLinearMap.toLinearMap (((ContinuousLinearMap.fst ℝ E _).comp
      ((fderiv ℝ (perturbedFlow f (fun i ↦ (g i).1) hf (fun i ↦ (g i).2) T) (x, 0)).comp
        (ContinuousLinearMap.inr ℝ E _))) :
      EuclideanSpace ℝ (Fin (Module.finrank ℝ (Submodule.span ℝ S))) →L[ℝ] E)
  have hφd : ∀ t, Differentiable ℝ (φ t) := fun t ↦
    (contDiff_negativeGradientFlow_apply f hf hfs t).differentiable one_ne_zero
  -- `Dφ_T(x)` maps the contributions of the family into the range of the parameter derivative.
  have hv : ∀ i, MT (v i) ∈ LinearMap.range L := fun i ↦ by
    refine ⟨-EuclideanSpace.single i 1, ?_⟩
    have hD := fst_fderiv_perturbedFlow_apply_eq_neg_integral hfs hf (fun i ↦ (g i).2) x
      (-EuclideanSpace.single i 1) T
    have hsum : ∀ p, ∑ j, (-EuclideanSpace.single i (1 : ℝ)) j • ∇ (g j).1 p = -∇ (g i).1 p :=
      fun p ↦ by simp
    calc L (-EuclideanSpace.single i 1)
        = (fderiv ℝ (perturbedFlow f (fun i ↦ (g i).1) hf (fun i ↦ (g i).2) T) (x, 0)
            (0, -EuclideanSpace.single i 1)).1 := rfl
      _ = MT (v i) := by
        rw [hD, ← hg i]
        simp only [hsum, map_neg, intervalIntegral.integral_neg, neg_neg]
        rfl
  have hS : Submodule.span ℝ S ≤ (LinearMap.range L).comap (MT : E →ₗ[ℝ] E) :=
    hvspan.symm.le.trans (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hv i))
  have hgrad : MT (∇ f x) = ∇ f (φ T x) := fderiv_negativeGradientFlow_apply_gradient hfs hf T x
  have htop := span_insert_gradient_range_contribution_eq_top hfs hf hx hT
  refine top_unique fun w _ ↦ ?_
  have hw : fderiv ℝ (φ (-T)) (φ T x) w ∈ Submodule.span ℝ (insert (∇ f x) S) := by
    rw [htop]
    exact Submodule.mem_top
  rw [Submodule.span_insert, Submodule.mem_sup] at hw
  obtain ⟨a, ha, b, hb, hab⟩ := hw
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 ha
  have hwab : w = MT b + c • ∇ f (φ T x) := by
    rw [← hgrad, ← map_smul, ← map_add, add_comm, hab]
    exact (fderiv_flow_apply_fderiv_flow_neg (hφd _ _) (hφd T x) w).symm
  rw [hwab]
  exact Submodule.add_mem_sup (hS hb) (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _))

end TauCeti
