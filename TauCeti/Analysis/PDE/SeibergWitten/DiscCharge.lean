/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.CutoffCurrent
public import TauCeti.Analysis.Contour.Winding.Number.Basic
import Mathlib.MeasureTheory.Integral.CircleIntegral
import TauCeti.Analysis.Calculus.DifferentialForm.Regularity
import TauCeti.Analysis.Contour.Winding.Integer
import TauCeti.Analysis.Contour.Winding.Number.Homotopy
import TauCeti.Analysis.Contour.Winding.RealIntegral.Basic

/-!
# Integer disc charges of the cutoff current

Let `(a, α)` be an abelian Higgs pair with `a = i b`, and let
`Θ = i F_a + d(χ(|α|²) τ)` be its cutoff current (`TauCeti.SeibergWitten.cutoffCurrent`), where
`χ` vanishes near `0`. A smooth disc `σ` whose boundary circle lies in the region where
`χ(|α|²) = 1` carries the charge

`I(σ) = (2π)⁻¹ ∫_D σ^* Θ`.

This file proves that this charge is an **integer**: it is the winding number of `α ∘ σ` around
the boundary circle (`exists_int_integral_cutoffCurrent_comp_closedBall`). The flux identity
`TauCeti.SeibergWitten.integral_cutoffCurrent_closedBall` already writes `∫_D Θ` as the winding
integral `∮ Im (α⁻¹ dα)`, with no contribution from the connection. Here that integral is
identified, through the real winding formula
`TauCeti.Contour.windingNumber_eq_real_integral_of_closed`, with `2π` times the winding number
`TauCeti.Contour.windingNumber`, which is an integer because the boundary loop is closed and
misses `0`. The pullback naturality of the cutoff current
(`TauCeti.SeibergWitten.cutoffCurrent_comp`) reduces the statement for a disc `σ : ℂ → E` in an
arbitrary real normed space to the case of a disc in the plane
(`exists_int_integral_cutoffCurrent_closedBall`).

If instead `χ = 1` near `|α|²` on the whole disc, the cutoff current vanishes there and the charge
is zero (`integral_cutoffCurrent_comp_closedBall_eq_zero`).

Since the charge is the winding number of the boundary loop, it is controlled by the zeros of
`α ∘ σ` and by the boundary circle:

* it vanishes as soon as `α ∘ σ` has no zero on the closed disc, even where `χ(|α|²) < 1`
  (`integral_cutoffCurrent_comp_closedBall_eq_zero_of_ne_zero`), because the boundary loop then
  contracts through `ℂ \ {0}`; so a disc of nonzero charge contains a zero of `α ∘ σ` in its
  interior (`exists_mem_ball_eq_zero_of_integral_cutoffCurrent_comp_ne_zero`);
* it is unchanged when the disc is shrunk to a concentric subdisc containing all the zeros of
  `α ∘ σ`, provided the smaller boundary circle also lies in `{χ(|α|²) = 1}`
  (`integral_cutoffCurrent_comp_closedBall_eq_of_annulus`);
* it is invariant under homotopies of discs whose boundary circles stay in `{χ(|α|²) = 1}`
  (`integral_cutoffCurrent_comp_closedBall_eq_of_continuousOn`); the interiors of the discs may
  cross the zeros of `α` along the homotopy.

In Taubes's passage from Seiberg–Witten solutions to pseudoholomorphic curves, `α` is the
component of the rescaled spinor along the canonical unit spinor and the cutoff currents converge
to the current of the limiting curve. The integer charges of discs whose boundary stays where
`|α|` is bounded below are the quantities whose limits are compared there with the local
intersection numbers of discs with the limiting curve; that comparison is not part of this file.

## Main results

* `TauCeti.SeibergWitten.exists_int_integral_cutoffCurrent_closedBall`: the flux of the cutoff
  current through a disc in the plane whose boundary circle lies in `{χ(|α|²) = 1}` is `2π n`,
  with `n` the integer winding number of `α` around that circle.
* `TauCeti.SeibergWitten.exists_int_integral_cutoffCurrent_comp_closedBall`: the same for the
  pullback of the cutoff current by a `C²` disc `σ : ℂ → E`, with `n` the winding number of
  `α ∘ σ`.
* `TauCeti.SeibergWitten.integral_cutoffCurrent_comp_closedBall_eq_zero`: the charge of a disc on
  which `χ = 1` near `|α|²` vanishes.
* `TauCeti.SeibergWitten.integral_cutoffCurrent_comp_closedBall_eq_zero_of_ne_zero` and
  `TauCeti.SeibergWitten.exists_mem_ball_eq_zero_of_integral_cutoffCurrent_comp_ne_zero`: a disc
  on which `α` does not vanish has charge zero, so a disc of nonzero charge meets the zeros of `α`.
* `TauCeti.SeibergWitten.integral_cutoffCurrent_comp_closedBall_eq_of_annulus`: the charge does
  not change on passing to a concentric subdisc containing the zeros of `α ∘ σ`.
* `TauCeti.SeibergWitten.integral_cutoffCurrent_comp_closedBall_eq_of_continuousOn`: the charge is
  invariant under homotopies keeping the boundary circle in `{χ(|α|²) = 1}`.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

noncomputable section

open ContinuousAlternatingMap Complex Filter Set MeasureTheory
open scoped Topology Real

namespace TauCeti.SeibergWitten

variable {χ : ℝ → ℝ}

/-- A cutoff vanishing near `0` takes the value `1` on `|w|²` only for `w ≠ 0`. -/
private theorem ne_zero_of_cutoff_eq_one (hχ₀ : χ =ᶠ[𝓝 0] 0) {w : ℂ} (h : χ (normSq w) = 1) :
    w ≠ 0 := by
  rintro rfl
  rw [normSq_zero, hχ₀.eq_of_nhds, Pi.zero_apply] at h
  exact zero_ne_one h

/-- **Integrality of the disc charge in the plane.** For fields on the plane such that
`χ(|α|²) = 1` on the boundary circle of a closed disc, the integral of the cutoff current over the
disc is `2π n`, where the integer `n` is the winding number of `α` around the boundary circle. -/
theorem exists_int_integral_cutoffCurrent_closedBall {α : ℂ → ℂ}
    {b : ℂ → ℂ [⋀^Fin 1]→L[ℝ] ℝ} {z₀ : ℂ} {r : ℝ} (hr : 0 ≤ r) (hα : ContDiff ℝ 2 α)
    (hb : ContDiff ℝ 1 b) (hχ : ContDiff ℝ 1 χ) (hχ₀ : χ =ᶠ[𝓝 0] 0)
    (hbd : ∀ θ, χ (normSq (α (circleMap z₀ r θ))) = 1) :
    ∃ n : ℤ, Contour.windingNumber (α ∘ circleMap z₀ r) (-π) π 0 = n ∧
      ∫ z in Metric.closedBall z₀ r, cutoffCurrent χ b α z ![1, I] = 2 * π * n := by
  set γ := α ∘ circleMap z₀ r with hγ
  have hderiv : deriv γ = fun θ ↦ fderiv ℝ α (circleMap z₀ r θ) (circleMap 0 r θ * I) :=
    funext fun θ ↦ ((hα.differentiable two_ne_zero _).hasFDerivAt.comp_hasDerivAt θ
      (hasDerivAt_circleMap z₀ r θ)).deriv
  have hγ₀ (θ : ℝ) : γ θ ≠ 0 := ne_zero_of_cutoff_eq_one hχ₀ (hbd θ)
  have hγc : Continuous γ := hα.continuous.comp (continuous_circleMap z₀ r)
  -- The index integrand `γ⁻¹ γ'` of the boundary loop is continuous, hence integrable.
  have hint : IntervalIntegrable (fun θ ↦ (γ θ - 0)⁻¹ * deriv γ θ) volume (-π) π := by
    simp_rw [sub_zero, hderiv]
    exact ((hγc.inv₀ hγ₀).mul (((hα.continuous_fderiv two_ne_zero).comp
      (continuous_circleMap z₀ r)).clm_apply ((continuous_circleMap 0 r).mul
        continuous_const))).intervalIntegrable _ _
  have hclosed : γ (-π) = γ π := by
    simp only [hγ, Function.comp_apply, ← periodic_circleMap z₀ r (-π)]
    ring_nf
  have hdiff (θ : ℝ) (_ : θ ∈ Ioo (min (-π) π) (max (-π) π) \ ∅) : DifferentiableAt ℝ γ θ :=
    (hα.differentiable two_ne_zero).differentiableAt.comp θ (differentiable_circleMap z₀ r θ)
  obtain ⟨n, hn⟩ := Contour.exists_int_windingNumber_of_closed hclosed countable_empty
    hγc.continuousOn hdiff (fun θ _ ↦ hγ₀ θ) hint
  refine ⟨n, hn, ?_⟩
  -- The winding number of the boundary loop is `(2π)⁻¹` times its real winding integral.
  have hreal := Contour.windingNumber_eq_real_integral_of_closed hclosed countable_empty
    hγc.continuousOn hdiff (fun θ _ ↦ hγ₀ θ) hint
  rw [hn, ← ofReal_intCast, ofReal_inj] at hreal
  rw [integral_cutoffCurrent_closedBall hr hα hb hχ hχ₀ hbd]
  calc ∫ θ in -π..π, phaseForm α (circleMap z₀ r θ) (fun _ ↦ circleMap 0 r θ * I)
      = ∫ θ in -π..π, Contour.realWindingIntegrand (γ θ - 0) (deriv γ θ) := by
        refine intervalIntegral.integral_congr fun θ _ ↦ ?_
        rw [Contour.realWindingIntegrand_def, hderiv]
        simp [hγ]
    _ = 2 * π * n := by
        rw [hreal]
        field_simp

/-- **Integrality of the disc charge.** Let `σ : ℂ → E` be a `C²` disc such that
`χ(|α|²) = 1` along `σ` of the boundary circle of a closed disc. Then the integral over the disc
of the pullback by `σ` of the cutoff current is `2π n`, where the integer `n` is the winding
number of `α ∘ σ` around the boundary circle. -/
theorem exists_int_integral_cutoffCurrent_comp_closedBall {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {α : E → ℂ} {b : E → E [⋀^Fin 1]→L[ℝ] ℝ} {σ : ℂ → E} {z₀ : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hα : ContDiff ℝ 2 α) (hb : ContDiff ℝ 1 b) (hχ : ContDiff ℝ 1 χ)
    (hχ₀ : χ =ᶠ[𝓝 0] 0) (hσ : ContDiff ℝ 2 σ)
    (hbd : ∀ θ, χ (normSq (α (σ (circleMap z₀ r θ)))) = 1) :
    ∃ n : ℤ, Contour.windingNumber (α ∘ σ ∘ circleMap z₀ r) (-π) π 0 = n ∧
      ∫ z in Metric.closedBall z₀ r,
        (cutoffCurrent χ b α (σ z)).compContinuousLinearMap (fderiv ℝ σ z) ![1, I] =
          2 * π * n := by
  have hpull : ContDiff ℝ 1 fun z ↦ (b (σ z)).compContinuousLinearMap (fderiv ℝ σ z) :=
    contDiff_iff_contDiffAt.2 fun z ↦ hσ.contDiffAt.differentialForm_pullback hb.contDiffAt
  simp_rw [← fun z ↦ cutoffCurrent_comp (y := z) hα.contDiffAt hb.contDiffAt hχ hχ₀ hσ.contDiffAt]
  exact exists_int_integral_cutoffCurrent_closedBall hr (hα.comp hσ) hpull hχ hχ₀ hbd

/-- **The charge of a disc in the vacuum vanishes.** If `χ = 1` near `|α|²` at every point of `σ`
of a closed disc, then the integral over the disc of the pullback by `σ` of the cutoff current
is zero. -/
theorem integral_cutoffCurrent_comp_closedBall_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {α : E → ℂ} {b : E → E [⋀^Fin 1]→L[ℝ] ℝ} {σ : ℂ → E} {z₀ : ℂ} {r : ℝ}
    (hα : ∀ z ∈ Metric.closedBall z₀ r, ContDiffAt ℝ 2 α (σ z))
    (hb : ∀ z ∈ Metric.closedBall z₀ r, DifferentiableAt ℝ b (σ z)) (hχ₀ : χ =ᶠ[𝓝 0] 0)
    (hvac : ∀ z ∈ Metric.closedBall z₀ r, χ =ᶠ[𝓝 (normSq (α (σ z)))] 1) :
    ∫ z in Metric.closedBall z₀ r,
      (cutoffCurrent χ b α (σ z)).compContinuousLinearMap (fderiv ℝ σ z) ![1, I] = 0 := by
  refine setIntegral_eq_zero_of_forall_eq_zero fun z hz ↦ ?_
  rw [cutoffCurrent_eq_zero (hα z hz)
    (ne_zero_of_cutoff_eq_one hχ₀ (hvac z hz).eq_of_nhds) (hb z hz) (hvac z hz)]
  simp

/-- **A disc on which `α` does not vanish has charge zero.** Let `σ : ℂ → E` be a `C²` disc such
that `χ(|α|²) = 1` along `σ` of the boundary circle of a closed disc, and such that `α ∘ σ` has
no zero on the closed disc. Then the integral over the disc of the pullback by `σ` of the cutoff
current vanishes. Unlike `integral_cutoffCurrent_comp_closedBall_eq_zero`, the cutoff `χ(|α|²)`
may be smaller than `1` inside the disc. -/
theorem integral_cutoffCurrent_comp_closedBall_eq_zero_of_ne_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {α : E → ℂ} {b : E → E [⋀^Fin 1]→L[ℝ] ℝ}
    {σ : ℂ → E} {z₀ : ℂ} {r : ℝ} (hr : 0 ≤ r) (hα : ContDiff ℝ 2 α) (hb : ContDiff ℝ 1 b)
    (hχ : ContDiff ℝ 1 χ) (hχ₀ : χ =ᶠ[𝓝 0] 0) (hσ : ContDiff ℝ 2 σ)
    (hbd : ∀ θ, χ (normSq (α (σ (circleMap z₀ r θ)))) = 1)
    (hne : ∀ z ∈ Metric.closedBall z₀ r, α (σ z) ≠ 0) :
    ∫ z in Metric.closedBall z₀ r,
      (cutoffCurrent χ b α (σ z)).compContinuousLinearMap (fderiv ℝ σ z) ![1, I] = 0 := by
  obtain ⟨n, hn, hI⟩ := exists_int_integral_cutoffCurrent_comp_closedBall hr hα hb hχ hχ₀ hσ hbd
  have h0 := Contour.windingNumber_comp_circleMap_eq_zero hr
    ((hα.comp hσ).contDiffOn.of_le one_le_two) hne (-π)
  rw [show -π + 2 * π = π by ring, Function.comp_assoc, hn, Int.cast_eq_zero] at h0
  rw [hI, h0, Int.cast_zero, mul_zero]

/-- **A disc of nonzero charge meets the zeros of `α`.** Let `σ : ℂ → E` be a `C²` disc such that
`χ(|α|²) = 1` along `σ` of the boundary circle of a closed disc. If the integral over the disc of
the pullback by `σ` of the cutoff current is nonzero, then `α ∘ σ` vanishes at some point of the
open disc. -/
theorem exists_mem_ball_eq_zero_of_integral_cutoffCurrent_comp_ne_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {α : E → ℂ} {b : E → E [⋀^Fin 1]→L[ℝ] ℝ}
    {σ : ℂ → E} {z₀ : ℂ} {r : ℝ} (hr : 0 ≤ r) (hα : ContDiff ℝ 2 α) (hb : ContDiff ℝ 1 b)
    (hχ : ContDiff ℝ 1 χ) (hχ₀ : χ =ᶠ[𝓝 0] 0) (hσ : ContDiff ℝ 2 σ)
    (hbd : ∀ θ, χ (normSq (α (σ (circleMap z₀ r θ)))) = 1)
    (hI : ∫ z in Metric.closedBall z₀ r,
      (cutoffCurrent χ b α (σ z)).compContinuousLinearMap (fderiv ℝ σ z) ![1, I] ≠ 0) :
    ∃ z ∈ Metric.ball z₀ r, α (σ z) = 0 := by
  by_contra! h
  refine hI (integral_cutoffCurrent_comp_closedBall_eq_zero_of_ne_zero hr hα hb hχ hχ₀ hσ hbd
    fun z hz ↦ ?_)
  rcases (Metric.mem_closedBall.1 hz).lt_or_eq with hlt | heq
  · exact h z (Metric.mem_ball.2 hlt)
  -- A point of the boundary circle is `circleMap z₀ r θ`, where `χ(|α|²) = 1`.
  obtain ⟨θ, rfl⟩ : z ∈ range (circleMap z₀ r) := by
    rw [range_circleMap, abs_of_nonneg hr]
    exact Metric.mem_sphere.2 heq
  exact ne_zero_of_cutoff_eq_one hχ₀ (hbd θ)

/-- **The disc charge only sees the zeros of `α`.** Let `σ : ℂ → E` be a `C²` disc, and let
`0 ≤ r₁ ≤ r₂` be radii such that `χ(|α|²) = 1` along `σ` of both circles of radii `r₁` and `r₂`
about `z₀`, and such that `α ∘ σ` has no zero on the closed annulus between them. Then the discs
of radii `r₁` and `r₂` carry the same charge. -/
theorem integral_cutoffCurrent_comp_closedBall_eq_of_annulus {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {α : E → ℂ} {b : E → E [⋀^Fin 1]→L[ℝ] ℝ}
    {σ : ℂ → E} {z₀ : ℂ} {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (hr : r₁ ≤ r₂) (hα : ContDiff ℝ 2 α)
    (hb : ContDiff ℝ 1 b) (hχ : ContDiff ℝ 1 χ) (hχ₀ : χ =ᶠ[𝓝 0] 0) (hσ : ContDiff ℝ 2 σ)
    (hbd₁ : ∀ θ, χ (normSq (α (σ (circleMap z₀ r₁ θ)))) = 1)
    (hbd₂ : ∀ θ, χ (normSq (α (σ (circleMap z₀ r₂ θ)))) = 1)
    (hne : ∀ z ∈ Metric.closedBall z₀ r₂ \ Metric.ball z₀ r₁, α (σ z) ≠ 0) :
    ∫ z in Metric.closedBall z₀ r₁,
        (cutoffCurrent χ b α (σ z)).compContinuousLinearMap (fderiv ℝ σ z) ![1, I] =
      ∫ z in Metric.closedBall z₀ r₂,
        (cutoffCurrent χ b α (σ z)).compContinuousLinearMap (fderiv ℝ σ z) ![1, I] := by
  obtain ⟨m, hm, hI₁⟩ := exists_int_integral_cutoffCurrent_comp_closedBall hr₁ hα hb hχ hχ₀ hσ hbd₁
  obtain ⟨n, hn, hI₂⟩ :=
    exists_int_integral_cutoffCurrent_comp_closedBall (hr₁.trans hr) hα hb hχ hχ₀ hσ hbd₂
  have h := Contour.windingNumber_comp_circleMap_eq_of_annulus hr₁ hr
    ((hα.comp hσ).contDiffOn.of_le one_le_two) hne (-π)
  rw [show -π + 2 * π = π by ring, Function.comp_assoc, Function.comp_assoc, hm, hn,
    Int.cast_inj] at h
  rw [hI₁, hI₂, h]

/-- **Homotopy invariance of the disc charge.** Let `σ p`, for `p` in a preconnected set `S` of
parameters, be `C²` discs such that `σ p z` depends jointly continuously on `p ∈ S` and on `z` in
the boundary circle of a closed disc, and such that `χ(|α|²) = 1` along each `σ p` of that circle.
Then all the discs `σ p` carry the same charge. Only the boundary circles enter: along the family,
the interiors of the discs may cross the zeros of `α`, and need not vary continuously. -/
theorem integral_cutoffCurrent_comp_closedBall_eq_of_continuousOn {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {α : E → ℂ} {b : E → E [⋀^Fin 1]→L[ℝ] ℝ}
    {P : Type*} [TopologicalSpace P] {S : Set P} (hS : IsPreconnected S) {σ : P → ℂ → E}
    {z₀ : ℂ} {r : ℝ} (hr : 0 ≤ r) (hα : ContDiff ℝ 2 α) (hb : ContDiff ℝ 1 b)
    (hχ : ContDiff ℝ 1 χ) (hχ₀ : χ =ᶠ[𝓝 0] 0) (hσ : ∀ p ∈ S, ContDiff ℝ 2 (σ p))
    (hσc : ContinuousOn (Function.uncurry σ) (S ×ˢ Metric.sphere z₀ r))
    (hbd : ∀ p ∈ S, ∀ θ, χ (normSq (α (σ p (circleMap z₀ r θ)))) = 1) {p q : P} (hp : p ∈ S)
    (hq : q ∈ S) :
    ∫ z in Metric.closedBall z₀ r,
        (cutoffCurrent χ b α (σ p z)).compContinuousLinearMap (fderiv ℝ (σ p) z) ![1, I] =
      ∫ z in Metric.closedBall z₀ r,
        (cutoffCurrent χ b α (σ q z)).compContinuousLinearMap (fderiv ℝ (σ q) z) ![1, I] := by
  obtain ⟨m, hm, hI₁⟩ := exists_int_integral_cutoffCurrent_comp_closedBall hr hα hb hχ hχ₀
    (hσ p hp) (hbd p hp)
  obtain ⟨n, hn, hI₂⟩ := exists_int_integral_cutoffCurrent_comp_closedBall hr hα hb hχ hχ₀
    (hσ q hq) (hbd q hq)
  -- The boundary loops `α ∘ σ p ∘ circleMap z₀ r` form a continuous family of closed curves
  -- avoiding `0`.
  have h := Contour.windingNumber_eq_of_continuousOn_uncurry
    (H := fun p ↦ α ∘ σ p ∘ circleMap z₀ r) (a := -π) (b := π) (w := 0) hS
    (hα.continuous.comp_continuousOn (hσc.comp
      (continuousOn_fst.prodMk ((continuous_circleMap z₀ r).comp_continuousOn continuousOn_snd))
      fun x hx ↦ ⟨hx.1, circleMap_mem_sphere z₀ hr x.2⟩))
    (fun p hp ↦ IsPiecewiseC1On.of_contDiffOn
      ((hα.comp ((hσ p hp).comp (contDiff_circleMap z₀ r))).contDiffOn.of_le one_le_two))
    (fun p _ ↦ by simp only [Function.comp_apply, ← periodic_circleMap z₀ r (-π)]; ring_nf)
    (fun p hp θ _ ↦ ne_zero_of_cutoff_eq_one hχ₀ (hbd p hp θ)) hp hq
  rw [hm, hn, Int.cast_inj] at h
  rw [hI₁, hI₂, h]

end TauCeti.SeibergWitten
