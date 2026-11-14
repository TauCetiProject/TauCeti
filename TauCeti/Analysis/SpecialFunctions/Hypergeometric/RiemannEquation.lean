/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Riemann's equation from the hypergeometric equation (DLMF 15.11.7)

Riemann's differential equation (DLMF 15.11.1) with distinct finite singular points `α, β, γ` and
exponent pairs `{a₁, a₂}`, `{b₁, b₂}`, `{c₁, c₂}` subject to Fuchs's relation
`a₁ + a₂ + b₁ + b₂ + c₁ + c₂ = 1` (DLMF 15.11.2) is

`w″ + (Σ (1 − a₁ − a₂)/(z − α)) w′ + (Σ (α − β)(α − γ) a₁ a₂/(z − α)) w / ((z − α)(z − β)(z − γ))
= 0`,

the sums running cyclically over the three singular points. If `u` solves the hypergeometric
equation (DLMF 15.10.1) with `a = a₁ + b₁ + c₁`, `b = a₁ + b₁ + c₂`, `c = 1 + a₁ − a₂`, then
`w(z) = ((z − α)/(z − γ))^{a₁} ((z − β)/(z − γ))^{b₁} u(ζ)`, with the Möbius variable
`ζ = (z − α)(β − γ)/((z − γ)(β − α))`, solves Riemann's equation (DLMF 15.11.7).

## Main results

* `TauCeti.riemannEquation_of_hypergeometricEquation`: DLMF 15.11.7, from a solution of the
  hypergeometric equation to a solution of Riemann's equation.

## References

* [DLMF] *NIST Digital Library of Mathematical Functions*, §15.11, <https://dlmf.nist.gov/15.11>.

The proof is adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), files
`DLMF/Hypergeometric/Riemann.lean` and `DLMF/Hypergeometric/FurtherTransformations/Quadratic.lean`,
where it is stated for the Gauss series itself.
-/

@[expose] public section

open Complex Filter
open scoped Topology

namespace TauCeti

/-- The derivative of `p · (F ∘ φ)` near a point, for analytic data. -/
private theorem deriv_mul_comp_eventuallyEq {p φ F : ℂ → ℂ} {z : ℂ} (hp : AnalyticAt ℂ p z)
    (hφ : AnalyticAt ℂ φ z) (hF : AnalyticAt ℂ F (φ z)) :
    deriv (fun w => p w * F (φ w)) =ᶠ[𝓝 z]
      fun w => deriv p w * F (φ w) + p w * (deriv F (φ w) * deriv φ w) := by
  filter_upwards [hp.eventually_analyticAt, hφ.eventually_analyticAt,
    hφ.continuousAt.tendsto.eventually hF.eventually_analyticAt] with w h1 h2 h3
  exact (h1.differentiableAt.hasDerivAt.mul
    (h3.differentiableAt.hasDerivAt.comp w h2.differentiableAt.hasDerivAt)).deriv

/-- The second derivative of `p · (F ∘ φ)`, for analytic data. -/
private theorem deriv_deriv_mul_comp {p φ F : ℂ → ℂ} {z : ℂ} (hp : AnalyticAt ℂ p z)
    (hφ : AnalyticAt ℂ φ z) (hF : AnalyticAt ℂ F (φ z)) :
    deriv (deriv (fun w => p w * F (φ w))) z =
      deriv (deriv p) z * F (φ z) + 2 * deriv p z * (deriv F (φ z) * deriv φ z) +
        p z * (deriv (deriv F) (φ z) * deriv φ z ^ 2 + deriv F (φ z) * deriv (deriv φ) z) := by
  rw [(deriv_mul_comp_eventuallyEq hp hφ hF).deriv_eq]
  have hFφ := hF.differentiableAt.hasDerivAt.comp z hφ.differentiableAt.hasDerivAt
  have hF'φ := hF.deriv.differentiableAt.hasDerivAt.comp z hφ.differentiableAt.hasDerivAt
  have h := (hp.deriv.differentiableAt.hasDerivAt.mul hFφ).add
    (hp.differentiableAt.hasDerivAt.mul (hF'φ.mul hφ.deriv.differentiableAt.hasDerivAt))
  have h' : HasDerivAt (fun w => deriv p w * F (φ w) + p w * (deriv F (φ w) * deriv φ w)) _ z :=
    h
  rw [h'.deriv]
  simp only [Function.comp_apply, Pi.mul_apply]
  ring

/-- **DLMF 15.11.7**: if `u` solves the hypergeometric equation (DLMF 15.10.1) with
`a = a₁ + b₁ + c₁`, `b = a₁ + b₁ + c₂`, `c = 1 + a₁ − a₂` on an open set `V`, then
`w(z) = ((z − α)/(z − γ))^{a₁} ((z − β)/(z − γ))^{b₁} u((z − α)(β − γ)/((z − γ)(β − α)))` solves
Riemann's equation (DLMF 15.11.1) with singular points `α, β, γ` and exponents `{a₁, a₂}`,
`{b₁, b₂}`, `{c₁, c₂}` under Fuchs's relation (DLMF 15.11.2), on every open set `U` where the two
quotients lie in the slit plane and the Möbius variable lies in `V`. -/
theorem riemannEquation_of_hypergeometricEquation {α β γ a₁ a₂ b₁ b₂ c₁ c₂ : ℂ} (hαβ : α ≠ β)
    (hβγ : β ≠ γ) (hαγ : α ≠ γ) (hsum : a₁ + a₂ + b₁ + b₂ + c₁ + c₂ = 1) {U V : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V)
    (hUs : ∀ z ∈ U, (z - α) / (z - γ) ∈ slitPlane ∧ (z - β) / (z - γ) ∈ slitPlane)
    (hUV : ∀ z ∈ U, (z - α) * (β - γ) / ((z - γ) * (β - α)) ∈ V) {u : ℂ → ℂ}
    (hu : DifferentiableOn ℂ u V)
    (hu' : ∀ ζ ∈ V, ζ * (1 - ζ) * deriv (deriv u) ζ +
      (1 + a₁ - a₂ - ((a₁ + b₁ + c₁) + (a₁ + b₁ + c₂) + 1) * ζ) * deriv u ζ -
        (a₁ + b₁ + c₁) * (a₁ + b₁ + c₂) * u ζ = 0) :
    let w : ℂ → ℂ := fun z => ((z - α) / (z - γ)) ^ a₁ * ((z - β) / (z - γ)) ^ b₁ *
      u ((z - α) * (β - γ) / ((z - γ) * (β - α)))
    DifferentiableOn ℂ w U ∧ ∀ z ∈ U, deriv (deriv w) z +
      ((1 - a₁ - a₂) / (z - α) + (1 - b₁ - b₂) / (z - β) + (1 - c₁ - c₂) / (z - γ)) * deriv w z +
        ((α - β) * (α - γ) * a₁ * a₂ / (z - α) + (β - α) * (β - γ) * b₁ * b₂ / (z - β) +
          (γ - α) * (γ - β) * c₁ * c₂ / (z - γ)) / ((z - α) * (z - β) * (z - γ)) * w z = 0 := by
  intro w
  set T : ℂ → ℂ := fun w => (w - α) * (β - γ) / ((w - γ) * (β - α))
  set A : ℂ → ℂ := fun w => (w - α) / (w - γ) with hA
  set B : ℂ → ℂ := fun w => (w - β) / (w - γ) with hB
  set P : ℂ → ℂ := fun w => A w ^ a₁ * B w ^ b₁ with hP
  set L : ℂ → ℂ := fun w =>
    a₁ * ((w - α)⁻¹ - (w - γ)⁻¹) + b₁ * ((w - β)⁻¹ - (w - γ)⁻¹) with hL
  have hw : w = fun z => P z * u (T z) := rfl
  have h4' : β - α ≠ 0 := sub_ne_zero.mpr hαβ.symm
  have h6 : β - γ ≠ 0 := sub_ne_zero.mpr hβγ
  have hne : ∀ z ∈ U, z - α ≠ 0 ∧ z - β ≠ 0 ∧ z - γ ≠ 0 := by
    intro z hz
    obtain ⟨hA', hB'⟩ := hUs z hz
    refine ⟨fun h => slitPlane_ne_zero hA' ?_, fun h => slitPlane_ne_zero hB' ?_,
      fun h => slitPlane_ne_zero hA' ?_⟩ <;> simp [h]
  have hPa : ∀ z ∈ U, AnalyticAt ℂ P z := fun z hz =>
    ((analyticAt_id.sub analyticAt_const).div (analyticAt_id.sub analyticAt_const)
      (hne z hz).2.2 |>.cpow analyticAt_const (hUs z hz).1).mul
      (((analyticAt_id.sub analyticAt_const).div (analyticAt_id.sub analyticAt_const)
        (hne z hz).2.2).cpow analyticAt_const (hUs z hz).2)
  have hTa : ∀ z ∈ U, AnalyticAt ℂ T z := fun z hz =>
    ((analyticAt_id.sub analyticAt_const).mul analyticAt_const).div
      ((analyticAt_id.sub analyticAt_const).mul analyticAt_const) (mul_ne_zero (hne z hz).2.2 h4')
  have hFa : ∀ z ∈ U, AnalyticAt ℂ u (T z) := fun z hz =>
    hu.analyticAt (hV.mem_nhds (hUV z hz))
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · rw [hw]
    exact ((hPa z hz).mul ((hFa z hz).comp (hTa z hz))).differentiableAt.differentiableWithinAt
  obtain ⟨hzα, hzβ, hzγ⟩ := hne z hz
  have hPd : ∀ w ∈ U, HasDerivAt P (P w * L w) w := by
    intro w hw
    obtain ⟨hwα, hwβ, hwγ⟩ := hne w hw
    have hAd : HasDerivAt A ((α - γ) / (w - γ) ^ 2) w := by
      have h := ((hasDerivAt_id w).sub_const α).div ((hasDerivAt_id w).sub_const γ) hwγ
      refine h.congr_deriv ?_
      simp only [id]
      field_simp
      ring
    have hBd : HasDerivAt B ((β - γ) / (w - γ) ^ 2) w := by
      have h := ((hasDerivAt_id w).sub_const β).div ((hasDerivAt_id w).sub_const γ) hwγ
      refine h.congr_deriv ?_
      simp only [id]
      field_simp
      ring
    have hA0 : A w ≠ 0 := slitPlane_ne_zero (hUs w hw).1
    have hB0 : B w ≠ 0 := slitPlane_ne_zero (hUs w hw).2
    refine ((hAd.cpow_const (c := a₁) (hUs w hw).1).mul
      (hBd.cpow_const (c := b₁) (hUs w hw).2)).congr_deriv ?_
    rw [cpow_sub _ _ hA0, cpow_sub _ _ hB0, cpow_one, cpow_one]
    simp only [hP, hL, hA, hB]
    field_simp
    ring
  have hPdd : deriv (deriv P) z = P z * (L z ^ 2 +
      (a₁ * (-((z - α) ^ 2)⁻¹ + ((z - γ) ^ 2)⁻¹) + b₁ * (-((z - β) ^ 2)⁻¹ + ((z - γ) ^ 2)⁻¹))) := by
    have hev : deriv P =ᶠ[𝓝 z] fun w => P w * L w := by
      filter_upwards [hU.mem_nhds hz] with w hw
      rw [(hPd w hw).deriv]
    rw [hev.deriv_eq]
    have hLd : HasDerivAt L (a₁ * (-((z - α) ^ 2)⁻¹ + ((z - γ) ^ 2)⁻¹) +
        b₁ * (-((z - β) ^ 2)⁻¹ + ((z - γ) ^ 2)⁻¹)) z := by
      have h := ((((hasDerivAt_id z).sub_const α).inv hzα).sub
        (((hasDerivAt_id z).sub_const γ).inv hzγ)).const_mul a₁ |>.add
        (((((hasDerivAt_id z).sub_const β).inv hzβ).sub
        (((hasDerivAt_id z).sub_const γ).inv hzγ)).const_mul b₁)
      refine h.congr_deriv ?_
      simp only [id]
      ring
    have hd : HasDerivAt (fun w => P w * L w) _ z := (hPd z hz).mul hLd
    rw [hd.deriv]
    ring
  set k : ℂ := (β - γ) * (α - γ) / (β - α) with hk
  have hTd : ∀ w : ℂ, w - γ ≠ 0 → HasDerivAt T (k * ((w - γ) ^ 2)⁻¹) w := by
    intro w hw
    have h := (((hasDerivAt_id w).sub_const α).mul_const (β - γ)).div
      (((hasDerivAt_id w).sub_const γ).mul_const (β - α)) (mul_ne_zero hw h4')
    refine h.congr_deriv ?_
    simp only [id, hk]
    field_simp
    ring
  have hTdd : deriv (deriv T) z = -2 * k * ((z - γ) ^ 3)⁻¹ := by
    have hopen : IsOpen {w : ℂ | w - γ ≠ 0} := isOpen_ne_fun (by fun_prop) continuous_const
    have hev : deriv T =ᶠ[𝓝 z] fun w => k * ((w - γ) ^ 2)⁻¹ := by
      filter_upwards [hopen.mem_nhds hzγ] with w hw
      rw [(hTd w hw).deriv]
    rw [hev.deriv_eq]
    have h := ((((hasDerivAt_id z).sub_const γ).pow 2).inv (pow_ne_zero 2 hzγ)).const_mul k
    have hd : HasDerivAt (fun w => k * ((w - γ) ^ 2)⁻¹) _ z := h
    rw [hd.deriv]
    simp only [id, Nat.cast_ofNat, Pi.pow_apply]
    field_simp
    ring
  have hode := hu' (T z) (hUV z hz)
  rw [hw, deriv_deriv_mul_comp (hPa z hz) (hTa z hz) (hFa z hz),
    (deriv_mul_comp_eventuallyEq (hPa z hz) (hTa z hz) (hFa z hz)).eq_of_nhds, hPdd,
    (hPd z hz).deriv, hTdd, (hTd z hzγ).deriv]
  beta_reduce
  have hc2 : c₂ = 1 - a₁ - a₂ - b₁ - b₂ - c₁ := by linear_combination hsum
  subst hc2
  generalize u (T z) = F0 at *
  generalize deriv u (T z) = F1 at *
  generalize deriv (deriv u) (T z) = F2 at *
  generalize P z = P0
  simp only [T, L, k] at hode ⊢
  linear_combination (norm := skip) (P0 * ((β - γ) * (α - γ) / (β - α)) ^ 2 * (β - α) ^ 2 *
    (z - γ) ^ 2 / ((z - α) * (β - γ) * (γ - α) * (z - β)) / (z - γ) ^ 4) * hode
  field_simp
  ring

end TauCeti
