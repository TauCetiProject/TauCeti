/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.SelfDual.Basic
import TauCeti.Geometry.Manifold.Riemannian.Codifferential
import Mathlib.Tactic.Linarith

/-!
# The wall coordinate of Taubes's large-parameter perturbation

On a closed oriented Riemannian four-manifold with `b₂⁺ = 1`, the Seiberg–Witten moduli space of
a `Spinᶜ` structure with determinant line `L` has reducible solutions exactly on the wall of
perturbations `η` with `w(g, η) = 0`, where

`w(g, η) = ⟨harm⁺ (F_A - η), i ω_g⟩_{L²} = -2π (c₁(L) - [i η / 2π]) · [ω_g]`

for a reference connection `A` on `L` and a self-dual harmonic form `ω_g`. The two sides
`w > 0` and `w < 0` are the chambers in which the invariant is defined. As elsewhere in this
directory, imaginary forms are indexed by real ones: the real curvature `i F_A` and the real
perturbation `i η` are smooth real two-forms. Since `ω_g` is self-dual harmonic, taking the
self-dual harmonic part does not change the `L²` pairing with `ω_g`, so in these terms

`w(g, η) = ∫_M ⟨i η - i F_A, ω_g⟩ vol`.

For a closed form `F = i F_A` this is `∫_M ⟨i η, ω_g⟩ vol - ⟨[F], [ω_g]⟩`, where
`⟨[F], [ω_g]⟩ = ∫_M F ∧ ω_g` is the Poincaré pairing of de Rham classes
(`TauCeti.SeibergWitten.integralTopForm_inner_sub_eq_sub_poincarePairing`). With
`[F] = 2π c₁(L)` this is the identity `w = -2π Δ` for the real cohomological coordinate
`Δ = (c₁(L) - [i η / 2π]) · [ω_g]`, where the class of the possibly nonclosed form `i η` is
read through its `L²` pairing with `ω_g`.

On a symplectic four-manifold with compatible metric, Taubes perturbs the curvature equation of
the twisted canonical `Spinᶜ` structure by `η_r + ρ`, with `η_r = F_{A₀}⁺ - i r ω / 4`. Here
`A₀` is the canonical connection on the anticanonical line `K⁻¹`, `ω` is the symplectic form,
which is self-dual and closed, `r` is a large parameter and `ρ` a small imaginary self-dual
forcing. The determinant connection is `A₀ + 2 a` for a connection `a` on the twisting line
`E`. In real terms, `i η_r = F₀⁺ + (r / 4) ω` with `F₀ = i F_{A₀}`, and the reference
curvature is `F₀ + 2 F` with `F = i F_a`. Since `F₀ - F₀⁺` is anti-self-dual, it is orthogonal
to `ω` at every point, so the wall coordinate is

`w(g, η_r + ρ) = (r / 4) ‖ω‖₂² - 2 ⟨[F], [ω]⟩ + ⟨i ρ, ω⟩₂`

(`TauCeti.SeibergWitten.integralTopForm_inner_selfDualPart_add_smul_add_sub_eq`). With
`[F] = 2π c₁(E)` the middle term is `-4π ⟨c₁(E) ∪ [ω], [X]⟩`. In particular the canonical
connection enters only through the self-dual part that `η_r` already contains, and `F₀` need not
be closed.

The first term grows linearly in `r` while the others are bounded in terms of `‖ω‖₂`, the
pairing `⟨[F], [ω]⟩` and `‖ρ‖₂`. On a compact manifold this gives a uniform wall gap
(`TauCeti.SeibergWitten.mul_div_le_integralTopForm_inner_selfDualPart_add_smul_add_sub`): if
`a ≤ ‖ω‖₂²`, `|⟨[F], [ω]⟩| ≤ b` and `‖ρ‖₂² ≤ c` with `a > 0`, then
`w(g, η_r + ρ) ≥ r a / 8` as soon as `r a ≥ 4 a + 16 b + 4 c`. The constants `a`, `b`, `c`
are all that the threshold depends on, so the bound is uniform over any family of metrics,
symplectic forms and forcings with such bounds. In particular the large-parameter perturbations
lie in the chamber `w > 0`.

## Main results

* `TauCeti.SeibergWitten.integralTopForm_inner_sub_eq_sub_poincarePairing`:
  `∫_M ⟨η - F, ω⟩ vol = ∫_M ⟨η, ω⟩ vol - ⟨[F], [ω]⟩` for closed `F` and closed self-dual `ω`.
* `TauCeti.SeibergWitten.integralTopForm_inner_selfDualPart_add_smul_add_sub_eq`: the value
  `(r / 4) ‖ω‖₂² - 2 ⟨[F], [ω]⟩ + ⟨ρ, ω⟩₂` of the wall coordinate at `η_r + ρ`.
* `TauCeti.SeibergWitten.mul_div_le_integralTopForm_inner_selfDualPart_add_smul_add_sub`: the
  uniform wall gap `w(g, η_r + ρ) ≥ r a / 8`.

## References

* C. H. Taubes, *The Seiberg–Witten invariants and symplectic forms*, Math. Res. Lett. 1 (1994),
  809–822.
* C. H. Taubes, *The Seiberg–Witten and Gromov invariants*, Math. Res. Lett. 2 (1995), 221–238.
-/

public section

noncomputable section

open Bundle
open scoped Manifold

namespace TauCeti.SeibergWitten

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : ℕ∞) M] [BoundarylessManifold I M] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x)]
  (o : Manifold.Orientation I M (Fin (2 + 2))) {ω F : SmoothForm I M ℝ 2}

/-- **The wall coordinate is a cohomological coordinate.** On an oriented boundaryless Riemannian
four-manifold, let `ω` be a compactly supported closed self-dual two-form, `F` a closed two-form
and `η` any two-form. Then

`∫_M ⟨η - F, ω⟩ vol = ∫_M ⟨η, ω⟩ vol - ⟨[F], [ω]⟩`.

For `F = i F_A` the real curvature of a connection on the determinant line `L`, `η` the real form
of the perturbation and `ω = ω_g` the self-dual harmonic form, the left side is the wall
coordinate `w(g, η)` and the right side is `-2π (c₁(L) - [η / 2π]) · [ω_g]`. -/
theorem integralTopForm_inner_sub_eq_sub_poincarePairing [SigmaCompactSpace M]
    (hω : ω ∈ compactlySupportedClosedForms I M 2) (hω' : ω ∈ SmoothForm.selfDualForms o)
    (hF : F ∈ closedForms I M 2) (η : SmoothForm I M ℝ 2) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 2 ((η - F).val x) (ω.val x) •
        riemannianVolumeForm o x) =
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 2 (η.val x) (ω.val x) •
        riemannianVolumeForm o x) -
      poincarePairing I M o (deRhamCohomology.mk I 2 ⟨F, hF⟩)
        (compactlySupportedDeRhamCohomology.mk I 2 ⟨ω, hω⟩) := by
  have hc : ω ∈ compactlySupportedForms I M 2 :=
    compactlySupportedClosedForms_le_compactlySupportedForms I 2 hω
  have h := SmoothForm.integralTopForm_inner_add_left o rfl (η - F) F ω (.inr hc)
  rw [sub_add_cancel,
    SmoothForm.integralTopForm_inner_smul_riemannianVolumeForm_eq_poincarePairing o hF hω hω'] at h
  linarith

/-- **The wall coordinate of Taubes's perturbation.** On an oriented boundaryless Riemannian
four-manifold, let `ω` be a compactly supported closed self-dual two-form and `F` a closed
two-form, and let `F₀`, `ρ` be any two-forms and `r` a real number. Then

`∫_M ⟨(F₀⁺ + (r / 4) ω + ρ) - (F₀ + 2 F), ω⟩ vol = (r / 4) ‖ω‖₂² - 2 ⟨[F], [ω]⟩ + ⟨ρ, ω⟩₂`.

With `F₀ = i F_{A₀}` for the canonical connection `A₀`, `F = i F_a` for a connection `a` on the
twisting line and `ρ` the real form of the forcing, the left side is the wall coordinate of the
perturbation `F_{A₀}⁺ - i r ω / 4 + ρ` relative to the reference connection `A₀ + 2 a`: the
anti-self-dual part of `F₀` is orthogonal to `ω` at every point and does not contribute. -/
theorem integralTopForm_inner_selfDualPart_add_smul_add_sub_eq [SigmaCompactSpace M]
    (hω : ω ∈ compactlySupportedClosedForms I M 2) (hω' : ω ∈ SmoothForm.selfDualForms o)
    (hF : F ∈ closedForms I M 2) (F₀ ρ : SmoothForm I M ℝ 2) (r : ℝ) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 2
        ((SmoothForm.selfDualPart o F₀ + (r / 4) • ω + ρ - (F₀ + (2 : ℝ) • F)).val x) (ω.val x) •
        riemannianVolumeForm o x) =
      r / 4 * integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 2 (ω.val x)
          (ω.val x) • riemannianVolumeForm o x) -
        2 * poincarePairing I M o (deRhamCohomology.mk I 2 ⟨F, hF⟩)
          (compactlySupportedDeRhamCohomology.mk I 2 ⟨ω, hω⟩) +
        integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 2 (ρ.val x) (ω.val x) •
          riemannianVolumeForm o x) := by
  have hc : ω ∈ compactlySupportedForms I M 2 :=
    compactlySupportedClosedForms_le_compactlySupportedForms I 2 hω
  -- The anti-self-dual part `F₀⁺ - F₀ = -F₀⁻` pairs to zero with `ω` at every point.
  have h₀ : integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 2
      ((SmoothForm.selfDualPart o F₀ - F₀).val x) (ω.val x) • riemannianVolumeForm o x) = 0 := by
    have hω'' := (SmoothForm.coe_mem_selfDualForms_iff (o := o)).mpr hω'
    convert integralTopForm_zero o using 2
    funext x
    rw [Submodule.coe_sub, Pi.sub_apply, LinearMap.map_sub₂, SmoothForm.coe_selfDualPart,
      RoughForm.alternatingFormInner_selfDualPart_of_mem_selfDualForms o even_two _ hω'' x,
      sub_self, zero_smul, Pi.zero_apply]
  have hsplit : SmoothForm.selfDualPart o F₀ + (r / 4) • ω + ρ - (F₀ + (2 : ℝ) • F) =
      (r / 4) • ω + ρ + (-2 : ℝ) • F + (SmoothForm.selfDualPart o F₀ - F₀) := by
    module
  rw [hsplit, SmoothForm.integralTopForm_inner_add_left o rfl _ _ _ (.inr hc), h₀,
    SmoothForm.integralTopForm_inner_add_left o rfl _ _ _ (.inr hc),
    SmoothForm.integralTopForm_inner_add_left o rfl _ _ _ (.inr hc),
    SmoothForm.integralTopForm_inner_smul_left, SmoothForm.integralTopForm_inner_smul_left,
    SmoothForm.integralTopForm_inner_smul_riemannianVolumeForm_eq_poincarePairing o hF hω hω']
  ring

/-- **The uniform wall gap at large parameter.** On a closed oriented Riemannian four-manifold,
let `ω` be a closed self-dual two-form and `F` a closed two-form, and let `F₀`, `ρ` be any
two-forms. Suppose `a ≤ ‖ω‖₂²` with `a > 0`, `|⟨[F], [ω]⟩| ≤ b` and `‖ρ‖₂² ≤ c`. Then the wall
coordinate of Taubes's perturbation satisfies

`r a / 8 ≤ ∫_M ⟨(F₀⁺ + (r / 4) ω + ρ) - (F₀ + 2 F), ω⟩ vol`

as soon as `4 a + 16 b + 4 c ≤ r a`. The threshold and the gap depend only on `a`, `b` and `c`, so
the large-parameter perturbations lie in the chamber `w > 0`, uniformly over any family of data
with such bounds. -/
theorem mul_div_le_integralTopForm_inner_selfDualPart_add_smul_add_sub [CompactSpace M]
    (hω : ω ∈ compactlySupportedClosedForms I M 2) (hω' : ω ∈ SmoothForm.selfDualForms o)
    (hF : F ∈ closedForms I M 2) (F₀ ρ : SmoothForm I M ℝ 2) {r a b c : ℝ} (ha : 0 < a)
    (haω : a ≤ integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 2 (ω.val x)
      (ω.val x) • riemannianVolumeForm o x))
    (hb : |poincarePairing I M o (deRhamCohomology.mk I 2 ⟨F, hF⟩)
      (compactlySupportedDeRhamCohomology.mk I 2 ⟨ω, hω⟩)| ≤ b)
    (hc : integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 2 (ρ.val x)
      (ρ.val x) • riemannianVolumeForm o x) ≤ c)
    (hr : 4 * a + 16 * b + 4 * c ≤ r * a) :
    r * a / 8 ≤ integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 2
        ((SmoothForm.selfDualPart o F₀ + (r / 4) • ω + ρ - (F₀ + (2 : ℝ) • F)).val x) (ω.val x) •
        riemannianVolumeForm o x) := by
  rw [integralTopForm_inner_selfDualPart_add_smul_add_sub_eq o hω hω' hF]
  set A := integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 2 (ω.val x)
    (ω.val x) • riemannianVolumeForm o x)
  set R := integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 2 (ρ.val x)
    (ρ.val x) • riemannianVolumeForm o x)
  set Q := integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 2 (ρ.val x)
    (ω.val x) • riemannianVolumeForm o x)
  set P := poincarePairing I M o (deRhamCohomology.mk I 2 ⟨F, hF⟩)
    (compactlySupportedDeRhamCohomology.mk I 2 ⟨ω, hω⟩)
  -- Young's inequality `-2 ⟨ρ, ω⟩₂ ≤ ‖ρ‖₂² + ‖ω‖₂²`.
  have hQ : -(R + A) ≤ 2 * Q :=
    SmoothForm.neg_add_le_two_mul_integralTopForm_inner o rfl
      (by simp [compactlySupportedForms_eq_top])
      (compactlySupportedClosedForms_le_compactlySupportedForms I 2 hω)
  have hR₀ : 0 ≤ R := RoughForm.integralTopForm_inner_self_smul_riemannianVolumeForm_nonneg o ρ.val
  have hP : P ≤ b := (le_abs_self P).trans hb
  -- `r ≥ 4` from `4 a ≤ r a`, so the coefficient `r / 4 - 1 / 2` of `A ≥ a` is positive. Then
  -- `r A / 4 - 2 P + Q ≥ (r / 4 - 1 / 2) A - 2 b - c / 2 ≥ (r / 4 - 1 / 2) a - 2 b - c / 2`,
  -- which is at least `r a / 8` exactly when `4 a + 16 b + 4 c ≤ r a`.
  have hr₄ : 4 ≤ r := le_of_mul_le_mul_right (by linarith [(abs_nonneg P).trans hb]) ha
  have hA : (r / 4 - 1 / 2) * a ≤ (r / 4 - 1 / 2) * A :=
    mul_le_mul_of_nonneg_left haω (by linarith)
  linarith

end TauCeti.SeibergWitten
