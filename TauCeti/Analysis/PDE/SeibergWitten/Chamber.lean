/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.SelfDual.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Integral

/-!
# The large-parameter perturbations lie in the positive chamber

On a closed oriented Riemannian four-manifold `X` with `b₂⁺ = 1`, the Seiberg–Witten invariant
depends on a chamber. Fix a closed self-dual two-form `ω` spanning the harmonic self-dual line,
for instance the symplectic form of a compatible metric. For a reference determinant connection
with curvature `F_ref` and a perturbation `η`, the reducible solutions are cut out by the vanishing
of the **wall coordinate**

`w(η) = ⟨harm⁺(F_ref - η), i ω⟩_{L²} = ∫_X ⟨F_ref - η, i ω⟩ vol`,

the two pairings agreeing because `ω` is harmonic and self-dual, so that pairing with `ω` only
sees the harmonic self-dual projection. The chambers are `C₊ = {w > 0}` and `C₋ = {w < 0}`.

As elsewhere in these files an imaginary form `x` is indexed by the real form `i x`. So `F` stands
for the closed real form `i F_ref`, whose de Rham class is `2π l` for the first Chern class `l` of
the determinant line, and `η` for the real form `i η`. Since `⟨-i α, i β⟩ = -⟨α, β⟩`, the wall
coordinate is

`w = ∫_X ⟨η - F, ω⟩ vol`,

the integral appearing in every statement below. This file computes it.

* **The cohomological coordinate.** By Chern–Weil theory the pairing `∫_X ⟨F, ω⟩ vol` is the
  Poincaré pairing `⟨[F] ∪ [ω], [X]⟩`, so
  `w = ∫_X ⟨η, ω⟩ vol - ⟨[F] ∪ [ω], [X]⟩ = -2π Δ`, where
  `Δ = ⟨l ∪ [ω], [X]⟩ - (2π)⁻¹ ∫_X ⟨η, ω⟩ vol` is the real cohomological coordinate
  (`TauCeti.SeibergWitten.integralTopForm_inner_sub_smul_riemannianVolumeForm_eq`). When `η` is
  closed this is `-⟨([F] - [η]) ∪ [ω], [X]⟩`
  (`TauCeti.SeibergWitten.integralTopForm_inner_sub_smul_riemannianVolumeForm_eq_neg`). Thus
  `Δ < 0` is the chamber `C₊`.
* **The large-parameter formula.** Taubes perturbs by `η_r + ρ` with
  `η_r = F_{A₀}⁺ - i r ω / 4` for the canonical connection `A₀` and a self-dual forcing `ρ`, and
  writes `A = A₀ + 2 a` for a connection `a` on the twisting line `E`, with reference curvature
  `F_ref = F_{A₀} + 2 F_a`. In real indexing `F = F₀ + 2 a` and the perturbation is
  `F₀⁺ + (r / 4) ω + ρ`, with `F₀ = i F_{A₀}` and `a = i F_a`. The anti-self-dual part of `F₀` is
  pointwise orthogonal to `ω`, so `F₀` drops out and
  `w = (r / 4) ‖ω‖₂² - 2 ⟨[a] ∪ [ω], [X]⟩ + ∫_X ⟨ρ, ω⟩ vol`
  (`TauCeti.SeibergWitten.integralTopForm_inner_largeParameter_eq`). With `[a] = 2π e` for the
  first Chern class `e` of `E`, this is Taubes's
  `w = (r / 4) ‖ω‖₂² - 4π ⟨e ∪ [ω], [X]⟩ + ⟨i ρ, ω⟩_{L²}`.
* **The wall gap.** Hence `w ≥ (r / 8) ‖ω‖₂²` as soon as
  `16 ⟨[a] ∪ [ω], [X]⟩ - 8 ∫_X ⟨ρ, ω⟩ vol ≤ r ‖ω‖₂²`
  (`TauCeti.SeibergWitten.mul_le_integralTopForm_inner_largeParameter`). On a compact manifold a
  pointwise bound `|ρ| ≤ K` bounds the forcing term by `K ∫_X |ω| vol`
  (`TauCeti.abs_integralTopForm_inner_smul_riemannianVolumeForm_le`), and so the large-parameter
  perturbations satisfy the uniform gap `w ≥ (r / 8) ‖ω‖₂²` for every forcing of norm at most
  `K` once `r ‖ω‖₂² ≥ 16 |⟨[a] ∪ [ω], [X]⟩| + 8 K ∫_X |ω| vol`
  (`TauCeti.SeibergWitten.mul_le_integralTopForm_inner_largeParameter_of_norm_le`). The
  threshold depends on the data only through `‖ω‖₂²`, `∫_X |ω| vol`, the class of `a` and `K`,
  which is what makes it uniform over a compact family of metrics and forcings. In particular,
  when `‖ω‖₂² > 0` the large-parameter perturbations lie in the chamber `C₊` for all large `r`.

The harmonic projection `harm⁺` itself is not constructed here: the statements are about the
`L²` pairing with `ω`, which is the wall coordinate once `ω` spans the harmonic self-dual forms.

## References

* C. H. Taubes, *The Seiberg–Witten and Gromov invariants*, Math. Res. Lett. 2 (1995), 221–238.
* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Section 1.
* C. Okonek and A. Teleman, *Seiberg–Witten invariants for manifolds with `b₊ = 1`, and the
  universal wall crossing formula*, Internat. J. Math. 7 (1996), 811–832.
-/

public section

noncomputable section

open Bundle
open scoped Manifold

namespace TauCeti.SeibergWitten

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : ℕ∞) M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x)]
  (o : Manifold.Orientation I M (Fin (2 + 2))) {ω F η : SmoothForm I M ℝ 2}

/-- **The wall coordinate is cohomological.** Let `ω` be a compactly supported closed self-dual
two-form on an oriented boundaryless Riemannian four-manifold and `F` a closed two-form. Then for
every two-form `η`,

`∫_M ⟨η - F, ω⟩ vol = ∫_M ⟨η, ω⟩ vol - ⟨[F], [ω]⟩`,

where `⟨[F], [ω]⟩ = ∫_M F ∧ ω` is the Poincaré pairing. For `F = i F_ref` with `[F] = 2π l` this
says that the wall coordinate is `-2π Δ` for the real cohomological coordinate
`Δ = ⟨l ∪ [ω], [X]⟩ - (2π)⁻¹ ∫_M ⟨η, ω⟩ vol`. -/
theorem integralTopForm_inner_sub_smul_riemannianVolumeForm_eq
    (hω : ω ∈ compactlySupportedClosedForms I M 2) (hω' : ω ∈ SmoothForm.selfDualForms o)
    (hF : F ∈ closedForms I M 2) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 2 ((η - F).val x) (ω.val x) •
        riemannianVolumeForm o x) =
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 2 (η.val x) (ω.val x) •
          riemannianVolumeForm o x) -
        poincarePairing I M o (deRhamCohomology.mk I 2 ⟨F, hF⟩)
          (compactlySupportedDeRhamCohomology.mk I 2 ⟨ω, hω⟩) := by
  have hc := compactlySupportedClosedForms_le_compactlySupportedForms I 2 hω
  -- The pairing with `-F` is the negative of the pairing with `F`.
  have hneg : integralTopForm o (fun x ↦
      alternatingFormInner (TangentSpace I x) 2 ((-F).val x) (ω.val x) • riemannianVolumeForm o x) =
      -1 * integralTopForm o (fun x ↦
        alternatingFormInner (TangentSpace I x) 2 (F.val x) (ω.val x) •
          riemannianVolumeForm o x) := by
    rw [← integralTopForm_mul_smul_riemannianVolumeForm]
    congr 1
    funext x
    rw [Submodule.coe_neg, Pi.neg_apply, LinearMap.map_neg₂, neg_one_mul]
  rw [sub_eq_add_neg, SmoothForm.integralTopForm_inner_add_left o rfl η (-F) ω (Or.inr hc), hneg,
    SmoothForm.integralTopForm_inner_smul_riemannianVolumeForm_eq_poincarePairing o hF hω hω']
  ring

/-- **The wall coordinate of a closed perturbation.** If moreover `η` is closed, the wall
coordinate is `∫_M ⟨η - F, ω⟩ vol = -⟨[F] - [η], [ω]⟩`, the Poincaré pairing of `-[F - η]` with
`[ω]`. -/
theorem integralTopForm_inner_sub_smul_riemannianVolumeForm_eq_neg
    (hω : ω ∈ compactlySupportedClosedForms I M 2) (hω' : ω ∈ SmoothForm.selfDualForms o)
    (hF : F ∈ closedForms I M 2) (hη : η ∈ closedForms I M 2) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 2 ((η - F).val x) (ω.val x) •
        riemannianVolumeForm o x) =
      -poincarePairing I M o (deRhamCohomology.mk I 2 ⟨F, hF⟩ - deRhamCohomology.mk I 2 ⟨η, hη⟩)
        (compactlySupportedDeRhamCohomology.mk I 2 ⟨ω, hω⟩) := by
  rw [integralTopForm_inner_sub_smul_riemannianVolumeForm_eq o hω hω' hF,
    SmoothForm.integralTopForm_inner_smul_riemannianVolumeForm_eq_poincarePairing o hη hω hω',
    map_sub, LinearMap.sub_apply]
  ring

/-- **Taubes's large-parameter wall formula.** Let `ω` be a compactly supported closed self-dual
two-form, `F₀` and `ρ` two-forms, `a` a closed two-form and `r` a real number. Then

`∫_M ⟨(F₀⁺ + (r / 4) ω + ρ) - (F₀ + 2 a), ω⟩ vol
  = (r / 4) ∫_M |ω|² vol - 2 ⟨[a], [ω]⟩ + ∫_M ⟨ρ, ω⟩ vol`.

This is the wall coordinate of the reference curvature `F₀ + 2 a` and the perturbation
`F₀⁺ + (r / 4) ω + ρ`, the real forms of Taubes's `F_{A₀} + 2 F_a` and `η_r + ρ` with
`η_r = F_{A₀}⁺ - i r ω / 4`. The canonical curvature `F₀` drops out, since its anti-self-dual part
is pointwise orthogonal to `ω`. With `[a] = 2π e` the middle term is `-4π ⟨e ∪ [ω], [X]⟩`. -/
theorem integralTopForm_inner_largeParameter_eq (hω : ω ∈ compactlySupportedClosedForms I M 2)
    (hω' : ω ∈ SmoothForm.selfDualForms o) {F₀ a ρ : SmoothForm I M ℝ 2}
    (ha : a ∈ closedForms I M 2) (r : ℝ) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 2
        ((SmoothForm.selfDualPart o F₀ + (r / 4) • ω + ρ - (F₀ + (2 : ℝ) • a)).val x) (ω.val x) •
        riemannianVolumeForm o x) =
      r / 4 * integralTopForm o (fun x ↦
          alternatingFormInner (TangentSpace I x) 2 (ω.val x) (ω.val x) •
            riemannianVolumeForm o x) -
        2 * poincarePairing I M o (deRhamCohomology.mk I 2 ⟨a, ha⟩)
          (compactlySupportedDeRhamCohomology.mk I 2 ⟨ω, hω⟩) +
        integralTopForm o (fun x ↦
          alternatingFormInner (TangentSpace I x) 2 (ρ.val x) (ω.val x) •
            riemannianVolumeForm o x) := by
  have hc := compactlySupportedClosedForms_le_compactlySupportedForms I 2 hω
  -- Pairing with `ω` takes a constant factor out of the first argument.
  have hsmul (c : ℝ) (φ : SmoothForm I M ℝ 2) : integralTopForm o (fun x ↦
      alternatingFormInner (TangentSpace I x) 2 ((c • φ).val x) (ω.val x) •
        riemannianVolumeForm o x) =
      c * integralTopForm o (fun x ↦
        alternatingFormInner (TangentSpace I x) 2 (φ.val x) (ω.val x) •
          riemannianVolumeForm o x) := by
    rw [← integralTopForm_mul_smul_riemannianVolumeForm]
    congr 1
    funext x
    rw [Submodule.coe_smul, Pi.smul_apply, LinearMap.map_smul₂, smul_eq_mul]
  -- Since `F₀ = F₀⁺ + F₀⁻`, the integrand is that of `(r / 4) ω + ρ - 2 a` up to the term
  -- `⟨F₀⁻, ω⟩`, which vanishes pointwise because `F₀⁻` is anti-self-dual and `ω` self-dual.
  have hω'' := (SmoothForm.coe_mem_selfDualForms_iff (o := o)).2 hω'
  have hF₀ := (SmoothForm.coe_mem_antiSelfDualForms_iff (o := o)).2
    (SmoothForm.antiSelfDualPart_mem_antiSelfDualForms o even_two F₀)
  have hint : (fun x ↦ alternatingFormInner (TangentSpace I x) 2
      ((SmoothForm.selfDualPart o F₀ + (r / 4) • ω + ρ - (F₀ + (2 : ℝ) • a)).val x) (ω.val x) •
        riemannianVolumeForm o x) = fun x ↦ alternatingFormInner (TangentSpace I x) 2
      (((r / 4) • ω + ρ + (-2 : ℝ) • a).val x) (ω.val x) • riemannianVolumeForm o x := by
    funext x
    have h0 := RoughForm.alternatingFormInner_eq_zero_of_mem_selfDualForms o hω'' hF₀ x
    rw [alternatingFormInner_comm] at h0
    have heq : SmoothForm.selfDualPart o F₀ + (r / 4) • ω + ρ - (F₀ + (2 : ℝ) • a) =
        ((r / 4) • ω + ρ + (-2 : ℝ) • a) - SmoothForm.antiSelfDualPart o F₀ := by
      nth_rw 2 [← SmoothForm.selfDualPart_add_antiSelfDualPart o F₀]
      module
    rw [heq, Submodule.coe_sub, Pi.sub_apply, LinearMap.map_sub₂, h0, sub_zero]
  rw [hint, SmoothForm.integralTopForm_inner_add_left o rfl _ _ ω (Or.inr hc),
    SmoothForm.integralTopForm_inner_add_left o rfl _ _ ω (Or.inr hc), hsmul, hsmul,
    SmoothForm.integralTopForm_inner_smul_riemannianVolumeForm_eq_poincarePairing o ha hω hω']
  ring

/-- **The large-parameter wall gap.** Under the hypotheses of
`TauCeti.SeibergWitten.integralTopForm_inner_largeParameter_eq`, if
`16 ⟨[a], [ω]⟩ - 8 ∫_M ⟨ρ, ω⟩ vol ≤ r ∫_M |ω|² vol`, then the wall coordinate of the
large-parameter perturbation is at least `(r / 8) ∫_M |ω|² vol`. -/
theorem mul_le_integralTopForm_inner_largeParameter
    (hω : ω ∈ compactlySupportedClosedForms I M 2) (hω' : ω ∈ SmoothForm.selfDualForms o)
    {F₀ a ρ : SmoothForm I M ℝ 2} (ha : a ∈ closedForms I M 2) {r : ℝ}
    (hr : 16 * poincarePairing I M o (deRhamCohomology.mk I 2 ⟨a, ha⟩)
          (compactlySupportedDeRhamCohomology.mk I 2 ⟨ω, hω⟩) -
        8 * integralTopForm o (fun x ↦
          alternatingFormInner (TangentSpace I x) 2 (ρ.val x) (ω.val x) •
            riemannianVolumeForm o x) ≤
      r * integralTopForm o (fun x ↦
        alternatingFormInner (TangentSpace I x) 2 (ω.val x) (ω.val x) • riemannianVolumeForm o x)) :
    r / 8 * integralTopForm o (fun x ↦
        alternatingFormInner (TangentSpace I x) 2 (ω.val x) (ω.val x) • riemannianVolumeForm o x) ≤
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 2
        ((SmoothForm.selfDualPart o F₀ + (r / 4) • ω + ρ - (F₀ + (2 : ℝ) • a)).val x) (ω.val x) •
        riemannianVolumeForm o x) := by
  rw [integralTopForm_inner_largeParameter_eq o hω hω' ha r]
  linarith

section Compact

variable [CompactSpace M]

/-- **The uniform large-parameter wall gap.** On a compact oriented Riemannian four-manifold, let
`ω` be a closed self-dual two-form, `F₀` a two-form, `a` a closed two-form and `ρ` a two-form of
pointwise norm at most `K`. If

`16 |⟨[a], [ω]⟩| + 8 K ∫_M |ω| vol ≤ r ∫_M |ω|² vol`,

then the wall coordinate of the large-parameter perturbation `F₀⁺ + (r / 4) ω + ρ` relative to the
reference curvature `F₀ + 2 a` is at least `(r / 8) ∫_M |ω|² vol`. The threshold on `r` does not
depend on `F₀` or on `ρ` beyond `K`, so the gap is uniform over all forcings of norm at most `K`;
when `r > 0` and `∫_M |ω|² vol > 0` it puts these perturbations in the chamber `w > 0`. -/
theorem mul_le_integralTopForm_inner_largeParameter_of_norm_le
    (hω : ω ∈ compactlySupportedClosedForms I M 2) (hω' : ω ∈ SmoothForm.selfDualForms o)
    {F₀ a ρ : SmoothForm I M ℝ 2} (ha : a ∈ closedForms I M 2) {r K : ℝ}
    (hρ : ∀ x, √(alternatingFormInner (TangentSpace I x) 2 (ρ.val x) (ρ.val x)) ≤ K)
    (hr : 16 * |poincarePairing I M o (deRhamCohomology.mk I 2 ⟨a, ha⟩)
          (compactlySupportedDeRhamCohomology.mk I 2 ⟨ω, hω⟩)| +
        8 * K * integralTopForm o (fun x ↦
          √(alternatingFormInner (TangentSpace I x) 2 (ω.val x) (ω.val x)) •
            riemannianVolumeForm o x) ≤
      r * integralTopForm o (fun x ↦
        alternatingFormInner (TangentSpace I x) 2 (ω.val x) (ω.val x) • riemannianVolumeForm o x)) :
    r / 8 * integralTopForm o (fun x ↦
        alternatingFormInner (TangentSpace I x) 2 (ω.val x) (ω.val x) • riemannianVolumeForm o x) ≤
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 2
        ((SmoothForm.selfDualPart o F₀ + (r / 4) • ω + ρ - (F₀ + (2 : ℝ) • a)).val x) (ω.val x) •
        riemannianVolumeForm o x) := by
  refine mul_le_integralTopForm_inner_largeParameter o hω hω' ha ?_
  have h₁ := le_abs_self (poincarePairing I M o (deRhamCohomology.mk I 2 ⟨a, ha⟩)
    (compactlySupportedDeRhamCohomology.mk I 2 ⟨ω, hω⟩))
  have h₂ := neg_le_of_abs_le (abs_integralTopForm_inner_smul_riemannianVolumeForm_le o
    (ρ.isSmoothForm.of_le bot_le) (ω.isSmoothForm.of_le bot_le) hρ)
  linarith

end Compact

end TauCeti.SeibergWitten
