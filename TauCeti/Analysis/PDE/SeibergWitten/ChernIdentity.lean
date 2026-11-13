/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.SelfDual
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Integral
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity

/-!
# The Chern identity and the `L¹` defect bound at large parameter

On a closed symplectic four-manifold `X` Taubes perturbs the Seiberg–Witten curvature equation by
a large multiple `r` of the symplectic form `ω`, which is self-dual for a compatible metric. A
solution has normalized spinor `χ = α u₀ + β` and a connection `a` on the line `E`. At each point,
the `ω`-component of the curvature equation for the real two-form `F = i F_a` reads

`⟨ω, F⟩ / 2 = (r / 8) (1 - |α|² + |β|²) - ⟨ω, η⟩ / 4`,

where `η` is the perturbation (`TauCeti.SeibergWitten.inner_div_two_eq_of_add_hodgeStar_eq`).
Integrated over `X`, the left side does not depend on the solution: `F` is closed and its de Rham
class is `2π c₁(E)`, so by Chern–Weil theory `∫_X ⟨F, ω⟩ vol = ∫_X F ∧ ω` is the cohomological
pairing `⟨[F] ∪ [ω], [X]⟩`
(`TauCeti.SmoothForm.integralTopForm_inner_smul_riemannianVolumeForm_eq_poincarePairing`). This
gives the **Chern identity**

`r ∫_X (1 - |α|² + |β|²) vol = 4 ⟨[F] ∪ [ω], [X]⟩ + 2 ∫_X ⟨ω, η⟩ vol`

(`TauCeti.SeibergWitten.mul_integralTopForm_one_sub_add_eq`). Combined with the pointwise bound
`|α|² + |β|² ≤ 1 + C / r`, which gives `r |1 - |α|² - |β|²| ≤ r (1 - |α|² + |β|²) + 2 C`, it
yields Taubes's **`L¹` defect bound**

`r ∫_X |1 - |χ|²| vol ≤ 4 ⟨[F] ∪ [ω], [X]⟩ + 2 ∫_X ⟨ω, η⟩ vol + 2 C Vol(X)`

(`TauCeti.SeibergWitten.mul_integralTopForm_abs_one_sub_sub_le`). The right side depends only on
the class of `F`, the perturbation and the constant `C`, not on `r` or on the solution. The
large-parameter estimates take this bound as a hypothesis, stated there for an abstract finite
measure, for instance in `TauCeti.SeibergWitten.integral_le_of_le_mul_max_one_sub`.

The statements take the pointwise squared norms `s = |α|²` and `t = |β|²` as functions on `X`,
the `ω`-component of the curvature equation as a pointwise hypothesis, and the de Rham class of
`F` through the Poincaré pairing `TauCeti.poincarePairing`. The symplectic form only enters as a
compactly supported closed self-dual two-form; its normalization `|ω| = √2` is part of the
pointwise identity.

## Main results

* `TauCeti.SeibergWitten.mul_abs_one_sub_sub_le`: the pointwise inequality
  `r |1 - s - t| ≤ r (1 - s + t) + 2 C` under `s + t ≤ 1 + C / r` and `t ≥ 0`.
* `TauCeti.SeibergWitten.mul_integralTopForm_one_sub_add_eq`: the Chern identity.
* `TauCeti.SeibergWitten.mul_integralTopForm_abs_one_sub_sub_le`: the `L¹` defect bound.

## References

* C. H. Taubes, *The Seiberg–Witten invariants and symplectic forms*, Math. Res. Lett. 1 (1994),
  809–822.
* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Section 2.
-/

public section

noncomputable section

open Bundle
open scoped Manifold

namespace TauCeti.SeibergWitten

/-- **The spinor defect is controlled by the `ω`-component.** If `0 ≤ t`, `0 ≤ C` and
`s + t ≤ 1 + C / r` with `r > 0`, then `r |1 - s - t| ≤ r (1 - s + t) + 2 C`. With `s = |α|²` and
`t = |β|²`, the right side is the `ω`-component of the large-parameter curvature equation up to
the constant `2 C`. -/
theorem mul_abs_one_sub_sub_le {s t r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C) (ht : 0 ≤ t)
    (hst : s + t ≤ 1 + C / r) :
    r * |1 - s - t| ≤ r * (1 - s + t) + 2 * C := by
  have h : r * (s + t) ≤ r + C := by
    calc r * (s + t) ≤ r * (1 + C / r) := mul_le_mul_of_nonneg_left hst hr.le
      _ = r + C := by field_simp
  rcases abs_cases (1 - s - t) with ⟨h₁, _⟩ | ⟨h₁, _⟩ <;> rw [h₁] <;> nlinarith

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : ℕ∞) M] [BoundarylessManifold I M] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x)]
  (o : Manifold.Orientation I M (Fin (2 + 2))) {ω F η : SmoothForm I M ℝ 2} {s t : M → ℝ}
  {r : ℝ}

/-- **The Chern identity for the large-parameter curvature equation.** Let `ω` be a compactly
supported closed self-dual two-form on an oriented boundaryless Riemannian four-manifold, `F` a
closed two-form and `η` a two-form, and suppose that the `ω`-component of the large-parameter
curvature equation `⟨ω, F⟩ / 2 = (r / 8) (1 - s + t) - ⟨ω, η⟩ / 4` holds at every point. Then

`r ∫_M (1 - s + t) vol = 4 ⟨[F], [ω]⟩ + 2 ∫_M ⟨ω, η⟩ vol`,

where `⟨[F], [ω]⟩ = ∫_M F ∧ ω` is the Poincaré pairing of the de Rham classes. For a solution
with normalized spinor `α u₀ + β`, `s = |α|²`, `t = |β|²` and `F = i F_a`, the right side depends
only on the line bundle, through the class `[F] = 2π c₁(E)`, and on the perturbation. -/
theorem mul_integralTopForm_one_sub_add_eq [SigmaCompactSpace M]
    (hω : ω ∈ compactlySupportedClosedForms I M 2)
    (hω' : ω ∈ SmoothForm.selfDualForms o) (hF : F ∈ closedForms I M 2)
    (hFω : ∀ x, alternatingFormInner (TangentSpace I x) 2 (ω.1 x) (F.1 x) / 2 =
      r / 8 * (1 - s x + t x) - alternatingFormInner (TangentSpace I x) 2 (ω.1 x) (η.1 x) / 4) :
    r * integralTopForm o (fun x ↦ (1 - s x + t x) • riemannianVolumeForm o x) =
      4 * poincarePairing I M o (deRhamCohomology.mk I 2 ⟨F, hF⟩)
          (compactlySupportedDeRhamCohomology.mk I 2 ⟨ω, hω⟩) +
        2 * integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 2 (ω.1 x) (η.1 x) •
          riemannianVolumeForm o x) := by
  have hc := (mem_compactlySupportedForms I).mp
    (compactlySupportedClosedForms_le_compactlySupportedForms I 2 hω)
  -- `∫ ⟨ω, F⟩ vol` is the Poincaré pairing of `[F]` and `[ω]`.
  have hpair : integralTopForm o (fun x ↦
      alternatingFormInner (TangentSpace I x) 2 (ω.1 x) (F.1 x) • riemannianVolumeForm o x) =
      poincarePairing I M o (deRhamCohomology.mk I 2 ⟨F, hF⟩)
        (compactlySupportedDeRhamCohomology.mk I 2 ⟨ω, hω⟩) := by
    rw [← SmoothForm.integralTopForm_inner_smul_riemannianVolumeForm_eq_poincarePairing o hF hω
      hω']
    simp only [alternatingFormInner_comm (ω.1 _)]
  -- The integrand is pointwise `4 ⟨ω, F⟩ vol + 2 ⟨ω, η⟩ vol`.
  have h : (fun x ↦ (r * (1 - s x + t x)) • riemannianVolumeForm o x) =
      (4 : ℝ) • (fun x ↦ alternatingFormInner (TangentSpace I x) 2 (ω.1 x) (F.1 x) •
        riemannianVolumeForm o x) +
      (2 : ℝ) • (fun x ↦ alternatingFormInner (TangentSpace I x) 2 (ω.1 x) (η.1 x) •
        riemannianVolumeForm o x) := by
    funext x
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_smul, smul_smul, ← add_smul]
    congr 1
    linarith [hFω x]
  rw [← integralTopForm_mul_smul_riemannianVolumeForm, h, integralTopForm_add o
    (((SmoothForm.isSmoothForm_inner_smul_riemannianVolumeForm o rfl ω F).of_le bot_le).smul 4)
    (((SmoothForm.isSmoothForm_inner_smul_riemannianVolumeForm o rfl ω η).of_le bot_le).smul 2)
    (by rw [RoughForm.tsupport_smul _ _ (by norm_num)]
        exact RoughForm.isCompact_tsupport_inner_smul_riemannianVolumeForm o ω.1 F.1 hc)
    (by rw [RoughForm.tsupport_smul _ _ (by norm_num)]
        exact RoughForm.isCompact_tsupport_inner_smul_riemannianVolumeForm o ω.1 η.1 hc),
    integralTopForm_smul, integralTopForm_smul, hpair]

/-- **Taubes's `L¹` defect bound.** On a closed oriented Riemannian four-manifold, let `ω` be a
closed self-dual two-form, `F` a closed two-form and `η` a two-form, and let `s` and `t ≥ 0` be
continuous functions with `s + t ≤ 1 + C / r`, where `r > 0` and `C ≥ 0`. If the `ω`-component of
the large-parameter curvature equation `⟨ω, F⟩ / 2 = (r / 8) (1 - s + t) - ⟨ω, η⟩ / 4` holds at
every point, then

`r ∫_M |1 - s - t| vol ≤ 4 ⟨[F], [ω]⟩ + 2 ∫_M ⟨ω, η⟩ vol + 2 C Vol(M)`.

For a solution with normalized spinor `χ = α u₀ + β`, `s = |α|²`, `t = |β|²` and `F = i F_a`,
this bounds `r ∫_M |1 - |χ|²| vol` independently of `r` and of the solution, given the class of
`F`, the perturbation `η` and the constant `C` of the pointwise bound `|χ|² ≤ 1 + C / r`. -/
theorem mul_integralTopForm_abs_one_sub_sub_le [CompactSpace M] {C : ℝ} (hr : 0 < r)
    (hC : 0 ≤ C) (hs : Continuous s) (ht : Continuous t) (ht₀ : ∀ x, 0 ≤ t x)
    (hst : ∀ x, s x + t x ≤ 1 + C / r) (hω : ω ∈ compactlySupportedClosedForms I M 2)
    (hω' : ω ∈ SmoothForm.selfDualForms o) (hF : F ∈ closedForms I M 2)
    (hFω : ∀ x, alternatingFormInner (TangentSpace I x) 2 (ω.1 x) (F.1 x) / 2 =
      r / 8 * (1 - s x + t x) - alternatingFormInner (TangentSpace I x) 2 (ω.1 x) (η.1 x) / 4) :
    r * integralTopForm o (fun x ↦ |1 - s x - t x| • riemannianVolumeForm o x) ≤
      4 * poincarePairing I M o (deRhamCohomology.mk I 2 ⟨F, hF⟩)
          (compactlySupportedDeRhamCohomology.mk I 2 ⟨ω, hω⟩) +
        2 * integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 2 (ω.1 x) (η.1 x) •
          riemannianVolumeForm o x) +
        2 * C * integralTopForm o (riemannianVolumeForm o) := by
  have hvol : integralTopForm o (fun x ↦ (2 * C) • riemannianVolumeForm o x) =
      2 * C * integralTopForm o (riemannianVolumeForm o) := by
    rw [← integralTopForm_smul, Pi.smul_def]
  rw [← integralTopForm_mul_smul_riemannianVolumeForm]
  calc _ ≤ integralTopForm o (fun x ↦ (r * (1 - s x + t x) + 2 * C) • riemannianVolumeForm o x) :=
        integralTopForm_smul_riemannianVolumeForm_mono o (by fun_prop) (by fun_prop)
          fun x ↦ mul_abs_one_sub_sub_le hr hC (ht₀ x) (hst x)
    _ = _ := by
      rw [integralTopForm_add_smul_riemannianVolumeForm o (by fun_prop) continuous_const,
        integralTopForm_mul_smul_riemannianVolumeForm, mul_integralTopForm_one_sub_add_eq o hω hω'
          hF hFω, hvol]

end TauCeti.SeibergWitten
