/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.SelfDual.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Interior
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Integral

/-!
# The energy identity of a two-form split along a unit vector field

Let `M` be an oriented Riemannian four-manifold with a unit vector field `T` and its dual
one-form `σ = ⟪T, ·⟫`; on a product `S¹ × Y` with the product metric these are `T = ∂ₛ` and
`σ = ds`. For a real two-form `F`, write `ι_T F` for its interior product with `T` and
`F⁺ = (F + ⋆F) / 2` for its self-dual part. Pointwise,

`2 ⟨σ ∧ ι_T F, F⁺⟩ vol = |ι_T F|² vol + (F ∧ F) / 2`

(`TauCeti.RoughForm.two_smul_inner_wedge_interior_selfDualPart_smul_riemannianVolumeForm`). This
is the identity of `⋀² V` proved in `Orientation.inner_ιMulti_twoVectorContraction_add_hodgeStar`,
read on the fibres of the bundle of forms: for alternating forms on an oriented four-dimensional
inner product space it says
`⟨σ ∧ ι_T F, F + ⋆F⟩ = |ι_T F|² + ⟨F, ⋆F⟩ / 2`
(`Orientation.alternatingFormInner_wedge_curryLeft_add_formHodgeStar`), and `F ∧ F = ⟨F, ⋆F⟩ vol`.

Integrating over `M`, for a compactly supported closed two-form `F` on a boundaryless manifold,

`2 ∫_M ⟨σ ∧ ι_T F, F⁺⟩ vol = ∫_M |ι_T F|² vol + ⟨[F] ∪ [F], [M]⟩ / 2`

(`TauCeti.SmoothForm.two_mul_integralTopForm_inner_wedge_interior_selfDualPart`), where the last
term is the Poincaré pairing of the de Rham class of `F` with itself.

This is the curvature half of the energy identity for the unperturbed Seiberg–Witten equations
on a product `S¹ × Y`, which rules out solutions on `Spinᶜ` structures whose determinant class
is not pulled back from `Y`. There the Dirac operator splits as `c(ds) ∇_T + B_A`, and when `ψ`
solves `F_A⁺ = q(ψ)`, `D_A ψ = 0`, the curvature term of `D_A² ψ` paired with `ψ` is pointwise
`2 ⟨ds ∧ ι_T F, F⁺⟩` for the real curvature `F = -i F_A`
(`TauCeti.SeibergWitten.re_inner_cliffordRestriction_ιMulti_twoVectorContraction`). With
`[F] = -2π c₁(L)` the topological term above is `2π² ⟨c₁(L)², [M]⟩`. The Weitzenböck formula for
the split Dirac operator, which turns the integrated identity into
`0 = ‖∇_T ψ‖² + ‖B_A ψ‖² + ‖ι_T F_A‖² + 2π² ⟨c₁(L)², [M]⟩`, is not part of this file.

## Main results

* `TauCeti.RoughForm.two_smul_inner_wedge_interior_selfDualPart_smul_riemannianVolumeForm`: the
  pointwise identity of top forms on an oriented Riemannian four-manifold.
* `TauCeti.SmoothForm.two_mul_integralTopForm_inner_wedge_interior_selfDualPart`: the integrated
  identity, with the Poincaré pairing of `[F]` with itself.
* `TauCeti.SmoothForm.interior_eq_zero_and_poincarePairing_eq_zero_of_integralTopForm_nonpos`:
  if `∫_M ⟨σ ∧ ι_T F, F⁺⟩ vol ≤ 0` and `⟨[F] ∪ [F], [M]⟩ ≥ 0`, then `ι_T F = 0` and
  `⟨[F] ∪ [F], [M]⟩ = 0`.

## References

* C. H. Taubes, *The Seiberg–Witten invariants and symplectic forms*, Math. Res. Lett. 1 (1994),
  809–822.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §5.2.
-/

public section

noncomputable section

open Module Bundle
open scoped RealInnerProductSpace Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E]

namespace RoughForm

variable [IsManifold I 1 M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  (o : Manifold.Orientation I M (Fin (2 + 2))) {T : (x : M) → TangentSpace I x}
  {σ : RoughForm I M ℝ 1}

/-- **The pointwise energy identity of a two-form split along a unit vector field.** On an
oriented Riemannian four-manifold, let `T` be a unit vector field with dual one-form
`σ = ⟪T, ·⟫` and let `F` be a two-form. Then

`2 ⟨σ ∧ ι_T F, F⁺⟩ vol = |ι_T F|² vol + (F ∧ F) / 2`,

where `F⁺ = (F + ⋆F) / 2` is the self-dual part of `F` and `vol` the Riemannian volume form. On a
product `S¹ × Y` with `T = ∂ₛ` and `σ = ds`, this evaluates the curvature term of the square of
the Dirac operator at a Seiberg–Witten solution. -/
theorem two_smul_inner_wedge_interior_selfDualPart_smul_riemannianVolumeForm
    (hT : ∀ x, ‖T x‖ = 1)
    (hσ : ∀ x, σ x =
      ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) ℝ 0 (innerSL ℝ (T x)))
    (F : RoughForm I M ℝ 2) :
    ((2 : ℝ) • fun x ↦ alternatingFormInner (TangentSpace I x) 2 ((σ.wedge (F.interior T)) x)
        (selfDualPart o F x) • riemannianVolumeForm o x) =
      (fun x ↦ alternatingFormInner (TangentSpace I x) 1 (F.interior T x) (F.interior T x) •
        riemannianVolumeForm o x) + (2⁻¹ : ℝ) • F.wedge F := by
  funext x
  ext v
  let := o.fact_finrank_tangentSpace x
  have hkk : 2 + 2 = finrank ℝ (TangentSpace I x) := (o.fact_finrank_tangentSpace x).out.symm
  -- The wedge square is `⟨F, ⋆F⟩ vol`, since `⋆⋆F = F`.
  have hFF : F.wedge F x v =
      alternatingFormInner (TangentSpace I x) 2 (F x) (hodgeStar o rfl F x) *
        riemannianVolumeForm o x v := by
    have h := wedge_hodgeStar_apply o rfl F (hodgeStar o rfl F) x v
    rw [hodgeStar_hodgeStar_of_even o even_two] at h
    rw [wedge_def, wedgeWith_apply', ← ContinuousAlternatingMap.wedge_def, h]
    simp
  -- The interior product and the wedge `σ ∧ ι_T F` are taken pointwise.
  have hint : F.interior T x = (F x).curryLeft (T x) := by
    ext w
    simp [ContinuousAlternatingMap.curryLeft_apply_apply]
  have hwedge : (σ.wedge (F.interior T)) x =
      (ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) ℝ 0
        (innerSL ℝ (T x))).wedge ((F x).curryLeft (T x)) := by
    rw [wedge_def, wedgeWith_apply', ← ContinuousAlternatingMap.wedge_def, hσ, hint]
  have key := (o.orientationAt x).alternatingFormInner_wedge_curryLeft_add_formHodgeStar hkk
    (hT x) (F x)
  simp only [Pi.smul_apply, Pi.add_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.add_apply, smul_eq_mul, hFF, selfDualPart_apply, hwedge, hint,
    map_smul, map_add, hodgeStar_apply] at key ⊢
  linear_combination riemannianVolumeForm o x v * key

end RoughForm

namespace SmoothForm

variable [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  (o : Manifold.Orientation I M (Fin (2 + 2))) {T : (x : M) → TangentSpace I x}
  {σ : RoughForm I M ℝ 1}

/-- **The integrated energy identity of a two-form split along a unit vector field.** On an
oriented boundaryless Riemannian four-manifold, let `T` be a smooth unit vector field with dual
one-form `σ = ⟪T, ·⟫` and let `F` be a compactly supported closed two-form. Then

`2 ∫_M ⟨σ ∧ ι_T F, F⁺⟩ vol = ∫_M |ι_T F|² vol + ⟨[F] ∪ [F], [M]⟩ / 2`,

where `F⁺` is the self-dual part of `F` and the last term is the Poincaré pairing of the de Rham
class of `F` with itself. For the real curvature `F = -i F_A` of a unitary connection on a line
`L` over a closed four-manifold, `[F] = -2π c₁(L)` and the last term is `2π² ⟨c₁(L)², [M]⟩`. -/
theorem two_mul_integralTopForm_inner_wedge_interior_selfDualPart (hT : ∀ x, ‖T x‖ = 1)
    (hTs : ContMDiff I I.tangent ∞ fun x ↦ (T x : TangentBundle I M))
    (hσ : ∀ x, σ x =
      ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) ℝ 0 (innerSL ℝ (T x)))
    {F : SmoothForm I M ℝ 2} (hF : F ∈ compactlySupportedClosedForms I M 2) :
    2 * integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 2
        ((σ.wedge (RoughForm.interior T F.1)) x) ((selfDualPart o F).1 x) •
          riemannianVolumeForm o x) =
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 1
        (RoughForm.interior T F.1 x) (RoughForm.interior T F.1 x) • riemannianVolumeForm o x) +
      poincarePairing I M o
          (deRhamCohomology.mk I 2 ⟨F, ((mem_compactlySupportedClosedForms I).mp hF).2⟩)
          (compactlySupportedDeRhamCohomology.mk I 2 ⟨F, hF⟩) / 2 := by
  have hc := (mem_compactlySupportedForms I).mp ((mem_compactlySupportedClosedForms I).mp hF).1
  -- The interior product `ι_T F` is a smooth one-form supported in the support of `F`.
  let ιF : SmoothForm I M ℝ 1 :=
    ⟨RoughForm.interior T F.1, (F.isSmoothForm.interior hTs).mem_smoothBundleForms⟩
  have hιc : IsCompact (_root_.tsupport (α := E [⋀^Fin 1]→L[ℝ] ℝ) ιF.1) :=
    hc.of_isClosed_subset (_root_.isClosed_tsupport _) (RoughForm.tsupport_interior_subset T F.1)
  have hB : IsSmoothForm I 0 (fun x ↦ alternatingFormInner (TangentSpace I x) 1
      (RoughForm.interior T F.1 x) (RoughForm.interior T F.1 x) • riemannianVolumeForm o x) :=
    (isSmoothForm_inner_smul_riemannianVolumeForm o (show 1 + 3 = 2 + 2 from rfl) ιF ιF).of_le
      bot_le
  have hW : IsSmoothForm I 0 ((2⁻¹ : ℝ) • RoughForm.wedge F.1 F.1) := by
    rw [← coe_wedge]
    exact ((wedge F F).isSmoothForm.of_le bot_le).smul _
  have hww := (mem_compactlySupportedForms I).mp
    (wedge_mem_compactlySupportedForms F ((mem_compactlySupportedClosedForms I).mp hF).1)
  rw [coe_wedge] at hww
  rw [← integralTopForm_smul, coe_selfDualPart,
    RoughForm.two_smul_inner_wedge_interior_selfDualPart_smul_riemannianVolumeForm o hT hσ,
    integralTopForm_add o hB hW
      (RoughForm.isCompact_tsupport_inner_smul_riemannianVolumeForm o _ _ hιc)
      (by rw [RoughForm.tsupport_smul _ _ (by norm_num)]; exact hww),
    integralTopForm_smul, poincarePairing_mk]
  ring

/-- **Vanishing from the integrated energy identity.** On an oriented boundaryless Riemannian
four-manifold, let `T` be a smooth unit vector field with dual one-form `σ = ⟪T, ·⟫` and let `F`
be a compactly supported closed two-form. If `∫_M ⟨σ ∧ ι_T F, F⁺⟩ vol ≤ 0` and
`⟨[F] ∪ [F], [M]⟩ ≥ 0`, then `ι_T F = 0` and `⟨[F] ∪ [F], [M]⟩ = 0`.

For an unperturbed Seiberg–Witten solution on `S¹ × Y` with `T = ∂ₛ`, `σ = ds` and `F = -i F_A`,
the Weitzenböck formula for the split Dirac operator identifies `2 ∫_M ⟨σ ∧ ι_T F, F⁺⟩ vol` with
`-‖∇_T ψ‖² - ‖B_A ψ‖² ≤ 0`, and `⟨[F] ∪ [F], [M]⟩ = 4π² ⟨c₁(L)², [M]⟩`, a positive multiple of
the expected dimension of the moduli space. -/
theorem interior_eq_zero_and_poincarePairing_eq_zero_of_integralTopForm_nonpos
    (hT : ∀ x, ‖T x‖ = 1) (hTs : ContMDiff I I.tangent ∞ fun x ↦ (T x : TangentBundle I M))
    (hσ : ∀ x, σ x =
      ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) ℝ 0 (innerSL ℝ (T x)))
    {F : SmoothForm I M ℝ 2} (hF : F ∈ compactlySupportedClosedForms I M 2)
    (hneg : integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 2
        ((σ.wedge (RoughForm.interior T F.1)) x) ((selfDualPart o F).1 x) •
          riemannianVolumeForm o x) ≤ 0)
    (hpos : 0 ≤ poincarePairing I M o
      (deRhamCohomology.mk I 2 ⟨F, ((mem_compactlySupportedClosedForms I).mp hF).2⟩)
      (compactlySupportedDeRhamCohomology.mk I 2 ⟨F, hF⟩)) :
    RoughForm.interior T F.1 = 0 ∧ poincarePairing I M o
      (deRhamCohomology.mk I 2 ⟨F, ((mem_compactlySupportedClosedForms I).mp hF).2⟩)
      (compactlySupportedDeRhamCohomology.mk I 2 ⟨F, hF⟩) = 0 := by
  have h := two_mul_integralTopForm_inner_wedge_interior_selfDualPart o hT hTs hσ hF
  have hB := integralTopForm_smul_riemannianVolumeForm_nonneg o fun x ↦
    alternatingFormInner_self_nonneg (RoughForm.interior T F.1 x)
  refine ⟨?_, by linarith⟩
  -- The energy `∫_M |ι_T F|² vol` vanishes, and it is the `L²` norm of a smooth form.
  let ιF : SmoothForm I M ℝ 1 :=
    ⟨RoughForm.interior T F.1, (F.isSmoothForm.interior hTs).mem_smoothBundleForms⟩
  have hιc : ιF ∈ compactlySupportedForms I M 1 :=
    (mem_compactlySupportedForms I).mpr
      ((mem_compactlySupportedForms I).mp ((mem_compactlySupportedClosedForms I).mp hF).1
        |>.of_isClosed_subset (_root_.isClosed_tsupport _)
          (RoughForm.tsupport_interior_subset T F.1))
  have h0 := (integralTopForm_inner_self_smul_riemannianVolumeForm_eq_zero_iff o
    (show 1 + 3 = 2 + 2 from rfl) hιc).mp (by linarith)
  exact congrArg Subtype.val h0

end SmoothForm

end TauCeti
