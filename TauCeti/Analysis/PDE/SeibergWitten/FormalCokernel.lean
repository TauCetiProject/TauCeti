/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.AbelianDeformation

/-!
# The formal cokernel of the abelian deformation operator

The formal adjoint of `T = (-2 d*, d⁺)` is `T*(f, γ) = -2 df + d*γ`, with the scalar
component first and `γ` self-dual. On a closed oriented Riemannian four-manifold its kernel
consists exactly of closed functions and closed self-dual two-forms. Equivalently, these
are precisely the smooth pairs annihilating the range of `T` under the sum of the two
integral inner products.

Applying `d*` to the adjoint equation first makes `f` harmonic. Green's identity then gives
`df = 0`; the remaining equation is `d*γ = 0`, equivalent to `dγ = 0` by self-duality.
This identifies the smooth annihilator, not the cokernel of a Sobolev realization: closed
range and regularity of weak annihilators are separate analytic requirements.

## References

* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press (1996).
* S. K. Donaldson and P. B. Kronheimer, *The Geometry of Four-Manifolds*, Oxford (1990).
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti.SeibergWitten

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  (o : Manifold.Orientation I M (Fin (2 + 2)))

/-- The formal adjoint of the abelian deformation operator, with scalar component first:
`T*(f, γ) = -2 df + d*γ`. -/
def abelianDeformationFormalAdjoint :
    (SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) →ₗ[ℝ]
      SmoothForm I M ℝ 1 :=
  (-2 : ℝ) • (mextDerivₗ I 0).comp (LinearMap.fst ℝ _ _) +
    (SmoothForm.codifferential o (show 1 + 1 + 2 = 2 + 2 from rfl)).comp
      ((SmoothForm.selfDualForms o).subtype.comp (LinearMap.snd ℝ _ _))

/-- The formal adjoint acts by `-2 df + d*γ`. -/
@[simp]
theorem abelianDeformationFormalAdjoint_apply
    (p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :
    abelianDeformationFormalAdjoint o p = (-2 : ℝ) • mextDerivₗ I 0 p.1 +
      SmoothForm.codifferential o (show 1 + 1 + 2 = 2 + 2 from rfl) p.2 :=
  (rfl)

variable [CompactSpace M] [BoundarylessManifold I M] [T2Space M]

/-- On a closed four-manifold the formal adjoint vanishes exactly on closed functions and
closed self-dual two-forms, the harmonic `H⁰ ⊕ H⁺` representatives. -/
theorem abelianDeformationFormalAdjoint_eq_zero_iff
    (p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :
    abelianDeformationFormalAdjoint o p = 0 ↔
      mextDerivₗ I 0 p.1 = 0 ∧ mextDerivₗ I 2 (p.2 : SmoothForm I M ℝ 2) = 0 := by
  have hstar := SmoothForm.mem_selfDualForms.mp p.2.property
  have hclosed : SmoothForm.codifferential o (show 1 + 1 + 2 = 2 + 2 from rfl) p.2 = 0 ↔
      mextDerivₗ I 2 (p.2 : SmoothForm I M ℝ 2) = 0 := by
    constructor
    · intro h
      have hs := SmoothForm.hodgeStar_codifferential o
        (show 1 + 1 + 2 = 2 + 2 from rfl) (show 1 + (2 + 1) = 2 + 2 from rfl)
        (p.2 : SmoothForm I M ℝ 2)
      simpa [h, hstar] using hs.symm
    · intro h
      simp [SmoothForm.codifferential_apply o rfl rfl, hstar, h]
  rw [abelianDeformationFormalAdjoint_apply]
  constructor
  · intro h
    have hδ := congrArg (SmoothForm.codifferential o
      (show 0 + 1 + 3 = 2 + 2 from rfl)) h
    have hΔ : SmoothForm.hodgeLaplacian o (show 0 + 4 = 2 + 2 from rfl) p.1 = 0 := by
      rw [SmoothForm.hodgeLaplacian_zero_add_one o rfl rfl]
      simpa using hδ
    have hf := (SmoothForm.hodgeLaplacian_eq_zero_iff_mextDeriv_eq_zero o rfl
      (by simp [compactlySupportedForms_eq_top])).mp hΔ
    refine ⟨hf, hclosed.mp ?_⟩
    simpa [hf] using h
  · rintro ⟨hf, hγ⟩
    simp [hf, hclosed.mpr hγ]

/-- Green's formula for the abelian deformation operator and its formal adjoint. The target
pairing is the sum of the scalar and self-dual pairings, in that order. -/
theorem integralTopForm_inner_abelianDeformationOperator_eq
    (a : SmoothForm I M ℝ 1)
    (p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 0
      ((abelianDeformationOperator o a).1.1 x) (p.1.1 x) • riemannianVolumeForm o x) +
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 2
      (((abelianDeformationOperator o a).2 : SmoothForm I M ℝ 2).1 x)
      ((p.2 : SmoothForm I M ℝ 2).1 x) • riemannianVolumeForm o x) =
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 1
      ((abelianDeformationFormalAdjoint o p).1 x) (a.1 x) • riemannianVolumeForm o x) := by
  have hf := SmoothForm.integralTopForm_inner_mextDeriv_eq_inner_codifferential o
    (show 0 + 1 + 3 = 2 + 2 from rfl) p.1 a
    (.inl (by simp [compactlySupportedForms_eq_top]))
  have hγ := SmoothForm.integralTopForm_inner_mextDeriv_eq_inner_codifferential o
    (show 1 + 1 + 2 = 2 + 2 from rfl) a (p.2 : SmoothForm I M ℝ 2)
    (.inl (by simp [compactlySupportedForms_eq_top]))
  rw [abelianDeformationFormalAdjoint_apply,
    SmoothForm.integralTopForm_inner_add_left o (show 1 + 3 = 2 + 2 from rfl) _ _ _
      (.inr (by simp [compactlySupportedForms_eq_top]))]
  congr 1
  · simp only [abelianDeformationOperator_apply_fst, Submodule.coe_smul, Pi.smul_apply,
      map_smul, LinearMap.smul_apply, smul_eq_mul, mul_smul]
    rw [← Pi.smul_def, integralTopForm_smul, ← Pi.smul_def, integralTopForm_smul]
    congr 1
    rw [RoughForm.integralTopForm_inner_smul_riemannianVolumeForm_comm]
    exact hf.symm
  · simp only [coe_abelianDeformationOperator_apply_snd, SmoothForm.coe_selfDualPart,
      RoughForm.alternatingFormInner_selfDualPart_of_mem_selfDualForms o even_two _
        (SmoothForm.coe_mem_selfDualForms_iff.mpr p.2.property)]
    rw [RoughForm.integralTopForm_inner_smul_riemannianVolumeForm_comm
      (α := (SmoothForm.codifferential o rfl (p.2 : SmoothForm I M ℝ 2)).1)]
    exact hγ

/-- The smooth annihilator of the range of `T` is exactly the closed scalar and self-dual
pairs. This does not assert closed range or regularity of distributional annihilators. -/
theorem forall_integralTopForm_inner_abelianDeformationOperator_eq_zero_iff
    (p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :
    (∀ a : SmoothForm I M ℝ 1,
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 0
        ((abelianDeformationOperator o a).1.1 x) (p.1.1 x) • riemannianVolumeForm o x) +
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 2
        (((abelianDeformationOperator o a).2 : SmoothForm I M ℝ 2).1 x)
        ((p.2 : SmoothForm I M ℝ 2).1 x) • riemannianVolumeForm o x) = 0) ↔
      mextDerivₗ I 0 p.1 = 0 ∧ mextDerivₗ I 2 (p.2 : SmoothForm I M ℝ 2) = 0 := by
  simp_rw [integralTopForm_inner_abelianDeformationOperator_eq]
  rw [← abelianDeformationFormalAdjoint_eq_zero_iff]
  constructor
  · intro h
    exact (SmoothForm.integralTopForm_inner_self_smul_riemannianVolumeForm_eq_zero_iff o
      (show 1 + 3 = 2 + 2 from rfl) (by simp [compactlySupportedForms_eq_top])).mp
        (h (abelianDeformationFormalAdjoint o p))
  · intro h a
    simp only [h, ZeroMemClass.coe_zero, Pi.zero_apply, LinearMap.map_zero₂, zero_smul]
    exact integralTopForm_zero o

end TauCeti.SeibergWitten
