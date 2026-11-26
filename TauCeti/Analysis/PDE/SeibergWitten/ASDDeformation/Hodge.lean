/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.ASDDeformation.Basic
public import TauCeti.Geometry.Manifold.Riemannian.SelfDual.Hodge

/-!
# Hodge factorization of the normalized abelian deformation operator

For `δ₀ a = (-d*a, √2 (da)⁺)` on an oriented Riemannian four-manifold, its formal adjoint is
`δ₀*(f, γ) = -df + √2 d*γ`. The compositions are exactly the Hodge Laplacians:

* `δ₀* δ₀ = Δ₁` on one-forms;
* `δ₀ δ₀* = Δ₀ ⊕ Δ₊` on scalar and self-dual forms, in that order.

These are identities on smooth forms and require neither compactness nor an almost complex
structure. On a closed manifold, the adjoint kernel is the ordered product of closed scalar
and closed self-dual forms, the harmonic representatives of `H⁰ ⊕ H⁺`. Together with the
one-form kernel characterization in `ASDDeformation.Basic`, these identities connect the
deformation operator with the Hodge model used for its determinant orientation. They do not
assert closed range or identify a Sobolev cokernel.

## References

* S. K. Donaldson and P. B. Kronheimer, *The Geometry of Four-Manifolds*, Oxford University
  Press (1990), §4.2: the abelian anti-self-dual deformation complex.
* C. H. Taubes, *GR = SW: Counting curves and connections*, J. Differential Geom. 52 (1999),
  453–609: the normalized real deformation operator and its canonical orientation.
-/

public section

noncomputable section

open Bundle Real
open scoped Manifold ContDiff

namespace TauCeti.SeibergWitten

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  (o : Manifold.Orientation I M (Fin (2 + 2)))

/-- The formal adjoint `δ₀*(f, γ) = -df + √2 d*γ` of the normalized abelian deformation
operator, with the scalar factor first in its domain. -/
def asdDeformationFormalAdjoint :
    (SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) →ₗ[ℝ]
      SmoothForm I M ℝ 1 :=
  -(mextDerivₗ I 0).comp (LinearMap.fst ℝ _ _) +
    √2 • (SmoothForm.codifferential o (show 1 + 1 + 2 = 2 + 2 from rfl)).comp
      ((SmoothForm.selfDualForms o).subtype.comp (LinearMap.snd ℝ _ _))

/-- The formal adjoint acts by `-df + √2 d*γ`. -/
@[simp]
theorem asdDeformationFormalAdjoint_apply
    (p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :
    asdDeformationFormalAdjoint o p = -mextDerivₗ I 0 p.1 +
      √2 • SmoothForm.codifferential o (show 1 + 1 + 2 = 2 + 2 from rfl) p.2 :=
  (rfl)

/-- The adjoint of the normalized operator is the adjoint of `T = (-2d*, d⁺)`
precomposed with the inverse target rescaling. -/
theorem asdDeformationFormalAdjoint_eq_comp :
    asdDeformationFormalAdjoint o = abelianDeformationFormalAdjoint o ∘ₗ
      (deformationTargetRescale o).symm.toLinearMap := by
  apply LinearMap.ext
  intro p
  simp only [asdDeformationFormalAdjoint_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    abelianDeformationFormalAdjoint_apply, deformationTargetRescale_symm_apply_fst,
    coe_deformationTargetRescale_symm_apply_snd, map_smul]
  module

/-- The square `δ₀* δ₀` is exactly the Hodge Laplacian on one-forms. -/
theorem asdDeformationFormalAdjoint_comp_asdDeformationOperator :
    asdDeformationFormalAdjoint o ∘ₗ asdDeformationOperator o =
      SmoothForm.hodgeLaplacian o (show 1 + 3 = 2 + 2 from rfl) := by
  ext a : 1
  have hclosed : mextDerivₗ I 2 (mextDerivₗ I 1 a) = 0 := by
    exact LinearMap.congr_fun (mextDerivₗ_comp_mextDerivₗ I 1) a
  simp only [LinearMap.comp_apply, asdDeformationFormalAdjoint_apply,
    asdDeformationOperator_apply_fst, coe_asdDeformationOperator_apply_snd, map_neg,
    neg_neg, map_smul,
    SmoothForm.codifferential_selfDualPart_of_mextDeriv_eq_zero o hclosed,
    smul_smul, SmoothForm.hodgeLaplacian_add_one_add_one (k := 0) (l := 2) o rfl rfl]
  rw [← mul_assoc, Real.mul_self_sqrt zero_le_two, mul_inv_cancel₀ two_ne_zero,
    one_smul, add_comm]

/-- The square `δ₀ δ₀*` is the product Hodge Laplacian on scalar and self-dual forms.
The order of these two factors agrees with the target of `δ₀`. -/
theorem asdDeformationOperator_comp_asdDeformationFormalAdjoint :
    asdDeformationOperator o ∘ₗ asdDeformationFormalAdjoint o =
      (SmoothForm.hodgeLaplacian o (show 0 + 4 = 2 + 2 from rfl)).prodMap
        (SmoothForm.selfDualHodgeLaplacian o) := by
  apply LinearMap.ext
  intro p
  apply Prod.ext
  · simp [asdDeformationFormalAdjoint_apply,
      SmoothForm.hodgeLaplacian_zero_add_one (l := 3) o rfl rfl]
  · apply Subtype.ext
    have hdd : mextDerivₗ I 1 (mextDerivₗ I 0 p.1) = 0 :=
      LinearMap.congr_fun (mextDerivₗ_comp_mextDerivₗ I 0) p.1
    simp only [LinearMap.comp_apply, coe_asdDeformationOperator_apply_snd,
      LinearMap.prodMap_apply, SmoothForm.coe_selfDualHodgeLaplacian_apply]
    rw [asdDeformationFormalAdjoint_apply]
    simp only [map_add, map_neg, map_smul, hdd, neg_zero, zero_add,
      SmoothForm.selfDualPart_mextDeriv_codifferential o p.2.property, smul_smul]
    rw [← mul_assoc, Real.mul_self_sqrt zero_le_two, mul_inv_cancel₀ two_ne_zero, one_smul]

section ClosedManifold

variable [CompactSpace M] [BoundarylessManifold I M] [T2Space M]

/-- Green's formula for `δ₀` and `δ₀*`, with the target pairing ordered as the scalar
pairing followed by the self-dual pairing. -/
theorem integralTopForm_inner_asdDeformationOperator_eq_inner_asdDeformationFormalAdjoint
    (a : SmoothForm I M ℝ 1)
    (p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 0
      ((asdDeformationOperator o a).1.val x) (p.1.val x) • riemannianVolumeForm o x) +
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 2
      (((asdDeformationOperator o a).2 : SmoothForm I M ℝ 2).val x)
      ((p.2 : SmoothForm I M ℝ 2).val x) • riemannianVolumeForm o x) =
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 1
      (a.val x) ((asdDeformationFormalAdjoint o p).val x) • riemannianVolumeForm o x) := by
  have h :=
    integralTopForm_inner_abelianDeformationOperator_eq_inner_abelianDeformationFormalAdjoint
      o a ((deformationTargetRescale o).symm p)
  rw [asdDeformationFormalAdjoint_eq_comp, LinearMap.comp_apply, LinearEquiv.coe_coe]
  convert h using 1
  congr 1
  · congr 1
    funext x
    simp only [asdDeformationOperator_apply_fst, abelianDeformationOperator_apply_fst,
      deformationTargetRescale_symm_apply_fst, Submodule.coe_neg, Submodule.coe_smul,
      Pi.neg_apply, Pi.smul_apply, map_neg, map_smul, LinearMap.neg_apply,
      LinearMap.smul_apply, smul_eq_mul]
    congr 1
    ring
  · congr 1
    funext x
    simp only [coe_asdDeformationOperator_apply_snd, coe_abelianDeformationOperator_apply_snd,
      coe_deformationTargetRescale_symm_apply_snd, Submodule.coe_smul, Pi.smul_apply,
      map_smul, LinearMap.smul_apply, smul_eq_mul]

/-- On a closed four-manifold, `δ₀*` vanishes exactly on the closed scalar and self-dual
pairs, the harmonic `H⁰ ⊕ H⁺` representatives. -/
theorem asdDeformationFormalAdjoint_eq_zero_iff
    (p : SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o) :
    asdDeformationFormalAdjoint o p = 0 ↔
      mextDerivₗ I 0 p.1 = 0 ∧ mextDerivₗ I 2 (p.2 : SmoothForm I M ℝ 2) = 0 := by
  rw [asdDeformationFormalAdjoint_eq_comp, LinearMap.comp_apply,
    LinearEquiv.coe_coe, abelianDeformationFormalAdjoint_eq_zero_iff]
  simp [Real.sqrt_ne_zero'.mpr zero_lt_two]

/-- The formal-adjoint kernel is the ordered product of closed scalar and self-dual forms. -/
theorem ker_asdDeformationFormalAdjoint :
    LinearMap.ker (asdDeformationFormalAdjoint o) =
      (LinearMap.ker (mextDerivₗ I (F := ℝ) 0)).prod
        (LinearMap.ker (mextDerivₗ I 2 ∘ₗ (SmoothForm.selfDualForms o).subtype)) := by
  ext p
  simp only [LinearMap.mem_ker, Submodule.mem_prod, LinearMap.comp_apply,
    Submodule.subtype_apply, asdDeformationFormalAdjoint_eq_zero_iff]

end ClosedManifold

end TauCeti.SeibergWitten
