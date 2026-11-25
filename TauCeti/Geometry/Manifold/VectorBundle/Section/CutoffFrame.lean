/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.ComplexModule
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension

/-!
# Cut-off frames of a vector bundle

A trivialization `t` of a smooth vector bundle `V → M` gives a frame of `V` only over its base set.
Multiplying by a smooth function `ψ` supported in the base set turns it into global data:

* the **cut-off frame section** `x ↦ ψ(x) t⁻¹ₓ v` of `V`, for a vector `v` of the model fibre
  (`Bundle.Trivialization.cutoffFrameSection`), is a smooth section of `V` on all of `M`;
* for a complex bundle over a real manifold, the **cut-off frame coefficient**
  `x ↦ χ(x) ℓ(tₓ (h x))` of a smooth section `h`, for a complex-linear functional `ℓ` on the model
  fibre (`Bundle.Trivialization.cutoffFrameCoeff`), is a smooth complex-valued function on `M`,
  complex-linear in `h`.

These read operators between sections of bundles as matrices of operators on functions, without
restricting to the base set of a trivialization: the entries of an operator `P` are the operators
`f ↦ χ ℓ(t' (P (f ψ t⁻¹ v)))` on functions on `M`.
-/

public section

noncomputable section

open Bundle Set
open scoped ContDiff Manifold

namespace Bundle.Trivialization

section Section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {EM : Type*} [NormedAddCommGroup EM]
  [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM] {I : ModelWithCorners 𝕜 EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] {n : ℕ∞ω}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [ContMDiffVectorBundle n F V I]
  (t : Trivialization F (π F V)) [MemTrivializationAtlas t]

/-- The **cut-off frame section** `x ↦ ψ(x) t⁻¹ₓ v` of `V`, for a trivialization `t` of `V` in its
atlas, a `C^n` function `ψ` whose support lies in the base set of `t` and a vector `v` of the model
fibre. It is a `C^n` section of `V` on all of `M`, vanishing outside the support of `ψ`. -/
def cutoffFrameSection (ψ : C^n⟮I, M; 𝕜⟯) (hψ : tsupport ψ ⊆ t.baseSet) (v : F) :
    Cₛ^n⟮I; F, V⟯ where
  toFun x := ψ x • t.symm x v
  contMDiff_toFun := by
    refine ContMDiffOn.smul_section_of_tsupport ψ.contMDiff.contMDiffOn t.open_baseSet hψ ?_
    refine (contMDiffOn_section_iff t t.open_baseSet subset_rfl).2 ?_
    exact contMDiffOn_const.congr fun x hx ↦ by rw [t.apply_mk_symm hx]

@[simp]
theorem cutoffFrameSection_apply (ψ : C^n⟮I, M; 𝕜⟯) (hψ : tsupport ψ ⊆ t.baseSet) (v : F)
    (x : M) : t.cutoffFrameSection ψ hψ v x = ψ x • t.symm x v :=
  (rfl)

end Section

section Coeff

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*} [TopologicalSpace HM]
  {I : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] {n : ℕ∞ω}
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {F : M → Type*} [TopologicalSpace (TotalSpace W F)] [∀ x, AddCommGroup (F x)]
  [∀ x, Module ℝ (F x)] [∀ x, Module ℂ (F x)] [∀ x, TopologicalSpace (F x)] [FiberBundle W F]
  [VectorBundle ℝ W F] [VectorBundle ℂ W F] [ContMDiffVectorBundle n W F I]
  (t : Trivialization W (π W F)) [MemTrivializationAtlas t]

/-- The cut-off frame coefficients `χ(x) ℓ(tₓ (h x))` of a `C^n` section `h` are `C^n`. -/
private theorem contMDiff_cutoffFrameCoeffFun (χ : C^n⟮I, M; ℝ⟯) (hχ : tsupport χ ⊆ t.baseSet)
    (ℓ : W →L[ℂ] ℂ) (h : Cₛ^n⟮I; W, F⟯) :
    ContMDiff I 𝓘(ℝ, ℂ) n fun x ↦ χ x • ℓ (t.continuousLinearMapAt ℂ x (h x)) := by
  refine ContMDiffOn.contMDiff_smul_of_tsupport_subset ?_ t.open_baseSet
    χ.contMDiff.contMDiffOn hχ
  have hs := (contMDiffOn_section_iff t t.open_baseSet subset_rfl).1 h.contMDiff.contMDiffOn
  refine ((ℓ.restrictScalars ℝ).contMDiff.comp_contMDiffOn hs).congr fun x hx ↦ ?_
  simp [continuousLinearMapAt_apply_of_mem ℂ t hx]

/-- The cut-off frame coefficients `χ(x) ℓ(tₓ (h x))` of a `C^n` section `h`, as a `C^n`
function. -/
private def cutoffFrameCoeffFun (χ : C^n⟮I, M; ℝ⟯) (hχ : tsupport χ ⊆ t.baseSet) (ℓ : W →L[ℂ] ℂ)
    (h : Cₛ^n⟮I; W, F⟯) : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ :=
  ⟨_, contMDiff_cutoffFrameCoeffFun t χ hχ ℓ h⟩

private theorem cutoffFrameCoeffFun_apply (χ : C^n⟮I, M; ℝ⟯) (hχ : tsupport χ ⊆ t.baseSet)
    (ℓ : W →L[ℂ] ℂ) (h : Cₛ^n⟮I; W, F⟯) (x : M) :
    cutoffFrameCoeffFun t χ hχ ℓ h x = χ x • ℓ (t.continuousLinearMapAt ℂ x (h x)) :=
  (rfl)

/-- The **cut-off frame coefficient** `x ↦ χ(x) ℓ(tₓ (h x))` of a section `h` of a complex vector
bundle `F` over a real manifold, for a trivialization `t` of `F` in its atlas, a real `C^n`
function `χ` whose support lies in the base set of `t` and a complex-linear functional `ℓ` on the
model fibre, as a complex-linear map from the `C^n` sections of `F` to the complex-valued `C^n`
functions. -/
def cutoffFrameCoeff (χ : C^n⟮I, M; ℝ⟯) (hχ : tsupport χ ⊆ t.baseSet) (ℓ : W →L[ℂ] ℂ) :
    Cₛ^n⟮I; W, F⟯ →ₗ[ℂ] C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ where
  toFun := cutoffFrameCoeffFun t χ hχ ℓ
  map_add' g h := by
    ext x
    simp [cutoffFrameCoeffFun_apply, smul_add]
  map_smul' c h := by
    ext x
    simp only [cutoffFrameCoeffFun_apply, ContMDiffMap.complex_smul_apply,
      ContMDiffSection.coe_smul_of_normedAlgebra, Pi.smul_apply, map_smul, Complex.real_smul,
      smul_eq_mul, RingHom.id_apply]
    ring

@[simp]
theorem cutoffFrameCoeff_apply (χ : C^n⟮I, M; ℝ⟯) (hχ : tsupport χ ⊆ t.baseSet) (ℓ : W →L[ℂ] ℂ)
    (h : Cₛ^n⟮I; W, F⟯) (x : M) :
    t.cutoffFrameCoeff χ hχ ℓ h x = χ x • ℓ (t.continuousLinearMapAt ℂ x (h x)) :=
  (rfl)

end Coeff

end Bundle.Trivialization
