/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Topology.Algebra.Module.ComplexSmulI
public import TauCeti.Topology.VectorBundle.Hom
public import TauCeti.Topology.VectorBundle.RestrictScalars
public import TauCeti.Topology.VectorBundle.Smul

/-!
# Complex structures and multiplication by `i` on topological vector bundles

Any real vector bundle `[VectorBundle ℝ G W]` over an arbitrary topological base `B` whose atlas
trivializations commute with `Complex.I • ·` carries a compatible `VectorBundle ℂ G W` structure
(`Bundle.Trivialization.isLinear_complex_of_map_I_smul`, `VectorBundle.ofMapISmul`). Fibrewise
multiplication by `Complex.I` acts on any complex vector bundle as a total-space homeomorphism
(`TauCeti.smulIHomeomorph`) and, when accompanied by a compatible `VectorBundle ℝ G W` structure, as
a continuous section of the real endomorphism bundle (`TauCeti.continuous_smulIEquiv_bundle`).
-/

public section

noncomputable section

open Bundle FiberBundle

namespace Bundle.Trivialization

/-- A real-linear trivialization of a bundle of complex vector spaces that commutes with
`Complex.I • ·` on every fibre over its base set is `ℂ`-linear. -/
theorem isLinear_complex_of_map_I_smul {B F : Type*} {E : B → Type*} [TopologicalSpace B]
    [TopologicalSpace F] [TopologicalSpace (TotalSpace F E)]
    [AddCommGroup F] [Module ℝ F] [Module ℂ F] [IsScalarTower ℝ ℂ F]
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)] [∀ x, Module ℂ (E x)]
    [∀ x, IsScalarTower ℝ ℂ (E x)] (e : Trivialization F (π F E)) [e.IsLinear ℝ]
    (hI : ∀ b ∈ e.baseSet, ∀ v : E b, (e ⟨b, Complex.I • v⟩).2 = Complex.I • (e ⟨b, v⟩).2) :
    e.IsLinear ℂ where
  linear b hb :=
    { map_add := (e.linear ℝ hb).map_add
      map_smul c v := by
        rw [← Complex.re_smul_add_im_smul c v, (e.linear ℝ hb).map_add, (e.linear ℝ hb).map_smul,
          (e.linear ℝ hb).map_smul, hI b hb, Complex.re_smul_add_im_smul] }

end Bundle.Trivialization

/-- A real vector bundle `[VectorBundle ℝ G W]` whose atlas trivializations commute with
multiplication by `Complex.I` carries a compatible `VectorBundle ℂ G W` structure, with no complex
structure assumed on the base `B`. -/
theorem VectorBundle.ofMapISmul {B : Type*} [TopologicalSpace B] (G : Type*) [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G] (W : B → Type*)
    [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, Module ℂ (W x)]
    [∀ x, IsScalarTower ℝ ℂ (W x)] [TopologicalSpace (TotalSpace G W)]
    [∀ x, TopologicalSpace (W x)] [FiberBundle G W] [VectorBundle ℝ G W]
    (hI : ∀ e : Trivialization G (π G W), MemTrivializationAtlas e →
      ∀ b ∈ e.baseSet, ∀ v : W b, (e ⟨b, Complex.I • v⟩).2 = Complex.I • (e ⟨b, v⟩).2) :
    VectorBundle ℂ G W :=
  VectorBundle.ofLinear ℝ ℂ G W fun e he ↦ Trivialization.isLinear_complex_of_map_I_smul e (hI e he)

namespace TauCeti

variable {B : Type*} [TopologicalSpace B]

section Homeomorph

variable (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] (W : B → Type*)
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℂ (W x)] [∀ x, TopologicalSpace (W x)]
  [TopologicalSpace (TotalSpace G W)] [FiberBundle G W] [VectorBundle ℂ G W]

/-- Multiplication by `Complex.I` on the fibres of a complex vector bundle as a homeomorphism of
its total space, with no finite-rank assumption. -/
def smulIHomeomorph : TotalSpace G W ≃ₜ TotalSpace G W where
  toFun p := ⟨p.proj, Complex.I • p.2⟩
  invFun p := ⟨p.proj, -Complex.I • p.2⟩
  left_inv := fun ⟨x, v⟩ ↦ congrArg (TotalSpace.mk x) (Complex.neg_I_smul_I_smul v)
  right_inv := fun ⟨x, v⟩ ↦ congrArg (TotalSpace.mk x) (Complex.I_smul_neg_I_smul v)
  continuous_toFun := (continuous_const (y := Complex.I)).smul_totalSpace continuous_id
  continuous_invFun := (continuous_const (y := -Complex.I)).smul_totalSpace continuous_id

variable {G W}

@[simp] theorem smulIHomeomorph_apply (p : TotalSpace G W) :
    smulIHomeomorph G W p = ⟨p.proj, Complex.I • p.2⟩ := (rfl)
@[simp] theorem smulIHomeomorph_symm_apply (p : TotalSpace G W) :
    (smulIHomeomorph G W).symm p = ⟨p.proj, -Complex.I • p.2⟩ := (rfl)

end Homeomorph

section HomBundle

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G]
  [IsScalarTower ℝ ℂ G] {W : B → Type*} [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)]
  [∀ x, Module ℂ (W x)] [∀ x, IsScalarTower ℝ ℂ (W x)] [∀ x, TopologicalSpace (W x)]
  [∀ x, ContinuousConstSMul ℂ (W x)] [TopologicalSpace (TotalSpace G W)] [FiberBundle G W]
  [VectorBundle ℂ G W] [VectorBundle ℝ G W]

/-- Read in any preferred trivialization, fibrewise multiplication by `Complex.I`
(`Complex.smulIEquiv (W x)`) is the constant model operator `Complex.smulIEquiv G`. -/
@[simp] theorem inCoordinates_smulIEquiv (a : B) {x : B}
    (hx : x ∈ (trivializationAt G W a).baseSet) :
    ContinuousLinearMap.inCoordinates G W G W a x a x
      (Complex.smulIEquiv (W x) : W x →L[ℝ] W x) = (Complex.smulIEquiv G : G →L[ℝ] G) := by
  have hW : (Complex.smulIEquiv (W x) : W x →L[ℝ] W x) = Complex.I • .id ℝ (W x) := by ext; simp
  have hG : (Complex.smulIEquiv G : G →L[ℝ] G) = Complex.I • .id ℝ G := by ext; simp
  rw [hW, hG, ContinuousLinearMap.inCoordinates_smul _ _,
    ContinuousLinearMap.inCoordinates_id hx]

/-- Read in any preferred trivialization, `(Complex.smulIEquiv (W x)).symm` is
`(Complex.smulIEquiv G).symm`. -/
@[simp] theorem inCoordinates_smulIEquiv_symm (a : B) {x : B}
    (hx : x ∈ (trivializationAt G W a).baseSet) :
    ContinuousLinearMap.inCoordinates G W G W a x a x
      ((Complex.smulIEquiv (W x)).symm : W x →L[ℝ] W x) =
      ((Complex.smulIEquiv G).symm : G →L[ℝ] G) := by
  have hW : ((Complex.smulIEquiv (W x)).symm : W x →L[ℝ] W x) = (-Complex.I) • .id ℝ (W x) := by
    ext; simp
  have hG : ((Complex.smulIEquiv G).symm : G →L[ℝ] G) = (-Complex.I) • .id ℝ G := by ext; simp
  rw [hW, hG, ContinuousLinearMap.inCoordinates_smul _ _,
    ContinuousLinearMap.inCoordinates_id hx]

variable [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul ℝ (W x)]

/-- Fibrewise multiplication by `Complex.I` is a continuous section of `fun x ↦ W x →L[ℝ] W x`. -/
theorem continuous_smulIEquiv_bundle :
    Continuous (fun x ↦ TotalSpace.mk' (G →L[ℝ] G)
      (E := fun y ↦ W y →L[ℝ] W y) x (Complex.smulIEquiv (W x) : W x →L[ℝ] W x)) :=
  continuous_hom_bundle_of_inCoordinates_eq_const fun a _ hx _ ↦ inCoordinates_smulIEquiv a hx

/-- Fibrewise multiplication by `-Complex.I` is a continuous section of `fun x ↦ W x →L[ℝ] W x`. -/
theorem continuous_smulIEquiv_symm_bundle :
    Continuous (fun x ↦ TotalSpace.mk' (G →L[ℝ] G)
      (E := fun y ↦ W y →L[ℝ] W y) x ((Complex.smulIEquiv (W x)).symm : W x →L[ℝ] W x)) :=
  continuous_hom_bundle_of_inCoordinates_eq_const fun a _ hx _ ↦ inCoordinates_smulIEquiv_symm a hx

end HomBundle

end TauCeti

end
