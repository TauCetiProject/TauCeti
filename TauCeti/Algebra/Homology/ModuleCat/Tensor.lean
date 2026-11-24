/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import TauCeti.Algebra.Homology.Monoidal.Summand

/-!
# The tensor product of morphisms of complexes of modules on pure tensors

For homological complexes of modules over a commutative ring, the tensor product of two morphisms
sends a pure tensor `a ⊗ₜ b` in the homogeneous summand `K₁.X i₁ ⊗ K₂.X i₂` to the pure tensor of
the images.  This is the elementwise form of `HomologicalComplex.ι_tensorHom` in
`TauCeti/Algebra/Homology/Monoidal/Summand.lean`, which holds in any preadditive monoidal category.
On the summand `R ⊗ K.X j` of `𝟙_ _ ⊗ K`, the left unitor of homological complexes of modules is
the scalar multiplication.

## Main results

* `HomologicalComplex.ι_tensorHom_apply`: the tensor product of two morphisms of complexes of
  modules on a pure tensor in a homogeneous summand.
* `HomologicalComplex.leftUnitor_hom_f_ιTensorObj_tmul`: on the summand `R ⊗ K.X j` of
  `𝟙_ _ ⊗ K`, the left unitor `𝟙_ _ ⊗ K ≅ K` is the scalar multiplication.
-/

public section

open CategoryTheory MonoidalCategory

universe v

namespace HomologicalComplex

variable {R : Type v} [CommRing R]
variable {I : Type*} [AddMonoid I] {c : ComplexShape I} [c.TensorSigns] [DecidableEq I]

/-- The tensor product of two morphisms of homological complexes of modules on a pure tensor in a
homogeneous summand: the tensor product of the components. -/
lemma ι_tensorHom_apply {K₁ K₂ L₁ L₂ : HomologicalComplex (ModuleCat.{v} R) c} (f₁ : K₁ ⟶ L₁)
    (f₂ : K₂ ⟶ L₂) [HasTensor K₁ K₂] [HasTensor L₁ L₂] (i₁ i₂ j : I) (h : i₁ + i₂ = j)
    (a : K₁.X i₁) (b : K₂.X i₂) :
    (tensorHom f₁ f₂).f j ((ιTensorObj K₁ K₂ i₁ i₂ j h).hom (a ⊗ₜ[R] b)) =
      (ιTensorObj L₁ L₂ i₁ i₂ j h).hom (f₁.f i₁ a ⊗ₜ[R] f₂.f i₂ b) :=
  LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (ι_tensorHom f₁ f₂ i₁ i₂ j h)) (a ⊗ₜ[R] b)

section Unitor

variable [∀ (X₁ X₂ : GradedObject I (ModuleCat.{v} R)), GradedObject.HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ : GradedObject I (ModuleCat.{v} R)), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I (ModuleCat.{v} R)), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

open scoped TensorProduct

/-- On the summand `R ⊗ K.X j` of `𝟙_ _ ⊗ K` in degree `j`, the left unitor of homological
complexes of modules is the scalar multiplication, after identifying the degree-`0` term of the
unit complex with `R`. -/
lemma leftUnitor_hom_f_ιTensorObj_tmul (K : HomologicalComplex (ModuleCat.{v} R) c) (j : I)
    (u : (𝟙_ (HomologicalComplex (ModuleCat.{v} R) c)).X 0) (x : K.X j) :
    ((λ_ K).hom.f j).hom
        ((ιTensorObj (𝟙_ (HomologicalComplex (ModuleCat.{v} R) c)) K 0 j j (zero_add j)).hom
          (u ⊗ₜ x)) =
      (singleObjXSelf c 0 (𝟙_ (ModuleCat.{v} R))).hom.hom u • x := by
  set e := singleObjXSelf c 0 (𝟙_ (ModuleCat.{v} R))
  have hu : u = e.hom.hom u • e.inv.hom 1 := by
    rw [← map_smul, smul_eq_mul, mul_one]
    exact (congrArg (fun φ => φ.hom u) e.hom_inv_id).symm
  have hx : (ιTensorObj (𝟙_ (HomologicalComplex (ModuleCat.{v} R) c)) K 0 j j
      (zero_add j)).hom (e.inv.hom 1 ⊗ₜ x) = ((λ_ K).inv.f j).hom x := by
    rw [leftUnitor_inv_f]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
      ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
      ModuleCat.MonoidalCategory.whiskerRight_apply]
    -- `ConcreteCategory.hom` and `ModuleCat.Hom.hom` agree on `ModuleCat`.
    rfl
  conv_lhs => rw [hu, ← TensorProduct.smul_tmul', map_smul, map_smul, hx]
  exact congrArg _ <| Iso.inv_hom_id_apply (Hom.isoApp (λ_ K) j) x

end Unitor

end HomologicalComplex
