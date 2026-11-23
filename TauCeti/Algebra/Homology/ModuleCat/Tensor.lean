/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import TauCeti.Algebra.Homology.Monoidal.Summand

/-!
# The tensor product of morphisms of complexes of modules on pure tensors

For homological complexes of modules over a commutative ring, the tensor product of two morphisms
sends a pure tensor `a ⊗ₜ b` in the homogeneous summand `K₁.X i₁ ⊗ K₂.X i₂` to the pure tensor of
the images.  This is the elementwise form of `HomologicalComplex.ι_tensorHom` in
`TauCeti/Algebra/Homology/Monoidal/Summand.lean`, which holds in any preadditive monoidal category.
On the degree-`0` summand `R ⊗ R` of the tensor square of the unit complex `R[0]`, the left
unitor of cochain complexes is the multiplication of `R`.

## Main results

* `HomologicalComplex.ι_tensorHom_apply`: the tensor product of two morphisms of complexes of
  modules on a pure tensor in a homogeneous summand.
* `CochainComplex.leftUnitor_hom_f_zero_ιTensorObj_tmul`: on the degree-`0` summand of
  `R[0] ⊗ R[0]`, the unitor `R[0] ⊗ R[0] ≅ R[0]` is the multiplication of `R`.
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

end HomologicalComplex

namespace CochainComplex

open scoped TensorProduct

variable {R : Type v} [CommRing R]

/-- On the degree-`0` summand `R ⊗ R` of `R[0] ⊗ R[0]`, the left unitor of cochain complexes is
the multiplication of `R`, after identifying the degree-`0` term of `R[0]` with `R`. -/
lemma leftUnitor_hom_f_zero_ιTensorObj_tmul
    (u w : (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)).X 0) :
    ((λ_ (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ))).hom.f 0).hom
        ((HomologicalComplex.ιTensorObj (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)) (𝟙_ _) 0 0 0
          (zero_add 0)).hom (u ⊗ₜ w)) =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{v} R))).hom.hom u • w := by
  set e := HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{v} R))
  have hu : u = e.hom.hom u • e.inv.hom 1 := by
    rw [← map_smul, smul_eq_mul, mul_one]
    exact (congrArg (fun φ => φ.hom u) e.hom_inv_id).symm
  have hw : (HomologicalComplex.ιTensorObj (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)) (𝟙_ _) 0 0 0
      (zero_add 0)).hom (e.inv.hom 1 ⊗ₜ w) =
        ((λ_ (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ))).inv.f 0).hom w := by
    rw [HomologicalComplex.leftUnitor_inv_f]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
      ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
      ModuleCat.MonoidalCategory.whiskerRight_apply]
    -- `ConcreteCategory.hom` and `ModuleCat.Hom.hom` agree on `ModuleCat`.
    rfl
  conv_lhs => rw [hu, ← TensorProduct.smul_tmul', map_smul, map_smul, hw]
  exact congrArg _ <| Iso.inv_hom_id_apply
    (HomologicalComplex.Hom.isoApp (λ_ (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ))) 0) w

end CochainComplex
