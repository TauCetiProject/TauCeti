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

## Main results

* `HomologicalComplex.ι_tensorHom_apply`: the tensor product of two morphisms of complexes of
  modules on a pure tensor in a homogeneous summand.
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
