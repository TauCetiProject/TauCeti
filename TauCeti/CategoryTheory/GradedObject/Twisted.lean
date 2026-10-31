/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.GradedObject.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Linear
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.DegreeThree

/-!
# Graded objects with a cocycle-twisted associator

Let `C` be an `R`-linear monoidal category and `I` an additive monoid. Mathlib makes
`GradedObject I C` a monoidal category, with `(X ⊗ Y) n = ∐_{i + j = n} X i ⊗ Y j`, and the
associator acting on the summand `(X₁ i₁ ⊗ X₂ i₂) ⊗ X₃ i₃` by the associator of `C`.

Given a normalized `3`-cocycle `ω : I → I → I → Rˣ`, that is a function satisfying
`ω (i₁ + i₂) i₃ i₄ * ω i₁ i₂ (i₃ + i₄) = ω i₂ i₃ i₄ * ω i₁ (i₂ + i₃) i₄ * ω i₁ i₂ i₃` and
`ω i₁ 0 i₃ = 1`, the associator may be twisted by multiplying it by `ω i₁ i₂ i₃` on that summand.
The cocycle identity is exactly what the pentagon axiom requires, and the normalization is what the
triangle axiom requires, so the result is again a monoidal category, with the same tensor product
and unitors. For `I = Additive G` and `C = ModuleCat k` this is the category of `G`-graded vector
spaces with associator twisted by `ω`: on the one-dimensional objects `δ_g` concentrated in a
single degree the associator is multiplication by `ω g h j`. Its finite-dimensional, finitely
supported objects form the pointed category `Vec^ω_G`.

## Main definitions

* `TauCeti.GradedObject.TwistingCocycle I R`: a normalized `3`-cocycle on `I` with values in `Rˣ`
  for the trivial action, bundled.
* `CategoryTheory.GradedObject.Monoidal.scaleTensorObj₃`: the endomorphism of
  `X₁ ⊗ (X₂ ⊗ X₃)` acting on the summand `X₁ i₁ ⊗ X₂ i₂ ⊗ X₃ i₃` by a scalar `u i₁ i₂ i₃`.
* `TauCeti.GradedObject.Twisted c C`: a type synonym for `GradedObject I C`, carrying the monoidal
  structure whose associator is twisted by the cocycle `c`.

## Main statements

* `TauCeti.GradedObject.Twisted.instMonoidalCategory`: the twisted associator, together with
  Mathlib's tensor product and unitors of graded objects, forms a monoidal category.
* `TauCeti.GradedObject.Twisted.ιTensorObj₃'_associator_hom`: the twisted associator acts on the
  summand `(X₁ i₁ ⊗ X₂ i₂) ⊗ X₃ i₃` as `ω i₁ i₂ i₃` times the associator of `C`.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §2.3
* `Mathlib/CategoryTheory/GradedObject/Monoidal.lean` (Joël Riou, Kim Morrison), whose
  construction of the associator and proof of the pentagon axiom are followed here, with scalars
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Category

namespace TauCeti.GradedObject

/-- A normalized `3`-cocycle on an additive monoid `I` with values in the units of `R`, for the
trivial action: the datum twisting the associator of `I`-graded objects. The cocycle identity is the
pentagon axiom for the twisted associator, and normalization in the middle variable is the triangle
axiom. The other two normalizations follow (`TwistingCocycle.ω_zero_left` and
`TwistingCocycle.ω_zero_right`).

The `3`-cocycles of a group in the sense of `TauCeti.groupCohomology.IsMulCocycle₃` are indexed
multiplicatively and need an action on the coefficients; this structure is indexed additively, as
Mathlib's monoidal graded objects are, with the trivial action built in, and
`TwistingCocycle.ofIsMulCocycle₃` converts. -/
@[ext]
structure TwistingCocycle (I : Type*) [AddMonoid I] (R : Type*) [Monoid R] where
  /-- The underlying function. -/
  ω : I → I → I → Rˣ
  /-- The `3`-cocycle identity, for the trivial action. -/
  cocycle (i₁ i₂ i₃ i₄ : I) :
    ω (i₁ + i₂) i₃ i₄ * ω i₁ i₂ (i₃ + i₄) = ω i₂ i₃ i₄ * ω i₁ (i₂ + i₃) i₄ * ω i₁ i₂ i₃
  /-- Normalization in the middle variable. -/
  ω_zero (i₁ i₃ : I) : ω i₁ 0 i₃ = 1

namespace TwistingCocycle

attribute [simp] ω_zero

variable {I : Type*} [AddMonoid I] {R : Type*} [Monoid R] (c : TwistingCocycle I R)

/-- A twisting cocycle is normalized in the first variable. -/
@[simp]
lemma ω_zero_left (i₂ i₃ : I) : c.ω 0 i₂ i₃ = 1 := by
  simpa using c.cocycle 0 0 i₂ i₃

/-- A twisting cocycle is normalized in the last variable. -/
@[simp]
lemma ω_zero_right (i₁ i₂ : I) : c.ω i₁ i₂ 0 = 1 := by
  simpa using c.cocycle i₁ i₂ 0 0

end TwistingCocycle

/-- A multiplicative `3`-cocycle `f` of a monoid `G` acting trivially on `Rˣ`, in the sense of
`TauCeti.groupCohomology.IsMulCocycle₃`, which is normalized in the middle variable, as a twisting
cocycle on `Additive G`. By `TauCeti.groupCohomology.exists_normalized_of_isMulCocycle₃`, every
`3`-cocycle of a group is cohomologous to one satisfying the normalization. -/
@[simps]
def TwistingCocycle.ofIsMulCocycle₃ {R G : Type*} [CommMonoid R] [Monoid G] [SMul G Rˣ]
    (f : G × G × G → Rˣ) (hf : groupCohomology.IsMulCocycle₃ f)
    (htriv : ∀ (g : G) (x : Rˣ), g • x = x)
    (hf₁ : ∀ g j : G, f (g, 1, j) = 1) : TwistingCocycle (Additive G) R where
  ω i₁ i₂ i₃ := f (i₁.toMul, i₂.toMul, i₃.toMul)
  cocycle i₁ i₂ i₃ i₄ := by
    simpa only [toMul_add, htriv] using
      (groupCohomology.isMulCocycle₃_iff f).1 hf i₁.toMul i₂.toMul i₃.toMul i₄.toMul
  ω_zero i₁ i₃ := hf₁ _ _

end TauCeti.GradedObject

namespace CategoryTheory.GradedObject.Monoidal

variable {I : Type*} [AddMonoid I] {C : Type*} [Category* C] [MonoidalCategory C]
  [Preadditive C]

section Scale

variable {R : Type*} [Semiring R] [Linear R C] (X₁ X₂ X₃ : GradedObject I C) [HasTensor X₂ X₃]
  [HasTensor X₁ (tensorObj X₂ X₃)] [HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-- The endomorphism of `X₁ ⊗ (X₂ ⊗ X₃)` acting on the summand `X₁ i₁ ⊗ X₂ i₂ ⊗ X₃ i₃` as
multiplication by `u i₁ i₂ i₃`. -/
def scaleTensorObj₃ (u : I → I → I → R) :
    tensorObj X₁ (tensorObj X₂ X₃) ⟶ tensorObj X₁ (tensorObj X₂ X₃) := fun j =>
  mapBifunctorBifunctor₂₃Desc (ρ₂₃ := ρ₂₃)
    (fun i₁ i₂ i₃ h => u i₁ i₂ i₃ • ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j h)

/-- `scaleTensorObj₃ X₁ X₂ X₃ u` acts on the summand `X₁ i₁ ⊗ X₂ i₂ ⊗ X₃ i₃` as `u i₁ i₂ i₃`. -/
@[reassoc (attr := simp)]
lemma ιTensorObj₃_scaleTensorObj₃ (u : I → I → I → R) (i₁ i₂ i₃ j : I)
    (h : i₁ + i₂ + i₃ = j) :
    ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ scaleTensorObj₃ X₁ X₂ X₃ u j =
      u i₁ i₂ i₃ • ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j h := by
  unfold scaleTensorObj₃
  exact ι_mapBifunctorBifunctor₂₃Desc (F := curriedTensor C) (G₂₃ := curriedTensor C)
    (ρ₂₃ := ρ₂₃) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) _ i₁ i₂ i₃ h

/-- The constant scalar `1` acts as the identity. -/
lemma scaleTensorObj₃_one :
    scaleTensorObj₃ X₁ X₂ X₃ (fun _ _ _ => (1 : R)) = 𝟙 _ := by
  ext j i₁ i₂ i₃ h
  simp

/-- Composing the endomorphisms given by scalars `u` and `v` gives the one given by `u * v`. -/
@[reassoc]
lemma scaleTensorObj₃_comp (u v : I → I → I → R) :
    scaleTensorObj₃ X₁ X₂ X₃ u ≫ scaleTensorObj₃ X₁ X₂ X₃ v =
      scaleTensorObj₃ X₁ X₂ X₃ (fun i₁ i₂ i₃ => u i₁ i₂ i₃ * v i₁ i₂ i₃) := by
  ext j i₁ i₂ i₃ h
  simp [smul_smul]

/-- The endomorphisms `scaleTensorObj₃` are natural. -/
@[reassoc]
lemma tensorHom_tensorHom_scaleTensorObj₃ {Y₁ Y₂ Y₃ : GradedObject I C} [HasTensor Y₂ Y₃]
    [HasTensor Y₁ (tensorObj Y₂ Y₃)] [HasGoodTensorTensor₂₃ Y₁ Y₂ Y₃]
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) (u : I → I → I → R) :
    tensorHom f₁ (tensorHom f₂ f₃) ≫ scaleTensorObj₃ Y₁ Y₂ Y₃ u =
      scaleTensorObj₃ X₁ X₂ X₃ u ≫ tensorHom f₁ (tensorHom f₂ f₃) := by
  ext j i₁ i₂ i₃ h
  simp

end Scale

section Associator

variable {R : Type*} [Semiring R] [Linear R C] (ω : I → I → I → Rˣ)
  (X₁ X₂ X₃ : GradedObject I C) [HasTensor X₁ X₂] [HasTensor (tensorObj X₁ X₂) X₃]
  [HasTensor X₂ X₃] [HasTensor X₁ (tensorObj X₂ X₃)]
  [HasGoodTensor₁₂Tensor X₁ X₂ X₃] [HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-- The associator of graded objects twisted by `ω`: on the summand `(X₁ i₁ ⊗ X₂ i₂) ⊗ X₃ i₃` it
is `ω i₁ i₂ i₃` times the associator of `C`. -/
def twistedAssociator :
    tensorObj (tensorObj X₁ X₂) X₃ ≅ tensorObj X₁ (tensorObj X₂ X₃) where
  hom := (associator X₁ X₂ X₃).hom ≫ scaleTensorObj₃ X₁ X₂ X₃ fun i₁ i₂ i₃ => (ω i₁ i₂ i₃ : R)
  inv := scaleTensorObj₃ X₁ X₂ X₃ (fun i₁ i₂ i₃ => (((ω i₁ i₂ i₃)⁻¹ : Rˣ) : R)) ≫
    (associator X₁ X₂ X₃).inv
  hom_inv_id := by
    rw [assoc, scaleTensorObj₃_comp_assoc]
    simp [scaleTensorObj₃_one]
  inv_hom_id := by
    rw [assoc, Iso.inv_hom_id_assoc, scaleTensorObj₃_comp]
    simp [scaleTensorObj₃_one]

/-- The twisted associator is Mathlib's associator followed by the scalars `ω`. -/
lemma twistedAssociator_hom :
    (twistedAssociator ω X₁ X₂ X₃).hom =
      (associator X₁ X₂ X₃).hom ≫ scaleTensorObj₃ X₁ X₂ X₃ fun i₁ i₂ i₃ => (ω i₁ i₂ i₃ : R) :=
  rfl

/-- The inverse of the twisted associator is the scalars `ω⁻¹` followed by the inverse of Mathlib's
associator. -/
lemma twistedAssociator_inv :
    (twistedAssociator ω X₁ X₂ X₃).inv =
      scaleTensorObj₃ X₁ X₂ X₃ (fun i₁ i₂ i₃ => (((ω i₁ i₂ i₃)⁻¹ : Rˣ) : R)) ≫
        (associator X₁ X₂ X₃).inv :=
  rfl

/-- The twisted associator acts on the summand `(X₁ i₁ ⊗ X₂ i₂) ⊗ X₃ i₃` as `ω i₁ i₂ i₃` times the
associator of `C`. -/
@[reassoc (attr := simp)]
lemma ιTensorObj₃'_twistedAssociator_hom (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) :
    ιTensorObj₃' X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ (twistedAssociator ω X₁ X₂ X₃).hom j =
      (ω i₁ i₂ i₃ : R) • ((α_ _ _ _).hom ≫ ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j h) := by
  simp [twistedAssociator_hom]

/-- The inverse twisted associator acts on the summand `X₁ i₁ ⊗ X₂ i₂ ⊗ X₃ i₃` as
`(ω i₁ i₂ i₃)⁻¹` times the inverse associator of `C`. -/
@[reassoc (attr := simp)]
lemma ιTensorObj₃_twistedAssociator_inv (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) :
    ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ (twistedAssociator ω X₁ X₂ X₃).inv j =
      (((ω i₁ i₂ i₃)⁻¹ : Rˣ) : R) • ((α_ _ _ _).inv ≫ ιTensorObj₃' X₁ X₂ X₃ i₁ i₂ i₃ j h) := by
  simp [twistedAssociator_inv]

/-- Twisting by the constant cocycle `1` recovers Mathlib's associator of graded objects. -/
lemma twistedAssociator_one :
    twistedAssociator (fun _ _ _ => (1 : Rˣ)) X₁ X₂ X₃ = associator X₁ X₂ X₃ := by
  ext : 1
  simp [twistedAssociator_hom, scaleTensorObj₃_one]

variable {X₁ X₂ X₃} in
/-- The twisted associator is natural. -/
lemma twistedAssociator_naturality {Y₁ Y₂ Y₃ : GradedObject I C} [HasTensor Y₁ Y₂]
    [HasTensor (tensorObj Y₁ Y₂) Y₃] [HasTensor Y₂ Y₃] [HasTensor Y₁ (tensorObj Y₂ Y₃)]
    [HasGoodTensor₁₂Tensor Y₁ Y₂ Y₃] [HasGoodTensorTensor₂₃ Y₁ Y₂ Y₃]
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    tensorHom (tensorHom f₁ f₂) f₃ ≫ (twistedAssociator ω Y₁ Y₂ Y₃).hom =
      (twistedAssociator ω X₁ X₂ X₃).hom ≫ tensorHom f₁ (tensorHom f₂ f₃) := by
  rw [twistedAssociator_hom, twistedAssociator_hom, ← assoc,
    GradedObject.Monoidal.associator_naturality, assoc, assoc,
    tensorHom_tensorHom_scaleTensorObj₃]

end Associator

section Pentagon

variable {R : Type*} [CommSemiring R] [Linear R C] [MonoidalPreadditive C] [MonoidalLinear R C]
  (ω : I → I → I → Rˣ)
  (hω : ∀ i₁ i₂ i₃ i₄ : I,
    ω (i₁ + i₂) i₃ i₄ * ω i₁ i₂ (i₃ + i₄) = ω i₂ i₃ i₄ * ω i₁ (i₂ + i₃) i₄ * ω i₁ i₂ i₃)
  (X₁ X₂ X₃ X₄ : GradedObject I C)
  [HasTensor X₁ X₂] [HasTensor X₂ X₃] [HasTensor X₃ X₄]
  [HasTensor (tensorObj X₁ X₂) X₃] [HasTensor X₁ (tensorObj X₂ X₃)]
  [HasTensor (tensorObj X₂ X₃) X₄] [HasTensor X₂ (tensorObj X₃ X₄)]
  [HasTensor (tensorObj (tensorObj X₁ X₂) X₃) X₄]
  [HasTensor (tensorObj X₁ (tensorObj X₂ X₃)) X₄]
  [HasTensor X₁ (tensorObj (tensorObj X₂ X₃) X₄)]
  [HasTensor X₁ (tensorObj X₂ (tensorObj X₃ X₄))]
  [HasTensor (tensorObj X₁ X₂) (tensorObj X₃ X₄)]
  [HasGoodTensor₁₂Tensor X₁ X₂ X₃] [HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasGoodTensor₁₂Tensor X₁ (tensorObj X₂ X₃) X₄]
  [HasGoodTensorTensor₂₃ X₁ (tensorObj X₂ X₃) X₄]
  [HasGoodTensor₁₂Tensor X₂ X₃ X₄] [HasGoodTensorTensor₂₃ X₂ X₃ X₄]
  [HasGoodTensor₁₂Tensor (tensorObj X₁ X₂) X₃ X₄]
  [HasGoodTensorTensor₂₃ (tensorObj X₁ X₂) X₃ X₄]
  [HasGoodTensor₁₂Tensor X₁ X₂ (tensorObj X₃ X₄)]
  [HasGoodTensorTensor₂₃ X₁ X₂ (tensorObj X₃ X₄)]
  [HasTensor₄ObjExt X₁ X₂ X₃ X₄]

include hω in
/-- The pentagon axiom for the twisted associator, in terms of inverses: the scalars produced
on the summand indexed by `(i₁, i₂, i₃, i₄)` by the two sides agree by the cocycle identity. -/
@[reassoc]
lemma twistedAssociator_pentagon_inv :
    tensorHom (𝟙 X₁) (twistedAssociator ω X₂ X₃ X₄).inv ≫
        (twistedAssociator ω X₁ (tensorObj X₂ X₃) X₄).inv ≫
        tensorHom (twistedAssociator ω X₁ X₂ X₃).inv (𝟙 X₄) =
      (twistedAssociator ω X₁ X₂ (tensorObj X₃ X₄)).inv ≫
        (twistedAssociator ω (tensorObj X₁ X₂) X₃ X₄).inv := by
  -- This is Mathlib's proof of `GradedObject.Monoidal.pentagon_inv`, run on the summand indexed
  -- by `(i₁, i₂, i₃, i₄)`. Each inverse twisted associator contributes a scalar, which is pulled to
  -- the front as soon as it appears; at the end both sides are scalar multiples of the same
  -- morphism, and the two scalars agree by the cocycle identity `hω i₁ i₂ i₃ i₄`.
  ext j i₁ i₂ i₃ i₄ h
  dsimp only [categoryOfGradedObjects_comp]
  conv_lhs =>
    rw [ιTensorObj₄_eq X₁ X₂ X₃ X₄ i₁ i₂ i₃ i₄ j h _ rfl, assoc, ι_tensorHom_assoc]
    dsimp only [categoryOfGradedObjects_id, id_eq, eq_mpr_eq_cast, cast_eq]
    rw [id_tensorHom, ← MonoidalCategory.whiskerLeft_comp_assoc,
      ιTensorObj₃_twistedAssociator_inv]
    simp only [MonoidalLinear.whiskerLeft_smul, Linear.smul_comp, Linear.comp_smul]
    rw [ιTensorObj₃'_eq X₂ X₃ X₄ i₂ i₃ i₄ _ rfl _ rfl, MonoidalCategory.whiskerLeft_comp_assoc,
      MonoidalCategory.whiskerLeft_comp_assoc,
      ← ιTensorObj₃_eq_assoc X₁ (tensorObj X₂ X₃) X₄ i₁ (i₂ + i₃) i₄ j
        (by simp only [← add_assoc, h]) _ rfl, ιTensorObj₃_twistedAssociator_inv_assoc]
    simp only [Linear.smul_comp, Linear.comp_smul, smul_smul, assoc]
    rw [ιTensorObj₃'_eq_assoc X₁ (tensorObj X₂ X₃) X₄ i₁ (i₂ + i₃) i₄ j
        (by simp only [← add_assoc, h]) (i₁ + i₂ + i₃) (by rw [add_assoc]), ι_tensorHom]
    dsimp only [id_eq, eq_mpr_eq_cast, categoryOfGradedObjects_id]
    rw [tensorHom_id, whisker_assoc_symm_assoc, Iso.hom_inv_id_assoc,
      ← MonoidalCategory.comp_whiskerRight_assoc, ← MonoidalCategory.comp_whiskerRight_assoc,
      ← ιTensorObj₃_eq X₁ X₂ X₃ i₁ i₂ i₃ _ rfl _ rfl, ιTensorObj₃_twistedAssociator_inv]
    simp only [MonoidalLinear.smul_whiskerRight, Linear.smul_comp, Linear.comp_smul, smul_smul,
      assoc]
    rw [MonoidalCategory.comp_whiskerRight_assoc, MonoidalCategory.pentagon_inv_assoc]
  conv_rhs =>
    rw [ιTensorObj₄_eq X₁ X₂ X₃ X₄ i₁ i₂ i₃ i₄ _ _ _ rfl,
      ιTensorObj₃_eq X₂ X₃ X₄ i₂ i₃ i₄ _ rfl _ rfl, assoc,
      MonoidalCategory.whiskerLeft_comp_assoc,
      ← ιTensorObj₃_eq_assoc X₁ X₂ (tensorObj X₃ X₄) i₁ i₂ (i₃ + i₄) j
        (by rw [← add_assoc, h]) (i₂ + i₃ + i₄) (by rw [add_assoc]),
      ιTensorObj₃_twistedAssociator_inv_assoc]
    simp only [Linear.smul_comp, Linear.comp_smul, smul_smul, assoc]
    rw [associator_inv_naturality_right_assoc,
      ιTensorObj₃'_eq_assoc X₁ X₂ (tensorObj X₃ X₄) i₁ i₂ (i₃ + i₄) j
        (by rw [← add_assoc, h]) _ rfl, whisker_exchange_assoc,
      ← ιTensorObj₃_eq_assoc (tensorObj X₁ X₂) X₃ X₄ (i₁ + i₂) i₃ i₄ j h _ rfl,
      ιTensorObj₃_twistedAssociator_inv]
    simp only [Linear.smul_comp, Linear.comp_smul, smul_smul, assoc]
    rw [whiskerRight_tensor_assoc, Iso.hom_inv_id_assoc,
      ιTensorObj₃'_eq (tensorObj X₁ X₂) X₃ X₄ (i₁ + i₂) i₃ i₄ j h _ rfl,
      ← MonoidalCategory.comp_whiskerRight_assoc,
      ← ιTensorObj₃'_eq X₁ X₂ X₃ i₁ i₂ i₃ _ rfl _ rfl]
  congr 1
  simp only [← Units.val_mul, ← mul_inv]
  congr 2
  rw [← hω, mul_comm]

include hω in
/-- The pentagon axiom for the twisted associator. -/
lemma twistedAssociator_pentagon :
    tensorHom (twistedAssociator ω X₁ X₂ X₃).hom (𝟙 X₄) ≫
        (twistedAssociator ω X₁ (tensorObj X₂ X₃) X₄).hom ≫
        tensorHom (𝟙 X₁) (twistedAssociator ω X₂ X₃ X₄).hom =
      (twistedAssociator ω (tensorObj X₁ X₂) X₃ X₄).hom ≫
        (twistedAssociator ω X₁ X₂ (tensorObj X₃ X₄)).hom := by
  rw [← cancel_epi (twistedAssociator ω (tensorObj X₁ X₂) X₃ X₄).inv,
    ← cancel_epi (twistedAssociator ω X₁ X₂ (tensorObj X₃ X₄)).inv, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, ← twistedAssociator_pentagon_inv_assoc ω hω]
  simp [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom_assoc]

end Pentagon

section Triangle

variable {R : Type*} [Semiring R] [Linear R C] (ω : I → I → I → Rˣ)
  (hω : ∀ i₁ i₃ : I, ω i₁ 0 i₃ = 1)
  [DecidableEq I] [HasInitial C]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  (X₁ X₃ : GradedObject I C) [HasTensor X₁ X₃]
  [HasTensor (tensorObj X₁ tensorUnit) X₃] [HasTensor X₁ (tensorObj tensorUnit X₃)]
  [HasGoodTensor₁₂Tensor X₁ tensorUnit X₃] [HasGoodTensorTensor₂₃ X₁ tensorUnit X₃]

omit [HasTensor X₁ X₃] [HasTensor (tensorObj X₁ tensorUnit) X₃]
  [HasGoodTensor₁₂Tensor X₁ tensorUnit X₃] in
include hω in
/-- A scalar function normalized in the middle variable acts trivially on
`X₁ ⊗ (𝟙 ⊗ X₃)`, whose summands with a nonzero middle index are initial. -/
lemma scaleTensorObj₃_tensorUnit :
    scaleTensorObj₃ X₁ tensorUnit X₃ (fun i₁ i₂ i₃ => (ω i₁ i₂ i₃ : R)) = 𝟙 _ := by
  ext j i₁ i₂ i₃ h
  by_cases hi : i₂ = 0
  · subst hi
    simp [hω]
  · exact (((isInitialTensorUnitApply i₂ hi).isInitialObj
      ((curriedTensor C).flip.obj (X₃ i₃))).isInitialObj
        ((curriedTensor C).obj (X₁ i₁))).hom_ext _ _

include hω in
/-- The triangle axiom for the twisted associator. -/
lemma twistedAssociator_triangle :
    (twistedAssociator ω X₁ tensorUnit X₃).hom ≫ tensorHom (𝟙 X₁) (leftUnitor X₃).hom =
      tensorHom (rightUnitor X₁).hom (𝟙 X₃) := by
  rw [twistedAssociator_hom, scaleTensorObj₃_tensorUnit ω hω, comp_id, triangle]

end Triangle

end CategoryTheory.GradedObject.Monoidal

namespace TauCeti.GradedObject

open CategoryTheory.GradedObject CategoryTheory.GradedObject.Monoidal

variable {I : Type*} [AddMonoid I] {R : Type*} [CommSemiring R]

/-- The category of `I`-graded objects of `C`, with the monoidal structure whose associator is
twisted by the normalized `3`-cocycle `c`. For `I = Additive G` and `C = ModuleCat k` this is the
category of `G`-graded vector spaces with associator twisted by `c`. -/
def Twisted (_c : TwistingCocycle I R) (C : Type*) : Type _ := GradedObject I C

namespace Twisted

variable (c : TwistingCocycle I R) (C : Type*) [Category* C]

instance : Category (Twisted c C) := inferInstanceAs (Category (GradedObject I C))

variable [MonoidalCategory C] [Preadditive C] [Linear R C] [MonoidalPreadditive C]
  [MonoidalLinear R C]
  [∀ (X₁ X₂ : GradedObject I C), HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ : GradedObject I C), HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [DecidableEq I] [HasInitial C]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), HasTensor₄ObjExt X₁ X₂ X₃ X₄]

/-- The monoidal structure on graded objects with associator twisted by a normalized `3`-cocycle:
Mathlib's tensor product and unitors of graded objects, with the associator
`CategoryTheory.GradedObject.Monoidal.twistedAssociator`. -/
instance instMonoidalCategory : MonoidalCategory (Twisted c C) where
  tensorObj (X Y : GradedObject I C) := Monoidal.tensorObj X Y
  tensorHom {X₁ Y₁ X₂ Y₂ : GradedObject I C} f g := Monoidal.tensorHom (X₁ := X₁) (X₂ := Y₁)
    (Y₁ := X₂) (Y₂ := Y₂) f g
  tensorHom_def {X₁ Y₁ X₂ Y₂ : GradedObject I C} f g := Monoidal.tensorHom_def (X₁ := X₁)
    (X₂ := Y₁) (Y₁ := X₂) (Y₂ := Y₂) f g
  whiskerLeft (X : GradedObject I C) (Y₁ Y₂ : GradedObject I C) φ :=
    Monoidal.whiskerLeft X (Y₁ := Y₁) (Y₂ := Y₂) φ
  whiskerRight {X₁ X₂ : GradedObject I C} φ (Y : GradedObject I C) :=
    Monoidal.whiskerRight (X₁ := X₁) (X₂ := X₂) φ Y
  id_tensorHom_id (X₁ X₂ : GradedObject I C) := Monoidal.id_tensorHom_id X₁ X₂
  whiskerLeft_id (X Y : GradedObject I C) := Monoidal.id_tensorHom_id X Y
  id_whiskerRight (X Y : GradedObject I C) := Monoidal.id_tensorHom_id X Y
  tensorUnit := Monoidal.tensorUnit (C := C)
  associator (X₁ X₂ X₃ : GradedObject I C) := twistedAssociator c.ω X₁ X₂ X₃
  associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : GradedObject I C} f₁ f₂ f₃ :=
    twistedAssociator_naturality (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) (Y₁ := Y₁) (Y₂ := Y₂)
      (Y₃ := Y₃) c.ω f₁ f₂ f₃
  leftUnitor (X : GradedObject I C) := Monoidal.leftUnitor X
  leftUnitor_naturality {X Y : GradedObject I C} f :=
    Monoidal.leftUnitor_naturality (X := X) (X' := Y) f
  rightUnitor (X : GradedObject I C) := Monoidal.rightUnitor X
  rightUnitor_naturality {X Y : GradedObject I C} f :=
    Monoidal.rightUnitor_naturality (X := X) (X' := Y) f
  tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : GradedObject I C} f₁ f₂ g₁ g₂ :=
    Monoidal.tensorHom_comp_tensorHom (X₁ := X₁) (X₂ := Y₁) (X₃ := Z₁) (Y₁ := X₂) (Y₂ := Y₂)
      (Y₃ := Z₂) f₁ g₁ f₂ g₂
  pentagon (X₁ X₂ X₃ X₄ : GradedObject I C) :=
    twistedAssociator_pentagon c.ω c.cocycle X₁ X₂ X₃ X₄
  triangle (X₁ X₂ : GradedObject I C) := twistedAssociator_triangle c.ω c.ω_zero X₁ X₂

variable {c C}

/-- The twisted associator acts on the summand `(X₁ i₁ ⊗ X₂ i₂) ⊗ X₃ i₃` of `(X₁ ⊗ X₂) ⊗ X₃` as
`c.ω i₁ i₂ i₃` times the associator of `C`. -/
@[reassoc (attr := simp)]
lemma ιTensorObj₃'_associator_hom (X₁ X₂ X₃ : GradedObject I C) (i₁ i₂ i₃ j : I)
    (h : i₁ + i₂ + i₃ = j) :
    ιTensorObj₃' X₁ X₂ X₃ i₁ i₂ i₃ j h ≫
        (@MonoidalCategoryStruct.associator (Twisted c C) _ _ X₁ X₂ X₃).hom j =
      (c.ω i₁ i₂ i₃ : R) • ((α_ _ _ _).hom ≫ ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j h) :=
  ιTensorObj₃'_twistedAssociator_hom c.ω X₁ X₂ X₃ i₁ i₂ i₃ j h

/-- The inverse of the twisted associator acts on the summand `X₁ i₁ ⊗ X₂ i₂ ⊗ X₃ i₃` of
`X₁ ⊗ (X₂ ⊗ X₃)` as `(c.ω i₁ i₂ i₃)⁻¹` times the inverse associator of `C`. -/
@[reassoc (attr := simp)]
lemma ιTensorObj₃_associator_inv (X₁ X₂ X₃ : GradedObject I C) (i₁ i₂ i₃ j : I)
    (h : i₁ + i₂ + i₃ = j) :
    ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j h ≫
        (@MonoidalCategoryStruct.associator (Twisted c C) _ _ X₁ X₂ X₃).inv j =
      (((c.ω i₁ i₂ i₃)⁻¹ : Rˣ) : R) •
        ((α_ _ _ _).inv ≫ ιTensorObj₃' X₁ X₂ X₃ i₁ i₂ i₃ j h) :=
  ιTensorObj₃_twistedAssociator_inv c.ω X₁ X₂ X₃ i₁ i₂ i₃ j h

end Twisted

end TauCeti.GradedObject
