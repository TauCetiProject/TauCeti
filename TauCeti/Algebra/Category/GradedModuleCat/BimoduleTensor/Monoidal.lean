/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.Associator
public import TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.Unit
public import TauCeti.Algebra.Category.GradedModuleCat.Coproducts.Basic
public import TauCeti.Algebra.Homology.Bifunctor.Homotopy
public import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Coherence for graded bimodule tensor composition

The associator of graded bimodule composition satisfies the pentagon, including
heterogeneous composition over five graded algebras. With the regular bimodule
as unit, it also satisfies the triangle. Both equations follow from pure-tensor
extensionality; the triangle is precisely the balancing relation.

For endobimodules these identities package the existing tensor maps, associator,
and unitors into `bimoduleMonoidalCategory`. The structure is chosen explicitly so its
factor grading and carrier universe remain visible. Its curried tensor functor is the existing
`bimoduleTensor`.

The module also provides `GradedBimoduleMonoidalDatum`, the pointwise homotopy-monoidal datum
of a functor on complexes of graded bimodules: for every pair of source complexes `X` and `Y`,
a homotopy equivalence comparing the target tensor product of the image complexes with the
image of the source tensor product. It is the monoidal compatibility data that such a functor
has to supply.

-/

public section

noncomputable section
open CategoryTheory MulOpposite
open scoped TensorProduct MonoidalCategory
namespace TauCeti.GradedModuleCat
universe v vM vN vP vQ uk uA uB uC uD uE
variable {k : Type uk} {A : Type uA} {B : Type uB} {C : Type uC}
  {D : Type uD} {E : Type uE}
  [CommRing k] [Ring A] [Ring B] [Ring C] [Ring D] [Ring E]
  [Algebra k A] [Algebra k B] [Algebra k C] [Algebra k D] [Algebra k E]
  (Γ : InternalGrading k A) (Δ : InternalGrading k B) (Θ : InternalGrading k C)
  (Ψ : InternalGrading k D) (Ω : InternalGrading k E)
  [GradedAlgebra Γ.piece] [GradedAlgebra Δ.piece] [GradedAlgebra Θ.piece]
  [GradedAlgebra Ψ.piece] [GradedAlgebra Ω.piece]

/-- Reassociation of four graded bimodules satisfies the pentagon. -/
@[reassoc]
theorem bimoduleTensorAssociator_pentagon
    (M : GradedModuleCat.{vM} (Γ.tensorProduct Δ.opposite).piece)
    (N : GradedModuleCat.{vN} (Δ.tensorProduct Θ.opposite).piece)
    (P : GradedModuleCat.{vP} (Θ.tensorProduct Ψ.opposite).piece)
    (Q : GradedModuleCat.{vQ} (Ψ.tensorProduct Ω.opposite).piece) :
    bimoduleTensorMap Γ Ψ Ω (bimoduleTensorAssociator Γ Δ Θ Ψ M N P).hom (𝟙 Q) ≫
        (bimoduleTensorAssociator Γ Δ Ψ Ω M (bimoduleTensorObj Δ Θ Ψ N P) Q).hom ≫
        bimoduleTensorMap Γ Δ Ω (𝟙 M) (bimoduleTensorAssociator Δ Θ Ψ Ω N P Q).hom =
      (bimoduleTensorAssociator Γ Θ Ψ Ω (bimoduleTensorObj Γ Δ Θ M N) P Q).hom ≫
        (bimoduleTensorAssociator Γ Δ Θ Ω M N (bimoduleTensorObj Θ Ψ Ω P Q)).hom := by
  apply bimoduleTensor_hom_ext Γ Ψ Ω
  intro x q
  induction x using bimoduleTensor_induction_on Γ Θ Ψ (bimoduleTensorObj Γ Δ Θ M N) P with
  | ht y p =>
    induction y using bimoduleTensor_induction_on Γ Δ Θ M N with
    | ht m n =>
      simp only [hom_comp, LinearMap.comp_apply, bimoduleTensorMap_tmul,
        bimoduleTensorAssociator_hom_tmul, hom_id, LinearMap.id_apply]
    | ha y z hy hz =>
      simp only [bimoduleTensorTmul_add_left, map_add, hy, hz]
  | ha x y hx hy => simp only [bimoduleTensorTmul_add_left, map_add, hx, hy]

/-- Evaluation of the middle regular bimodule is compatible with reassociation. -/
@[reassoc]
theorem bimoduleTensorAssociator_triangle
    (M : GradedModuleCat.{max v uB} (Γ.tensorProduct Δ.opposite).piece)
    (N : GradedModuleCat.{max v uB} (Δ.tensorProduct Θ.opposite).piece) :
    (bimoduleTensorAssociator Γ Δ Δ Θ M (bimoduleUnit.{v} Δ) N).hom ≫
        bimoduleTensorMap Γ Δ Θ (𝟙 M) (bimoduleTensorLeftUnitor.{v} Δ Θ N).hom =
      bimoduleTensorMap Γ Δ Θ (bimoduleTensorRightUnitor.{v} Γ Δ M).hom (𝟙 N) := by
  apply bimoduleTensor_hom_ext Γ Δ Θ
  intro x n
  induction x using bimoduleTensor_induction_on Γ Δ Δ M (bimoduleUnit.{v} Δ) with
  | ht m u =>
    simp only [hom_comp, LinearMap.comp_apply, bimoduleTensorAssociator_hom_tmul,
      bimoduleTensorMap_tmul, hom_id, LinearMap.id_apply,
      bimoduleTensorLeftUnitor_hom, bimoduleTensorRightUnitor_hom,
      bimoduleTensorLeftUnitorHom_tmul, bimoduleTensorRightUnitorHom_tmul]
    exact (bimoduleTensorTmul_balance Γ Δ Θ M N
      ((bimoduleUnitEquiv.{v} Δ).symm u) m n).symm
  | ha x y hx hy => simp only [bimoduleTensorTmul_add_left, map_add, hx, hy]

/-- The chosen monoidal structure on graded endobimodules, with regular bimodule unit. -/
-- Expose the chosen object assignments so dependent morphism and isomorphism types compute.
@[expose, instance_reducible]
def bimoduleMonoidalCategory :
    MonoidalCategory (GradedModuleCat.{max v uA} (Γ.tensorProduct Γ.opposite).piece) :=
  let _ : MonoidalCategoryStruct
      (GradedModuleCat.{max v uA} (Γ.tensorProduct Γ.opposite).piece) :=
    { tensorObj := bimoduleTensorObj Γ Γ Γ
      tensorHom := bimoduleTensorMap Γ Γ Γ
      whiskerLeft M {N P} f := bimoduleTensorMap Γ Γ Γ (𝟙 M) f
      whiskerRight {N P} f M := bimoduleTensorMap Γ Γ Γ f (𝟙 M)
      tensorUnit := bimoduleUnit.{v} Γ
      associator := bimoduleTensorAssociator Γ Γ Γ Γ
      leftUnitor := bimoduleTensorLeftUnitor.{v} Γ Γ
      rightUnitor := bimoduleTensorRightUnitor.{v} Γ Γ }
  MonoidalCategory.ofTensorHom
    (fun _ _ ↦ bimoduleTensorMap_id Γ Γ Γ)
    (fun _ {_ _} _ ↦ rfl) (fun {_ _} _ _ ↦ rfl)
    (by
      intro X₁ Y₁ Z₁ X₂ Y₂ Z₂ f₁ f₂ g₁ g₂
      exact (bimoduleTensorMap_comp Γ Γ Γ f₁ f₂ g₁ g₂).symm)
    (by
      intro X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃
      exact bimoduleTensorAssociator_naturality Γ Γ Γ Γ X₁ X₂ X₃ f₁ f₂ f₃)
    (by
      intro X Y f
      have h := bimoduleTensorLeftUnitorHom_naturality Γ Γ X f
      simp only [← bimoduleTensorLeftUnitor_hom] at h
      exact h)
    (by
      intro X Y f
      have h := bimoduleTensorRightUnitorHom_naturality Γ Γ X f
      simp only [← bimoduleTensorRightUnitor_hom] at h
      exact h)
    (bimoduleTensorAssociator_pentagon Γ Γ Γ Γ Γ)
    (bimoduleTensorAssociator_triangle.{v} Γ Γ Γ)

section Components

variable (M N P Q : GradedModuleCat.{max v uA} (Γ.tensorProduct Γ.opposite).piece)

/-- The chosen tensor object is balanced graded bimodule composition. -/
@[simp]
theorem bimoduleMonoidalCategory_tensorObj :
    let _ := bimoduleMonoidalCategory.{v} Γ
    M ⊗ N = bimoduleTensorObj Γ Γ Γ M N := (rfl)

/-- The chosen tensor morphism is the map induced on the balanced tensor product. -/
@[simp]
theorem bimoduleMonoidalCategory_tensorHom (f : M ⟶ N) (g : P ⟶ Q) :
    let _ := bimoduleMonoidalCategory.{v} Γ
    f ⊗ₘ g = bimoduleTensorMap Γ Γ Γ f g := (rfl)

/-- Left whiskering maps the second balanced tensor factor. -/
@[simp]
theorem bimoduleMonoidalCategory_whiskerLeft (f : N ⟶ P) :
    let _ := bimoduleMonoidalCategory.{v} Γ
    M ◁ f = bimoduleTensorMap Γ Γ Γ (𝟙 M) f := (rfl)

/-- Right whiskering maps the first balanced tensor factor. -/
@[simp]
theorem bimoduleMonoidalCategory_whiskerRight (f : M ⟶ N) :
    let _ := bimoduleMonoidalCategory.{v} Γ
    f ▷ P = bimoduleTensorMap Γ Γ Γ f (𝟙 P) := (rfl)

/-- The chosen associator is graded balanced-tensor reassociation. -/
@[simp]
theorem bimoduleMonoidalCategory_associator :
    let _ := bimoduleMonoidalCategory.{v} Γ
    α_ M N P = bimoduleTensorAssociator Γ Γ Γ Γ M N P := (rfl)

/-- The chosen left unitor evaluates the regular left factor. -/
@[simp]
theorem bimoduleMonoidalCategory_leftUnitor :
    let _ := bimoduleMonoidalCategory.{v} Γ
    λ_ M = bimoduleTensorLeftUnitor.{v} Γ Γ M := (rfl)

/-- The chosen right unitor evaluates the regular right factor. -/
@[simp]
theorem bimoduleMonoidalCategory_rightUnitor :
    let _ := bimoduleMonoidalCategory.{v} Γ
    ρ_ M = bimoduleTensorRightUnitor.{v} Γ Γ M := (rfl)

end Components

/-- The chosen tensor unit is the universe-lifted regular graded bimodule. -/
@[simp]
theorem bimoduleMonoidalCategory_tensorUnit :
    let _ := bimoduleMonoidalCategory.{v} Γ
    𝟙_ (GradedModuleCat.{max v uA} (Γ.tensorProduct Γ.opposite).piece) =
      bimoduleUnit.{v} Γ := (rfl)

/-- The chosen monoidal tensor functor is the canonical balanced bimodule bifunctor. -/
@[simp]
theorem bimoduleMonoidalCategory_curriedTensor :
    let _ := bimoduleMonoidalCategory.{v} Γ
    MonoidalCategory.curriedTensor (GradedModuleCat.{max v uA} (Γ.tensorProduct Γ.opposite).piece) =
      bimoduleTensor Γ Γ Γ := (rfl)

end TauCeti.GradedModuleCat

namespace TauCeti

universe w uA uB

variable (k : Type w) [CommRing k]

local notation "c" => ComplexShape.up ℤ

variable {A₁ : Type uA} [Ring A₁] [Algebra k A₁]
variable {A₂ : Type uB} [Ring A₂] [Algebra k A₂]
variable (Ξ₁ : InternalGrading k A₁) [GradedAlgebra Ξ₁.piece]
variable (Ξ₂ : InternalGrading k A₂) [GradedAlgebra Ξ₂.piece]
variable (Φ : HomologicalComplex (GradedBimoduleCat k Ξ₁) c ⥤
    HomologicalComplex (GradedBimoduleCat k Ξ₂) c)

/-- The pointwise homotopy-monoidal datum of the functor `Φ` on complexes of graded bimodules
between the source and the target graded bimodule setting: for every pair of source complexes
`X` and `Y`, a homotopy equivalence comparing the target tensor product of the image
complexes with the image of the source tensor product. -/
abbrev GradedBimoduleMonoidalDatum :=
  ∀ (X Y : HomologicalComplex (GradedBimoduleCat k Ξ₁) c),
    HomotopyEquiv
      (HomologicalComplex.mapBifunctor (Φ.obj X) (Φ.obj Y)
        (GradedModuleCat.bimoduleTensor Ξ₂ Ξ₂ Ξ₂) c)
      (Φ.obj (HomologicalComplex.mapBifunctor X Y
        (GradedModuleCat.bimoduleTensor Ξ₁ Ξ₁ Ξ₁) c))

end TauCeti
