/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Etale.Finite

/-!
# Finite étale schemes and their coordinate algebras

Finite étale schemes over an affine base are anti-equivalent to finite étale algebras over
its coordinate ring. In particular, over a separably closed field they are equivalent to
finite sets. These comparisons allow finite étale geometry to be expressed in terms of
coordinate algebras without replacing a scheme by a chosen affine presentation.

The construction restricts Mathlib's fully faithful `AlgebraicGeometry.algSpec`; essential
surjectivity uses affineness of finite morphisms. The inverse is naturally identified with
`AlgebraicGeometry.algΓ` using `AlgebraicGeometry.algΓAlgSpecAdjunction`. The classification
over a separably closed field uses `CommAlgCat.FiniteEtale.equivOfIsSepClosed`.

## References

* The Stacks Project, *Étale morphisms*, Sections 29.36 and 58.2.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace TauCeti

/-- The property of a scheme over `S` being finite and étale over `S`. -/
def finiteEtaleSchemeProperty (S : Scheme.{u}) : ObjectProperty (Over S) :=
  (@IsFinite ⊓ @Etale : MorphismProperty Scheme).overObj

/-- A scheme over `S` is finite étale exactly when its structure morphism is finite and étale. -/
@[simp]
theorem finiteEtaleSchemeProperty_iff {S : Scheme.{u}} (X : Over S) :
    finiteEtaleSchemeProperty S X ↔ IsFinite X.hom ∧ Etale X.hom :=
  (Iff.rfl)

/-- Finite étale schemes over `S`, with all morphisms over `S`. -/
abbrev FiniteEtaleScheme (S : Scheme.{u}) :=
  (finiteEtaleSchemeProperty S).FullSubcategory

namespace FiniteEtaleScheme

instance {S : Scheme.{u}} (X : FiniteEtaleScheme S) : IsFinite X.obj.hom := X.property.1

instance {S : Scheme.{u}} (X : FiniteEtaleScheme S) : Etale X.obj.hom := X.property.2

/-- Bundle a scheme with a finite étale structure morphism. -/
def ofHom {S X : Scheme.{u}} (f : X ⟶ S) [IsFinite f] [Etale f] : FiniteEtaleScheme S :=
  ⟨Over.mk f, by
    constructor
    · exact ‹IsFinite f›
    · exact ‹Etale f›⟩

/-- The underlying object over `S` of `ofHom f` is `Over.mk f`. -/
@[simp]
theorem ofHom_obj {S X : Scheme.{u}} (f : X ⟶ S) [IsFinite f] [Etale f] :
    (ofHom f).obj = Over.mk f :=
  (rfl)

variable (R : CommRingCat.{u})

/-- The spectrum functor on finite étale algebras, with target finite étale schemes. -/
noncomputable def spec : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ ⥤ FiniteEtaleScheme (Spec R) :=
  (finiteEtaleSchemeProperty (Spec R)).lift
    ((CommAlgCat.finiteEtale R).ι.op ⋙ algSpec R) fun A ↦ by
      -- `algSpec` bundles the ordinary spectrum and its algebra structure map. Give the
      -- properties on that spectrum explicitly to avoid rewriting its dependent source.
      have hf : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R A.unop.obj))) :=
        (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
      have he : Etale (Spec.map (CommRingCat.ofHom (algebraMap R A.unop.obj))) :=
        (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
          (RingHom.etale_algebraMap.mpr inferInstance)
      exact ⟨hf, he⟩

/-- Forgetting the finite étale properties of `spec` gives Mathlib's algebraic spectrum
functor, on both objects and morphisms. -/
@[simp]
theorem spec_comp_ι :
    spec R ⋙ (finiteEtaleSchemeProperty (Spec R)).ι =
      (CommAlgCat.finiteEtale R).ι.op ⋙ algSpec R :=
  (rfl)

/-- The object over the base underlying a finite étale spectrum is Mathlib's algebraic
spectrum of its coordinate algebra. -/
@[simp]
theorem spec_obj_obj (A : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ) :
    ((spec R).obj A).obj = (algSpec R).obj (op A.unop.obj) :=
  (rfl)

private theorem exists_spec_iso (X : FiniteEtaleScheme (Spec R)) :
    ∃ A : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ, Nonempty ((spec R).obj A ≅ X) := by
  have : IsAffine X.obj.left := isAffine_of_isAffineHom X.obj.hom
  let φ := (Spec.preimage (X.obj.left.isoSpec.inv ≫ X.obj.hom)).hom
  let _ : Algebra R Γ(X.obj.left, ⊤) := φ.toAlgebra
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap R Γ(X.obj.left, ⊤))) =
      X.obj.left.isoSpec.inv ≫ X.obj.hom := Spec.map_preimage _
  have hfinite : IsFinite (Spec.map (CommRingCat.ofHom
      (algebraMap R Γ(X.obj.left, ⊤)))) := by
    rw [hφ]
    infer_instance
  have hetale : Etale (Spec.map (CommRingCat.ofHom
      (algebraMap R Γ(X.obj.left, ⊤)))) := by
    rw [hφ]
    infer_instance
  have : Module.Finite R Γ(X.obj.left, ⊤) :=
    RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp hfinite)
  have : Algebra.Etale R Γ(X.obj.left, ⊤) :=
    RingHom.etale_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Etale)).mp hetale)
  refine ⟨op (CommAlgCat.FiniteEtale.of R Γ(X.obj.left, ⊤)),
    ⟨ObjectProperty.isoMk _ (Over.isoMk X.obj.left.isoSpec.symm ?_)⟩⟩
  exact hφ.symm

instance : (spec R).EssSurj where
  mem_essImage X := exists_spec_iso R X

instance : (spec R).IsEquivalence where
  faithful := ObjectProperty.instFaithfulFullSubcategoryLift _ _ _
  full := ObjectProperty.instFullFullSubcategoryLift _ _ _

/-- Finite étale algebras over a commutative ring are anti-equivalent to finite étale schemes
over its spectrum. The forward functor is `spec`. -/
noncomputable def finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme :
    (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ ≌ FiniteEtaleScheme (Spec R) :=
  (spec R).asEquivalence

/-- The forward functor of the finite étale anti-equivalence is the spectrum functor. -/
@[simp]
theorem finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme_functor :
    (finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme R).functor = spec R :=
  (rfl)

/-- After forgetting finiteness and étaleness, the inverse coordinate-algebra functor is
naturally isomorphic to Mathlib's global-sections functor `algΓ`. The components identify
coordinate algebras, and `.hom.naturality` identifies pullback on every morphism. -/
noncomputable def finiteEtaleCommAlgCatOpEquivFiniteEtaleSchemeInverseCompInclusionIso :
    (finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme R).inverse ⋙ (CommAlgCat.finiteEtale R).ι.op ≅
      (finiteEtaleSchemeProperty (Spec R)).ι ⋙ algΓ R :=
  Iso.inverseCompIso (G := finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme R)
    ((Functor.rightUnitor _).symm ≪≫
      Functor.isoWhiskerLeft _ (asIso (algΓAlgSpecAdjunction R).counit).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        ((finiteEtaleSchemeProperty (Spec R)).liftCompιIso _ _).symm (algΓ R) ≪≫
      Functor.associator _ _ _)

/-- Over a separably closed field, finite étale schemes are equivalent to finite sets.
The inverse constructs the spectrum of the algebra of functions on the finite set. -/
noncomputable def equivOfIsSepClosed (K : Type u) [Field K] [IsSepClosed K] :
    FiniteEtaleScheme (Spec (.of K)) ≌ FintypeCat.{u} :=
  (finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme (.of K)).symm.trans
    (CommAlgCat.FiniteEtale.equivOfIsSepClosed K)

/-- The finite-set classification takes the finite prime spectrum of the coordinate algebra.
Its object and map computations are those of Mathlib's `finiteSpec`; the coordinate algebra
and its pullback are identified with global sections by
`finiteEtaleCommAlgCatOpEquivFiniteEtaleSchemeInverseCompInclusionIso`. -/
@[simp]
theorem equivOfIsSepClosed_functor (K : Type u) [Field K] [IsSepClosed K] :
    (equivOfIsSepClosed K).functor =
      (finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme (.of K)).inverse ⋙
        CommAlgCat.FiniteEtale.finiteSpec K := by
  simp only [equivOfIsSepClosed, Equivalence.trans_functor, Equivalence.symm_functor,
    CommAlgCat.FiniteEtale.equivOfIsSepClosed_functor]

/-- The inverse finite-set classification forms the function algebra and then takes its
spectrum. Mathlib's inverse object and map lemmas compute the function-algebra functor. -/
@[simp]
theorem equivOfIsSepClosed_inverse (K : Type u) [Field K] [IsSepClosed K] :
    (equivOfIsSepClosed K).inverse =
      (CommAlgCat.FiniteEtale.equivOfIsSepClosed K).inverse ⋙ spec (.of K) := by
  simp only [equivOfIsSepClosed, Equivalence.trans_inverse, Equivalence.symm_inverse,
    finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme_functor]

/-- The finite-set classification is naturally isomorphic to the geometric fibre of the
coordinate algebra: algebra homomorphisms to the separably closed base field, with
precomposition as the action on morphisms. -/
noncomputable def equivOfIsSepClosedFunctorIsoFiber (K : Type u) [Field K] [IsSepClosed K] :
    (equivOfIsSepClosed K).functor ≅
      (finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme (.of K)).inverse ⋙
        CommAlgCat.FiniteEtale.fiber K K :=
  eqToIso (equivOfIsSepClosed_functor K) ≪≫
    Functor.isoWhiskerLeft _ (CommAlgCat.FiniteEtale.fiberIsoFiniteSpec K).symm

end FiniteEtaleScheme

end TauCeti
