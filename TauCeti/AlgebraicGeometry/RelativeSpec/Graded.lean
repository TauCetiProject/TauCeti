/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.DirectSum
public import TauCeti.AlgebraicGeometry.RelativeSpec.Equivalence
public import TauCeti.CategoryTheory.Limits.Shapes.Pullback.Categorical.Equivalence

/-!
# Graded relative Spec

A grading of an affine scheme `p : V ⟶ X` over `X` is a nonnegatively graded quasicoherent
algebra `A = (Aₙ)ₙ` on `X` together with an isomorphism of quasicoherent algebras
`p_* 𝒪_V ≅ ⨁ₙ Aₙ`. Affine schemes over `X` equipped with a grading form the category
`GradedAffineSchemeOver X`: the categorical pullback of the coordinate-algebra functor
`affineFunctions X` along the direct-sum functor `A ↦ ⨁ₙ Aₙ`. A morphism consists of a morphism
of schemes over `X` and a graded algebra morphism between the gradings, in the opposite
direction, which induces the pullback of regular functions along the morphism of schemes.

Since relative Spec is an anti-equivalence between quasicoherent algebras and affine schemes over
`X`, relative Spec with the grading retained,
`A ↦ (Spec_X (⨁ₙ Aₙ), A, p_* 𝒪 ≅ ⨁ₙ Aₙ)`, is an anti-equivalence
`gradedRelativeSpecEquiv X : (GradedQuasicoherentAlgebra X)ᵒᵖ ≌ GradedAffineSchemeOver X`. Its
inverse reads off the grading, and forgetting the grading recovers relative Spec of the
direct-sum algebra. This is the setting for linear schemes such as `Spec_X (Sym F)`, graded by
the symmetric powers of a quasicoherent sheaf `F`.

## Main declarations

* `TauCeti.AlgebraicGeometry.GradedAffineSchemeOver`: affine schemes over `X` with a grading of
  their function algebra;
* `TauCeti.AlgebraicGeometry.gradedRelativeSpec`: relative Spec of the direct-sum algebra, with
  its grading;
* `TauCeti.AlgebraicGeometry.gradedRelativeSpecEquiv`: graded relative Spec is an
  anti-equivalence, with identity unit and with counit given on underlying schemes by relative
  Spec of the grading isomorphism followed by the relative-Spec counit;
* `TauCeti.AlgebraicGeometry.gradedRelativeSpecForgetIso`: forgetting the grading of
  `gradedRelativeSpec X` gives relative Spec of the direct-sum algebra.

## References

* The Stacks Project, [Tag 01LQ](https://stacks.math.columbia.edu/tag/01LQ) (relative spectrum as
  a functor).
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique II*, §1.3.
-/

public section

open CategoryTheory Limits CategoricalPullback Opposite _root_.AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable (X : Scheme.{u})

/-- Affine schemes over `X` with a nonnegative grading of their function algebra: triples of an
affine scheme `p : V ⟶ X` over `X`, a graded quasicoherent algebra `A = (Aₙ)ₙ`, and an
isomorphism `p_* 𝒪_V ≅ ⨁ₙ Aₙ` of quasicoherent algebras. A morphism is a morphism of schemes over
`X` together with a graded algebra morphism of the gradings, in the opposite direction, such that
the two agree as morphisms of function algebras. -/
abbrev GradedAffineSchemeOver : Type (u + 1) :=
  CategoricalPullback (affineFunctions X)
    (GradedQuasicoherentAlgebra.toQuasicoherentAlgebra (X := X)).op

/-- Graded relative Spec is an anti-equivalence between graded quasicoherent algebras and graded
affine schemes over `X`. The functor sends `A` to the relative spectrum of `⨁ₙ Aₙ`, graded through
the relative-Spec unit `p_* 𝒪 ≅ ⨁ₙ Aₙ`, and the inverse reads off the grading. The unit is the
identity, and the counit is, on underlying schemes, relative Spec of the grading isomorphism
followed by the relative-Spec counit. -/
-- Exposed, like `sndEquiv`, since the characteristic equation of the structural isomorphism is
-- typed through the components of the image objects.
@[expose]
def gradedRelativeSpecEquiv :
    (GradedQuasicoherentAlgebra X)ᵒᵖ ≌ GradedAffineSchemeOver X :=
  sndEquiv
    { functor := affineFunctions X
      inverse := relativeSpec X
      unitIso := (relativeSpecCounit X).symm
      counitIso := (relativeSpecUnit X).symm
      functor_unitIso_comp V := by
        simp [← affineFunctions_map_relativeSpecCounit_hom_app, ← Functor.map_comp] }
    GradedQuasicoherentAlgebra.toQuasicoherentAlgebra.op

/-- Relative Spec of the direct-sum algebra of a graded quasicoherent algebra, with its grading
retained. -/
@[expose]
def gradedRelativeSpec : (GradedQuasicoherentAlgebra X)ᵒᵖ ⥤ GradedAffineSchemeOver X :=
  (gradedRelativeSpecEquiv X).functor

variable {X}

/-- The functor of the graded relative-Spec anti-equivalence is graded relative Spec. -/
@[simp]
lemma gradedRelativeSpecEquiv_functor :
    (gradedRelativeSpecEquiv X).functor = gradedRelativeSpec X :=
  rfl

/-- The inverse of the graded relative-Spec anti-equivalence reads off the grading. -/
@[simp]
lemma gradedRelativeSpecEquiv_inverse :
    (gradedRelativeSpecEquiv X).inverse =
      π₂ (affineFunctions X) GradedQuasicoherentAlgebra.toQuasicoherentAlgebra.op :=
  rfl

/-- The scheme underlying the graded relative spectrum of `A` is the relative spectrum of the
direct-sum algebra `⨁ₙ Aₙ`. -/
@[simp]
lemma gradedRelativeSpec_obj_fst (A : (GradedQuasicoherentAlgebra X)ᵒᵖ) :
    ((gradedRelativeSpec X).obj A).fst =
      (relativeSpec X).obj (op (GradedQuasicoherentAlgebra.toQuasicoherentAlgebra.obj A.unop)) :=
  rfl

/-- The grading of the graded relative spectrum of `A` is `A`. -/
@[simp]
lemma gradedRelativeSpec_obj_snd (A : (GradedQuasicoherentAlgebra X)ᵒᵖ) :
    ((gradedRelativeSpec X).obj A).snd = A :=
  rfl

/-- The grading of the graded relative spectrum of `A` identifies its function algebra with
`⨁ₙ Aₙ` through the relative-Spec unit. -/
@[simp]
lemma gradedRelativeSpec_obj_iso (A : (GradedQuasicoherentAlgebra X)ᵒᵖ) :
    ((gradedRelativeSpec X).obj A).iso =
      ((relativeSpecUnit X).app
        (op (GradedQuasicoherentAlgebra.toQuasicoherentAlgebra.obj A.unop))).symm :=
  rfl

/-- On underlying schemes, graded relative Spec acts on a graded algebra morphism through
relative Spec of the induced morphism of direct-sum algebras. -/
@[simp]
lemma gradedRelativeSpec_map_fst {A B : (GradedQuasicoherentAlgebra X)ᵒᵖ} (f : A ⟶ B) :
    ((gradedRelativeSpec X).map f).fst =
      (relativeSpec X).map (GradedQuasicoherentAlgebra.toQuasicoherentAlgebra.map f.unop).op :=
  rfl

/-- On gradings, graded relative Spec acts on a graded algebra morphism by that morphism. -/
@[simp]
lemma gradedRelativeSpec_map_snd {A B : (GradedQuasicoherentAlgebra X)ᵒᵖ} (f : A ⟶ B) :
    ((gradedRelativeSpec X).map f).snd = f :=
  rfl

/-- The unit of the graded relative-Spec anti-equivalence is the identity. -/
@[simp]
lemma gradedRelativeSpecEquiv_unitIso_hom_app (A : (GradedQuasicoherentAlgebra X)ᵒᵖ) :
    (gradedRelativeSpecEquiv X).unitIso.hom.app A = 𝟙 A :=
  rfl

/-- The inverse unit of the graded relative-Spec anti-equivalence is the identity. -/
@[simp]
lemma gradedRelativeSpecEquiv_unitIso_inv_app (A : (GradedQuasicoherentAlgebra X)ᵒᵖ) :
    (gradedRelativeSpecEquiv X).unitIso.inv.app A = 𝟙 A :=
  rfl

/-- On underlying schemes, the counit at a graded affine scheme `(V, A, φ)` is relative Spec of
`φ`, followed by the relative-Spec counit `Spec_X (p_* 𝒪_V) ⟶ V`. -/
@[simp]
lemma gradedRelativeSpecEquiv_counitIso_hom_app_fst (V : GradedAffineSchemeOver X) :
    ((gradedRelativeSpecEquiv X).counitIso.hom.app V).fst =
      (relativeSpec X).map V.iso.inv ≫ (relativeSpecCounit X).hom.app V.fst :=
  rfl

/-- On gradings, the counit of the graded relative-Spec anti-equivalence is the identity. -/
@[simp]
lemma gradedRelativeSpecEquiv_counitIso_hom_app_snd (V : GradedAffineSchemeOver X) :
    ((gradedRelativeSpecEquiv X).counitIso.hom.app V).snd = 𝟙 V.snd :=
  rfl

/-- On underlying schemes, the inverse counit at a graded affine scheme `(V, A, φ)` is the
inverse relative-Spec counit `V ⟶ Spec_X (p_* 𝒪_V)`, followed by relative Spec of `φ⁻¹`. -/
@[simp]
lemma gradedRelativeSpecEquiv_counitIso_inv_app_fst (V : GradedAffineSchemeOver X) :
    ((gradedRelativeSpecEquiv X).counitIso.inv.app V).fst =
      (relativeSpecCounit X).inv.app V.fst ≫ (relativeSpec X).map V.iso.hom :=
  rfl

/-- On gradings, the inverse counit of the graded relative-Spec anti-equivalence is the
identity. -/
@[simp]
lemma gradedRelativeSpecEquiv_counitIso_inv_app_snd (V : GradedAffineSchemeOver X) :
    ((gradedRelativeSpecEquiv X).counitIso.inv.app V).snd = 𝟙 V.snd :=
  rfl

variable (X) in
/-- Graded relative Spec is an equivalence, in particular fully faithful and essentially
surjective. -/
instance gradedRelativeSpec_isEquivalence : (gradedRelativeSpec X).IsEquivalence := by
  rw [← gradedRelativeSpecEquiv_functor]
  exact (gradedRelativeSpecEquiv X).isEquivalence_functor

variable (X) in
/-- Forgetting the grading of the graded relative spectrum gives relative Spec of the direct-sum
algebra. -/
def gradedRelativeSpecForgetIso :
    gradedRelativeSpec X ⋙
        π₁ (affineFunctions X) GradedQuasicoherentAlgebra.toQuasicoherentAlgebra.op ≅
      GradedQuasicoherentAlgebra.toQuasicoherentAlgebra.op ⋙ relativeSpec X :=
  Iso.refl _

/-- The comparison `gradedRelativeSpecForgetIso` is the identity on each object. -/
@[simp]
lemma gradedRelativeSpecForgetIso_hom_app (A : (GradedQuasicoherentAlgebra X)ᵒᵖ) :
    (gradedRelativeSpecForgetIso X).hom.app A = 𝟙 _ :=
  (rfl)

/-- The inverse comparison `gradedRelativeSpecForgetIso` is the identity on each object. -/
@[simp]
lemma gradedRelativeSpecForgetIso_inv_app (A : (GradedQuasicoherentAlgebra X)ᵒᵖ) :
    (gradedRelativeSpecForgetIso X).inv.app A = 𝟙 _ :=
  (rfl)

end

end TauCeti.AlgebraicGeometry
