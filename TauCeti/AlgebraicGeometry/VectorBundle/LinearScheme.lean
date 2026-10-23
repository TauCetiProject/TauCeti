/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.Free
public import TauCeti.AlgebraicGeometry.RelativeSpec.Graded
public import TauCeti.CategoryTheory.Equivalence.Trans

/-!
# Linear schemes over a scheme

A (quasicoherent) linear scheme over a scheme `X` is an affine scheme `p : V ⟶ X` together with
a grading `p_* 𝒪_V ≅ ⨁ₙ Aₙ` of its function algebra by a graded quasicoherent algebra `A` that is
freely generated in degree one, that is `Sym A₁ ≅ A` as graded algebras. Linear schemes form the
full subcategory `QuasicoherentLinearScheme X` of the category `GradedAffineSchemeOver X` of
graded affine schemes over `X`, so their morphisms are morphisms of schemes over `X` that preserve
the gradings.

The basic example is `𝕍(F) = Spec_X (Sym F)` for a quasicoherent sheaf `F` (Stacks Project,
tag 01M1), graded by the symmetric powers of `F`; this is `linearSpec X`. Its degree-one
component recovers `F`, and every linear scheme arises in this way: the functors
`linearSpec X : (QuasicoherentSheaf X)ᵒᵖ ⥤ QuasicoherentLinearScheme X` and
`QuasicoherentLinearScheme.degreeOne X` are quasi-inverse equivalences (`linearSpecEquiv X`).
This is the composite of the equivalence `QCoh(X) ≌ FreeGrQCAlg(X)` given by graded symmetric
algebras and of graded relative Spec restricted to algebras free in degree one
(`freeGradedRelativeSpecEquiv X`).

## Main declarations

* `TauCeti.AlgebraicGeometry.QuasicoherentLinearScheme`: graded affine schemes over `X` whose
  grading is freely generated in degree one;
* `TauCeti.AlgebraicGeometry.freeGradedRelativeSpecEquiv`: graded relative Spec is an
  anti-equivalence between graded quasicoherent algebras freely generated in degree one and
  linear schemes;
* `TauCeti.AlgebraicGeometry.linearSpec`: the linear scheme `Spec_X (Sym F)` of a quasicoherent
  sheaf `F`, contravariant in `F`;
* `TauCeti.AlgebraicGeometry.QuasicoherentLinearScheme.degreeOne`: the degree-one component of
  the grading of a linear scheme;
* `TauCeti.AlgebraicGeometry.linearSpecEquiv`: the anti-equivalence
  `(QuasicoherentSheaf X)ᵒᵖ ≌ QuasicoherentLinearScheme X` with functor `linearSpec X` and inverse
  `QuasicoherentLinearScheme.degreeOne X`, with unit `degreeOneLinearSpecIso` and counit
  `linearSpecDegreeOneIso`.

## References

* The Stacks Project, [Tag 01M1](https://stacks.math.columbia.edu/tag/01M1) (vector bundles).
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique II*, §1.7.
-/

public section

open CategoryTheory Limits CategoricalPullback Opposite _root_.AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable (X : Scheme.{u})

/-- A graded affine scheme over `X` is a linear scheme when its grading is freely generated in
degree one, that is, lies in the essential image of the graded symmetric algebra functor. -/
def isQuasicoherentLinearScheme : ObjectProperty (GradedAffineSchemeOver X) :=
  (gradedSymmetricAlgebra X).essImage.op.inverseImage
    (π₂ (affineFunctions X) GradedQuasicoherentAlgebra.toQuasicoherentAlgebra.op)

variable {X} in
/-- A graded affine scheme over `X` is a linear scheme exactly when its grading lies in the
essential image of the graded symmetric algebra functor. -/
theorem isQuasicoherentLinearScheme_iff_essImage (V : GradedAffineSchemeOver X) :
    isQuasicoherentLinearScheme X V ↔ (gradedSymmetricAlgebra X).essImage V.snd.unop :=
  Iff.rfl

variable {X} in
/-- A graded affine scheme over `X` is a linear scheme exactly when its grading is isomorphic to
the graded symmetric algebra of its degree-one component. -/
theorem isQuasicoherentLinearScheme_iff (V : GradedAffineSchemeOver X) :
    isQuasicoherentLinearScheme X V ↔
      Nonempty ((gradedSymmetricAlgebra X).obj
        (GradedQuasicoherentAlgebra.degreeOne.obj V.snd.unop) ≅ V.snd.unop) :=
  essImage_gradedSymmetricAlgebra_iff V.snd.unop

/-- Being a linear scheme is invariant under isomorphism of graded affine schemes. -/
instance : (isQuasicoherentLinearScheme X).IsClosedUnderIsomorphisms :=
  inferInstanceAs (ObjectProperty.IsClosedUnderIsomorphisms
    ((gradedSymmetricAlgebra X).essImage.op.inverseImage
      (π₂ (affineFunctions X) GradedQuasicoherentAlgebra.toQuasicoherentAlgebra.op)))

/-- The category of (quasicoherent) linear schemes over `X`: affine schemes over `X` with a
grading of their function algebra that is freely generated in degree one. Morphisms are the
morphisms of graded affine schemes over `X`, i.e. morphisms of schemes over `X` preserving the
gradings. -/
abbrev QuasicoherentLinearScheme : Type (u + 1) :=
  (isQuasicoherentLinearScheme X).FullSubcategory

/-- Graded relative Spec, restricted to graded quasicoherent algebras freely generated in degree
one, is an anti-equivalence onto linear schemes over `X`. Its inverse reads off the grading, its
unit is the identity and its counit is that of `gradedRelativeSpecEquiv X`. -/
-- Exposed, like `gradedRelativeSpecEquiv`, so that its functor, inverse, unit and counit are
-- computed by unfolding.
@[expose]
def freeGradedRelativeSpecEquiv :
    (FreeGradedQuasicoherentAlgebra X)ᵒᵖ ≌ QuasicoherentLinearScheme X where
  functor := (isQuasicoherentLinearScheme X).lift
    ((gradedSymmetricAlgebra X).essImage.ι.op ⋙ gradedRelativeSpec X)
    fun A ↦ (isQuasicoherentLinearScheme_iff_essImage _).2 A.unop.property
  inverse := ((gradedSymmetricAlgebra X).essImage.lift
    ((isQuasicoherentLinearScheme X).ι ⋙ (gradedRelativeSpecEquiv X).inverse).leftOp
    fun V ↦ (isQuasicoherentLinearScheme_iff_essImage _).1 V.unop.property).rightOp
  unitIso := NatIso.ofComponents fun A ↦ Iso.refl A
  counitIso := NatIso.ofComponents
    (fun V ↦ (isQuasicoherentLinearScheme X).isoMk
      ((gradedRelativeSpecEquiv X).counitIso.app V.obj))
    fun f ↦ ObjectProperty.hom_ext _ ((gradedRelativeSpecEquiv X).counitIso.hom.naturality f.hom)
  functor_unitIso_comp A := ObjectProperty.hom_ext _
    ((gradedRelativeSpecEquiv X).functor_unitIso_comp (op A.unop.obj))

variable {X}

/-- The graded affine scheme underlying the linear scheme `freeGradedRelativeSpecEquiv X` assigns
to `A` is the graded relative spectrum of `A`. -/
@[simp]
theorem freeGradedRelativeSpecEquiv_functor_obj_obj (A : (FreeGradedQuasicoherentAlgebra X)ᵒᵖ) :
    ((freeGradedRelativeSpecEquiv X).functor.obj A).obj =
      (gradedRelativeSpec X).obj (op A.unop.obj) :=
  (rfl)

/-- On morphisms, the functor of `freeGradedRelativeSpecEquiv X` is graded relative Spec. -/
@[simp]
theorem freeGradedRelativeSpecEquiv_functor_map_hom {A B : (FreeGradedQuasicoherentAlgebra X)ᵒᵖ}
    (f : A ⟶ B) :
    ((freeGradedRelativeSpecEquiv X).functor.map f).hom =
      (gradedRelativeSpec X).map f.unop.hom.op :=
  (rfl)

/-- The inverse of `freeGradedRelativeSpecEquiv X` reads off the grading of a linear scheme. -/
@[simp]
theorem freeGradedRelativeSpecEquiv_inverse_obj (V : QuasicoherentLinearScheme X) :
    (freeGradedRelativeSpecEquiv X).inverse.obj V =
      op ⟨V.obj.snd.unop, (isQuasicoherentLinearScheme_iff_essImage _).1 V.property⟩ :=
  (rfl)

/-- On morphisms, the inverse of `freeGradedRelativeSpecEquiv X` is the morphism of gradings. -/
@[simp]
theorem freeGradedRelativeSpecEquiv_inverse_map_unop_hom {V W : QuasicoherentLinearScheme X}
    (f : V ⟶ W) :
    ((freeGradedRelativeSpecEquiv X).inverse.map f).unop.hom = f.hom.snd.unop :=
  (rfl)

/-- The unit of `freeGradedRelativeSpecEquiv X` is the identity. -/
@[simp]
theorem freeGradedRelativeSpecEquiv_unit_app (A : (FreeGradedQuasicoherentAlgebra X)ᵒᵖ) :
    (freeGradedRelativeSpecEquiv X).unit.app A = 𝟙 A :=
  (rfl)

/-- The counit of `freeGradedRelativeSpecEquiv X` is the counit of `gradedRelativeSpecEquiv X` on
the underlying graded affine scheme. -/
@[simp]
theorem freeGradedRelativeSpecEquiv_counit_app_hom (V : QuasicoherentLinearScheme X) :
    ((freeGradedRelativeSpecEquiv X).counit.app V).hom =
      (gradedRelativeSpecEquiv X).counitIso.hom.app V.obj :=
  (rfl)

variable (X)

/-- The linear scheme `𝕍(F) = Spec_X (Sym F)` of a quasicoherent sheaf `F`: the relative spectrum
of the graded symmetric algebra of `F`, graded by the symmetric powers of `F`. It is contravariant
in `F`. -/
-- Exposed, like `gradedRelativeSpec`, so that its objects and morphisms are computed by unfolding.
@[expose]
def linearSpec : (QuasicoherentSheaf X)ᵒᵖ ⥤ QuasicoherentLinearScheme X :=
  ObjectProperty.lift _ ((gradedSymmetricAlgebra X).op ⋙ gradedRelativeSpec X)
    fun F ↦ (isQuasicoherentLinearScheme_iff_essImage _).2
      ((gradedSymmetricAlgebra X).obj_mem_essImage F.unop)

namespace QuasicoherentLinearScheme

/-- The degree-one component `A₁` of the grading of a linear scheme, contravariant in the linear
scheme. -/
-- Exposed, like `linearSpec`, so that its objects and morphisms are computed by unfolding.
@[expose]
def degreeOne : QuasicoherentLinearScheme X ⥤ (QuasicoherentSheaf X)ᵒᵖ :=
  (isQuasicoherentLinearScheme X).ι ⋙
    π₂ (affineFunctions X) GradedQuasicoherentAlgebra.toQuasicoherentAlgebra.op ⋙
      GradedQuasicoherentAlgebra.degreeOne.op

variable {X}

/-- The degree-one component of a linear scheme is the degree-one component of its grading. -/
@[simp]
theorem degreeOne_obj (V : QuasicoherentLinearScheme X) :
    (degreeOne X).obj V = op (GradedQuasicoherentAlgebra.degreeOne.obj V.obj.snd.unop) :=
  (rfl)

/-- A morphism of linear schemes acts on degree-one components through the degree-one component
of its graded algebra morphism. -/
@[simp]
theorem degreeOne_map {V W : QuasicoherentLinearScheme X} (f : V ⟶ W) :
    (degreeOne X).map f = (GradedQuasicoherentAlgebra.degreeOne.map f.hom.snd.unop).op :=
  (rfl)

end QuasicoherentLinearScheme

variable {X}

/-- The graded affine scheme underlying `linearSpec X` at `F` is the graded relative spectrum of
the graded symmetric algebra of `F`. -/
@[simp]
theorem linearSpec_obj_obj (F : (QuasicoherentSheaf X)ᵒᵖ) :
    ((linearSpec X).obj F).obj =
      (gradedRelativeSpec X).obj (op ((gradedSymmetricAlgebra X).obj F.unop)) :=
  (rfl)

/-- `linearSpec X` acts on a morphism of quasicoherent sheaves through graded relative Spec of the
induced morphism of graded symmetric algebras. -/
@[simp]
theorem linearSpec_map_hom {F G : (QuasicoherentSheaf X)ᵒᵖ} (f : F ⟶ G) :
    ((linearSpec X).map f).hom =
      (gradedRelativeSpec X).map ((gradedSymmetricAlgebra X).map f.unop).op :=
  (rfl)

variable (X) in
/-- Forgetting the grading of `linearSpec X` gives the relative spectrum `Spec_X (⨁ₙ Symⁿ F)` of
the direct-sum algebra of the graded symmetric algebra. -/
def linearSpecForgetIso :
    linearSpec X ⋙ (isQuasicoherentLinearScheme X).ι ⋙
        π₁ (affineFunctions X) GradedQuasicoherentAlgebra.toQuasicoherentAlgebra.op ≅
      (gradedSymmetricAlgebra X ⋙ GradedQuasicoherentAlgebra.toQuasicoherentAlgebra).op ⋙
        relativeSpec X :=
  Iso.refl _

/-- The comparison `linearSpecForgetIso` is the identity on each object. -/
@[simp]
theorem linearSpecForgetIso_hom_app (F : (QuasicoherentSheaf X)ᵒᵖ) :
    (linearSpecForgetIso X).hom.app F = 𝟙 _ :=
  (rfl)

/-- The inverse comparison `linearSpecForgetIso` is the identity on each object. -/
@[simp]
theorem linearSpecForgetIso_inv_app (F : (QuasicoherentSheaf X)ᵒᵖ) :
    (linearSpecForgetIso X).inv.app F = 𝟙 _ :=
  (rfl)

/-- The degree-one component of `linearSpec X` at `F` recovers `F`: the identification
`Sym¹ F ≅ F`. -/
def degreeOneLinearSpecIso (F : (QuasicoherentSheaf X)ᵒᵖ) :
    (QuasicoherentLinearScheme.degreeOne X).obj ((linearSpec X).obj F) ≅ F :=
  ((gradedSymmetricAlgebraDegreeOneIso X).app F.unop).op.symm

/-- `degreeOneLinearSpecIso F` is the opposite of the inverse of `Sym¹ F ≅ F`. -/
@[simp]
theorem degreeOneLinearSpecIso_hom (F : (QuasicoherentSheaf X)ᵒᵖ) :
    (degreeOneLinearSpecIso F).hom = ((gradedSymmetricAlgebraDegreeOneIso X).inv.app F.unop).op :=
  (rfl)

/-- The inverse of `degreeOneLinearSpecIso F` is the opposite of `Sym¹ F ≅ F`. -/
@[simp]
theorem degreeOneLinearSpecIso_inv (F : (QuasicoherentSheaf X)ᵒᵖ) :
    (degreeOneLinearSpecIso F).inv = ((gradedSymmetricAlgebraDegreeOneIso X).hom.app F.unop).op :=
  (rfl)

/-- Every linear scheme `V`, graded by `A`, is the linear scheme of its degree-one component: the
isomorphism `𝕍(A₁) = Spec_X (Sym A₁) ≅ V` given by graded relative Spec of the graded algebra
isomorphism `Sym A₁ ≅ A`, followed by the counit of `gradedRelativeSpecEquiv X`. -/
def linearSpecDegreeOneIso (V : QuasicoherentLinearScheme X) :
    (linearSpec X).obj ((QuasicoherentLinearScheme.degreeOne X).obj V) ≅ V :=
  (isQuasicoherentLinearScheme X).isoMk <|
    (gradedRelativeSpec X).mapIso ((gradedSymmetricAlgebra X).essImage.ι.mapIso
        ((gradedSymmetricAlgebraEquiv X).counitIso.app
          ⟨V.obj.snd.unop, (isQuasicoherentLinearScheme_iff_essImage _).1 V.property⟩)).op.symm ≪≫
      (gradedRelativeSpecEquiv X).counitIso.app V.obj

/-- On underlying graded affine schemes, `linearSpecDegreeOneIso V` is graded relative Spec of
`Sym A₁ ≅ A`, followed by the counit of `gradedRelativeSpecEquiv X`. -/
@[simp]
theorem linearSpecDegreeOneIso_hom_hom (V : QuasicoherentLinearScheme X) :
    (linearSpecDegreeOneIso V).hom.hom =
      (gradedRelativeSpec X).map ((gradedSymmetricAlgebraEquiv X).counitIso.inv.app
          ⟨V.obj.snd.unop, (isQuasicoherentLinearScheme_iff_essImage _).1 V.property⟩).hom.op ≫
        (gradedRelativeSpecEquiv X).counitIso.hom.app V.obj :=
  (rfl)

variable (X) in
/-- The anti-equivalence `(QuasicoherentSheaf X)ᵒᵖ ≌ QuasicoherentLinearScheme X`: `linearSpec X`
and the degree-one functor are quasi-inverse, with unit the inverse of `degreeOneLinearSpecIso`
and counit `linearSpecDegreeOneIso`. It is the composite of the graded symmetric-algebra
equivalence `QCoh(X) ≌ FreeGrQCAlg(X)` and of `freeGradedRelativeSpecEquiv X`. -/
-- Exposed so that the statements of the unit and counit lemmas below, which identify the functor
-- and inverse with `linearSpec X` and the degree-one functor, typecheck by unfolding.
@[expose]
def linearSpecEquiv : (QuasicoherentSheaf X)ᵒᵖ ≌ QuasicoherentLinearScheme X :=
  (gradedSymmetricAlgebraEquiv X).op.trans (freeGradedRelativeSpecEquiv X)

variable (X) in
/-- The forward functor of `linearSpecEquiv X` is `linearSpec X`. -/
@[simp]
theorem linearSpecEquiv_functor : (linearSpecEquiv X).functor = linearSpec X :=
  (rfl)

variable (X) in
/-- The inverse functor of `linearSpecEquiv X` is the degree-one functor. -/
@[simp]
theorem linearSpecEquiv_inverse :
    (linearSpecEquiv X).inverse = QuasicoherentLinearScheme.degreeOne X :=
  (rfl)

/-- The unit of `linearSpecEquiv X` at `F` is the inverse of `degreeOneLinearSpecIso F`. -/
@[simp]
theorem linearSpecEquiv_unit_app (F : (QuasicoherentSheaf X)ᵒᵖ) :
    (linearSpecEquiv X).unit.app F = (degreeOneLinearSpecIso F).inv := by
  refine (Equivalence.trans_unit_app _ _ F).trans ?_
  rw [freeGradedRelativeSpecEquiv_unit_app]
  -- The identity produced by the unit of `freeGradedRelativeSpecEquiv X` is typed at an object
  -- that is only definitionally equal to the source of the morphism it is mapped along, so
  -- `Functor.map_id` matches only up to unfolding.
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  -- The unit of the opposite of `gradedSymmetricAlgebraEquiv X` is, by definition of
  -- `Equivalence.op` and `NatIso.op`, the opposite of the inverse of its unit `Sym¹ F ≅ F`.
  rfl

/-- The counit of `linearSpecEquiv X` at `V` is `linearSpecDegreeOneIso V`. -/
@[simp]
theorem linearSpecEquiv_counit_app (V : QuasicoherentLinearScheme X) :
    (linearSpecEquiv X).counit.app V = (linearSpecDegreeOneIso V).hom := by
  refine (Equivalence.trans_counit_app _ _ V).trans (ObjectProperty.hom_ext _ ?_)
  -- By definition of `Equivalence.op`, `NatIso.op` and `ObjectProperty.lift`, both sides apply
  -- graded relative Spec to the inverse counit of `gradedSymmetricAlgebraEquiv X`.
  rfl

variable (X) in
/-- `linearSpec X` is an equivalence, in particular fully faithful and essentially surjective. -/
instance linearSpec_isEquivalence : (linearSpec X).IsEquivalence :=
  (linearSpecEquiv X).isEquivalence_functor

variable (X) in
/-- The degree-one functor of linear schemes is an equivalence. -/
instance QuasicoherentLinearScheme.degreeOne_isEquivalence :
    (QuasicoherentLinearScheme.degreeOne X).IsEquivalence :=
  (linearSpecEquiv X).isEquivalence_inverse

end

end TauCeti.AlgebraicGeometry
