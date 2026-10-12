/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.Basic
public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Torsor

/-!
# Homogeneous quotient projections are torsors

For an affine group `G` and any closed subgroup `N`, the fppf homogeneous quotient
projection has kernel pair `G × N`, with maps `(g, n) ↦ g` and `(g, n) ↦ gn`.
Together with local surjectivity, this says that `G → G/N` is an `N`-torsor.
Normality is unnecessary: the quotient is a sheaf of sets, and need not be a group.

This identifies the fibers needed when realizing a homogeneous quotient as the orbit
of a line with stabilizer `N`. It does not assert representability of that orbit.
The base ring, ambient group, subgroup, and value algebras may all be nonreduced.

The action and product comparisons are those of
`TauCeti.CommHopfAlgCat.pointwiseQuotientTorsorAction` and
`TauCeti.CommHopfAlgCat.fppfQuotientTorsorProductIso`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §5, homogeneous spaces and quotient sheaves.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §14.
-/

public section

open CategoryTheory Opposite
open CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CommHopfAlgCat

open TauCeti TauCeti.CommHopfAlgCat

universe u

variable {R : Type u} [CommRing R]
variable (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H)

private theorem homogeneousQuotientTorsorProjection_app
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ) :
    ((eqToHom ((pointsPresheafGrp_X_eq H).trans
      (pointsGroupPresheaf_ulift_forget_eq_pointsPresheaf_ulift H)) ≫
    homogeneousQuotientPresheafProjection H I).app A) =
    (↾fun g : ULift.{u + 1, u} (HopfAlgebra.points (R := R) (H := H) A.unop.unop) =>
      homogeneousQuotientPresheafMk H I A g.down) := by
  ext g
  -- At each object, the carrier identification is the identity on lifted points;
  -- reduce its transport before using the projection's public application formula.
  change (homogeneousQuotientPresheafProjection H I).app A (ULift.up g.down) =
    homogeneousQuotientPresheafMk H I A g.down
  exact homogeneousQuotientPresheafProjection_app_apply H I A g.down

/-- The coset projection has kernel pair `G × N`, even for a nonnormal subgroup. -/
theorem isPullback_homogeneousQuotientPresheafTorsor :
    IsPullback
      (CartesianMonoidalCategory.fst _ _)
      (pointwiseQuotientTorsorAction H I)
      (eqToHom ((pointsPresheafGrp_X_eq H).trans
        (pointsGroupPresheaf_ulift_forget_eq_pointsPresheaf_ulift H)) ≫
          homogeneousQuotientPresheafProjection H I)
      (eqToHom ((pointsPresheafGrp_X_eq H).trans
        (pointsGroupPresheaf_ulift_forget_eq_pointsPresheaf_ulift H)) ≫
          homogeneousQuotientPresheafProjection H I) := by
  apply IsPullback.of_forall_isPullback_app
  intro A
  rw [homogeneousQuotientTorsorProjection_app]
  rw [Functor.Monoidal.fst_app, pointwiseQuotientTorsorAction_app]
  -- The product in the functor category and the concrete first projection need reduction
  -- before the type-valued pullback criterion can match their domains.
  change IsPullback
    (↾fun p : ULift.{u + 1, u} (HopfAlgebra.points (R := R) (H := H) A.unop.unop) ×
      ULift.{u + 1, u} (HopfAlgebra.points (R := R) (H := quotient H I) A.unop.unop) => p.1)
    (↾fun p => ULift.up.{u + 1, u}
      (p.1.down * quotientPointsHom H I A.unop.unop p.2.down))
    (↾fun g : ULift.{u + 1, u} (HopfAlgebra.points (R := R) (H := H) A.unop.unop) =>
      homogeneousQuotientPresheafMk H I A g.down)
    (↾fun g : ULift.{u + 1, u} (HopfAlgebra.points (R := R) (H := H) A.unop.unop) =>
      homogeneousQuotientPresheafMk H I A g.down)
  rw [CategoryTheory.Limits.Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext p
    simp only [TypeCat.Fun.toFun_apply, types_comp_apply, TypeCat.ofHom_apply]
    rw [← homogeneousQuotientPresheafProjection_app_apply,
      ← homogeneousQuotientPresheafProjection_app_apply]
    apply (homogeneousQuotientPresheafProjection_eq_iff H I A _ _).2
    simpa using quotientPointsHom_mem_quotientPointsSubgroup H I A.unop.unop p.2.down
  · rintro ⟨g, n⟩ ⟨g', n'⟩ ⟨hg, hgn⟩
    -- The concrete function wrappers in `Types.isPullback_iff` have no application lemma.
    change g = g' at hg
    subst g'
    apply Prod.ext
    · rfl
    apply ULift.ext
    apply quotientPointsHom_injective H I A.unop.unop
    exact mul_left_cancel (congrArg ULift.down hgn)
  · intro g g' hgg'
    have hmem := (homogeneousQuotientPresheafProjection_eq_iff H I A _ _).1
      (by simpa only [homogeneousQuotientPresheafProjection_app_apply, TypeCat.ofHom_apply]
        using hgg')
    obtain ⟨n, hn⟩ := hmem
    refine ⟨⟨g, ULift.up n⟩, rfl, ULift.ext ?_⟩
    -- Reduce the concrete action wrapper to multiplication, then use its subgroup witness.
    change g.down * quotientPointsHom H I A.unop.unop n = g'.down
    rw [hn]
    simp

/-- The morphism of fppf sheaves from ambient group points to the homogeneous quotient. -/
noncomputable def fppfHomogeneousQuotientSheafProjection :
    (pointsFppfGroupObject H).X ⟶ fppfHomogeneousQuotient H I :=
  eqToHom (pointsFppfGroupObject_X_eq H) ≫
    (presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).map
      (eqToHom ((pointsPresheafGrp_X_eq H).trans
        (pointsGroupPresheaf_ulift_forget_eq_pointsPresheaf_ulift H)) ≫
          homogeneousQuotientPresheafProjection H I) ≫
    eqToHom (fppfHomogeneousQuotient_eq H I).symm

/-- On ambient points, the sheaf morphism agrees with the original projection to
the sheafification of the coset presheaf. -/
@[reassoc (attr := simp)]
theorem toSheafify_comp_fppfHomogeneousQuotientSheafProjection :
    toSheafify (CommAlgCat.fppfTopology R) (pointsPresheafGrp H).X ≫
        eqToHom (congrArg
          (fun X : Sheaf (CommAlgCat.fppfTopology R) (Type (u + 1)) ↦ X.obj)
          (pointsFppfGroupObject_X_eq H).symm) ≫
          (fppfHomogeneousQuotientSheafProjection H I).hom =
      eqToHom ((pointsPresheafGrp_X_eq H).trans
        (pointsGroupPresheaf_ulift_forget_eq_pointsPresheaf_ulift H)) ≫
          fppfHomogeneousQuotientProjection H I := by
  rw [fppfHomogeneousQuotientProjection_def]
  simp [fppfHomogeneousQuotientSheafProjection, Category.assoc,
    sheafifyMap, ObjectProperty.eqToHom_hom]

/-- The projection to the fppf homogeneous quotient is an epimorphism of sheaves. -/
instance epi_fppfHomogeneousQuotientSheafProjection :
    Epi (fppfHomogeneousQuotientSheafProjection H I) := by
  let _ (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ) :
      Epi ((homogeneousQuotientPresheafProjection H I).app A) :=
    ConcreteCategory.epi_of_surjective _ (homogeneousQuotientPresheafProjection_surjective H I A)
  have : Epi (homogeneousQuotientPresheafProjection H I) := NatTrans.epi_of_epi_app _
  unfold fppfHomogeneousQuotientSheafProjection
  infer_instance

/-- Every section of `G/N` lifts fppf locally to a section of the ambient group sheaf. -/
theorem isLocallySurjective_fppfHomogeneousQuotientSheafProjection :
    Sheaf.IsLocallySurjective (fppfHomogeneousQuotientSheafProjection H I) := by
  rw [Sheaf.isLocallySurjective_iff_epi']
  infer_instance

/-- The homogeneous quotient projection has torsor kernel pair `G × N` in fppf sheaves. -/
theorem isPullback_fppfHomogeneousQuotientTorsor :
    IsPullback
      (CartesianMonoidalCategory.fst _ _)
      (fppfQuotientTorsorAction H I)
      (fppfHomogeneousQuotientSheafProjection H I)
      (fppfHomogeneousQuotientSheafProjection H I) := by
  let F := presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))
  have h := (isPullback_homogeneousQuotientPresheafTorsor H I).map F
  apply h.of_iso (fppfQuotientTorsorProductIso H I).symm
    (eqToIso (pointsFppfGroupObject_X_eq H).symm)
    (eqToIso (pointsFppfGroupObject_X_eq H).symm) (eqToIso (fppfHomogeneousQuotient_eq H I).symm)
  · apply (cancel_epi (fppfQuotientTorsorProductIso H I).hom).1
    simpa only [Category.assoc, Iso.symm_hom, Iso.hom_inv_id_assoc, eqToIso.hom] using
      sheafify_pointwiseQuotientTorsorFst H I
  · apply (cancel_epi (fppfQuotientTorsorProductIso H I).hom).1
    simpa only [Category.assoc, Iso.symm_hom, Iso.hom_inv_id_assoc, eqToIso.hom] using
      sheafify_pointwiseQuotientTorsorAction H I
  · simp [fppfHomogeneousQuotientSheafProjection, F]
  · simp [fppfHomogeneousQuotientSheafProjection, F]

end CommHopfAlgCat
