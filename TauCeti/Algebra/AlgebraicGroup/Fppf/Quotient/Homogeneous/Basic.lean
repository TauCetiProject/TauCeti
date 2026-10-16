/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Fppf.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Naturality
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Fppf homogeneous quotients

For an affine group `G` and a closed subgroup `N`, the fppf homogeneous quotient `G/N`
is the sheafification of the presheaf of left cosets `A ↦ G(A)/N(A)`. No normality is
required. Maps from this sheaf to an fppf sheaf are exactly natural maps from `G`
that are invariant under right multiplication by `N`.

The construction admits nonreduced groups and value algebras, over any commutative base
ring. It supplies the quotient sheaf whose representability as a homogeneous space can
subsequently be proved. Sheafification is essential: a section of `G/N` need only lift
to `G` locally in the fppf topology.

We use Mathlib's left-coset setoid and sheafification adjunction. Values are lifted by
one universe so that type-valued sheafification is available on the affine site.

## References

* J. S. Milne, *Algebraic Groups* (2017), §5, homogeneous spaces and quotient sheaves.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §14.
-/

public section

open CategoryTheory Opposite

namespace CommHopfAlgCat

open TauCeti TauCeti.CommHopfAlgCat

universe u

noncomputable section

variable {R : Type u} [CommRing R] (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H)

/-- The presheaf of left cosets by a closed subgroup, without a normality assumption. -/
def homogeneousQuotientPresheaf : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ ⥤ Type (u + 1) where
  obj A := ULift.{u + 1, u} (HopfAlgebra.points (R := R) (H := H) A.unop.unop ⧸
    quotientPointsSubgroup H I A.unop.unop)
  map {A B} χ := ↾fun q ↦ ULift.up <| Quotient.map'
    (HopfAlgebra.mapPoints (H := H) χ.unop.unop) (fun x y hxy ↦ by
      apply QuotientGroup.leftRel_apply.mpr
      simpa only [map_mul, map_inv] using mapPoints_mem_quotientPointsSubgroup H I
        χ.unop.unop (QuotientGroup.leftRel_apply.mp hxy)) q.down
  map_id A := by
    ext q
    obtain ⟨q⟩ := q
    induction q using Quotient.inductionOn' with | _ g =>
      simp [HopfAlgebra.mapPoints_id]
  map_comp χ ψ := by
    ext q
    obtain ⟨q⟩ := q
    induction q using Quotient.inductionOn' with | _ g =>
      simp [HopfAlgebra.mapPoints_comp]

/-- The left coset represented by a group point. -/
def homogeneousQuotientPresheafMk
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ)
    (g : HopfAlgebra.points (R := R) (H := H) A.unop.unop) :
    (homogeneousQuotientPresheaf H I).obj A :=
  ULift.up (QuotientGroup.mk g)

/-- To prove a property of a coset section, it suffices to prove it for representatives. -/
@[elab_as_elim]
theorem homogeneousQuotientPresheaf_induction_on
    {A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ}
    (q : (homogeneousQuotientPresheaf H I).obj A)
    {P : (homogeneousQuotientPresheaf H I).obj A → Prop}
    (h : ∀ g, P (homogeneousQuotientPresheafMk H I A g)) : P q := by
  obtain ⟨q⟩ := q
  induction q using Quotient.inductionOn' with | _ g => exact h g

/-- Mapping a left coset maps its representative by the functor of points. -/
@[simp]
theorem homogeneousQuotientPresheaf_map_mk
    {A B : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ} (χ : A ⟶ B)
    (g : HopfAlgebra.points (R := R) (H := H) A.unop.unop) :
    (homogeneousQuotientPresheaf H I).map χ (homogeneousQuotientPresheafMk H I A g) =
      homogeneousQuotientPresheafMk H I B
        (HopfAlgebra.mapPoints (H := H) χ.unop.unop g) :=
  (rfl)

/-- The natural projection from affine-group points to left cosets. -/
def homogeneousQuotientPresheafProjection :
    HopfAlgebra.pointsPresheaf H ⋙ uliftFunctor.{u + 1, u} ⟶
      homogeneousQuotientPresheaf H I where
  app _ := ↾fun g ↦ ULift.up (QuotientGroup.mk g.down)
  naturality {A B} χ := by ext g; rfl

/-- The projection sends a point to its left coset. -/
@[simp]
theorem homogeneousQuotientPresheafProjection_app_apply
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ)
    (g : HopfAlgebra.points (R := R) (H := H) A.unop.unop) :
    dsimp% (homogeneousQuotientPresheafProjection H I).app A (ULift.up g) =
      homogeneousQuotientPresheafMk H I A g :=
  (rfl)

/-- Every section of the coset presheaf is represented by an ambient group point. -/
theorem homogeneousQuotientPresheafProjection_surjective
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ) :
    Function.Surjective ((homogeneousQuotientPresheafProjection H I).app A) := by
  intro q
  induction q using homogeneousQuotientPresheaf_induction_on H I with
  | h g => exact ⟨ULift.up g, homogeneousQuotientPresheafProjection_app_apply H I A g⟩

/-- Two points have the same coset exactly when their difference lies in the closed subgroup. -/
theorem homogeneousQuotientPresheafProjection_eq_iff
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ)
    (g g' : HopfAlgebra.points (R := R) (H := H) A.unop.unop) :
    dsimp% (homogeneousQuotientPresheafProjection H I).app A (ULift.up g) =
        (homogeneousQuotientPresheafProjection H I).app A (ULift.up g') ↔
      g⁻¹ * g' ∈ quotientPointsSubgroup H I A.unop.unop := by
  rw [homogeneousQuotientPresheafProjection_app_apply,
    homogeneousQuotientPresheafProjection_app_apply]
  exact ULift.up_inj.trans QuotientGroup.eq

/-- A natural map from group points which is invariant under the subgroup descends to cosets. -/
def homogeneousQuotientPresheafLift
    {F : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ ⥤ Type (u + 1)}
    (f : HopfAlgebra.pointsPresheaf H ⋙ uliftFunctor.{u + 1, u} ⟶ F)
    (hf : ∀ (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ)
      (g : HopfAlgebra.points (R := R) (H := H) A.unop.unop)
      (n : quotientPointsSubgroup H I A.unop.unop),
      f.app A (ULift.up (g * n.val)) = f.app A (ULift.up g)) :
    homogeneousQuotientPresheaf H I ⟶ F where
  app A := ↾fun q ↦ Quotient.liftOn' q.down (fun g ↦ f.app A (ULift.up g))
    (fun g g' hgg' ↦ by
      have h := hf A g ⟨g⁻¹ * g', QuotientGroup.leftRel_apply.mp hgg'⟩
      simpa only [mul_inv_cancel_left] using h.symm)
  naturality {A B} χ := by
    ext q
    obtain ⟨q⟩ := q
    induction q using Quotient.inductionOn' with | _ g =>
      exact congrArg (fun t ↦ t (ULift.up g)) (f.naturality χ)

/-- The descended map has its prescribed value on every representative. -/
@[simp]
theorem homogeneousQuotientPresheafLift_app_mk
    {F : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ ⥤ Type (u + 1)}
    (f : HopfAlgebra.pointsPresheaf H ⋙ uliftFunctor.{u + 1, u} ⟶ F)
    (hf : ∀ (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ)
      (g : HopfAlgebra.points (R := R) (H := H) A.unop.unop)
      (n : quotientPointsSubgroup H I A.unop.unop),
      f.app A (ULift.up (g * n.val)) = f.app A (ULift.up g))
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ)
    (g : HopfAlgebra.points (R := R) (H := H) A.unop.unop) :
    (homogeneousQuotientPresheafLift H I f hf).app A
        (homogeneousQuotientPresheafMk H I A g) =
      f.app A (ULift.up g) :=
  (rfl)

/-- A map from the coset presheaf is determined by its values on group points. -/
theorem homogeneousQuotientPresheaf_hom_ext
    {F : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ ⥤ Type (u + 1)}
    {f g : homogeneousQuotientPresheaf H I ⟶ F}
    (h : homogeneousQuotientPresheafProjection H I ≫ f =
      homogeneousQuotientPresheafProjection H I ≫ g) : f = g := by
  ext A q
  obtain ⟨q⟩ := q
  induction q using Quotient.inductionOn' with | _ x =>
    exact congrArg (fun t ↦ t.app A (ULift.up x)) h

/-- Maps out of the coset presheaf are precisely natural subgroup-invariant maps out of `G`. -/
def homogeneousQuotientPresheafHomEquiv
    (F : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ ⥤ Type (u + 1)) :
    (homogeneousQuotientPresheaf H I ⟶ F) ≃
      {f : HopfAlgebra.pointsPresheaf H ⋙ uliftFunctor.{u + 1, u} ⟶ F //
        ∀ (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ)
          (g : HopfAlgebra.points (R := R) (H := H) A.unop.unop)
          (n : quotientPointsSubgroup H I A.unop.unop),
          f.app A (ULift.up (g * n.val)) = f.app A (ULift.up g)} where
  toFun f := ⟨homogeneousQuotientPresheafProjection H I ≫ f, fun A g n ↦ by
    have heq : (QuotientGroup.mk (g * n.val) :
        HopfAlgebra.points (R := R) (H := H) A.unop.unop ⧸
          quotientPointsSubgroup H I A.unop.unop) = QuotientGroup.mk g := by
      apply QuotientGroup.eq.mpr
      simp
    exact congrArg (fun q ↦ f.app A (ULift.up q)) heq⟩
  invFun f := homogeneousQuotientPresheafLift H I f.val f.property
  left_inv f := by
    apply homogeneousQuotientPresheaf_hom_ext
    ext A g
    obtain ⟨g⟩ := g
    rfl
  right_inv f := by
    apply Subtype.ext
    ext A g
    obtain ⟨g⟩ := g
    rfl

/-- The presheaf universal property restricts a map along the coset projection. -/
@[simp]
theorem homogeneousQuotientPresheafHomEquiv_apply
    (F : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ ⥤ Type (u + 1))
    (f : homogeneousQuotientPresheaf H I ⟶ F) :
    (homogeneousQuotientPresheafHomEquiv H I F f).val =
      homogeneousQuotientPresheafProjection H I ≫ f :=
  (rfl)

/-- The fppf homogeneous quotient by the closed subgroup cut out by `I`.
Normality and representability are not required for this construction. -/
def fppfHomogeneousQuotient : Sheaf (CommAlgCat.fppfTopology R) (Type (u + 1)) :=
  (presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).obj
    (homogeneousQuotientPresheaf H I)

/-- The homogeneous quotient is obtained by applying the fppf sheafification functor
to the coset presheaf. -/
theorem fppfHomogeneousQuotient_eq :
    fppfHomogeneousQuotient H I =
      (presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).obj
        (homogeneousQuotientPresheaf H I) :=
  (rfl)

/-- The quotient's underlying presheaf is the sheafification of the coset presheaf. -/
@[simp]
theorem fppfHomogeneousQuotient_obj :
    (fppfHomogeneousQuotient H I).obj =
      sheafify (CommAlgCat.fppfTopology R) (homogeneousQuotientPresheaf H I) :=
  (rfl)

/-- The canonical map from affine-group points to the fppf homogeneous quotient. -/
def fppfHomogeneousQuotientProjection :
    HopfAlgebra.pointsPresheaf H ⋙ uliftFunctor.{u + 1, u} ⟶
      (fppfHomogeneousQuotient H I).obj :=
  homogeneousQuotientPresheafProjection H I ≫
    toSheafify (CommAlgCat.fppfTopology R) (homogeneousQuotientPresheaf H I)

/-- The projection to the homogeneous quotient is the coset projection followed
by the unit of fppf sheafification. -/
theorem fppfHomogeneousQuotientProjection_def :
    fppfHomogeneousQuotientProjection H I =
      homogeneousQuotientPresheafProjection H I ≫
        toSheafify (CommAlgCat.fppfTopology R) (homogeneousQuotientPresheaf H I) ≫
          eqToHom (fppfHomogeneousQuotient_obj H I).symm :=
  (rfl)

/-- The quotient projection sends a point to the sheafification of its left coset. -/
@[simp]
theorem fppfHomogeneousQuotientProjection_app_apply
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ)
    (g : HopfAlgebra.points (R := R) (H := H) A.unop.unop) :
    dsimp% ((fppfHomogeneousQuotientProjection H I).app A ≫
      eqToHom (congrArg (fun P ↦ P.obj A) (fppfHomogeneousQuotient_obj H I)))
        (ULift.up g) =
      (toSheafify (CommAlgCat.fppfTopology R) (homogeneousQuotientPresheaf H I)).app A
        (homogeneousQuotientPresheafMk H I A g) :=
  (rfl)

/-- Every section of the homogeneous quotient lifts fppf locally to a group point. -/
instance fppfHomogeneousQuotientProjection_isLocallySurjective :
    Presheaf.IsLocallySurjective (CommAlgCat.fppfTopology R)
      (fppfHomogeneousQuotientProjection H I) := by
  have : Presheaf.IsLocallySurjective (CommAlgCat.fppfTopology R)
      (homogeneousQuotientPresheafProjection H I) := by
    apply Presheaf.isLocallySurjective_of_surjective
    exact homogeneousQuotientPresheafProjection_surjective H I
  unfold fppfHomogeneousQuotientProjection
  have := Presheaf.isLocallySurjective_toSheafify'
    (CommAlgCat.fppfTopology R) (homogeneousQuotientPresheaf H I)
  exact Presheaf.isLocallySurjective_comp (CommAlgCat.fppfTopology R)
    (homogeneousQuotientPresheafProjection H I)
    (toSheafify (CommAlgCat.fppfTopology R) (homogeneousQuotientPresheaf H I))

/-- Maps from `G/N` to any fppf sheaf are exactly natural maps from `G` invariant under
right multiplication by the closed subgroup `N`, over all value algebras. -/
def fppfHomogeneousQuotientHomEquiv
    (F : Sheaf (CommAlgCat.fppfTopology R) (Type (u + 1))) :
    (fppfHomogeneousQuotient H I ⟶ F) ≃
      {f : HopfAlgebra.pointsPresheaf H ⋙ uliftFunctor.{u + 1, u} ⟶ F.obj //
        ∀ (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ)
          (g : HopfAlgebra.points (R := R) (H := H) A.unop.unop)
          (n : quotientPointsSubgroup H I A.unop.unop),
          f.app A (ULift.up (g * n.val)) = f.app A (ULift.up g)} :=
  ((sheafificationAdjunction (CommAlgCat.fppfTopology R) (Type (u + 1))).homEquiv
    (homogeneousQuotientPresheaf H I) F).trans
      (homogeneousQuotientPresheafHomEquiv H I F.obj)

/-- The universal property sends a sheaf morphism to its composite with the quotient projection. -/
@[simp]
theorem fppfHomogeneousQuotientHomEquiv_apply
    (F : Sheaf (CommAlgCat.fppfTopology R) (Type (u + 1)))
    (f : fppfHomogeneousQuotient H I ⟶ F) :
    (fppfHomogeneousQuotientHomEquiv H I F f).val =
      fppfHomogeneousQuotientProjection H I ≫ f.hom := by
  unfold fppfHomogeneousQuotient at f
  -- Reduce the composite equivalence to its two factors; there is no computation lemma
  -- for this composite, and unfolding the presheaf equivalence would hide its API lemma.
  change (homogeneousQuotientPresheafHomEquiv H I F.obj
    ((sheafificationAdjunction (CommAlgCat.fppfTopology R) (Type (u + 1))).homEquiv
      (homogeneousQuotientPresheaf H I) F f)).val = _
  rw [homogeneousQuotientPresheafHomEquiv_apply, Adjunction.homEquiv_unit,
    sheafificationAdjunction_unit_app]
  dsimp only [fppfHomogeneousQuotientProjection, sheafToPresheaf]
  exact (Category.assoc _ _ _).symm

/-- Descending a subgroup-invariant natural map and then restricting along the quotient
projection recovers that map. -/
@[simp]
theorem fppfHomogeneousQuotientHomEquiv_symm_apply
    (F : Sheaf (CommAlgCat.fppfTopology R) (Type (u + 1)))
    (f : HopfAlgebra.pointsPresheaf H ⋙ uliftFunctor.{u + 1, u} ⟶ F.obj)
    (hf : ∀ (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ)
      (g : HopfAlgebra.points (R := R) (H := H) A.unop.unop)
      (n : quotientPointsSubgroup H I A.unop.unop),
      f.app A (ULift.up (g * n.val)) = f.app A (ULift.up g)) :
    fppfHomogeneousQuotientProjection H I ≫
        ((fppfHomogeneousQuotientHomEquiv H I F).symm ⟨f, hf⟩).hom = f := by
  exact (fppfHomogeneousQuotientHomEquiv_apply H I F _).symm.trans
    (congrArg Subtype.val ((fppfHomogeneousQuotientHomEquiv H I F).apply_symm_apply ⟨f, hf⟩))

end

end CommHopfAlgCat
