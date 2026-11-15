/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity
-/
module

public import TauCeti.Algebra.Category.CommAlgCat.PointsSheaf
public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.Conjugation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import TauCeti.AlgebraicGeometry.AffineGroupScheme.HopfSpec

/-!
# Schemes representing fppf homogeneous quotients

Let `G` be an affine group over a commutative ring `R` with coordinate Hopf algebra `H`, and let
`N` be the closed subgroup cut out by a Hopf ideal `I`. A scheme `X` over `Spec R` represents the
fppf homogeneous quotient `G / N` when there is an isomorphism of affine fppf sheaves
`e : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X`.

Using the full faithfulness of `TauCeti.CommAlgCat.pointsSheafFunctor`, this file develops the
universal property and functoriality of representing schemes without requiring smoothness,
reducedness, normality, or finite-type hypotheses:

* `CommHopfAlgCat.pointsPresheafToPointsSheafEquiv`: Yoneda equivalence between morphisms
  `Spec H ⟶ X` over `Spec R` and natural maps from `G` into `pointsSheaf X`.
* `CommHopfAlgCat.fppfHomogeneousQuotientSchemeProjection`: the canonical scheme morphism
  `Spec H ⟶ X` over `Spec R` corresponding to `G ⟶ G / N`.
* `CommHopfAlgCat.fppfHomogeneousQuotientSchemeHomEquiv`: **universal property of `G / N` as a
  scheme** (Milne, Proposition 5.22): morphisms `X ⟶ Z` over `Spec R` are equivalent to `N`-right
  invariant morphisms `Spec H ⟶ Z` over `Spec R`.
* `CommHopfAlgCat.fppfHomogeneousQuotientSchemeIso`: uniqueness of a representing scheme up to
  canonical isomorphism over `Spec R`, together with transfer of any isomorphism-invariant
  `MorphismProperty` (in particular `AlgebraicGeometry.IsProper`).
* `CommHopfAlgCat.fppfHomogeneousQuotientSchemeMap`: the canonical scheme morphism `X ⟶ Y` over
  `Spec R` induced by an inclusion of closed subgroups (`J ≤ I`), with identity and composition
  laws.
* `CommHopfAlgCat.fppfHomogeneousQuotientSchemeTranslation`: left-translation automorphisms of `X`
  by `R`-valued points of `G`, commuting with subgroup-induced projections.
* `CommHopfAlgCat.fppfHomogeneousQuotientConjugateRepresentingIso`: transport of a representing
  scheme from `G / N` to `G / (g N g⁻¹)`, preserving any isomorphism-invariant morphism property.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 5.22, p. 104.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite WithConv

namespace CommHopfAlgCat

open TauCeti TauCeti.CommHopfAlgCat

universe u

noncomputable section

variable {R : Type u} [CommRing R] (H : _root_.CommHopfAlgCat.{u} R)

section Yoneda

/-- Evaluating an `A`-point of `H` followed by a scheme morphism `φ` out of `Spec H` over
`Spec R` gives a morphism over `Spec R`. -/
private theorem SpecMap_comp_hom_over (X : Over (Spec (CommRingCat.of R)))
    (φ : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R H))) ⟶ X)
    {A : Type u} [CommRing A] [Algebra R A] (g : H →ₐ[R] A) :
    (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ φ.left) ≫ X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  rw [Category.assoc, Over.w φ]
  dsimp only [Over.mk_hom]
  rw [← Spec.map_comp]
  congr 1
  ext x
  exact g.commutes x

/-- Changing the value algebra of a point along `χ` precomposes its evaluated `Spec` morphism with
`Spec χ`. -/
private theorem SpecMap_comp_naturality (X : Over (Spec (CommRingCat.of R)))
    (φ : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R H))) ⟶ X)
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (χ : A →ₐ[R] B) (g : H →ₐ[R] A) :
    Spec.map (CommRingCat.ofHom (χ.comp g).toRingHom) ≫ φ.left =
      Spec.map (CommRingCat.ofHom χ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom g.toRingHom) ≫ φ.left := by
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

/-- **Yoneda bridge for affine group points.** Morphisms `Spec H ⟶ X` over `Spec R` are equivalent
to natural transformations from the universe-lifted points presheaf of `H` to the affine fppf
points sheaf of `X`. -/
def pointsPresheafToPointsSheafEquiv (X : Over (Spec (CommRingCat.of R))) :
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R H))) ⟶ X) ≃
      (HopfAlgebra.pointsPresheaf H ⋙ uliftFunctor.{u + 1, u} ⟶
        (CommAlgCat.pointsSheaf X).obj) where
  toFun φ :=
    { app A := ↾fun (g : ULift.{u + 1, u} (HopfAlgebra.points (R := R) (H := H) A.unop.unop)) ↦
        ULift.up <| Over.homMk
          (Spec.map (CommRingCat.ofHom g.down.ofConv.toRingHom) ≫ φ.left)
          (SpecMap_comp_hom_over H X φ g.down.ofConv)
      naturality {A B} χ := by
        ext ⟨(g : HopfAlgebra.points (R := R) (H := H) A.unop.unop)⟩
        have h := SpecMap_comp_naturality H X φ χ.unop.unop.hom g.ofConv
        rw [← WithConv.ofConv_toConv (χ.unop.unop.hom.comp g.ofConv),
          ← HopfAlgebra.mapPoints_apply (H := H) χ.unop.unop g] at h
        refine congrArg ULift.up (Over.OverMorphism.ext ?_)
        exact h.trans (congrArg (· ≫ Spec.map (CommRingCat.ofHom g.ofConv.toRingHom) ≫ φ.left)
          (TauCeti.algSpec_map_left_ofAlgHom (R := R) χ.unop.unop.hom).symm) }
  invFun α :=
    let u := (α.app (op (op (CommAlgCat.of R H)))
      (ULift.up (toConv (AlgHom.id R H)))).down
    Over.homMk u.left ((Over.w u).trans (algSpec_obj_hom _))
  left_inv φ := by
    apply Over.OverMorphism.ext
    -- Unpack `Over.homMk` and `TypeCat.ofHom` evaluation at `AlgHom.id R H`.
    change Spec.map (CommRingCat.ofHom (AlgHom.id R H).toRingHom) ≫ φ.left = φ.left
    have hid : CommRingCat.ofHom (AlgHom.id R H).toRingHom = 𝟙 (CommRingCat.of H) := rfl
    rw [hid, Spec.map_id, Category.id_comp]
  right_inv α := by
    ext A ⟨(g : HopfAlgebra.points (R := R) (H := H) A.unop.unop)⟩
    let ψ : CommAlgCat.of R H ⟶ A.unop.unop := CommAlgCat.ofHom g.ofConv
    have hmap : HopfAlgebra.mapPoints (H := H) ψ (toConv (AlgHom.id R H)) = g := by
      apply WithConv.ofConv_injective
      rw [HopfAlgebra.mapPoints_apply, WithConv.ofConv_toConv, CommAlgCat.hom_ofHom,
        AlgHom.comp_id]
    have hnat := congrArg (fun t ↦ t (ULift.up (toConv (AlgHom.id R H))))
      (α.naturality ψ.op.op)
    have hnat' : α.app A (ULift.up g) =
        ((CommAlgCat.pointsSheaf X).obj.map ψ.op.op)
          (α.app (op (op (CommAlgCat.of R H))) (ULift.up (toConv (AlgHom.id R H)))) := by
      rw [← hmap]
      exact hnat
    refine Eq.trans ?_ hnat'.symm
    refine congrArg ULift.up (Over.OverMorphism.ext ?_)
    exact (congrArg (· ≫ _) (TauCeti.algSpec_map_left_ofAlgHom (R := R) g.ofConv)).symm

/-- Evaluating `pointsPresheafToPointsSheafEquiv` at an `A`-point `g` precomposes `φ.left` with
`Spec g`. -/
@[simp]
theorem pointsPresheafToPointsSheafEquiv_apply_app_down_left
    (X : Over (Spec (CommRingCat.of R)))
    (φ : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R H))) ⟶ X)
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ)
    (g : HopfAlgebra.points (R := R) (H := H) A.unop.unop) :
    dsimp% (((pointsPresheafToPointsSheafEquiv H X φ).app A (ULift.up g)).down).left =
      Spec.map (CommRingCat.ofHom (g.ofConv : H →+* A.unop.unop)) ≫ φ.left :=
  (rfl)

/-- `pointsPresheafToPointsSheafEquiv` is natural in the target scheme over `Spec R`. -/
@[simp]
theorem pointsPresheafToPointsSheafEquiv_comp
    {X Y : Over (Spec (CommRingCat.of R))}
    (φ : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R H))) ⟶ X) (f : X ⟶ Y) :
    pointsPresheafToPointsSheafEquiv H Y (φ ≫ f) =
      pointsPresheafToPointsSheafEquiv H X φ ≫ (CommAlgCat.pointsSheafHomEquiv f).hom := by
  ext A ⟨(g : HopfAlgebra.points (R := R) (H := H) A.unop.unop)⟩
  have hrhs := CommAlgCat.pointsSheafHomEquiv_hom_app_apply f A
    ((pointsPresheafToPointsSheafEquiv H X φ).app A (ULift.up g))
  refine Eq.trans ?_ hrhs.symm
  refine congrArg ULift.up (Over.OverMorphism.ext ?_)
  exact (Category.assoc (Spec.map (CommRingCat.ofHom g.ofConv.toRingHom)) φ.left f.left).symm

/-- Descending a natural map after postcomposing with `pointsSheafHomEquiv f` postcomposes the
descended scheme morphism with `f`. -/
@[simp]
theorem pointsPresheafToPointsSheafEquiv_symm_comp
    {X Y : Over (Spec (CommRingCat.of R))}
    (α : HopfAlgebra.pointsPresheaf H ⋙ uliftFunctor.{u + 1, u} ⟶ (CommAlgCat.pointsSheaf X).obj)
    (f : X ⟶ Y) :
    (pointsPresheafToPointsSheafEquiv H Y).symm
        (α ≫ (CommAlgCat.pointsSheafHomEquiv f).hom) =
      (pointsPresheafToPointsSheafEquiv H X).symm α ≫ f := by
  apply (pointsPresheafToPointsSheafEquiv H Y).injective
  rw [pointsPresheafToPointsSheafEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

end Yoneda

section RepresentingScheme

variable {I J K : HopfIdeal R H}
variable {X X' Y Z : Over (Spec (CommRingCat.of R))}

/-- **Canonical quotient morphism to a representing scheme.** Given an isomorphism
`e : G / N ≅ pointsSheaf X`, this is the scheme morphism `Spec H ⟶ X` over `Spec R` corresponding
to the quotient projection `G ⟶ G / N`. -/
def fppfHomogeneousQuotientSchemeProjection (I : HopfIdeal R H)
    (e : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R H))) ⟶ X :=
  (pointsPresheafToPointsSheafEquiv H X).symm
    (fppfHomogeneousQuotientProjection H I ≫ e.hom.hom)

/-- Under the Yoneda bridge, `fppfHomogeneousQuotientSchemeProjection` recovers the sheaf quotient
projection composed with `e.hom`. -/
@[simp]
theorem pointsPresheafToPointsSheafEquiv_fppfHomogeneousQuotientSchemeProjection
    (I : HopfIdeal R H) (e : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X) :
    pointsPresheafToPointsSheafEquiv H X (fppfHomogeneousQuotientSchemeProjection H I e) =
      fppfHomogeneousQuotientProjection H I ≫ e.hom.hom :=
  (pointsPresheafToPointsSheafEquiv H X).apply_symm_apply _

/-- Pointwise invariance of `pointsPresheafToPointsSheafEquiv H Z φ` under right multiplication by
the subgroup cut out by `I` is equivalent to right invariance of `φ.left` on `Spec` of points. -/
private theorem pointsPresheafToPointsSheafEquiv_invariant_iff
    (I : HopfIdeal R H) (φ : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R H))) ⟶ Z) :
    (∀ (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ)
        (g : HopfAlgebra.points (R := R) (H := H) A.unop.unop)
        (n : quotientPointsSubgroup H I A.unop.unop),
        (pointsPresheafToPointsSheafEquiv H Z φ).app A (ULift.up (g * n.val)) =
          (pointsPresheafToPointsSheafEquiv H Z φ).app A (ULift.up g)) ↔
      ∀ (A : CommAlgCat.{u} R) (g : HopfAlgebra.points (R := R) (H := H) A)
        (n : quotientPointsSubgroup H I A),
        Spec.map (CommRingCat.ofHom ((g * n.val).ofConv : H →+* A)) ≫ φ.left =
          Spec.map (CommRingCat.ofHom (g.ofConv : H →+* A)) ≫ φ.left := by
  constructor
  · intro h A g n
    exact congrArg (fun x ↦ x.down.left) (h (op (op A)) g n)
  · intro h A g n
    exact congrArg ULift.up (Over.OverMorphism.ext (h A.unop.unop g n))

/-- **Universal property of a scheme representing `G / N` (Milne, Proposition 5.22).**
Morphisms `X ⟶ Z` over `Spec R` out of a scheme `X` representing `fppfHomogeneousQuotient H I` are
canonically equivalent to morphisms `Spec H ⟶ Z` over `Spec R` whose affine points are invariant
under right multiplication by the closed subgroup cut out by `I`. -/
def fppfHomogeneousQuotientSchemeHomEquiv (I : HopfIdeal R H)
    (e : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (Z : Over (Spec (CommRingCat.of R))) :
    (X ⟶ Z) ≃
      {φ : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R H))) ⟶ Z //
        ∀ (A : CommAlgCat.{u} R) (g : HopfAlgebra.points (R := R) (H := H) A)
          (n : quotientPointsSubgroup H I A),
          Spec.map (CommRingCat.ofHom ((g * n.val).ofConv : H →+* A)) ≫ φ.left =
            Spec.map (CommRingCat.ofHom (g.ofConv : H →+* A)) ≫ φ.left} :=
  CommAlgCat.pointsSheafHomEquiv.trans <|
    (Iso.homCongr e.symm (Iso.refl (CommAlgCat.pointsSheaf Z))).trans <|
      (fppfHomogeneousQuotientHomEquiv H I (CommAlgCat.pointsSheaf Z)).trans <|
        (Equiv.subtypeEquiv (pointsPresheafToPointsSheafEquiv H Z).symm fun α ↦ by
          simpa only [Equiv.apply_symm_apply] using
            pointsPresheafToPointsSheafEquiv_invariant_iff H I
              ((pointsPresheafToPointsSheafEquiv H Z).symm α))

/-- The universal property sends `f : X ⟶ Z` to its composite with the canonical quotient
projection `Spec H ⟶ X`. -/
@[simp]
theorem fppfHomogeneousQuotientSchemeHomEquiv_apply (I : HopfIdeal R H)
    (e : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (Z : Over (Spec (CommRingCat.of R))) (f : X ⟶ Z) :
    (fppfHomogeneousQuotientSchemeHomEquiv H I e Z f).val =
      fppfHomogeneousQuotientSchemeProjection H I e ≫ f := by
  simp only [fppfHomogeneousQuotientSchemeHomEquiv, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.symm_inv, Iso.refl_hom, Category.comp_id, fppfHomogeneousQuotientHomEquiv_apply,
    Equiv.subtypeEquiv_apply, ObjectProperty.FullSubcategory.comp_hom, ← Category.assoc,
    pointsPresheafToPointsSheafEquiv_symm_comp]
  rfl

/-- Restricting a descended morphism `X ⟶ Z` along `Spec H ⟶ X` recovers the original subgroup-
invariant morphism `Spec H ⟶ Z`. -/
@[reassoc (attr := simp)]
theorem fppfHomogeneousQuotientSchemeProjection_comp_homEquiv_symm (I : HopfIdeal R H)
    (e : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (Z : Over (Spec (CommRingCat.of R)))
    (φ : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R H))) ⟶ Z)
    (hφ : ∀ (A : CommAlgCat.{u} R) (g : HopfAlgebra.points (R := R) (H := H) A)
      (n : quotientPointsSubgroup H I A),
      Spec.map (CommRingCat.ofHom ((g * n.val).ofConv : H →+* A)) ≫ φ.left =
        Spec.map (CommRingCat.ofHom (g.ofConv : H →+* A)) ≫ φ.left) :
    fppfHomogeneousQuotientSchemeProjection H I e ≫
        (fppfHomogeneousQuotientSchemeHomEquiv H I e Z).symm ⟨φ, hφ⟩ = φ :=
  (fppfHomogeneousQuotientSchemeHomEquiv_apply H I e Z _).symm.trans
    (congrArg Subtype.val
      ((fppfHomogeneousQuotientSchemeHomEquiv H I e Z).apply_symm_apply ⟨φ, hφ⟩))

/-- Two morphisms out of a scheme representing `G / N` over `Spec R` are equal as soon as they
agree after precomposition with the canonical projection `Spec H ⟶ X`. -/
theorem fppfHomogeneousQuotientScheme_hom_ext (I : HopfIdeal R H)
    (e : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X) {f g : X ⟶ Z}
    (h : fppfHomogeneousQuotientSchemeProjection H I e ≫ f =
      fppfHomogeneousQuotientSchemeProjection H I e ≫ g) :
    f = g := by
  apply (fppfHomogeneousQuotientSchemeHomEquiv H I e Z).injective
  apply Subtype.ext
  simpa only [fppfHomogeneousQuotientSchemeHomEquiv_apply] using h

/-- **Uniqueness of representing schemes.** Any two schemes over `Spec R` representing the same
fppf homogeneous quotient `G / N` are canonically isomorphic over `Spec R`. -/
def fppfHomogeneousQuotientSchemeIso (I : HopfIdeal R H)
    (e₁ : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (e₂ : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X') :
    X ≅ X' :=
  CommAlgCat.pointsSheafIsoEquiv.symm (e₁.symm ≪≫ e₂)

/-- On points sheaves, `fppfHomogeneousQuotientSchemeIso` transports `e₁` to `e₂`. -/
@[simp]
theorem pointsSheafHomEquiv_fppfHomogeneousQuotientSchemeIso_hom (I : HopfIdeal R H)
    (e₁ : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (e₂ : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X') :
    CommAlgCat.pointsSheafHomEquiv (fppfHomogeneousQuotientSchemeIso H I e₁ e₂).hom =
      e₁.inv ≫ e₂.hom := by
  rw [fppfHomogeneousQuotientSchemeIso, CommAlgCat.pointsSheafIsoEquiv_symm_hom,
    Equiv.apply_symm_apply, Iso.trans_hom, Iso.symm_hom]

/-- The canonical isomorphism between two representing schemes intertwines their projections from
`Spec H`. -/
@[reassoc (attr := simp)]
theorem fppfHomogeneousQuotientSchemeProjection_comp_iso_hom (I : HopfIdeal R H)
    (e₁ : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (e₂ : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X') :
    fppfHomogeneousQuotientSchemeProjection H I e₁ ≫
        (fppfHomogeneousQuotientSchemeIso H I e₁ e₂).hom =
      fppfHomogeneousQuotientSchemeProjection H I e₂ := by
  apply (pointsPresheafToPointsSheafEquiv H X').injective
  rw [pointsPresheafToPointsSheafEquiv_comp,
    pointsPresheafToPointsSheafEquiv_fppfHomogeneousQuotientSchemeProjection,
    pointsPresheafToPointsSheafEquiv_fppfHomogeneousQuotientSchemeProjection,
    pointsSheafHomEquiv_fppfHomogeneousQuotientSchemeIso_hom,
    ObjectProperty.FullSubcategory.comp_hom, Category.assoc, ← Category.assoc e₁.hom.hom,
    ← ObjectProperty.FullSubcategory.comp_hom, e₁.hom_inv_id,
    ObjectProperty.FullSubcategory.id_hom, Category.id_comp]

/-- Comparing a representing scheme with itself gives the identity isomorphism. -/
@[simp]
theorem fppfHomogeneousQuotientSchemeIso_refl (I : HopfIdeal R H)
    (e : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X) :
    fppfHomogeneousQuotientSchemeIso H I e e = Iso.refl X := by
  ext1
  apply fppfHomogeneousQuotientScheme_hom_ext H I e
  simp

/-- Swapping the two representing schemes inverts their canonical isomorphism. -/
@[simp]
theorem fppfHomogeneousQuotientSchemeIso_symm (I : HopfIdeal R H)
    (e₁ : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (e₂ : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X') :
    (fppfHomogeneousQuotientSchemeIso H I e₁ e₂).symm =
      fppfHomogeneousQuotientSchemeIso H I e₂ e₁ := by
  ext1
  apply fppfHomogeneousQuotientScheme_hom_ext H I e₂
  rw [fppfHomogeneousQuotientSchemeProjection_comp_iso_hom,
    ← fppfHomogeneousQuotientSchemeProjection_comp_iso_hom H I e₁ e₂, Category.assoc,
    Iso.symm_hom, Iso.hom_inv_id, Category.comp_id]

/-- Any isomorphism-invariant morphism property holds for one scheme representing `G / N` if and
only if it holds for any other scheme representing `G / N`. -/
theorem morphismProperty_hom_iff_of_fppfHomogeneousQuotientIso
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso] (I : HopfIdeal R H)
    (e₁ : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (e₂ : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X') :
    P X.hom ↔ P X'.hom :=
  CommAlgCat.morphismProperty_hom_iff_of_pointsSheafIso P (e₁.symm ≪≫ e₂)

/-- Properness over `Spec R` is independent of the choice of scheme representing `G / N`. -/
theorem isProper_hom_iff_of_fppfHomogeneousQuotientIso (I : HopfIdeal R H)
    (e₁ : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (e₂ : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X') :
    IsProper X.hom ↔ IsProper X'.hom :=
  morphismProperty_hom_iff_of_fppfHomogeneousQuotientIso H @IsProper I e₁ e₂

/-- **Subgroup-induced morphism between representing schemes.** An inclusion of closed subgroups
`P ⊆ Q` (expressed contravariantly on Hopf ideals by `hJI : J ≤ I`) induces a unique morphism
`X ⟶ Y` over `Spec R` between any schemes representing `G / P` and `G / Q` that commutes with the
projections from `Spec H`. -/
def fppfHomogeneousQuotientSchemeMap
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eJ : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y)
    (hJI : J ≤ I) : X ⟶ Y :=
  CommAlgCat.pointsSheafHomEquiv.symm (eI.inv ≫ fppfHomogeneousQuotientMap H hJI ≫ eJ.hom)

/-- Applying `pointsSheafHomEquiv` to `fppfHomogeneousQuotientSchemeMap` recovers
`fppfHomogeneousQuotientMap` conjugated by the representing isomorphisms. -/
@[simp]
theorem pointsSheafHomEquiv_fppfHomogeneousQuotientSchemeMap
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eJ : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y)
    (hJI : J ≤ I) :
    CommAlgCat.pointsSheafHomEquiv (fppfHomogeneousQuotientSchemeMap H eI eJ hJI) =
      eI.inv ≫ fppfHomogeneousQuotientMap H hJI ≫ eJ.hom :=
  CommAlgCat.pointsSheafHomEquiv.apply_symm_apply _

/-- The subgroup-induced scheme morphism commutes with the canonical projections from `Spec H`. -/
@[reassoc (attr := simp)]
theorem fppfHomogeneousQuotientSchemeProjection_comp_map
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eJ : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y)
    (hJI : J ≤ I) :
    fppfHomogeneousQuotientSchemeProjection H I eI ≫
        fppfHomogeneousQuotientSchemeMap H eI eJ hJI =
      fppfHomogeneousQuotientSchemeProjection H J eJ := by
  apply (pointsPresheafToPointsSheafEquiv H Y).injective
  rw [pointsPresheafToPointsSheafEquiv_comp,
    pointsPresheafToPointsSheafEquiv_fppfHomogeneousQuotientSchemeProjection,
    pointsPresheafToPointsSheafEquiv_fppfHomogeneousQuotientSchemeProjection,
    pointsSheafHomEquiv_fppfHomogeneousQuotientSchemeMap,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    Category.assoc, ← Category.assoc eI.hom.hom, ← ObjectProperty.FullSubcategory.comp_hom,
    eI.hom_inv_id, ObjectProperty.FullSubcategory.id_hom, Category.id_comp,
    fppfHomogeneousQuotientProjection_comp_map_assoc]

/-- `fppfHomogeneousQuotientSchemeMap` is characterized as the unique morphism `X ⟶ Y` over
`Spec R` commuting with the canonical projections from `Spec H`. -/
theorem fppfHomogeneousQuotientSchemeMap_eq_iff
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eJ : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y)
    (hJI : J ≤ I) (f : X ⟶ Y) :
    f = fppfHomogeneousQuotientSchemeMap H eI eJ hJI ↔
      fppfHomogeneousQuotientSchemeProjection H I eI ≫ f =
        fppfHomogeneousQuotientSchemeProjection H J eJ := by
  constructor
  · rintro rfl
    exact fppfHomogeneousQuotientSchemeProjection_comp_map H eI eJ hJI
  · intro hf
    apply fppfHomogeneousQuotientScheme_hom_ext H I eI
    rw [hf, fppfHomogeneousQuotientSchemeProjection_comp_map]

/-- For a single representing scheme, the morphism associated to `le_refl I` is the identity. -/
@[simp]
theorem fppfHomogeneousQuotientSchemeMap_refl
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X) :
    fppfHomogeneousQuotientSchemeMap H eI eI (le_refl I) = 𝟙 X := by
  apply fppfHomogeneousQuotientScheme_hom_ext H I eI
  simp

/-- Subgroup-induced morphisms between representing schemes compose along subgroup inclusions. -/
@[reassoc (attr := simp)]
theorem fppfHomogeneousQuotientSchemeMap_comp
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eJ : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y)
    (eK : fppfHomogeneousQuotient H K ≅ CommAlgCat.pointsSheaf Z)
    (hJI : J ≤ I) (hKJ : K ≤ J) :
    fppfHomogeneousQuotientSchemeMap H eI eJ hJI ≫
        fppfHomogeneousQuotientSchemeMap H eJ eK hKJ =
      fppfHomogeneousQuotientSchemeMap H eI eK (hKJ.trans hJI) := by
  apply fppfHomogeneousQuotientScheme_hom_ext H I eI
  simp

/-- **Left translation on a representing scheme.** Every `R`-valued point `g` of `G` induces a
left-translation automorphism of any scheme `X` representing `G / N` over `Spec R`. -/
def fppfHomogeneousQuotientSchemeTranslation
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    X ≅ X :=
  CommAlgCat.pointsSheafIsoEquiv.symm
    (eI.symm ≪≫ fppfHomogeneousQuotientTranslation H I g ≪≫ eI)

/-- On points sheaves, `fppfHomogeneousQuotientSchemeTranslation` conjugates
`fppfHomogeneousQuotientTranslation` by the representing isomorphism. -/
@[simp]
theorem pointsSheafHomEquiv_fppfHomogeneousQuotientSchemeTranslation_hom
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    CommAlgCat.pointsSheafHomEquiv (fppfHomogeneousQuotientSchemeTranslation H eI g).hom =
      eI.inv ≫ (fppfHomogeneousQuotientTranslation H I g).hom ≫ eI.hom := by
  rw [fppfHomogeneousQuotientSchemeTranslation, CommAlgCat.pointsSheafIsoEquiv_symm_hom,
    Equiv.apply_symm_apply, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom]

/-- Translation by `1` on a representing scheme is the identity isomorphism. -/
@[simp]
theorem fppfHomogeneousQuotientSchemeTranslation_one
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X) :
    fppfHomogeneousQuotientSchemeTranslation H eI 1 = Iso.refl X := by
  simp [fppfHomogeneousQuotientSchemeTranslation]

/-- Left translations on a representing scheme compose in left-action order. -/
@[simp]
theorem fppfHomogeneousQuotientSchemeTranslation_mul
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (g h : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    fppfHomogeneousQuotientSchemeTranslation H eI (g * h) =
      fppfHomogeneousQuotientSchemeTranslation H eI h ≪≫
        fppfHomogeneousQuotientSchemeTranslation H eI g := by
  rw [fppfHomogeneousQuotientSchemeTranslation, fppfHomogeneousQuotientSchemeTranslation,
    fppfHomogeneousQuotientSchemeTranslation, fppfHomogeneousQuotientTranslation_mul,
    ← CommAlgCat.pointsSheafIsoEquiv_symm_trans]
  congr 1
  ext1
  simp

/-- Inverting the point inverts its left-translation automorphism on a representing scheme. -/
@[simp]
theorem fppfHomogeneousQuotientSchemeTranslation_inv
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    fppfHomogeneousQuotientSchemeTranslation H eI g⁻¹ =
      (fppfHomogeneousQuotientSchemeTranslation H eI g).symm := by
  rw [fppfHomogeneousQuotientSchemeTranslation, fppfHomogeneousQuotientSchemeTranslation,
    fppfHomogeneousQuotientTranslation_inv, ← CommAlgCat.pointsSheafIsoEquiv_symm_symm]
  congr 1

/-- Subgroup-induced morphisms between representing schemes are equivariant for left translation
by `R`-valued points of `G`. -/
@[reassoc]
theorem fppfHomogeneousQuotientSchemeTranslation_hom_comp_map
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eJ : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y)
    (hJI : J ≤ I)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    (fppfHomogeneousQuotientSchemeTranslation H eI g).hom ≫
        fppfHomogeneousQuotientSchemeMap H eI eJ hJI =
      fppfHomogeneousQuotientSchemeMap H eI eJ hJI ≫
        (fppfHomogeneousQuotientSchemeTranslation H eJ g).hom := by
  apply CommAlgCat.pointsSheafHomEquiv.injective
  simp only [CommAlgCat.pointsSheafHomEquiv_comp,
    pointsSheafHomEquiv_fppfHomogeneousQuotientSchemeMap,
    pointsSheafHomEquiv_fppfHomogeneousQuotientSchemeTranslation_hom,
    Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (fppfHomogeneousQuotientTranslation H I g).hom,
    fppfHomogeneousQuotientTranslation_hom_comp_map H I hJI g, Category.assoc]

/-- A scheme representing `G / N` also represents `G / (g N g⁻¹)` for any `R`-valued point `g` of
`G`, by composing with `fppfHomogeneousQuotientConjugateIso`. -/
def fppfHomogeneousQuotientConjugateRepresentingIso (I : HopfIdeal R H)
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    fppfHomogeneousQuotient H (I.conjugate g) ≅ CommAlgCat.pointsSheaf X :=
  (fppfHomogeneousQuotientConjugateIso H I g).symm ≪≫ eI

/-- Any isomorphism-invariant morphism property transfers between schemes representing `G / N` and
`G / (g N g⁻¹)` for an `R`-valued point `g` of `G`. -/
theorem morphismProperty_hom_iff_of_fppfHomogeneousQuotientConjugateIso
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso] (I : HopfIdeal R H)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eConj : fppfHomogeneousQuotient H (I.conjugate g) ≅ CommAlgCat.pointsSheaf Y) :
    P X.hom ↔ P Y.hom :=
  morphismProperty_hom_iff_of_fppfHomogeneousQuotientIso H P (I.conjugate g)
    (fppfHomogeneousQuotientConjugateRepresentingIso H I eI g) eConj

/-- Properness over `Spec R` is invariant under conjugating the closed subgroup by an `R`-valued
point of `G`. -/
theorem isProper_hom_iff_of_fppfHomogeneousQuotientConjugateIso (I : HopfIdeal R H)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eConj : fppfHomogeneousQuotient H (I.conjugate g) ≅ CommAlgCat.pointsSheaf Y) :
    IsProper X.hom ↔ IsProper Y.hom :=
  morphismProperty_hom_iff_of_fppfHomogeneousQuotientConjugateIso H @IsProper I g eI eConj

end RepresentingScheme

end

end CommHopfAlgCat
