/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import TauCeti.Algebra.AlgebraicGroup.Fppf.SchemePoints
public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.RationalPoints
public import TauCeti.Algebra.AlgebraicGroup.Hopf.LeftTranslation

/-!
# Universal property and functoriality of represented homogeneous quotients

Let `G = Spec H` be an affine group scheme over a commutative ring `R`, and let `N` be the closed
subgroup scheme cut out by a Hopf ideal `I` of `H`. Suppose the fppf homogeneous quotient `G/N` is
represented by a scheme `X` over `Spec R` via an isomorphism
`e : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X`.

Because `CommAlgCat.pointsSheafFunctor` is fully faithful, the sheaf-theoretic universal property
`CommHopfAlgCat.fppfHomogeneousQuotientHomEquiv` descends directly to schemes over `Spec R`:

* The quotient projection `G ⟶ G/N` corresponds to a canonical `R`-scheme morphism
  `representedQuotientProjection H I e : Spec H ⟶ X`, which is an epimorphism in `Over (Spec R)`,
  surjective on underlying schemes, and invariant under right multiplication by `N` on
  algebra-valued points.
* For every `R`-scheme `Y`, precomposition with `representedQuotientProjection H I e` identifies
  `R`-scheme morphisms `X ⟶ Y` with `R`-scheme morphisms `Spec H ⟶ Y` that are invariant under
  right multiplication by `N` on all `A`-valued points (`representedQuotientHomEquiv`).
* For closed subgroups `P ⊆ Q` defined by Hopf ideals `I` and `J` with `J ≤ I`, there is a unique
  `R`-scheme morphism `representedQuotientMap H hJI eI eJ : X ⟶ Y` between any representing
  schemes of `G/P` and `G/Q` compatible with the projections from `Spec H`. These morphisms are
  surjective on underlying schemes, descend universal closedness and properness over `Spec R`
  (`universallyClosed_hom_of_le`, `isProper_hom_of_le`), preserve identities and composition,
  canonically identify any two representing schemes of the same quotient (`representedQuotientIso`,
  `isProper_hom_iff_of_iso`), and intertwine left translations by `R`-points of `G`
  (`representedQuotientTranslation`).
* Over an algebraically closed field `k`, `k`-rational points of a representing scheme `X` are
  identified with the coset space `G(k)/N(k)` compatibly with subgroup-induced quotient morphisms
  and left translations (`representedQuotientRationalPointsEquiv`).

No smoothness, reducedness, finite-type, or normality hypothesis is imposed on `R`, `G`, or `N`.

## Main declarations

* `CommHopfAlgCat.representedQuotientProjection`: the canonical `R`-scheme projection
  `Spec H ⟶ X` onto a scheme representing `G/N`.
* `CommHopfAlgCat.representedQuotientHomEquiv`: universal property of a representing scheme `X`
  for `N`-invariant `R`-scheme morphisms out of `Spec H`.
* `CommHopfAlgCat.representedQuotientDesc`: descent of an `N`-invariant `R`-scheme morphism
  `Spec H ⟶ Y` to `X ⟶ Y`.
* `CommHopfAlgCat.representedQuotientMap`: the `R`-scheme morphism `G/P ⟶ G/Q` between
  representing schemes induced by `J ≤ I` (`P ⊆ Q`).
* `CommHopfAlgCat.universallyClosed_hom_of_le`, `CommHopfAlgCat.isProper_hom_of_le`: descent of
  universal closedness and properness along `representedQuotientMap`.
* `CommHopfAlgCat.representedQuotientIso`, `CommHopfAlgCat.isProper_hom_iff_of_iso`: canonical
  `R`-scheme isomorphism and properness invariance between schemes representing the same quotient.
* `CommHopfAlgCat.representedQuotientTranslation`: left-translation `R`-scheme automorphisms of a
  representing scheme by `R`-valued points of `G`.
* `CommHopfAlgCat.representedQuotientRationalPointsEquiv`: over an algebraically closed field `k`,
  the equivalence between `G(k)/N(k)` and `k`-rational points of a representing scheme.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 5.22 and §§5.c, 7.e.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §14.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace CommHopfAlgCat

open TauCeti TauCeti.CommHopfAlgCat

universe u

noncomputable section

section CommRing

variable {R : Type u} [CommRing R] (H : _root_.CommHopfAlgCat.{u} R)

section QuotientUniversalProperty

variable (I : HopfIdeal R H) {X : Over (Spec (CommRingCat.of R))}
  (e : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)

/-- **The canonical quotient projection `Spec H ⟶ X` onto a representing scheme.** When `e`
identifies the fppf homogeneous quotient `G/N` with the sheaf of points of `X`, the quotient
projection `G ⟶ G/N` descends to a morphism of schemes over `Spec R`. -/
def representedQuotientProjection :
    (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)) ⟶ X :=
  (specPointsHomEquiv H X).symm (fppfHomogeneousQuotientProjection H I ≫ e.hom.hom)

/-- Evaluating `representedQuotientProjection` on an `A`-valued group point `g` computes the image
of `g` under the quotient projection and the representing isomorphism `e`. -/
@[reassoc]
theorem mapMulEquiv_comp_representedQuotientProjection
    {A : CommAlgCat.{u} R} (g : HopfAlgebra.points (R := R) (H := H) A) :
    Spec.mapMulEquiv g ≫ representedQuotientProjection H I e =
      (e.hom.hom.app (op (op A))
        ((fppfHomogeneousQuotientProjection H I).app (op (op A)) (ULift.up g))).down :=
  comp_specPointsHomEquiv_symm H _ g

/-- On fppf point presheaves, `representedQuotientProjection` corresponds to
`fppfHomogeneousQuotientProjection H I ≫ e.hom.hom`. -/
@[simp]
theorem specPointsHomEquiv_representedQuotientProjection :
    specPointsHomEquiv H X (representedQuotientProjection H I e) =
      fppfHomogeneousQuotientProjection H I ≫ e.hom.hom :=
  (specPointsHomEquiv H X).apply_symm_apply _

/-- On fppf sheaves of points, `representedQuotientProjection` is locally surjective. -/
instance isLocallySurjective_pointsSheafMap_representedQuotientProjection :
    Sheaf.IsLocallySurjective
      (CommAlgCat.pointsSheafMap (representedQuotientProjection H I e)) := by
  have hfac :
      (pointsPresheafUliftIsoPointsSheaf H).hom ≫
        (CommAlgCat.pointsSheafMap (representedQuotientProjection H I e)).hom =
        fppfHomogeneousQuotientProjection H I ≫ e.hom.hom := by
    rw [← specPointsHomEquiv_eq_comp, specPointsHomEquiv_representedQuotientProjection]
  have : IsIso e.hom.hom := inferInstanceAs (IsIso ((sheafToPresheaf _ _).map e.hom))
  exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac (CommAlgCat.fppfTopology R) hfac

/-- **The canonical projection `Spec H ⟶ X` is surjective on underlying schemes.** -/
instance instSurjectiveRepresentedQuotientProjectionLeft :
    Surjective (representedQuotientProjection H I e).left :=
  CommAlgCat.surjective_left_of_isLocallySurjective_pointsSheafMap
    (representedQuotientProjection H I e)

/-- The canonical projection `Spec H ⟶ X` is invariant under right multiplication by the closed
subgroup `N` on all algebra-valued points. -/
theorem mapMulEquiv_mul_comp_representedQuotientProjection
    {A : CommAlgCat.{u} R} (g : HopfAlgebra.points (R := R) (H := H) A)
    (n : quotientPointsSubgroup H I A) :
    Spec.mapMulEquiv (g * n.val) ≫ representedQuotientProjection H I e =
      Spec.mapMulEquiv g ≫ representedQuotientProjection H I e := by
  have hinv := (fppfHomogeneousQuotientHomEquiv H I (CommAlgCat.pointsSheaf X) e.hom).property
    (op (op A)) g n
  rw [fppfHomogeneousQuotientHomEquiv_apply] at hinv
  rw [mapMulEquiv_comp_representedQuotientProjection,
    mapMulEquiv_comp_representedQuotientProjection]
  exact congrArg ULift.down hinv

/-- **Universal property of a represented homogeneous quotient (Milne, Proposition 5.22).**
Morphisms `X ⟶ Y` over `Spec R` from a scheme `X` representing `G/N` to an `R`-scheme `Y`
correspond bijectively, via precomposition with `representedQuotientProjection H I e`, to
morphisms `Spec H ⟶ Y` over `Spec R` that are invariant under right multiplication by `N` on all
algebra-valued points. -/
def representedQuotientHomEquiv (Y : Over (Spec (CommRingCat.of R))) :
    (X ⟶ Y) ≃
      {q : (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)) ⟶ Y //
        ∀ (A : CommAlgCat.{u} R) (g : HopfAlgebra.points (R := R) (H := H) A)
          (n : quotientPointsSubgroup H I A),
          Spec.mapMulEquiv (g * n.val) ≫ q = Spec.mapMulEquiv g ≫ q} :=
  (CommAlgCat.pointsSheafHomEquiv X Y).trans <|
    (Iso.homCongr e (Iso.refl (CommAlgCat.pointsSheaf Y))).symm.trans <|
      (fppfHomogeneousQuotientHomEquiv H I (CommAlgCat.pointsSheaf Y)).trans
        { toFun f := ⟨(specPointsHomEquiv H Y).symm f.val, fun A g n ↦ by
            rw [comp_specPointsHomEquiv_symm, comp_specPointsHomEquiv_symm]
            exact congrArg ULift.down (f.property (op (op A)) g n)⟩
          invFun q := ⟨specPointsHomEquiv H Y q.val, fun A g n ↦ by
            rw [specPointsHomEquiv_apply_app_apply, specPointsHomEquiv_apply_app_apply,
              q.property A.unop.unop g n]⟩
          left_inv f := Subtype.ext ((specPointsHomEquiv H Y).apply_symm_apply f.val)
          right_inv q := Subtype.ext ((specPointsHomEquiv H Y).symm_apply_apply q.val) }

/-- Forward evaluation of `representedQuotientHomEquiv` precomposes with
`representedQuotientProjection`. -/
@[simp]
theorem representedQuotientHomEquiv_apply {Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) :
    (representedQuotientHomEquiv H I e Y f).val =
      representedQuotientProjection H I e ≫ f := by
  apply (specPointsHomEquiv H Y).injective
  rw [specPointsHomEquiv_comp, specPointsHomEquiv_representedQuotientProjection]
  unfold representedQuotientHomEquiv
  simp only [Equiv.trans_apply, Equiv.coe_fn_mk,
    (specPointsHomEquiv H Y).apply_symm_apply,
    CommAlgCat.pointsSheafHomEquiv_apply, Iso.homCongr_symm, Iso.homCongr_apply,
    Iso.symm_inv, Iso.refl_symm, Iso.refl_hom, Category.comp_id,
    fppfHomogeneousQuotientHomEquiv_apply, ObjectProperty.FullSubcategory.comp_hom,
    Category.assoc]

/-- **Descent of an `N`-invariant scheme morphism to `G/N`.** Every `R`-scheme morphism
`q : Spec H ⟶ Y` invariant under right multiplication by `N` factors through
`representedQuotientProjection H I e` by a morphism `X ⟶ Y` over `Spec R`. -/
def representedQuotientDesc {Y : Over (Spec (CommRingCat.of R))}
    (q : (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)) ⟶ Y)
    (hq : ∀ (A : CommAlgCat.{u} R) (g : HopfAlgebra.points (R := R) (H := H) A)
      (n : quotientPointsSubgroup H I A),
      Spec.mapMulEquiv (g * n.val) ≫ q = Spec.mapMulEquiv g ≫ q) :
    X ⟶ Y :=
  (representedQuotientHomEquiv H I e Y).symm ⟨q, hq⟩

/-- Inverse evaluation of `representedQuotientHomEquiv` is `representedQuotientDesc`. -/
@[simp]
theorem representedQuotientHomEquiv_symm_apply {Y : Over (Spec (CommRingCat.of R))}
    (q : {q : (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)) ⟶ Y //
      ∀ (A : CommAlgCat.{u} R) (g : HopfAlgebra.points (R := R) (H := H) A)
        (n : quotientPointsSubgroup H I A),
        Spec.mapMulEquiv (g * n.val) ≫ q = Spec.mapMulEquiv g ≫ q}) :
    (representedQuotientHomEquiv H I e Y).symm q =
      representedQuotientDesc H I e q.val q.property :=
  (rfl)

/-- Composing `representedQuotientProjection` with `representedQuotientDesc` recovers the original
morphism from `Spec H`. -/
@[reassoc (attr := simp)]
theorem representedQuotientProjection_comp_desc {Y : Over (Spec (CommRingCat.of R))}
    (q : (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)) ⟶ Y)
    (hq : ∀ (A : CommAlgCat.{u} R) (g : HopfAlgebra.points (R := R) (H := H) A)
      (n : quotientPointsSubgroup H I A),
      Spec.mapMulEquiv (g * n.val) ≫ q = Spec.mapMulEquiv g ≫ q) :
    representedQuotientProjection H I e ≫ representedQuotientDesc H I e q hq = q :=
  (representedQuotientHomEquiv_apply H I e (representedQuotientDesc H I e q hq)).symm.trans
    (congrArg Subtype.val ((representedQuotientHomEquiv H I e Y).apply_symm_apply ⟨q, hq⟩))

/-- Morphisms out of a scheme representing `G/N` are determined by their composites with
`representedQuotientProjection`. -/
theorem representedQuotient_hom_ext {Y : Over (Spec (CommRingCat.of R))} {f₁ f₂ : X ⟶ Y}
    (h : representedQuotientProjection H I e ≫ f₁ = representedQuotientProjection H I e ≫ f₂) :
    f₁ = f₂ :=
  (representedQuotientHomEquiv H I e Y).injective <| Subtype.ext <| by
    rw [representedQuotientHomEquiv_apply, representedQuotientHomEquiv_apply]
    exact h

/-- The canonical projection `Spec H ⟶ X` onto a representing scheme is an epimorphism in
`Over (Spec R)`. -/
instance epi_representedQuotientProjection : Epi (representedQuotientProjection H I e) :=
  ⟨fun _ _ h ↦ representedQuotient_hom_ext H I e h⟩

/-- A morphism `f : X ⟶ Y` equals `representedQuotientDesc H I e q hq` if and only if its
composite with `representedQuotientProjection H I e` is `q`. -/
theorem eq_representedQuotientDesc_iff {Y : Over (Spec (CommRingCat.of R))}
    (f : X ⟶ Y) (q : (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)) ⟶ Y)
    (hq : ∀ (A : CommAlgCat.{u} R) (g : HopfAlgebra.points (R := R) (H := H) A)
      (n : quotientPointsSubgroup H I A),
      Spec.mapMulEquiv (g * n.val) ≫ q = Spec.mapMulEquiv g ≫ q) :
    f = representedQuotientDesc H I e q hq ↔
      representedQuotientProjection H I e ≫ f = q :=
  ⟨by rintro rfl; exact representedQuotientProjection_comp_desc H I e q hq,
   fun h ↦ representedQuotient_hom_ext H I e
    (h.trans (representedQuotientProjection_comp_desc H I e q hq).symm)⟩

end QuotientUniversalProperty

section SubgroupMap

variable {I J K : HopfIdeal R H}
  {X Y Z : Over (Spec (CommRingCat.of R))}

/-- **Morphism `G/P ⟶ G/Q` of representing schemes induced by `P ⊆ Q` (Milne, Proposition 5.22).**
For closed subgroups `P ⊆ Q` defined by Hopf ideals `I` and `J` with `J ≤ I`, and schemes `X`, `Y`
over `Spec R` representing `fppfHomogeneousQuotient H I` and `fppfHomogeneousQuotient H J`, the
quotient sheaf projection `fppfHomogeneousQuotientMap H hJI` descends to a unique `R`-scheme
morphism `X ⟶ Y`. -/
def representedQuotientMap (hJI : J ≤ I)
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eJ : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y) :
    X ⟶ Y :=
  CommAlgCat.homOfPointsSheafHom (eI.inv ≫ fppfHomogeneousQuotientMap H hJI ≫ eJ.hom)

/-- On fppf sheaves of points, `representedQuotientMap` induces `fppfHomogeneousQuotientMap`
transported across `eI` and `eJ`. -/
@[simp]
theorem pointsSheafMap_representedQuotientMap (hJI : J ≤ I)
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eJ : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y) :
    CommAlgCat.pointsSheafMap (representedQuotientMap H hJI eI eJ) =
      eI.inv ≫ fppfHomogeneousQuotientMap H hJI ≫ eJ.hom :=
  CommAlgCat.pointsSheafMap_homOfPointsSheafHom _

/-- On fppf sheaves of points, `representedQuotientMap` is locally surjective. -/
instance isLocallySurjective_pointsSheafMap_representedQuotientMap (hJI : J ≤ I)
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eJ : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y) :
    Sheaf.IsLocallySurjective
      (CommAlgCat.pointsSheafMap (representedQuotientMap H hJI eI eJ)) := by
  change Presheaf.IsLocallySurjective (CommAlgCat.fppfTopology R)
    (CommAlgCat.pointsSheafMap (representedQuotientMap H hJI eI eJ)).hom
  rw [pointsSheafMap_representedQuotientMap]
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  have : IsIso eI.inv.hom := inferInstanceAs (IsIso ((sheafToPresheaf _ _).map eI.inv))
  have : IsIso eJ.hom.hom := inferInstanceAs (IsIso ((sheafToPresheaf _ _).map eJ.hom))
  infer_instance

/-- **Subgroup-induced quotient morphisms `G/P ⟶ G/Q` are surjective on underlying schemes.** -/
instance instSurjectiveRepresentedQuotientMapLeft (hJI : J ≤ I)
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eJ : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y) :
    Surjective (representedQuotientMap H hJI eI eJ).left :=
  CommAlgCat.surjective_left_of_isLocallySurjective_pointsSheafMap
    (representedQuotientMap H hJI eI eJ)

/-- **Universal closedness descends along subgroup inclusions.** For closed subgroups `P ⊆ Q`
defined by Hopf ideals `I` and `J` with `J ≤ I`, if a scheme `X` representing `G/P` is universally
closed over `Spec R`, then any scheme `Y` representing `G/Q` is universally closed over
`Spec R`. -/
theorem universallyClosed_hom_of_le (hJI : J ≤ I)
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eJ : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y)
    [UniversallyClosed X.hom] :
    UniversallyClosed Y.hom := by
  have : UniversallyClosed ((representedQuotientMap H hJI eI eJ).left ≫ Y.hom) := by
    rwa [Over.w]
  exact UniversallyClosed.of_comp_surjective (representedQuotientMap H hJI eI eJ).left Y.hom

/-- **Properness descends along subgroup inclusions.** For closed subgroups `P ⊆ Q` defined by Hopf
ideals `I` and `J` with `J ≤ I`, if a scheme `X` representing `G/P` is proper over `Spec R` and a
scheme `Y` representing `G/Q` is separated and locally of finite type over `Spec R`, then `Y` is
proper over `Spec R`. -/
theorem isProper_hom_of_le (hJI : J ≤ I)
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eJ : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y)
    [IsProper X.hom] [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] :
    IsProper Y.hom := by
  have : UniversallyClosed Y.hom := universallyClosed_hom_of_le H hJI eI eJ
  exact ⟨⟩

/-- The subgroup-induced morphism of representing schemes commutes with the canonical projections
from `Spec H`. -/
@[reassoc (attr := simp)]
theorem representedQuotientProjection_comp_map (hJI : J ≤ I)
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eJ : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y) :
    representedQuotientProjection H I eI ≫ representedQuotientMap H hJI eI eJ =
      representedQuotientProjection H J eJ := by
  have heI : eI.hom.hom ≫ eI.inv.hom = 𝟙 _ := by
    rw [← ObjectProperty.FullSubcategory.comp_hom, eI.hom_inv_id,
      ObjectProperty.FullSubcategory.id_hom]
  apply (specPointsHomEquiv H Y).injective
  rw [specPointsHomEquiv_comp, specPointsHomEquiv_representedQuotientProjection,
    specPointsHomEquiv_representedQuotientProjection, pointsSheafMap_representedQuotientMap]
  simp only [ObjectProperty.FullSubcategory.comp_hom, Category.assoc]
  rw [← Category.assoc eI.hom.hom, heI, Category.id_comp,
    ← Category.assoc, fppfHomogeneousQuotientProjection_comp_map]

/-- `representedQuotientMap` is the unique `R`-scheme morphism `X ⟶ Y` compatible with the
canonical projections from `Spec H`. -/
theorem eq_representedQuotientMap_iff (hJI : J ≤ I)
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eJ : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y)
    (f : X ⟶ Y) :
    f = representedQuotientMap H hJI eI eJ ↔
      representedQuotientProjection H I eI ≫ f = representedQuotientProjection H J eJ :=
  ⟨by rintro rfl; exact representedQuotientProjection_comp_map H hJI eI eJ,
   fun h ↦ representedQuotient_hom_ext H I eI
    (h.trans (representedQuotientProjection_comp_map H hJI eI eJ).symm)⟩

/-- `representedQuotientMap` agrees with descending `representedQuotientProjection H J eJ` along
`representedQuotientProjection H I eI`. -/
theorem representedQuotientMap_eq_desc (hJI : J ≤ I)
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eJ : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y) :
    representedQuotientMap H hJI eI eJ =
      representedQuotientDesc H I eI (representedQuotientProjection H J eJ)
        (fun A g n ↦ mapMulEquiv_mul_comp_representedQuotientProjection H J eJ g
          ⟨n.val, quotientPointsSubgroup_le_of_le H hJI A n.property⟩) :=
  (eq_representedQuotientDesc_iff H I eI _ _ _).mpr
    (representedQuotientProjection_comp_map H hJI eI eJ)

/-- For `I = J` with the same representing isomorphism, `representedQuotientMap` is the identity. -/
@[simp]
theorem representedQuotientMap_refl (I : HopfIdeal R H)
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X) :
    representedQuotientMap H (le_refl I) eI eI = 𝟙 X := by
  apply representedQuotient_hom_ext H I eI
  rw [representedQuotientProjection_comp_map, Category.comp_id]

/-- Subgroup-induced morphisms of representing schemes compose along chains `K ≤ J ≤ I`. -/
@[reassoc (attr := simp)]
theorem representedQuotientMap_comp (hJI : J ≤ I) (hKJ : K ≤ J)
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eJ : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y)
    (eK : fppfHomogeneousQuotient H K ≅ CommAlgCat.pointsSheaf Z) :
    representedQuotientMap H hJI eI eJ ≫ representedQuotientMap H hKJ eJ eK =
      representedQuotientMap H (hKJ.trans hJI) eI eK := by
  apply representedQuotient_hom_ext H I eI
  rw [representedQuotientProjection_comp_map_assoc, representedQuotientProjection_comp_map,
    representedQuotientProjection_comp_map]

variable (I) in
/-- **Canonical isomorphism between schemes representing the same homogeneous quotient.** Any two
`R`-schemes representing `fppfHomogeneousQuotient H I` are canonically isomorphic over `Spec R`
compatibly with the quotient projections from `Spec H`. -/
def representedQuotientIso
    (e₁ : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (e₂ : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf Y) :
    X ≅ Y :=
  CommAlgCat.isoOfPointsSheafIso (e₁.symm ≪≫ e₂)

/-- The forward morphism of `representedQuotientIso` is `representedQuotientMap H (le_refl I)`. -/
@[simp]
theorem representedQuotientIso_hom
    (e₁ : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (e₂ : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf Y) :
    (representedQuotientIso H I e₁ e₂).hom = representedQuotientMap H (le_refl I) e₁ e₂ := by
  apply CommAlgCat.over_hom_ext_of_pointsSheafMap
  simp [representedQuotientIso]

/-- The inverse morphism of `representedQuotientIso` is `representedQuotientMap H (le_refl I)` in
the opposite direction. -/
@[simp]
theorem representedQuotientIso_inv
    (e₁ : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (e₂ : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf Y) :
    (representedQuotientIso H I e₁ e₂).inv = representedQuotientMap H (le_refl I) e₂ e₁ := by
  apply CommAlgCat.over_hom_ext_of_pointsSheafMap
  simp [representedQuotientIso]

/-- Comparing a representing scheme with itself gives the identity isomorphism. -/
@[simp]
theorem representedQuotientIso_refl
    (e₁ : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X) :
    representedQuotientIso H I e₁ e₁ = Iso.refl X := by
  ext : 1
  simp

/-- Swapping the two representing schemes inverts `representedQuotientIso`. -/
@[simp]
theorem representedQuotientIso_symm
    (e₁ : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (e₂ : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf Y) :
    (representedQuotientIso H I e₁ e₂).symm = representedQuotientIso H I e₂ e₁ := by
  ext : 1
  simp

/-- Canonical comparison isomorphisms between representing schemes compose transitively. -/
@[simp]
theorem representedQuotientIso_trans
    (e₁ : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (e₂ : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf Y)
    (e₃ : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf Z) :
    representedQuotientIso H I e₁ e₂ ≪≫ representedQuotientIso H I e₂ e₃ =
      representedQuotientIso H I e₁ e₃ := by
  ext : 1
  simp

variable (I) in
/-- Universal closedness over `Spec R` is invariant across schemes representing the same
`fppfHomogeneousQuotient H I`. -/
theorem universallyClosed_hom_iff_of_iso
    (e₁ : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (e₂ : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf Y) :
    UniversallyClosed X.hom ↔ UniversallyClosed Y.hom :=
  ⟨fun _ ↦ universallyClosed_hom_of_le H (le_refl I) e₁ e₂,
   fun _ ↦ universallyClosed_hom_of_le H (le_refl I) e₂ e₁⟩

variable (I) in
/-- **Properness over `Spec R` is an intrinsic property of a represented homogeneous quotient.**
Any two `R`-schemes representing `fppfHomogeneousQuotient H I` are simultaneously proper over
`Spec R`. -/
theorem isProper_hom_iff_of_iso
    (e₁ : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (e₂ : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf Y) :
    IsProper X.hom ↔ IsProper Y.hom := by
  have : IsIso (representedQuotientIso H I e₁ e₂).hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (representedQuotientIso H I e₁ e₂).hom))
  rw [← Over.w (representedQuotientIso H I e₁ e₂).hom]
  exact MorphismProperty.cancel_left_of_respectsIso @IsProper _ _

end SubgroupMap

section Translation

variable (I : HopfIdeal R H) {X : Over (Spec (CommRingCat.of R))}
  (e : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)

/-- **Left translation on a representing scheme.** Every `R`-valued group point `g ∈ G(R)` acts by
an `R`-scheme automorphism on any scheme `X` representing `fppfHomogeneousQuotient H I`. -/
def representedQuotientTranslation
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    X ≅ X :=
  CommAlgCat.isoOfPointsSheafIso (e.symm ≪≫ fppfHomogeneousQuotientTranslation H I g ≪≫ e)

/-- On fppf sheaves of points, `representedQuotientTranslation` induces
`fppfHomogeneousQuotientTranslation` conjugated by `e`. -/
@[simp]
theorem pointsSheafIso_representedQuotientTranslation
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    CommAlgCat.pointsSheafIso (representedQuotientTranslation H I e g) =
      e.symm ≪≫ fppfHomogeneousQuotientTranslation H I g ≪≫ e :=
  CommAlgCat.pointsSheafIso_isoOfPointsSheafIso _

/-- On morphisms of fppf sheaves of points, `(representedQuotientTranslation H I e g).hom` induces
`(fppfHomogeneousQuotientTranslation H I g).hom` conjugated by `e`. -/
@[simp]
theorem pointsSheafMap_representedQuotientTranslation_hom
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    CommAlgCat.pointsSheafMap (representedQuotientTranslation H I e g).hom =
      e.inv ≫ (fppfHomogeneousQuotientTranslation H I g).hom ≫ e.hom := by
  simpa only [CommAlgCat.pointsSheafIso_hom, Iso.trans_hom, Iso.symm_hom] using
    congrArg Iso.hom (pointsSheafIso_representedQuotientTranslation H I e g)

/-- On morphisms of fppf sheaves of points, `(representedQuotientTranslation H I e g).inv` induces
`(fppfHomogeneousQuotientTranslation H I g).inv` conjugated by `e`. -/
@[simp]
theorem pointsSheafMap_representedQuotientTranslation_inv
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    CommAlgCat.pointsSheafMap (representedQuotientTranslation H I e g).inv =
      e.inv ≫ (fppfHomogeneousQuotientTranslation H I g).inv ≫ e.hom := by
  simpa only [CommAlgCat.pointsSheafIso_inv, Iso.trans_inv, Iso.symm_inv, Category.assoc] using
    congrArg Iso.inv (pointsSheafIso_representedQuotientTranslation H I e g)

/-- Translation by `1 ∈ G(R)` is the identity automorphism of `X`. -/
@[simp]
theorem representedQuotientTranslation_one :
    representedQuotientTranslation H I e 1 = Iso.refl X := by
  ext : 1
  apply CommAlgCat.over_hom_ext_of_pointsSheafMap
  simp

/-- Left translations on `X` compose in action order. -/
@[simp]
theorem representedQuotientTranslation_mul
    (g h : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    representedQuotientTranslation H I e (g * h) =
      representedQuotientTranslation H I e h ≪≫ representedQuotientTranslation H I e g := by
  ext : 1
  apply CommAlgCat.over_hom_ext_of_pointsSheafMap
  have hmul := congrArg Iso.hom (fppfHomogeneousQuotientTranslation_mul H I g h)
  simp only [Iso.trans_hom, pointsSheafMap_representedQuotientTranslation_hom,
    CommAlgCat.pointsSheafMap_comp, hmul, Category.assoc, Iso.hom_inv_id_assoc]

/-- Translation by `g⁻¹` is the inverse automorphism of translation by `g`. -/
@[simp]
theorem representedQuotientTranslation_inv
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    representedQuotientTranslation H I e g⁻¹ =
      (representedQuotientTranslation H I e g).symm := by
  ext : 1
  have h := congrArg Iso.hom (representedQuotientTranslation_mul H I e g g⁻¹)
  rw [mul_inv_cancel, representedQuotientTranslation_one, Iso.refl_hom, Iso.trans_hom] at h
  rw [Iso.symm_hom, ← Category.id_comp (representedQuotientTranslation H I e g).inv, h,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- On projected `A`-valued points of `G`, `representedQuotientTranslation` acts by left
multiplication by the base-changed point `extendPoint H A g`. -/
@[reassoc]
theorem mapMulEquiv_representedQuotientProjection_comp_translation_hom
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    {A : CommAlgCat.{u} R} (x : HopfAlgebra.points (R := R) (H := H) A) :
    Spec.mapMulEquiv x ≫ representedQuotientProjection H I e ≫
        (representedQuotientTranslation H I e g).hom =
      Spec.mapMulEquiv (HopfAlgebra.extendPoint H A g * x) ≫
        representedQuotientProjection H I e := by
  have hcomp :
      specPointsHomEquiv H X
          (representedQuotientProjection H I e ≫
            (representedQuotientTranslation H I e g).hom) =
        fppfHomogeneousQuotientProjection H I ≫
          (fppfHomogeneousQuotientTranslation H I g).hom.hom ≫ e.hom.hom := by
    have he : e.hom.hom ≫ e.inv.hom = 𝟙 _ := by
      rw [← ObjectProperty.FullSubcategory.comp_hom, e.hom_inv_id,
        ObjectProperty.FullSubcategory.id_hom]
    rw [specPointsHomEquiv_comp, specPointsHomEquiv_representedQuotientProjection,
      pointsSheafMap_representedQuotientTranslation_hom]
    simp only [ObjectProperty.FullSubcategory.comp_hom, Category.assoc]
    rw [← Category.assoc e.hom.hom, he, Category.id_comp]
  have happ := congrArg (fun α ↦ (α.app (op (op A)) (ULift.up x)).down) hcomp
  have hlhs :
      ((specPointsHomEquiv H X
        (representedQuotientProjection H I e ≫
          (representedQuotientTranslation H I e g).hom)).app
        (op (op A)) (ULift.up x)).down =
        Spec.mapMulEquiv x ≫ representedQuotientProjection H I e ≫
          (representedQuotientTranslation H I e g).hom :=
    congrArg ULift.down (specPointsHomEquiv_apply_app_apply H _ (op (op A)) x)
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at happ
  rw [fppfHomogeneousQuotientTranslation_hom_app_projection] at happ
  exact hlhs.symm.trans (happ.trans (mapMulEquiv_comp_representedQuotientProjection H I e
    (HopfAlgebra.extendPoint H A g * x)).symm)

/-- On projected `A`-valued points of `G`, `(representedQuotientTranslation H I e g).inv` acts by
left multiplication by the base-changed inverse point `extendPoint H A g⁻¹`. -/
@[reassoc]
theorem mapMulEquiv_representedQuotientProjection_comp_translation_inv
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    {A : CommAlgCat.{u} R} (x : HopfAlgebra.points (R := R) (H := H) A) :
    Spec.mapMulEquiv x ≫ representedQuotientProjection H I e ≫
        (representedQuotientTranslation H I e g).inv =
      Spec.mapMulEquiv (HopfAlgebra.extendPoint H A g⁻¹ * x) ≫
        representedQuotientProjection H I e := by
  rw [← Iso.symm_hom, ← representedQuotientTranslation_inv]
  exact mapMulEquiv_representedQuotientProjection_comp_translation_hom H I e g⁻¹ x

/-- `representedQuotientProjection` intertwines left translation on `Spec H` by `g ∈ G(R)` with
`representedQuotientTranslation` on `X`. -/
@[reassoc]
theorem representedQuotientProjection_comp_translation_hom
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    representedQuotientProjection H I e ≫ (representedQuotientTranslation H I e g).hom =
      Spec.mapMulEquiv (WithConv.toConv (HopfAlgebra.leftTranslationAlgEquiv g).toAlgHom) ≫
        representedQuotientProjection H I e := by
  have hid : Spec.mapMulEquiv (WithConv.toConv (AlgHom.id R H)) =
      𝟙 ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) :=
    Over.OverMorphism.ext <|
      (TauCeti.CommHopfAlgCat.mapMulEquiv_left
        (WithConv.toConv (AlgHom.id R H))).trans (Spec.map_id (CommRingCat.of H))
  have h := mapMulEquiv_representedQuotientProjection_comp_translation_hom H I e g
    (A := CommAlgCat.of R H) (WithConv.toConv (AlgHom.id R H))
  rw [hid, Category.id_comp, HopfAlgebra.extendPoint_apply, ← AlgHom.mapValue_apply,
    ← HopfAlgebra.toConv_leftTranslationAlgEquiv] at h
  exact h

/-- `representedQuotientProjection` intertwines left translation on `Spec H` by `g⁻¹ ∈ G(R)` with
`(representedQuotientTranslation H I e g).inv` on `X`. -/
@[reassoc]
theorem representedQuotientProjection_comp_translation_inv
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    representedQuotientProjection H I e ≫ (representedQuotientTranslation H I e g).inv =
      Spec.mapMulEquiv (WithConv.toConv (HopfAlgebra.leftTranslationAlgEquiv g⁻¹).toAlgHom) ≫
        representedQuotientProjection H I e := by
  rw [← Iso.symm_hom, ← representedQuotientTranslation_inv]
  exact representedQuotientProjection_comp_translation_hom H I e g⁻¹

/-- **Equivariance of subgroup-induced quotient morphisms.** For `J ≤ I` (`P ⊆ Q`), the morphism
`representedQuotientMap H hJI e eJ` intertwines left translation by every `g ∈ G(R)`. -/
@[reassoc]
theorem representedQuotientTranslation_hom_comp_map {J : HopfIdeal R H} (hJI : J ≤ I)
    {Y : Over (Spec (CommRingCat.of R))}
    (eJ : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    (representedQuotientTranslation H I e g).hom ≫ representedQuotientMap H hJI e eJ =
      representedQuotientMap H hJI e eJ ≫ (representedQuotientTranslation H J eJ g).hom := by
  apply CommAlgCat.over_hom_ext_of_pointsSheafMap
  simp only [CommAlgCat.pointsSheafMap_comp, pointsSheafMap_representedQuotientTranslation_hom,
    pointsSheafMap_representedQuotientMap, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (fppfHomogeneousQuotientTranslation H I g).hom,
    fppfHomogeneousQuotientTranslation_hom_comp_map H I hJI g, Category.assoc]

/-- For `J ≤ I` (`P ⊆ Q`), `representedQuotientMap H hJI e eJ` also intertwines inverse left
translation by every `g ∈ G(R)`. -/
@[reassoc]
theorem representedQuotientTranslation_inv_comp_map {J : HopfIdeal R H} (hJI : J ≤ I)
    {Y : Over (Spec (CommRingCat.of R))}
    (eJ : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    (representedQuotientTranslation H I e g).inv ≫ representedQuotientMap H hJI e eJ =
      representedQuotientMap H hJI e eJ ≫ (representedQuotientTranslation H J eJ g).inv := by
  rw [← Iso.symm_hom, ← representedQuotientTranslation_inv,
    ← Iso.symm_hom, ← representedQuotientTranslation_inv]
  exact representedQuotientTranslation_hom_comp_map H I e hJI eJ g⁻¹

end Translation

end CommRing

section AlgClosed

variable {k : Type u} [Field k] [IsAlgClosed k] (H : _root_.CommHopfAlgCat.{u} k)
  (I : HopfIdeal k H) {X : Over (Spec (CommRingCat.of k))}
  (e : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)

/-- **Rational points of a scheme representing `G/N`.** Over an algebraically closed field `k`,
the left cosets `G(k)/N(k)` are in canonical bijection with `k`-rational points of any `k`-scheme
`X` representing `fppfHomogeneousQuotient H I`. -/
def representedQuotientRationalPointsEquiv :
    HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) ⧸
        quotientPointsSubgroup H I (CommAlgCat.of k k) ≃
      ((Spec (CommRingCat.of k)).asOver (Spec (CommRingCat.of k)) ⟶ X) :=
  (fppfHomogeneousQuotientRationalPointsEquiv H I).trans <|
    (Iso.toEquiv (((sheafToPresheaf (CommAlgCat.fppfTopology k) (Type (u + 1))).mapIso e).app
      (op (op (CommAlgCat.of k k))))).trans Equiv.ulift

/-- `representedQuotientRationalPointsEquiv` sends the coset of `g ∈ G(k)` to the image of `g`
under `representedQuotientProjection`. -/
@[simp]
theorem representedQuotientRationalPointsEquiv_mk
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) :
    representedQuotientRationalPointsEquiv H I e (QuotientGroup.mk g) =
      Spec.mapMulEquiv g ≫ representedQuotientProjection H I e := by
  unfold representedQuotientRationalPointsEquiv
  exact (congrArg (fun s ↦ (e.hom.hom.app (op (op (CommAlgCat.of k k))) s).down)
    (fppfHomogeneousQuotientRationalPointsEquiv_mk H I g)).trans
      (mapMulEquiv_comp_representedQuotientProjection H I e g).symm

/-- Inverse evaluation of `representedQuotientRationalPointsEquiv` sends the projected point of
`g ∈ G(k)` to its left coset `QuotientGroup.mk g`. -/
@[simp]
theorem representedQuotientRationalPointsEquiv_symm_mapMulEquiv_comp_representedQuotientProjection
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) :
    (representedQuotientRationalPointsEquiv H I e).symm
        (Spec.mapMulEquiv g ≫ representedQuotientProjection H I e) =
      QuotientGroup.mk g :=
  (representedQuotientRationalPointsEquiv H I e).symm_apply_eq.mpr
    (representedQuotientRationalPointsEquiv_mk H I e g).symm

/-- Every `k`-rational point of a scheme representing `G/N` over an algebraically closed field `k`
lifts to a `k`-rational point of `G`. -/
theorem exists_mapMulEquiv_comp_representedQuotientProjection_eq
    (x : (Spec (CommRingCat.of k)).asOver (Spec (CommRingCat.of k)) ⟶ X) :
    ∃ g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k),
      Spec.mapMulEquiv g ≫ representedQuotientProjection H I e = x := by
  obtain ⟨q, rfl⟩ := (representedQuotientRationalPointsEquiv H I e).surjective x
  induction q using QuotientGroup.induction_on with
  | H g => exact ⟨g, (representedQuotientRationalPointsEquiv_mk H I e g).symm⟩

/-- Two `k`-rational points of `G` have the same image in `X` if and only if they lie in the same
left coset of `N(k)`. -/
theorem mapMulEquiv_comp_representedQuotientProjection_eq_iff
    (g g' : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) :
    Spec.mapMulEquiv g ≫ representedQuotientProjection H I e =
        Spec.mapMulEquiv g' ≫ representedQuotientProjection H I e ↔
      g⁻¹ * g' ∈ quotientPointsSubgroup H I (CommAlgCat.of k k) := by
  rw [← representedQuotientRationalPointsEquiv_mk, ← representedQuotientRationalPointsEquiv_mk,
    (representedQuotientRationalPointsEquiv H I e).injective.eq_iff, QuotientGroup.eq]

/-- **Compatibility of `representedQuotientMap` with rational cosets.** For `J ≤ I` (`P ⊆ Q`),
composing a `k`-point of `X` with `representedQuotientMap H hJI e eJ` applies the canonical coset
projection `G(k)/P(k) → G(k)/Q(k)`. -/
@[reassoc]
theorem representedQuotientRationalPointsEquiv_comp_map {J : HopfIdeal k H} (hJI : J ≤ I)
    {Y : Over (Spec (CommRingCat.of k))}
    (eJ : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y)
    (q : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) ⧸
      quotientPointsSubgroup H I (CommAlgCat.of k k)) :
    representedQuotientRationalPointsEquiv H I e q ≫ representedQuotientMap H hJI e eJ =
      representedQuotientRationalPointsEquiv H J eJ
        (Subgroup.quotientMapOfLE (quotientPointsSubgroup_le_of_le H hJI _) q) := by
  induction q using QuotientGroup.induction_on with
  | H g =>
    rw [Subgroup.quotientMapOfLE_apply_mk, representedQuotientRationalPointsEquiv_mk,
      representedQuotientRationalPointsEquiv_mk, Category.assoc,
      representedQuotientProjection_comp_map]

/-- **Compatibility of `representedQuotientTranslation` with rational cosets.** Composing a
`k`-point of `X` with `(representedQuotientTranslation H I e g).hom` acts on `G(k)/N(k)` by left
multiplication by `g`. -/
@[reassoc]
theorem representedQuotientRationalPointsEquiv_comp_translation_hom
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k))
    (q : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) ⧸
      quotientPointsSubgroup H I (CommAlgCat.of k k)) :
    representedQuotientRationalPointsEquiv H I e q ≫
        (representedQuotientTranslation H I e g).hom =
      representedQuotientRationalPointsEquiv H I e (g • q) := by
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [representedQuotientRationalPointsEquiv_mk, MulAction.Quotient.smul_mk, smul_eq_mul,
      representedQuotientRationalPointsEquiv_mk, Category.assoc,
      mapMulEquiv_representedQuotientProjection_comp_translation_hom,
      HopfAlgebra.extendPoint_self]

/-- Composing a `k`-point of `X` with `(representedQuotientTranslation H I e g).inv` acts on
`G(k)/N(k)` by left multiplication by `g⁻¹`. -/
@[reassoc]
theorem representedQuotientRationalPointsEquiv_comp_translation_inv
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k))
    (q : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) ⧸
      quotientPointsSubgroup H I (CommAlgCat.of k k)) :
    representedQuotientRationalPointsEquiv H I e q ≫
        (representedQuotientTranslation H I e g).inv =
      representedQuotientRationalPointsEquiv H I e (g⁻¹ • q) := by
  rw [← Iso.symm_hom, ← representedQuotientTranslation_inv]
  exact representedQuotientRationalPointsEquiv_comp_translation_hom H I e g⁻¹ q

end AlgClosed

end

end CommHopfAlgCat
