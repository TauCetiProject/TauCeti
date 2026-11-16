/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.RationalPoints
public import TauCeti.Algebra.AlgebraicGroup.Hopf.LeftTranslation
import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.SchemePoints

/-!
# Representing schemes for fppf homogeneous quotients

Let `G = Spec H` be an affine group scheme over a commutative ring `R`, let `N` be the closed
subgroup cut out by a Hopf ideal `I` of `H`, and suppose that the fppf homogeneous quotient
`G/N` (`CommHopfAlgCat.fppfHomogeneousQuotient H I`) is represented by a scheme `X` over `Spec R`
via an isomorphism `eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X`.

Because `CommAlgCat.pointsSheafFunctor R` is fully faithful, sheaf-level constructions on `G/N`
descend uniquely to scheme morphisms over `Spec R`:

1. **Quotient projection and universal property (Milne, Proposition 5.22).** The canonical sheaf
   projection `G ⟶ G/N` corresponds to a scheme morphism
   `fppfHomogeneousQuotientSchemeProjection eI : (Spec H).asOver (Spec R) ⟶ X` which is invariant
   under right multiplication by `N`, surjective on underlying schemes, and an epimorphism in
   `Over (Spec R)`. For every `R`-scheme `Y` (not necessarily affine), morphisms `X ⟶ Y` over
   `Spec R` are in bijection (`fppfHomogeneousQuotientSchemeHomEquiv eI Y`) with morphisms
   `(Spec H).asOver (Spec R) ⟶ Y` that are invariant under right multiplication by `N(A)` on
   `A`-points for all commutative `R`-algebras `A`.
2. **Canonical uniqueness and subgroup-induced projections.** Any two schemes representing `G/N`
   over `Spec R` are canonically isomorphic under `G` (`fppfHomogeneousQuotientSchemeIso`). Given
   an inclusion of closed subgroups `N₁ ⊆ N₂` (corresponding to `J ≤ I` on Hopf ideals) and
   schemes `X`, `Y` representing `G/N₁`, `G/N₂`, the sheaf map `fppfHomogeneousQuotientMap H hJI`
   descends to a unique `R`-scheme morphism `fppfHomogeneousQuotientSchemeMap eI eJ hJI : X ⟶ Y`
   under `G`. This morphism is functorial in subgroup inclusions, an epimorphism in
   `Over (Spec R)`, and surjective on underlying schemes.
3. **Invariance and descent of properness.** Any isomorphism-respecting morphism property of a
   representing scheme depends only on the homogeneous quotient
   (`morphismProperty_hom_iff_of_fppfHomogeneousQuotientScheme`, specialized to properness in
   `isProper_hom_iff_of_fppfHomogeneousQuotientScheme`). When `X` is universally closed over
   `Spec R`, surjectivity of `X ⟶ Y` transfers universal closedness from `X` to `Y`
   (`universallyClosed_hom_of_fppfHomogeneousQuotientScheme_of_le`); if `Y` is also separated and
   locally of finite type over `Spec R`, then `Y` is proper over `Spec R`
   (`isProper_hom_of_fppfHomogeneousQuotientScheme_of_le`). Neither hypothesis on `Y` can be
   omitted for general surjective `R`-scheme morphisms from a proper source:
   `Spec k ⟶ Spec (k[x₀, x₁, …]/(xᵢ xⱼ))` has non-locally-of-finite-type target, while the map
   from `ℙ¹_k ⊔ ℙ¹_k` onto the projective line with doubled origin has non-separated target.
4. **Left translations and equivariance.** Ground-ring points `g ∈ G(R)` act on `X` by `R`-scheme
   automorphisms (`fppfHomogeneousQuotientSchemeTranslation eI g`) that intertwine coordinate left
   translation `HopfAlgebra.leftTranslationAlgEquiv g` on `Spec H` and commute with the
   projections `X ⟶ Y` induced by subgroup inclusions.
5. **Rational points over an algebraically closed field.** When `R = k` is an algebraically closed
   field, `k`-rational points of `X` over `Spec k` are in canonical bijection with the left coset
   space `G(k)/N(k)` (`fppfHomogeneousQuotientSchemeRationalPointsEquiv`), compatibly with
   subgroup projections and left translation.

No reducedness, smoothness, normality, or finite-type hypotheses are imposed on `G` or `N`
anywhere in this file; the rational-points section adds only `[Field k] [IsAlgClosed k]`, and the
properness descent theorem imposes `[UniversallyClosed X.hom]`, `[IsSeparated Y.hom]`, and
`[LocallyOfFiniteType Y.hom]` on the representing schemes. The ambient group scheme is written as
`(Spec H).asOver (Spec R)`, matching `Spec.mapMulEquiv` directly.

## Main declarations

* `TauCeti.CommHopfAlgCat.fppfHomogeneousQuotientSchemeProjection`: the quotient morphism `G ⟶ X`
  over `Spec R` associated to a representation `fppfHomogeneousQuotient H I ≅ pointsSheaf X`.
* `TauCeti.CommHopfAlgCat.fppfHomogeneousQuotientSchemeHomEquiv`: universal property of a scheme
  representing `G/N` with respect to arbitrary `R`-schemes (Milne, Proposition 5.22).
* `TauCeti.CommHopfAlgCat.fppfHomogeneousQuotientSchemeIso`: canonical isomorphism between any
  two schemes representing `G/N` over `Spec R`.
* `TauCeti.CommHopfAlgCat.fppfHomogeneousQuotientSchemeMap`: the surjective `R`-scheme morphism
  `G/N₁ ⟶ G/N₂` under `G` (commuting with left translation by `R`-points `G(R)`) induced by an
  inclusion `J ≤ I` of defining Hopf ideals.
* `TauCeti.CommHopfAlgCat.morphismProperty_hom_iff_of_fppfHomogeneousQuotientScheme`: any
  isomorphism-respecting morphism property of a representing scheme depends only on `G/N`.
* `TauCeti.CommHopfAlgCat.universallyClosed_hom_of_fppfHomogeneousQuotientScheme_of_le` and
  `TauCeti.CommHopfAlgCat.isProper_hom_of_fppfHomogeneousQuotientScheme_of_le`: universal
  closedness of `G/N₁` over `Spec R` descends to `G/N₂`, giving properness of any separated,
  locally of finite type representing scheme `G/N₂`.
* `TauCeti.CommHopfAlgCat.fppfHomogeneousQuotientSchemeTranslation`: left-translation
  automorphisms of `X` by `R`-points of `G`.
* `TauCeti.CommHopfAlgCat.fppfHomogeneousQuotientSchemeRationalPointsEquiv`: the bijection
  `G(k)/N(k) ≃ ((Spec k).asOver (Spec k) ⟶ X)` over an algebraically closed field `k`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 5, Proposition 5.22 and §5.d.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite WithConv
open scoped CategoryTheory.MonObj

namespace TauCeti.CommHopfAlgCat

open TauCeti _root_.CommHopfAlgCat

universe u

noncomputable section

section UniversalProperty

variable {R : Type u} [CommRing R] {H : _root_.CommHopfAlgCat.{u} R}
variable {I : HopfIdeal R H} {X : Over (Spec (CommRingCat.of R))}

/-- **The quotient morphism `G ⟶ X` to a scheme representing `G/N`.** Given an isomorphism
`eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X`, this is the unique morphism
`(Spec H).asOver (Spec R) ⟶ X` inducing the composite `G ⟶ G/N ≅ X` on affine fppf points. -/
def fppfHomogeneousQuotientSchemeProjection
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X) :
    (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)) ⟶ X :=
  (specAsOverHomEquivPointsPresheafHom H X).symm
    (fppfHomogeneousQuotientProjection H I ≫ eI.hom.hom)

/-- Under `specAsOverHomEquivPointsPresheafHom`, the scheme projection `G ⟶ X` corresponds to the
quotient projection `G ⟶ G/N` followed by `eI.hom`. -/
@[simp]
theorem specAsOverHomEquivPointsPresheafHom_fppfHomogeneousQuotientSchemeProjection
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X) :
    specAsOverHomEquivPointsPresheafHom H X (fppfHomogeneousQuotientSchemeProjection eI) =
      fppfHomogeneousQuotientProjection H I ≫ eI.hom.hom :=
  (specAsOverHomEquivPointsPresheafHom H X).apply_symm_apply _

/-- The induced map of `fppfHomogeneousQuotientSchemeProjection` on affine points intertwines
`pointsPresheafUliftIsoPointsSheaf` with `fppfHomogeneousQuotientProjection ≫ eI.hom`. -/
@[reassoc]
theorem pointsPresheafUliftIsoPointsSheaf_hom_comp_fppfHomogeneousQuotientSchemeProjection
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X) :
    (pointsPresheafUliftIsoPointsSheaf H).hom ≫
        (CommAlgCat.pointsSheafMap (fppfHomogeneousQuotientSchemeProjection eI)).hom =
      fppfHomogeneousQuotientProjection H I ≫ eI.hom.hom :=
  (specAsOverHomEquivPointsPresheafHom_apply H X _).symm.trans
    (specAsOverHomEquivPointsPresheafHom_fppfHomogeneousQuotientSchemeProjection eI)

/-- On an `A`-point `g` of `G`, postcomposing `Spec.mapMulEquiv g` with the scheme projection
`G ⟶ X` agrees with applying `eI.hom` to the projected coset section of `g`. -/
theorem mapMulEquiv_comp_fppfHomogeneousQuotientSchemeProjection
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    {A : CommAlgCat.{u} R} (g : HopfAlgebra.points (R := R) (H := H) A) :
    ULift.up (Spec.mapMulEquiv g ≫ fppfHomogeneousQuotientSchemeProjection eI) =
      eI.hom.hom.app (op (op A))
        ((fppfHomogeneousQuotientProjection H I).app (op (op A)) (ULift.up g)) := by
  have h := congrArg (fun α ↦ α.app (op (op A)) (ULift.up g))
    (specAsOverHomEquivPointsPresheafHom_fppfHomogeneousQuotientSchemeProjection eI)
  exact (specAsOverHomEquivPointsPresheafHom_apply_app_apply H X
    (fppfHomogeneousQuotientSchemeProjection eI) A g).symm.trans h

/-- **Right `N`-invariance of the scheme quotient projection.** Multiplying an `A`-point of `G`
on the right by an `A`-point of the closed subgroup `N` leaves its image in `X` unchanged. -/
@[reassoc]
theorem mapMulEquiv_mul_comp_fppfHomogeneousQuotientSchemeProjection
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    {A : CommAlgCat.{u} R} (g : HopfAlgebra.points (R := R) (H := H) A)
    (n : quotientPointsSubgroup H I A) :
    Spec.mapMulEquiv (g * n.val) ≫ fppfHomogeneousQuotientSchemeProjection eI =
      Spec.mapMulEquiv g ≫ fppfHomogeneousQuotientSchemeProjection eI := by
  apply ULift.up_inj.mp
  have h := (fppfHomogeneousQuotientHomEquiv H I _ eI.hom).property (op (op A)) g n
  rw [fppfHomogeneousQuotientHomEquiv_apply] at h
  exact (mapMulEquiv_comp_fppfHomogeneousQuotientSchemeProjection eI (g * n.val)).trans
    (h.trans (mapMulEquiv_comp_fppfHomogeneousQuotientSchemeProjection eI g).symm)

/-- Two `A`-points of `G` have the same image under `G ⟶ X` precisely when they have the same
image in the fppf homogeneous quotient `G/N`. -/
theorem mapMulEquiv_comp_fppfHomogeneousQuotientSchemeProjection_eq_iff
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    {A : CommAlgCat.{u} R} (g g' : HopfAlgebra.points (R := R) (H := H) A) :
    Spec.mapMulEquiv g ≫ fppfHomogeneousQuotientSchemeProjection eI =
        Spec.mapMulEquiv g' ≫ fppfHomogeneousQuotientSchemeProjection eI ↔
      (fppfHomogeneousQuotientProjection H I).app (op (op A)) (ULift.up g) =
        (fppfHomogeneousQuotientProjection H I).app (op (op A)) (ULift.up g') := by
  have heI : IsIso (eI.hom.hom.app (op (op A))) :=
    inferInstanceAs (IsIso (((sheafToPresheaf _ _).map eI.hom).app (op (op A))))
  refine ⟨fun h ↦ (ConcreteCategory.bijective_of_isIso (eI.hom.hom.app (op (op A)))).injective ?_,
    fun h ↦ ULift.up_inj.mp ?_⟩
  · exact (mapMulEquiv_comp_fppfHomogeneousQuotientSchemeProjection eI g).symm.trans
      ((congrArg ULift.up h).trans
        (mapMulEquiv_comp_fppfHomogeneousQuotientSchemeProjection eI g'))
  · exact (mapMulEquiv_comp_fppfHomogeneousQuotientSchemeProjection eI g).trans
      ((congrArg (eI.hom.hom.app (op (op A))) h).trans
        (mapMulEquiv_comp_fppfHomogeneousQuotientSchemeProjection eI g').symm)

/-- **The scheme quotient projection is fppf locally surjective on affine points.** -/
instance isLocallySurjective_pointsSheafMap_fppfHomogeneousQuotientSchemeProjection
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X) :
    Presheaf.IsLocallySurjective (CommAlgCat.fppfTopology R)
      (CommAlgCat.pointsSheafMap (fppfHomogeneousQuotientSchemeProjection eI)).hom := by
  have : IsIso eI.hom.hom := inferInstanceAs (IsIso ((sheafToPresheaf _ _).map eI.hom))
  have : Presheaf.IsLocallySurjective (CommAlgCat.fppfTopology R)
      (fppfHomogeneousQuotientProjection H I ≫ eI.hom.hom) :=
    Presheaf.isLocallySurjective_comp (CommAlgCat.fppfTopology R)
      (fppfHomogeneousQuotientProjection H I) eI.hom.hom
  exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac (CommAlgCat.fppfTopology R)
    (pointsPresheafUliftIsoPointsSheaf_hom_comp_fppfHomogeneousQuotientSchemeProjection eI)

/-- **The scheme quotient projection `G ⟶ X` is an epimorphism in `Over (Spec R)`.** -/
instance epi_fppfHomogeneousQuotientSchemeProjection
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X) :
    Epi (fppfHomogeneousQuotientSchemeProjection eI) :=
  CommAlgCat.epi_of_isLocallySurjective_pointsSheafMap _

/-- **The scheme quotient projection `G ⟶ X` is surjective on underlying schemes.** -/
instance surjective_fppfHomogeneousQuotientSchemeProjection_left
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X) :
    Surjective (fppfHomogeneousQuotientSchemeProjection eI).left :=
  CommAlgCat.surjective_left_of_isLocallySurjective_pointsSheafMap _

/-- Morphisms out of a scheme `X` representing `G/N` over `Spec R` are determined by their
composites with `fppfHomogeneousQuotientSchemeProjection eI : G ⟶ X`. -/
theorem fppfHomogeneousQuotientScheme_hom_ext
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    {Y : Over (Spec (CommRingCat.of R))} {f₁ f₂ : X ⟶ Y}
    (h : fppfHomogeneousQuotientSchemeProjection eI ≫ f₁ =
      fppfHomogeneousQuotientSchemeProjection eI ≫ f₂) :
    f₁ = f₂ :=
  (cancel_epi (fppfHomogeneousQuotientSchemeProjection eI)).mp h

private theorem comp_homEquiv_symm_aux
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    {Y : Over (Spec (CommRingCat.of R))}
    (q : {q : (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)) ⟶ Y //
      ∀ (A : CommAlgCat.{u} R) (g : HopfAlgebra.points (R := R) (H := H) A)
        (n : quotientPointsSubgroup H I A),
        Spec.mapMulEquiv (g * n.val) ≫ q = Spec.mapMulEquiv g ≫ q}) :
    fppfHomogeneousQuotientSchemeProjection eI ≫
        (CommAlgCat.pointsSheafHomEquiv X Y).symm
          (eI.inv ≫
            (fppfHomogeneousQuotientHomEquiv H I (CommAlgCat.pointsSheaf Y)).symm
              ⟨specAsOverHomEquivPointsPresheafHom H Y q.val, fun ⟨⟨A⟩⟩ g n ↦ by
                rw [specAsOverHomEquivPointsPresheafHom_apply_app_apply,
                  specAsOverHomEquivPointsPresheafHom_apply_app_apply]
                exact congrArg ULift.up (q.property A g n)⟩) =
      q.val := by
  apply (specAsOverHomEquivPointsPresheafHom H Y).injective
  simp [specAsOverHomEquivPointsPresheafHom_comp]

/-- **Universal property of a scheme representing `G/N` (Milne, Proposition 5.22).** For every
scheme `Y` over `Spec R`, morphisms `X ⟶ Y` over `Spec R` correspond bijectively to morphisms
`(Spec H).asOver (Spec R) ⟶ Y` that are invariant under right multiplication by `N(A)` on
`A`-points for all commutative `R`-algebras `A`. -/
def fppfHomogeneousQuotientSchemeHomEquiv
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (Y : Over (Spec (CommRingCat.of R))) :
    (X ⟶ Y) ≃
      {q : (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)) ⟶ Y //
        ∀ (A : CommAlgCat.{u} R) (g : HopfAlgebra.points (R := R) (H := H) A)
          (n : quotientPointsSubgroup H I A),
          Spec.mapMulEquiv (g * n.val) ≫ q = Spec.mapMulEquiv g ≫ q} where
  toFun f :=
    ⟨fppfHomogeneousQuotientSchemeProjection eI ≫ f, fun _ g n ↦ by
      rw [← Category.assoc, mapMulEquiv_mul_comp_fppfHomogeneousQuotientSchemeProjection,
        Category.assoc]⟩
  invFun q :=
    (CommAlgCat.pointsSheafHomEquiv X Y).symm
      (eI.inv ≫
        (fppfHomogeneousQuotientHomEquiv H I (CommAlgCat.pointsSheaf Y)).symm
          ⟨specAsOverHomEquivPointsPresheafHom H Y q.val, fun ⟨⟨A⟩⟩ g n ↦ by
            rw [specAsOverHomEquivPointsPresheafHom_apply_app_apply,
              specAsOverHomEquivPointsPresheafHom_apply_app_apply]
            exact congrArg ULift.up (q.property A g n)⟩)
  left_inv f := fppfHomogeneousQuotientScheme_hom_ext eI (comp_homEquiv_symm_aux eI _)
  right_inv q := Subtype.ext (comp_homEquiv_symm_aux eI q)

/-- The universal property sends `f : X ⟶ Y` to its precomposition with the quotient projection
`G ⟶ X`. -/
@[simp]
theorem fppfHomogeneousQuotientSchemeHomEquiv_apply_coe
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y) :
    (fppfHomogeneousQuotientSchemeHomEquiv eI Y f).val =
      fppfHomogeneousQuotientSchemeProjection eI ≫ f :=
  (rfl)

/-- Descending a right-`N`-invariant morphism `q : G ⟶ Y` to `X ⟶ Y` and precomposing with the
quotient projection `G ⟶ X` recovers `q`. -/
@[reassoc (attr := simp)]
theorem fppfHomogeneousQuotientSchemeProjection_comp_homEquiv_symm
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (Y : Over (Spec (CommRingCat.of R)))
    (q : {q : (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)) ⟶ Y //
      ∀ (A : CommAlgCat.{u} R) (g : HopfAlgebra.points (R := R) (H := H) A)
        (n : quotientPointsSubgroup H I A),
        Spec.mapMulEquiv (g * n.val) ≫ q = Spec.mapMulEquiv g ≫ q}) :
    fppfHomogeneousQuotientSchemeProjection eI ≫
        (fppfHomogeneousQuotientSchemeHomEquiv eI Y).symm q =
      q.val :=
  comp_homEquiv_symm_aux eI q

end UniversalProperty

section SubgroupMaps

variable {R : Type u} [CommRing R] {H : _root_.CommHopfAlgCat.{u} R}

/-- **Canonical uniqueness of a scheme representing `G/N`.** Any two schemes `X` and `X'` over
`Spec R` representing `fppfHomogeneousQuotient H I` are canonically isomorphic over `Spec R`. -/
def fppfHomogeneousQuotientSchemeIso {I : HopfIdeal R H}
    {X X' : Over (Spec (CommRingCat.of R))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eI' : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X') :
    X ≅ X' :=
  (CommAlgCat.pointsSheafIsoEquiv X X').symm (eI.symm ≪≫ eI')

/-- On affine fppf points, the forward morphism of `fppfHomogeneousQuotientSchemeIso eI eI'`
induces `eI.inv ≫ eI'.hom`. -/
@[simp]
theorem pointsSheafMap_fppfHomogeneousQuotientSchemeIso_hom {I : HopfIdeal R H}
    {X X' : Over (Spec (CommRingCat.of R))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eI' : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X') :
    CommAlgCat.pointsSheafMap (fppfHomogeneousQuotientSchemeIso eI eI').hom =
      eI.inv ≫ eI'.hom := by
  simp [fppfHomogeneousQuotientSchemeIso]

/-- On affine fppf points, the inverse morphism of `fppfHomogeneousQuotientSchemeIso eI eI'`
induces `eI'.inv ≫ eI.hom`. -/
@[simp]
theorem pointsSheafMap_fppfHomogeneousQuotientSchemeIso_inv {I : HopfIdeal R H}
    {X X' : Over (Spec (CommRingCat.of R))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eI' : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X') :
    CommAlgCat.pointsSheafMap (fppfHomogeneousQuotientSchemeIso eI eI').inv =
      eI'.inv ≫ eI.hom := by
  simp [fppfHomogeneousQuotientSchemeIso]

/-- The canonical isomorphism between two schemes representing `G/N` commutes with the quotient
projections from `G`. -/
@[reassoc (attr := simp)]
theorem fppfHomogeneousQuotientSchemeProjection_comp_iso_hom {I : HopfIdeal R H}
    {X X' : Over (Spec (CommRingCat.of R))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eI' : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X') :
    fppfHomogeneousQuotientSchemeProjection eI ≫
        (fppfHomogeneousQuotientSchemeIso eI eI').hom =
      fppfHomogeneousQuotientSchemeProjection eI' := by
  apply (specAsOverHomEquivPointsPresheafHom H X').injective
  simp [specAsOverHomEquivPointsPresheafHom_comp]

/-- The inverse of the canonical isomorphism between two schemes representing `G/N` commutes with
the quotient projections from `G`. -/
@[reassoc (attr := simp)]
theorem fppfHomogeneousQuotientSchemeProjection_comp_iso_inv {I : HopfIdeal R H}
    {X X' : Over (Spec (CommRingCat.of R))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eI' : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X') :
    fppfHomogeneousQuotientSchemeProjection eI' ≫
        (fppfHomogeneousQuotientSchemeIso eI eI').inv =
      fppfHomogeneousQuotientSchemeProjection eI := by
  apply (specAsOverHomEquivPointsPresheafHom H X).injective
  simp [specAsOverHomEquivPointsPresheafHom_comp]

/-- Comparing a representation of `G/N` with itself yields `Iso.refl`. -/
@[simp]
theorem fppfHomogeneousQuotientSchemeIso_refl {I : HopfIdeal R H}
    {X : Over (Spec (CommRingCat.of R))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X) :
    fppfHomogeneousQuotientSchemeIso eI eI = Iso.refl X := by
  ext1
  apply fppfHomogeneousQuotientScheme_hom_ext eI
  simp

/-- Swapping the two representations of `G/N` inverts `fppfHomogeneousQuotientSchemeIso`. -/
theorem fppfHomogeneousQuotientSchemeIso_symm {I : HopfIdeal R H}
    {X X' : Over (Spec (CommRingCat.of R))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eI' : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X') :
    fppfHomogeneousQuotientSchemeIso eI' eI =
      (fppfHomogeneousQuotientSchemeIso eI eI').symm := by
  ext1
  apply fppfHomogeneousQuotientScheme_hom_ext eI'
  simp

/-- Canonical isomorphisms between schemes representing `G/N` compose transitively. -/
@[simp]
theorem fppfHomogeneousQuotientSchemeIso_trans {I : HopfIdeal R H}
    {X₁ X₂ X₃ : Over (Spec (CommRingCat.of R))}
    (e₁ : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X₁)
    (e₂ : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X₂)
    (e₃ : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X₃) :
    fppfHomogeneousQuotientSchemeIso e₁ e₂ ≪≫ fppfHomogeneousQuotientSchemeIso e₂ e₃ =
      fppfHomogeneousQuotientSchemeIso e₁ e₃ := by
  ext1
  apply fppfHomogeneousQuotientScheme_hom_ext e₁
  simp

/-- **The `R`-scheme morphism `G/N₁ ⟶ G/N₂` induced by an inclusion of closed subgroups.** Given
Hopf ideals `J ≤ I` (cutting out closed subgroups `N₁ ⊆ N₂`) and schemes `X`, `Y` over `Spec R`
representing `G/N₁`, `G/N₂`, this is the unique morphism `X ⟶ Y` over `Spec R` transporting
`fppfHomogeneousQuotientMap H hJI` across `eI` and `eJ`. -/
def fppfHomogeneousQuotientSchemeMap {I J : HopfIdeal R H}
    {X Y : Over (Spec (CommRingCat.of R))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eJ : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y)
    (hJI : J ≤ I) : X ⟶ Y :=
  (CommAlgCat.pointsSheafHomEquiv X Y).symm
    (eI.inv ≫ fppfHomogeneousQuotientMap H hJI ≫ eJ.hom)

/-- On affine fppf points, `fppfHomogeneousQuotientSchemeMap eI eJ hJI` induces
`eI.inv ≫ fppfHomogeneousQuotientMap H hJI ≫ eJ.hom`. -/
@[simp]
theorem pointsSheafMap_fppfHomogeneousQuotientSchemeMap {I J : HopfIdeal R H}
    {X Y : Over (Spec (CommRingCat.of R))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eJ : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y)
    (hJI : J ≤ I) :
    CommAlgCat.pointsSheafMap (fppfHomogeneousQuotientSchemeMap eI eJ hJI) =
      eI.inv ≫ fppfHomogeneousQuotientMap H hJI ≫ eJ.hom :=
  CommAlgCat.pointsSheafMap_pointsSheafHomEquiv_symm _

/-- Precomposing the induced sheaf map of `fppfHomogeneousQuotientSchemeMap` with `eI.hom` gives
`fppfHomogeneousQuotientMap H hJI ≫ eJ.hom`. -/
@[reassoc]
theorem hom_comp_pointsSheafMap_fppfHomogeneousQuotientSchemeMap {I J : HopfIdeal R H}
    {X Y : Over (Spec (CommRingCat.of R))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eJ : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y)
    (hJI : J ≤ I) :
    eI.hom ≫ CommAlgCat.pointsSheafMap (fppfHomogeneousQuotientSchemeMap eI eJ hJI) =
      fppfHomogeneousQuotientMap H hJI ≫ eJ.hom := by
  rw [pointsSheafMap_fppfHomogeneousQuotientSchemeMap, Iso.hom_inv_id_assoc]

/-- **Subgroup projections commute with the quotient morphisms from `G`.** -/
@[reassoc (attr := simp)]
theorem fppfHomogeneousQuotientSchemeProjection_comp_map {I J : HopfIdeal R H}
    {X Y : Over (Spec (CommRingCat.of R))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eJ : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y)
    (hJI : J ≤ I) :
    fppfHomogeneousQuotientSchemeProjection eI ≫
        fppfHomogeneousQuotientSchemeMap eI eJ hJI =
      fppfHomogeneousQuotientSchemeProjection eJ := by
  apply (specAsOverHomEquivPointsPresheafHom H Y).injective
  simp [specAsOverHomEquivPointsPresheafHom_comp]

/-- On underlying schemes, `fppfHomogeneousQuotientSchemeMap` commutes with the structure morphisms
to `Spec R`. -/
@[reassoc]
theorem fppfHomogeneousQuotientSchemeMap_w {I J : HopfIdeal R H}
    {X Y : Over (Spec (CommRingCat.of R))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eJ : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y)
    (hJI : J ≤ I) :
    (fppfHomogeneousQuotientSchemeMap eI eJ hJI).left ≫ Y.hom = X.hom :=
  Over.w _

/-- `fppfHomogeneousQuotientSchemeMap eI eJ hJI` is the unique `R`-scheme morphism `X ⟶ Y`
compatible with the quotient projections from `G`. -/
theorem fppfHomogeneousQuotientSchemeMap_eq_iff {I J : HopfIdeal R H}
    {X Y : Over (Spec (CommRingCat.of R))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eJ : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y)
    (hJI : J ≤ I) (f : X ⟶ Y) :
    f = fppfHomogeneousQuotientSchemeMap eI eJ hJI ↔
      fppfHomogeneousQuotientSchemeProjection eI ≫ f =
        fppfHomogeneousQuotientSchemeProjection eJ := by
  refine ⟨fun h ↦ h ▸ fppfHomogeneousQuotientSchemeProjection_comp_map eI eJ hJI, fun h ↦ ?_⟩
  exact fppfHomogeneousQuotientScheme_hom_ext eI
    (h.trans (fppfHomogeneousQuotientSchemeProjection_comp_map eI eJ hJI).symm)

/-- For `le_refl I` and a single representation `eI`, the induced scheme map is the identity. -/
@[simp]
theorem fppfHomogeneousQuotientSchemeMap_refl {I : HopfIdeal R H}
    {X : Over (Spec (CommRingCat.of R))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X) :
    fppfHomogeneousQuotientSchemeMap eI eI (le_refl I) = 𝟙 X := by
  apply fppfHomogeneousQuotientScheme_hom_ext eI
  simp

/-- For `le_refl I` and two representations `eI`, `eI'`, the induced scheme map is the canonical
isomorphism `fppfHomogeneousQuotientSchemeIso eI eI'`. -/
theorem fppfHomogeneousQuotientSchemeMap_self {I : HopfIdeal R H}
    {X X' : Over (Spec (CommRingCat.of R))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eI' : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X') :
    fppfHomogeneousQuotientSchemeMap eI eI' (le_refl I) =
      (fppfHomogeneousQuotientSchemeIso eI eI').hom := by
  apply fppfHomogeneousQuotientScheme_hom_ext eI
  simp

/-- **Functoriality of subgroup-induced scheme maps.** Projections between representing schemes
compose along chains `K ≤ J ≤ I` of defining Hopf ideals. -/
@[reassoc (attr := simp)]
theorem fppfHomogeneousQuotientSchemeMap_comp {I J K : HopfIdeal R H}
    {X Y Z : Over (Spec (CommRingCat.of R))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eJ : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y)
    (eK : fppfHomogeneousQuotient H K ≅ CommAlgCat.pointsSheaf Z)
    (hJI : J ≤ I) (hKJ : K ≤ J) :
    fppfHomogeneousQuotientSchemeMap eI eJ hJI ≫
        fppfHomogeneousQuotientSchemeMap eJ eK hKJ =
      fppfHomogeneousQuotientSchemeMap eI eK (hKJ.trans hJI) := by
  apply fppfHomogeneousQuotientScheme_hom_ext eI
  simp

/-- **Subgroup-induced scheme projections are fppf locally surjective on affine points.** -/
instance isLocallySurjective_pointsSheafMap_fppfHomogeneousQuotientSchemeMap
    {I J : HopfIdeal R H} {X Y : Over (Spec (CommRingCat.of R))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eJ : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y)
    (hJI : J ≤ I) :
    Presheaf.IsLocallySurjective (CommAlgCat.fppfTopology R)
      (CommAlgCat.pointsSheafMap (fppfHomogeneousQuotientSchemeMap eI eJ hJI)).hom := by
  have : IsIso eI.inv.hom := inferInstanceAs (IsIso ((sheafToPresheaf _ _).map eI.inv))
  have : IsIso eJ.hom.hom := inferInstanceAs (IsIso ((sheafToPresheaf _ _).map eJ.hom))
  rw [pointsSheafMap_fppfHomogeneousQuotientSchemeMap,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom]
  have := Presheaf.isLocallySurjective_comp (CommAlgCat.fppfTopology R)
    (fppfHomogeneousQuotientMap H hJI).hom eJ.hom.hom
  exact Presheaf.isLocallySurjective_comp (CommAlgCat.fppfTopology R) eI.inv.hom _

/-- **Subgroup-induced scheme projections `G/N₁ ⟶ G/N₂` are epimorphisms in `Over (Spec R)`.** -/
instance epi_fppfHomogeneousQuotientSchemeMap {I J : HopfIdeal R H}
    {X Y : Over (Spec (CommRingCat.of R))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eJ : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y)
    (hJI : J ≤ I) :
    Epi (fppfHomogeneousQuotientSchemeMap eI eJ hJI) :=
  CommAlgCat.epi_of_isLocallySurjective_pointsSheafMap _

/-- **Subgroup-induced scheme projections `G/N₁ ⟶ G/N₂` are surjective on underlying schemes.** -/
instance surjective_fppfHomogeneousQuotientSchemeMap_left {I J : HopfIdeal R H}
    {X Y : Over (Spec (CommRingCat.of R))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eJ : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y)
    (hJI : J ≤ I) :
    Surjective (fppfHomogeneousQuotientSchemeMap eI eJ hJI).left :=
  CommAlgCat.surjective_left_of_isLocallySurjective_pointsSheafMap _

/-- **Isomorphism-invariant morphism properties depend only on the homogeneous quotient.** For any
isomorphism-respecting morphism property `P` of schemes, two schemes representing the same fppf
homogeneous quotient `G/N` over `Spec R` have equivalent `P` on their structure morphisms. -/
theorem morphismProperty_hom_iff_of_fppfHomogeneousQuotientScheme
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso] {I : HopfIdeal R H}
    {X X' : Over (Spec (CommRingCat.of R))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eI' : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X') :
    P X.hom ↔ P X'.hom :=
  P.comma_iso_iff (fppfHomogeneousQuotientSchemeIso eI eI')

/-- **Properness of a representing scheme depends only on the homogeneous quotient.** Two schemes
representing the same fppf homogeneous quotient `G/N` over `Spec R` have equivalent properness
over `Spec R`. -/
theorem isProper_hom_iff_of_fppfHomogeneousQuotientScheme {I : HopfIdeal R H}
    {X X' : Over (Spec (CommRingCat.of R))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eI' : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X') :
    IsProper X.hom ↔ IsProper X'.hom :=
  morphismProperty_hom_iff_of_fppfHomogeneousQuotientScheme @IsProper eI eI'

/-- **Universal closedness descends to quotients by larger closed subgroups.** Let `J ≤ I` be Hopf
ideals (cutting out closed subgroups `N₁ ⊆ N₂`) and let `X`, `Y` be schemes over `Spec R`
representing `G/N₁`, `G/N₂`. If `X` is universally closed over `Spec R`, then so is `Y`, without
separatedness or finite-type hypotheses on `X` or `Y`. -/
theorem universallyClosed_hom_of_fppfHomogeneousQuotientScheme_of_le {I J : HopfIdeal R H}
    {X Y : Over (Spec (CommRingCat.of R))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eJ : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y)
    (hJI : J ≤ I) [UniversallyClosed X.hom] :
    UniversallyClosed Y.hom := by
  have : UniversallyClosed ((fppfHomogeneousQuotientSchemeMap eI eJ hJI).left ≫ Y.hom) := by
    rw [fppfHomogeneousQuotientSchemeMap_w]
    infer_instance
  exact UniversallyClosed.of_comp_surjective
    (fppfHomogeneousQuotientSchemeMap eI eJ hJI).left Y.hom

/-- **Properness descends to quotients by larger closed subgroups.** Let `J ≤ I` be Hopf ideals
(cutting out closed subgroups `N₁ ⊆ N₂`) and let `X`, `Y` be schemes over `Spec R` representing
`G/N₁`, `G/N₂`. If `X` is universally closed (in particular, proper) over `Spec R` and `Y` is
separated and locally of finite type over `Spec R`, then `Y` is proper over `Spec R`. -/
theorem isProper_hom_of_fppfHomogeneousQuotientScheme_of_le {I J : HopfIdeal R H}
    {X Y : Over (Spec (CommRingCat.of R))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eJ : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y)
    (hJI : J ≤ I) [UniversallyClosed X.hom] [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] :
    IsProper Y.hom := by
  have : UniversallyClosed Y.hom :=
    universallyClosed_hom_of_fppfHomogeneousQuotientScheme_of_le eI eJ hJI
  exact ⟨⟩

end SubgroupMaps

section Translation

variable {R : Type u} [CommRing R] {H : _root_.CommHopfAlgCat.{u} R}

/-- **Left translation on a scheme representing `G/N` by an `R`-valued point of `G`.** This
transports `fppfHomogeneousQuotientTranslation H I g` across `eI`. -/
def fppfHomogeneousQuotientSchemeTranslation {I : HopfIdeal R H}
    {X : Over (Spec (CommRingCat.of R))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    X ≅ X :=
  (CommAlgCat.pointsSheafIsoEquiv X X).symm
    (eI.symm ≪≫ fppfHomogeneousQuotientTranslation H I g ≪≫ eI)

/-- On affine fppf points, the forward morphism of `fppfHomogeneousQuotientSchemeTranslation eI g`
induces the conjugate of `(fppfHomogeneousQuotientTranslation H I g).hom` by `eI`. -/
@[simp]
theorem pointsSheafMap_fppfHomogeneousQuotientSchemeTranslation_hom {I : HopfIdeal R H}
    {X : Over (Spec (CommRingCat.of R))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    CommAlgCat.pointsSheafMap (fppfHomogeneousQuotientSchemeTranslation eI g).hom =
      eI.inv ≫ (fppfHomogeneousQuotientTranslation H I g).hom ≫ eI.hom := by
  rw [fppfHomogeneousQuotientSchemeTranslation, CommAlgCat.pointsSheafIsoEquiv_symm_hom,
    CommAlgCat.pointsSheafMap_pointsSheafHomEquiv_symm]
  simp only [Iso.trans_hom, Iso.symm_hom]

/-- On affine fppf points, the inverse morphism of `fppfHomogeneousQuotientSchemeTranslation eI g`
induces the conjugate of `(fppfHomogeneousQuotientTranslation H I g).inv` by `eI`. -/
@[simp]
theorem pointsSheafMap_fppfHomogeneousQuotientSchemeTranslation_inv {I : HopfIdeal R H}
    {X : Over (Spec (CommRingCat.of R))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    CommAlgCat.pointsSheafMap (fppfHomogeneousQuotientSchemeTranslation eI g).inv =
      eI.inv ≫ (fppfHomogeneousQuotientTranslation H I g).inv ≫ eI.hom := by
  rw [fppfHomogeneousQuotientSchemeTranslation, CommAlgCat.pointsSheafIsoEquiv_symm_inv,
    CommAlgCat.pointsSheafMap_pointsSheafHomEquiv_symm]
  simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc]

/-- Precomposing the induced forward sheaf map of `fppfHomogeneousQuotientSchemeTranslation` with
`eI.hom` intertwines `fppfHomogeneousQuotientTranslation`. -/
@[reassoc]
theorem hom_comp_pointsSheafMap_fppfHomogeneousQuotientSchemeTranslation_hom
    {I : HopfIdeal R H} {X : Over (Spec (CommRingCat.of R))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    eI.hom ≫ CommAlgCat.pointsSheafMap (fppfHomogeneousQuotientSchemeTranslation eI g).hom =
      (fppfHomogeneousQuotientTranslation H I g).hom ≫ eI.hom := by
  rw [pointsSheafMap_fppfHomogeneousQuotientSchemeTranslation_hom, Iso.hom_inv_id_assoc]

/-- Precomposing the induced inverse sheaf map of `fppfHomogeneousQuotientSchemeTranslation` with
`eI.hom` intertwines `(fppfHomogeneousQuotientTranslation H I g).inv`. -/
@[reassoc]
theorem hom_comp_pointsSheafMap_fppfHomogeneousQuotientSchemeTranslation_inv
    {I : HopfIdeal R H} {X : Over (Spec (CommRingCat.of R))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    eI.hom ≫ CommAlgCat.pointsSheafMap (fppfHomogeneousQuotientSchemeTranslation eI g).inv =
      (fppfHomogeneousQuotientTranslation H I g).inv ≫ eI.hom := by
  rw [pointsSheafMap_fppfHomogeneousQuotientSchemeTranslation_inv, Iso.hom_inv_id_assoc]

/-- Left translation by the identity `R`-point is the identity scheme automorphism. -/
@[simp]
theorem fppfHomogeneousQuotientSchemeTranslation_one {I : HopfIdeal R H}
    {X : Over (Spec (CommRingCat.of R))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X) :
    fppfHomogeneousQuotientSchemeTranslation eI 1 = Iso.refl X := by
  simp [fppfHomogeneousQuotientSchemeTranslation]

/-- Left translations on `X` compose in left-action order, matching
`fppfHomogeneousQuotientTranslation_mul`. -/
@[simp]
theorem fppfHomogeneousQuotientSchemeTranslation_mul {I : HopfIdeal R H}
    {X : Over (Spec (CommRingCat.of R))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (g h : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    fppfHomogeneousQuotientSchemeTranslation eI (g * h) =
      fppfHomogeneousQuotientSchemeTranslation eI h ≪≫
        fppfHomogeneousQuotientSchemeTranslation eI g := by
  ext1
  apply (CommAlgCat.pointsSheafHomEquiv X X).injective
  rw [fppfHomogeneousQuotientSchemeTranslation, fppfHomogeneousQuotientTranslation_mul]
  simp

/-- Left translation by `g⁻¹` is the inverse scheme isomorphism. -/
@[simp]
theorem fppfHomogeneousQuotientSchemeTranslation_inv {I : HopfIdeal R H}
    {X : Over (Spec (CommRingCat.of R))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    fppfHomogeneousQuotientSchemeTranslation eI g⁻¹ =
      (fppfHomogeneousQuotientSchemeTranslation eI g).symm := by
  ext1
  rw [fppfHomogeneousQuotientSchemeTranslation, fppfHomogeneousQuotientSchemeTranslation,
    fppfHomogeneousQuotientTranslation_inv, Iso.symm_hom,
    CommAlgCat.pointsSheafIsoEquiv_symm_hom, CommAlgCat.pointsSheafIsoEquiv_symm_inv]
  congr 1

/-- On projected `A`-points of `G`, left translation on `X` multiplies the group point on the left
by `HopfAlgebra.extendPoint H A g`. -/
theorem mapMulEquiv_comp_fppfHomogeneousQuotientSchemeTranslation_hom {I : HopfIdeal R H}
    {X : Over (Spec (CommRingCat.of R))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    {A : CommAlgCat.{u} R} (x : HopfAlgebra.points (R := R) (H := H) A) :
    Spec.mapMulEquiv x ≫ fppfHomogeneousQuotientSchemeProjection eI ≫
        (fppfHomogeneousQuotientSchemeTranslation eI g).hom =
      Spec.mapMulEquiv (HopfAlgebra.extendPoint H A g * x) ≫
        fppfHomogeneousQuotientSchemeProjection eI := by
  apply ULift.up_inj.mp
  have h := congrArg (fun α ↦ α.app (op (op A))
    ((fppfHomogeneousQuotientProjection H I).app (op (op A)) (ULift.up x)))
      (Sheaf.hom_ext_iff.mp
        (hom_comp_pointsSheafMap_fppfHomogeneousQuotientSchemeTranslation_hom eI g))
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply] at h
  have h₁ :
      (CommAlgCat.pointsSheafMap
          (fppfHomogeneousQuotientSchemeTranslation eI g).hom).hom.app (op (op A))
          (ULift.up (Spec.mapMulEquiv x ≫ fppfHomogeneousQuotientSchemeProjection eI)) =
        ULift.up (Spec.mapMulEquiv x ≫ fppfHomogeneousQuotientSchemeProjection eI ≫
          (fppfHomogeneousQuotientSchemeTranslation eI g).hom) :=
    (CommAlgCat.pointsSheafMap_hom_app_apply _ (op (op A)) _).trans
      (congrArg ULift.up (Category.assoc _ _ _))
  have h₂ :
      eI.hom.hom.app (op (op A))
          ((fppfHomogeneousQuotientTranslation H I g).hom.hom.app (op (op A))
            ((fppfHomogeneousQuotientProjection H I).app (op (op A)) (ULift.up x))) =
        eI.hom.hom.app (op (op A))
          ((fppfHomogeneousQuotientProjection H I).app (op (op A))
            (ULift.up (HopfAlgebra.extendPoint H A g * x))) :=
    congrArg (eI.hom.hom.app (op (op A)))
      (fppfHomogeneousQuotientTranslation_hom_app_projection H I g (op (op A)) x)
  exact h₁.symm.trans
    ((congrArg _ (mapMulEquiv_comp_fppfHomogeneousQuotientSchemeProjection eI x)).trans
      (h.trans (h₂.trans (mapMulEquiv_comp_fppfHomogeneousQuotientSchemeProjection eI _).symm)))

/-- On projected `A`-points of `G`, inverse left translation on `X` multiplies the group point on
the left by `HopfAlgebra.extendPoint H A g⁻¹`. -/
theorem mapMulEquiv_comp_fppfHomogeneousQuotientSchemeTranslation_inv {I : HopfIdeal R H}
    {X : Over (Spec (CommRingCat.of R))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    {A : CommAlgCat.{u} R} (x : HopfAlgebra.points (R := R) (H := H) A) :
    Spec.mapMulEquiv x ≫ fppfHomogeneousQuotientSchemeProjection eI ≫
        (fppfHomogeneousQuotientSchemeTranslation eI g).inv =
      Spec.mapMulEquiv (HopfAlgebra.extendPoint H A g⁻¹ * x) ≫
        fppfHomogeneousQuotientSchemeProjection eI := by
  rw [← Iso.symm_hom, ← fppfHomogeneousQuotientSchemeTranslation_inv]
  exact mapMulEquiv_comp_fppfHomogeneousQuotientSchemeTranslation_hom eI g⁻¹ x

/-- **Over-scheme intertwining of left translation.** Over `Spec R`, the quotient projection
`G ⟶ X` intertwines `Spec.mapMulEquiv` of `HopfAlgebra.leftTranslationAlgEquiv g` with
`fppfHomogeneousQuotientSchemeTranslation eI g`. -/
@[reassoc]
theorem mapMulEquiv_leftTranslationAlgEquiv_comp_fppfHomogeneousQuotientSchemeProjection
    {I : HopfIdeal R H} {X : Over (Spec (CommRingCat.of R))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    Spec.mapMulEquiv (toConv (HopfAlgebra.leftTranslationAlgEquiv g).toAlgHom) ≫
        fppfHomogeneousQuotientSchemeProjection eI =
      fppfHomogeneousQuotientSchemeProjection eI ≫
        (fppfHomogeneousQuotientSchemeTranslation eI g).hom := by
  let u : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R H) := toConv (AlgHom.id R H)
  have hmul : HopfAlgebra.extendPoint H (CommAlgCat.of R H) g * u =
      toConv (HopfAlgebra.leftTranslationAlgEquiv g).toAlgHom := by
    rw [HopfAlgebra.extendPoint_apply, ← AlgHom.mapValue_apply]
    exact (HopfAlgebra.toConv_leftTranslationAlgEquiv g).symm
  have hpt := mapMulEquiv_comp_fppfHomogeneousQuotientSchemeTranslation_hom eI g u
  rw [mapMulEquiv_toConv_id, Category.id_comp, hmul] at hpt
  exact hpt.symm

/-- **Over-scheme intertwining of inverse left translation.** Over `Spec R`, the quotient
projection `G ⟶ X` intertwines `Spec.mapMulEquiv` of `(HopfAlgebra.leftTranslationAlgEquiv g)⁻¹`
with `(fppfHomogeneousQuotientSchemeTranslation eI g).inv`. -/
@[reassoc]
theorem mapMulEquiv_leftTranslationAlgEquiv_inv_comp_fppfHomogeneousQuotientSchemeProjection
    {I : HopfIdeal R H} {X : Over (Spec (CommRingCat.of R))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    Spec.mapMulEquiv (toConv (HopfAlgebra.leftTranslationAlgEquiv g)⁻¹.toAlgHom) ≫
        fppfHomogeneousQuotientSchemeProjection eI =
      fppfHomogeneousQuotientSchemeProjection eI ≫
        (fppfHomogeneousQuotientSchemeTranslation eI g).inv := by
  rw [← HopfAlgebra.leftTranslationAlgEquiv_inv, ← Iso.symm_hom,
    ← fppfHomogeneousQuotientSchemeTranslation_inv]
  exact mapMulEquiv_leftTranslationAlgEquiv_comp_fppfHomogeneousQuotientSchemeProjection eI g⁻¹

/-- **Scheme-level intertwining of left translation.** On underlying schemes `Spec H ⟶ X.left`,
the quotient projection intertwines `Spec.map` of `HopfAlgebra.leftTranslationAlgEquiv g` with
`fppfHomogeneousQuotientSchemeTranslation eI g`. -/
@[reassoc]
theorem specMap_leftTranslationAlgEquiv_comp_fppfHomogeneousQuotientSchemeProjection_left
    {I : HopfIdeal R H} {X : Over (Spec (CommRingCat.of R))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    Spec.map (CommRingCat.ofHom (HopfAlgebra.leftTranslationAlgEquiv g).toAlgHom.toRingHom) ≫
        (fppfHomogeneousQuotientSchemeProjection eI).left =
      (fppfHomogeneousQuotientSchemeProjection eI).left ≫
        (fppfHomogeneousQuotientSchemeTranslation eI g).hom.left := by
  have h := congrArg Over.Hom.left
    (mapMulEquiv_leftTranslationAlgEquiv_comp_fppfHomogeneousQuotientSchemeProjection eI g)
  erw [Over.comp_left, Over.comp_left, mapMulEquiv_left] at h
  exact h

/-- **Scheme-level intertwining of inverse left translation.** On underlying schemes
`Spec H ⟶ X.left`, the quotient projection intertwines `Spec.map` of
`(HopfAlgebra.leftTranslationAlgEquiv g)⁻¹` with
`(fppfHomogeneousQuotientSchemeTranslation eI g).inv`. -/
@[reassoc]
theorem specMap_leftTranslationAlgEquiv_inv_comp_fppfHomogeneousQuotientSchemeProjection_left
    {I : HopfIdeal R H} {X : Over (Spec (CommRingCat.of R))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    Spec.map (CommRingCat.ofHom (HopfAlgebra.leftTranslationAlgEquiv g)⁻¹.toAlgHom.toRingHom) ≫
        (fppfHomogeneousQuotientSchemeProjection eI).left =
      (fppfHomogeneousQuotientSchemeProjection eI).left ≫
        (fppfHomogeneousQuotientSchemeTranslation eI g).inv.left := by
  rw [← HopfAlgebra.leftTranslationAlgEquiv_inv, ← Iso.symm_hom,
    ← fppfHomogeneousQuotientSchemeTranslation_inv]
  exact specMap_leftTranslationAlgEquiv_comp_fppfHomogeneousQuotientSchemeProjection_left eI g⁻¹

/-- **Equivariance of subgroup-induced scheme maps.** For `J ≤ I`, the induced morphism
`fppfHomogeneousQuotientSchemeMap eI eJ hJI : X ⟶ Y` commutes with left translation by every
`R`-valued point of `G`. -/
@[reassoc]
theorem fppfHomogeneousQuotientSchemeTranslation_hom_comp_map {I J : HopfIdeal R H}
    {X Y : Over (Spec (CommRingCat.of R))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eJ : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y)
    (hJI : J ≤ I)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    (fppfHomogeneousQuotientSchemeTranslation eI g).hom ≫
        fppfHomogeneousQuotientSchemeMap eI eJ hJI =
      fppfHomogeneousQuotientSchemeMap eI eJ hJI ≫
        (fppfHomogeneousQuotientSchemeTranslation eJ g).hom := by
  apply (CommAlgCat.pointsSheafHomEquiv X Y).injective
  simp [fppfHomogeneousQuotientTranslation_hom_comp_map_assoc]

/-- **Equivariance of subgroup-induced scheme maps under inverse left translation.** -/
@[reassoc]
theorem fppfHomogeneousQuotientSchemeTranslation_inv_comp_map {I J : HopfIdeal R H}
    {X Y : Over (Spec (CommRingCat.of R))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eJ : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y)
    (hJI : J ≤ I)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    (fppfHomogeneousQuotientSchemeTranslation eI g).inv ≫
        fppfHomogeneousQuotientSchemeMap eI eJ hJI =
      fppfHomogeneousQuotientSchemeMap eI eJ hJI ≫
        (fppfHomogeneousQuotientSchemeTranslation eJ g).inv := by
  rw [← Iso.symm_hom, ← fppfHomogeneousQuotientSchemeTranslation_inv,
    ← Iso.symm_hom, ← fppfHomogeneousQuotientSchemeTranslation_inv]
  exact fppfHomogeneousQuotientSchemeTranslation_hom_comp_map eI eJ hJI g⁻¹

end Translation

section RationalPoints

variable {k : Type u} [Field k] [IsAlgClosed k] {H : _root_.CommHopfAlgCat.{u} k}

/-- **Rational points of a scheme representing `G/N` over an algebraically closed field.** For any
scheme `X` over `Spec k` representing `fppfHomogeneousQuotient H I`, the `k`-rational points
`(Spec k).asOver (Spec k) ⟶ X` are in canonical bijection with the left coset space
`G(k)/N(k)`. -/
def fppfHomogeneousQuotientSchemeRationalPointsEquiv {I : HopfIdeal k H}
    {X : Over (Spec (CommRingCat.of k))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X) :
    HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) ⧸
        quotientPointsSubgroup H I (CommAlgCat.of k k) ≃
      ((Spec (CommRingCat.of k)).asOver (Spec (CommRingCat.of k)) ⟶ X) :=
  (fppfHomogeneousQuotientRationalPointsEquiv H I).trans <|
    (((sheafToPresheaf _ _).mapIso eI).app (op (op (CommAlgCat.of k k)))).toEquiv.trans
      Equiv.ulift

/-- The coset `g N(k)` corresponds to the `k`-point `Spec.mapMulEquiv g` composed with the scheme
quotient projection `G ⟶ X`. -/
@[simp]
theorem fppfHomogeneousQuotientSchemeRationalPointsEquiv_mk {I : HopfIdeal k H}
    {X : Over (Spec (CommRingCat.of k))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) :
    fppfHomogeneousQuotientSchemeRationalPointsEquiv eI (QuotientGroup.mk g) =
      Spec.mapMulEquiv g ≫ fppfHomogeneousQuotientSchemeProjection eI := by
  have heval : fppfHomogeneousQuotientSchemeRationalPointsEquiv eI (QuotientGroup.mk g) =
      (eI.hom.hom.app (op (op (CommAlgCat.of k k)))
        (fppfHomogeneousQuotientRationalPointsEquiv H I (QuotientGroup.mk g))).down := rfl
  apply ULift.up_inj.mp
  rw [heval, ULift.up_down, fppfHomogeneousQuotientRationalPointsEquiv_mk]
  exact (mapMulEquiv_comp_fppfHomogeneousQuotientSchemeProjection eI g).symm

/-- The inverse rational-points equivalence sends a projected `k`-point `Spec.mapMulEquiv g ≫ π`
back to the coset `g N(k)`. -/
@[simp]
theorem fppfHomogeneousQuotientSchemeRationalPointsEquiv_symm_comp_projection {I : HopfIdeal k H}
    {X : Over (Spec (CommRingCat.of k))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) :
    (fppfHomogeneousQuotientSchemeRationalPointsEquiv eI).symm
        (Spec.mapMulEquiv g ≫ fppfHomogeneousQuotientSchemeProjection eI) =
      QuotientGroup.mk g := by
  rw [← fppfHomogeneousQuotientSchemeRationalPointsEquiv_mk, Equiv.symm_apply_apply]

/-- **Every `k`-rational point of `X` lifts to a `k`-point of `G`.** -/
theorem exists_mapMulEquiv_comp_fppfHomogeneousQuotientSchemeProjection_eq
    {I : HopfIdeal k H} {X : Over (Spec (CommRingCat.of k))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (p : (Spec (CommRingCat.of k)).asOver (Spec (CommRingCat.of k)) ⟶ X) :
    ∃ g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k),
      Spec.mapMulEquiv g ≫ fppfHomogeneousQuotientSchemeProjection eI = p := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective
    ((fppfHomogeneousQuotientSchemeRationalPointsEquiv eI).symm p)
  refine ⟨g, ?_⟩
  rw [← fppfHomogeneousQuotientSchemeRationalPointsEquiv_mk, hg, Equiv.apply_symm_apply]

/-- **Compatibility of `k`-rational points with subgroup-induced scheme projections.** -/
theorem fppfHomogeneousQuotientSchemeRationalPointsEquiv_comp_map {I J : HopfIdeal k H}
    {X Y : Over (Spec (CommRingCat.of k))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eJ : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y)
    (hJI : J ≤ I)
    (q : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) ⧸
      quotientPointsSubgroup H I (CommAlgCat.of k k)) :
    fppfHomogeneousQuotientSchemeRationalPointsEquiv eI q ≫
        fppfHomogeneousQuotientSchemeMap eI eJ hJI =
      fppfHomogeneousQuotientSchemeRationalPointsEquiv eJ
        (Subgroup.quotientMapOfLE (quotientPointsSubgroup_le_of_le H hJI _) q) := by
  induction q using QuotientGroup.induction_on with
  | H g =>
    rw [Subgroup.quotientMapOfLE_apply_mk, fppfHomogeneousQuotientSchemeRationalPointsEquiv_mk,
      fppfHomogeneousQuotientSchemeRationalPointsEquiv_mk, Category.assoc,
      fppfHomogeneousQuotientSchemeProjection_comp_map]

/-- **Compatibility of `k`-rational points with left translation on `X`.** -/
theorem fppfHomogeneousQuotientSchemeRationalPointsEquiv_comp_translation_hom
    {I : HopfIdeal k H} {X : Over (Spec (CommRingCat.of k))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k))
    (q : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) ⧸
      quotientPointsSubgroup H I (CommAlgCat.of k k)) :
    fppfHomogeneousQuotientSchemeRationalPointsEquiv eI q ≫
        (fppfHomogeneousQuotientSchemeTranslation eI g).hom =
      fppfHomogeneousQuotientSchemeRationalPointsEquiv eI (g • q) := by
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [fppfHomogeneousQuotientSchemeRationalPointsEquiv_mk, Category.assoc,
      mapMulEquiv_comp_fppfHomogeneousQuotientSchemeTranslation_hom,
      HopfAlgebra.extendPoint_self, MulAction.Quotient.smul_mk, smul_eq_mul,
      fppfHomogeneousQuotientSchemeRationalPointsEquiv_mk]

/-- **Compatibility of `k`-rational points with inverse left translation on `X`.** -/
theorem fppfHomogeneousQuotientSchemeRationalPointsEquiv_comp_translation_inv
    {I : HopfIdeal k H} {X : Over (Spec (CommRingCat.of k))}
    (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k))
    (q : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) ⧸
      quotientPointsSubgroup H I (CommAlgCat.of k k)) :
    fppfHomogeneousQuotientSchemeRationalPointsEquiv eI q ≫
        (fppfHomogeneousQuotientSchemeTranslation eI g).inv =
      fppfHomogeneousQuotientSchemeRationalPointsEquiv eI (g⁻¹ • q) := by
  rw [← Iso.symm_hom, ← fppfHomogeneousQuotientSchemeTranslation_inv]
  exact fppfHomogeneousQuotientSchemeRationalPointsEquiv_comp_translation_hom eI g⁻¹ q

end RationalPoints

end

end TauCeti.CommHopfAlgCat
