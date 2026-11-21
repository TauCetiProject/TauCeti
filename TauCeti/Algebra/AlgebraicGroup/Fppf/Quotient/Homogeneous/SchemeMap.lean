/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.Map
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Projections between schemes representing homogeneous quotients

Let `G` be an affine group over a commutative ring `R` and let `P ⊆ Q` be closed subgroups.
Suppose the fppf homogeneous quotients `G/P` and `G/Q` are represented by schemes `X` and `Y`
over `Spec R`, that is, `G/P` is isomorphic to the fppf sheaf of points of `X` and `G/Q` to
that of `Y`. The sheaf projection `G/P ⟶ G/Q` is then induced by a unique morphism of schemes
`X ⟶ Y` over `Spec R`, because schemes are determined by their fppf sheaves of affine points.
On `A`-valued points it sends the image of `g ∈ G(A)` in `X` to the image of `g` in `Y`; it is
the unique morphism with this property. These morphisms are functorial in the inclusion.

The scheme projection is surjective, because the sheaf projection is fppf locally surjective.
Consequently universal closedness descends from `X` to `Y`: if `G/P` is represented by a
universally closed scheme, so is `G/Q`, and the same holds for properness when `Y` is separated
and locally of finite type. This is the form in which completeness of `G/B` for a Borel
subgroup `B` gives completeness of `G/Q` for every closed subgroup `Q ⊇ B`.

No finiteness, smoothness, reducedness or normality hypothesis is placed on `G` or its
subgroups, and the representing isomorphisms are arbitrary.

## Main declarations

* `CommHopfAlgCat.fppfHomogeneousQuotientSchemeMap`: the morphism `X ⟶ Y` of representing
  schemes induced by `P ⊆ Q`.
* `CommHopfAlgCat.fppfHomogeneousQuotientSchemeMap_eq_iff`: it is the unique morphism compatible
  with the maps from `G`.
* `CommHopfAlgCat.comp_fppfHomogeneousQuotientSchemeMap`: it sends the image of an `A`-point of
  `G` in `X` to its image in `Y`.
* `CommHopfAlgCat.surjective_fppfHomogeneousQuotientSchemeMap`: it is surjective.
* `CommHopfAlgCat.universallyClosed_hom_of_le` and `CommHopfAlgCat.isProper_hom_of_le`: universal
  closedness and properness descend from `X` to `Y`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 5.22 (the quotient universal property)
  and Theorem 17.16 (completeness of quotients by subgroups containing a Borel subgroup).
-/

public section

open CategoryTheory Opposite AlgebraicGeometry

namespace CommHopfAlgCat

open TauCeti TauCeti.CommHopfAlgCat

universe u

noncomputable section

variable {R : Type u} [CommRing R] (H : _root_.CommHopfAlgCat.{u} R) {I J K : HopfIdeal R H}
  {X Y Z : Over (Spec (CommRingCat.of R))}

/-- The morphism of representing schemes induced by an inclusion `P ⊆ Q` of closed subgroups.
If `eX` identifies `G/P` with the points of `X` and `eY` identifies `G/Q` with the points of
`Y`, this is the morphism `X ⟶ Y` over `Spec R` inducing the projection `G/P ⟶ G/Q`. Here `I`
defines `P` and `J` defines `Q`, so its hypothesis is `J ≤ I`. -/
def fppfHomogeneousQuotientSchemeMap (hJI : J ≤ I)
    (eX : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eY : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y) : X ⟶ Y :=
  (CommAlgCat.fullyFaithfulPointsSheafFunctor R).preimage
    (eX.inv ≫ fppfHomogeneousQuotientMap H hJI ≫ eY.hom)

/-- On sheaves of points, the morphism of representing schemes is the projection `G/P ⟶ G/Q`
transported along the representing isomorphisms. -/
@[simp]
theorem pointsSheafFunctor_map_fppfHomogeneousQuotientSchemeMap (hJI : J ≤ I)
    (eX : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eY : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y) :
    (CommAlgCat.pointsSheafFunctor R).map (fppfHomogeneousQuotientSchemeMap H hJI eX eY) =
      eX.inv ≫ fppfHomogeneousQuotientMap H hJI ≫ eY.hom :=
  (CommAlgCat.fullyFaithfulPointsSheafFunctor R).map_preimage _

/-- **The projection of representing schemes is unique.** A morphism `X ⟶ Y` over `Spec R` is the
morphism induced by `P ⊆ Q` exactly when it is compatible with the maps from `G` to the points of
`X` and of `Y`. -/
theorem fppfHomogeneousQuotientSchemeMap_eq_iff (hJI : J ≤ I)
    (eX : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eY : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y) (f : X ⟶ Y) :
    f = fppfHomogeneousQuotientSchemeMap H hJI eX eY ↔
      fppfHomogeneousQuotientProjection H I ≫ eX.hom.hom ≫
          ((CommAlgCat.pointsSheafFunctor R).map f).hom =
        fppfHomogeneousQuotientProjection H J ≫ eY.hom.hom := by
  rw [← (CommAlgCat.pointsSheafFunctor R).map_injective.eq_iff,
    pointsSheafFunctor_map_fppfHomogeneousQuotientSchemeMap, Iso.eq_inv_comp]
  constructor
  · intro h
    simpa using congrArg (fun φ ↦ fppfHomogeneousQuotientProjection H I ≫ φ.hom) h
  · intro h
    apply fppfHomogeneousQuotient_hom_ext
    simpa using h

/-- **The projection of representing schemes on points.** For every value algebra `A` and every
`g ∈ G(A)`, the morphism `X ⟶ Y` sends the `A`-point of `X` representing the coset `gP` to the
`A`-point of `Y` representing the coset `gQ`. -/
@[reassoc (attr := simp)]
theorem comp_fppfHomogeneousQuotientSchemeMap (hJI : J ≤ I)
    (eX : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eY : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y)
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ) (g : HopfAlgebra.points (R := R) (H := H) A.unop.unop) :
    dsimp% (eX.hom.hom.app A ((fppfHomogeneousQuotientProjection H I).app A (ULift.up g))).down ≫
        fppfHomogeneousQuotientSchemeMap H hJI eX eY =
      (eY.hom.hom.app A ((fppfHomogeneousQuotientProjection H J).app A (ULift.up g))).down :=
  congrArg (fun α ↦ (α.app A (ULift.up g)).down)
    ((fppfHomogeneousQuotientSchemeMap_eq_iff H hJI eX eY _).mp rfl)

/-- The morphism of representing schemes induced by equality of closed subgroups, along the same
representing isomorphism, is the identity. -/
@[simp]
theorem fppfHomogeneousQuotientSchemeMap_refl
    (eX : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X) :
    fppfHomogeneousQuotientSchemeMap H (le_refl I) eX eX = 𝟙 X := by
  apply (CommAlgCat.pointsSheafFunctor R).map_injective
  rw [pointsSheafFunctor_map_fppfHomogeneousQuotientSchemeMap, fppfHomogeneousQuotientMap_refl,
    Category.id_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]

/-- The morphisms of representing schemes compose along inclusions of closed subgroups. -/
@[reassoc (attr := simp)]
theorem fppfHomogeneousQuotientSchemeMap_comp (hJI : J ≤ I) (hKJ : K ≤ J)
    (eX : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eY : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y)
    (eZ : fppfHomogeneousQuotient H K ≅ CommAlgCat.pointsSheaf Z) :
    fppfHomogeneousQuotientSchemeMap H hJI eX eY ≫ fppfHomogeneousQuotientSchemeMap H hKJ eY eZ =
      fppfHomogeneousQuotientSchemeMap H (hKJ.trans hJI) eX eZ := by
  apply (CommAlgCat.pointsSheafFunctor R).map_injective
  rw [CategoryTheory.Functor.map_comp, pointsSheafFunctor_map_fppfHomogeneousQuotientSchemeMap,
    pointsSheafFunctor_map_fppfHomogeneousQuotientSchemeMap,
    pointsSheafFunctor_map_fppfHomogeneousQuotientSchemeMap, Category.assoc, Category.assoc,
    Iso.hom_inv_id_assoc, fppfHomogeneousQuotientMap_comp_assoc]

/-- The morphism of representing schemes induces an fppf locally surjective map of points. -/
instance isLocallySurjective_pointsSheafFunctor_map_fppfHomogeneousQuotientSchemeMap
    (hJI : J ≤ I) (eX : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eY : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y) :
    Sheaf.IsLocallySurjective
      ((CommAlgCat.pointsSheafFunctor R).map (fppfHomogeneousQuotientSchemeMap H hJI eX eY)) := by
  rw [pointsSheafFunctor_map_fppfHomogeneousQuotientSchemeMap]
  have : Sheaf.IsLocallySurjective (fppfHomogeneousQuotientMap H hJI) :=
    fppfHomogeneousQuotientMap_isLocallySurjective H hJI
  infer_instance

/-- **The projection of representing schemes is surjective.** -/
instance surjective_fppfHomogeneousQuotientSchemeMap (hJI : J ≤ I)
    (eX : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eY : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y) :
    Surjective (fppfHomogeneousQuotientSchemeMap H hJI eX eY).left :=
  CommAlgCat.surjective_of_isLocallySurjective_pointsSheafFunctor_map _

/-- **Universal closedness descends to quotients by larger subgroups.** If `P ⊆ Q` and `G/P` is
represented by a scheme universally closed over `Spec R`, then any scheme representing `G/Q` is
universally closed over `Spec R`. -/
theorem universallyClosed_hom_of_le (hJI : J ≤ I)
    (eX : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eY : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y) [UniversallyClosed X.hom] :
    UniversallyClosed Y.hom := by
  have : UniversallyClosed ((fppfHomogeneousQuotientSchemeMap H hJI eX eY).left ≫ Y.hom) := by
    rwa [Over.w]
  exact UniversallyClosed.of_comp_surjective (fppfHomogeneousQuotientSchemeMap H hJI eX eY).left _

/-- **Properness descends to quotients by larger subgroups.** If `P ⊆ Q` and `G/P` is
represented by a scheme proper over `Spec R`, then any scheme representing `G/Q` which is
separated and locally of finite type over `Spec R` is proper over `Spec R`. -/
theorem isProper_hom_of_le (hJI : J ≤ I)
    (eX : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    (eY : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y) [IsProper X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] : IsProper Y.hom :=
  have := universallyClosed_hom_of_le H hJI eX eY
  ⟨⟩

end

end CommHopfAlgCat
