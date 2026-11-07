/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order

/-!
# Projections between fppf homogeneous quotients

An inclusion of closed subgroups `P ⊆ Q` induces the projection `G/P ⟶ G/Q`.
On defining Hopf ideals the inclusion is reversed: `J ≤ I` induces a map from the
quotient by `I` to the quotient by `J`. We construct these maps both for the coset
presheaves and for their fppf sheafifications, with identity and composition laws.

The sheaf projection is characterized by its composite with `G ⟶ G/P` and is fppf
locally surjective, hence an epimorphism. This does not assert surjectivity on
sections over every algebra: representatives of sections of the sheaf quotient
need only exist locally. No normality, smoothness, finite type or representability
hypothesis is required.

The construction uses `homogeneousQuotientPresheafLift` on cosets and
`fppfHomogeneousQuotientHomEquiv` to descend the projection to sheaves.

## References

* J. S. Milne, *Algebraic Groups* (2017), §5, quotient sheaves and homogeneous spaces.
-/

public section

open CategoryTheory Opposite

namespace CommHopfAlgCat

open TauCeti TauCeti.CommHopfAlgCat

universe u

noncomputable section

variable {R : Type u} [CommRing R] (H : _root_.CommHopfAlgCat.{u} R)
variable {I J K : HopfIdeal R H}

/-- The map of coset presheaves induced by an inclusion of closed subgroups.
The defining ideals have the opposite inclusion. -/
def homogeneousQuotientPresheafMap (hJI : J ≤ I) :
    homogeneousQuotientPresheaf H I ⟶ homogeneousQuotientPresheaf H J :=
  homogeneousQuotientPresheafLift H I (homogeneousQuotientPresheafProjection H J)
    fun A g n ↦ (homogeneousQuotientPresheafProjection_eq_iff H J A
      (g * n.val) g).mpr (by
        simpa using (quotientPointsSubgroup_le_of_le H hJI A.unop.unop) n.property)

/-- The projection preserves a coset's representative. -/
@[simp]
theorem homogeneousQuotientPresheafMap_app_mk (hJI : J ≤ I)
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ)
    (g : HopfAlgebra.points (R := R) (H := H) A.unop.unop) :
    (homogeneousQuotientPresheafMap H hJI).app A
        (homogeneousQuotientPresheafMk H I A g) =
      homogeneousQuotientPresheafMk H J A g := by
  simp [homogeneousQuotientPresheafMap]

/-- The coset projection commutes with the maps from ambient group points. -/
@[reassoc (attr := simp)]
theorem homogeneousQuotientPresheafProjection_comp_map (hJI : J ≤ I) :
    homogeneousQuotientPresheafProjection H I ≫ homogeneousQuotientPresheafMap H hJI =
      homogeneousQuotientPresheafProjection H J := by
  simp only [homogeneousQuotientPresheafMap,
    homogeneousQuotientPresheafProjection_comp_lift]

/-- The projection associated to equality is the identity. -/
@[simp]
theorem homogeneousQuotientPresheafMap_refl (I : HopfIdeal R H) :
    homogeneousQuotientPresheafMap H (le_refl I) = 𝟙 _ := by
  apply homogeneousQuotientPresheaf_hom_ext
  simp

/-- Projections of coset presheaves compose along inclusions. -/
@[reassoc (attr := simp)]
theorem homogeneousQuotientPresheafMap_comp (hJI : J ≤ I) (hKJ : K ≤ J) :
    homogeneousQuotientPresheafMap H hJI ≫ homogeneousQuotientPresheafMap H hKJ =
      homogeneousQuotientPresheafMap H (hKJ.trans hJI) := by
  apply homogeneousQuotientPresheaf_hom_ext
  simp

/-- Every section of the target coset presheaf lifts to the source coset presheaf. -/
theorem homogeneousQuotientPresheafMap_surjective (hJI : J ≤ I)
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ) :
    Function.Surjective ((homogeneousQuotientPresheafMap H hJI).app A) := by
  intro q
  induction q using homogeneousQuotientPresheaf_induction_on H J with
  | h g => exact ⟨homogeneousQuotientPresheafMk H I A g, by simp⟩

/-- The projection `G/P ⟶ G/Q` for `P ⊆ Q`, as a morphism of fppf sheaves.
Here `I` defines `P` and `J` defines `Q`, so its hypothesis is `J ≤ I`. -/
def fppfHomogeneousQuotientMap (hJI : J ≤ I) :
    fppfHomogeneousQuotient H I ⟶ fppfHomogeneousQuotient H J :=
  (fppfHomogeneousQuotientHomEquiv H I (fppfHomogeneousQuotient H J)).symm
    ⟨fppfHomogeneousQuotientProjection H J, fun A g n ↦ by
      have h := (fppfHomogeneousQuotientHomEquiv H J
        (fppfHomogeneousQuotient H J) (𝟙 _)).property A g
          ⟨n.val, quotientPointsSubgroup_le_of_le H hJI A.unop.unop n.property⟩
      simpa only [fppfHomogeneousQuotientHomEquiv_apply, ObjectProperty.FullSubcategory.id_hom,
        Category.comp_id] using h⟩

/-- The canonical projection commutes with the maps from ambient group points. -/
@[reassoc (attr := simp)]
theorem fppfHomogeneousQuotientProjection_comp_map (hJI : J ≤ I) :
    fppfHomogeneousQuotientProjection H I ≫ (fppfHomogeneousQuotientMap H hJI).hom =
      fppfHomogeneousQuotientProjection H J := by
  exact fppfHomogeneousQuotientHomEquiv_symm_apply H I _ _ _

/-- Sheafification of a coset and projection to a larger subgroup commute.
The equality morphisms identify the native quotient sheaves with their sheafifications. -/
@[reassoc]
theorem toSheafify_comp_fppfHomogeneousQuotientMap (hJI : J ≤ I) :
    (toSheafify (CommAlgCat.fppfTopology R) (homogeneousQuotientPresheaf H I) ≫
      eqToHom (fppfHomogeneousQuotient_obj H I).symm) ≫
        (fppfHomogeneousQuotientMap H hJI).hom =
      homogeneousQuotientPresheafMap H hJI ≫
        toSheafify (CommAlgCat.fppfTopology R) (homogeneousQuotientPresheaf H J) ≫
          eqToHom (fppfHomogeneousQuotient_obj H J).symm := by
  apply homogeneousQuotientPresheaf_hom_ext
  rw [← Category.assoc, ← fppfHomogeneousQuotientProjection_def,
    fppfHomogeneousQuotientProjection_comp_map,
    homogeneousQuotientPresheafProjection_comp_map_assoc,
    ← fppfHomogeneousQuotientProjection_def]

/-- The quotient projection is the unique sheaf morphism compatible with the maps
from the ambient group. -/
theorem fppfHomogeneousQuotientMap_eq_iff (hJI : J ≤ I)
    (f : fppfHomogeneousQuotient H I ⟶ fppfHomogeneousQuotient H J) :
    f = fppfHomogeneousQuotientMap H hJI ↔
      fppfHomogeneousQuotientProjection H I ≫ f.hom =
        fppfHomogeneousQuotientProjection H J := by
  constructor
  · rintro rfl
    simp
  · intro h
    apply fppfHomogeneousQuotient_hom_ext
    simpa using h

/-- The projection associated to equality of closed subgroups is the identity. -/
@[simp]
theorem fppfHomogeneousQuotientMap_refl (I : HopfIdeal R H) :
    fppfHomogeneousQuotientMap H (le_refl I) = 𝟙 _ := by
  apply fppfHomogeneousQuotient_hom_ext
  simp

/-- The sheaf projections compose along inclusions of closed subgroups. -/
@[reassoc (attr := simp)]
theorem fppfHomogeneousQuotientMap_comp (hJI : J ≤ I) (hKJ : K ≤ J) :
    fppfHomogeneousQuotientMap H hJI ≫ fppfHomogeneousQuotientMap H hKJ =
      fppfHomogeneousQuotientMap H (hKJ.trans hJI) := by
  apply fppfHomogeneousQuotient_hom_ext
  simp

/-- The projection of fppf homogeneous quotients is locally surjective. -/
instance fppfHomogeneousQuotientMap_isLocallySurjective (hJI : J ≤ I) :
    Presheaf.IsLocallySurjective (CommAlgCat.fppfTopology R)
      (fppfHomogeneousQuotientMap H hJI).hom :=
  Presheaf.isLocallySurjective_of_isLocallySurjective_fac
    (CommAlgCat.fppfTopology R) (fppfHomogeneousQuotientProjection_comp_map H hJI)

end

end CommHopfAlgCat
