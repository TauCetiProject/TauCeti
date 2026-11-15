/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.SingularLocus.Basic
public import TauCeti.RingTheory.Kaehler.UnramifiedBase
import TauCeti.AlgebraicGeometry.Curves.SingularLocus.Etale

/-!
# Independence of the singular locus from an unramified base

Let `X → Spec S → Spec R` be a compatible pair of structure morphisms, with `S/R`
formally unramified. When both structure morphisms define relative curves, their
singular ideal sheaves on `X` agree: `Ω[A⁄R] ≃ Ω[A⁄S]` on every affine open of `X`,
so their first Fitting ideals agree.

Together with restriction on the source, this comparison identifies singular loci
computed on overlapping affine base charts. The equality is scheme-theoretic and
does not discard nilpotents in the singular subscheme.

## References

* The Stacks Project, Tag 00RS: the transitivity sequence for differentials.
* The Stacks Project, Tag 0C3C: Fitting ideal sheaves.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {X : Scheme.{u}} [X.Over (Spec (.of R))] [X.Over (Spec (.of S))]

variable [Algebra.FormallyUnramified R S]
  [Flat (X ↘ Spec (.of R))] [LocallyOfFinitePresentation (X ↘ Spec (.of R))]
  [TauCeti.AlgebraicGeometry.PureRelativeDimension 1 (X ↘ Spec (.of R))]
  [Flat (X ↘ Spec (.of S))] [LocallyOfFinitePresentation (X ↘ Spec (.of S))]
  [TauCeti.AlgebraicGeometry.PureRelativeDimension 1 (X ↘ Spec (.of S))]

/-- The relative singular ideal is unchanged on enlarging the affine base through a
formally unramified algebra, provided the structure morphisms are compatible. -/
theorem singularLocus_eq_of_formallyUnramified_base
    (h : (X ↘ Spec (.of S)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) =
      (X ↘ Spec (.of R))) :
    X.singularLocus R = X.singularLocus S := by
  apply Scheme.IdealSheafData.ext
  funext U
  let : Algebra R Γ(X, U) :=
    ((X.baseRingToStructurePresheaf R).app (op U.1)).hom.toAlgebra
  let : Algebra S Γ(X, U) :=
    ((X.baseRingToStructurePresheaf S).app (op U.1)).hom.toAlgebra
  have : IsScalarTower R S Γ(X, U) :=
    .of_algebraMap_eq fun r ↦ (X.baseRingToStructurePresheaf_app_algebraMap h U.1 r).symm
  have := TauCeti.AlgebraicGeometry.finiteType_sections_of_locallyOfFiniteType R X U
  have := TauCeti.AlgebraicGeometry.finiteType_sections_of_locallyOfFiniteType S X U
  rw [Scheme.singularLocus_ideal, Scheme.singularLocus_ideal]
  exact TauCeti.fittingIdeal_congr
    (KaehlerDifferential.equivOfFormallyUnramifiedBase R S Γ(X, U)) 1

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FormallyUnramified R S]
  {X Y : Scheme.{u}} [X.Over (Spec (.of S))] [Y.Over (Spec (.of R))]
  [Flat (Y ↘ Spec (.of R))] [LocallyOfFinitePresentation (Y ↘ Spec (.of R))]
  [TauCeti.AlgebraicGeometry.PureRelativeDimension 1 (Y ↘ Spec (.of R))]
  [Flat (X ↘ Spec (.of S))] [LocallyOfFinitePresentation (X ↘ Spec (.of S))]
  [TauCeti.AlgebraicGeometry.PureRelativeDimension 1 (X ↘ Spec (.of S))]

/-- Singular loci computed on different affine bases agree after restriction along an
open immersion of sources, when the base-ring map is formally unramified and the
structure morphisms commute. -/
theorem singularLocus_eq_comap_of_isOpenImmersion_of_formallyUnramified_base
    (i : X ⟶ Y) [IsOpenImmersion i]
    (h : (X ↘ Spec (.of S)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) =
      i ≫ (Y ↘ Spec (.of R))) :
    X.singularLocus S = (Y.singularLocus R).comap i := by
  let : X.Over (Spec (.of R)) := ⟨i ≫ (Y ↘ Spec (.of R))⟩
  have : i.IsOver (Spec (.of R)) := ⟨rfl⟩
  -- The chosen structure map is the restriction of the structure map of `Y`.
  have : Flat (X ↘ Spec (.of R)) :=
    inferInstanceAs (Flat (i ≫ (Y ↘ Spec (.of R))))
  have : LocallyOfFinitePresentation (X ↘ Spec (.of R)) :=
    inferInstanceAs (LocallyOfFinitePresentation (i ≫ (Y ↘ Spec (.of R))))
  have : TauCeti.AlgebraicGeometry.PureRelativeDimension 1 (X ↘ Spec (.of R)) :=
    inferInstanceAs (TauCeti.AlgebraicGeometry.PureRelativeDimension 1
      (i ≫ (Y ↘ Spec (.of R))))
  rw [← singularLocus_eq_of_formallyUnramified_base h]
  exact singularLocus_eq_comap_of_etale i

/-- Restriction of sources and a formally unramified change of affine base give a
pullback square of singular subschemes. -/
theorem isPullback_singularLocus_subschemeι_of_isOpenImmersion_of_formallyUnramified_base
    (i : X ⟶ Y) [IsOpenImmersion i]
    (h : (X ↘ Spec (.of S)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) =
      i ≫ (Y ↘ Spec (.of R))) :
    IsPullback (X.singularLocus S).subschemeι
      ((X.singularLocus S).subschemeMap (Y.singularLocus R) i
        (Scheme.IdealSheafData.le_map_iff_comap_le.mpr
          (singularLocus_eq_comap_of_isOpenImmersion_of_formallyUnramified_base i h).ge))
      i (Y.singularLocus R).subschemeι :=
  isPullback_of_isClosedImmersion _ _ _ _ (by simp) (by
    rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι,
      singularLocus_eq_comap_of_isOpenImmersion_of_formallyUnramified_base i h])

end AlgebraicGeometry.Scheme
