/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Unramified.Diagonal
public import TauCeti.RingTheory.Henselization.Neighbourhood
public import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Filteredness of étale neighbourhoods

The étale neighbourhoods of a ring–ideal pair form a filtered category. In addition to tensor
products providing common targets, parallel maps are equalized after localizing the target at the
complement of the idempotent that cuts out their equalizer. This filtered category indexes the
construction of the henselization of a pair.

## References

* [Stacks Project, Tag 0A02](https://stacks.math.columbia.edu/tag/0A02)
-/

public section

open CategoryTheory TensorProduct

universe u v

namespace TauCeti.Henselization

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- Two parallel maps of étale neighbourhoods become equal after a further étale
neighbourhood. -/
theorem parallel_equalization {B C : Neighbourhood.{u, v} I} (f g : B ⟶ C) :
    ∃ (D : Neighbourhood.{u, v} I) (h : C ⟶ D), f ≫ h = g ≫ h := by
  let f' : B.obj →ₐ[R] C.obj := f.hom.hom
  let g' : B.obj →ₐ[R] C.obj := g.hom.hom
  let d : B.obj ⊗[R] B.obj →ₐ[R] C.obj := Algebra.TensorProduct.productMap f' g'
  let J := I.map (algebraMap R C.obj)
  have : Algebra.Etale R B.obj := ((isNeighbourhood_iff I _).mp B.property).1
  obtain ⟨e, he, hker⟩ :=
    TauCeti.Algebra.FormallyUnramified.exists_isIdempotentElem_ker_lmul_eq_span R B.obj
  have hde : d e ∈ J :=
    Algebra.TensorProduct.productMap_mem_of_comp_eq
      (RingHom.mem_ker.mp (hker ▸ Ideal.mem_span_singleton_self e)) J (by
        ext b
        exact quotient_mk_eq_of_reducedMap_surjective I
          ((isNeighbourhood_iff I _).mp B.property).2.2 f' g' b)
  have hs : IsUnit (Ideal.Quotient.mk J (1 - d e)) := by
    rw [map_sub, map_one, Ideal.Quotient.eq_zero_iff_mem.mpr hde, sub_zero]
    exact isUnit_one
  -- Localizing at the complement of `d e` gives a neighbourhood equalizing `f` and `g`.
  let D : Neighbourhood.{u, v} I :=
    ⟨_, isNeighbourhood_localization_of_isNeighbourhood I C.obj C.property hs⟩
  let h₀ : C.obj →ₐ[R] Localization.Away (1 - d e) := IsScalarTower.toAlgHom R C.obj _
  refine ⟨D, ObjectProperty.homMk (CommAlgCat.ofHom h₀), ?_⟩
  apply ObjectProperty.hom_ext
  apply CommAlgCat.hom_ext
  exact TauCeti.Algebra.FormallyUnramified.comp_eq_comp_of_isUnit_one_sub_productMap he hker.le
    f' g' h₀ (IsLocalization.Away.algebraMap_isUnit _)

/-- The category of étale neighbourhoods of a ring–ideal pair is filtered. -/
instance neighbourhood_isFiltered : IsFiltered (Neighbourhood.{u, max u v} I) where
  cocone_objs B C := by
    obtain ⟨D, ⟨f⟩, ⟨g⟩⟩ := exists_common_target I B C
    exact ⟨D, f, g, trivial⟩
  cocone_maps := fun {_ _} f g ↦ parallel_equalization I f g
  nonempty := ⟨⟨CommAlgCat.of R (ULift.{v} R),
    isNeighbourhood_of_algEquiv I (ULift.algEquiv (R := R)).symm⟩⟩

end TauCeti.Henselization
