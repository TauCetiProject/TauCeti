/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import TauCeti.RingTheory.Henselization.Lift
import TauCeti.RingTheory.Henselian.Basic
import TauCeti.RingTheory.Henselization.Henselian
import TauCeti.RingTheory.Henselization.Jacobson
import TauCeti.RingTheory.Henselization.Residue

/-!
# The henselization of a local ring

The henselization of a pair `(R, 𝔪)` with `𝔪` a maximal ideal is a henselian local ring whose
maximal ideal is the extended ideal `𝔪 R^h`. When `R` is local with maximal ideal `𝔪`, the
structure map `R → R^h` is a local homomorphism inducing an isomorphism of residue fields, and
`R^h` is universal among local homomorphisms from `R` to henselian local rings. So the
henselization of the pair `(R, 𝔪)` is the henselization of the local ring `R`.

## Main results

* `TauCeti.Henselization.isMaximal_extended`: the extension of a maximal ideal to the
  henselization is maximal.
* `TauCeti.Henselization.henselianLocalRing`: the henselization along a maximal ideal is a
  henselian local ring, with maximal ideal `extended I` (`maximalIdeal_eq_extended`).
* `TauCeti.Henselization.isLocalHom_algebraMap`: for a local ring `R`, the structure map to the
  henselization along the maximal ideal is local.
* `TauCeti.Henselization.residueField_map_bijective`: it induces an isomorphism of residue
  fields.
* `TauCeti.Henselization.existsUnique_isLocalHom`: every local homomorphism from `R` to a
  henselian local ring factors through a unique local homomorphism out of the henselization.

## References

* [Stacks Project, Lemma 15.12.3](https://stacks.math.columbia.edu/tag/0A03), the henselization
  of the pair `(R, 𝔪)` is the henselization of the local ring `R`.
* Stacks Project, Definition 10.155.3, the henselization of a local ring.
-/

public section

open IsLocalRing

universe u v

namespace TauCeti.Henselization

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- An element of `R` maps into the extended ideal of the henselization exactly when it lies
in `I`. -/
@[simp]
theorem comap_extended : (extended I).comap (algebraMap R (algebra I)) = I :=
  le_antisymm (fun _ hr ↦ mem_of_algebraMap_mem_map_of_reducedMap_injective I
    (quotient_bijective I).1 hr) Ideal.le_comap_map

/-- The extension of a maximal ideal to the henselization is a maximal ideal: the quotient by
it is the residue field `R ⧸ I`. -/
instance isMaximal_extended [I.IsMaximal] : (extended I).IsMaximal := by
  rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
  exact (RingEquiv.ofBijective _ (quotient_bijective I)).symm.toMulEquiv.isField
    ((Ideal.Quotient.maximal_ideal_iff_isField_quotient I).mp ‹_›)

/-- The henselization along a maximal ideal is a local ring. -/
instance isLocalRing [I.IsMaximal] : IsLocalRing (algebra I) :=
  have hI : (extended I).IsMaximal := inferInstance
  .of_unique_max_ideal ⟨extended I, hI, fun _ hM ↦ (hI.eq_of_le hM.ne_top <|
    (extended_le_jacobson I).trans (sInf_le ⟨bot_le, hM⟩)).symm⟩

/-- The maximal ideal of the henselization along a maximal ideal `I` is the extended ideal. -/
theorem maximalIdeal_eq_extended [I.IsMaximal] : maximalIdeal (algebra I) = extended I :=
  (eq_maximalIdeal inferInstance).symm

/-- The henselization along a maximal ideal is a henselian local ring. -/
instance henselianLocalRing [I.IsMaximal] : HenselianLocalRing (algebra I) :=
  have : HenselianRing (algebra I) (maximalIdeal (algebra I)) :=
    maximalIdeal_eq_extended I ▸ inferInstance
  HenselianRing.henselianLocalRing _

/-- The map from the henselization along a maximal ideal `I` to a henselian local ring in which
`I` generates a proper ideal is a local homomorphism. -/
theorem isLocalHom_lift [I.IsMaximal] {S : Type v} [CommRing S] [HenselianLocalRing S]
    [Algebra R S] (hI : I.map (algebraMap R S) ≤ maximalIdeal S) : IsLocalHom (lift hI) := by
  have : IsLocalHom (lift hI : algebra I →+* S) := ((local_hom_TFAE _).out 1 3).mpr <| by
    rwa [maximalIdeal_eq_extended, Ideal.map_coe, map_extended]
  exact ⟨this.map_nonunit⟩

section IsLocalRing

variable (R) [IsLocalRing R]

/-- The structure map from a local ring to its henselization along the maximal ideal is a local
homomorphism. -/
instance isLocalHom_algebraMap : IsLocalHom (algebraMap R (algebra (maximalIdeal R))) :=
  ((local_hom_TFAE _).out 1 5).mpr <| by
    rw [maximalIdeal_eq_extended, comap_extended]

/-- The structure map from a local ring to its henselization along the maximal ideal induces an
isomorphism of residue fields. -/
theorem residueField_map_bijective :
    Function.Bijective (ResidueField.map (algebraMap R (algebra (maximalIdeal R)))) := by
  refine ⟨RingHom.injective _, fun y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := residue_surjective y
  obtain ⟨r, hr⟩ := exists_sub_algebraMap_mem_map_of_reducedMap_surjective _
    (quotient_bijective (maximalIdeal R)).2 x
  refine ⟨residue R r, ?_⟩
  rw [ResidueField.map_residue, eq_comm]
  exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    (maximalIdeal_eq_extended (maximalIdeal R) ▸ hr)

variable {R} {S : Type v} [CommRing S] [HenselianLocalRing S] [Algebra R S]
  [IsLocalHom (algebraMap R S)]

/-- **The universal property of the henselization of a local ring.** Every local homomorphism
from a local ring `R` to a henselian local ring `S` factors through a unique local
`R`-algebra map from the henselization of `R` along its maximal ideal. Every `R`-algebra map
from the henselization to `S` is in fact local and equal to this one (`eq_lift`). -/
@[stacks 0A03]
theorem existsUnique_isLocalHom :
    ∃! f : algebra (maximalIdeal R) →ₐ[R] S, IsLocalHom f :=
  have hR := map_maximalIdeal_le (algebraMap R S)
  ⟨lift hR, isLocalHom_lift _ hR, fun f _ ↦ eq_lift hR f⟩

end IsLocalRing

-- The henselization of a local ring along its maximal ideal is a henselian local ring.
example [IsLocalRing R] : HenselianLocalRing (algebra (maximalIdeal R)) := inferInstance

end TauCeti.Henselization
