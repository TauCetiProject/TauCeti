/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.LocalRing
public import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.Augmentation
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic

/-!
# Completed group algebras of pro-`p` groups are local

Let `R` be a local ring in which the prime `p` is not a unit, for instance `ℤ_[p]`, the ring of
integers of a finite extension of `ℚ_p`, or a field of characteristic `p`, and let `Γ` be a
topological group whose open normal quotients are finite, for instance a profinite group. This
file proves that the completed group algebra `R[[Γ]]` is a local ring if and only if `Γ` is
pro-`p`. No analyticity or finite generation of `Γ` is assumed.

An element of `R[[Γ]]` is a unit exactly when each of its projections to the finite group algebras
`R[Γ ⧸ U]` is, because the transition maps carry inverses to inverses
(`TauCeti.completedGroupAlgebra.isUnit_iff_forall_isUnit_proj`). The augmentation `R[[Γ]] → R`
is the common augmentation of the projections
(`TauCeti.completedGroupAlgebra.augmentation_proj`). When `Γ` is pro-`p`, each `Γ ⧸ U` is a
finite `p`-group, so an element of `R[Γ ⧸ U]` with unit augmentation is a unit
(`TauCeti.MonoidAlgebra.isLocalHom_augmentation_of_isPGroup`). Hence the augmentation of
`R[[Γ]]` is a local homomorphism: an element of `R[[Γ]]` is a unit exactly when its augmentation
is, and `R[[Γ]]` is local. Conversely, every `R[Γ ⧸ U]` is a quotient of
`R[[Γ]]`, so it is local when `R[[Γ]]` is, which forces `Γ ⧸ U` to be a `p`-group
(`TauCeti.MonoidAlgebra.isPGroup_of_isLocalRing`).

## Main results

* `TauCeti.completedGroupAlgebra.isLocalHom_augmentation_of_isProP`: for pro-`p` `Γ`, an element
  of `R[[Γ]]` whose augmentation is a unit is a unit.
* `TauCeti.completedGroupAlgebra.isLocalRing_iff_isProP`: `R[[Γ]]` is local if and only if `Γ`
  is pro-`p`.

## References

* M. Lazard, *Groupes analytiques `p`-adiques*, Publ. Math. IHÉS 26 (1965), Chapitre II, (2.2.2).
* K. Ardakov and K. A. Brown, *Ring-theoretic properties of Iwasawa algebras: a survey*,
  Doc. Math. Extra Vol. (2006), §4.1, Theorem (2).
-/

public section

namespace TauCeti

namespace completedGroupAlgebra

universe u v

variable {R : Type u} [CommRing R] {Γ : Type v} [Group Γ] [TopologicalSpace Γ]

section FiniteQuotients

variable [∀ U : OpenNormalSubgroup Γ, Finite (Γ ⧸ U.toSubgroup)] {p : ℕ} [Fact p.Prime]

/-- **The augmentation of a pro-`p` completed group algebra is local.** If `Γ` is pro-`p` with
finite open normal quotients and `R` is a local ring in which `p` is not a unit, an element of
`R[[Γ]]` whose augmentation is a unit is a unit. -/
theorem isLocalHom_augmentation_of_isProP [IsLocalRing R] (hp : ¬IsUnit (p : R))
    (hΓ : IsProP p Γ) : IsLocalHom (augmentation R Γ) :=
  ⟨fun x hx ↦ isUnit_iff_forall_isUnit_proj.mpr fun U ↦
    (MonoidAlgebra.isLocalHom_augmentation_of_isPGroup hp (isProP_iff.mp hΓ U)).map_nonunit _
      (by rwa [augmentation_proj])⟩

/-- **The completed group algebra of a pro-`p` group is local.** If `Γ` is pro-`p` with finite
open normal quotients and `R` is a local ring in which `p` is not a unit, then `R[[Γ]]` is a
local ring. -/
theorem isLocalRing_of_isProP [IsLocalRing R] (hp : ¬IsUnit (p : R)) (hΓ : IsProP p Γ) :
    IsLocalRing (completedGroupAlgebra R Γ) :=
  have := isLocalHom_augmentation_of_isProP hp hΓ
  (augmentation R Γ).domain_isLocalRing

/-- **A local completed group algebra forces a pro-`p` group.** If `Γ` has finite open normal
quotients, `p` is not a unit in `R`, and `R[[Γ]]` is a local ring, then `Γ` is pro-`p`. -/
theorem isProP_of_isLocalRing [IsLocalRing (completedGroupAlgebra R Γ)] (hp : ¬IsUnit (p : R)) :
    IsProP p Γ := isProP_iff.mpr fun U ↦ by
  have : Nontrivial R := (algebraMap R (completedGroupAlgebra R Γ)).domain_nontrivial
  -- The level `R[Γ ⧸ U]` is a quotient of the local ring `R[[Γ]]`.
  have : IsLocalRing (MonoidAlgebra R (Γ ⧸ U.toSubgroup)) :=
    IsLocalRing.of_surjective' (proj R Γ U).toRingHom (proj_surjective R Γ U)
  exact MonoidAlgebra.isPGroup_of_isLocalRing hp isMulTorsion_of_finite

/-- **The local-ring criterion for completed group algebras.** If `Γ` has finite open normal
quotients, for instance if `Γ` is profinite, and `R` is a local ring in which the prime `p` is not
a unit, then `R[[Γ]]` is a local ring if and only if `Γ` is pro-`p`. -/
theorem isLocalRing_iff_isProP [IsLocalRing R] (hp : ¬IsUnit (p : R)) :
    IsLocalRing (completedGroupAlgebra R Γ) ↔ IsProP p Γ :=
  ⟨fun _ ↦ isProP_of_isLocalRing hp, isLocalRing_of_isProP hp⟩

end FiniteQuotients

end completedGroupAlgebra

end TauCeti
