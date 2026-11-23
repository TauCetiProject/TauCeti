/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.LocalRing
public import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic

/-!
# Local completed group algebras

Let `R` be a commutative local ring in which the prime `p` is not a unit, for instance `ℤ_p`, the
ring of integers of a finite extension of `ℚ_p`, or a field of characteristic `p`, and let `Γ` be
a topological group whose quotients by open normal subgroups are finite, for instance a profinite
group. The completed group algebra `R[[Γ]]` is a local ring if and only if `Γ` is pro-`p`. In that
case an element of `R[[Γ]]` is a unit exactly when its augmentation is a unit of `R`, so the
nonunits of `R[[Γ]]` are the preimage under the augmentation of the maximal ideal of `R`.

No analyticity, finite generation or countability is assumed of `Γ`, and `Γ` need not be
commutative. The criterion reduces to the finite levels: an element of `R[[Γ]]` is a unit when all
of its projections to the group algebras `R[Γ ⧸ U]` are
(`TauCeti.completedGroupAlgebra.isUnit_iff_forall_isUnit_proj`), and the group algebra of a finite
group over `R` is local exactly when the group is a `p`-group
(`TauCeti.MonoidAlgebra.isLocalRing_iff_isPGroup`).

## Main results

* `TauCeti.completedGroupAlgebra.isLocalHom_augmentation_of_isProP`: for pro-`p` `Γ`, an element
  of `R[[Γ]]` whose augmentation is a unit is a unit.
* `TauCeti.completedGroupAlgebra.isProP_of_isLocalRing`: if `R[[Γ]]` is local, `Γ` is pro-`p`.
* `TauCeti.completedGroupAlgebra.isLocalRing_iff_isProP`: `R[[Γ]]` is local if and only if `Γ` is
  pro-`p`.

## References

* M. Lazard, *Groupes analytiques `p`-adiques*, Publ. Math. IHÉS 26 (1965), Chapitre II,
  (2.2.2).
* K. Ardakov and K. A. Brown, *Ring-theoretic properties of Iwasawa algebras: a survey*,
  Documenta Math. Extra Volume Coates (2006), §4.1.
-/

public section

namespace TauCeti.completedGroupAlgebra

variable {R : Type*} [CommRing R] {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
  [∀ U : OpenNormalSubgroup Γ, Finite (Γ ⧸ U.toSubgroup)] {p : ℕ} [Fact p.Prime]

/-- **The augmentation of the completed group algebra of a pro-`p` group is local.** For a local
ring `R` in which `p` is not a unit and a pro-`p` group `Γ` with finite quotients by its open
normal subgroups, an element of `R[[Γ]]` whose augmentation is a unit is a unit. -/
theorem isLocalHom_augmentation_of_isProP [IsLocalRing R] (hp : ¬IsUnit (p : R))
    (hΓ : IsProP p Γ) : IsLocalHom (augmentation R Γ) := by
  refine ⟨fun x hx ↦ isUnit_iff_forall_isUnit_proj.mpr fun U ↦ ?_⟩
  have := MonoidAlgebra.isLocalHom_augmentation_of_isPGroup hp (isProP_iff.mp hΓ U)
  exact isUnit_of_map_unit (_root_.MonoidAlgebra.augmentation R _) _
    (by rwa [augmentation_proj])

/-- **A group with local completed group algebra is pro-`p`.** If the completed group algebra
`R[[Γ]]` of a group `Γ` with finite quotients by its open normal subgroups is local, and the prime
`p` is not a unit in `R`, then `Γ` is pro-`p`. -/
theorem isProP_of_isLocalRing (hp : ¬IsUnit (p : R)) [IsLocalRing (completedGroupAlgebra R Γ)] :
    IsProP p Γ := isProP_iff.mpr fun U ↦ by
  -- `R` is nontrivial, since `R[[Γ]]` is, so the levels `R[Γ ⧸ U]` are nontrivial.
  have : Nontrivial R := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact not_subsingleton (completedGroupAlgebra R Γ)
      ⟨fun x y ↦ ext fun U ↦ Subsingleton.elim _ _⟩
  have : IsLocalRing (_root_.MonoidAlgebra R (Γ ⧸ U.toSubgroup)) :=
    IsLocalRing.of_surjective' (proj R Γ U).toRingHom (proj_surjective R Γ U)
  exact MonoidAlgebra.isPGroup_of_isLocalRing hp

/-- **The completed group algebra is local exactly over a pro-`p` group.** For a local ring `R` in
which the prime `p` is not a unit and a group `Γ` with finite quotients by its open normal
subgroups, for instance a profinite group, the completed group algebra `R[[Γ]]` is a local ring if
and only if `Γ` is pro-`p`. -/
theorem isLocalRing_iff_isProP [IsLocalRing R] (hp : ¬IsUnit (p : R)) :
    IsLocalRing (completedGroupAlgebra R Γ) ↔ IsProP p Γ :=
  ⟨fun _ ↦ isProP_of_isLocalRing hp, fun hΓ ↦
    have := isLocalHom_augmentation_of_isProP hp hΓ
    (augmentation R Γ).domain_isLocalRing⟩

end TauCeti.completedGroupAlgebra
