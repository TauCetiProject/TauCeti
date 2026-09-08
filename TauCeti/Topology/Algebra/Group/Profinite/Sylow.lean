/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Sylow
public import TauCeti.Topology.Algebra.Group.Profinite.Index
public import TauCeti.Topology.Algebra.Group.Profinite.ProP
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Sylow subgroups of profinite groups

A Sylow pro-`p` subgroup is a closed pro-`p` subgroup whose image in every finite continuous
quotient has index prime to `p`. This file introduces that predicate and identifies its
finite-level content in two ways: the prime-to-`p` condition is equivalent to prime-to-`p`
supernatural index, and for finite discrete groups the predicate agrees with Mathlib's
`Sylow` subgroups.

The finite comparison supplies the nonempty finite-level systems from which profinite Sylow
subgroups are constructed. Existence and conjugacy in an arbitrary profinite group require a
compatible inverse-limit argument and are developed separately.

## Main definitions and results

* `IsProPSylow`: the predicate for a Sylow pro-`p` subgroup.
* `isProPSylow_iff_not_dvd_profiniteIndex`: its supernatural-index formulation.
* `isProPSylow_iff_isPGroup_and_not_dvd_index`: its finite discrete specialization.
* `Sylow.isProPSylow`: a finite Sylow subgroup satisfies the profinite predicate.
* `isProPSylow_iff_exists_sylow_eq`: agreement with Mathlib's bundled `Sylow` subgroups.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.3.
-/

public section

namespace TauCeti

universe u

/-- A subgroup `P` of a profinite group is a **Sylow pro-`p` subgroup** when it is closed,
is itself pro-`p`, and its image in every finite continuous quotient has index not divisible
by `p`.

The definition is meaningful for an arbitrary topological group. Compactness and total
disconnectedness enter the existence and conjugacy theorems, rather than the predicate. -/
def IsProPSylow (p : ℕ) {G : Type u} [Group G] [TopologicalSpace G]
    (P : Subgroup G) : Prop :=
  IsClosed (P : Set G) ∧ IsProP p P ∧
    ∀ U : OpenNormalSubgroup G, ¬ p ∣ (P.map (QuotientGroup.mk' U.toSubgroup)).index

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] {P : Subgroup G}

/-- The defining conditions for a Sylow pro-`p` subgroup. -/
theorem isProPSylow_iff : IsProPSylow p P ↔
    IsClosed (P : Set G) ∧ IsProP p P ∧
      ∀ U : OpenNormalSubgroup G, ¬ p ∣ (P.map (QuotientGroup.mk' U.toSubgroup)).index :=
  Iff.rfl

namespace IsProPSylow

/-- A Sylow pro-`p` subgroup is closed. -/
theorem isClosed (hP : IsProPSylow p P) : IsClosed (P : Set G) :=
  (isProPSylow_iff.mp hP).1

/-- A Sylow pro-`p` subgroup is pro-`p` in its subspace topology. -/
theorem isProP (hP : IsProPSylow p P) : IsProP p P :=
  (isProPSylow_iff.mp hP).2.1

/-- The image of a Sylow pro-`p` subgroup in every finite continuous quotient has index
prime to `p`. -/
theorem not_dvd_index (hP : IsProPSylow p P) (U : OpenNormalSubgroup G) :
    ¬ p ∣ (P.map (QuotientGroup.mk' U.toSubgroup)).index :=
  (isProPSylow_iff.mp hP).2.2 U

end IsProPSylow

section ProfiniteIndex

variable [IsTopologicalGroup G] [CompactSpace G]

/-- The finite-quotient and supernatural-index formulations of the prime-to-`p` condition
for a subgroup of a profinite group agree. -/
theorem not_dvd_profiniteIndex_iff_forall_not_dvd_index (q : Nat.Primes) :
    ¬ (q : Supernatural) ∣ P.profiniteIndex ↔
      ∀ U : OpenNormalSubgroup G, ¬ q.val ∣
        (P.map (QuotientGroup.mk' U.toSubgroup)).index := by
  let _ : Fact q.val.Prime := ⟨q.prop⟩
  constructor
  · intro h U hpU
    apply h
    rw [Supernatural.coe_prime_dvd_iff, Subgroup.profiniteIndex_apply]
    have hval : (padicValNat q.val
        (P.map (QuotientGroup.mk' U.toSubgroup)).index : ℕ∞) ≠ 0 := by
      exact_mod_cast (dvd_iff_padicValNat_ne_zero
        (Subgroup.index_ne_zero_of_finite (H := P.map (QuotientGroup.mk' U.toSubgroup)))).mp hpU
    exact fun hsup ↦ hval <| le_antisymm
      ((le_iSup (fun V : OpenNormalSubgroup G ↦
        (padicValNat q.val (P.map (QuotientGroup.mk' V.toSubgroup)).index : ℕ∞)) U).trans_eq hsup)
      bot_le
  · intro h
    rw [Supernatural.coe_prime_dvd_iff, not_ne_iff, Subgroup.profiniteIndex_apply,
      ENat.iSup_eq_zero]
    intro U
    exact_mod_cast padicValNat.eq_zero_of_not_dvd (h U)

/-- A closed pro-`p` subgroup is Sylow exactly when its supernatural index is prime to `p`. -/
theorem isProPSylow_iff_not_dvd_profiniteIndex (q : Nat.Primes) : IsProPSylow q.val P ↔
    IsClosed (P : Set G) ∧ IsProP q.val P ∧
      ¬ (q : Supernatural) ∣ P.profiniteIndex := by
  rw [isProPSylow_iff, not_dvd_profiniteIndex_iff_forall_not_dvd_index q]

end ProfiniteIndex

section Finite

variable [DiscreteTopology G]

/-- On a finite discrete group, a subgroup is Sylow pro-`p` exactly when it is a `p`-group
of index prime to `p`. -/
theorem isProPSylow_iff_isPGroup_and_not_dvd_index :
    IsProPSylow p P ↔ IsPGroup p P ∧ ¬ p ∣ P.index := by
  constructor
  · intro hP
    refine ⟨isProP_iff_isPGroup.mp hP.isProP, ?_⟩
    let U := openNormalSubgroupBot G
    have hindex : (P.map (QuotientGroup.mk' U.toSubgroup)).index = P.index :=
      P.index_map_eq (QuotientGroup.mk'_surjective U.toSubgroup) <| by
        rw [QuotientGroup.ker_mk', openNormalSubgroupBot_toSubgroup]
        exact bot_le
    simpa only [hindex] using hP.not_dvd_index U
  · rintro ⟨hP, hindex⟩
    refine isProPSylow_iff.mpr ⟨isClosed_discrete _, isProP_iff_isPGroup.mpr hP, ?_⟩
    intro U hpU
    exact hindex (hpU.trans (P.index_map_dvd (QuotientGroup.mk'_surjective U.toSubgroup)))

variable [Fact p.Prime]

/-- A Mathlib Sylow subgroup of finite index in a discrete group is a Sylow pro-`p`
subgroup. -/
theorem _root_.Sylow.isProPSylow (Q : Sylow p G) [Q.FiniteIndex] :
    IsProPSylow p (Q : Subgroup G) :=
  isProPSylow_iff_isPGroup_and_not_dvd_index.mpr ⟨Q.isPGroup', Q.not_dvd_index⟩

variable [Finite G]

/-- The profinite predicate on a finite discrete group is equivalent to being the underlying
subgroup of a Mathlib Sylow subgroup. -/
theorem isProPSylow_iff_exists_sylow_eq : IsProPSylow p P ↔
    ∃ Q : Sylow p G, (Q : Subgroup G) = P := by
  constructor
  · intro hP
    obtain ⟨hPp, hPindex⟩ := isProPSylow_iff_isPGroup_and_not_dvd_index.mp hP
    exact ⟨hPp.toSylow hPindex, IsPGroup.toSylow_coe hPp hPindex⟩
  · rintro ⟨Q, rfl⟩
    exact Q.isProPSylow

/-- Every finite discrete group has a Sylow pro-`p` subgroup. This is the finite-level
existence input for the inverse-limit construction of profinite Sylow subgroups. -/
theorem exists_isProPSylow_of_finite : ∃ P : Subgroup G, IsProPSylow p P := by
  let Q : Sylow p G := Sylow.nonempty.some
  exact ⟨(Q : Subgroup G), Q.isProPSylow⟩

end Finite

end TauCeti
