/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Sylow
public import TauCeti.Topology.Algebra.Group.Profinite.Index.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic

/-!
# Sylow subgroups of profinite groups

A Sylow pro-`p` subgroup is a closed pro-`p` subgroup whose image in every quotient by an open
normal subgroup has index prime to `p`; for a profinite group these quotients are exactly the
finite continuous ones. This file introduces that predicate and identifies its finite-level
content in two ways: for a profinite group the prime-to-`p` condition is equivalent to
prime-to-`p` supernatural index, and for a discrete group the predicate picks out exactly the
subgroups of finite index underlying Mathlib's `Sylow` subgroups.

The finite comparison supplies the nonempty finite-level systems from which profinite Sylow
subgroups are constructed. Existence and conjugacy in an arbitrary profinite group still require
a separate compatible inverse-limit argument.

## Main definitions and results

* `IsProPSylow`: the predicate for a Sylow pro-`p` subgroup.
* `IsProPSylow.isPGroup_map_mk'`: its image in every finite continuous quotient is a
  `p`-group.
* `isProPSylow_iff_isClosed_and_isProP_and_not_dvd_profiniteIndex`: its
  supernatural-index formulation.
* `isProPSylow_iff_isPGroup_and_not_dvd_index`: its specialization to a discrete group.
* `Sylow.isProPSylow`: a Sylow subgroup of finite index in a discrete group satisfies the
  profinite predicate.
* `isProPSylow_iff_exists_sylow_eq`: agreement with Mathlib's bundled `Sylow` subgroups.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.3.
-/

public section

namespace TauCeti

universe u

/-- A subgroup `P` of a topological group is a **Sylow pro-`p` subgroup** when it is closed,
is itself pro-`p`, and its image in every quotient by an open normal subgroup has index not
divisible by `p`.

The definition is meaningful for an arbitrary topological group; for a profinite group the
quotients above are exactly the finite continuous ones. Compactness and total disconnectedness
enter the existence and conjugacy theorems, rather than the predicate. -/
def IsProPSylow (p : ℕ) {G : Type u} [Group G] [TopologicalSpace G]
    (P : Subgroup G) : Prop :=
  IsClosed (P : Set G) ∧ IsProP p P ∧
    ∀ U : OpenNormalSubgroup G, ¬ p ∣ (P.map (QuotientGroup.mk' U.toSubgroup)).index

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] {P : Subgroup G}

/-- A subgroup is Sylow pro-`p` exactly when it is closed, pro-`p`, and its image in every
quotient by an open normal subgroup has index prime to `p`. -/
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

/-- The image of a Sylow pro-`p` subgroup in every quotient by an open normal subgroup has
index prime to `p`. -/
theorem not_dvd_index (hP : IsProPSylow p P) (U : OpenNormalSubgroup G) :
    ¬ p ∣ (P.map (QuotientGroup.mk' U.toSubgroup)).index :=
  (isProPSylow_iff.mp hP).2.2 U

section

variable [IsTopologicalGroup G]

/-- The image of a Sylow pro-`p` subgroup in a finite continuous quotient is a `p`-group. -/
theorem isPGroup_map_mk' (hP : IsProPSylow p P) (U : OpenNormalSubgroup G) :
    IsPGroup p (P.map (QuotientGroup.mk' U.toSubgroup)) := by
  let f : P →* G ⧸ U.toSubgroup :=
    (QuotientGroup.mk' U.toSubgroup).domRestrict P
  have hf : Continuous f := QuotientGroup.continuous_mk.comp continuous_subtype_val
  have hrange : IsProP p f.range :=
    hP.isProP.of_surjective f.rangeRestrict
      (continuous_induced_rng.mpr hf) f.rangeRestrict_surjective
  rw [← MonoidHom.domRestrict_range]
  exact isProP_iff_isPGroup.mp hrange

end

end IsProPSylow

section ProfiniteIndex

variable [IsTopologicalGroup G] [CompactSpace G]

/-- A subgroup of a profinite group is Sylow pro-`p` exactly when it is closed, is pro-`p`,
and its supernatural index is prime to `p`. -/
theorem isProPSylow_iff_isClosed_and_isProP_and_not_dvd_profiniteIndex (q : Nat.Primes) :
    IsProPSylow q.val P ↔
      IsClosed (P : Set G) ∧ IsProP q.val P ∧
        ¬ (q : Supernatural) ∣ P.profiniteIndex := by
  rw [isProPSylow_iff, P.not_dvd_profiniteIndex_iff_forall_not_dvd_index q]

end ProfiniteIndex

section Discrete

variable [DiscreteTopology G]

/-- On a discrete group, a subgroup is Sylow pro-`p` exactly when it is a `p`-group of index
prime to `p`. -/
@[simp]
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

section FiniteIndex

variable [P.FiniteIndex]

/-- A subgroup of finite index in a discrete group satisfies the profinite predicate exactly
when it is the underlying subgroup of a Mathlib Sylow subgroup. -/
theorem isProPSylow_iff_exists_sylow_eq : IsProPSylow p P ↔
    ∃ Q : Sylow p G, (Q : Subgroup G) = P := by
  constructor
  · intro hP
    obtain ⟨hPp, hPindex⟩ := isProPSylow_iff_isPGroup_and_not_dvd_index.mp hP
    exact ⟨hPp.toSylow hPindex, IsPGroup.toSylow_coe hPp hPindex⟩
  · rintro ⟨Q, rfl⟩
    exact Q.isProPSylow

end FiniteIndex

variable [Finite G]

/-- Every finite discrete group has a Sylow pro-`p` subgroup. This is the finite-level
existence input for the inverse-limit construction of profinite Sylow subgroups. -/
theorem exists_isProPSylow_of_finite : ∃ P : Subgroup G, IsProPSylow p P := by
  let Q : Sylow p G := Sylow.nonempty.some
  exact ⟨(Q : Subgroup G), Q.isProPSylow⟩

end Discrete

end TauCeti
