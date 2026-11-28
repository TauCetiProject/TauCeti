/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.NNRat.Defs
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.SubMulAction

import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.NNRat.Lemmas
import Mathlib.Data.SetLike.Fintype
import Mathlib.Order.WellFounded
import Mathlib.Order.WellFoundedSet
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Orbit-multiplicative invariants of finite group actions

This file proves the orbit-multiplicative induction principle on finite Δ-sets used in the
permutation-module dévissage for multiplicative invariants of finite R[Δ]-modules:

* TauCeti.orbitCompl: the complement of the orbit of y in a Δ-set Y, as a SubMulAction.
* TauCeti.exists_pow_eq_of_equivariant_quotient: if an orbit-multiplicative invariant  equals
  1 on all proper-subgroup orbits Δ ⧸ K' (K' < K), then its value on any finite Δ-set
  mapping equivariantly to Δ ⧸ K is a natural power of  (Δ ⧸ K).
* TauCeti.eq_one_of_prod_quotient: if X has a Δ-fixed point and  (X × Δ ⧸ K) = 1 for
  every subgroup K ≤ Δ, then  (Δ ⧸ K) = 1 for every subgroup K ≤ Δ.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean, commit
72fead102f663d5c7a407964a13dc0cf9d977207), file src/Lib/General/Algebra/CartanMap.lean
(New.DiscreteModule.orbitCompl, New.DiscreteModule.eq_one_of_prod_quotient).
-/

public section

open MulAction

namespace TauCeti

/-- The complement of the orbit of y in the Δ-set Y, as a Δ-set. -/
abbrev orbitCompl (Δ : Type*) {Y : Type*} [Group Δ] [MulAction Δ Y] (y : Y) : SubMulAction Δ Y :=
  (SubMulAction.mk (orbit Δ y) fun g : Δ ↦ mem_orbit_of_mem_orbit g)ᶜ

/-- Let Δ be a finite group and  an orbit-multiplicative invariant of finite Δ-sets with
values in ℚ≥0. If  (Δ ⧸ K') = 1 for every strict subgroup K' < K, then for every finite
Δ-set Y with an equivariant map Y →[Δ] Δ ⧸ K,  Y is a power of  (Δ ⧸ K). -/
theorem exists_pow_eq_of_equivariant_quotient.{u} (Δ : Type u) [Group Δ] [Finite Δ]
    (f : ∀ (Y : Type u) [Finite Y] [MulAction Δ Y], ℚ≥0)
    (h_empty : ∀ (Y : Type u) [Finite Y] [MulAction Δ Y], IsEmpty Y → f Y = 1)
    (h_orbit : ∀ (Y : Type u) [Finite Y] [MulAction Δ Y] (y : Y),
      f Y = f (orbitCompl Δ y) * f (Δ ⧸ stabilizer Δ y))
    {K : Subgroup Δ} (hK : ∀ K' : Subgroup Δ, K' < K → f (Δ ⧸ K') = 1) :
    ∀ (Y : Type u) [Finite Y] [MulAction Δ Y],
      (Y →[Δ] Δ ⧸ K) → ∃ n : ℕ, f (Δ ⧸ K) ^ n = f Y := by
  refine (measure Nat.card).wf.fix fun Y ihY _ _ p ↦ ?_
  obtain hY | ⟨⟨y₀⟩⟩ := isEmpty_or_nonempty Y
  · exact ⟨0, by simp [h_empty Y hY]⟩
  obtain ⟨y, hy⟩ : ∃ y : Y, p y = ⟦1⟧ :=
    (exists_smul_eq Δ (p y₀) ⟦1⟧).elim fun g hg ↦ ⟨g • y₀, (map_smul p g y₀).trans hg⟩
  have stab_le : stabilizer Δ y ≤ K := fun a ha ↦ by
    simpa [hy, QuotientGroup.eq, mem_stabilizer_iff.mp ha] using (map_smul p a y).symm
  obtain ⟨n, hn⟩ := ihY (orbitCompl Δ y) (Finite.card_subtype_lt (x := y) fun h_compl ↦
    h_compl (mem_orbit_self y)) ⟨fun y' ↦ p y', by simp⟩
  rw [h_orbit Y y, ← hn]
  obtain h_eq | h_lt := stab_le.eq_or_lt
  · exact ⟨n + 1, by rw [h_eq, pow_succ]⟩
  · exact ⟨n, by simp [hK _ h_lt]⟩

/-- Let Δ be a finite group and  a function of finite Δ-sets with values in ℚ≥0 that is 1
on empty sets and satisfies  Y = f (Y ∖ Δ y) * f (Δ ⧸ Stab y) for y ∈ Y. If X has a fixed
point x and  (X × Δ ⧸ K) = 1 for all subgroups K, then  (Δ ⧸ K) = 1 for all K. -/
theorem eq_one_of_prod_quotient.{u, v} (Δ : Type (max u v)) {X : Type u} [Group Δ] [Finite Δ]
    [Finite X] [MulAction Δ X] (f : ∀ (Y : Type (max u v)) [Finite Y] [MulAction Δ Y], ℚ≥0)
    (x : MulAction.fixedPoints Δ X)
    (h_empty : ∀ (Y : Type (max u v)) [Finite Y] [MulAction Δ Y], IsEmpty Y → f Y = 1)
    (h_orbit : ∀ (Y : Type (max u v)) [Finite Y] [MulAction Δ Y] (y : Y),
      f Y = f (orbitCompl Δ y) * f (Δ ⧸ stabilizer Δ y))
    (h_prod : ∀ K : Subgroup Δ, f (X × Δ ⧸ K) = 1) :
    ∀ K : Subgroup Δ, f (Δ ⧸ K) = 1 := by
  refine wellFounded_lt.fix fun K ih ↦ ?_
  let y : X × Δ ⧸ K := (x, ⟦1⟧)
  have h_stab : stabilizer Δ y = K :=
    SetLike.ext fun g ↦ by simp [y, QuotientGroup.eq, x.property g]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, f (Δ ⧸ K) ^ n = f (orbitCompl Δ y) :=
    exists_pow_eq_of_equivariant_quotient Δ f h_empty h_orbit ih (orbitCompl Δ y)
      ⟨fun y' ↦ y'.val.snd, by simp⟩
  have h_pow : f (Δ ⧸ K) ^ (n + 1) = 1 := by
    rw [pow_succ, hn, ← h_prod K, h_orbit (X × Δ ⧸ K) y, h_stab]
  exact (pow_eq_one_iff_of_nonneg zero_le n.succ_ne_zero).mp h_pow

end TauCeti
