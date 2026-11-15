/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.OrbitCount.Basic
public import Mathlib.GroupTheory.Perm.Fin

/-!
# Orbits of cyclic rotation

Cyclic rotation of a nonempty finite ordinal is a single cycle through every point, including the
singleton case where the rotation is the identity: its full cycle partition has the one part `n`,
so it has one orbit and order `n`. Its powers that are again single cycles through every point
are exactly those with exponent coprime to `n`. The orbit count includes fixed points. The
formula is useful when a traversal permutation is identified, up to conjugacy, with cyclic
rotation: it reduces the resulting orbit or component count to whether the underlying ordinal is
empty. Conversely, every permutation of a finite type with a single orbit becomes cyclic rotation
after numbering the type suitably (`TauCeti.exists_equiv_permCongr_eq_finRotate`).
-/

public section

namespace TauCeti

open Equiv Equiv.Perm

/-- The full cycle partition of cyclic rotation of a nonempty finite ordinal has the single
part `n`. -/
theorem parts_partition_finRotate {n : ℕ} (hn : n ≠ 0) : (finRotate n).partition.parts = {n} := by
  rcases n with _ | _ | n
  · exact absurd rfl hn
  -- For `n = 1` the rotation is the identity of `Fin 1`, whose only part is its one fixed point.
  · simp [finRotate_one, ← Equiv.Perm.one_def]
  · rw [parts_partition_of_isCycle isCycle_finRotate, support_finRotate]
    simp

/-- Cyclic rotation of a nonempty finite ordinal of length `n` has order `n`. -/
theorem orderOf_finRotate {n : ℕ} (hn : n ≠ 0) : orderOf (finRotate n) = n := by
  rw [← lcm_parts_partition, parts_partition_finRotate hn, Multiset.lcm_singleton, normalize_eq]

/-- A power of cyclic rotation of a nonempty finite ordinal of length `n`, with exponent coprime
to `n`, is again a single cycle through every point: its full cycle partition has the single
part `n`. -/
theorem parts_partition_finRotate_pow {n k : ℕ} (hn : n ≠ 0) (hk : k.Coprime n) :
    (finRotate n ^ k).partition.parts = {n} := by
  rcases n with _ | _ | n
  · exact absurd rfl hn
  · rw [Subsingleton.elim (finRotate 1 ^ k) (finRotate 1)]
    exact parts_partition_finRotate one_ne_zero
  · have hk' : k.Coprime (orderOf (finRotate (n + 2))) := by rwa [orderOf_finRotate hn]
    rw [parts_partition_of_isCycle (isCycle_finRotate.pow_iff.mpr hk'), support_pow_coprime hk',
      support_finRotate]
    simp

/-- A power of cyclic rotation of a nonempty finite ordinal of length `n` is a single cycle
through every point exactly when its exponent is coprime to `n`. -/
@[simp]
theorem parts_partition_finRotate_pow_eq_singleton_iff {n k : ℕ} (hn : n ≠ 0) :
    (finRotate n ^ k).partition.parts = {n} ↔ k.Coprime n := by
  refine ⟨fun h => ?_, parts_partition_finRotate_pow hn⟩
  have hord : orderOf (finRotate n ^ k) = n := by
    rw [← lcm_parts_partition, h, Multiset.lcm_singleton, normalize_eq]
  rw [orderOf_pow, orderOf_finRotate hn, Nat.div_eq_self] at hord
  exact Nat.Coprime.symm (hord.resolve_left hn)

/-- Cyclic rotation has one orbit when the ordinal is nonempty, and none otherwise. -/
@[simp]
theorem orbitCount_finRotate (n : ℕ) : orbitCount (finRotate n) = if n = 0 then 0 else 1 := by
  split_ifs with hn
  · subst hn
    rw [orbitCount_eq_card_parts_partition, parts_partition_of_isEmpty, Multiset.card_zero]
  · rw [orbitCount_eq_card_parts_partition, parts_partition_finRotate hn, Multiset.card_singleton]

/-- **A permutation with one orbit is cyclic rotation in a suitable numbering.** A permutation
of a finite type with a single orbit is carried to cyclic rotation by some equivalence of the
type with `Fin n`. -/
theorem exists_equiv_permCongr_eq_finRotate {α : Type*} [Fintype α] {σ : Perm α}
    (hσ : orbitCount σ = 1) : ∃ e : α ≃ Fin (Fintype.card α), e.permCongr σ = finRotate _ := by
  classical
  set n := Fintype.card α
  let e₀ := Fintype.equivFin α
  have hn : n ≠ 0 := by
    intro hn
    have : IsEmpty α := Fintype.card_eq_zero_iff.mp hn
    rw [orbitCount_def, Nat.card_of_isEmpty] at hσ
    exact zero_ne_one hσ
  -- The numbered permutation has a single cycle through all `n` points, like the rotation.
  have hparts : (e₀.permCongr σ).partition.parts = {n} := by
    have hcard := orbitCount_eq_card_parts_partition (e₀.permCongr σ)
    rw [Equiv.orbitCount_permCongr, hσ, eq_comm, Multiset.card_eq_one] at hcard
    obtain ⟨m, hm⟩ := hcard
    have hsum := (e₀.permCongr σ).partition.parts_sum
    rw [hm, Multiset.sum_singleton, Fintype.card_fin] at hsum
    rw [hm, hsum]
  obtain ⟨c, hc⟩ := isConj_iff.mp (partition_eq_of_isConj.mpr
    (Nat.Partition.ext (hparts.trans (parts_partition_finRotate hn).symm)))
  refine ⟨e₀.trans c, Equiv.ext fun x => ?_⟩
  rw [← hc]
  simp [Perm.mul_apply]

end TauCeti
