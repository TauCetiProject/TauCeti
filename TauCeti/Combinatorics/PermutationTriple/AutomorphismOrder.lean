/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.IsoClass

/-!
# Automorphism orders of permutation triple classes

Relabeling the sheets of a permutation triple conjugates its automorphism group in
`Equiv.Perm (Fin n)`, so the order `Nat.card t.automorphismGroup` depends only on the isomorphism
class of `t`. This file descends that order to `TauCeti.PermutationTriple.IsoClass` and
`TauCeti.ConnectedIsoClass`, pairs it with an executable finset count for kernel computations on
finite quotients, and records finiteness of `TauCeti.MarkedIsoClass`.
-/

open Equiv MulAction

public section

namespace TauCeti

variable {n : ℕ}

namespace PermutationTriple

/-- The automorphisms of a permutation triple `t`, enumerated as a finset of sheet permutations. -/
@[expose] def automorphismFinset (t : PermutationTriple n) : Finset (Perm (Fin n)) :=
  Finset.univ.filter fun τ ↦ τ • t = t

@[simp]
theorem mem_automorphismFinset {t : PermutationTriple n} {τ : Perm (Fin n)} :
    τ ∈ t.automorphismFinset ↔ τ ∈ t.automorphismGroup := by
  simp only [automorphismFinset, Finset.mem_filter, Finset.mem_univ, true_and,
    t.mem_automorphismGroup_iff]
  exact ⟨fun h ↦ ⟨by rw [← smul_σ0, h], by rw [← smul_σ1, h]⟩,
    fun ⟨h0, h1⟩ ↦ ext_of_two (by rw [smul_σ0, h0]) (by rw [smul_σ1, h1])⟩

@[simp]
theorem coe_automorphismFinset (t : PermutationTriple n) :
    (t.automorphismFinset : Set (Perm (Fin n))) = t.automorphismGroup := by
  ext τ
  simp

@[simp]
theorem card_automorphismFinset (t : PermutationTriple n) :
    t.automorphismFinset.card = Nat.card t.automorphismGroup := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun _ ↦ mem_automorphismFinset)

/-- Relabeling the sheets preserves the order of the automorphism group. -/
@[simp]
theorem card_automorphismGroup_smul (τ : Perm (Fin n)) (t : PermutationTriple n) :
    Nat.card (τ • t).automorphismGroup = Nat.card t.automorphismGroup := by
  rw [automorphismGroup_smul]
  exact (Nat.card_congr
    (t.automorphismGroup.equivMapOfInjective _ (MulAut.conj τ).injective).toEquiv).symm

/-- Isomorphic permutation triples have automorphism groups of the same order. -/
theorem Equivalent.card_automorphismGroup_eq {t t' : PermutationTriple n} (h : t.Equivalent t') :
    Nat.card t.automorphismGroup = Nat.card t'.automorphismGroup := by
  obtain ⟨τ, rfl⟩ := equivalent_iff_exists_smul_eq.mp h
  exact (card_automorphismGroup_smul τ t).symm

namespace IsoClass

/-- The order of the automorphism group of any representative of an isomorphism class of triples. -/
noncomputable def automorphismOrder : IsoClass n → ℕ :=
  lift (fun t ↦ Nat.card t.automorphismGroup) fun _ _ h ↦ h.card_automorphismGroup_eq

@[simp]
theorem automorphismOrder_mk (t : PermutationTriple n) :
    (mk t).automorphismOrder = Nat.card t.automorphismGroup :=
  lift_mk _ _ t

theorem automorphismOrder_pos (C : IsoClass n) : 0 < C.automorphismOrder := by
  obtain ⟨t, rfl⟩ := mk_surjective C
  rw [automorphismOrder_mk]
  exact Nat.card_pos

end IsoClass

end PermutationTriple

namespace ConnectedIsoClass

/-- The order of the automorphism group of any representative of a connected isomorphism class. -/
noncomputable def automorphismOrder (C : ConnectedIsoClass n) : ℕ :=
  C.forget.automorphismOrder

@[simp]
theorem automorphismOrder_mk (t : ConnectedTriple n) :
    (mk t).automorphismOrder = Nat.card t.1.automorphismGroup := by
  rw [automorphismOrder, forget_mk, PermutationTriple.IsoClass.automorphismOrder_mk]

theorem automorphismOrder_forget (C : ConnectedIsoClass n) :
    C.forget.automorphismOrder = C.automorphismOrder :=
  (rfl)

theorem automorphismOrder_pos (C : ConnectedIsoClass n) : 0 < C.automorphismOrder :=
  C.forget.automorphismOrder_pos

/-- For a connected isomorphism class of degree `n`, the automorphism order divides `n`. -/
theorem automorphismOrder_dvd (C : ConnectedIsoClass n) : C.automorphismOrder ∣ n := by
  obtain ⟨t, rfl⟩ := mk_surjective C
  rw [automorphismOrder_mk]
  exact t.1.card_automorphismGroup_dvd t.2.isPretransitive

/-- Executable automorphism order of a connected isomorphism class, computed from
`TauCeti.PermutationTriple.automorphismFinset`. -/
@[expose] def computedAutomorphismOrder (C : ConnectedIsoClass n) : ℕ :=
  Quotient.liftOn' C (fun t ↦ t.1.automorphismFinset.card) fun t t' h ↦ by
    obtain ⟨τ, rfl⟩ := h
    simp

theorem computedAutomorphismOrder_mk (t : ConnectedTriple n) :
    (mk t).computedAutomorphismOrder = t.1.automorphismFinset.card :=
  (rfl)

/-- The executable automorphism order agrees with the mathematical automorphism order. -/
@[simp]
theorem computedAutomorphismOrder_eq (C : ConnectedIsoClass n) :
    C.computedAutomorphismOrder = C.automorphismOrder := by
  obtain ⟨t, rfl⟩ := mk_surjective C
  simp [computedAutomorphismOrder_mk]

end ConnectedIsoClass

namespace MarkedIsoClass

/-- There are finitely many marked isomorphism classes of connected triples in each degree. -/
instance : Finite (MarkedIsoClass n) :=
  Finite.of_surjective (fun p : ConnectedTriple n × Fin n ↦ mk p.1 p.2) fun c ↦ by
    obtain ⟨t, i, h⟩ := mk_surjective c
    exact ⟨(t, i), h⟩

end MarkedIsoClass

end TauCeti
