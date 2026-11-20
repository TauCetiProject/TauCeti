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
class of `t`. This file descends that order to `TauCeti.PermutationTriple.IsoClass`,
`TauCeti.ConnectedIsoClass`, and `TauCeti.MarkedIsoClass`, and pairs it with an executable finset
count (`TauCeti.PermutationTriple.automorphismFinset` and
`TauCeti.ConnectedIsoClass.computedAutomorphismOrder`) for kernel computations on finite quotients.
-/

open Equiv MulAction

public section

namespace TauCeti

variable {n : ℕ}

namespace PermutationTriple

/-- The automorphisms of a permutation triple `t`, enumerated as a finset of sheet permutations. -/
@[expose] def automorphismFinset (t : PermutationTriple n) : Finset (Perm (Fin n)) :=
  Finset.univ.filter fun τ ↦ τ • t = t

/-- A sheet permutation belongs to `t.automorphismFinset` if and only if it belongs to
`t.automorphismGroup`. -/
@[simp]
theorem mem_automorphismFinset {t : PermutationTriple n} {τ : Perm (Fin n)} :
    τ ∈ t.automorphismFinset ↔ τ ∈ t.automorphismGroup := by
  simp only [automorphismFinset, Finset.mem_filter, Finset.mem_univ, true_and,
    t.mem_automorphismGroup_iff]
  exact ⟨fun h ↦ ⟨by rw [← smul_σ0, h], by rw [← smul_σ1, h]⟩,
    fun ⟨h0, h1⟩ ↦ ext_of_two (by rw [smul_σ0, h0]) (by rw [smul_σ1, h1])⟩

/-- Coercing `t.automorphismFinset` to a set recovers the carrier of `t.automorphismGroup`. -/
@[simp]
theorem coe_automorphismFinset (t : PermutationTriple n) :
    (t.automorphismFinset : Set (Perm (Fin n))) = t.automorphismGroup := by
  ext τ
  simp

/-- The cardinality of `t.automorphismFinset` equals `Nat.card t.automorphismGroup`. -/
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

/-- On the class of `t`, `automorphismOrder` evaluates to `Nat.card t.automorphismGroup`. -/
@[simp]
theorem automorphismOrder_mk (t : PermutationTriple n) :
    (mk t).automorphismOrder = Nat.card t.automorphismGroup :=
  lift_mk _ _ t

/-- Every isomorphism class of permutation triples has positive automorphism order. -/
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

/-- On the connected class of `t`, `automorphismOrder` evaluates to
`Nat.card t.1.automorphismGroup`. -/
@[simp]
theorem automorphismOrder_mk (t : ConnectedTriple n) :
    (mk t).automorphismOrder = Nat.card t.val.automorphismGroup := by
  rw [automorphismOrder, forget_mk, PermutationTriple.IsoClass.automorphismOrder_mk]

/-- Forgetting connectedness preserves `automorphismOrder`. -/
theorem automorphismOrder_forget (C : ConnectedIsoClass n) :
    C.forget.automorphismOrder = C.automorphismOrder :=
  (rfl)

/-- Every connected isomorphism class has positive automorphism order. -/
theorem automorphismOrder_pos (C : ConnectedIsoClass n) : 0 < C.automorphismOrder :=
  C.forget.automorphismOrder_pos

/-- For a connected isomorphism class of degree `n`, the automorphism order divides `n`. -/
theorem automorphismOrder_dvd (C : ConnectedIsoClass n) : C.automorphismOrder ∣ n := by
  obtain ⟨t, rfl⟩ := mk_surjective C
  rw [automorphismOrder_mk]
  exact t.val.card_automorphismGroup_dvd t.property.isPretransitive

/-- Executable automorphism order of a connected isomorphism class, computed from
`TauCeti.PermutationTriple.automorphismFinset`. -/
@[expose] def computedAutomorphismOrder (C : ConnectedIsoClass n) : ℕ :=
  Quotient.liftOn' C (fun t ↦ t.val.automorphismFinset.card) fun t t' h ↦ by
    obtain ⟨τ, rfl⟩ := h
    simp

/-- On `ConnectedIsoClass.mk t`, `computedAutomorphismOrder` is `t.1.automorphismFinset.card`. -/
theorem computedAutomorphismOrder_mk (t : ConnectedTriple n) :
    (mk t).computedAutomorphismOrder = t.val.automorphismFinset.card :=
  (rfl)

/-- The executable automorphism order agrees with the mathematical automorphism order. -/
@[simp]
theorem computedAutomorphismOrder_eq (C : ConnectedIsoClass n) :
    C.computedAutomorphismOrder = C.automorphismOrder := by
  obtain ⟨t, rfl⟩ := mk_surjective C
  simp [computedAutomorphismOrder_mk]

end ConnectedIsoClass

namespace MarkedIsoClass

/-- The automorphism order of the underlying connected class of a marked isomorphism class. -/
noncomputable def automorphismOrder (m : MarkedIsoClass n) : ℕ :=
  m.forget.automorphismOrder

/-- On `MarkedIsoClass.mk t i`, `automorphismOrder` is `Nat.card t.1.automorphismGroup`. -/
@[simp]
theorem automorphismOrder_mk (t : ConnectedTriple n) (i : Fin n) :
    (mk t i).automorphismOrder = Nat.card t.val.automorphismGroup := by
  rw [automorphismOrder, forget_mk, ConnectedIsoClass.automorphismOrder_mk]

/-- Forgetting the marked sheet preserves `automorphismOrder`. -/
theorem automorphismOrder_forget (m : MarkedIsoClass n) :
    m.forget.automorphismOrder = m.automorphismOrder :=
  (rfl)

end MarkedIsoClass

end TauCeti
