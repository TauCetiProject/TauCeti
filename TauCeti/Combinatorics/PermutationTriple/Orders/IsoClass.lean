/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.IsoClass
public import TauCeti.Combinatorics.PermutationTriple.Orders.Basic

/-!
# Dividing-order conditions on isomorphism classes of permutation triples

Simultaneous sheet relabeling conjugates the three components of a permutation triple, so the
dividing-order condition `TauCeti.PermutationTriple.HasDividingOrders` is invariant under
isomorphism and descends to `TauCeti.PermutationTriple.IsoClass`, `TauCeti.ConnectedIsoClass`, and
`TauCeti.MarkedIsoClass`. Because the power equations `σ0 ^ a = 1`, `σ1 ^ b = 1`, `σinf ^ c = 1`
are decidable in `Equiv.Perm (Fin n)`, the descended predicates on `IsoClass` and
`ConnectedIsoClass` are decidable as well, cutting out the computable finset
`TauCeti.connectedIsoClassesWithDividingOrders`.
-/

open Equiv

public section

namespace TauCeti

variable {n a b c : ℕ}

namespace PermutationTriple

/-- Relabeling the sheets preserves dividing-order relations. -/
theorem hasDividingOrders_smul_iff (τ : Perm (Fin n)) (t : PermutationTriple n) :
    (τ • t).HasDividingOrders a b c ↔ t.HasDividingOrders a b c := by
  have key {σ : Perm (Fin n)} {k : ℕ} : (τ * σ * τ⁻¹) ^ k = 1 ↔ σ ^ k = 1 := by
    -- Express sheet conjugation via `MulAut.conj τ` so `map_pow` and `map_eq_one_iff` apply.
    change MulAut.conj τ σ ^ k = 1 ↔ σ ^ k = 1
    rw [← map_pow, MulEquiv.map_eq_one_iff]
  simp only [hasDividingOrders_iff, smul_σ0, smul_σ1, smul_σinf, key]

/-- Isomorphic permutation triples satisfy the same dividing-order relations. -/
theorem Equivalent.hasDividingOrders_iff {t t' : PermutationTriple n} (h : t.Equivalent t') :
    t.HasDividingOrders a b c ↔ t'.HasDividingOrders a b c := by
  obtain ⟨τ, rfl⟩ := equivalent_iff_exists_smul_eq.mp h
  exact (hasDividingOrders_smul_iff τ t).symm

instance (t : PermutationTriple n) (a b c : ℕ) : Decidable (t.HasDividingOrders a b c) :=
  decidable_of_iff (t.σ0 ^ a = 1 ∧ t.σ1 ^ b = 1 ∧ t.σinf ^ c = 1) t.hasDividingOrders_iff.symm

namespace IsoClass

/-- An isomorphism class of permutation triples has dividing orders `(a, b, c)` when its
representatives satisfy `σ0 ^ a = 1`, `σ1 ^ b = 1`, and `σinf ^ c = 1`. -/
def HasDividingOrders (C : IsoClass n) (a b c : ℕ) : Prop :=
  lift (fun t ↦ t.HasDividingOrders a b c) (fun _ _ h ↦ propext h.hasDividingOrders_iff) C

@[simp]
theorem hasDividingOrders_mk (t : PermutationTriple n) :
    (mk t).HasDividingOrders a b c ↔ t.HasDividingOrders a b c := by
  rw [HasDividingOrders, lift_mk]

instance (C : IsoClass n) (a b c : ℕ) : Decidable (C.HasDividingOrders a b c) :=
  Quotient.recOnSubsingleton C fun t ↦
    decidable_of_iff (t.HasDividingOrders a b c) <| by
      rw [quotient_mk, hasDividingOrders_mk]

end IsoClass

end PermutationTriple

namespace ConnectedIsoClass

/-- A connected isomorphism class has dividing orders `(a, b, c)` when its underlying triple class
does. -/
def HasDividingOrders (C : ConnectedIsoClass n) (a b c : ℕ) : Prop :=
  C.forget.HasDividingOrders a b c

@[simp]
theorem hasDividingOrders_mk (t : ConnectedTriple n) :
    (mk t).HasDividingOrders a b c ↔ t.1.HasDividingOrders a b c := by
  rw [HasDividingOrders, forget_mk, PermutationTriple.IsoClass.hasDividingOrders_mk]

theorem hasDividingOrders_forget (C : ConnectedIsoClass n) :
    C.forget.HasDividingOrders a b c ↔ C.HasDividingOrders a b c :=
  Iff.rfl

instance (C : ConnectedIsoClass n) (a b c : ℕ) : Decidable (C.HasDividingOrders a b c) :=
  Quotient.recOnSubsingleton' C fun t ↦
    decidable_of_iff (t.1.HasDividingOrders a b c) (hasDividingOrders_mk t).symm

/-- Connected isomorphism classes with dividing orders `(a, b, c)` are the connected elements of
`PermutationTriple.IsoClass n` satisfying `HasDividingOrders a b c`. -/
def equivIsoClassSubtypeDividingOrders (n a b c : ℕ) :
    {C : ConnectedIsoClass n // C.HasDividingOrders a b c} ≃
      {C : PermutationTriple.IsoClass n // C.IsConnected ∧ C.HasDividingOrders a b c} :=
  ((equivSubtype n).subtypeEquiv fun C ↦ by
    obtain ⟨t, rfl⟩ := mk_surjective C
    simp).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter
      PermutationTriple.IsoClass.IsConnected (fun C ↦ C.HasDividingOrders a b c))

@[simp]
theorem coe_equivIsoClassSubtypeDividingOrders_apply
    (C : {C : ConnectedIsoClass n // C.HasDividingOrders a b c}) :
    (equivIsoClassSubtypeDividingOrders n a b c C : PermutationTriple.IsoClass n) = C.1.forget := by
  rcases C with ⟨C, hC⟩
  obtain ⟨t, rfl⟩ := mk_surjective C
  simp [equivIsoClassSubtypeDividingOrders]

end ConnectedIsoClass

/-- The computable finset of connected isomorphism classes of degree `n` whose component orders
divide `(a, b, c)`. -/
@[expose] def connectedIsoClassesWithDividingOrders (n a b c : ℕ) : Finset (ConnectedIsoClass n) :=
  Finset.univ.filter fun C ↦ C.HasDividingOrders a b c

@[simp]
theorem mem_connectedIsoClassesWithDividingOrders {C : ConnectedIsoClass n} :
    C ∈ connectedIsoClassesWithDividingOrders n a b c ↔ C.HasDividingOrders a b c := by
  simp [connectedIsoClassesWithDividingOrders]

theorem card_connectedIsoClassesWithDividingOrders (n a b c : ℕ) :
    (connectedIsoClassesWithDividingOrders n a b c).card =
      Nat.card {C : ConnectedIsoClass n // C.HasDividingOrders a b c} := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun _ ↦ mem_connectedIsoClassesWithDividingOrders)

namespace MarkedIsoClass

/-- A marked isomorphism class has dividing orders `(a, b, c)` when its underlying connected class
does. -/
def HasDividingOrders (m : MarkedIsoClass n) (a b c : ℕ) : Prop :=
  m.forget.HasDividingOrders a b c

@[simp]
theorem hasDividingOrders_mk (t : ConnectedTriple n) (i : Fin n) :
    (mk t i).HasDividingOrders a b c ↔ t.1.HasDividingOrders a b c := by
  rw [HasDividingOrders, forget_mk, ConnectedIsoClass.hasDividingOrders_mk]

theorem hasDividingOrders_forget (m : MarkedIsoClass n) :
    m.forget.HasDividingOrders a b c ↔ m.HasDividingOrders a b c :=
  Iff.rfl

end MarkedIsoClass

end TauCeti
