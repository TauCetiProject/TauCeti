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
are decidable in `Equiv.Perm (Fin n)`, the descended predicates on `IsoClass`, `ConnectedIsoClass`,
and `MarkedIsoClass` are decidable as well, cutting out the computable finset
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
  simp only [hasDividingOrders_iff, smul_σ0, smul_σ1, smul_σinf, conj_pow, conj_eq_one_iff]

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

/-- The isomorphism class of `t` has dividing orders `(a, b, c)` iff `t` does. -/
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

/-- `ConnectedIsoClass.mk t` has dividing orders `(a, b, c)` iff `t.1` does. -/
@[simp]
theorem hasDividingOrders_mk (t : ConnectedTriple n) :
    (mk t).HasDividingOrders a b c ↔ t.val.HasDividingOrders a b c := by
  rw [HasDividingOrders, forget_mk, PermutationTriple.IsoClass.hasDividingOrders_mk]

/-- Forgetting connectedness preserves `HasDividingOrders`. -/
theorem hasDividingOrders_forget (C : ConnectedIsoClass n) :
    C.forget.HasDividingOrders a b c ↔ C.HasDividingOrders a b c :=
  Iff.rfl

instance (C : ConnectedIsoClass n) (a b c : ℕ) : Decidable (C.HasDividingOrders a b c) :=
  Quotient.recOnSubsingleton' C fun t ↦
    decidable_of_iff (t.val.HasDividingOrders a b c) (hasDividingOrders_mk t).symm

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

/-- `equivIsoClassSubtypeDividingOrders` acts on underlying classes via `ConnectedIsoClass.forget`.
-/
@[simp]
theorem coe_equivIsoClassSubtypeDividingOrders_apply
    (C : {C : ConnectedIsoClass n // C.HasDividingOrders a b c}) :
    (equivIsoClassSubtypeDividingOrders n a b c C : PermutationTriple.IsoClass n) = C.val.forget
        := by
  rcases C with ⟨C, hC⟩
  obtain ⟨t, rfl⟩ := mk_surjective C
  simp [equivIsoClassSubtypeDividingOrders]

/-- The inverse of `equivIsoClassSubtypeDividingOrders` sends `IsoClass.mk t` to
`ConnectedIsoClass.mk ⟨t, ...⟩`. -/
@[simp]
theorem coe_equivIsoClassSubtypeDividingOrders_symm_mk (t : PermutationTriple n)
    (h : (PermutationTriple.IsoClass.mk t).IsConnected ∧
      (PermutationTriple.IsoClass.mk t).HasDividingOrders a b c) :
    ((equivIsoClassSubtypeDividingOrders n a b c).symm
      ⟨PermutationTriple.IsoClass.mk t, h⟩ : ConnectedIsoClass n) =
      mk ⟨t, (PermutationTriple.IsoClass.isConnected_mk t).mp h.1⟩ := by
  apply forget_injective
  have key := (equivIsoClassSubtypeDividingOrders n a b c).apply_symm_apply
    ⟨PermutationTriple.IsoClass.mk t, h⟩
  exact (coe_equivIsoClassSubtypeDividingOrders_apply _).symm.trans <|
    (congrArg Subtype.val key).trans
      (forget_mk ⟨t, (PermutationTriple.IsoClass.isConnected_mk t).mp h.1⟩).symm

end ConnectedIsoClass

/-- The computable finset of connected isomorphism classes of degree `n` whose component orders
divide `(a, b, c)`. -/
@[expose] def connectedIsoClassesWithDividingOrders (n a b c : ℕ) : Finset (ConnectedIsoClass n) :=
  Finset.univ.filter fun C ↦ C.HasDividingOrders a b c

/-- A connected class belongs to `connectedIsoClassesWithDividingOrders n a b c` iff it satisfies
`HasDividingOrders a b c`. -/
@[simp]
theorem mem_connectedIsoClassesWithDividingOrders {C : ConnectedIsoClass n} :
    C ∈ connectedIsoClassesWithDividingOrders n a b c ↔ C.HasDividingOrders a b c := by
  simp [connectedIsoClassesWithDividingOrders]

/-- The cardinality of `connectedIsoClassesWithDividingOrders n a b c` equals `Nat.card` of the
subtype `{C : ConnectedIsoClass n // C.HasDividingOrders a b c}`. -/
theorem card_connectedIsoClassesWithDividingOrders (n a b c : ℕ) :
    (connectedIsoClassesWithDividingOrders n a b c).card =
      Nat.card {C : ConnectedIsoClass n // C.HasDividingOrders a b c} := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun _ ↦ mem_connectedIsoClassesWithDividingOrders)

/-- In degree zero there are no connected isomorphism classes. -/
@[simp]
theorem connectedIsoClassesWithDividingOrders_zero (a b c : ℕ) :
    connectedIsoClassesWithDividingOrders 0 a b c = ∅ := by
  have : IsEmpty (ConnectedIsoClass 0) :=
    ⟨fun C ↦ let ⟨t, _⟩ := ConnectedIsoClass.mk_surjective C; t.property.ne_zero rfl⟩
  exact Finset.eq_empty_of_isEmpty _

namespace MarkedIsoClass

/-- A marked isomorphism class has dividing orders `(a, b, c)` when its underlying connected class
does. -/
def HasDividingOrders (m : MarkedIsoClass n) (a b c : ℕ) : Prop :=
  m.forget.HasDividingOrders a b c

/-- `MarkedIsoClass.mk t i` has dividing orders `(a, b, c)` iff `t.1` does. -/
@[simp]
theorem hasDividingOrders_mk (t : ConnectedTriple n) (i : Fin n) :
    (mk t i).HasDividingOrders a b c ↔ t.val.HasDividingOrders a b c := by
  rw [HasDividingOrders, forget_mk, ConnectedIsoClass.hasDividingOrders_mk]

/-- Forgetting the marked sheet preserves `HasDividingOrders`. -/
theorem hasDividingOrders_forget (m : MarkedIsoClass n) :
    m.forget.HasDividingOrders a b c ↔ m.HasDividingOrders a b c :=
  Iff.rfl

instance (m : MarkedIsoClass n) (a b c : ℕ) : Decidable (m.HasDividingOrders a b c) :=
  inferInstanceAs (Decidable (m.forget.HasDividingOrders a b c))

end MarkedIsoClass

end TauCeti
