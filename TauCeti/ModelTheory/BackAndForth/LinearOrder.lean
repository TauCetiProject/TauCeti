/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.BackAndForth.Equivalence
public import TauCeti.ModelTheory.Order
public import TauCeti.Order.Compare
public import Mathlib.ModelTheory.Order

/-!
# Atomic types and back-and-forth equivalence in the language of orders

In the language of orders, whose only symbol is `≤`, two tuples have the same atomic type exactly
when they have the same equalities and order relations between their entries. For linear orders,
read as structures in this language through Mathlib's `FirstOrder.Language.orderStructure`, this
means that their entries compare in the same way under `cmp`. Back-and-forth equivalence of tuples
of orders is carried along order isomorphisms.

## Main results

* `TauCeti.sameAtomicType_order_iff`: in the language of orders, two tuples have the same atomic
  type exactly when they have the same equalities and order relations between their entries.
* `TauCeti.sameAtomicType_order_iff_cmp`: tuples of linear orders have the same atomic type
  exactly when their entries compare in the same way.
* `TauCeti.BFEquiv.orderIso_comp`: back-and-forth equivalence of tuples of orders is preserved by
  order isomorphisms.
* `TauCeti.BFEquiv.orderIso_congr`: the same for orders as structures, that is, for the empty
  tuple.
* `TauCeti.bfEquiv_of_type_lt_eq`: well-orders of the same order type are back-and-forth
  equivalent at every level.
-/

public section

universe w w' u₁ u₂ o

namespace TauCeti

open FirstOrder FirstOrder.Language Fin

section Atomic

variable {M : Type w} {N : Type w'} [LE M] [LE N]
variable [Language.order.Structure M] [Language.order.OrderedStructure M]
variable [Language.order.Structure N] [Language.order.OrderedStructure N]

/-- In the language of orders, two tuples have the same atomic type exactly when they have the
same equalities and the same order relations between their entries. -/
theorem sameAtomicType_order_iff {n : ℕ} (a : Fin n → M) (b : Fin n → N) :
    SameAtomicType (L := Language.order) a b ↔
      (∀ i j, a i = a j ↔ b i = b j) ∧ ∀ i j, a i ≤ a j ↔ b i ≤ b j := by
  rw [sameAtomicType_iff]
  refine and_congr_right fun _ => ⟨fun h i j => ?_, fun h k r f => ?_⟩
  · simpa [relMap_leSymb] using h leSymb ![i, j]
  · obtain ⟨⟩ := r
    rw [order.relation_eq_leSymb .le, relMap_leSymb, relMap_leSymb]
    exact h (f 0) (f 1)

end Atomic

attribute [local instance] orderStructure

section LinearOrder

variable {M : Type w} {N : Type w'} [LinearOrder M] [LinearOrder N] {n : ℕ}

/-- In the language of orders, tuples of two linear orders have the same atomic type exactly when
their entries compare in the same way. -/
theorem sameAtomicType_order_iff_cmp (a : Fin n → M) (b : Fin n → N) :
    SameAtomicType (L := Language.order) a b ↔ ∀ i j, cmp (a i) (a j) = cmp (b i) (b j) := by
  rw [sameAtomicType_order_iff]
  exact ⟨fun ⟨_, hle⟩ i j => cmp_eq_cmp_of_le_iff_le (hle i j) (hle j i), fun h =>
    ⟨fun i j => eq_iff_eq_of_cmp_eq_cmp (h i j), fun i j => le_iff_le_of_cmp_eq_cmp (h i j)⟩⟩

/-- Extending two tuples of the same atomic type by one point each preserves the atomic type
exactly when the new points compare with the old entries in the same way. -/
theorem sameAtomicType_snoc_iff_cmp {a : Fin n → M} {b : Fin n → N} {x : M} {y : N} :
    SameAtomicType (L := Language.order) (snoc a x) (snoc b y) ↔
      SameAtomicType (L := Language.order) a b ∧ ∀ i, cmp (a i) x = cmp (b i) y := by
  simp only [sameAtomicType_order_iff_cmp, forall_fin_succ', snoc_castSucc, snoc_last,
    cmp_self_eq_eq, and_true]
  exact ⟨fun h => ⟨fun i => (h.1 i).1, fun i => (h.1 i).2⟩,
    fun h => ⟨fun i => ⟨h.1 i, h.2 i⟩, fun j => cmp_eq_cmp_symm.1 (h.2 j)⟩⟩

/-- Any two points of linear orders have the same atomic type. -/
theorem sameAtomicType_snoc_elim0 (x : M) (y : N) :
    SameAtomicType (L := Language.order) (snoc (Fin.elim0 : Fin 0 → M) x)
      (snoc (Fin.elim0 : Fin 0 → N) y) :=
  sameAtomicType_snoc_iff_cmp.2 ⟨sameAtomicType_elim0, finZeroElim⟩

end LinearOrder

section OrderIso

variable {M : Type w} {N : Type w'} {M' : Type u₁} {N' : Type u₂} [LE M] [LE N] [LE M'] [LE N']
  {n : ℕ}

/-- Back-and-forth equivalence of tuples of orders is preserved by order isomorphisms. -/
theorem BFEquiv.orderIso_comp {γ : Ordinal.{o}} {a : Fin n → M} {b : Fin n → N}
    (h : BFEquiv (L := Language.order) γ n a b) (e : M ≃o M') (f : N ≃o N') :
    BFEquiv (L := Language.order) γ n (e ∘ a) (f ∘ b) :=
  ((StrongHomClass.toEquiv e : M ≃[Language.order] M').bfEquiv γ a).symm.trans
    (h.trans ((StrongHomClass.toEquiv f : N ≃[Language.order] N').bfEquiv γ b))

/-- Back-and-forth equivalence of orders, as structures with the empty tuple, is preserved by
order isomorphisms. -/
theorem BFEquiv.orderIso_congr {γ : Ordinal.{o}}
    (h : BFEquiv (L := Language.order) γ 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N))
    (e : M ≃o M') (f : N ≃o N') :
    BFEquiv (L := Language.order) γ 0 (Fin.elim0 : Fin 0 → M') (Fin.elim0 : Fin 0 → N') := by
  have h' := h.orderIso_comp e f
  rwa [Subsingleton.elim (_ ∘ Fin.elim0) Fin.elim0, Subsingleton.elim (_ ∘ Fin.elim0) Fin.elim0]
    at h'

end OrderIso

section WellOrder

open Ordinal

/-- Well-orders of the same order type are back-and-forth equivalent at every level. -/
theorem bfEquiv_of_type_lt_eq {A B : Type u₁} [LinearOrder A] [LinearOrder B]
    [WellFoundedLT A] [WellFoundedLT B] (h : typeLT A = typeLT B) (γ : Ordinal.{o}) :
    BFEquiv (L := Language.order) γ 0 (Fin.elim0 : Fin 0 → A) (Fin.elim0 : Fin 0 → B) :=
  (BFEquiv.refl γ _).orderIso_congr (OrderIso.refl A) (OrderIso.ofRelIsoLT (type_eq.1 h).some)

end WellOrder

end TauCeti
