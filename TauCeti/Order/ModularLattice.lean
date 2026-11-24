/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.ModularLattice
public import TauCeti.Order.Catenary
import TauCeti.Order.KrullDimension

/-!
# Krull dimension of modular lattices, and complements adapted to a flag

In a modular lattice Krull dimension is additive on intervals: for `a ≤ b ≤ c`,
`dim [a, c] = dim [a, b] + dim [b, c]`, finite or not. Consequently every saturated chain from `a`
to `c`, that is every composition series of the interval `[a, c]`, has length `dim [a, c]`, and a
modular lattice of finite Krull dimension is catenary. For the lattice of submodules of a module
this is the additivity of length and the Jordan–Hölder theorem for lengths; the same statements
hold for the lattice of subobjects of an object of an abelian category, which is modular.

In a complemented modular lattice a flag `a ≤ b` has adapted complements: there are `m` and `q`
with `a ⊔ m = b` and `q` complementary to `b`, so that `⊤` is the independent supremum of `a`, `m`
and `q`. For the lattice of subrepresentations of a semisimple representation this is an
invariant splitting `V = A ⊕ M ⊕ Q` with `A ⊕ M = B`.

## Main results

* `Order.krullDim_Icc_eq_krullDim_Icc_add_krullDim_Icc`: in a modular lattice,
  `dim [a, c] = dim [a, b] + dim [b, c]` for `a ≤ b ≤ c`.
* `Order.krullDim_eq_krullDim_Iic_add_krullDim_Ici`: in a bounded modular lattice,
  `dim α = dim (Iic a) + dim (Ici a)`.
* `Order.krullDim_Icc_eq_length_of_covBy`: in a modular lattice, the interval between the
  endpoints of a saturated chain has Krull dimension the length of the chain; and
  `Order.krullDim_eq_length_of_covBy`: a bounded modular lattice with a composition series from `⊥`
  to `⊤` of length `n` has Krull dimension `n`, so that every strict chain has length at most `n`.
* `TauCeti.Order.IsCatenary.of_isModularLattice`: a modular lattice of finite Krull dimension is
  catenary.
* `TauCeti.exists_sup_eq_and_isCompl_of_le`: in a complemented modular lattice, complements
  `⊤ = a ⊕ m ⊕ q` adapted to a flag `a ≤ b`, with `a ⊔ m = b`.

## Implementation notes

The map `x ↦ (x ⊓ b, x ⊔ b)` from `[a, c]` to `[a, b] × [b, c]` is strictly monotone in a modular
lattice (Mathlib's `strictMono_inf_prod_sup`), which bounds `dim [a, c]` by `dim ([a, b] × [b, c])`,
hence by `dim [a, b] + dim [b, c]` (`Order.krullDim_prod_le`). The reverse inequality holds in
every preorder (`Order.krullDim_Icc_add_krullDim_Icc_le`). No composition series or Jordan–Hölder
argument is needed; the statements about saturated chains then follow from the description of
catenary orders by additivity (`TauCeti.Order.krullDim_Icc_eq_length_of_add`,
`TauCeti.Order.isCatenary_iff_krullDim_Icc_add`).

## References

* G. Birkhoff, *Lattice Theory*, 3rd ed., AMS Colloquium Publications 25 (1967), Chapters I
  and II, for modular lattices and the Jordan–Dedekind chain condition.
-/

public section

namespace Order

variable {α : Type*} [Lattice α] [IsModularLattice α]

/-- **Krull dimension is additive on intervals of a modular lattice**: for `a ≤ b ≤ c`,
`dim [a, c] = dim [a, b] + dim [b, c]`. -/
theorem krullDim_Icc_eq_krullDim_Icc_add_krullDim_Icc {a b c : α} (hab : a ≤ b) (hbc : b ≤ c) :
    krullDim (Set.Icc a c) = krullDim (Set.Icc a b) + krullDim (Set.Icc b c) := by
  refine le_antisymm ((krullDim_le_of_strictMono (fun x : Set.Icc a c ↦
    ((⟨x ⊓ b, le_inf x.property.1 hab, inf_le_right⟩ : Set.Icc a b),
      (⟨x ⊔ b, le_sup_right, sup_le x.property.2 hbc⟩ : Set.Icc b c))) fun _ _ h ↦ ?_).trans
    krullDim_prod_le) (krullDim_Icc_add_krullDim_Icc_le hab hbc)
  exact strictMono_inf_prod_sup (z := b) h

/-- **Krull dimension is additive in a bounded modular lattice**: `dim α` is the sum of the Krull
dimensions of the intervals below and above any element. -/
theorem krullDim_eq_krullDim_Iic_add_krullDim_Ici [BoundedOrder α] (a : α) :
    krullDim α = krullDim (Set.Iic a) + krullDim (Set.Ici a) := by
  rw [← krullDim_eq_of_orderIso ((Set.orderIsoOfEq _ _ Set.Icc_bot_top).trans OrderIso.Set.univ),
    krullDim_Icc_eq_krullDim_Icc_add_krullDim_Icc (bot_le : ⊥ ≤ a) le_top,
    krullDim_eq_of_orderIso (Set.orderIsoOfEq _ _ (Set.Icc_bot (a := a))),
    krullDim_eq_of_orderIso (Set.orderIsoOfEq _ _ (Set.Icc_top (a := a)))]

/-- In a modular lattice, the interval between the endpoints of a saturated chain, a composition
series of that interval, has Krull dimension the length of the chain. In particular all saturated
chains with the same endpoints have the same length. -/
theorem krullDim_Icc_eq_length_of_covBy (s : RelSeries {(x, y) : α × α | x ⋖ y}) :
    krullDim (Set.Icc s.head s.last) = s.length :=
  TauCeti.Order.krullDim_Icc_eq_length_of_add
    (fun _ _ _ ↦ krullDim_Icc_eq_krullDim_Icc_add_krullDim_Icc) s

/-- A bounded modular lattice with a composition series from `⊥` to `⊤` of length `n` has Krull
dimension `n`: every strict chain has length at most `n`. -/
theorem krullDim_eq_length_of_covBy [BoundedOrder α] (s : RelSeries {(x, y) : α × α | x ⋖ y})
    (hhead : s.head = ⊥) (hlast : s.last = ⊤) : krullDim α = s.length := by
  rw [← krullDim_Icc_eq_length_of_covBy, hhead, hlast]
  exact (krullDim_eq_of_orderIso
    ((Set.orderIsoOfEq _ _ Set.Icc_bot_top).trans OrderIso.Set.univ)).symm

end Order

namespace TauCeti.Order.IsCatenary

open _root_.Order

/-- **A modular lattice of finite Krull dimension is catenary**: its intervals have finite Krull
dimension, which is additive on them (`Order.krullDim_Icc_eq_krullDim_Icc_add_krullDim_Icc`). -/
instance of_isModularLattice {α : Type*} [Lattice α] [IsModularLattice α]
    [FiniteDimensionalOrder α] : IsCatenary α :=
  isCatenary_iff_krullDim_Icc_add.2 ⟨fun a b _ ↦ ne_top_of_le_ne_top
    krullDim_ne_top_of_finiteDimensionalOrder
    (krullDim_le_of_strictMono (fun x : Set.Icc a b ↦ (x : α)) (Subtype.strictMono_coe _)),
    fun _ _ _ ↦ krullDim_Icc_eq_krullDim_Icc_add_krullDim_Icc⟩

end TauCeti.Order.IsCatenary

namespace TauCeti

/-- **Complements adapted to a flag.** In a complemented modular lattice, for `a ≤ b` there are
`m` and `q` with `a ⊔ m = b` and `q` complementary to `b`. Then `⊤` is the independent supremum
of `a`, `m` and `q`: each of `a` and `m` is complementary to the supremum of the other two. -/
theorem exists_sup_eq_and_isCompl_of_le {α : Type*} [Lattice α] [BoundedOrder α]
    [IsModularLattice α] [ComplementedLattice α] {a b : α} (h : a ≤ b) :
    ∃ m q : α, a ⊔ m = b ∧ IsCompl b q ∧ IsCompl a (m ⊔ q) ∧ IsCompl m (a ⊔ q) := by
  obtain ⟨m, hm, hm'⟩ := IsModularLattice.exists_disjoint_and_sup_eq h
  obtain ⟨q, hq⟩ := exists_isCompl b
  exact ⟨m, q, hm', hq, hm.isCompl_sup_right_of_isCompl_sup_left (hm' ▸ hq),
    hm.symm.isCompl_sup_right_of_isCompl_sup_left ((sup_comm m a ▸ hm') ▸ hq)⟩

end TauCeti
