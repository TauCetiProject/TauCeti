/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.ChordDiagram
public import TauCeti.Combinatorics.NoncrossingPartition.Catalan
public import TauCeti.Order.Partition.PerfectMatching

/-!
# Noncrossing perfect matchings as pair partitions

The orbit-partition equivalence between perfect matchings and pair partitions restricts to
noncrossing objects. This identifies the involution and partition encodings of planar matchings
and transfers the Catalan count from noncrossing pair partitions. The underlying finite linear
order need not be an initial interval of the natural numbers.

The noncrossing compatibility uses
`Function.Involutive.isNoncrossingMatching_iff`; the counting result uses the existing
`TauCeti.NoncrossingPartition.card_isPairing_eq_catalan`.
-/

public section

open Finset

namespace TauCeti.PerfectMatching

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- The orbit-partition conversion preserves and reflects noncrossing. -/
theorem isNoncrossing_toFinpartition_iff (D : PerfectMatching α) :
    D.toFinpartition.IsNoncrossing ↔ D.val.IsNoncrossingMatching := by
  let : DecidableRel (Equiv.Perm.SameCycle.setoid D.val) :=
    inferInstanceAs (DecidableRel D.val.SameCycle)
  simpa only [toFinpartition] using D.prop.involutive.isNoncrossingMatching_iff.symm

/-- Noncrossing perfect matchings are equivalent to noncrossing pair partitions.
The forward map sends an arc to its two-element block. -/
@[expose]
def noncrossingPairingEquiv :
    {D : PerfectMatching α // D.val.IsNoncrossingMatching} ≃
      {P : NoncrossingPartition (univ : Finset α) // P.val.IsPairing} :=
  (pairingEquiv.subtypeEquiv fun D => D.isNoncrossing_toFinpartition_iff.symm).trans
    ((Equiv.subtypeSubtypeEquivSubtypeInter _ _).trans
      ((Equiv.subtypeEquivRight fun _ => and_comm).trans
        (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm))

/-- The noncrossing equivalence has the same underlying partition as the unrestricted one. -/
@[simp]
theorem noncrossingPairingEquiv_apply_coe
    (D : {D : PerfectMatching α // D.val.IsNoncrossingMatching}) :
    (noncrossingPairingEquiv D).val.val = D.val.toFinpartition := rfl

/-- The inverse noncrossing equivalence recovers the unique block partners. -/
@[simp]
theorem noncrossingPairingEquiv_symm_apply_val
    (P : {P : NoncrossingPartition (univ : Finset α) // P.val.IsPairing}) :
    (noncrossingPairingEquiv.symm P).val = P.prop.toPerfectMatching := rfl

/-- A finite linear order with `2 * n` points has `catalan n` noncrossing perfect matchings. -/
theorem card_noncrossing_eq_catalan {n : ℕ} (hn : Fintype.card α = 2 * n) :
    Nat.card {D : PerfectMatching α // D.val.IsNoncrossingMatching} = catalan n := by
  rw [Nat.card_congr (noncrossingPairingEquiv (α := α)), Nat.card_eq_fintype_card]
  exact NoncrossingPartition.card_isPairing_eq_catalan (by simpa using hn)

end TauCeti.PerfectMatching
