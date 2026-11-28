/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.Cochain.SingleEdge
public import TauCeti.GroupTheory.Perm.MovedNorm

/-!
# Transposition single-edge cochain evaluations

Specializations of `TauCeti.Cochain.singleEdge` on `TauCeti.TwoComplex.complete V` to a
transposition `t : Equiv.Perm α` under the moved-point norm `Equiv.Perm.movedNorm α`:

* `TauCeti.Cochain.defect_movedNorm_singleEdge`: the defect at distinct vertices `u ≠ v` equals
  `2 * (Fintype.card V - 2 : ℕ)`.
* `TauCeti.Cochain.gaugeDist_movedNorm_singleEdge_of_three_le_card`: for `3 ≤ Fintype.card V` and
  `u ≠ v`, the gauge distance equals `2`.
-/

public section

namespace TauCeti

namespace Cochain

section MovedNorm

variable {V α : Type*} [Fintype V] [LinearOrder V] [Fintype α] [DecidableEq α]

/-- On `TwoComplex.complete V`, the `Equiv.Perm.movedNorm α` defect of `Cochain.singleEdge` at any
distinct vertices `u ≠ v` and transposition `t` equals `2 * (Fintype.card V - 2 : ℕ)`. -/
theorem defect_movedNorm_singleEdge {u v : V} (huv : u ≠ v) {t : Equiv.Perm α} (ht : t.IsSwap) :
    (singleEdge (TwoComplex.complete V) u v t).defect (Equiv.Perm.movedNorm α) =
      2 * ((Fintype.card V - 2 : ℕ) : ℝ) := by
  rw [defect_singleEdge_complete _ huv t, ht.movedNorm, mul_comm]

/-- On `TwoComplex.complete V` with `3 ≤ Fintype.card V`, the `Equiv.Perm.movedNorm α` gauge
distance of `Cochain.singleEdge` at `u ≠ v` and any transposition `t` equals `2`. -/
theorem gaugeDist_movedNorm_singleEdge_of_three_le_card (hV : 3 ≤ Fintype.card V) {u v : V}
    (huv : u ≠ v) {t : Equiv.Perm α} (ht : t.IsSwap) :
    (singleEdge (TwoComplex.complete V) u v t).gaugeDist (Equiv.Perm.movedNorm α) = 2 := by
  rw [gaugeDist_singleEdge_of_three_le_card Equiv.Perm.isConjInvariant_movedNorm hV huv t,
    ht.movedNorm]

end MovedNorm

end Cochain

end TauCeti
