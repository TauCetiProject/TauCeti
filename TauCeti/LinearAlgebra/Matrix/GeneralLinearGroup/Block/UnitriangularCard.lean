/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Block.Triangular
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Free-entry parametrization, cardinality, and lifting of block unitriangular groups

For a finite index type `n` with a level function `lev : n → α` into a linear order `α`, a matrix
in the block upper unitriangular subgroup `TauCeti.unitriangularSubgroup lev R` of `GL n R` is
uniquely determined by its strictly upper entries `(i, j)` with `lev i < lev j`, since all entries
with `lev j ≤ lev i` agree with the identity matrix and every block unitriangular matrix has
determinant `1`.

This file builds the equivalence `TauCeti.unitriangularSubgroupEquiv` between
`unitriangularSubgroup lev R` and functions on `{p : n × n // lev p.fst < lev p.snd}`, deduces the
cardinality formula `Nat.card (unitriangularSubgroup lev R) = Nat.card R ^ Nat.card {p // ...}`,
and proves simultaneous lifting of block unitriangular matrices along any jointly surjective family
of ring homomorphisms (such as Chinese remainder reduction modulo coprime ideals).

## Main results

* `TauCeti.unitriangularSubgroupEquiv`: equivalence between `unitriangularSubgroup lev R` and
  `{p : n × n // lev p.fst < lev p.snd} → R`.
* `TauCeti.unitriangularSubgroupEquiv_symm_apply_of_lt`: entry evaluation of the inverse map on
  free entries `lev i < lev j`.
* `TauCeti.card_unitriangularSubgroup`: `Nat.card (unitriangularSubgroup lev R)` equals
  `Nat.card R ^ Nat.card {p : n × n // lev p.fst < lev p.snd}`.
* `TauCeti.exists_unitriangularSubgroup_map_eq`: simultaneous lifting of block unitriangular
  matrices along any family of ring homomorphisms `f p : R →+* F p` that is jointly surjective.

## Provenance

Adapted from `grh-lean` (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/New/Spanning/Unfolding/ReducedGroups.lean`, declarations `New.unitriangularEquiv`,
`New.unitriangularEquiv_symm_apply_of_lt`, `New.card_unitriangular`, and
`New.exists_unitriangular_map_eq`. Here the results are stated directly on Tau Ceti's
`TauCeti.unitriangularSubgroup`.
-/

public section

open Matrix

namespace TauCeti

variable {n α R : Type*} [Fintype n] [DecidableEq n] [LinearOrder α] [CommRing R] (lev : n → α)

/-- **Free-entry parametrization of the block unitriangular subgroup.** A block upper unitriangular
matrix for the level function `lev` is uniquely determined by its entries at pairs `(i, j)` with
`lev i < lev j`. -/
noncomputable def unitriangularSubgroupEquiv (R : Type*) [CommRing R] :
    unitriangularSubgroup lev R ≃ ({p : n × n // lev p.fst < lev p.snd} → R) where
  toFun u p := (u : GL n R) p.val.fst p.val.snd
  invFun a :=
    let Z : Matrix n n R :=
      of fun i j ↦ if h : lev i < lev j then a ⟨(i, j), h⟩ else (1 : Matrix n n R) i j
    have hZ : Z.BlockUnitriangular lev :=
      blockUnitriangular_of_apply_eq_one_apply_of_not_lt fun _ _ hij ↦ dite_eq_right hij
    ⟨GeneralLinearGroup.mk'' Z hZ.isUnit_det, (mem_unitriangularSubgroup lev).mpr hZ⟩
  left_inv u := by
    ext i j
    have hu : ((u : GL n R) : Matrix n n R).BlockUnitriangular lev :=
      (mem_unitriangularSubgroup lev).mp u.property
    change (if lev i < lev j then (u : GL n R) i j else (1 : Matrix n n R) i j) =
      (u : GL n R) i j
    split_ifs with h
    · rfl
    · rcases (not_lt.mp h).lt_or_eq with hlt | heq
      · rw [hu.blockTriangular hlt,
          Matrix.one_apply_ne fun hij ↦ hlt.ne (congrArg lev hij.symm)]
      · exact (hu.apply_of_eq heq.symm).symm
  right_inv a := funext fun p ↦ dite_eq_left p.property

/-- Evaluating the inverse of `TauCeti.unitriangularSubgroupEquiv` at a free entry `lev i < lev j`
recovers the prescribed entry. -/
theorem unitriangularSubgroupEquiv_symm_apply_of_lt (a : {p : n × n // lev p.fst < lev p.snd} → R)
    {i j : n} (hij : lev i < lev j) :
    ((unitriangularSubgroupEquiv lev R).symm a : GL n R) i j = a ⟨(i, j), hij⟩ :=
  dite_eq_left hij

/-- **Cardinality of the block unitriangular subgroup.** The cardinality of
`unitriangularSubgroup lev R` is `Nat.card R` raised to the number of free entries
`{p : n × n // lev p.fst < lev p.snd}`. -/
theorem card_unitriangularSubgroup (R : Type*) [CommRing R] :
    Nat.card (unitriangularSubgroup lev R) =
      Nat.card R ^ Nat.card {p : n × n // lev p.fst < lev p.snd} :=
  (Nat.card_congr (unitriangularSubgroupEquiv lev R)).trans Nat.card_fun

/-- **Simultaneous lifting of block unitriangular matrices.** If `f p : R →+* F p` is a jointly
surjective family of ring homomorphisms, then any family `s p ∈ unitriangularSubgroup lev (F p)`
lifts to a single `u ∈ unitriangularSubgroup lev R` with `GeneralLinearGroup.map (f p) u = s p`. -/
theorem exists_unitriangularSubgroup_map_eq {ι : Type*} {F : ι → Type*} [∀ p : ι, CommRing (F p)]
    (f : ∀ p : ι, R →+* F p) (hf : ∀ t : ∀ p : ι, F p, ∃ y : R, ∀ p : ι, f p y = t p)
    (s : ∀ p : ι, GL n (F p)) (hs : ∀ p : ι, s p ∈ unitriangularSubgroup lev (F p)) :
    ∃ u ∈ unitriangularSubgroup lev R, ∀ p : ι, GeneralLinearGroup.map (f p) u = s p := by
  choose lift h_lift using fun e : {p : n × n // lev p.fst < lev p.snd} ↦
    hf fun p ↦ s p e.val.fst e.val.snd
  let u : unitriangularSubgroup lev R := (unitriangularSubgroupEquiv lev R).symm lift
  have hu : ((u : GL n R) : Matrix n n R).BlockUnitriangular lev :=
    (mem_unitriangularSubgroup lev).mp u.property
  refine ⟨u, u.property, fun p ↦ GeneralLinearGroup.ext fun i j ↦ ?_⟩
  change f p ((u : GL n R) i j) = s p i j
  obtain h_free | h_fixed := lt_or_ge (lev i) (lev j)
  · rw [unitriangularSubgroupEquiv_symm_apply_of_lt lev lift h_free, h_lift]
  · have hsp : (s p : Matrix n n (F p)).BlockUnitriangular lev :=
      (mem_unitriangularSubgroup lev).mp (hs p)
    rcases h_fixed.lt_or_eq with hlt | heq
    · rw [hu.blockTriangular hlt, hsp.blockTriangular hlt, map_zero]
    · rw [hu.apply_of_eq heq.symm, hsp.apply_of_eq heq.symm]
      exact congrFun₂ (Matrix.map_one (f p) (f p).map_zero (f p).map_one) i j

end TauCeti
