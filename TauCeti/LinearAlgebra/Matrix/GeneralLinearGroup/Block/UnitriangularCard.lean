/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Block.Triangular
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Cardinality of block unitriangular groups

For a finite index type `n` with a level function `lev : n → α` into a linear order `α`, the block
upper unitriangular subgroup `TauCeti.unitriangularSubgroup lev R` of `GL n R` is in bijection with
functions on the free entries `{p : n × n // lev p.fst < lev p.snd}`
(`TauCeti.unitriangularSubgroupEquiv`), so its cardinality is `Nat.card R` raised to the number of
free entries.

## Main results

* `TauCeti.card_unitriangularSubgroup`: `Nat.card (unitriangularSubgroup lev R)` equals
  `Nat.card R ^ Nat.card {p : n × n // lev p.fst < lev p.snd}`.

## Provenance

Adapted from `grh-lean` (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/New/Spanning/Unfolding/ReducedGroups.lean`, declaration `New.card_unitriangular`. Here the
result is stated directly on Tau Ceti's `TauCeti.unitriangularSubgroup`.
-/

public section

namespace TauCeti

variable {n α : Type*} [Fintype n] [DecidableEq n] [LinearOrder α] (lev : n → α)

/-- **Cardinality of the block unitriangular subgroup.** The cardinality of
`unitriangularSubgroup lev R` is `Nat.card R` raised to the number of free entries
`{p : n × n // lev p.fst < lev p.snd}`. -/
theorem card_unitriangularSubgroup (R : Type*) [CommRing R] :
    Nat.card (unitriangularSubgroup lev R) =
      Nat.card R ^ Nat.card {p : n × n // lev p.fst < lev p.snd} :=
  (Nat.card_congr (unitriangularSubgroupEquiv lev R)).trans Nat.card_fun

end TauCeti
