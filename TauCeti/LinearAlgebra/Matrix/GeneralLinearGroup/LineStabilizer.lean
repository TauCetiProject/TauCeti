/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.LinearAlgebra.Projectivization.Action
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-!
# Index of the stabilizer of a coordinate line in `GL n F`

Over a finite field `F`, the subgroup of `GL n F` stabilizing a coordinate line `F · eᵢ`
(equivalently, the matrices whose `i`-th column vanishes off the diagonal) has index
`∑ j ∈ Finset.range (Fintype.card n), Nat.card F ^ j`.

## Main results

* `TauCeti.mem_stabilizer_coordLine_iff`: a matrix `g : GL n F` stabilizes the coordinate line
  `Projectivization.mk F (Pi.single i 1) _` iff `∀ j ≠ i, g j i = 0`.
* `TauCeti.index_stabilizer_coordLine`: any subgroup `H ≤ GL n F` characterized by
  `g ∈ H ↔ ∀ j ≠ i, g j i = 0` has index `∑ j ∈ Finset.range (Fintype.card n), Nat.card F ^ j`.

## Provenance

Adapted from `New.index_stabilizer_line` in `src/Lib/Weil/Unramified/HeckeGL.lean` of `grh-lean`
(https://github.com/lsernau/grh-lean, commit `72fead102f663d5c7a407964a13dc0cf9d977207`,
Apache 2.0, Copyright 2026 Anthropic, PBC), extracting `TauCeti.mem_stabilizer_coordLine_iff`
so that the stabilizer characterization holds over any field `F` without finiteness.
-/

public section

open Matrix

namespace TauCeti

variable {n F : Type*} [Fintype n] [DecidableEq n] [Field F]

/-- A matrix `g : GL n F` stabilizes the coordinate line spanned by `Pi.single i 1` in
`Projectivization F (n → F)` if and only if its `i`-th column vanishes off the diagonal. -/
theorem mem_stabilizer_coordLine_iff (i : n) (g : GL n F) :
    g ∈ MulAction.stabilizer (GL n F)
        (Projectivization.mk F (Pi.single i (1 : F) : n → F) (by simp)) ↔
      ∀ j ≠ i, g j i = 0 := by
  simp [MulAction.mem_stabilizer_iff, Projectivization.smul_mk, Projectivization.mk_eq_mk_iff',
    funext_iff, Pi.single_apply, Units.smul_def, mulVec_single, ite_eq_iff', forall_and,
    eq_comm (a := (0 : F))]

/-- Over a finite field `F`, the subgroup `H` of `GL n F` of matrices whose `i`-th column
vanishes off the diagonal (the stabilizer of the `i`-th coordinate line) has index
`∑ j ∈ Finset.range (Fintype.card n), Nat.card F ^ j`. -/
theorem index_stabilizer_coordLine [Finite F] (i : n) {H : Subgroup (GL n F)}
    (hH : ∀ g : GL n F, g ∈ H ↔ ∀ j ≠ i, g j i = 0) :
    H.index = ∑ j ∈ Finset.range (Fintype.card n), Nat.card F ^ j := by
  let p : Projectivization F (n → F) := .mk F (Pi.single i 1) (by simp)
  have h_stab : H = MulAction.stabilizer (GL n F) p :=
    Subgroup.ext fun g ↦ (hH g).trans (mem_stabilizer_coordLine_iff i g).symm
  have h_transitive : MulAction.IsPretransitive (GL n F) (Projectivization F (n → F)) :=
    .of_smul_eq SpecialLinearGroup.toGL rfl
  rw [h_stab, MulAction.index_stabilizer_of_transitive,
    Projectivization.card_of_finrank _ _ (Module.finrank_pi F)]

end TauCeti
