/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Algebra.Group.Units
public import TauCeti.Topology.Algebra.Matrix.Unique

/-!
# `GL₁` as the units

For a singleton index type `m`, passing to units in `Matrix.uniqueContinuousMulEquiv` identifies
`GL m A` with `Aˣ` as topological groups, each with its native units topology
(`Matrix.GeneralLinearGroup.uniqueContinuousMulEquiv`). For the adele ring of a number field, this
says that the topology of `GL₁(𝔸_F)` is that of the ideles.

## Main definitions

* `Matrix.GeneralLinearGroup.uniqueContinuousMulEquiv`: `GL m A ≃ₜ* Aˣ` for `[Unique m]`.
-/

public section

namespace Matrix

namespace GeneralLinearGroup

variable (m A : Type*) [Fintype m] [DecidableEq m] [Unique m] [Semiring A] [TopologicalSpace A]

/-- **`GL₁` is the group of units**: reading off the unique entry identifies `GL m A` with `Aˣ` as
topological groups, for a singleton index type `m`, each with its units topology. -/
def uniqueContinuousMulEquiv : GL m A ≃ₜ* Aˣ :=
  Units.mapContinuousMulEquiv (Matrix.uniqueContinuousMulEquiv m A)

variable {m A} in
@[simp]
theorem coe_uniqueContinuousMulEquiv_apply (g : GL m A) :
    (uniqueContinuousMulEquiv m A g : A) = (g : Matrix m m A) default default := by
  rw [uniqueContinuousMulEquiv, Units.mapContinuousMulEquiv_apply, Units.coe_map,
    MonoidHom.coe_ofClass]
  -- Mathlib has no lemma unfolding the coercion of a `ContinuousMulEquiv` to a `MulEquiv`; the
  -- coerced map is definitionally the original one, so the matrix-level lemma applies.
  exact Matrix.uniqueContinuousMulEquiv_apply _

variable {m A} in
@[simp]
theorem coe_uniqueContinuousMulEquiv_symm_apply (u : Aˣ) :
    ((uniqueContinuousMulEquiv m A).symm u : Matrix m m A) = of fun _ _ ↦ (u : A) := by
  rw [uniqueContinuousMulEquiv, Units.symm_mapContinuousMulEquiv, Units.mapContinuousMulEquiv_apply,
    Units.coe_map, MonoidHom.coe_ofClass]
  -- Mathlib has no lemma unfolding the coercion of a `ContinuousMulEquiv` to a `MulEquiv`; the
  -- coerced map is definitionally the original one, so the matrix-level lemma applies.
  exact Matrix.uniqueContinuousMulEquiv_symm_apply _

end GeneralLinearGroup

end Matrix
