/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Algebra.Group.Units
public import TauCeti.Topology.Algebra.Matrix.Unique

/-!
# `GL₁` as the units

For a singleton index type `m`, passing to units in `Matrix.uniqueContinuousMulEquiv` identifies
`GL m A` with `Aˣ` as topological groups, each with its native units topology
(`Matrix.GeneralLinearGroup.uniqueContinuousMulEquiv`). When both carry Borel σ-algebras, the
same map is a measurable equivalence (`Matrix.GeneralLinearGroup.uniqueMeasurableEquiv`). For the
adele ring of a number field, this says that the topology and the Borel structure of
`GL₁(𝔸_F)` are those of the ideles.

## Main definitions

* `Matrix.GeneralLinearGroup.uniqueContinuousMulEquiv`: `GL m A ≃ₜ* Aˣ` for `[Unique m]`.
* `Matrix.GeneralLinearGroup.uniqueMeasurableEquiv`: the same map as a measurable equivalence of
  Borel spaces.
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
    (uniqueContinuousMulEquiv m A g : A) = (g : Matrix m m A) default default :=
  Matrix.uniqueContinuousMulEquiv_apply _

variable {m A} in
@[simp]
theorem coe_uniqueContinuousMulEquiv_symm_apply (u : Aˣ) :
    ((uniqueContinuousMulEquiv m A).symm u : Matrix m m A) = of fun _ _ ↦ (u : A) :=
  Matrix.uniqueContinuousMulEquiv_symm_apply _

/-- **`GL₁` and the units have the same Borel structure**: when `GL m A` and `Aˣ` are Borel
spaces, `Matrix.GeneralLinearGroup.uniqueContinuousMulEquiv` is a measurable equivalence. -/
def uniqueMeasurableEquiv [MeasurableSpace (GL m A)] [BorelSpace (GL m A)] [MeasurableSpace Aˣ]
    [BorelSpace Aˣ] : GL m A ≃ᵐ Aˣ :=
  (uniqueContinuousMulEquiv m A).toHomeomorph.toMeasurableEquiv

variable {m A} in
@[simp]
theorem uniqueMeasurableEquiv_apply [MeasurableSpace (GL m A)] [BorelSpace (GL m A)]
    [MeasurableSpace Aˣ] [BorelSpace Aˣ] (g : GL m A) :
    uniqueMeasurableEquiv m A g = uniqueContinuousMulEquiv m A g :=
  (rfl)

variable {m A} in
@[simp]
theorem uniqueMeasurableEquiv_symm_apply [MeasurableSpace (GL m A)] [BorelSpace (GL m A)]
    [MeasurableSpace Aˣ] [BorelSpace Aˣ] (u : Aˣ) :
    (uniqueMeasurableEquiv m A).symm u = (uniqueContinuousMulEquiv m A).symm u :=
  (rfl)

end GeneralLinearGroup

end Matrix
