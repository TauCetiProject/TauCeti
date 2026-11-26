/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import TauCeti.Topology.Algebra.Matrix.GeneralLinearGroup.Unique

/-!
# The Borel structure of `GL₁`

For a singleton index type `m`, when `GL m A` and `Aˣ` carry Borel σ-algebras, the homeomorphism
`Matrix.GeneralLinearGroup.uniqueContinuousMulEquiv` is a measurable equivalence
(`Matrix.GeneralLinearGroup.uniqueMeasurableEquiv`). For the adele ring of a number field, this
says that the Borel structure of `GL₁(𝔸_F)` is that of the ideles.

## Main definitions

* `Matrix.GeneralLinearGroup.uniqueMeasurableEquiv`: `GL m A ≃ᵐ Aˣ` for `[Unique m]`, when both
  are Borel spaces.
-/

public section

namespace Matrix

namespace GeneralLinearGroup

variable (m A : Type*) [Fintype m] [DecidableEq m] [Unique m] [Semiring A] [TopologicalSpace A]

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
