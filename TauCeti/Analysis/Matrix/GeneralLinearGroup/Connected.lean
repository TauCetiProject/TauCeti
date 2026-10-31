/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Normed.Ring.Units
import TauCeti.Analysis.Matrix.Polar
import TauCeti.Analysis.Matrix.PosDef
import TauCeti.Analysis.Matrix.UnitaryGroup.Connected

/-!
# Path connectedness of the complex general linear group

The complex general linear group is path connected, including in dimension zero.
The polar decomposition expresses every invertible matrix as the product of a
positive-definite matrix and a unitary matrix. The positive-definite cone is convex,
so both factors lie in path connected spaces, and multiplication is a continuous
surjection onto the general linear group.

## References

* Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition,
  Springer GTM 222, 2015, Section 2.5 (polar decomposition).
-/

public section

noncomputable section

open scoped ComplexOrder Matrix.Norms.L2Operator

open Matrix

namespace TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The complex general linear group is path connected, including in dimension zero. -/
instance instPathConnectedSpaceMatrixGeneralLinearGroup : PathConnectedSpace (GL n ℂ) := by
  let : PathConnectedSpace {P : Matrix n n ℂ | P.PosDef} :=
    isPathConnected_iff_pathConnectedSpace.mp
      (convex_setOf_posDef.isPathConnected ⟨1, PosDef.one⟩)
  let f : {P : Matrix n n ℂ | P.PosDef} × unitaryGroup n ℂ → GL n ℂ :=
    fun PU => PU.1.2.isUnit.unit * Unitary.toUnits PU.2
  have hf : Function.Surjective f := by
    intro A
    obtain ⟨⟨P, U⟩, ⟨hP, hPU⟩, _⟩ := A.existsUnique_posDef_mul_unitary
    refine ⟨(⟨P, hP⟩, U), Units.ext ?_⟩
    simpa only [f, Units.val_mul, IsUnit.unit_spec, Unitary.val_toUnits_apply] using hPU
  apply hf.pathConnectedSpace
  apply Units.isOpenEmbedding_val.isEmbedding.isInducing.continuous_iff.mpr
  simpa only [f, Function.comp_def, Units.val_mul, IsUnit.unit_spec,
    Unitary.val_toUnits_apply] using
    continuous_subtype_val.fst'.matrix_mul continuous_subtype_val.snd'

end TauCeti
