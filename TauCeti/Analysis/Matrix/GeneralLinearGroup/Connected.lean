/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.Topology.Algebra.Matrix.Realify
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

Its realification, the subgroup of `GL (n ⊕ n) ℝ` of invertible real matrices commuting with
`J` (`Matrix.GeneralLinearGroup.mem_range_realify_iff`), is then path connected as well, being
the image of `GL n ℂ` under the continuous realification map. So is the group of invertible
continuous linear endomorphisms `(F →L[ℂ] F)ˣ` of a finite-dimensional complex normed space `F`,
which a basis of `F` identifies with `GL n ℂ`.

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
      (convex_setOfPred_posDef.isPathConnected ⟨1, PosDef.one⟩)
  let f : {P : Matrix n n ℂ | P.PosDef} × unitaryGroup n ℂ → GL n ℂ :=
    fun PU => PU.1.property.isUnit.unit * Unitary.toUnits PU.2
  have hf : Function.Surjective f := by
    intro A
    obtain ⟨⟨P, U⟩, ⟨hP, hPU⟩, _⟩ := A.existsUnique_posDef_mul_unitary
    refine ⟨(⟨P, hP⟩, U), Units.ext ?_⟩
    simpa only [f, Units.val_mul, IsUnit.unit_spec, Unitary.val_toUnits_apply] using hPU
  apply hf.pathConnectedSpace
  apply Units.isOpenEmbedding_val.isEmbedding.isInducing.continuous_iff.mpr
  simpa only [f, Function.comp_def, Units.val_mul, IsUnit.unit_spec,
    Unitary.val_toUnits_apply] using
    continuous_subtypeVal.fst'.matrix_mul continuous_subtypeVal.snd'

/-- The realified complex general linear group, the subgroup of `GL (n ⊕ n) ℝ` of invertible real
matrices commuting with `J`, is path connected. -/
instance instPathConnectedSpaceRangeRealify :
    PathConnectedSpace (GeneralLinearGroup.realify n ℂ).range :=
  isPathConnected_iff_pathConnectedSpace.mp <| by
    rw [MonoidHom.coe_range]
    exact isPathConnected_range (GeneralLinearGroup.isClosedEmbedding_realify n ℂ).continuous

/-- The group of invertible continuous linear endomorphisms of a finite-dimensional complex
normed space is path connected, including in dimension zero: a basis identifies it with the
complex general linear group. -/
instance instPathConnectedSpaceUnitsContinuousLinearMap (F : Type*) [NormedAddCommGroup F]
    [NormedSpace ℂ F] [FiniteDimensional ℂ F] : PathConnectedSpace (F →L[ℂ] F)ˣ := by
  let b := Module.finBasis ℂ F
  -- Matrices act on `F` through the basis `b`, multiplicatively.
  let φ : Matrix (Fin (Module.finrank ℂ F)) (Fin (Module.finrank ℂ F)) ℂ →* (F →L[ℂ] F) :=
    { toFun A := LinearMap.toContinuousLinearMap (Matrix.toLin b b A)
      map_one' := ContinuousLinearMap.ext fun v ↦ by simp
      map_mul' A B := ContinuousLinearMap.ext fun v ↦ by simp [Matrix.toLin_mul b b b] }
  -- Conversely, an endomorphism of `F` has a matrix in the basis `b`.
  let ψ : (F →L[ℂ] F) →* Matrix (Fin (Module.finrank ℂ F)) (Fin (Module.finrank ℂ F)) ℂ :=
    { toFun f := LinearMap.toMatrix b b f
      map_one' := by simp
      map_mul' f g := by simp [LinearMap.toMatrix_mul] }
  have hφ : Continuous φ :=
    (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ
      (Matrix.toLin b b).toLinearMap).continuous_of_finiteDimensional
  refine Function.Surjective.pathConnectedSpace (f := Units.map φ) (fun g ↦ ⟨Units.map ψ g,
    Units.ext (ContinuousLinearMap.ext fun v ↦ ?_)⟩) (hφ.units_map φ)
  simp [φ, ψ]

end TauCeti
