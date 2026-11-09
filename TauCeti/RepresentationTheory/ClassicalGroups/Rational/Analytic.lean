/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Rational
public import TauCeti.Analysis.Matrix.Normed
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.PolynomialFunctions.Analytic
public import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import TauCeti.Geometry.Manifold.ContMDiff.FiniteDimension
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Holomorphic rational representations

Every rational representation of `GL n ℂ` has complex-analytic matrix coefficients. For a normed
complex carrier, it gives a complex-analytic homomorphism into the invertible continuous linear
operators, with their native open-submanifold structure. Rationality supplies the finite
dimensionality and completeness of the carrier.

## Main results

* `TauCeti.IsRationalRep.contMDiff_dual_apply`: matrix coefficients are complex analytic.
* `TauCeti.IsRationalRep.contMDiff_toContinuousLinearMap`: so is the operator-valued action.
* `TauCeti.IsRationalRep.contMDiff_toHomUnits`: holomorphy with values in the invertible operators.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter III, §8, Proposition (8.6), pp.154–155: algebraic matrix coefficients yield a
  holomorphic representation; Proposition (8.7) identifies the classical complexifications.
-/

public section

open Matrix Manifold
open scoped ContDiff Manifold Matrix.Norms.Operator
attribute [local instance] Matrix.linftyOpTopologicalSpace
noncomputable section

open TauCeti.Matrix.GeneralLinearGroup
namespace TauCeti.IsRationalRep

variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ (GL (Fin n) ℂ) W}

/-- Every matrix coefficient of a rational representation is complex analytic. -/
theorem contMDiff_dual_apply (h : IsRationalRep ρ) (f : Module.Dual ℂ W) (w : W) :
    ContMDiff 𝓘(ℂ, Matrix (Fin n) (Fin n) ℂ) 𝓘(ℂ) ω
      (fun g : GL (Fin n) ℂ ↦ f (ρ g w)) :=
  contMDiff_of_mem_rationalFunctions (h.dual_apply_mem_rationalFunctions f w)

section Operators
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  {σ : Representation ℂ (GL (Fin n) ℂ) V}

/-- A rational representation is complex analytic as a family of continuous linear operators.
The finite-dimensional structure needed for the conversion is supplied by rationality. -/
theorem contMDiff_toContinuousLinearMap (h : IsRationalRep σ) :
    let _ : FiniteDimensional ℂ V := h.finite
    ContMDiff 𝓘(ℂ, Matrix (Fin n) (Fin n) ℂ) 𝓘(ℂ, V →L[ℂ] V) ω
      (fun g : GL (Fin n) ℂ ↦ Module.End.toContinuousLinearMap V (σ g)) := by
  let _ : FiniteDimensional ℂ V := h.finite
  dsimp only
  let b := Module.finBasis ℂ V
  have hv (v : V) : ContMDiff 𝓘(ℂ, Matrix (Fin n) (Fin n) ℂ) 𝓘(ℂ, V) ω
      (fun g : GL (Fin n) ℂ ↦ σ g v) := by
    have hc : ContMDiff 𝓘(ℂ, Matrix (Fin n) (Fin n) ℂ)
        𝓘(ℂ, Fin (Module.finrank ℂ V) → ℂ) ω
        (fun g : GL (Fin n) ℂ ↦ b.equivFunL (σ g v)) :=
      contMDiff_pi_module_iff.mpr fun i ↦ h.contMDiff_dual_apply (b.coord i) v
    simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using
      b.equivFunL.symm.contDiff.contMDiff.comp hc
  intro g
  exact TauCeti.contMDiffAt_clm_apply.mpr fun v ↦ by
    simpa only [Module.End.toContinuousLinearMap_apply] using (hv v).contMDiffAt

/-- A rational representation gives a holomorphic homomorphism into the invertible continuous
linear operators. Its carrier's finite dimensionality and completeness follow from rationality. -/
theorem contMDiff_toHomUnits (h : IsRationalRep σ) :
    let _ : FiniteDimensional ℂ V := h.finite
    let _ : CompleteSpace V := FiniteDimensional.complete ℂ V
    ContMDiff 𝓘(ℂ, Matrix (Fin n) (Fin n) ℂ) 𝓘(ℂ, V →L[ℂ] V) ω
      (((Module.End.toContinuousLinearMap V).toMonoidHom.comp σ).toHomUnits) := by
  let _ : FiniteDimensional ℂ V := h.finite
  let _ : CompleteSpace V := FiniteDimensional.complete ℂ V
  dsimp only
  apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
  exact h.contMDiff_toContinuousLinearMap.congr fun g ↦
    MonoidHom.coe_toHomUnits ((Module.End.toContinuousLinearMap V).toMonoidHom.comp σ) g

end Operators
end TauCeti.IsRationalRep
