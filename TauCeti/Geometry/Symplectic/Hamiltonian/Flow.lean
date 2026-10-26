/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Basic
public import TauCeti.Dynamics.Flow.Variational
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Autonomous Hamiltonian flows

A globally Lipschitz Hamiltonian vector field on a finite-dimensional symplectic vector space
has a canonical global flow. The Hamiltonian is constant along each orbit. For a `C²`
Hamiltonian, every time map preserves the symplectic form on tangent vectors: differentiating
the pairing of two variations and using symmetry of the Hessian gives zero.

The construction and variational equation reuse `TauCeti.flowOfLipschitz`.
See McDuff--Salamon, *Introduction to Symplectic Topology*, Hamiltonian flows.
-/

public section

open scoped NNReal

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (ω : SymplecticForm V) (H : V → ℝ) {K : ℝ≥0}

/-- The autonomous Hamiltonian flow, defined for all real times when its vector field is
globally Lipschitz. -/
noncomputable def hamiltonianFlow (hX : LipschitzWith K (ω.hamiltonianVectorField H)) :
    Flow ℝ V :=
  flowOfLipschitz (ω.hamiltonianVectorField H) hX

/-- The Hamiltonian flow is the canonical Lipschitz flow of its Hamiltonian vector field. -/
theorem hamiltonianFlow_eq (hX : LipschitzWith K (ω.hamiltonianVectorField H)) :
    ω.hamiltonianFlow H hX = flowOfLipschitz (ω.hamiltonianVectorField H) hX := (rfl)

/-- Hamiltonian orbits solve Hamilton's differential equation. -/
theorem hasDerivAt_hamiltonianFlow (hX : LipschitzWith K (ω.hamiltonianVectorField H))
    (x : V) (t : ℝ) :
    HasDerivAt (fun s ↦ ω.hamiltonianFlow H hX s x)
      (ω.hamiltonianVectorField H (ω.hamiltonianFlow H hX t x)) t :=
  hasDerivAt_flowOfLipschitz hX x t

/-- An autonomous differentiable Hamiltonian is conserved by its flow. -/
theorem hamiltonianFlow_conserves (hX : LipschitzWith K (ω.hamiltonianVectorField H))
    (hH : Differentiable ℝ H) (t : ℝ) (x : V) :
    H (ω.hamiltonianFlow H hX t x) = H x := by
  have hd (s : ℝ) : HasDerivAt (fun s ↦ H (ω.hamiltonianFlow H hX s x)) 0 s := by
    convert (hH _).hasFDerivAt.comp_hasDerivAt s
      (ω.hasDerivAt_hamiltonianFlow H hX x s) using 1
    · rfl
    · simp
  have hc := is_const_of_deriv_eq_zero (fun s ↦ (hd s).differentiableAt)
    (fun s ↦ (hd s).deriv) t 0
  simpa using hc

/-- The time maps of a globally Lipschitz Hamiltonian flow are `C^(n+1)` when the
Hamiltonian is `C^(n+2)`. -/
theorem contDiff_hamiltonianFlow_apply (n : ℕ)
    (hX : LipschitzWith K (ω.hamiltonianVectorField H)) (hH : ContDiff ℝ (n + 2) H)
    (t : ℝ) : ContDiff ℝ (n + 1) (ω.hamiltonianFlow H hX t) :=
  contDiff_flowOfLipschitz_apply n _ hX
    (ω.contDiff_hamiltonianVectorField
      (by simpa only [add_assoc, one_add_one_eq_two] using hH)) t

/-- Each time map of a `C²` Hamiltonian flow preserves the symplectic form on tangent
vectors. No nondegeneracy of the Hessian is required. -/
@[simp]
theorem apply_fderiv_hamiltonianFlow (hX : LipschitzWith K (ω.hamiltonianVectorField H))
    (hH : ContDiff ℝ 2 H) (t : ℝ) (x u v : V) :
    ω (fderiv ℝ (ω.hamiltonianFlow H hX t) x u)
      (fderiv ℝ (ω.hamiltonianFlow H hX t) x v) = ω u v := by
  have hXs : ContDiff ℝ 1 (ω.hamiltonianVectorField H) :=
    ω.contDiff_hamiltonianVectorField hH
  have hd (s : ℝ) : HasDerivAt
      (fun s ↦ ω (fderiv ℝ (ω.hamiltonianFlow H hX s) x u)
        (fderiv ℝ (ω.hamiltonianFlow H hX s) x v)) 0 s := by
    have hu := hasDerivAt_fderiv_flowOfLipschitz_apply hX hXs x u s
    have hv := hasDerivAt_fderiv_flowOfLipschitz_apply hX hXs x v s
    have hp := ω.toBilinForm.toContinuousBilinearMap.hasDerivAt_of_bilinear
      (fun _ ↦ hu) (fun _ ↦ hv)
    convert hp using 1
    · rfl
    · simpa only [hamiltonianFlow_eq, LinearMap.toContinuousBilinearMap_apply, add_comm] using
        (ω.apply_fderiv_hamiltonianVectorField_add hH.contDiffAt
          (fderiv ℝ (ω.hamiltonianFlow H hX s) x u)
          (fderiv ℝ (ω.hamiltonianFlow H hX s) x v)).symm
  have hc := is_const_of_deriv_eq_zero (fun s ↦ (hd s).differentiableAt)
    (fun s ↦ (hd s).deriv) t 0
  simpa using hc

end TauCeti.SymplecticForm
