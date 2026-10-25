/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Basic
public import TauCeti.Analysis.Calculus.ParametricFDeriv

/-!
# Variations of Hamiltonian vector fields

For a constant symplectic form, taking the Hamiltonian vector field commutes with parameter
variation: `δX_H = X_(δH)`. Joint `C²` regularity of the Hamiltonians justifies exchanging the
parameter and target derivatives. We also record joint regularity of the vector fields, with
one derivative lost. These are the coefficient calculus needed to differentiate inhomogeneous
Cauchy–Riemann equations in local coordinates.

The contraction convention is `ω(X_H, ·) = dH`. See McDuff–Salamon, *Introduction to Symplectic
Topology*, the discussion of Hamiltonian vector fields. Mixed derivatives use
`TauCeti.hasFDerivAt_spatialFDeriv`.
-/

public section

namespace TauCeti.SymplecticForm

open ContinuousLinearMap

variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- A jointly `C^(n+1)` Hamiltonian family has jointly `C^n` Hamiltonian vector fields. -/
theorem contDiffAt_hamiltonianVectorField_uncurry (ω : SymplecticForm V)
    {K : P → V → ℝ} {p : P} {x : V} {n : WithTop ℕ∞}
    (hK : ContDiffAt ℝ (n + 1) (Function.uncurry K) (p, x)) :
    ContDiffAt ℝ n (fun w : P × V ↦ ω.hamiltonianVectorField (K w.1) w.2) (p, x) := by
  have hK' : ContDiffAt ℝ (n + 1)
      (Function.uncurry fun w : P × V ↦ K w.1) ((p, x), x) :=
    hK.comp ((p, x), x) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  simpa only [hamiltonianVectorField_def, Function.comp_def] using
    ω.toBilinForm.toContinuousBilinearMap.inverse.contDiff.contDiffAt.comp (p, x)
      (hK'.fderiv contDiffAt_snd le_rfl)

/-- Differentiating a Hamiltonian vector field in a parameter direction gives the Hamiltonian
vector field of the actual parameter derivative of the Hamiltonian. -/
theorem fderiv_hamiltonianVectorField_parameter_apply (ω : SymplecticForm V)
    {K : P → V → ℝ} {p : P} {x : V}
    (hK : ContDiffAt ℝ 2 (Function.uncurry K) (p, x)) (h : P) :
    fderiv ℝ (fun q ↦ ω.hamiltonianVectorField (K q) x) p h =
      ω.hamiltonianVectorField (fun y ↦ fderiv ℝ (fun q ↦ K q y) p h) x := by
  have hA := hasFDerivAt_spatialFDeriv (𝕜 := ℝ) (F := Function.uncurry K)
    (by simpa using hK)
  have hswap : ContDiffAt ℝ 2 (Function.uncurry fun y q ↦ K q y) (x, p) :=
    hK.comp (x, p) (contDiffAt_snd.prodMk contDiffAt_fst)
  have hParameter :=
    (hswap.fderiv (m := 1) contDiffAt_const (by norm_num)).differentiableAt one_ne_zero
  have hδ := hParameter.hasFDerivAt.clm_apply (hasFDerivAt_const (x := x) h)
  have hX := ω.toBilinForm.toContinuousBilinearMap.inverse.hasFDerivAt.comp p hA
  simp only [Function.comp_def, Function.uncurry_def] at hX
  simp only [hamiltonianVectorField_def]
  rw [hX.fderiv]
  simp only [comp_apply]
  simp only [comp_zero, zero_add] at hδ
  rw [hδ.fderiv]

/-- Along a varying target point, the variation is the spatial linearization plus the
Hamiltonian vector field of the parameter variation. -/
theorem fderiv_hamiltonianVectorField_comp_apply (ω : SymplecticForm V)
    {K : P → V → ℝ} {u : P → V} {p : P}
    (hK : ContDiffAt ℝ 2 (Function.uncurry K) (p, u p))
    (hu : DifferentiableAt ℝ u p) (h : P) :
    fderiv ℝ (fun q ↦ ω.hamiltonianVectorField (K q) (u q)) p h =
      fderiv ℝ (ω.hamiltonianVectorField (K p)) (u p) (fderiv ℝ u p h) +
        ω.hamiltonianVectorField (fun y ↦ fderiv ℝ (fun q ↦ K q y) p h) (u p) := by
  have hX := (ω.contDiffAt_hamiltonianVectorField_uncurry (n := 1) hK).differentiableAt
    one_ne_zero
  have hparam := congrArg (fun L : P →L[ℝ] V ↦ L h) (fderiv_slice_left hX)
  simp only [comp_apply, inl_apply] at hparam
  rw [fderiv_comp_graph_apply (f := fun w ↦ ω.hamiltonianVectorField (K w.1) w.2) hu hX,
    ← hparam, ω.fderiv_hamiltonianVectorField_parameter_apply hK, add_comm]

end TauCeti.SymplecticForm
