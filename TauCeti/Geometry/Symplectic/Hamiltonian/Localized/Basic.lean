/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Localized Hamiltonians with prescribed vector field

A Hamiltonian depending smoothly on a finite-dimensional parameter can realize any prescribed
Hamiltonian vector at a single parameter/target point, while having compact support in any
neighborhood of that point. The Hamiltonian itself can be chosen to vanish at that point.

This supplies localized coefficient variations for inhomogeneous Cauchy–Riemann equations.
Localization is in the product of the parameter and target spaces, so distinct domain points
can be separated even when their target images coincide. This is a constant-symplectic-form
coordinate construction, not a manifold extension or a transversality theorem.

The construction multiplies the linear Hamiltonian `y ↦ ω(v, y - x)` by a smooth bump taking
value one at `(p, x)`. Since the linear Hamiltonian vanishes at `x`, differentiating the bump
does not alter its prescribed target derivative.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1,
  on localized Hamiltonian perturbations in the universal Cauchy–Riemann equation.
-/

public section

open Set Topology

namespace TauCeti.SymplecticForm

variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Any vector is the Hamiltonian vector of a smooth, compactly supported parameter-dependent
Hamiltonian localized in a prescribed neighborhood of `(p, x)`. Its value at `(p, x)` is zero.
No condition on the derivative of a map through `(p, x)` is required. -/
theorem exists_contDiff_hamiltonianVectorField_eq (ω : SymplecticForm V)
    (p : P) (x v : V) {U : Set (P × V)} (hU : U ∈ 𝓝 (p, x)) :
    ∃ K : P → V → ℝ, ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry K) ∧
      HasCompactSupport (Function.uncurry K) ∧ tsupport (Function.uncurry K) ⊆ U ∧
      K p x = 0 ∧ ω.hamiltonianVectorField (K p) x = v := by
  obtain ⟨b, hbU, hbc, hbs, -, hb⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) hU
  let L : V →L[ℝ] ℝ := ω.toBilinForm.toContinuousBilinearMap v
  let K : P → V → ℝ := fun q y ↦ b (q, y) * L (y - x)
  have hL : ContDiff ℝ (⊤ : ℕ∞) (fun w : P × V ↦ L (w.2 - x)) :=
    L.contDiff.comp (contDiff_snd.sub contDiff_const)
  refine ⟨K, hbs.mul hL, hbc.mul_right, tsupport_mul_subset_left.trans hbU, ?_, ?_⟩
  · simp [K]
  · have hbp : DifferentiableAt ℝ (fun y ↦ b (p, y)) x :=
      (hbs.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) x
    have hlin : HasFDerivAt (fun y ↦ L (y - x)) L x := by
      simpa only [Function.comp_def, ContinuousLinearMap.comp_id, id_eq] using
        L.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const x)
    have hd := hbp.hasFDerivAt.mul hlin
    rw [eq_comm, ω.eq_hamiltonianVectorField_iff]
    intro w
    simpa [K, hb, L, Pi.mul_def] using
      congrArg (fun A : V →L[ℝ] ℝ ↦ A w) hd.fderiv.symm

end TauCeti.SymplecticForm
