/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Localized.Manifold
import TauCeti.Geometry.Manifold.ContMDiff.Prod

/-!
# Localized Hamiltonians with prescribed vector field

A Hamiltonian depending smoothly on a finite-dimensional parameter can realize any prescribed
Hamiltonian vector at a single parameter/target point, while having compact support in any
neighborhood of that point. The Hamiltonian itself can be chosen to vanish at that point.

This supplies localized coefficient variations for inhomogeneous Cauchy–Riemann equations.
Localization is in the product of the parameter and target spaces, so distinct domain points
can be separated even when their target images coincide. This specializes the manifold
construction to a constant symplectic form; it is not a transversality theorem.

This is the vector-space specialization of the manifold realization theorem, applied to the
constant smooth two-form associated to `ω`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1,
  on localized Hamiltonian perturbations in the universal Cauchy–Riemann equation.
-/

public section

open Set Topology Manifold

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
  obtain ⟨K, hK, hKc, hKU, hK0, hKv⟩ :=
    SmoothTwoForm.exists_contMDiff_hamiltonianVectorField_eq (J := 𝓘(ℝ, P))
      (σ := ω.constSmooth) p x ((isNondegenerate_constSmooth ω).isInvertible_flat x) v hU
  refine ⟨K, ?_, hKc, hKU, hK0, ?_⟩
  · exact contMDiff_iff_contDiff.mp (contMDiff_prod_modelWithCornersSelf_iff.mp hK)
  · rw [hamiltonianVectorField_constSmooth] at hKv
    exact hKv

end TauCeti.SymplecticForm
