/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.ConleyZehnder.Parity
public import TauCeti.Geometry.Symplectic.Hamiltonian.TimeDependent

import TauCeti.Geometry.Symplectic.Hamiltonian.Variation
import TauCeti.LinearAlgebra.Eigenspace.Matrix

/-!
# The Conley–Zehnder index of a Hamiltonian orbit in a symplectic vector space

Let `(V, ω)` be a finite-dimensional symplectic vector space, `H : ℝ → V → ℝ` a jointly `C²`
time-dependent Hamiltonian and `x` a continuous path in `V`. The propagator
`Ψ(t) = TauCeti.dysonSeriesLeft S t` of the linearized Hamiltonian equation `ζ' = S_t ζ`,
`S_t = dX_{H_t}(x(t))`, preserves `ω`
(`TauCeti.SymplecticForm.apply_dysonSeriesLeft_fderiv_hamiltonianVectorField`), and along an orbit
it is the derivative of the Hamiltonian evolution, `Ψ(t) = dφ_{0,t}(x(0))`
(`TauCeti.SymplecticForm.fderiv_timeDependentHamiltonianFlow_eq_dysonSeriesLeft`). On `[0, 1]` it
is therefore a path of linear symplectic maps from the identity
(`TauCeti.SymplecticForm.linearizedFlowPath`), and its Conley–Zehnder index
(`TauCeti.SymplecticForm.conleyZehnderIndex`) is the **Conley–Zehnder index of the orbit**
`TauCeti.SymplecticForm.orbitConleyZehnderIndex`. Its sign convention is that of the matrix
index `TauCeti.GLSymplectic.conleyZehnderIndex`, read in bases in which `ω` has the matrix `J`. On
a vector space no trivialization has to be chosen along a cap: the identity of `V` frames the
tangent spaces along the whole orbit.

The index is the Conley–Zehnder index of the matrices of `Ψ` in any symplectic basis
(`TauCeti.SymplecticForm.conleyZehnderIndex_eq`); no basis is part of the definition. When
`x` is a one-periodic orbit of a one-periodic Hamiltonian and `x(0)` is a nondegenerate fixed point
of the time-one map, the return map `Ψ(1)` has no eigenvector for the eigenvalue `1`
(`TauCeti.SymplecticForm.eigenspace_linearizedFlowPath_one_eq_bot`), and so its matrix in any
basis has no eigenvalue `1`
(`TauCeti.SymplecticForm.finrank_eigenspace_toLin'_toMatrix_linearizedFlowPath_one_eq_zero`). This
is the endpoint condition that makes the orbit nondegenerate, and under it the index of the orbit
is an integer `k` with `(-1) ^ (n - k) = sign det (1 - Ψ(1))`, `2n = dim V`
(`TauCeti.SymplecticForm.exists_int_orbitConleyZehnderIndex_eq`).

## Main definitions

* `TauCeti.SymplecticForm.linearizedFlowPath`: the propagator of the linearized Hamiltonian
  equation along `x` on `[0, 1]`, a path of linear symplectic maps from the identity.
* `TauCeti.SymplecticForm.orbitConleyZehnderIndex`: its Conley–Zehnder index.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. **7**, AMS, 1999, Lectures 1 and 2 (the Conley–Zehnder index of a nondegenerate
  periodic orbit).
* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827–844.
-/

public section

noncomputable section

open Function Matrix Module
open scoped unitInterval NNReal Manifold

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (ω : SymplecticForm V) {H : ℝ → V → ℝ} {x : ℝ → V}

/-- **The linearized Hamiltonian flow along a path.** For a jointly `C²` Hamiltonian `H` and a
continuous path `x`, the propagator `t ↦ Ψ(t)` of the linearized Hamiltonian equation
`ζ' = dX_{H_t}(x(t)) ζ` on `[0, 1]`, a path of linear maps from the identity to the return map
`Ψ(1)`. Along an orbit of `H` it is `t ↦ dφ_{0,t}(x(0))`. -/
def linearizedFlowPath (hH : ContDiff ℝ 2 (uncurry H)) (hx : Continuous x) :
    Path (1 : V →L[ℝ] V)
      (dysonSeriesLeft (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) 1) where
  toFun t := dysonSeriesLeft (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) t
  continuous_toFun :=
    (continuous_dysonSeriesLeft (ω.continuous_fderiv_hamiltonianVectorField_comp hH hx)).comp
      continuous_subtypeVal
  source' := by simp [dysonSeriesLeft_zero]
  target' := by simp

@[simp]
theorem linearizedFlowPath_apply (hH : ContDiff ℝ 2 (uncurry H)) (hx : Continuous x) (t : I) :
    ω.linearizedFlowPath hH hx t =
      dysonSeriesLeft (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) t :=
  (rfl)

/-- **The linearized Hamiltonian flow is symplectic.** Every map of the path
`TauCeti.SymplecticForm.linearizedFlowPath` preserves `ω`. -/
theorem apply_linearizedFlowPath_apply (hH : ContDiff ℝ 2 (uncurry H)) (hx : Continuous x)
    (t : I) (u v : V) :
    ω (ω.linearizedFlowPath hH hx t u) (ω.linearizedFlowPath hH hx t v) = ω u v := by
  simpa only [linearizedFlowPath_apply, zero_add] using
    ω.apply_dysonSeriesLeft_fderiv_hamiltonianVectorField hH hx 0 t u v

/-- **The Conley–Zehnder index of a Hamiltonian orbit.** For a jointly `C²` Hamiltonian `H` on a
finite-dimensional symplectic vector space and a continuous path `x`, the Conley–Zehnder index of
the linearized Hamiltonian flow `t ↦ Ψ(t)` along `x` on `[0, 1]`, read in symplectic bases. -/
def orbitConleyZehnderIndex (hH : ContDiff ℝ 2 (uncurry H)) (hx : Continuous x) : ℝ :=
  ω.conleyZehnderIndex (ω.linearizedFlowPath hH hx) (ω.apply_linearizedFlowPath_apply hH hx)

/-- The Conley–Zehnder index of a Hamiltonian orbit is that of its linearized flow; in a
symplectic basis it is computed by `TauCeti.SymplecticForm.conleyZehnderIndex_eq`. -/
theorem orbitConleyZehnderIndex_def (hH : ContDiff ℝ 2 (uncurry H)) (hx : Continuous x) :
    ω.orbitConleyZehnderIndex hH hx =
      ω.conleyZehnderIndex (ω.linearizedFlowPath hH hx) (ω.apply_linearizedFlowPath_apply hH hx) :=
  (rfl)

/-- **The return map of a nondegenerate orbit has no eigenvalue `1`.** For a one-periodic orbit
`x` of a jointly `C²` time-dependent Hamiltonian whose suspended vector field is globally
Lipschitz, if `x(0)` is a nondegenerate fixed point of the time-one map, then the endpoint `Ψ(1)` of
the linearized flow fixes no nonzero vector. -/
theorem eigenspace_linearizedFlowPath_one_eq_bot (hH : ContDiff ℝ 2 (uncurry H)) {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0)) :
    End.eigenspace (ω.linearizedFlowPath hH
      (continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt) 1 : V →ₗ[ℝ] V) 1 = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun v hv ↦ ω.eq_zero_of_dysonSeriesLeft_apply_eq_self hX hH hx
    hnd ?_
  rw [End.mem_eigenspace_iff, one_smul] at hv
  simpa using hv

/-- **The return matrix of a nondegenerate orbit has no eigenvalue `1`.** In every basis, the
matrix of the endpoint `Ψ(1)` of the linearized flow along a nondegenerate one-periodic orbit has
no eigenvector for the eigenvalue `1`: the return map of the orbit is nondegenerate. -/
theorem finrank_eigenspace_toLin'_toMatrix_linearizedFlowPath_one_eq_zero
    (hH : ContDiff ℝ 2 (uncurry H)) {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ V) :
    finrank ℝ (End.eigenspace (toLin' (LinearMap.toMatrix b b (ω.linearizedFlowPath hH
      (continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt) 1 : V →ₗ[ℝ] V))) 1) = 0 := by
  rw [LinearMap.finrank_eigenspace_toLin'_toMatrix,
    ω.eigenspace_linearizedFlowPath_one_eq_bot hH hX hx hnd, finrank_bot]

/-- **The Conley–Zehnder index of a nondegenerate orbit is an integer.** For a one-periodic orbit
`x` of a jointly `C²` time-dependent Hamiltonian on a symplectic vector space of dimension `2n`,
whose suspended vector field is globally Lipschitz, if `x(0)` is a nondegenerate fixed point of the
time-one map, then the Conley–Zehnder index of `x` is an integer `k` whose parity is that of the
return map `Ψ(1)`: `(-1) ^ (n - k) = sign det (1 - Ψ(1))`. -/
theorem exists_int_orbitConleyZehnderIndex_eq (hH : ContDiff ℝ 2 (uncurry H)) {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0)) :
    ∃ k : ℤ, ω.orbitConleyZehnderIndex hH
        (continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt) = k ∧
      ((((finrank ℝ V / 2 : ℕ) : ℤ) - k).negOnePow : ℤ) =
        SignType.sign (LinearMap.det (1 - (ω.linearizedFlowPath hH
          (continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt) 1 : V →ₗ[ℝ] V))) := by
  have hB := ω.eigenspace_linearizedFlowPath_one_eq_bot hH hX hx hnd
  rw [Path.target] at hB ⊢
  exact ω.exists_int_conleyZehnderIndex_eq_of_one _ _ hB

end TauCeti.SymplecticForm
