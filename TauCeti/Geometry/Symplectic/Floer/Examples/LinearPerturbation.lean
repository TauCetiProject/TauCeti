/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Energy
public import TauCeti.Geometry.Symplectic.Hamiltonian.Standard

/-!
# The curvature of the linear perturbation `q ds + p dt`

The curvature of a Hamiltonian perturbation `K = K_s ds + K_t dt` is
`R_K = ∂_s K_t - ∂_t K_s - {K_s, K_t}` (`TauCeti.SymplecticForm.hamiltonianCurvature`), and the
Poisson bracket term is what makes the energy identity
`E = ω(∂_s u, ∂_t u) + d(K(u)) - R_K(u)` hold. This file computes the simplest perturbation in
which that term is the whole curvature: linear position and momentum coordinates, constant in the
domain.

On the phase space `V × V` with its standard symplectic form `ω₀ = Σ dqᵢ ∧ dpᵢ`
(`TauCeti.stdSymplecticForm`), take `K = ⟪a, q⟫ ds + ⟪b, p⟫ dt`. Its components do not depend on
the domain point, so `∂_s K_t - ∂_t K_s = 0`, while the canonical Poisson bracket is
`{⟪a, q⟫, ⟪b, p⟫} = ⟪a, b⟫` (`TauCeti.stdSymplecticForm_poissonBracket_inner_fst_inner_snd`).
Hence

* the curvature is `R_K = -⟪a, b⟫`
  (`TauCeti.stdSymplecticForm_hamiltonianCurvature_inner_fst_inner_snd`);
* a constant map has energy density `ω₀(X_{K_s}, X_{K_t}) = ⟪a, b⟫ = -R_K`
  (`TauCeti.stdSymplecticForm_floerEnergyDensity_inner_fst_inner_snd_fun_const`), as the energy
  identity requires of a map with no area and no boundary term.

For the plane `(ℝ², dq ∧ dp)` and `K = q ds + p dt` this reads `X_q = -∂_p`, `X_p = ∂_q`,
`{q, p} = 1`, `R_K = -1`, and every constant map has energy density `1`
(`TauCeti.stdSymplecticForm_hamiltonianVectorField_fst`,
`TauCeti.stdSymplecticForm_hamiltonianVectorField_snd`,
`TauCeti.stdSymplecticForm_hamiltonianCurvature_fst_snd`,
`TauCeti.stdSymplecticForm_floerEnergyDensity_fst_snd_fun_const`). A curvature `∂_s K_t - ∂_t K_s`
without the bracket term would vanish here, and the energy identity would fail at constant maps.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 8.1 (Hamiltonian perturbations, their curvature and
  the energy identity).
-/

public section

namespace TauCeti

open scoped InnerProductSpace

section InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The perturbation `K = ⟪a, q⟫ ds + ⟪b, p⟫ dt` on `V × V` has curvature `R_K = -⟪a, b⟫`. -/
theorem stdSymplecticForm_hamiltonianCurvature_inner_fst_inner_snd (a b : V) (z : ℝ × ℝ)
    (x : V × V) :
    (stdSymplecticForm (V := V)).hamiltonianCurvature (fun _ y ↦ ⟪a, y.1⟫_ℝ)
      (fun _ y ↦ ⟪b, y.2⟫_ℝ) z x = -⟪a, b⟫_ℝ := by
  simp

/-- For the perturbation `K = ⟪a, q⟫ ds + ⟪b, p⟫ dt` on `V × V`, every constant map has Floer
energy density `⟪a, b⟫`, which is `-R_K`. -/
theorem stdSymplecticForm_floerEnergyDensity_inner_fst_inner_snd_fun_const (a b : V) (x : V × V)
    (z : ℝ × ℝ) :
    (stdSymplecticForm (V := V)).floerEnergyDensity (fun _ y ↦ ⟪a, y.1⟫_ℝ)
      (fun _ y ↦ ⟪b, y.2⟫_ℝ) (fun _ ↦ x) z = ⟪a, b⟫_ℝ := by
  simp

end InnerProductSpace

section Plane

/-- On `(ℝ², dq ∧ dp)` the position `q` has Hamiltonian vector field `X_q = -∂_p`. -/
theorem stdSymplecticForm_hamiltonianVectorField_fst (x : ℝ × ℝ) :
    (stdSymplecticForm (V := ℝ)).hamiltonianVectorField Prod.fst x = (0, -1) := by
  simpa using stdSymplecticForm_hamiltonianVectorField_inner_fst (1 : ℝ) x

/-- On `(ℝ², dq ∧ dp)` the momentum `p` has Hamiltonian vector field `X_p = ∂_q`. -/
theorem stdSymplecticForm_hamiltonianVectorField_snd (x : ℝ × ℝ) :
    (stdSymplecticForm (V := ℝ)).hamiltonianVectorField Prod.snd x = (1, 0) := by
  simpa using stdSymplecticForm_hamiltonianVectorField_inner_snd (1 : ℝ) x

/-- On `(ℝ², dq ∧ dp)` the perturbation `K = q ds + p dt` has curvature `R_K = -1`. -/
theorem stdSymplecticForm_hamiltonianCurvature_fst_snd (z : ℝ × ℝ) (x : ℝ × ℝ) :
    (stdSymplecticForm (V := ℝ)).hamiltonianCurvature (fun _ ↦ Prod.fst) (fun _ ↦ Prod.snd) z x =
      -1 := by
  simpa using stdSymplecticForm_hamiltonianCurvature_inner_fst_inner_snd (1 : ℝ) 1 z x

/-- On `(ℝ², dq ∧ dp)`, for the perturbation `K = q ds + p dt`, every constant map has Floer energy
density `ω(X_q, X_p) = 1 = -R_K`. -/
theorem stdSymplecticForm_floerEnergyDensity_fst_snd_fun_const (x : ℝ × ℝ) (z : ℝ × ℝ) :
    (stdSymplecticForm (V := ℝ)).floerEnergyDensity (fun _ ↦ Prod.fst) (fun _ ↦ Prod.snd)
      (fun _ ↦ x) z = 1 := by
  simpa using stdSymplecticForm_floerEnergyDensity_inner_fst_inner_snd_fun_const (1 : ℝ) 1 x z

end Plane

end TauCeti
