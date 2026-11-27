/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Sphere
public import TauCeti.Geometry.Symplectic.Flux.Hamiltonian.Kernel
public import TauCeti.Geometry.Symplectic.Manifold.Sphere
import TauCeti.Geometry.Sphere.Connected

/-!
# Hamiltonian diffeomorphisms of spheres

On a compact connected symplectic manifold `(M, σ)`, the endpoint flux identifies the quotient of
the group `G_σ` of final maps of symplectic isotopies by the Hamiltonian group `Ham(M, σ)` with
`H¹_dR(M) / Γ_σ` (`TauCeti.quotientHamiltonianGroupEquiv`). The unit sphere `Sⁿ` of an
`(n + 1)`-dimensional real inner product space, for `n ≥ 2`, is compact and connected and has
`H¹_dR(Sⁿ) = 0` (`TauCeti.subsingleton_deRhamCohomology_sphere_one`). So the flux of every
symplectic isotopy of a sphere vanishes and

`Ham(Sⁿ, σ) = G_σ`

for every symplectic form `σ` (`TauCeti.hamiltonianGroup_eq_isotopyStabilizer_sphere`). Among
these spheres only `S²` carries a symplectic form, and for its area form
`σ_x(v, w) = x ⬝ (v × w)` (`TauCeti.sphereAreaForm`) this says that every diffeomorphism of `S²`
joined to the identity by a smooth isotopy through area-preserving diffeomorphisms is Hamiltonian
(`TauCeti.hamiltonianGroup_sphereAreaForm`).

## Main results

* `TauCeti.hamiltonianGroup_eq_isotopyStabilizer_sphere`: for a symplectic form on a sphere of
  dimension at least two, `Ham(Sⁿ, σ) = G_σ`.
* `TauCeti.hamiltonianGroup_sphereAreaForm`: `Ham(S², σ) = G_σ` for the area form of `S²`.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  University Press, 2017, Section 10.2 (the flux homomorphism and its kernel).
* Augustin Banyaga, *Sur la structure du groupe des difféomorphismes qui préservent une forme
  symplectique*, Commentarii Mathematici Helvetici 53 (1978), 174–227, Section II.
-/

public section

noncomputable section

open Metric Module
open scoped Manifold

namespace TauCeti

open SmoothForm

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- **Symplectic isotopies of spheres are Hamiltonian.** For a symplectic form `σ` on the unit
sphere `Sⁿ` of an `(n + 1)`-dimensional real inner product space with `n ≥ 2`, the Hamiltonian
group `Ham(Sⁿ, σ)` is the whole group `G_σ` of final maps of diffeotopies preserving `σ`, because
`H¹_dR(Sⁿ) = 0`. -/
theorem hamiltonianGroup_eq_isotopyStabilizer_sphere (hn : 1 < n)
    {σ : SmoothTwoForm (𝓡 n) (sphere (0 : E) 1)} (hσ : σ.IsSymplectic) :
    hamiltonianGroup σ = isotopyStabilizer σ := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have : NeZero n := ⟨by omega⟩
  have := connectedSpace_sphere (E := E) n
  have := subsingleton_deRhamCohomology_sphere_one (E := E) hn
  exact hamiltonianGroup_eq_isotopyStabilizer hσ

/-- **Area-preserving isotopies of the two-sphere are Hamiltonian.** For the area form
`σ_x(v, w) = x ⬝ (v × w)` of the unit sphere `S² ⊂ ℝ³`, the Hamiltonian group `Ham(S², σ)` is the
whole group `G_σ` of final maps of diffeotopies preserving `σ`. -/
theorem hamiltonianGroup_sphereAreaForm :
    hamiltonianGroup sphereAreaForm = isotopyStabilizer sphereAreaForm :=
  have : Fact (finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨finrank_euclideanSpace_fin⟩
  hamiltonianGroup_eq_isotopyStabilizer_sphere one_lt_two isSymplectic_sphereAreaForm

end TauCeti
