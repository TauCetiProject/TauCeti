/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Basic
public import TauCeti.Topology.Order.Sublevel

/-!
# Lyapunov stability at a strict minimum of the energy

Let `H` be a Hamiltonian on a finite-dimensional symplectic vector space `(V, ω)`, continuous near
a point `x` at which it has a strict local minimum. Then `x` is a **Lyapunov stable** point of the
Hamiltonian vector field `X_H`: for every neighbourhood `U` of `x`, every integral curve of `X_H`
passing close enough to `x` stays in `U` for all times at which it is defined, in the past as well
as in the future (`TauCeti.SymplecticForm.eventually_forall_mem_of_strictLocalMin`). This is the
Lagrange–Dirichlet theorem. It needs no nondegeneracy of the minimum and no completeness of `X_H`.

The proof combines conservation of energy along integral curves
(`TauCeti.SymplecticForm.apply_eq_of_hasDerivAt_hamiltonianVectorField`) with the topological
fact that, near a strict local minimum, a connected set through `y` on which `H` stays at most
`H y` cannot leave a given neighbourhood
(`TauCeti.eventually_forall_isPreconnected_subset_of_strictLocalMin`).

When `H` is differentiable at `x`, a strict local minimum is a critical point, so `x` is an
equilibrium of `X_H`. The same argument applies to a strict local maximum, by replacing `H` with
`-H`, whose Hamiltonian vector field is `-X_H`.

## Main results

* `TauCeti.SymplecticForm.eventually_forall_mem_of_strictLocalMin`: integral curves of `X_H`
  starting near a strict local minimum of `H` stay in any given neighbourhood of it.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 25 (stability of equilibria at a minimum of the
  potential energy).
* M. W. Hirsch, S. Smale, R. L. Devaney, *Differential Equations, Dynamical Systems, and an
  Introduction to Chaos*, 3rd ed., Academic Press, 2013, Section 9.2 (Lyapunov functions).
-/

public section

namespace TauCeti.SymplecticForm

open Filter Set Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Lagrange–Dirichlet stability.** Let `H` be continuous on a neighbourhood `s` of `x` and have
a strict local minimum at `x`. For every neighbourhood `U` of `x`, if `y` is close enough to `x`,
every integral curve `γ` of the Hamiltonian vector field `X_H` on a preconnected open set of times
`T` which passes through `y`, and along which `H` is differentiable, stays in `U` for all `t ∈ T`.
-/
theorem eventually_forall_mem_of_strictLocalMin (ω : SymplecticForm V) {H : V → ℝ} {x : V}
    {s : Set V} (hs : s ∈ 𝓝 x) (hH : ContinuousOn H s) (hmin : ∀ᶠ y in 𝓝[≠] x, H x < H y)
    {U : Set V} (hU : U ∈ 𝓝 x) :
    ∀ᶠ y in 𝓝 x, ∀ (γ : ℝ → V) (T : Set ℝ), IsOpen T → IsPreconnected T →
      (∀ t ∈ T, HasDerivAt γ (ω.hamiltonianVectorField H (γ t)) t) →
      (∀ t ∈ T, DifferentiableAt ℝ H (γ t)) → ∀ t₀ ∈ T, γ t₀ = y → ∀ t ∈ T, γ t ∈ U := by
  filter_upwards [eventually_forall_isPreconnected_subset_of_strictLocalMin hs hH hmin hU]
    with y hy γ T hT hT' hγ hHγ t₀ ht₀ hγt₀ t ht
  -- The trajectory is a connected set on which the energy is constant, equal to `H y`.
  refine hy (γ '' T) (hT'.image γ fun t ht ↦ (hγ t ht).continuousAt.continuousWithinAt)
    ⟨t₀, ht₀, hγt₀⟩ ?_ (mem_image_of_mem γ ht)
  rintro _ ⟨t', ht', rfl⟩
  rw [← hγt₀, ω.apply_eq_of_hasDerivAt_hamiltonianVectorField hT hT' hγ hHγ ht₀ ht']

end TauCeti.SymplecticForm
