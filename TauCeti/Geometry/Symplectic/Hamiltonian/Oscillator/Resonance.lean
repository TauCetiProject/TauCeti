/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Oscillator.ActionAngle
import TauCeti.Analysis.Fourier.Kronecker

/-!
# Resonant and nonresonant orbits of uncoupled harmonic oscillators

Consider finitely many uncoupled harmonic oscillators, the `i`-th of mass `m i > 0` and angular
frequency `ν i > 0`, each on its own phase plane `ℝ × ℝ`, with total Hamiltonian
`H x = ∑ i, H_i (x i)` for `H_i = TauCeti.oscillatorHamiltonian (m i) (ν i)`. In the action–angle
coordinates of each oscillator (`TauCeti.oscillatorActionAngle`), the motion is the uniform
rotation `t ↦ (θ i + ν i t, I i)` (`TauCeti.hasDerivAt_oscillatorActionAngle`). The actions
`I i = E_i / ν i` are conserved, so when all of them are positive the orbit stays on the
invariant torus

`{x | ∀ i, oscillatorAction (m i) (ν i) (x i) = I i}`,

the image of the angle torus `(ℝ / 2πℤ)^ι` under the action–angle parametrization.

The orbit fills this torus densely exactly when the frequencies are nonresonant, that is when no
nonzero integer vector `k` satisfies `∑ i, k i * ν i = 0`
(`TauCeti.closure_range_oscillatorActionAngle_eq_iff`). For resonant frequencies the closure of
the orbit is not the whole invariant torus.

The action–angle parametrization restricted to the actions `I`,
`TauCeti.oscillatorTorusEmbedding`, defined with the action–angle coordinates in
`TauCeti.Geometry.Symplectic.Hamiltonian.Oscillator.ActionAngle`, is a closed embedding of the
compact angle torus onto the invariant torus
(`TauCeti.isClosedEmbedding_oscillatorTorusEmbedding`, `TauCeti.range_oscillatorTorusEmbedding`).
It carries the line `t ↦ θ + t ν` of the angle torus onto the orbit, so the statement reduces to
Kronecker's theorem `TauCeti.AddCircle.denseRange_coe_add_mul_iff`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, second edition, Graduate Texts in
  Mathematics 60, Springer, 1989, Sections 49 and 51.
-/

public section

open Set Real

namespace TauCeti

variable {ι : Type*} {m ν I : ι → ℝ}

/-- **Resonant versus nonresonant orbits of uncoupled oscillators.** For oscillators of positive
masses `m i` and frequencies `ν i`, the orbit `t ↦ (θ i + ν i t, I i)` in action–angle coordinates,
with positive actions `I i`, is dense in its invariant torus
`{x | ∀ i, oscillatorAction (m i) (ν i) (x i) = I i}` exactly when the frequencies are
nonresonant: `∑ i, k i * ν i = 0` for an integer vector `k` only when `k = 0`. -/
theorem closure_range_oscillatorActionAngle_eq_iff [Fintype ι] (hm : ∀ i, 0 < m i)
    (hν : ∀ i, 0 < ν i) (hI : ∀ i, 0 < I i) (θ : ι → ℝ) :
    closure (range fun t : ℝ ↦ fun i ↦ oscillatorActionAngle (m i) (ν i) (θ i + ν i * t, I i)) =
        {x | ∀ i, oscillatorAction (m i) (ν i) (x i) = I i} ↔
      ∀ k : ι → ℤ, ∑ i, (k i : ℝ) * ν i = 0 → k = 0 := by
  have hΦ := isClosedEmbedding_oscillatorTorusEmbedding hm hν hI
  -- The torus embedding carries the line `t ↦ θ + t ν` of the angle torus onto the orbit.
  have horbit : (range fun t : ℝ ↦ fun i ↦ oscillatorActionAngle (m i) (ν i) (θ i + ν i * t, I i)) =
      oscillatorTorusEmbedding m ν I ''
        range fun t : ℝ ↦ fun i ↦ ((θ i + ν i * t : ℝ) : AddCircle (2 * π)) := by
    rw [← range_comp]
    exact congrArg range (funext fun t ↦ (oscillatorTorusEmbedding_coe m ν I _).symm)
  rw [horbit, hΦ.closure_image_eq, ← range_oscillatorTorusEmbedding hm hν fun i ↦ (hI i).le,
    ← image_univ (f := oscillatorTorusEmbedding m ν I), (image_injective.2 hΦ.injective).eq_iff,
    ← dense_iff_closure_eq, ← DenseRange,
    AddCircle.denseRange_coe_add_mul_iff two_pi_pos.ne']

end TauCeti
