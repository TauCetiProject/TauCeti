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
`TauCeti.oscillatorTorusEmbedding`, is a continuous injection of the compact angle torus onto
the invariant torus, hence a closed embedding
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

/-- At a fixed action `I`, the action–angle parametrization is `2π`-periodic in the angle. -/
theorem periodic_oscillatorActionAngle (m ν I : ℝ) :
    Function.Periodic (fun φ : ℝ ↦ oscillatorActionAngle m ν (φ, I)) (2 * π) :=
  fun φ ↦ by simp [oscillatorActionAngle_apply, Real.sin_add_two_pi, Real.cos_add_two_pi]

/-- The action–angle parametrization of the torus of actions `I`: the angle torus `(ℝ / 2πℤ)^ι`
is sent to the point `oscillatorActionAngle (m i) (ν i) (φ i, I i)` in the `i`-th phase plane.
For positive masses, frequencies and actions it is a closed embedding onto the invariant torus
`{x | ∀ i, oscillatorAction (m i) (ν i) (x i) = I i}`
(`TauCeti.isClosedEmbedding_oscillatorTorusEmbedding`, `TauCeti.range_oscillatorTorusEmbedding`).
-/
noncomputable def oscillatorTorusEmbedding (m ν I : ι → ℝ) (φ : ι → AddCircle (2 * π)) :
    ι → ℝ × ℝ :=
  fun i ↦ (periodic_oscillatorActionAngle (m i) (ν i) (I i)).lift (φ i)

/-- The `i`-th coordinate of `oscillatorTorusEmbedding` at an angle `a` whose `i`-th entry is the
class of `φ : ℝ` is the action–angle parametrization at `(φ, I i)`. This form applies to an
arbitrary angle `a`; it is not a simp lemma because `φ` does not occur on the left-hand side. -/
theorem oscillatorTorusEmbedding_apply_of_coe_eq {a : ι → AddCircle (2 * π)} {i : ι} {φ : ℝ}
    (h : (φ : AddCircle (2 * π)) = a i) :
    oscillatorTorusEmbedding m ν I a i = oscillatorActionAngle (m i) (ν i) (φ, I i) :=
  show (periodic_oscillatorActionAngle (m i) (ν i) (I i)).lift (a i) = _ from
    h ▸ (periodic_oscillatorActionAngle _ _ _).lift_coe φ

/-- On angles lifted from `ι → ℝ`, `oscillatorTorusEmbedding` is the action–angle
parametrization in each coordinate. -/
@[simp]
theorem oscillatorTorusEmbedding_coe (m ν I : ι → ℝ) (φ : ι → ℝ) :
    oscillatorTorusEmbedding m ν I (fun i ↦ (φ i : AddCircle (2 * π))) =
      fun i ↦ oscillatorActionAngle (m i) (ν i) (φ i, I i) :=
  funext fun _ ↦ oscillatorTorusEmbedding_apply_of_coe_eq rfl

/-- The action–angle parametrization of a torus of actions is continuous. -/
theorem continuous_oscillatorTorusEmbedding (m ν I : ι → ℝ) :
    Continuous (oscillatorTorusEmbedding m ν I) := by
  refine continuous_pi fun i ↦ Continuous.comp ?_ (continuous_apply i)
  refine (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (2 * π))).continuous_iff.2 ?_
  have hc : Continuous fun φ : ℝ ↦ oscillatorActionAngle (m i) (ν i) (φ, I i) := by
    simp only [oscillatorActionAngle_apply]
    fun_prop
  exact hc.congr fun φ ↦ ((periodic_oscillatorActionAngle _ _ _).lift_coe φ).symm

/-- For positive masses, frequencies and actions, distinct angles give distinct points. -/
theorem injective_oscillatorTorusEmbedding (hm : ∀ i, 0 < m i) (hν : ∀ i, 0 < ν i)
    (hI : ∀ i, 0 < I i) : Function.Injective (oscillatorTorusEmbedding m ν I) := by
  intro a b hab
  funext i
  obtain ⟨α, hα⟩ := QuotientAddGroup.mk_surjective (a i)
  obtain ⟨β, hβ⟩ := QuotientAddGroup.mk_surjective (b i)
  have hab := congrFun hab i
  rw [oscillatorTorusEmbedding_apply_of_coe_eq hα, oscillatorTorusEmbedding_apply_of_coe_eq hβ]
    at hab
  have h := ((oscillatorActionAngle_eq_oscillatorActionAngle_iff (hm i) (hν i) (hI i) (hI i)).1
    hab).2
  rw [← sub_eq_zero, ← Real.Angle.coe_sub, Real.Angle.coe_eq_zero_iff] at h
  rw [← hα, ← hβ, ← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  exact h

/-- For positive masses and frequencies and nonnegative actions `I`, the action–angle
parametrization covers exactly the level set of the actions `I`. -/
theorem range_oscillatorTorusEmbedding (hm : ∀ i, 0 < m i) (hν : ∀ i, 0 < ν i)
    (hI : ∀ i, 0 ≤ I i) :
    range (oscillatorTorusEmbedding m ν I) =
      {x | ∀ i, oscillatorAction (m i) (ν i) (x i) = I i} := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩ i
    obtain ⟨φ, hφ⟩ := QuotientAddGroup.mk_surjective (a i)
    rw [oscillatorTorusEmbedding_apply_of_coe_eq hφ]
    exact oscillatorAction_oscillatorActionAngle (hm i) (hν i) (hI i)
  · intro hx
    refine ⟨fun i ↦ ((oscillatorAngle (m i) (ν i) (x i)).toReal : AddCircle (2 * π)), ?_⟩
    rw [oscillatorTorusEmbedding_coe]
    funext i
    rw [← hx i]
    exact oscillatorActionAngle_oscillatorAction (hm i) (hν i) (Real.Angle.coe_toReal _)

/-- For positive masses, frequencies and actions, the action–angle parametrization is a closed
embedding of the compact angle torus. -/
theorem isClosedEmbedding_oscillatorTorusEmbedding (hm : ∀ i, 0 < m i) (hν : ∀ i, 0 < ν i)
    (hI : ∀ i, 0 < I i) :
    Topology.IsClosedEmbedding (oscillatorTorusEmbedding m ν I) :=
  have : Fact (0 < 2 * π) := ⟨two_pi_pos⟩
  (continuous_oscillatorTorusEmbedding m ν I).isClosedEmbedding
    (injective_oscillatorTorusEmbedding hm hν hI)

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
