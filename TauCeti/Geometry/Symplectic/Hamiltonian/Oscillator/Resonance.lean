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

The action–angle parametrization restricted to the actions `I` is a continuous injection of the
compact angle torus, hence a closed embedding. It carries the line `t ↦ θ + t ν` of the angle
torus onto the orbit, so the statement reduces to Kronecker's theorem
`AddCircle.denseRange_coe_add_mul_iff`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, second edition, Graduate Texts in
  Mathematics 60, Springer, 1989, Sections 49 and 51.
-/

public section

open Set Real

namespace TauCeti

variable {ι : Type*} [Fintype ι] {m ν I : ι → ℝ}

/-- **Resonant versus nonresonant orbits of uncoupled oscillators.** For oscillators of positive
masses `m i` and frequencies `ν i`, the orbit `t ↦ (θ i + ν i t, I i)` in action–angle coordinates,
with positive actions `I i`, is dense in its invariant torus
`{x | ∀ i, oscillatorAction (m i) (ν i) (x i) = I i}` exactly when the frequencies are
nonresonant: `∑ i, k i * ν i = 0` for an integer vector `k` only when `k = 0`. -/
theorem closure_range_oscillatorActionAngle_eq_iff (hm : ∀ i, 0 < m i) (hν : ∀ i, 0 < ν i)
    (hI : ∀ i, 0 < I i) (θ : ι → ℝ) :
    closure (range fun t : ℝ ↦ fun i ↦ oscillatorActionAngle (m i) (ν i) (θ i + ν i * t, I i)) =
        {x | ∀ i, oscillatorAction (m i) (ν i) (x i) = I i} ↔
      ∀ k : ι → ℤ, ∑ i, (k i : ℝ) * ν i = 0 → k = 0 := by
  have : Fact (0 < 2 * π) := ⟨two_pi_pos⟩
  have hper (i : ι) :
      Function.Periodic (fun φ : ℝ ↦ oscillatorActionAngle (m i) (ν i) (φ, I i)) (2 * π) :=
    fun φ ↦ by simp [oscillatorActionAngle_apply, Real.sin_add_two_pi, Real.cos_add_two_pi]
  -- The angle torus parametrizes the invariant torus.
  let Φ : (ι → AddCircle (2 * π)) → ι → ℝ × ℝ := fun φ i ↦ (hper i).lift (φ i)
  have hΦ (φ : ι → ℝ) : Φ (fun i ↦ (φ i : AddCircle (2 * π))) =
      fun i ↦ oscillatorActionAngle (m i) (ν i) (φ i, I i) :=
    funext fun i ↦ (hper i).lift_coe _
  have hlift (a : ι → AddCircle (2 * π)) : ∃ φ : ι → ℝ, (fun i ↦ (φ i : AddCircle (2 * π))) = a :=
    ⟨fun i ↦ (QuotientAddGroup.mk_surjective (a i)).choose,
      funext fun i ↦ (QuotientAddGroup.mk_surjective (a i)).choose_spec⟩
  have hΦc : Continuous Φ := by
    refine continuous_pi fun i ↦ Continuous.comp ?_ (continuous_apply i)
    refine (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (2 * π))).continuous_iff.2 ?_
    have hc : Continuous fun φ : ℝ ↦ oscillatorActionAngle (m i) (ν i) (φ, I i) := by
      simp only [oscillatorActionAngle_apply]
      fun_prop
    exact hc.congr fun φ ↦ ((hper i).lift_coe φ).symm
  have hΦi : Function.Injective Φ := by
    intro a b hab
    obtain ⟨α, rfl⟩ := hlift a
    obtain ⟨β, rfl⟩ := hlift b
    rw [hΦ, hΦ] at hab
    funext i
    have h := ((oscillatorActionAngle_eq_oscillatorActionAngle_iff (hm i) (hν i) (hI i) (hI i)).1
      (congrFun hab i)).2
    rw [← sub_eq_zero, ← Real.Angle.coe_sub, Real.Angle.coe_eq_zero_iff] at h
    rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
    exact h
  have hrange : Φ '' univ = {x | ∀ i, oscillatorAction (m i) (ν i) (x i) = I i} := by
    ext x
    constructor
    · rintro ⟨a, -, rfl⟩ i
      obtain ⟨φ, rfl⟩ := hlift a
      rw [hΦ]
      exact oscillatorAction_oscillatorActionAngle (hm i) (hν i) (hI i).le
    · intro hx
      refine ⟨fun i ↦ ((oscillatorAngle (m i) (ν i) (x i)).toReal : AddCircle (2 * π)), trivial, ?_⟩
      rw [hΦ]
      funext i
      rw [← hx i]
      exact oscillatorActionAngle_oscillatorAction (hm i) (hν i) (Real.Angle.coe_toReal _)
  have horbit : (range fun t : ℝ ↦ fun i ↦ oscillatorActionAngle (m i) (ν i) (θ i + ν i * t, I i)) =
      Φ '' range fun t : ℝ ↦ fun i ↦ ((θ i + ν i * t : ℝ) : AddCircle (2 * π)) := by
    rw [← range_comp]
    exact congrArg range (funext fun t ↦ (hΦ _).symm)
  rw [horbit, (hΦc.isClosedEmbedding hΦi).closure_image_eq, ← hrange,
    (image_injective.2 hΦi).eq_iff, ← dense_iff_closure_eq, ← DenseRange,
    AddCircle.denseRange_coe_add_mul_iff two_pi_pos.ne']

end TauCeti
