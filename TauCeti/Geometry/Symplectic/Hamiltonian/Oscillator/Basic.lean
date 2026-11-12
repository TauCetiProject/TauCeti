/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Standard
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# The harmonic oscillator flow

`TauCeti.oscillatorEvolution` is the evolution of the Hamiltonian `(q² + p²) / 2` on the
standard symplectic plane. It is smooth jointly in time and initial point, satisfies the flow
law, is inverted by reversing time, and preserves the standard symplectic form. Its velocity
is `(p, -q)`, the Hamiltonian vector field of the oscillator energy.

More generally, `TauCeti.oscillatorHamiltonian m ν` is the energy `p² / (2m) + m ν² q² / 2` of a
harmonic oscillator of mass `m` and angular frequency `ν`, and
`TauCeti.stdSymplecticForm_hamiltonianVectorField_oscillatorHamiltonian` states its Hamilton's
equations `q' = p / m`, `p' = -m ν² q`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, second edition, §§15 and 40.
-/

public section

noncomputable section

namespace TauCeti

open ContinuousLinearMap

/-- The time-`t` evolution of the unit harmonic oscillator. -/
def oscillatorEvolution (t : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ × ℝ :=
  (Real.cos t • fst ℝ ℝ ℝ + Real.sin t • snd ℝ ℝ ℝ).prod
    (-Real.sin t • fst ℝ ℝ ℝ + Real.cos t • snd ℝ ℝ ℝ)

theorem oscillatorEvolution_apply (t : ℝ) (x : ℝ × ℝ) :
    oscillatorEvolution t x =
      (Real.cos t * x.1 + Real.sin t * x.2, -Real.sin t * x.1 + Real.cos t * x.2) :=
  (rfl)

@[simp]
theorem oscillatorEvolution_zero (x : ℝ × ℝ) : oscillatorEvolution 0 x = x := by
  simp [oscillatorEvolution_apply]

/-- Evolution for successive times is evolution for their sum. -/
theorem oscillatorEvolution_add (s t : ℝ) (x : ℝ × ℝ) :
    oscillatorEvolution (s + t) x = oscillatorEvolution s (oscillatorEvolution t x) := by
  ext <;> simp [oscillatorEvolution_apply, Real.cos_add, Real.sin_add] <;> ring

/-- Reversing time inverts oscillator evolution. -/
@[simp]
theorem oscillatorEvolution_neg_apply (t : ℝ) (x : ℝ × ℝ) :
    oscillatorEvolution (-t) (oscillatorEvolution t x) = x := by
  rw [← oscillatorEvolution_add, neg_add_cancel, oscillatorEvolution_zero]

/-- Joint smoothness includes the times where a first-kind generating function breaks down. -/
theorem contDiff_oscillatorEvolution {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun x : ℝ × (ℝ × ℝ) ↦ oscillatorEvolution x.1 x.2) := by
  exact (((Real.contDiff_cos.comp contDiff_fst).mul contDiff_snd.fst).add
    ((Real.contDiff_sin.comp contDiff_fst).mul contDiff_snd.snd)).prodMk
      ((((Real.contDiff_sin.comp contDiff_fst).neg).mul contDiff_snd.fst).add
        ((Real.contDiff_cos.comp contDiff_fst).mul contDiff_snd.snd))

/-- The evolution solves `q' = p`, `p' = -q` at every time. -/
theorem hasDerivAt_oscillatorEvolution (t : ℝ) (x : ℝ × ℝ) :
    HasDerivAt (fun s ↦ oscillatorEvolution s x)
      ((oscillatorEvolution t x).2, -(oscillatorEvolution t x).1) t := by
  simpa only [oscillatorEvolution_apply, Pi.add_apply, Pi.neg_apply, neg_mul,
    neg_add_rev, add_comm] using
    HasDerivAt.prodMk (((Real.hasDerivAt_cos t).mul_const x.1).add
      ((Real.hasDerivAt_sin t).mul_const x.2))
      ((((Real.hasDerivAt_sin t).neg).mul_const x.1).add
        ((Real.hasDerivAt_cos t).mul_const x.2))

/-- Hamilton's vector field of the oscillator energy is `(p, -q)`. -/
theorem stdSymplecticForm_hamiltonianVectorField_oscillator (x : ℝ × ℝ) :
    (stdSymplecticForm (V := ℝ)).hamiltonianVectorField
      (fun y ↦ (y.1 ^ 2 + y.2 ^ 2) / 2) x = (x.2, -x.1) := by
  have h := (((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 2).add
    ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 2)).mul_const (2 : ℝ)⁻¹
  have hH : HasFDerivAt (fun y : ℝ × ℝ ↦ (y.1 ^ 2 + y.2 ^ 2) / 2)
      ((innerSL ℝ x.1).coprod (innerSL ℝ x.2)) x := by
    have he : (innerSL ℝ x.1).coprod (innerSL ℝ x.2) =
        (2 : ℝ)⁻¹ • ((2 • x.1 ^ (2 - 1)) • fst ℝ ℝ ℝ +
          (2 • x.2 ^ (2 - 1)) • snd ℝ ℝ ℝ) := by
      apply ContinuousLinearMap.ext
      intro u
      simp [innerSL_apply_apply, RCLike.inner_apply]
      ring
    rw [he]
    simpa only [div_eq_mul_inv, Pi.add_apply] using h
  exact stdSymplecticForm_hamiltonianVectorField hH

/-- Oscillator evolution preserves the standard symplectic form for every time. -/
theorem stdSymplecticForm_oscillatorEvolution (t : ℝ) (u v : ℝ × ℝ) :
    stdSymplecticForm (oscillatorEvolution t u) (oscillatorEvolution t v) =
      stdSymplecticForm u v := by
  simp only [stdSymplecticForm_apply, oscillatorEvolution_apply, RCLike.inner_apply,
    RCLike.conj_to_real]
  linear_combination (u.1 * v.2 - u.2 * v.1) * Real.sin_sq_add_cos_sq t

/-! ### Mass and frequency: the Hamiltonian and Hamilton's equations -/

/-- The energy `H(q, p) = p² / (2m) + m ν² q² / 2` of a harmonic oscillator of mass `m` and angular
frequency `ν`, on the phase space `ℝ × ℝ` of positions and momenta. -/
def oscillatorHamiltonian (m ν : ℝ) (x : ℝ × ℝ) : ℝ :=
  x.2 ^ 2 / (2 * m) + m * ν ^ 2 * x.1 ^ 2 / 2

theorem oscillatorHamiltonian_apply (m ν : ℝ) (x : ℝ × ℝ) :
    oscillatorHamiltonian m ν x = x.2 ^ 2 / (2 * m) + m * ν ^ 2 * x.1 ^ 2 / 2 :=
  (rfl)

/-- **Hamilton's equations** of the harmonic oscillator: `q' = p / m`, `p' = -m ν² q`. -/
theorem stdSymplecticForm_hamiltonianVectorField_oscillatorHamiltonian (m ν : ℝ) (x : ℝ × ℝ) :
    (stdSymplecticForm (V := ℝ)).hamiltonianVectorField (oscillatorHamiltonian m ν) x =
      (x.2 / m, -(m * ν ^ 2 * x.1)) := by
  have hH : oscillatorHamiltonian m ν =
      fun y ↦ y.2 ^ 2 * (2 * m)⁻¹ + m * ν ^ 2 * y.1 ^ 2 * 2⁻¹ := by
    ext y
    simp [oscillatorHamiltonian_apply, div_eq_mul_inv]
  have h := (((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 2).mul_const (2 * m)⁻¹).add
    ((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 2).const_mul (m * ν ^ 2)).mul_const 2⁻¹)
  rw [hH]
  refine stdSymplecticForm_hamiltonianVectorField (h.congr_fderiv ?_)
  ext <;> simp [RCLike.inner_apply] <;> ring

end TauCeti
