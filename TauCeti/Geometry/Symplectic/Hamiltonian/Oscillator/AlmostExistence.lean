/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.AlmostExistence
public import TauCeti.Geometry.Symplectic.Hamiltonian.Oscillator.Basic
public import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Contractible

/-!
# Almost existence for the harmonic oscillator

On the standard symplectic plane, the energy `H(q, p) = (q² + p²) / 2` of the unit harmonic
oscillator has the circles of radius `√(2c)` as its positive levels. Each of them is a closed
characteristic: the oscillator evolution `t ↦ φ_t(√(2c), 0)` runs around it with period `2π`,
and its loop is contractible in any convex set containing the circle
(`TauCeti.hasContractibleClosedCharacteristic_oscillator`). So every positive level has the
contractible almost existence property in every convex set containing the nearby levels, indeed
with a closed characteristic on every nearby level
(`TauCeti.hasContractibleAlmostExistence_oscillator`). This is the basic example of the property,
the boundary of a ball in the plane.

## Main results

* `TauCeti.hasContractibleClosedCharacteristic_oscillator`: every positive level of the
  oscillator carries a closed characteristic contractible in a convex set containing it.
* `TauCeti.hasContractibleAlmostExistence_oscillator`: every positive level of the oscillator has
  the contractible almost existence property in a convex set containing the levels near it.

## References

* H. Hofer, E. Zehnder, *Symplectic Invariants and Hamiltonian Dynamics*, Birkhäuser, 1994,
  Section 1.1 (the harmonic oscillator and closed characteristics of spheres).
-/

public section

open Function Set
open scoped Manifold

namespace TauCeti

variable {W : Set (ℝ × ℝ)} {c : ℝ}

/-- **Closed characteristics of the harmonic oscillator.** For `c > 0`, the level `c` of the
oscillator energy `(q² + p²) / 2` on the standard symplectic plane carries a closed
characteristic contractible in every convex set `W` containing the level, traced by the oscillator
evolution with period `2π`. -/
theorem hasContractibleClosedCharacteristic_oscillator (hW : Convex ℝ W) (hc : 0 < c)
    (hcW : {x : ℝ × ℝ | (x.1 ^ 2 + x.2 ^ 2) / 2 = c} ⊆ W) :
    (stdSymplecticForm (V := ℝ)).constSmooth.HasContractibleClosedCharacteristic W
      (fun x ↦ (x.1 ^ 2 + x.2 ^ 2) / 2) c := by
  set r := √(2 * c)
  have hr : 0 < r := Real.sqrt_pos.2 (by positivity)
  set γ : ℝ → ℝ × ℝ := fun t ↦ oscillatorEvolution t (r, 0)
  have hlev (t : ℝ) : ((γ t).1 ^ 2 + (γ t).2 ^ 2) / 2 = c := by
    have hr2 : r ^ 2 = 2 * c := Real.sq_sqrt (by positivity)
    simp only [γ, oscillatorEvolution_apply, mul_zero, add_zero]
    linear_combination (r ^ 2 / 2) * Real.cos_sq_add_sin_sq t + hr2 / 2
  have hper : Periodic γ (2 * Real.pi) := fun t ↦ by
    simp only [γ, oscillatorEvolution_apply, Real.cos_add_two_pi, Real.sin_add_two_pi]
  have hcont : Continuous γ :=
    (contDiff_oscillatorEvolution (n := 0)).continuous.comp (continuous_id.prodMk continuous_const)
  -- The loop of `γ` in `W`, through `ℝ / 2πℤ`.
  set δ : ℝ → W := fun t ↦ ⟨γ t, hcW (hlev t)⟩
  have hδ : Periodic δ (2 * Real.pi) := fun t ↦ Subtype.ext (hper t)
  have hne : W.Nonempty := ⟨γ 0, hcW (hlev 0)⟩
  have := hW.contractibleSpace hne
  rw [SmoothTwoForm.hasContractibleClosedCharacteristic_iff]
  refine ⟨2 * Real.pi, γ, by positivity, fun t ↦ ?_, hper, ⟨Real.pi, ?_⟩, hlev,
    ⟨hδ.lift, continuous_coinduced_dom.2 (hcont.subtype_mk _)⟩, ?_, fun t ↦ by simp [δ]⟩
  · rw [SymplecticForm.hamiltonianVectorField_constSmooth,
      stdSymplecticForm_hamiltonianVectorField_oscillator]
    exact hasMFDerivAt_iff_hasFDerivAt.2 (hasDerivAt_oscillatorEvolution t (r, 0)).hasFDerivAt
  · simp only [γ, oscillatorEvolution_apply, Real.cos_pi, Real.sin_pi, Real.cos_zero,
      Real.sin_zero]
    intro h
    have := congrArg Prod.fst h
    simp only at this
    linarith
  · simpa using (id_nullhomotopic W).comp_left
      ⟨hδ.lift, continuous_coinduced_dom.2 (hcont.subtype_mk _)⟩

/-- **Almost existence for the harmonic oscillator.** For `c > 0`, the level `c` of the
oscillator energy `(q² + p²) / 2` on the standard symplectic plane has the contractible almost
existence property in every convex set `W` containing the levels below `2c`: every level in
`(0, 2c)` carries a closed characteristic contractible in `W`. -/
theorem hasContractibleAlmostExistence_oscillator (hW : Convex ℝ W) (hc : 0 < c)
    (hcW : {x : ℝ × ℝ | (x.1 ^ 2 + x.2 ^ 2) / 2 < 2 * c} ⊆ W) :
    (stdSymplecticForm (V := ℝ)).constSmooth.HasContractibleAlmostExistence W
      (fun x ↦ (x.1 ^ 2 + x.2 ^ 2) / 2) c := by
  rw [SmoothTwoForm.hasContractibleAlmostExistence_iff]
  refine ⟨c, hc, Filter.Eventually.of_forall fun c' hc' _ ↦ ?_⟩
  rw [sub_self, mem_Ioo] at hc'
  refine hasContractibleClosedCharacteristic_oscillator hW hc'.1 fun x hx ↦ hcW ?_
  rw [mem_ofPred_eq] at hx ⊢
  linarith [hc'.2]

end TauCeti
