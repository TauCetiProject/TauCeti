/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import TauCeti.Dynamics.Ergodic.MeasurePreserving

/-!
# Rational rotation number and an invariant measure of full support

Let `f` be a continuous strictly increasing lift of a circle homeomorphism (a
`CircleDeg1Lift`) with translation number `p / q`, `q ≥ 1`. Then `f^q(x) = x + p` for some `x`
(Mathlib's `CircleDeg1Lift.translationNumber_eq_rat_iff`). If moreover `f` preserves a measure
of full support on the circle, then `f^q(x) = x + p` for every `x`: every orbit is periodic of
type `(p, q)` (`CircleDeg1Lift.iterate_eq_add_of_measurePreserving`). The measure is given on
the line as a locally finite measure with full support, invariant under `f` and under the
integer translations, as the lift of a measure on the circle is.

The proof: the map `h = f^q − p` is strictly increasing, preserves the measure, and has a fixed
point, hence fixed points below and above every `x`. Such a map fixes every point between two of
its fixed points (`MeasureTheory.MeasurePreserving.map_eq_self_of_strictMono`): if `x < h(x)`
below a fixed point `y`, the intervals `[hⁿ(x), hⁿ⁺¹(x))` are pairwise disjoint subsets of
`[x, y]` of equal positive measure, which contradicts the finiteness of the measure of `[x, y]`.

## References

* M. Bialy, A. E. Mironov, *The Birkhoff–Poritsky conjecture for centrally-symmetric billiard
  tables*, Ann. of Math. (2022), Section 1.3.
-/

public section

open MeasureTheory

namespace CircleDeg1Lift

variable {μ : Measure ℝ} [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure]

/-- **Rational rotation number with an invariant measure of full support.** Let `f` be a
continuous strictly increasing `CircleDeg1Lift` with translation number `p / q`, `q ≥ 1`, and
let `μ` be a locally finite measure on `ℝ` of full support, invariant under `f` and under the
integer translations (the lift of an invariant measure of full support on the circle). Then
`f^q(x) = x + p` for every `x`: every orbit is periodic of type `(p, q)`. -/
theorem iterate_eq_add_of_measurePreserving {f : CircleDeg1Lift} (hf : StrictMono f)
    (hfc : Continuous f) {p : ℤ} {q : ℕ} (hq : 0 < q) (hτ : f.translationNumber = p / q)
    (hμ : MeasurePreserving f μ μ) (hμℤ : ∀ m : ℤ, MeasurePreserving (· + (m : ℝ)) μ μ)
    (x : ℝ) : f^[q] x = x + p := by
  obtain ⟨z, hz⟩ := (f.translationNumber_eq_rat_iff hfc hq).1 hτ
  rw [coe_pow] at hz
  set h : ℝ → ℝ := fun y => f^[q] y + (-p : ℤ)
  have hh : StrictMono h := fun a b hab => by simpa [h] using hf.iterate q hab
  have hhμ : MeasurePreserving h μ μ := (hμℤ (-p)).comp (hμ.iterate q)
  -- The integer translates of the fixed point `z` of `h` are fixed points of `h`.
  have hfix (m : ℤ) : h (z + m) = z + m := by
    have := (f ^ q).map_add_int z m
    rw [coe_pow, hz] at this
    simp only [h, this]
    push_cast
    ring
  obtain ⟨m₁, hm₁⟩ := exists_int_lt (x - z)
  obtain ⟨m₂, hm₂⟩ := exists_int_gt (x - z)
  have hx := hhμ.map_eq_self_of_strictMono hh (x := x) (hfix m₁) (hfix m₂) (by linarith)
    (by linarith)
  simp only [h] at hx
  push_cast at hx
  linarith

end CircleDeg1Lift
