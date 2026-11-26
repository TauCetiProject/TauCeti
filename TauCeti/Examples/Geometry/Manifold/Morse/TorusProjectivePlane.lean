/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import TauCeti.Geometry.Manifold.Morse.Perfect

/-!
# Examples: the Morse polynomials of the two-torus and of the real projective plane

For a Morse function on a compact manifold with critical counts `cⱼ` and Betti numbers `bⱼ` over a
division ring, the strong Morse inequalities say `∑ cⱼ tʲ = ∑ bⱼ tʲ + (1 + t) Q(t)` for a
polynomial `Q` with natural coefficients (`TauCeti.morse_inequalities`), and `Q` is determined by
the counts and the Betti numbers (`TauCeti.forall_criticalCount_eq_bettiNumber_add_coeff_iff`).
This file computes both sides on two surfaces.

* **The two-torus.** The cosine function `cos (2π x₀ / p₀) + cos (2π x₁ / p₁)` on the torus
  `T² = ∀ i : Fin 2, AddCircle (p i)` (`TauCeti.torusCos`) has one minimum, two saddles and one
  maximum, so its Morse polynomial `∑ cⱼ tʲ` is `1 + 2t + t²`. Over every field this is also the
  Betti polynomial of `T²`, so `Q = 0`.
* **The real projective plane.** Let `f` be a Morse function on `ℝP²` with one critical point of
  each index `0`, `1` and `2`, such as the moment function `[x] ↦ (x₁² + 2 x₂²) / ‖x‖²`, the
  quadratic coordinate function with the three weights `0, 1, 2`. The same counts `1 + t + t²`
  meet different Betti polynomials: over `ℚ` the Betti polynomial of `ℝP²` is `1` and `Q = t`,
  `1 + t + t² = 1 + (1 + t) t`, while over `ZMod 2` it is `1 + t + t²` and `Q = 0`, so `f` is
  perfect over `ZMod 2` but not over `ℚ`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Section 5.
-/

public section

open Polynomial
open scoped Manifold LinearAlgebra.Projectivization

namespace TauCeti.Examples.MorsePolynomialTorusProjectivePlane

open TauCeti

/-! ### The two-torus -/

section Torus

/-- The coefficients of `1 + 2t + t² = (1 + t)²` are the binomial coefficients `(2 choose j)`. -/
theorem coeff_one_add_two_mul_X_add_X_sq (j : ℕ) :
    (1 + 2 * X + X ^ 2 : ℕ[X]).coeff j = (2 : ℕ).choose j := by
  rw [show (1 + 2 * X + X ^ 2 : ℕ[X]) = (X + 1) ^ 2 by ring, coeff_X_add_one_pow, Nat.cast_id]

variable (p : Fin 2 → ℝ) [∀ i, Fact (0 < p i)]

-- The cosine function on `T²` has one critical point of index `0`, two of index `1` and one of
-- index `2`: its Morse polynomial is `1 + 2t + t²`.
example (j : ℕ) :
    criticalCount (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) (torusCos p) j =
      ((1 + 2 * X + X ^ 2 : ℕ[X]).coeff j : ℕ∞) := by
  rw [criticalCount_torusCos, coeff_one_add_two_mul_X_add_X_sq, Fintype.card_fin]

-- Over every field the Betti polynomial of `T²` is `1 + 2t + t²` too: it agrees with the critical
-- counts of the cosine function, which is perfect.
example (k : Type) [Field k] (j : ℕ) :
    bettiNumber k (∀ i, AddCircle (p i)) j = (1 + 2 * X + X ^ 2 : ℕ[X]).coeff j := by
  have h := (isPerfectMorse_torusCos p k).criticalCount_eq j
  rw [criticalCount_torusCos, Fintype.card_fin, ← bettiNumber_def, Nat.cast_inj] at h
  rw [← h, coeff_one_add_two_mul_X_add_X_sq]

-- So the cosine function on `T²` is perfect over every field: its polynomial `Q` is `0`.
example (k : Type) [Field k] {Q : ℕ[X]} :
    (∀ j : ℕ, criticalCount (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) (torusCos p) j =
      ((bettiNumber k (∀ i, AddCircle (p i)) j + ((1 + X) * Q).coeff j : ℕ) : ℕ∞)) ↔ Q = 0 :=
  forall_criticalCount_eq_bettiNumber_add_coeff_iff fun j ↦ by
    simp [(isPerfectMorse_torusCos p k).criticalCount_eq j, bettiNumber_def]

end Torus

/-! ### The real projective plane -/

section ProjectivePlane

-- Over `ℚ` the Betti polynomial of `ℝP²` is `1`: `H₁(ℝP²; ℚ)` and `H₂(ℝP²; ℚ)` vanish.
example (j : ℕ) : bettiNumber ℚ (ℙ ℝ (Fin 3 → ℝ)) j = (1 : ℕ[X]).coeff j := by
  rw [bettiNumber_def,
    RealProjectiveSpace.finrank_singularHomology_projectivization_of_two_ne_zero
      (two_ne_zero : (2 : ℚ) ≠ 0),
    coeff_one]
  simp [show ¬Odd 2 by decide]

-- Over `ZMod 2` the Betti polynomial of `ℝP²` is `1 + t + t²`.
example (j : ℕ) :
    bettiNumber (ZMod 2) (ℙ ℝ (Fin 3 → ℝ)) j = (1 + X + X ^ 2 : ℕ[X]).coeff j := by
  rw [bettiNumber_def,
    RealProjectiveSpace.finrank_singularHomology_projectivization_of_two_eq_zero
      (by decide : (2 : ZMod 2) = 0)]
  rcases j with _ | _ | _ | j <;> simp [coeff_one, coeff_X, coeff_X_pow]

-- The moment function with the weights `0, 1, 2` is a Morse function on `ℝP²` with one critical
-- point of each index `0`, `1` and `2`.
example : IsMorse 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ fun i : Fin 3 ↦ ((i : ℕ) : ℝ)) ∧
    ∀ j ≤ 2, criticalCount 𝓘(ℝ, Fin 2 → ℝ)
      (projectiveMomentFunction ℝ fun i : Fin 3 ↦ ((i : ℕ) : ℝ)) j = 1 :=
  have hw : Function.Injective fun i : Fin 3 ↦ ((i : ℕ) : ℝ) :=
    Nat.cast_injective.comp Fin.val_injective
  ⟨isMorse_projectiveMomentFunction hw, fun j hj ↦ by
    simp [criticalCount_projectiveMomentFunction_real hw, hj]⟩

variable {f : ℙ ℝ (Fin 3 → ℝ) → ℝ}

-- For a function on `ℝP²` with one critical point of each index, the Morse polynomial over `ℚ`
-- is `Q = t`: `1 + t + t² = 1 + (1 + t) t`.
example (hc : ∀ j ≤ 2, criticalCount 𝓘(ℝ, Fin 2 → ℝ) f j = 1) {Q : ℕ[X]} :
    (∀ j : ℕ, criticalCount 𝓘(ℝ, Fin 2 → ℝ) f j =
      ((bettiNumber ℚ (ℙ ℝ (Fin 3 → ℝ)) j + ((1 + X) * Q).coeff j : ℕ) : ℕ∞)) ↔ Q = X := by
  rw [forall_criticalCount_projectivization_real_eq_bettiNumber_add_coeff_iff hc
    (two_ne_zero : (2 : ℚ) ≠ 0)]
  simp [Finset.sum_filter, Finset.sum_range_succ]

-- Over `ZMod 2` such a Morse function is perfect, so its Morse polynomial is `Q = 0`:
-- `1 + t + t² = (1 + t + t²) + (1 + t) · 0`.
example (hf : IsMorse 𝓘(ℝ, Fin 2 → ℝ) f)
    (hc : ∀ j ≤ 2, criticalCount 𝓘(ℝ, Fin 2 → ℝ) f j = 1) {Q : ℕ[X]} :
    (∀ j : ℕ, criticalCount 𝓘(ℝ, Fin 2 → ℝ) f j =
      ((bettiNumber (ZMod 2) (ℙ ℝ (Fin 3 → ℝ)) j + ((1 + X) * Q).coeff j : ℕ) : ℕ∞)) ↔ Q = 0 :=
  have hperf := hf.isPerfectMorse_projectivization_real hc (by decide : (2 : ZMod 2) = 0)
  forall_criticalCount_eq_bettiNumber_add_coeff_iff fun j ↦ by
    simp [hperf.criticalCount_eq j, bettiNumber_def]

-- Over `ℚ` no Morse function on `ℝP²` is perfect.
example : ¬IsPerfectMorse 𝓘(ℝ, Fin 2 → ℝ) ℚ f :=
  not_isPerfectMorse_projectivization_real (by decide) two_ne_zero f

end ProjectivePlane

end TauCeti.Examples.MorsePolynomialTorusProjectivePlane
