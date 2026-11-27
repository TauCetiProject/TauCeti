/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import TauCeti.LinearAlgebra.Matrix.Charpoly.Newton
public import TauCeti.RepresentationTheory.Character.Pow
import TauCeti.LinearAlgebra.Charpoly.FinrankTwo

/-!
# Characters determine characteristic polynomials

For a finite-dimensional representation `ρ` of a monoid and an element `g`, the traces of the
powers of `ρ g` are character values: `tr (ρ g ^ j) = χ_ρ (g ^ j)`. Newton's identities for the
traces of the powers of an endomorphism therefore express the coefficients of `det (1 - X ρ g)`
through the character values `χ_ρ (g), χ_ρ (g ^ 2), …`. In characteristic zero the recurrence can
be solved, so the dimension of `ρ` together with the values `χ_ρ (g ^ j)` for `0 < j ≤ dim ρ`
determines the characteristic polynomial of `ρ g`. In dimension two it is enough that `2 ≠ 0`:
`det (ρ g) = (χ_ρ (g) ^ 2 - χ_ρ (g ^ 2)) / 2`.

## Main results

* `Representation.mul_coeff_reverse_charpoly_eq_neg_sum`: **Newton's identities** in character
  form, `r c_r = -(c_(r-1) χ(g) + c_(r-2) χ(g ^ 2) + ⋯ + c_0 χ(g ^ r))` for the coefficients `c_r`
  of `det (1 - X ρ g)`, in every characteristic.
* `Representation.charpoly_eq_of_character_eq_of_finrank_eq_two`: when `2 ≠ 0`, the character
  values on `g` and `g ^ 2` determine the characteristic polynomial of `ρ g` in dimension two.
* `Representation.charpoly_eq_of_character_pow_eq`,
  `Representation.charpoly_eq_iff_character_pow_eq`: in characteristic zero, the dimension and the
  character values on `g, g ^ 2, …, g ^ d` determine the characteristic polynomial of `ρ g`. The
  two representations may be of different monoids.
* `Representation.det_eq_det_pow_of_character_eq`: in characteristic zero, if
  `χ_{ρ'}(y) = χ_ρ(y ^ j)` on the powers `y` of `x`, then `det ρ'(x) = (det ρ(x)) ^ j`.
* `Representation.charpoly_apply_eq_of_sq_eq_one`: in characteristic zero, if `g ^ 2 = 1`, then
  `charpoly (ρ g) = (X - 1) ^ a * (X + 1) ^ b` whenever `a + b = dim ρ` and `a - b = χ_ρ (g)`.

## References

* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, 2nd ed., Oxford (1995), Ch. I,
  §2, (2.11′).
-/

public section

open Finset Module Polynomial

namespace Representation

variable {k G H V W : Type*} [Field k] [Monoid G] [Monoid H] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [FiniteDimensional k V] [FiniteDimensional k W]
  {ρ : Representation k G V} {σ : Representation k H W}

variable (ρ) in
/-- **Newton's identities** in character form: the coefficients `c_r` of `det (1 - X ρ g)`, the
reverse of the characteristic polynomial of `ρ g`, satisfy
`r c_r = -(c_(r-1) χ(g) + c_(r-2) χ(g ^ 2) + ⋯ + c_0 χ(g ^ r))`, in every characteristic. -/
theorem mul_coeff_reverse_charpoly_eq_neg_sum (g : G) (r : ℕ) :
    (r : k) * (ρ g).charpoly.reverse.coeff r =
      -∑ j ∈ range r, (ρ g).charpoly.reverse.coeff (r - (j + 1)) * ρ.character (g ^ (j + 1)) := by
  simp only [← trace_pow_eq_character_pow]
  exact (ρ g).mul_coeff_reverse_charpoly_eq_neg_sum r

/-- In every characteristic, the characteristic polynomial of `ρ g` determines the character values
at all powers of `g`. -/
theorem character_pow_eq_of_charpoly_eq {g : G} {h : H} (hgh : (ρ g).charpoly = (σ h).charpoly)
    (j : ℕ) : ρ.character (g ^ j) = σ.character (h ^ j) := by
  rw [← trace_pow_eq_character_pow, ← trace_pow_eq_character_pow,
    LinearMap.trace_pow_eq_of_charpoly_eq hgh j]

/-- **Characters determine characteristic polynomials in dimension two** when `2 ≠ 0`: the
determinant of `ρ g` is `(χ_ρ (g) ^ 2 - χ_ρ (g ^ 2)) / 2`. The two representations may be of
different monoids. -/
theorem charpoly_eq_of_character_eq_of_finrank_eq_two (hk : (2 : k) ≠ 0)
    (hV : finrank k V = 2) (hW : finrank k W = 2) {g : G} {h : H}
    (h₁ : ρ.character g = σ.character h) (h₂ : ρ.character (g ^ 2) = σ.character (h ^ 2)) :
    (ρ g).charpoly = (σ h).charpoly := by
  simp only [character] at h₁ h₂
  have hdet : LinearMap.det (ρ g) = LinearMap.det (σ h) := by
    have hρ := LinearMap.trace_mul_self_of_finrank_eq_two hV (ρ g)
    have hσ := LinearMap.trace_mul_self_of_finrank_eq_two hW (σ h)
    rw [← map_mul, ← sq] at hρ hσ
    refine mul_left_cancel₀ hk ?_
    linear_combination hρ - hσ - h₂ + (LinearMap.trace k V (ρ g) +
      LinearMap.trace k W (σ h)) * h₁
  rw [LinearMap.charpoly_of_finrank_eq_two hV, LinearMap.charpoly_of_finrank_eq_two hW, h₁, hdet]

variable [CharZero k]

/-- In characteristic zero, the dimension of `ρ` and the character values `χ_ρ (g ^ j)` for
`0 < j ≤ dim ρ` determine the characteristic polynomial of `ρ g`. The two representations may be
of different monoids. -/
theorem charpoly_eq_of_character_pow_eq {g : G} {h : H} (hVW : finrank k V = finrank k W)
    (hgh : ∀ j, 0 < j → j ≤ finrank k V → ρ.character (g ^ j) = σ.character (h ^ j)) :
    (ρ g).charpoly = (σ h).charpoly :=
  LinearMap.charpoly_eq_of_trace_pow_eq hVW fun j hj hjV ↦ by
    rw [trace_pow_eq_character_pow, trace_pow_eq_character_pow, hgh j hj hjV]

/-- In characteristic zero, for representations of the same dimension, `ρ g` and `σ h` have the
same characteristic polynomial if and only if `χ_ρ (g ^ j) = χ_σ (h ^ j)` for every `j > 0`. -/
theorem charpoly_eq_iff_character_pow_eq {g : G} {h : H} (hVW : finrank k V = finrank k W) :
    (ρ g).charpoly = (σ h).charpoly ↔ ∀ j, 0 < j → ρ.character (g ^ j) = σ.character (h ^ j) :=
  ⟨fun hgh j _ ↦ character_pow_eq_of_charpoly_eq hgh j, fun hgh ↦
    charpoly_eq_of_character_pow_eq hVW fun j hj _ ↦ hgh j hj⟩

variable (ρ) in
/-- **Determinants of power-map twists.** In characteristic zero, if the character of `ρ'` at every
power `y` of `x` is the character of `ρ` at `y ^ j`, then `det ρ'(x) = (det ρ(x)) ^ j`. -/
theorem det_eq_det_pow_of_character_eq (ρ' : Representation k G W) {x : G} {j : ℕ}
    (h : ∀ y ∈ Submonoid.powers x, ρ'.character y = ρ.character (y ^ j)) :
    (ρ' x).det = (ρ x).det ^ j := by
  have hdim : finrank k W = finrank k V := by
    have h1 := h 1 (one_mem _)
    rw [one_pow, char_one, char_one] at h1
    exact_mod_cast h1
  have hcp : (ρ' x).charpoly = (ρ (x ^ j)).charpoly :=
    charpoly_eq_of_character_pow_eq hdim fun i _ _ ↦ by
      rw [h _ (pow_mem (Submonoid.mem_powers x) i), ← pow_mul, ← pow_mul, mul_comm]
  rw [LinearMap.det_eq_sign_charpoly_coeff, hcp, hdim, ← LinearMap.det_eq_sign_charpoly_coeff,
    map_pow, map_pow]

/-- In characteristic zero, if `g ^ 2 = 1`, then the characteristic polynomial of `ρ g` is
`(X - 1) ^ a * (X + 1) ^ b` for any `a` and `b` with `a + b = dim ρ` and `a - b = χ_ρ (g)`. -/
theorem charpoly_apply_eq_of_sq_eq_one {g : G} (hg : g ^ 2 = 1) {a b : ℕ}
    (hab : a + b = finrank k V) (hχ : (a : k) - b = ρ.character g) :
    (ρ g).charpoly = (X - 1) ^ a * (X + 1) ^ b :=
  LinearMap.charpoly_eq_of_sq_eq_one (by rw [← map_pow, hg, map_one]) hab hχ

end Representation
