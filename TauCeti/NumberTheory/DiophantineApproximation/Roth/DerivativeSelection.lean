/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import TauCeti.RingTheory.MvPolynomial.WeightedIndex

/-!
# Choosing a Hasse derivative of Roth's auxiliary polynomial

In the proof of Roth's theorem, an integer auxiliary polynomial `P` vanishes to a high index at
the diagonal point `(α, …, α)`, while Roth's index estimate shows that its index at a tuple `β` of
good rational approximations of `α` is small. The final step needs a polynomial that does not
vanish at `β` at all. It is obtained as a Hasse derivative `Q = ∂^d P`, where `d` is a jet of `P`
at `β` of minimal weight. Since `∂^d` lowers indices by at most the weight of `d`, the index of
`Q` at the diagonal point is still large, and the coefficients of `Q` are at most `2 ^ ∑ᵢ rᵢ`
times those of `P`, where the `rᵢ` bound the partial degrees of `P`.

The value `Q(β)` is then a nonzero rational number which is bounded from above using the large
index of `Q` at the diagonal point, and from below by the denominators of `β`. Comparing the two
bounds yields the contradiction which proves Roth's theorem.

## Main results

* `TauCeti.exists_roth_hasseDeriv`: the choice of `Q` made by
  `MvPolynomial.exists_hasseDeriv_eval_ne_zero`, with the parameters of the proof of Roth's
  theorem. An index at least `(n / 2) (1 - ε)` at `a` and an index at most `5 n ε / 2` at `b`
  leave the derivative an index at least `(1 / 2 - 3 ε) n` at `a`, and coefficients at most
  `exp (C₁ ∑ᵢ rᵢ)` with `∑ᵢ rᵢ ≤ 2 D / L` become coefficients at most `exp (4 C₁ D / L)`.

## References

* L. Pottmeyer, [*Diophantine Approximation*](https://esaga.uni-due.de/f/lukas.pottmeyer/DioApp.pdf)
  (2022), §3.5, Lemma 3.5.7.
-/

public section

namespace TauCeti

open MvPolynomial Finset
open scoped ENNReal

variable {σ F K : Type*} [Fintype σ] [CommRing F] [CommRing K]

/-- **Pottmeyer, Lemma 3.5.7.** The choice of a nonvanishing Hasse derivative of Roth's
auxiliary polynomial. Let `P` be an integer polynomial in `n` variables with partial degrees
`degreeOf i P ≤ r i`, where `∑ᵢ rᵢ ≤ 2 D / L`, and with coefficients of absolute value at most
`exp (C₁ ∑ᵢ rᵢ)`, where `C₁ ≥ log 2`. Let `0 ≤ ε`. If the index of `P` is at least
`(n / 2) (1 - ε)` at `a` and at most `5 n ε / 2` at `b`, then some Hasse derivative
`Q = ∂^d P` does not vanish at `b`, has index at least `(1 / 2 - 3 ε) n` at `a`, has partial
degrees at most `r i`, and has coefficients of absolute value at most `exp (4 C₁ D / L)`. -/
theorem exists_roth_hasseDeriv {P : MvPolynomial σ ℤ} {r : σ → ℕ}
    (hdeg : ∀ i, P.degreeOf i ≤ r i) {ε C₁ D L : ℝ} (hε : 0 ≤ ε) (hC₁ : Real.log 2 ≤ C₁)
    (hr : ∑ i, (r i : ℝ) ≤ 2 * D / L)
    (hP : ∀ μ, |(P.coeff μ : ℝ)| ≤ Real.exp (C₁ * ∑ i, (r i : ℝ))) {a : σ → F} {b : σ → K}
    (ha : ENNReal.ofReal (Fintype.card σ / 2 * (1 - ε)) ≤
      weightedIndex r a (P.map (Int.castRingHom F)))
    (hb : weightedIndex r b (P.map (Int.castRingHom K)) ≤
      ENNReal.ofReal (5 * Fintype.card σ * ε / 2)) :
    ∃ d : σ →₀ ℕ, eval b ((hasseDeriv d P).map (Int.castRingHom K)) ≠ 0 ∧
      ENNReal.ofReal ((1 / 2 - 3 * ε) * Fintype.card σ) ≤
        weightedIndex r a ((hasseDeriv d P).map (Int.castRingHom F)) ∧
      (∀ i, (hasseDeriv d P).degreeOf i ≤ r i) ∧
      ∀ μ, |((hasseDeriv d P).coeff μ : ℝ)| ≤ Real.exp (4 * C₁ * D / L) := by
  obtain ⟨d, hd, hind, hdeg', hcoeff⟩ :=
    exists_hasseDeriv_eval_ne_zero hdeg (AbsoluteValue.abs.comp (f := Int.castRingHom ℝ)
      Int.cast_injective) hP (Int.castRingHom F) a (Int.castRingHom K)
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb)
  refine ⟨d, hd, le_trans ?_ (le_trans (tsub_le_tsub ha hb) hind), hdeg', fun μ ↦ ?_⟩
  · rw [← ENNReal.ofReal_sub _ (by positivity)]
    exact le_of_eq (congrArg ENNReal.ofReal (by ring))
  -- `2 ^ ∑ᵢ rᵢ * exp (C₁ ∑ᵢ rᵢ) = exp ((log 2 + C₁) ∑ᵢ rᵢ) ≤ exp (2 C₁ ∑ᵢ rᵢ)`.
  have hC₀ : 0 ≤ C₁ := (Real.log_nonneg one_le_two).trans hC₁
  have hr₀ : 0 ≤ ∑ i, (r i : ℝ) := by positivity
  refine (hcoeff μ).trans ?_
  rw [← Real.exp_log (two_pos (α := ℝ)), ← Real.exp_nat_mul, ← Real.exp_add, Nat.cast_sum]
  gcongr
  calc (∑ i, (r i : ℝ)) * Real.log 2 + C₁ * ∑ i, (r i : ℝ) ≤ 2 * C₁ * ∑ i, (r i : ℝ) := by
        nlinarith
    _ ≤ 2 * C₁ * (2 * D / L) := by gcongr
    _ = 4 * C₁ * D / L := by ring

end TauCeti
