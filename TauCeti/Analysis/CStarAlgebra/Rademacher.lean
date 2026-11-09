/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import TauCeti.Algebra.BigOperators.SignCube
public import TauCeti.Analysis.CStarAlgebra.Module.Constructions

/-!
# Rademacher sums in C⋆-algebras

This file proves two estimates for random sign sums with coefficients in a possibly nonunital
C⋆-algebra `A`, averaged over the sign cube `ι → ℤˣ` (`TauCeti.signAverage`). They are the
operator-valued ingredients of the noncommutative Khintchine inequality at the exponent one with
the constant `3^(-1/2)`.

* **Square functions of sign coefficients.** If `‖Φ ε‖ ≤ r` for every sign vector `ε`, the
  coefficients `yₖ = 𝔼 εₖ Φ` satisfy `‖∑ₖ yₖ* yₖ‖ ≤ r²` and `‖∑ₖ yₖ yₖ*‖ ≤ r²`
  (`TauCeti.norm_sum_star_mul_le_of_norm_le`, `TauCeti.norm_sum_mul_star_le_of_norm_le`). This is
  the norm form of Bessel's inequality for the sign functions,
  `TauCeti.sum_star_mul_le_signAverage_star_mul`.
* **The fourth moment estimate.** For self-adjoint `x₁, …, xₙ` and `S = ∑ₖ εₖ xₖ`,
  `‖𝔼 S⁴‖ ≤ 3 ‖∑ₖ xₖ²‖²` (`TauCeti.norm_signAverage_rademacherSum_mul_four_le`). The proof expands
  `𝔼 S⁴` over pairings (`TauCeti.signAverage_rademacherSum_mul_four`), bounds each of the three
  pairing terms by `‖∑ₖ xₖ²‖²` (`TauCeti.norm_sum_mul_sum_mul_self_mul_le`, and for the crossing
  term `TauCeti.norm_sum_sum_mul_mul_mul_le`, through the row–column inequality
  `TauCeti.norm_sum_mul_le_sqrt_mul_sqrt`), and discards the nonpositive diagonal correction. The
  constant `3` is optimal: for commuting scalars `xₖ = 1` the ratio is `3 - 2 / n`.

## References

* G. Pisier, *Grothendieck's theorem, past and present*, Bull. Amer. Math. Soc. 49 (2012),
  237–323, §9: Lemma 9.2 (the fourth moment estimate, which Pisier attributes to Pisier (1978)
  and Haagerup (1985)) and the orthogonality estimate (9.11) in the proof of Theorem 9.1.
* U. Haagerup and M. Musat, *On the best constants in noncommutative Khintchine-type
  inequalities*, J. Funct. Anal. 250 (2007), 588–624, §2.
-/

public section

open Finset

namespace TauCeti

variable {ι A : Type*} [Fintype ι] [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-! ### Square functions of sign coefficients -/

section SquareFunction

variable [DecidableEq ι]

/-- The column square function of the sign coefficients `yₖ = 𝔼 εₖ Φ` of a function `Φ` bounded
by `r` satisfies `‖∑ₖ yₖ* yₖ‖ ≤ r²`. -/
theorem norm_sum_star_mul_le_of_norm_le {Φ : (ι → ℤˣ) → A} {r : ℝ} (h : ∀ ε, ‖Φ ε‖ ≤ r) :
    ‖∑ k, star (signAverage fun ε => (ε k : ℤ) • Φ ε) *
        signAverage (fun ε => (ε k : ℤ) • Φ ε)‖ ≤ r ^ 2 := by
  refine (CStarAlgebra.norm_le_norm_of_le_of_nonneg (sum_star_mul_le_signAverage_star_mul Φ)
    (sum_nonneg fun k _ => star_mul_self_nonneg _)).trans (norm_signAverage_le fun ε => ?_)
  rw [CStarRing.norm_star_mul_self, ← sq]
  exact pow_le_pow_left₀ (norm_nonneg _) (h ε) 2

/-- The row square function of the sign coefficients `yₖ = 𝔼 εₖ Φ` of a function `Φ` bounded
by `r` satisfies `‖∑ₖ yₖ yₖ*‖ ≤ r²`. -/
theorem norm_sum_mul_star_le_of_norm_le {Φ : (ι → ℤˣ) → A} {r : ℝ} (h : ∀ ε, ‖Φ ε‖ ≤ r) :
    ‖∑ k, signAverage (fun ε => (ε k : ℤ) • Φ ε) *
        star (signAverage fun ε => (ε k : ℤ) • Φ ε)‖ ≤ r ^ 2 := by
  refine (CStarAlgebra.norm_le_norm_of_le_of_nonneg (sum_mul_star_le_signAverage_mul_star Φ)
    (sum_nonneg fun k _ => mul_star_self_nonneg _)).trans (norm_signAverage_le fun ε => ?_)
  rw [CStarRing.norm_self_mul_star, ← sq]
  exact pow_le_pow_left₀ (norm_nonneg _) (h ε) 2

end SquareFunction

/-! ### The fourth moment estimate -/

section FourthMoment

variable [DecidableEq ι] {x : ι → A}

/-- **The fourth moment estimate for Rademacher sums.** For self-adjoint `x₁, …, xₙ` in a
C⋆-algebra and `S = ∑ₖ εₖ xₖ`, the average of `S⁴` over the signs satisfies
`‖𝔼 S⁴‖ ≤ 3 ‖∑ₖ xₖ²‖²`. -/
theorem norm_signAverage_rademacherSum_mul_four_le (hx : ∀ k, IsSelfAdjoint (x k)) :
    ‖signAverage (fun ε => rademacherSum x ε * rademacherSum x ε * rademacherSum x ε *
        rademacherSum x ε)‖ ≤ 3 * ‖∑ k, x k * x k‖ ^ 2 := by
  have hstar (k : ι) : star (x k) = x k := (hx k).star_eq
  -- `𝔼 S⁴` is positive, and below the sum of the three pairing terms
  have h₀ : 0 ≤ signAverage (fun ε => rademacherSum x ε * rademacherSum x ε *
      rademacherSum x ε * rademacherSum x ε) := by
    refine signAverage_nonneg fun ε => ?_
    have hS := (isSelfAdjoint_rademacherSum hx ε).star_eq
    simpa only [star_mul, hS, mul_assoc] using
      star_mul_self_nonneg (rademacherSum x ε * rademacherSum x ε)
  have hD : 0 ≤ ∑ i, x i * x i * x i * x i :=
    sum_nonneg fun i _ => by
      simpa only [star_mul, hstar, mul_assoc] using star_mul_self_nonneg (x i * x i)
  have hle : signAverage (fun ε => rademacherSum x ε * rademacherSum x ε *
      rademacherSum x ε * rademacherSum x ε) ≤
        (∑ i, x i * x i) * (∑ i, x i * x i) + ∑ i, x i * (∑ j, x j * x j) * x i +
          ∑ i, ∑ j, x i * x j * x i * x j := by
    rw [signAverage_rademacherSum_mul_four]
    exact sub_le_self _ (nsmul_nonneg hD 2)
  calc _ ≤ ‖(∑ i, x i * x i) * (∑ i, x i * x i) + ∑ i, x i * (∑ j, x j * x j) * x i +
          ∑ i, ∑ j, x i * x j * x i * x j‖ := CStarAlgebra.norm_le_norm_of_le_of_nonneg hle h₀
    _ ≤ ‖(∑ i, x i * x i) * (∑ i, x i * x i)‖ + ‖∑ i, x i * (∑ j, x j * x j) * x i‖ +
          ‖∑ i, ∑ j, x i * x j * x i * x j‖ := norm_add₃_le
    _ ≤ ‖∑ k, x k * x k‖ ^ 2 + ‖∑ k, x k * x k‖ ^ 2 + ‖∑ k, x k * x k‖ ^ 2 := by
      gcongr
      · exact (norm_mul_le _ _).trans_eq (sq _).symm
      · exact norm_sum_mul_sum_mul_self_mul_le hx
      · exact (norm_sum_sum_mul_mul_mul_le hx).trans (norm_sum_mul_sum_mul_self_mul_le hx)
    _ = 3 * ‖∑ k, x k * x k‖ ^ 2 := by ring

end FourthMoment

end TauCeti
