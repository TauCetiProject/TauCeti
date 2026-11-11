/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Field.RootsOfUnity
public import TauCeti.NumberTheory.Padics.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The cyclotomic radius in `ℂ_p`

For a primitive `p`-th root of unity `ζ` in `ℂ_[p]`, the distance from `ζ` to one is
`p ^ (-1 / (p - 1))`, strictly less than one. In particular the translated constant term
`ζ - 1` lies in the open unit ball, including at `p = 2`. This is the radius governing
convergent root-of-unity translations of integral power series.

The norm is computed from the cyclotomic product at one, not the field norm of a
cyclotomic extension. No choice of an algebraic representative of `ζ` is needed.

## References

* Rodrigues Jacinto and Williams, *An introduction to p-adic L-functions*, §3.5.3–5,
  for root-of-unity translation and averaging.
-/

public section

namespace IsPrimitiveRoot

variable {p : ℕ} [Fact p.Prime] {ζ : ℂ_[p]}

/-- The exact cyclotomic radius of a primitive `p`-th root of unity in `ℂ_[p]`.
The formula holds also for `p = 2`. -/
theorem norm_sub_one_padicComplex (hζ : IsPrimitiveRoot ζ p) :
    ‖ζ - 1‖ = (p : ℝ) ^ (-1 / ((p : ℝ) - 1)) := by
  have hn : p - 1 ≠ 0 := by have := (Fact.out : p.Prime).one_lt; omega
  have h := congrArg (fun x : ℝ => x ^ (((p - 1 : ℕ) : ℝ)⁻¹))
    hζ.norm_sub_one_pow_prime_sub_one
  rw [Real.pow_rpow_inv_natCast (norm_nonneg _) hn, PadicComplex.norm_p,
    ← Real.rpow_neg_eq_inv_rpow] at h
  simpa [Nat.cast_sub (Fact.out : p.Prime).one_lt.le, div_eq_mul_inv] using h

/-- Every primitive `p`-th root in `ℂ_[p]` lies at distance strictly less than one from one. -/
theorem norm_sub_one_padicComplex_lt_one (hζ : IsPrimitiveRoot ζ p) : ‖ζ - 1‖ < 1 := by
  rw [hζ.norm_sub_one_padicComplex]
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  exact Real.rpow_lt_one_of_one_lt_of_neg hp
    (div_neg_of_neg_of_pos (by norm_num) (sub_pos.mpr hp))

end IsPrimitiveRoot

/-- At the dyadic root `-1`, the cyclotomic radius is `1/2`, not one. -/
example : ‖(-1 : ℂ_[2]) - 1‖ = (2 : ℝ)⁻¹ := by
  have h := (IsPrimitiveRoot.neg_one 0 (by decide) : IsPrimitiveRoot (-1 : ℂ_[2]) 2)
  have heq := h.norm_sub_one_pow_prime_sub_one
  rw [PadicComplex.norm_p 2] at heq
  simpa using heq

example {ζ : ℂ_[3]} (hζ : IsPrimitiveRoot ζ 3) : ‖ζ - 1‖ ^ 2 = (3 : ℝ)⁻¹ := by
  have heq := hζ.norm_sub_one_pow_prime_sub_one
  rw [PadicComplex.norm_p 3] at heq
  simpa using heq

-- Primitivity matters: the trivial root does not have the cyclotomic radius.
example : ‖(1 : ℂ_[3]) - 1‖ ≠ (3 : ℝ) ^ (-1 / (3 - 1 : ℝ)) := by
  have : 0 < (3 : ℝ) ^ (-1 / (3 - 1 : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  simpa using this.ne
