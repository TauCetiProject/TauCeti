/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.JacobiSum.Basic
public import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.Basic

/-!
# The Jacobi sum of a power residue symbol

Let `K` be a number field whose ring of integers contains the `n`-th roots of unity, let `P` be
a maximal ideal of `𝓞 K` whose norm `N P` is prime to `n`, and let `χ = (· / P)_n` be the `n`-th
power residue symbol at `P`, a character of order `n` of the residue field with values in `𝓞 K`.
If `n > 2`, the Jacobi sum `J(χ, χ)` satisfies:

* `P ∣ J(χ, χ)`. Modulo `P` the symbol is the power map `x ↦ x ^ k` with `k = (N P - 1) / n`
  (`Ideal.mk_powerResidueSymbol`), so `J(χ, χ)` reduces to `∑ x, x ^ k (1 - x) ^ k`, which
  vanishes because `2 k < N P - 1`.
* `|σ (J(χ, χ))| = √(N P)` for every complex embedding `σ` of `K`, since `χ` and `χ ^ 2` are
  nontrivial.

These are the two facts that identify the Jacobi sum of the cubic residue symbol at a prime of
`ℤ[ω]` with the primary generator of that prime, the starting point of the proof of cubic
reciprocity through Jacobi sums.

## Main results

* `Ideal.jacobiSum_powerResidueSymbol_mem`: `J(χ, χ) ∈ P`.
* `Ideal.norm_jacobiSum_powerResidueSymbol`: `‖σ (J(χ, χ))‖ = √(N P)`.

## References

* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 8, §3,
  Theorem 1, and Chapter 9, §4, Lemma 1.
* S. D. Adhikari, *The early reciprocity laws: from Gauss to Eisenstein*, §3, Lemma 3.2.
* N. Xu, *Reciprocity Laws*, Proposition 4.8.
-/

public section

open NumberField

namespace Ideal

variable {K : Type*} [Field K] [NumberField K] {P : Ideal (𝓞 K)} [P.IsMaximal]
  [Fintype (𝓞 K ⧸ P)] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity (𝓞 K) n]

/-- **A prime divides the Jacobi sum of its power residue symbol.** If `n > 2` and `N P` is prime
to `n`, then `J(χ, χ) ∈ P` for the `n`-th power residue symbol `χ = (· / P)_n`. -/
theorem jacobiSum_powerResidueSymbol_mem (hP : (absNorm P).Coprime n) (hn : 2 < n) :
    jacobiSum (powerResidueSymbol P n) (powerResidueSymbol P n) ∈ P := by
  let _ := Ideal.Quotient.field P
  set k := (absNorm P - 1) / n
  have hcard : absNorm P = Fintype.card (𝓞 K ⧸ P) := by
    rw [absNorm_eq_natCard, Nat.card_eq_fintype_card]
  have hdvd : n ∣ absNorm P - 1 := dvd_absNorm_sub_one hP
  have hpos : 0 < absNorm P - 1 := by
    rw [hcard, Fintype.card_eq_nat_card, ← Nat.card_units]
    exact Nat.card_pos
  have hk : 0 < k := Nat.div_pos (Nat.le_of_dvd hpos hdvd) (NeZero.pos n)
  -- Modulo `P`, the symbol is the power map `x ↦ x ^ k`.
  have hχ (x : 𝓞 K ⧸ P) : Ideal.Quotient.mk P (powerResidueSymbol P n x) = x ^ k := by
    obtain rfl | hx := eq_or_ne x 0
    · rw [MulChar.map_zero, map_zero, zero_pow hk.ne']
    · exact mk_powerResidueSymbol hP hx
  have hkn : k + k < k * n := by nlinarith
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  refine TauCeti.map_jacobiSum_eq_zero _ hχ hχ ?_
  rwa [← hcard, ← Nat.div_mul_cancel hdvd]

/-- **The absolute value of the Jacobi sum of a power residue symbol.** If `n > 2` and `N P` is
prime to `n`, then `‖σ (J(χ, χ))‖ = √(N P)` for the `n`-th power residue symbol `χ = (· / P)_n`
and every complex embedding `σ` of `K`. -/
theorem norm_jacobiSum_powerResidueSymbol (hP : (absNorm P).Coprime n) (hn : 2 < n)
    (σ : K →+* ℂ) :
    ‖σ (jacobiSum (powerResidueSymbol P n) (powerResidueSymbol P n) : 𝓞 K)‖ = √(absNorm P) := by
  let _ := Ideal.Quotient.field P
  let f := σ.comp (algebraMap (𝓞 K) K)
  have hf : Function.Injective f := σ.injective.comp (FaithfulSMul.algebraMap_injective _ _)
  have hord := orderOf_powerResidueSymbol hP
  have hχ : (powerResidueSymbol P n).ringHomComp f ≠ 1 := by
    rw [MulChar.ringHomComp_ne_one_iff hf]
    exact fun h ↦ by simp [h] at hord; lia
  have hχχ : (powerResidueSymbol P n).ringHomComp f * (powerResidueSymbol P n).ringHomComp f ≠
      1 := by
    rw [← MulChar.ringHomComp_mul, MulChar.ringHomComp_ne_one_iff hf, ← sq]
    exact pow_ne_one_of_lt_orderOf two_ne_zero (by rwa [hord])
  have h : σ (jacobiSum (powerResidueSymbol P n) (powerResidueSymbol P n) : 𝓞 K) =
      jacobiSum ((powerResidueSymbol P n).ringHomComp f)
        ((powerResidueSymbol P n).ringHomComp f) :=
    (jacobiSum_ringHomComp _ _ f).symm
  rw [h, TauCeti.norm_jacobiSum hχ hχ hχχ, absNorm_eq_natCard, Nat.card_eq_fintype_card]

end Ideal
