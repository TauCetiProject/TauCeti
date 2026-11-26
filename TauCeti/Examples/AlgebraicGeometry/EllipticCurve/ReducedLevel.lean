/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.ReducedLevel
import Mathlib.Tactic.Simproc.Factors
import Mathlib.Data.Nat.Squarefree

/-!
# Examples of the reduced level `M₀`

The arithmetic reduced level `M₀ = M / ∏ q`, over the primes `q ∥ M` with `ℓ ∣ v_q(Δ)`, on the
data of Bennett–Siksek, equation (3):

* `M = 33`, `v_3(Δ) = 6`, `v_11(Δ) = 2` and `ℓ = 3` give `M₀ = 11`: the prime `3 = ℓ` is removed;
* `M = 141 = 3 · 47`, `v_3(Δ) = 7`, `v_47(Δ) = 1` and `ℓ = 3` give `M₀ = 141`, while `ℓ = 7`
  gives `M₀ = 47`;
* `M = 3² · 5`, `v_3(Δ) = v_5(Δ) = 7` and `ℓ = 7` give `M₀ = 9`: the exponent two at `3` is kept;
* `M = 1` gives `M₀ = 1`, and the sign of `Δ` does not matter.

The elliptic curve `141a1`, `y² + y = x³ + x² - 12 x + 2`, has discriminant `3⁷ · 47` and
`c₄ = 2⁴ · 37`. These are coprime, so the equation is globally minimal and the curve is
semistable of conductor `141`. Its reduced level is `141` at `ℓ = 3` and `47` at `ℓ = 7`. At
`ℓ = 3` Ribet–Stein (§1.4) record the Serre conductor `N(E[3]) = 47`, which is not computed here:
the reduced level is a weight-two level and need not be the Serre conductor.

## References

* M. A. Bennett and S. Siksek, *A conjecture of Erdős, supersingular primes and short character
  sums*, Ann. of Math. 191 (2020), 355–392, equation (3).
* K. A. Ribet and W. A. Stein, *Lectures on Serre's conjectures*, §1.4.
* J. E. Cremona, *Algorithms for Modular Elliptic Curves*, 2nd ed., the tables, curve 141A1.
-/

public section

namespace TauCeti.Examples.ReducedLevel

open Nat WeierstrassCurve

/-- The prime factors of `n` as the underlying set of its list of prime factors, a form that the
`Nat.primeFactorsList` simproc evaluates on numerals. -/
private theorem primeFactors_eq_toFinset (n : ℕ) : n.primeFactors = n.primeFactorsList.toFinset :=
  (Nat.toFinset_factors n).symm

/-- The level-lowering primes in terms of lists of prime factors, so that `norm_num` evaluates
them on numerals: at a prime `q`, the exponent of `q` in `n` is the number of times `q` occurs
in the list of prime factors of `n`. -/
private theorem levelLoweringPrimes_eq_count (M : ℕ) (Δ : ℤ) (ℓ : ℕ) :
    levelLoweringPrimes M Δ ℓ = M.primeFactorsList.toFinset.filter fun q ↦
      M.primeFactorsList.count q = 1 ∧ ℓ ∣ Δ.natAbs.primeFactorsList.count q := by
  rw [levelLoweringPrimes_def, ← primeFactors_eq_toFinset]
  refine Finset.filter_congr fun q hq ↦ ?_
  have hq := Nat.prime_of_mem_primeFactors hq
  simp only [Nat.multiplicity_eq_factorization hq, Nat.primeFactorsList_count_eq]

/-! ### The arithmetic reduced level -/

-- `M = 33`, `Δ = 3⁶ · 11²`, `ℓ = 3`: the prime `3 = ℓ` is removed and `11` is kept.
example : levelLoweringPrimes 33 (3 ^ 6 * 11 ^ 2) 3 = {3} := by
  rw [levelLoweringPrimes_eq_count]
  norm_num [Finset.filter_insert, Finset.filter_singleton]

example : reducedEllipticLevel 33 (3 ^ 6 * 11 ^ 2) 3 = 11 := by
  rw [reducedEllipticLevel_def, levelLoweringPrimes_eq_count]
  norm_num [Finset.filter_insert, Finset.filter_singleton]

-- `M = 141`, `Δ = 3⁷ · 47`, `ℓ = 3`: neither valuation is divisible by `3`, nothing is removed.
example : reducedEllipticLevel 141 (3 ^ 7 * 47) 3 = 141 := by
  rw [reducedEllipticLevel_def, levelLoweringPrimes_eq_count]
  norm_num [Finset.filter_insert, Finset.filter_singleton]

-- The same data at `ℓ = 7` removes `3`, since `7 ∣ v_3(Δ) = 7`.
example : reducedEllipticLevel 141 (3 ^ 7 * 47) 7 = 47 := by
  rw [reducedEllipticLevel_def, levelLoweringPrimes_eq_count]
  norm_num [Finset.filter_insert, Finset.filter_singleton]

-- `M = 3² · 5`, `Δ = 3⁷ · 5⁷`, `ℓ = 7`: `5` is removed, the exponent two at `3` is kept.
example : reducedEllipticLevel (3 ^ 2 * 5) (3 ^ 7 * 5 ^ 7) 7 = 9 := by
  rw [reducedEllipticLevel_def, levelLoweringPrimes_eq_count]
  norm_num [Finset.filter_insert, Finset.filter_singleton]

-- A conductor exponent above one is never stripped, whatever `Δ` and `ℓ` are.
example {M : ℕ} {Δ : ℤ} {ℓ q : ℕ} (hq : q.Prime) (h : 1 < multiplicity q M) :
    multiplicity q (reducedEllipticLevel M Δ ℓ) = multiplicity q M :=
  multiplicity_reducedEllipticLevel_of_one_lt hq h

-- At `M = 1` nothing is removed, and the sign of `Δ` never matters.
example {Δ : ℤ} {ℓ : ℕ} : reducedEllipticLevel 1 Δ ℓ = 1 := by simp

example : reducedEllipticLevel 141 (-(3 ^ 7 * 47)) 7 = 47 := by
  rw [reducedEllipticLevel_neg, reducedEllipticLevel_def, levelLoweringPrimes_eq_count]
  norm_num [Finset.filter_insert, Finset.filter_singleton]

/-! ### The curve 141a1 -/

/-- The curve 141a1, `y² + y = x³ + x² - 12 x + 2`, as an integral Weierstrass model. -/
abbrev curve141a1 : WeierstrassCurve ℤ := ⟨0, 1, 1, -12, 2⟩

/-- The discriminant of `y² + y = x³ + x² - 12 x + 2` is `3⁷ · 47`. -/
theorem Δ_curve141a1 : curve141a1.Δ = 3 ^ 7 * 47 := by
  simp [Δ, b₂, b₄, b₆, b₈]

/-- The invariant `c₄` of `y² + y = x³ + x² - 12 x + 2` is `592 = 2⁴ · 37`. -/
theorem c₄_curve141a1 : curve141a1.c₄ = 592 := by
  simp [c₄, b₂, b₄]

/-- 141a1 is an elliptic curve over `ℚ`. -/
instance : (curve141a1.baseChange ℚ).IsElliptic := by
  rw [isElliptic_iff, ← algebraMap_Δ_of_baseChange_eq rfl, Δ_curve141a1]
  exact IsUnit.mk0 _ (by norm_num)

/-- The discriminant `3⁷ · 47` and `c₄ = 2⁴ · 37` of 141a1 are coprime. -/
theorem isCoprime_Δ_c₄_curve141a1 : IsCoprime curve141a1.Δ curve141a1.c₄ := by
  rw [Δ_curve141a1, c₄_curve141a1, Int.isCoprime_iff_gcd_eq_one]
  norm_num

/-- `y² + y = x³ + x² - 12 x + 2` is globally minimal: its discriminant and `c₄` are coprime. -/
theorem isGlobalMinimal_curve141a1 : IsGlobalMinimal ℤ (curve141a1.baseChange ℚ) :=
  isGlobalMinimal_baseChange_of_isCoprime curve141a1 isCoprime_Δ_c₄_curve141a1

/-- **The conductor of 141a1 is `141`.** The primes of bad reduction are the primes `3` and `47`
dividing the discriminant, and the reduction is multiplicative at both, since they do not divide
`c₄`. -/
theorem absNorm_algorithmicConductor_curve141a1 :
    Ideal.absNorm (algorithmicConductor ℤ (curve141a1.baseChange ℚ)) = 141 := by
  set N := Ideal.absNorm (algorithmicConductor ℤ (curve141a1.baseChange ℚ))
  have hN : N ≠ 0 := Ideal.absNorm_eq_zero_iff.not.2 (algorithmicConductor_ne_bot ℤ _)
  have hsq : Squarefree N := Nat.squarefree_iff_prime_squarefree.2 fun p hp hpN ↦ by
    obtain ⟨hΔ, hc₄⟩ := (isGlobalMinimal_curve141a1.sq_dvd_absNorm_algorithmicConductor_iff rfl
      hp).1 (by rwa [sq])
    have := Int.isUnit_iff_natAbs_eq.1 (isCoprime_Δ_c₄_curve141a1.isUnit_of_dvd' hΔ hc₄)
    exact hp.one_lt.ne' (by simpa using this)
  have hpf : N.primeFactors = Nat.primeFactors 102789 := by
    ext p
    simp only [Nat.mem_primeFactors, ne_eq, hN, not_false_eq_true, and_true, OfNat.ofNat_ne_zero]
    refine and_congr_right fun hp ↦ ?_
    rw [isGlobalMinimal_curve141a1.dvd_absNorm_algorithmicConductor_iff rfl hp, Δ_curve141a1]
    norm_cast
  rw [← Nat.prod_primeFactors_of_squarefree hsq, hpf]
  norm_num [primeFactors_eq_toFinset]

/-- **At `ℓ = 3` the reduced level of 141a1 is its conductor `141`**: the valuations
`v_3(Δ) = 7` and `v_47(Δ) = 1` are prime to `3`, so no prime is removed. -/
theorem reducedLevel_curve141a1_three : (curve141a1.baseChange ℚ).reducedLevel 3 = 141 := by
  rw [isGlobalMinimal_curve141a1.reducedLevel_eq 3 rfl, absNorm_algorithmicConductor_curve141a1,
    Δ_curve141a1, reducedEllipticLevel_def, levelLoweringPrimes_eq_count]
  norm_num [Finset.filter_insert, Finset.filter_singleton]

/-- **At `ℓ = 7` the reduced level of 141a1 is `47`**: since `7 ∣ v_3(Δ) = 7`, the prime `3` is
removed. -/
theorem reducedLevel_curve141a1_seven : (curve141a1.baseChange ℚ).reducedLevel 7 = 47 := by
  rw [isGlobalMinimal_curve141a1.reducedLevel_eq 7 rfl, absNorm_algorithmicConductor_curve141a1,
    Δ_curve141a1, reducedEllipticLevel_def, levelLoweringPrimes_eq_count]
  norm_num [Finset.filter_insert, Finset.filter_singleton]

end TauCeti.Examples.ReducedLevel
