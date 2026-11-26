/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.Quadratic.LegendreTwist
public import TauCeti.NumberTheory.LSeries.Quadratic.ThetaTail

/-!
# Theta tails of Legendre twists

For primes `d ≡ 7 mod 8`, quadratic reciprocity puts the prime in the numerator of the
Jacobi symbols in the joint theta tail. This compares sums of tails of Legendre twists
with sums over all numerators in the same window, to which character mean-square estimates
apply. For a fixed character the twists all have the opposite parity, so the same Gaussian
weight applies throughout the window.

The use of reciprocity in this comparison follows `New.zero_density_quadTwist` in
`grh/src/Lib/Analytic/QuadraticTwist.lean` of [lsernau/grh-lean](https://github.com/lsernau/grh-lean)
(commit `72fead102f663d5c7a407964a13dc0cf9d977207`).
-/

public section

open scoped Nat

namespace DirichletCharacter

open TauCeti

/-- For a prime `d ≡ 7 mod 8`, the joint theta tail of a Legendre twist is the joint theta
tail with Jacobi numerator `-d`. The identity includes the Möbius-weighted term. -/
theorem quadraticTwistGaussianThetaTailIntegral_legendreTwist {q d : ℕ} [Fact d.Prime]
    (χ : DirichletCharacter ℂ q) (hd : d % 8 = 7) (j : Fin 2) (T : ℝ) :
    quadraticTwistGaussianThetaTailIntegral j (fun n ↦ χ.legendreTwist d n) T =
      quadraticTwistGaussianThetaTailIntegral j
        (fun n ↦ χ n * jacobiSym (-(d : ℤ)) (ordCompl[2] n)) T :=
  quadraticTwistGaussianThetaTailIntegral_congr
    (fun n ↦ χ.legendreTwist_apply_natCast_eq_mul_jacobiSym d hd n.ne_zero) T

/-- Over any finite set of primes congruent to `7` modulo `8` in `[1, X]`, the sum of the
Legendre-twist tails is bounded above by the sum of the Jacobi tails over all numerators in
`[1, X]`. -/
theorem sum_quadraticTwistGaussianThetaTailIntegral_legendreTwist_le {q : ℕ}
    (χ : DirichletCharacter ℂ q) (j : Fin 2) (T : ℝ) {S : Finset ℕ} {X : ℕ}
    (hle : ∀ d ∈ S, d ≤ X) (hprime : ∀ d ∈ S, d.Prime) (hmod : ∀ d ∈ S, d % 8 = 7) :
    (∑ d : S,
      letI : Fact (Nat.Prime (d : ℕ)) := ⟨hprime d d.property⟩
      quadraticTwistGaussianThetaTailIntegral j (fun n ↦ χ.legendreTwist d n) T) ≤
    ∑ d ∈ Finset.Icc 1 X,
      quadraticTwistGaussianThetaTailIntegral j
        (fun n ↦ χ n * jacobiSym (-(d : ℤ)) (ordCompl[2] n)) T := by
  calc
    _ = ∑ d : S, quadraticTwistGaussianThetaTailIntegral j
          (fun n ↦ χ n * jacobiSym (-(d : ℤ)) (ordCompl[2] n)) T := by
        refine Finset.sum_congr rfl fun d _ ↦ ?_
        let : Fact (Nat.Prime (d : ℕ)) := ⟨hprime d d.property⟩
        exact χ.quadraticTwistGaussianThetaTailIntegral_legendreTwist (hmod d d.property) j T
    _ ≤ _ := by
        rw [Finset.sum_coe_sort S (fun d ↦ quadraticTwistGaussianThetaTailIntegral j
          (fun n ↦ χ n * jacobiSym (-(d : ℤ)) (ordCompl[2] n)) T)]
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (fun d hd ↦ Finset.mem_Icc.mpr ⟨(hprime d hd).pos, hle d hd⟩)
          (fun _ _ _ ↦ quadraticTwistGaussianThetaTailIntegral_nonneg T)

end DirichletCharacter
