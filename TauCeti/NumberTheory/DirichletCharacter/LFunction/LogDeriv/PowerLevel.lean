/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.ZeroFreeRegion
import TauCeti.NumberTheory.DirichletCharacter.LFunction.SamePrimeFactors
import TauCeti.NumberTheory.DirichletCharacter.Quadratic.PowerLevel
import Mathlib.Analysis.Asymptotics.Ring
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-!
# Uniform zero-free bounds for powers of a fixed modulus

The near-one lower bound needed in the Dirichlet zero-free region can be made uniform across
powers of a fixed modulus: the characters of order dividing two have the same regularized
L-functions as a finite set of characters at the cube of the base modulus (or at level one
for exponent zero). On a disk of radius `1 / X` the resulting logarithmic derivative bound is
at most both `X` and `2 * ((A + 1) * log X) ^ 25` for moduli at most `X ^ A`. This is the local
bound used when detecting primes in logarithmic windows in the class of `1`.

The argument follows the reduction to finitely many characters in lsernau/grh-lean (commit
`72fead1`), `Lib/Analytic/Primes.lean` (`New.eventually_norm_logDeriv_entireL_le_near_one`),
using the cube instead of the square so that the base modulus need not be divisible by `4`.
-/

public section

open Filter Real Topology

namespace DirichletCharacter

/-- For sufficiently small `r`, every character of order dividing two at a power of the
fixed modulus `m` has regularized L-function of norm at least `r` within distance `r` of `1`. -/
theorem eventually_le_norm_regularizedLFunction_pow (m : ℕ) [NeZero m] :
    ∀ᶠ r : ℝ in 𝓝 0, ∀ (k : ℕ) (χ : DirichletCharacter ℂ (m ^ k)), χ ^ 2 = 1 →
      ∀ z : ℂ, ‖z - 1‖ ≤ r → r ≤ ‖χ.regularizedLFunction z‖ := by
  have hcube : ∀ᶠ r : ℝ in 𝓝 0, ∀ ψ : DirichletCharacter ℂ (m ^ 3),
      ∀ z : ℂ, ‖z - 1‖ ≤ r → r ≤ ‖ψ.regularizedLFunction z‖ :=
    eventually_all.mpr fun ψ ↦ ψ.eventually_le_norm_regularizedLFunction
  filter_upwards [hcube, (1 : DirichletCharacter ℂ 1).eventually_le_norm_regularizedLFunction]
    with r hr hone k χ hχ z hz
  rcases eq_or_ne k 0 with rfl | hk
  · have : Subsingleton (DirichletCharacter ℂ (m ^ 0)) := by simpa using
      (inferInstance : Subsingleton (DirichletCharacter ℂ 1))
    rw [Subsingleton.elim χ 1]
    exact hone z hz
  have hprimes : (m ^ k).primeFactors = (m ^ 3).primeFactors := by
    simp [Nat.primeFactors_pow, hk]
  by_cases h : k ≤ 3
  · have hd : m ^ k ∣ m ^ 3 := pow_dvd_pow_of_dvd_of_le (dvd_refl m) h
    rw [← χ.regularizedLFunction_changeLevel_of_primeFactors_eq hd hprimes.symm]
    exact hr _ z hz
  · have h₈ (h₂ : 2 ∣ m ^ k) : 8 ∣ m ^ 3 :=
      pow_dvd_pow_of_dvd_of_le (Nat.prime_two.dvd_of_dvd_pow h₂) le_rfl
    obtain ⟨hd, ψ, hψ⟩ := χ.factorsThrough_pow_of_sq_eq_one hχ (by decide : 0 < 3)
      (by omega : 3 ≤ k) (fun h₄ ↦ (by decide : 4 ∣ 8).trans (h₈ ((by decide : 2 ∣ 4).trans h₄)))
      (fun h ↦ h₈ ((by decide : 2 ∣ 8).trans h))
    rw [hψ, ψ.regularizedLFunction_changeLevel_of_primeFactors_eq hd hprimes]
    exact hr _ z hz

private theorem eventually_const_mul_log_pow_le (C c : ℝ) (n : ℕ) :
    ∀ᶠ X : ℝ in atTop, C * (c * log X) ^ n ≤ X := by
  have h := (isLittleO_pow_log_id_atTop (n := n)).const_mul_left (C * c ^ n)
  filter_upwards [h.eventuallyLE, eventually_ge_atTop (0 : ℝ)] with X hX hX₀
  calc
    C * (c * log X) ^ n = (C * c ^ n) * log X ^ n := by rw [mul_pow, mul_assoc]
    _ ≤ ‖(C * c ^ n) * log X ^ n‖ := le_abs_self _
    _ ≤ X := hX.trans_eq (Real.norm_of_nonneg hX₀)

/-- For sufficiently large `X`, uniformly over levels `m ^ k ≤ X ^ A` and all their characters,
the pole-removed L-function is nonzero on the closed disk of radius `1 / X` about `1`.
The logarithmic derivative there has norm at most both `X` and `2 * ((A + 1) * log X) ^ 25`. -/
theorem eventually_norm_logDeriv_entireLFunction_le_near_one (m : ℕ) [NeZero m] (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ (k : ℕ), (m : ℝ) ^ k ≤ X ^ A →
      ∀ (χ : DirichletCharacter ℂ (m ^ k)) (s : ℂ), ‖s - 1‖ ≤ 1 / X →
        χ.entireLFunction s ≠ 0 ∧
          ‖logDeriv χ.entireLFunction s‖ ≤ min X (2 * (((A + 1 : ℕ) : ℝ) * log X) ^ 25) := by
  let l (X : ℝ) : ℝ := (A + 1 : ℕ) * log X
  have htop : Tendsto l atTop atTop := tendsto_log_atTop.const_mul_atTop (by positivity)
  have hsmall : Tendsto (fun X ↦ 1 / l X) atTop (𝓝 0) := tendsto_const_nhds.div_atTop htop
  have hpow : ∀ᶠ X : ℝ in atTop, 2 * l X ^ 25 ≤ X := eventually_const_mul_log_pow_le 2 _ 25
  have hnear := hsmall.eventually (eventually_le_norm_regularizedLFunction_pow m)
  filter_upwards [htop.eventually_ge_atTop (10 ^ 10), hpow, eventually_ge_atTop (1 : ℝ), hnear]
    with X hl hp hX hn k hk χ s hs
  have hl₁ : 1 ≤ l X := by linarith
  have hXL : (l X) ^ 25 ≤ X := by linarith [pow_nonneg (zero_le_one.trans hl₁) 25]
  have he : exp (l X) = X ^ (A + 1) := by
    dsimp [l]
    rw [exp_natCast_mul, exp_log (by positivity)]
  have hmod : (↑(m ^ k) : ℝ) ≤ exp (l X) := by
    rw [Nat.cast_pow, he]
    exact hk.trans (pow_le_pow_right₀ hX (Nat.le_succ _))
  have hreal : 1 - 1 / l X ^ 25 ≤ s.re := by
    have hdist : |s.re - 1| ≤ ‖s - 1‖ := by simpa using Complex.abs_re_le_norm (s - 1)
    have := one_div_le_one_div_of_le (by positivity : 0 < l X ^ 25) hXL
    linarith [(abs_le.mp hdist).1]
  have hnorm : ‖s‖ ≤ exp (l X) := by
    have h₁ := one_div_le_one_div_of_le zero_lt_one hX
    have h₂ := norm_le_norm_sub_add s (1 : ℂ)
    rw [norm_one] at h₂
    linarith [add_one_le_exp (l X)]
  obtain ⟨hne, hb⟩ := χ.entireLFunction_ne_zero_and_norm_logDeriv_le hl hmod (hn k χ) hreal hnorm
  exact ⟨hne, le_min (hb.trans hp) hb⟩

end DirichletCharacter
