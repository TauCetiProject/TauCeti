/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.NumberTheory.DirichletCharacter.Conductor
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Entire
public import TauCeti.NumberTheory.PrimeFactors.Bounds
import TauCeti.Analysis.SpecialFunctions.Pow.EulerFactor

/-!
# Uniform bounds for deleted Euler factors

Raising the level of a Dirichlet character deletes finitely many Euler factors. On every
half-plane `Re(s) ≥ δ > 0`, the correction and its reciprocal are bounded by `C N ^ ε`,
for any `ε > 0`, uniformly over the characters, levels and points in that half-plane.
Thus passage between an imprimitive character and its primitive character costs an arbitrarily
small power of the ambient level. This applies in particular to products of primitive quadratic
characters at their common level, including primes dividing both conductors.

The factors are analytic and nonzero on `Re(s) > 0`, so this passage preserves exact meromorphic
orders there, including the simple pole at `s = 1` for principal characters.
`DirichletCharacter.prod_one_sub_mul_prime_cpow_ne_zero` covers all of `Re(s) ≠ 0`, so the
level change preserves zeros off the imaginary axis. At `s = 1` pointwise L-function comparison
requires nonprincipal characters, as in the native continuation API.

`regularizedLFunction_eq_primitiveCharacter_mul_prod_one_sub_mul_prime_cpow` compares
regularized L-functions with those of the inducing primitive characters at every point.
For principal characters `LFunctionTrivChar₁_eq_mul_prod_one_sub_prime_cpow` gives the
comparison after the pole is removed but before dividing by `s`.
`one_sub_rpow_pow_le_norm_prod_one_sub_mul_prime_cpow` bounds the correction from below
in terms of the number of distinct prime divisors, rather than the size of the new level.

The exact identity is Mathlib's `DirichletCharacter.LFunction_changeLevel`,
by David Loeffler and Michael Stoll. When the levels have the same prime factors,
`DirichletCharacter.LFunction_changeLevel_eq_of_primeFactors_eq` shows that no correction
is needed, away from the possible pole. This comparison is used in
`New.exists_regularL_eq_of_sq_eq_one` in `grh/src/Lib/Analytic/Primes.lean` of
https://github.com/lsernau/grh-lean (rev. `72fead1`).

For the elementary finite-product estimates see Davenport, *Multiplicative Number Theory*,
the treatment of imprimitive characters and Siegel's theorem.
-/

public section

open Finset Complex Filter
open scoped Topology

namespace DirichletCharacter

private theorem norm_mul_natCast_cpow_le {M p : ℕ} (χ : DirichletCharacter ℂ M)
    (hp : 2 ≤ p) {δ : ℝ} (hδ : 0 ≤ δ) {s : ℂ} (hs : δ ≤ s.re) :
    ‖χ p * (p : ℂ) ^ (-s)‖ ≤ (2 : ℝ) ^ (-δ) := by
  have hp₁ : 1 ≤ p := (by decide : 1 ≤ 2).trans hp
  rw [norm_mul, norm_natCast_cpow_of_pos hp₁, neg_re]
  calc
    ‖χ p‖ * (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-s.re) :=
      mul_le_of_le_one_left (by positivity) (χ.norm_le_one p)
    _ ≤ (p : ℝ) ^ (-δ) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp₁) (by linarith)
    _ ≤ (2 : ℝ) ^ (-δ) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hp) (by linarith)

private theorem one_sub_rpow_le_norm_one_sub_mul_natCast_cpow {M p : ℕ}
    (χ : DirichletCharacter ℂ M) (hp : 2 ≤ p) {δ : ℝ} {s : ℂ} (hs : δ ≤ s.re) :
    1 - (2 : ℝ) ^ (-δ) ≤ ‖1 - χ p * (p : ℂ) ^ (-s)‖ := by
  rcases le_or_gt 0 δ with hδ | hδ
  · have h := norm_mul_natCast_cpow_le χ hp hδ hs
    have htri := norm_sub_norm_le (1 : ℂ) (χ p * (p : ℂ) ^ (-s))
    rw [norm_one] at htri
    linarith
  · have h := Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) (neg_nonneg.mpr hδ.le)
    exact (sub_nonpos.mpr h).trans (norm_nonneg _)

/-- Deleted Euler factors have no zeros off the imaginary axis, for arbitrary complex Dirichlet
characters, including principal ones. Each term `χ(p) p⁻ˢ` is `0` or has absolute value
`p^(-Re s)`, which is `< 1` for `Re s > 0` and `> 1` for `Re s < 0`. -/
theorem prod_one_sub_mul_prime_cpow_ne_zero {M N : ℕ} (χ : DirichletCharacter ℂ M)
    {s : ℂ} (hs : s.re ≠ 0) :
    (∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-s))) ≠ 0 := by
  refine prod_ne_zero_iff.2 fun p hp h ↦ ?_
  have hp := Nat.prime_of_mem_primeFactors hp
  have h1 : χ p * (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.1 h).symm
  rcases hs.lt_or_gt with hs | hs
  · by_cases hu : IsUnit (p : ZMod M)
    · have hlt : 1 < ‖χ p * (p : ℂ) ^ (-s)‖ := by
        rw [norm_mul, norm_natCast_cpow_of_pos hp.pos, ← hu.unit_spec, χ.unit_norm_eq_one,
          one_mul, neg_re]
        exact Real.one_lt_rpow (by exact_mod_cast hp.one_lt) (by linarith)
      rw [h1, norm_one] at hlt
      exact lt_irrefl _ hlt
    · rw [χ.map_nonunit hu, zero_mul] at h1
      exact zero_ne_one h1
  · have hlt := (norm_mul_natCast_cpow_le χ hp.two_le hs.le le_rfl).trans_lt
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hs))
    rw [h1, norm_one] at hlt
    exact (lt_self_iff_false 1).mp hlt

/-- On a fixed closed right half-plane, the deleted Euler product and its reciprocal cost at
most an arbitrarily small power of the ambient level. The same constant works for every
character and every level. -/
theorem exists_norm_prod_one_sub_mul_prime_cpow_le_rpow {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ A > 0, ∀ (M N : ℕ), N ≠ 0 → ∀ (χ : DirichletCharacter ℂ M) (s : ℂ), δ ≤ s.re →
      ‖∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-s))‖ ≤ A * (N : ℝ) ^ ε ∧
      ‖(∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-s)))⁻¹‖ ≤ A * (N : ℝ) ^ ε := by
  let r : ℝ := 2 ^ (-δ)
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  let K := max (1 + r) (1 - r)⁻¹
  have hK : 1 ≤ K := le_trans (by linarith) (le_max_left _ _)
  obtain ⟨A, hA, hbound⟩ := TauCeti.exists_pow_card_primeFactors_le_mul_rpow hK hε
  refine ⟨A, hA, fun M N hN χ s hs ↦ ?_⟩
  have hlocal (p : ℕ) (hp : p ∈ N.primeFactors) :
      ‖1 - χ p * (p : ℂ) ^ (-s)‖ ≤ K ∧ ‖(1 - χ p * (p : ℂ) ^ (-s))⁻¹‖ ≤ K := by
    have hp₂ := (Nat.prime_of_mem_primeFactors hp).two_le
    have hz := norm_mul_natCast_cpow_le χ hp₂ hδ.le hs
    have hlo : 1 - r ≤ ‖1 - χ p * (p : ℂ) ^ (-s)‖ :=
      one_sub_rpow_le_norm_one_sub_mul_natCast_cpow χ hp₂ hs
    constructor
    · have hu := norm_sub_le (1 : ℂ) (χ p * (p : ℂ) ^ (-s))
      simp only [norm_one] at hu
      have hu' : ‖1 - χ p * (p : ℂ) ^ (-s)‖ ≤ 1 + r := by linarith
      exact hu'.trans (le_max_left _ _)
    · rw [norm_inv]
      exact (inv_anti₀ (by linarith) hlo).trans (le_max_right _ _)
  constructor
  · rw [norm_prod]
    exact (prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun p hp ↦ (hlocal p hp).1)).trans
      (by simpa using hbound N hN)
  · rw [← prod_inv_distrib, norm_prod]
    exact (prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun p hp ↦ (hlocal p hp).2)).trans
      (by simpa using hbound N hN)

/-- On `Re s ≥ δ ≥ 0`, each deleted Euler factor has norm at least `1 - 2 ^ (-δ)`.
When `δ > 0`, a bound on the number of prime divisors thus bounds the product away from zero,
independently of the level's prime-power exponents. -/
theorem one_sub_rpow_pow_le_norm_prod_one_sub_mul_prime_cpow {M N k : ℕ}
    (χ : DirichletCharacter ℂ M) (hk : N.primeFactors.card ≤ k)
    {δ : ℝ} (hδ : 0 ≤ δ) {s : ℂ} (hs : δ ≤ s.re) :
    (1 - (2 : ℝ) ^ (-δ)) ^ k ≤ ‖∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-s))‖ := by
  have hbase : 0 ≤ 1 - (2 : ℝ) ^ (-δ) := sub_nonneg.mpr <| by
    rw [← Real.rpow_zero (2 : ℝ)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_nonpos.mpr hδ)
  have hbase' : 1 - (2 : ℝ) ^ (-δ) ≤ 1 := sub_le_self _ (by positivity)
  refine (pow_le_pow_of_le_one hbase hbase' hk).trans ?_
  rw [norm_prod, ← prod_const]
  exact prod_le_prod₀ (fun _ _ ↦ hbase) fun p hp ↦
    one_sub_rpow_le_norm_one_sub_mul_natCast_cpow χ (Nat.prime_of_mem_primeFactors hp).two_le hs

/-- After removing the principal pole, the change-of-level formula from level one holds
at every `s`, including `s = 1`. -/
theorem LFunctionTrivChar₁_eq_mul_prod_one_sub_prime_cpow (N : ℕ) [NeZero N] (s : ℂ) :
    LFunctionTrivChar₁ N s =
      LFunctionTrivChar₁ 1 s * ∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-s)) := by
  by_cases hs : s = 1
  · subst s
    simp [LFunctionTrivChar₁, cpow_neg_one]
  · rw [LFunctionTrivChar₁_apply_of_ne_one N hs, LFunctionTrivChar₁_one_apply_of_ne_one hs,
      LFunctionTrivChar_eq_mul_riemannZeta hs]
    ring

/-- At every `s`, the regularized L-function is the regularized L-function of the inducing
primitive character times the deleted Euler factors. This includes `s = 1` for the principal
character. -/
theorem regularizedLFunction_eq_primitiveCharacter_mul_prod_one_sub_mul_prime_cpow
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) :
    χ.regularizedLFunction s = χ.primitiveCharacter.regularizedLFunction s *
      ∏ p ∈ N.primeFactors, (1 - χ.primitiveCharacter p * (p : ℂ) ^ (-s)) := by
  obtain rfl | hχ := eq_or_ne χ 1
  · simp only [primitiveCharacter_one, regularizedLFunction_one_apply, entireLFunction_one]
    have hunit (p : ℕ) : IsUnit (p : ZMod (1 : DirichletCharacter ℂ N).conductor) := by
      rw [conductor_one]
      exact isUnit_of_subsingleton _
    have hlevel (M : ℕ) [NeZero M] (hM : M = 1) :
        LFunctionTrivChar₁ M s = LFunctionTrivChar₁ 1 s := by
      subst M
      rfl
    simp only [MulChar.one_apply (hunit _), one_mul, hlevel _ conductor_one]
    rw [LFunctionTrivChar₁_eq_mul_prod_one_sub_prime_cpow, mul_div_right_comm]
  · have hprim : χ.primitiveCharacter ≠ 1 := mt χ.primitiveCharacter_eq_one_iff.mp hχ
    rw [χ.regularizedLFunction_of_ne_one hχ, regularizedLFunction_of_ne_one _ hprim]
    conv_lhs => rw [← χ.changeLevel_primitiveCharacter]
    exact LFunction_changeLevel _ _ (.inl hprim)

/-- Raising the level multiplies `χ.LFunction` by the deleted Euler factors on a punctured
neighbourhood of every `s : ℂ`. -/
theorem LFunction_changeLevel_eventuallyEq_nhdsNE {M N : ℕ} [NeZero M] [NeZero N]
    (χ : DirichletCharacter ℂ M) (hMN : M ∣ N) (s : ℂ) :
    (changeLevel hMN χ).LFunction =ᶠ[𝓝[≠] s]
      (∏ p ∈ N.primeFactors, fun z : ℂ ↦ 1 - χ p * (p : ℂ) ^ (-z)) * χ.LFunction := by
  filter_upwards [(eventually_cofinite_ne 1).filter_mono (nhdsNE_le_cofinite s)] with z hz
  simp [Finset.prod_apply, LFunction_changeLevel hMN χ (.inr hz), mul_comm]

/-- Away from the principal pole (`s ≠ 1 ∨ χ ≠ 1`), raising the level multiplies `χ.LFunction`
by the deleted Euler factors on a neighbourhood of `s`. -/
theorem LFunction_changeLevel_eventuallyEq_nhds {M N : ℕ} [NeZero M] [NeZero N]
    (χ : DirichletCharacter ℂ M) (hMN : M ∣ N) {s : ℂ} (h : s ≠ 1 ∨ χ ≠ 1) :
    (changeLevel hMN χ).LFunction =ᶠ[𝓝 s]
      (∏ p ∈ N.primeFactors, fun z : ℂ ↦ 1 - χ p * (p : ℂ) ^ (-z)) * χ.LFunction := by
  rcases h with hs | hχ
  · filter_upwards [eventually_ne_nhds hs] with z hz
    simp [Finset.prod_apply, LFunction_changeLevel hMN χ (.inr hz), mul_comm]
  · exact Eventually.of_forall fun z ↦ by
      simp [Finset.prod_apply, LFunction_changeLevel hMN χ (.inl hχ), mul_comm]

/-- Raising the level without adding prime factors leaves the L-function unchanged, away from
`1` in the principal case and everywhere in the nonprincipal case. -/
theorem LFunction_changeLevel_eq_of_primeFactors_eq {M N : ℕ} [NeZero M] [NeZero N]
    (χ : DirichletCharacter ℂ M) (hMN : M ∣ N) (h : N.primeFactors = M.primeFactors)
    {s : ℂ} (hs : χ ≠ 1 ∨ s ≠ 1) : (χ.changeLevel hMN).LFunction s = χ.LFunction s := by
  rw [LFunction_changeLevel hMN χ hs, h, Finset.prod_eq_one, mul_one]
  intro p hp
  simp [χ.map_nonunit (ZMod.not_isUnit_of_mem_primeFactors hp)]

/-- Raising the level preserves the zeros of the continued L-function off the imaginary axis.
At the possible pole `1`, require the original character to be nonprincipal. -/
@[simp] theorem LFunction_changeLevel_eq_zero_iff {M N : ℕ} [NeZero M] [NeZero N]
    (χ : DirichletCharacter ℂ M) (hMN : M ∣ N) {s : ℂ} (hs : s.re ≠ 0)
    (h : χ ≠ 1 ∨ s ≠ 1) :
    (changeLevel hMN χ).LFunction s = 0 ↔ χ.LFunction s = 0 := by
  rw [LFunction_changeLevel hMN χ h, mul_eq_zero]
  simp only [prod_one_sub_mul_prime_cpow_ne_zero (N := N) χ hs, or_false]

/-- A Dirichlet character and its inducing primitive character have the same zeros of the
continued L-function in the open right half-plane. At the possible pole `1`, require the primitive
character to be nonprincipal. -/
theorem LFunction_primitiveCharacter_eq_zero_iff {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 0 < s.re) (h : χ.primitiveCharacter ≠ 1 ∨ s ≠ 1) :
    χ.primitiveCharacter.LFunction s = 0 ↔ χ.LFunction s = 0 := by
  conv_rhs => rw [← χ.changeLevel_primitiveCharacter]
  exact (LFunction_changeLevel_eq_zero_iff _ χ.conductor_dvd_level hs.ne' h).symm

/-- Raising the level preserves the meromorphic order of the continued L-function at every point of
the open right half-plane `Re(s) > 0`, including `s = 1` for principal characters. -/
@[simp] theorem meromorphicOrderAt_LFunction_changeLevel {M N : ℕ} [NeZero M] [NeZero N]
    (χ : DirichletCharacter ℂ M) (hMN : M ∣ N) {s : ℂ} (hs : 0 < s.re) :
    meromorphicOrderAt (changeLevel hMN χ).LFunction s = meromorphicOrderAt χ.LFunction s := by
  have hPdiff : Differentiable ℂ
      (∏ p ∈ N.primeFactors, fun z : ℂ ↦ 1 - χ p * (p : ℂ) ^ (-z)) :=
    Differentiable.finsetProd fun _ hp ↦ Complex.differentiable_one_sub_mul_cpow_neg
      (mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero) _
  have hPs : (∏ p ∈ N.primeFactors, fun z : ℂ ↦ 1 - χ p * (p : ℂ) ^ (-z)) s ≠ 0 := by
    simpa [Finset.prod_apply] using prod_one_sub_mul_prime_cpow_ne_zero (N := N) χ hs.ne'
  rw [meromorphicOrderAt_congr (LFunction_changeLevel_eventuallyEq_nhdsNE χ hMN s),
    meromorphicOrderAt_mul_of_ne_zero (hPdiff.analyticAt s) hPs]

/-- Uniform comparison of the L-functions before and after a level change in either direction.
In particular it applies to the primitive character at its conductor and the original character
at its ambient level. -/
theorem exists_norm_LFunction_changeLevel_le_rpow {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ A > 0, ∀ (M N : ℕ) [NeZero M] [NeZero N] (χ : DirichletCharacter ℂ M)
      (hMN : M ∣ N) (s : ℂ), δ ≤ s.re → (χ ≠ 1 ∨ s ≠ 1) →
      ‖(changeLevel hMN χ).LFunction s‖ ≤ A * (N : ℝ) ^ ε * ‖χ.LFunction s‖ ∧
      ‖χ.LFunction s‖ ≤ A * (N : ℝ) ^ ε * ‖(changeLevel hMN χ).LFunction s‖ := by
  obtain ⟨A, hA, hb⟩ := exists_norm_prod_one_sub_mul_prime_cpow_le_rpow hδ hε
  refine ⟨A, hA, fun M N _ _ χ hMN s hs h ↦ ?_⟩
  obtain ⟨hup, hinv⟩ := hb M N (NeZero.ne N) χ s hs
  have he := LFunction_changeLevel hMN χ h
  have hne := prod_one_sub_mul_prime_cpow_ne_zero (N := N) χ (hδ.trans_le hs).ne'
  constructor
  · rw [he, norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hup (norm_nonneg _)
  · have hi : χ.LFunction s = (changeLevel hMN χ).LFunction s *
        (∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-s)))⁻¹ := by
      rw [he, mul_assoc, mul_inv_cancel₀ hne, mul_one]
    rw [hi, norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hinv (norm_nonneg _)

end DirichletCharacter

namespace TauCeti

open DirichletCharacter

/-- On the open right half-plane `Re(s) > 0`, the principal Dirichlet `L`-function modulo `N` has
the same meromorphic order as `riemannZeta` (including `-1` at `s = 1`). -/
theorem meromorphicOrderAt_LFunctionTrivChar_eq_meromorphicOrderAt_riemannZeta
    {N : ℕ} [NeZero N] {s : ℂ} (hs : 0 < s.re) :
    meromorphicOrderAt (LFunctionTrivChar N) s = meromorphicOrderAt riemannZeta s := by
  have hch : changeLevel (one_dvd N) (1 : DirichletCharacter ℂ 1) = 1 := map_one _
  have h := meromorphicOrderAt_LFunction_changeLevel (1 : DirichletCharacter ℂ 1) (one_dvd N) hs
  rwa [hch, LFunction_modOne_eq] at h

end TauCeti
