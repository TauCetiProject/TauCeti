/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.NumberTheory.PrimeFactors.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import TauCeti.Analysis.SpecialFunctions.Pow.EulerFactor
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Basic

/-!
# Uniform bounds for deleted Euler factors

Raising the level of a Dirichlet character deletes finitely many Euler factors. On every
half-plane `Re(s) ≥ δ > 0`, the correction and its reciprocal are bounded by `C N ^ ε`,
for any `ε > 0`, uniformly over the characters, levels and points in that half-plane.
Thus passage between an imprimitive character and its primitive character costs an arbitrarily
small power of the ambient level. This applies in particular to products of primitive quadratic
characters at their common level, including primes dividing both conductors.

The factors are analytic and nonzero on `Re(s) > 0`, so this passage preserves zeros and exact
meromorphic orders there, including the simple pole at `s = 1` for principal characters. At `s = 1`
pointwise L-function comparison requires nonprincipal characters, as in the native continuation API.
On `Re(s) ≥ 1`, taking logarithmic derivatives turns the deleted-factor product into a finite sum
whose norm is bounded by `log N` (including at `s = 1` for principal characters, where both
logarithmic derivatives vanish by totalization).

The exact identity is Mathlib's `DirichletCharacter.LFunction_changeLevel`,
by David Loeffler and Michael Stoll.
For the elementary finite-product estimates see Davenport, *Multiplicative Number Theory*,
the treatment of imprimitive characters and Siegel's theorem.
-/

public section

open Finset Complex Filter
open scoped Topology

namespace DirichletCharacter

private theorem norm_mul_prime_cpow_le {M p : ℕ} (χ : DirichletCharacter ℂ M)
    (hp : p.Prime) {δ : ℝ} (hδ : 0 < δ) {s : ℂ} (hs : δ ≤ s.re) :
    ‖χ p * (p : ℂ) ^ (-s)‖ ≤ (2 : ℝ) ^ (-δ) := by
  rw [norm_mul, norm_natCast_cpow_of_pos hp.pos, neg_re]
  calc
    ‖χ p‖ * (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-s.re) :=
      mul_le_of_le_one_left (by positivity) (χ.norm_le_one p)
    _ ≤ (p : ℝ) ^ (-δ) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_lt.le) (by linarith)
    _ ≤ (2 : ℝ) ^ (-δ) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hp.two_le) (by linarith)

/-- Deleted Euler factors have no zeros in the open right half-plane, for arbitrary complex
Dirichlet characters, including principal ones. -/
theorem prod_one_sub_mul_prime_cpow_ne_zero {M N : ℕ} (χ : DirichletCharacter ℂ M)
    {s : ℂ} (hs : 0 < s.re) :
    (∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-s))) ≠ 0 := by
  refine prod_ne_zero_iff.2 fun p hp ↦ ?_
  have h := (norm_mul_prime_cpow_le χ (Nat.prime_of_mem_primeFactors hp) hs le_rfl).trans_lt
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hs))
  exact sub_ne_zero.mpr fun he ↦ by rw [← he, norm_one] at h; exact (lt_self_iff_false 1).mp h

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
    have hz := norm_mul_prime_cpow_le χ (Nat.prime_of_mem_primeFactors hp) hδ hs
    have hlo : 1 - r ≤ ‖1 - χ p * (p : ℂ) ^ (-s)‖ := by
      have := norm_sub_norm_le (1 : ℂ) (χ p * (p : ℂ) ^ (-s))
      simp only [norm_one] at this
      linarith
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

/-- Raising the level preserves the zeros of the continued L-function in the open right
half-plane. At the possible pole `1`, require the original character to be nonprincipal. -/
@[simp] theorem LFunction_changeLevel_eq_zero_iff {M N : ℕ} [NeZero M] [NeZero N]
    (χ : DirichletCharacter ℂ M) (hMN : M ∣ N) {s : ℂ} (hs : 0 < s.re)
    (h : χ ≠ 1 ∨ s ≠ 1) :
    (changeLevel hMN χ).LFunction s = 0 ↔ χ.LFunction s = 0 := by
  rw [LFunction_changeLevel hMN χ h, mul_eq_zero]
  simp [prod_one_sub_mul_prime_cpow_ne_zero (N := N) χ hs]

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
    simpa [Finset.prod_apply] using prod_one_sub_mul_prime_cpow_ne_zero (N := N) χ hs
  rw [meromorphicOrderAt_congr (LFunction_changeLevel_eventuallyEq_nhdsNE χ hMN s),
    meromorphicOrderAt_mul_of_ne_zero (hPdiff.analyticAt s) hPs]

/-- On the open right half-plane `Re(s) > 0`, the principal Dirichlet `L`-function modulo `N` has
the same meromorphic order as `riemannZeta` (including `-1` at `s = 1`). -/
theorem meromorphicOrderAt_LFunctionTrivChar_eq_meromorphicOrderAt_riemannZeta
    {N : ℕ} [NeZero N] {s : ℂ} (hs : 0 < s.re) :
    meromorphicOrderAt (LFunctionTrivChar N) s = meromorphicOrderAt riemannZeta s := by
  have hch : changeLevel (one_dvd N) (1 : DirichletCharacter ℂ 1) = 1 := map_one _
  have h := meromorphicOrderAt_LFunction_changeLevel (1 : DirichletCharacter ℂ 1) (one_dvd N) hs
  rwa [hch, LFunction_modOne_eq] at h

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
  have hne := prod_one_sub_mul_prime_cpow_ne_zero (N := N) χ (hδ.trans_le hs)
  constructor
  · rw [he, norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hup (norm_nonneg _)
  · have hi : χ.LFunction s = (changeLevel hMN χ).LFunction s *
        (∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-s)))⁻¹ := by
      rw [he, mul_assoc, mul_inv_cancel₀ hne, mul_one]
    rw [hi, norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hinv (norm_nonneg _)

/-- Exact logarithmic-derivative formula for changing level: away from the principal pole
(`s ≠ 1 ∨ ψ ≠ 1`), if neither the deleted Euler factors nor `ψ.LFunction` vanish at `s`, then
`logDeriv (changeLevel hMN ψ).LFunction s - logDeriv ψ.LFunction s` equals the sum of the
logarithmic derivatives of the deleted Euler factors. -/
theorem logDeriv_LFunction_changeLevel_sub {M N : ℕ} [NeZero M] [NeZero N]
    (ψ : DirichletCharacter ℂ M) (hMN : M ∣ N) {s : ℂ} (h : s ≠ 1 ∨ ψ ≠ 1)
    (hPs : (∏ p ∈ N.primeFactors, (1 - ψ p * (p : ℂ) ^ (-s))) ≠ 0)
    (hψ : ψ.LFunction s ≠ 0) :
    logDeriv (changeLevel hMN ψ).LFunction s - logDeriv ψ.LFunction s =
      ∑ p ∈ N.primeFactors, logDeriv (fun z : ℂ ↦ 1 - ψ p * (p : ℂ) ^ (-z)) s := by
  let f (p : ℕ) (z : ℂ) := 1 - ψ p * (p : ℂ) ^ (-z)
  have hdf (p : ℕ) (hp : p ∈ N.primeFactors) : Differentiable ℂ (f p) :=
    Complex.differentiable_one_sub_mul_cpow_neg
      (mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero) _
  have hPs' : (∏ p ∈ N.primeFactors, f p) s ≠ 0 := by simpa [f, Finset.prod_apply] using hPs
  have hnef (p : ℕ) (hp : p ∈ N.primeFactors) : f p s ≠ 0 :=
    prod_ne_zero_iff.mp hPs p hp
  have hPdiff : Differentiable ℂ (∏ p ∈ N.primeFactors, f p) :=
    Differentiable.finsetProd fun p hp ↦ hdf p hp
  rw [(logDeriv_congr_nhds (LFunction_changeLevel_eventuallyEq_nhds ψ hMN h)).eq_of_nhds,
    logDeriv_mul s hPs' hψ (hPdiff s) (ψ.differentiableAt_LFunction s h), add_sub_cancel_right]
  exact logDeriv_prod hnef fun p hp ↦ hdf p hp s

/-- **Deleted Euler factors in the logarithmic derivative under level change.** On the closed
half-plane `1 ≤ re s`, raising the level of a character `ψ` modulo `M` to a multiple `N` changes
`logDeriv` by at most `log N` in norm. At `s = 1` for `ψ = 1`, both `L`-functions fail to be
differentiable so both logarithmic derivatives vanish by Lean's totalization. -/
theorem norm_logDeriv_LFunction_changeLevel_sub_le {M N : ℕ} [NeZero M] [NeZero N]
    (ψ : DirichletCharacter ℂ M) (hMN : M ∣ N) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖logDeriv (changeLevel hMN ψ).LFunction s - logDeriv ψ.LFunction s‖ ≤ Real.log N := by
  by_cases h1 : s = 1 ∧ ψ = 1
  · obtain ⟨rfl, rfl⟩ := h1
    have hch : changeLevel hMN (1 : DirichletCharacter ℂ M) = 1 := map_one _
    have hnd {K : ℕ} [NeZero K] : ¬ DifferentiableAt ℂ (1 : DirichletCharacter ℂ K).LFunction 1 :=
      mt ((1 : DirichletCharacter ℂ K).differentiableAt_LFunction_iff 1).mp (by simp)
    rw [hch, logDeriv_eq_zero_of_not_differentiableAt _ _ hnd,
      logDeriv_eq_zero_of_not_differentiableAt _ _ hnd, sub_self, norm_zero]
    exact Real.log_nonneg (Nat.one_le_cast.mpr NeZero.one_le)
  have h : s ≠ 1 ∨ ψ ≠ 1 := not_and_or.mp h1
  have hPs : (∏ p ∈ N.primeFactors, (1 - ψ p * (p : ℂ) ^ (-s))) ≠ 0 :=
    prod_one_sub_mul_prime_cpow_ne_zero (N := N) ψ (zero_lt_one.trans_le hs)
  rw [logDeriv_LFunction_changeLevel_sub ψ hMN h hPs (LFunction_ne_zero_of_one_le_re ψ h.symm hs)]
  refine (norm_sum_le _ _).trans ((sum_le_sum fun p hp ↦ ?_).trans (Nat.sum_primeFactors_log_le N))
  simpa using Complex.norm_logDeriv_one_sub_mul_ofReal_cpow_neg_le (q := p)
    (mod_cast (Nat.prime_of_mem_primeFactors hp).two_le) (ψ.norm_le_one p) hs

end DirichletCharacter
