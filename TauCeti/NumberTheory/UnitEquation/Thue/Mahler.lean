/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Homogenize
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.SmoothNumbers
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation

import TauCeti.Algebra.Field.LinearFractional
import TauCeti.Algebra.Polynomial.Homogenize
import TauCeti.NumberTheory.Height.Basic
import TauCeti.NumberTheory.Height.NumberField
import TauCeti.NumberTheory.Height.Rat
import TauCeti.NumberTheory.NumberField.Ideal.DvdAway

/-!
# Thue–Mahler equations via unit equations in finitely generated groups

Let `g ∈ ℤ[X]` have three distinct roots `θ₀, θ₁, θ₂` in the ring of integers of a number
field `K`, let `G` be its homogenization, `m ≠ 0` an integer and `S` a finite set of primes. The
**Thue–Mahler equation** asks for the coprime integers `x, y` with

  `G(x, y) = m p₁ ^ z₁ ⋯ pₛ ^ zₛ`,  `pᵢ ∈ S`, `zᵢ ≥ 0`,

that is, `G(x, y) = m k` with `k ∈ Nat.factoredNumbers S`. This file reduces it to finitely many
unit equations `a X + b Y = 1` in a finitely generated subgroup `Γ` of `Kˣ`, following Evertse's
reduction of Thue equations to unit equations, with the units of `𝓞 K` replaced by `Γ`.

Let `P` be a finite set of primes of `𝓞 K` containing every prime above `S`. Each linear factor
`x - θᵢ y` divides `G(x, y)`, so away from `P` it divides `m`. Suppose that every nonzero
`β ∈ 𝓞 K` dividing `m` away from `P` is `μ γ` with `μ` in a set `M` and `γ ∈ Γ`; for finite `M`
and finitely generated `Γ` such a pair is supplied by
`TauCeti.NumberField.exists_finset_subgroup_forall_eq_mul`. Then `x - θᵢ y = μᵢ γᵢ`, and Siegel's
identity (`TauCeti.siegel_identity`) shows that `(γ₀ / γ₂, γ₁ / γ₂) ∈ Γ²` solves

  `(θ₁ - θ₂) / (θ₁ - θ₀) · μ₀ / μ₂ · X + (θ₂ - θ₀) / (θ₁ - θ₀) · μ₁ / μ₂ · Y = 1`.

Conversely `t = μ₀ / μ₂ · γ₀ / γ₂ = (x - θ₀ y) / (x - θ₂ y)` determines `x / y`, and for coprime
`x, y` the height of `x / y` is `log max(|x|, |y|)`. Hence:

* a bound `B` for the heights of the solutions `X` of these unit equations bounds the solutions
  of the Thue–Mahler equation explicitly,
  `max(|x|, |y|) ≤ exp ((2 (2 A + B) + h(θ₀) + h(θ₂)) / [K : ℚ] + 2 log 2)`, where `A` bounds the
  heights of the elements of `M` and the heights are taken over `K`;
* if these finitely many unit equations have finitely many solutions in `Γ²`, the Thue–Mahler
  equation has finitely many coprime solutions; in particular this holds as soon as every unit
  equation `a X + b Y = 1` with `a, b ≠ 0` has finitely many solutions in each finitely generated
  subgroup of `Kˣ`, which is Győry's theorem.

## Main results

* `TauCeti.NumberField.exists_mul_add_mul_eq_one_of_forall_intValuation_le`: if each `x - θᵢ y`
  divides `m` away from `P`, the quotients `γᵢ / γ₂` solve one of the unit equations above.
* `TauCeti.NumberField.exists_mul_add_mul_eq_one_of_eval_homogenize_eq_mul`: the same for an
  integer solution of the Thue–Mahler equation.
* `TauCeti.NumberField.max_abs_le_of_eval_homogenize_eq_mul`: the explicit bound above.
* `TauCeti.NumberField.finite_setOf_isCoprime_eval_homogenize_eq_mul`: finiteness of the coprime
  solutions, given finiteness of the solutions of the finitely many unit equations.
* `TauCeti.NumberField.finite_setOf_isCoprime_eval_homogenize_eq_mul_of_forall_finite`:
  finiteness of the coprime solutions, given finiteness of the solutions of all unit equations in
  finitely generated subgroups of `Kˣ`.

## References

* [J.-H. Evertse, *Diophantine Approximation*, lecture notes, Leiden/Mastermath, 2019],
  Chapter 5, Theorems 5.13 and 5.18.
* N. Tzanakis and B. M. M. de Weger, *How to explicitly solve a Thue–Mahler equation*,
  Compositio Math. **84** (1992), 223–288, §§1, 5–6.
-/

public section

open IsDedekindDomain Module NumberField Height
open scoped NumberField Polynomial

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **Reduction to unit equations in a finitely generated group** (Evertse, proofs of
Theorems 5.13 and 5.18). Let `P` be a set of primes of `𝓞 K`, `m ∈ 𝓞 K`, and suppose that every
nonzero `β ∈ 𝓞 K` dividing `m` away from `P` is `μ * γ` with `μ ∈ M` and `γ ∈ Γ`. Let
`θ : Fin 3 → 𝓞 K` with `θ 1 ≠ θ 0` and `x, y ∈ 𝓞 K` such that each `x - θ i * y` is nonzero and
divides `m` away from `P`. Then `x - θ i * y = μ i * γ i` with nonzero `μ i ∈ M` and `γ i ∈ Γ`,
and `γ 0 / γ 2`, `γ 1 / γ 2` solve the unit equation `a X + b Y = 1` with
`a = (θ 1 - θ 2) / (θ 1 - θ 0) · μ 0 / μ 2` and `b = (θ 2 - θ 0) / (θ 1 - θ 0) · μ 1 / μ 2`. -/
theorem exists_mul_add_mul_eq_one_of_forall_intValuation_le
    {P : Set (HeightOneSpectrum (𝓞 K))} {m : 𝓞 K} {M : Set (𝓞 K)} {Γ : Subgroup Kˣ}
    (hMΓ : ∀ β : 𝓞 K, β ≠ 0 → (∀ v ∉ P, v.intValuation m ≤ v.intValuation β) →
      ∃ μ ∈ M, ∃ γ ∈ Γ, (β : K) = μ * (γ : K))
    {θ : Fin 3 → 𝓞 K} (hθ : θ 1 ≠ θ 0) {x y : 𝓞 K} (hxy : ∀ i, x - θ i * y ≠ 0)
    (hv : ∀ i, ∀ v ∉ P, v.intValuation m ≤ v.intValuation (x - θ i * y)) :
    ∃ μ : Fin 3 → 𝓞 K, (∀ i, μ i ∈ M ∧ μ i ≠ 0) ∧ ∃ γ : Fin 3 → Kˣ, (∀ i, γ i ∈ Γ) ∧
      (∀ i, (x : K) - θ i * y = μ i * γ i) ∧
      ((θ 1 : K) - θ 2) / ((θ 1 : K) - θ 0) * ((μ 0 : K) / μ 2) * ((γ 0 / γ 2 : Kˣ) : K) +
        ((θ 2 : K) - θ 0) / ((θ 1 : K) - θ 0) * ((μ 1 : K) / μ 2) *
          ((γ 1 / γ 2 : Kˣ) : K) = 1 := by
  choose μ hμ γ hγ hβ using fun i ↦ hMΓ _ (hxy i) (hv i)
  have hxyK (i : Fin 3) : (x : K) - θ i * y ≠ 0 := by
    simpa [← RingOfIntegers.coe_eq_zero_iff] using hxy i
  have hfac (i : Fin 3) : (x : K) - θ i * y = μ i * γ i := by simpa using hβ i
  have hμ0 (i : Fin 3) : μ i ≠ 0 := by
    rintro h0
    exact hxyK i (by simp [hfac i, h0])
  refine ⟨μ, fun i ↦ ⟨hμ i, hμ0 i⟩, γ, hγ, hfac, ?_⟩
  have h := siegel_identity (fun h ↦ hθ (RingOfIntegers.coe_injective h)) (hxyK 2)
  rw [hfac 0, hfac 1, hfac 2] at h
  rw [Units.val_div_eq_div_val, Units.val_div_eq_div_val, ← h]
  ring

/-- **Thue–Mahler equations reduce to unit equations** (Evertse, proofs of Theorems 5.13 and
5.18). Let `g ∈ ℤ[X]` have roots `θ 0, θ 1, θ 2 ∈ 𝓞 K` with `θ 1 ≠ θ 0`, let `n ≥ natDegree g`
and let `G` be the homogenization of `g` of degree `n`. Let `S` be a finite set of natural
numbers and `P` a set of primes of `𝓞 K` containing every prime above a prime of `S`, let
`m ≠ 0`, and suppose that every nonzero `β ∈ 𝓞 K` dividing `m` away from `P` is `μ * γ` with
`μ ∈ M` and `γ ∈ Γ`. If `x, y ∈ ℤ` satisfy `G(x, y) = m * k` with `k` a product of primes of `S`,
then `x - θ i * y = μ i * γ i` with nonzero `μ i ∈ M` and `γ i ∈ Γ`, and `γ 0 / γ 2`,
`γ 1 / γ 2` solve the unit equation `a X + b Y = 1` with
`a = (θ 1 - θ 2) / (θ 1 - θ 0) · μ 0 / μ 2` and `b = (θ 2 - θ 0) / (θ 1 - θ 0) · μ 1 / μ 2`. -/
theorem exists_mul_add_mul_eq_one_of_eval_homogenize_eq_mul
    {S : Finset ℕ} {P : Set (HeightOneSpectrum (𝓞 K))}
    (hP : ∀ v ∉ P, ∀ p ∈ S, p.Prime → (p : 𝓞 K) ∉ v.asIdeal) {m : ℤ} (hm : m ≠ 0)
    {M : Set (𝓞 K)} {Γ : Subgroup Kˣ}
    (hMΓ : ∀ β : 𝓞 K, β ≠ 0 → (∀ v ∉ P, v.intValuation (m : 𝓞 K) ≤ v.intValuation β) →
      ∃ μ ∈ M, ∃ γ ∈ Γ, (β : K) = μ * (γ : K))
    {g : ℤ[X]} {n : ℕ} (hn : g.natDegree ≤ n) {θ : Fin 3 → 𝓞 K}
    (hg : ∀ i, Polynomial.aeval (θ i) g = 0) (hθ : θ 1 ≠ θ 0) {x y : ℤ} {k : ℕ}
    (hk : k ∈ Nat.factoredNumbers S) (hxy : MvPolynomial.eval ![x, y] (g.homogenize n) = m * k) :
    ∃ μ : Fin 3 → 𝓞 K, (∀ i, μ i ∈ M ∧ μ i ≠ 0) ∧ ∃ γ : Fin 3 → Kˣ, (∀ i, γ i ∈ Γ) ∧
      (∀ i, (x : K) - θ i * y = μ i * γ i) ∧
      ((θ 1 : K) - θ 2) / ((θ 1 : K) - θ 0) * ((μ 0 : K) / μ 2) * ((γ 0 / γ 2 : Kˣ) : K) +
        ((θ 2 : K) - θ 0) / ((θ 1 : K) - θ 0) * ((μ 1 : K) / μ 2) *
          ((γ 1 / γ 2 : Kˣ) : K) = 1 := by
  -- In `𝓞 K`, `m * k = G(x, y)` is divisible by each linear factor `x - θ i * y`.
  have hdvd (i : Fin 3) : (x : 𝓞 K) - θ i * y ∣ (m : 𝓞 K) * k := by
    have hm' : ((m * k : ℤ) : 𝓞 K) = MvPolynomial.eval ![(x : 𝓞 K), y]
        ((g.map (algebraMap ℤ (𝓞 K))).homogenize n) := by
      have hv : algebraMap ℤ (𝓞 K) ∘ ![x, y] = ![(x : 𝓞 K), y] := by
        ext j
        fin_cases j <;> simp
      rw [← hxy, ← eq_intCast (algebraMap ℤ (𝓞 K)), MvPolynomial.map_eval, hv,
        Polynomial.homogenize_map]
    have h := Polynomial.sub_mul_dvd_eval_homogenize
      (by rw [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def, hg i])
      (Polynomial.natDegree_map_le.trans hn) ![(x : 𝓞 K), y]
    rw [← hm'] at h
    simpa using h
  have hk0 : k ≠ 0 := (Nat.mem_factoredNumbers.mp hk).1
  have hmk : (m : 𝓞 K) * k ≠ 0 := mul_ne_zero (Int.cast_ne_zero.mpr hm) (Nat.cast_ne_zero.mpr hk0)
  -- Away from `P`, `k` is a unit: none of its prime factors lies in `v`.
  have hkv (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ P) : v.intValuation (k : 𝓞 K) = 1 := by
    rw [HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl, Ideal.mem_primeCompl_iff,
      ← Nat.prod_primeFactorsList hk0, ← Multiset.prod_coe, Nat.cast_multiset_prod,
      v.isPrime.multiset_prod_mem_iff_exists_mem]
    rintro ⟨q, hq, hqv⟩
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hq
    rw [Multiset.mem_coe] at hp
    exact hP v hv p ((Nat.mem_factoredNumbers.mp hk).2 p hp) (Nat.prime_of_mem_primeFactorsList hp)
      hqv
  refine exists_mul_add_mul_eq_one_of_forall_intValuation_le hMΓ hθ
    (fun i h0 ↦ hmk (zero_dvd_iff.mp (h0 ▸ hdvd i))) fun i v hv ↦ ?_
  obtain ⟨c, hc⟩ := hdvd i
  calc v.intValuation (m : 𝓞 K) = v.intValuation ((m : 𝓞 K) * k) := by
        rw [map_mul, hkv v hv, mul_one]
    _ = v.intValuation ((x : 𝓞 K) - θ i * y) * v.intValuation c := by rw [hc, map_mul]
    _ ≤ v.intValuation ((x : 𝓞 K) - θ i * y) :=
        mul_le_of_le_one_right' (v.intValuation_le_one c)

/-- **An explicit bound for the solutions of a Thue–Mahler equation** (Evertse, proofs of
Theorems 5.13 and 5.18). In the setting of `exists_mul_add_mul_eq_one_of_eval_homogenize_eq_mul`,
assume also `θ 0 ≠ θ 2`, that every element of `M` has logarithmic height at most `A`, and that
every solution `(X, Y) ∈ Γ²` of each unit equation `a X + b Y = 1` given there, with `μ` a triple
of nonzero elements of `M`, has `h(X) ≤ B`. Then every coprime solution of the Thue–Mahler
equation `G(x, y) = m * k` satisfies

`max(|x|, |y|) ≤ exp ((2 (2 A + B) + h(θ 0) + h(θ 2)) / [K : ℚ] + 2 log 2)`,

where `h` is the logarithmic height over `K`. -/
theorem max_abs_le_of_eval_homogenize_eq_mul
    {S : Finset ℕ} {P : Set (HeightOneSpectrum (𝓞 K))}
    (hP : ∀ v ∉ P, ∀ p ∈ S, p.Prime → (p : 𝓞 K) ∉ v.asIdeal) {m : ℤ} (hm : m ≠ 0)
    {M : Set (𝓞 K)} {Γ : Subgroup Kˣ}
    (hMΓ : ∀ β : 𝓞 K, β ≠ 0 → (∀ v ∉ P, v.intValuation (m : 𝓞 K) ≤ v.intValuation β) →
      ∃ μ ∈ M, ∃ γ ∈ Γ, (β : K) = μ * (γ : K))
    {g : ℤ[X]} {n : ℕ} (hn : g.natDegree ≤ n) {θ : Fin 3 → 𝓞 K}
    (hg : ∀ i, Polynomial.aeval (θ i) g = 0) (hθ₁₀ : θ 1 ≠ θ 0) (hθ₀₂ : θ 0 ≠ θ 2) {A B : ℝ}
    (hA : ∀ μ ∈ M, logHeight₁ (μ : K) ≤ A)
    (hB : ∀ μ : Fin 3 → 𝓞 K, (∀ i, μ i ∈ M ∧ μ i ≠ 0) → ∀ X ∈ Γ, ∀ Y ∈ Γ,
      ((θ 1 : K) - θ 2) / ((θ 1 : K) - θ 0) * ((μ 0 : K) / μ 2) * (X : K) +
        ((θ 2 : K) - θ 0) / ((θ 1 : K) - θ 0) * ((μ 1 : K) / μ 2) * (Y : K) = 1 →
      logHeight₁ (X : K) ≤ B)
    {x y : ℤ} (hcop : IsCoprime x y) {k : ℕ} (hk : k ∈ Nat.factoredNumbers S)
    (hxy : MvPolynomial.eval ![x, y] (g.homogenize n) = m * k) :
    max |(x : ℝ)| |(y : ℝ)| ≤ Real.exp ((2 * (2 * A + B) + logHeight₁ (θ 0 : K) +
      logHeight₁ (θ 2 : K)) / finrank ℚ K + 2 * Real.log 2) := by
  obtain ⟨μ, hμ, γ, hγ, hfac, hunit⟩ :=
    exists_mul_add_mul_eq_one_of_eval_homogenize_eq_mul hP hm hMΓ hn hg hθ₁₀ hk hxy
  set D : ℝ := (finrank ℚ K : ℝ)
  have hD : 0 < D := Nat.cast_pos.mpr finrank_pos
  -- The quotient `X = γ 0 / γ 2` solves a unit equation, so `h(X) ≤ B`.
  have hX : logHeight₁ ((γ 0 / γ 2 : Kˣ) : K) ≤ B :=
    hB μ hμ _ (div_mem (hγ 0) (hγ 2)) _ (div_mem (hγ 1) (hγ 2)) hunit
  have hμA (i : Fin 3) : logHeight₁ (μ i : K) ≤ A := hA _ (hμ i).1
  have hA0 : 0 ≤ A := (zero_le_logHeight₁ _).trans (hμA 0)
  have hB0 : 0 ≤ B := (zero_le_logHeight₁ _).trans hX
  have hθ0 := zero_le_logHeight₁ (θ 0 : K)
  have hθ2 := zero_le_logHeight₁ (θ 2 : K)
  have hlog2 := Real.log_pos one_lt_two
  rcases eq_or_ne y 0 with rfl | hy
  · -- Coprimality forces `x = ±1`.
    obtain hx | hx := Int.isUnit_iff.mp (isCoprime_zero_right.mp hcop) <;>
    · subst hx
      norm_num
      positivity
  -- With `t = (μ 0 / μ 2) X = (x - θ 0 y) / (x - θ 2 y)`, `t` determines `x / y`.
  set t : K := (μ 0 : K) / μ 2 * ((γ 0 / γ 2 : Kˣ) : K)
  have hμ2 : (μ 2 : K) ≠ 0 := by simpa using (hμ 2).2
  have ht : t * ((x : K) - θ 2 * y) = x - θ 0 * y := by
    rw [hfac 2, hfac 0]
    simp only [t, Units.val_div_eq_div_val]
    field_simp [Units.ne_zero (γ 2)]
  have hK := logHeight₁_div_le_of_mul_sub_mul_eq
    (fun h ↦ hθ₀₂ (RingOfIntegers.coe_injective h)) (Int.cast_ne_zero.mpr hy) ht
  rw [totalWeight_eq_finrank] at hK
  have hth : logHeight₁ t ≤ 2 * A + B := by
    linarith [logHeight₁_mul_le ((μ 0 : K) / μ 2) ((γ 0 / γ 2 : Kˣ) : K),
      logHeight₁_div_le (μ 0 : K) (μ 2), hμA 0, hμA 2]
  -- Heights over `K` are `D` times heights over `ℚ`.
  have hQ : logHeight₁ ((x : K) / y) = D * logHeight₁ ((x : ℚ) / y) := by
    rw [← logHeight₁_algebraMap (L := K)]
    simp
  rw [hQ] at hK
  have hlog : logHeight₁ ((x : ℚ) / y) ≤
      (2 * (2 * A + B) + logHeight₁ (θ 0 : K) + logHeight₁ (θ 2 : K)) / D + 2 * Real.log 2 := by
    rw [div_add' _ _ _ hD.ne', le_div_iff₀ hD]
    nlinarith
  rw [← Rat.mulHeight₁_intCast_div_of_isCoprime hcop, ← Real.exp_log (mulHeight₁_pos _),
    ← logHeight₁_eq_log_mulHeight₁]
  exact Real.exp_le_exp.mpr hlog

/-- **Finiteness of the solutions of a Thue–Mahler equation, given finiteness for unit
equations** (Evertse, proofs of Theorems 5.13 and 5.18). In the setting of
`exists_mul_add_mul_eq_one_of_eval_homogenize_eq_mul`, assume also `θ 0 ≠ θ 2` and that `M` is
finite. If each of the finitely many unit equations `a X + b Y = 1` given there, with `μ` a triple
of nonzero elements of `M`, has finitely many solutions `(X, Y) ∈ Γ²`, then the Thue–Mahler
equation `G(x, y) = m * k`, with `k` a product of primes of `S`, has only finitely many coprime
integer solutions `(x, y)`. -/
theorem finite_setOf_isCoprime_eval_homogenize_eq_mul
    {S : Finset ℕ} {P : Set (HeightOneSpectrum (𝓞 K))}
    (hP : ∀ v ∉ P, ∀ p ∈ S, p.Prime → (p : 𝓞 K) ∉ v.asIdeal) {m : ℤ} (hm : m ≠ 0)
    {M : Set (𝓞 K)} (hM : M.Finite) {Γ : Subgroup Kˣ}
    (hMΓ : ∀ β : 𝓞 K, β ≠ 0 → (∀ v ∉ P, v.intValuation (m : 𝓞 K) ≤ v.intValuation β) →
      ∃ μ ∈ M, ∃ γ ∈ Γ, (β : K) = μ * (γ : K))
    {g : ℤ[X]} {n : ℕ} (hn : g.natDegree ≤ n) {θ : Fin 3 → 𝓞 K}
    (hg : ∀ i, Polynomial.aeval (θ i) g = 0) (hθ₁₀ : θ 1 ≠ θ 0) (hθ₀₂ : θ 0 ≠ θ 2)
    (hfin : ∀ μ : Fin 3 → 𝓞 K, (∀ i, μ i ∈ M ∧ μ i ≠ 0) →
      {XY : Kˣ × Kˣ | XY.1 ∈ Γ ∧ XY.2 ∈ Γ ∧
        ((θ 1 : K) - θ 2) / ((θ 1 : K) - θ 0) * ((μ 0 : K) / μ 2) * (XY.1 : K) +
          ((θ 2 : K) - θ 0) / ((θ 1 : K) - θ 0) * ((μ 1 : K) / μ 2) * (XY.2 : K) = 1}.Finite) :
    {xy : ℤ × ℤ | IsCoprime xy.1 xy.2 ∧
      ∃ k ∈ Nat.factoredNumbers S,
        MvPolynomial.eval ![xy.1, xy.2] (g.homogenize n) = m * k}.Finite := by
  -- The heights of the elements of `M` are bounded by some `A`.
  obtain ⟨A, hA⟩ := (hM.image fun μ : 𝓞 K ↦ logHeight₁ (μ : K)).bddAbove
  -- The finitely many unit equations have finitely many solutions in total, so the heights of
  -- their solutions are bounded by some `B`.
  set T : Set (Fin 3 → 𝓞 K) := {μ | ∀ i, μ i ∈ M ∧ μ i ≠ 0}
  have hT : T.Finite :=
    (Set.Finite.pi' fun _ ↦ hM).subset fun μ hμ i ↦ (hμ i).1
  obtain ⟨B, hB⟩ := ((hT.biUnion fun μ hμ ↦ hfin μ hμ).image
    fun XY : Kˣ × Kˣ ↦ logHeight₁ (XY.1 : K)).bddAbove
  have hbound := fun x y hcop k hk hxy ↦ max_abs_le_of_eval_homogenize_eq_mul hP hm hMΓ hn hg
    hθ₁₀ hθ₀₂ (A := A) (B := B) (fun μ hμ ↦ hA ⟨μ, hμ, rfl⟩)
    (fun μ hμ X hX Y hY h ↦ hB ⟨(X, Y), Set.mem_biUnion (x := μ) hμ ⟨hX, hY, h⟩, rfl⟩)
    (x := x) (y := y) hcop (k := k) hk hxy
  -- Every solution lies in a box of integer points.
  set R : ℤ := ⌈Real.exp ((2 * (2 * A + B) + logHeight₁ (θ 0 : K) +
    logHeight₁ (θ 2 : K)) / finrank ℚ K + 2 * Real.log 2)⌉
  refine ((Set.finite_Icc (-R) R).prod (Set.finite_Icc (-R) R)).subset ?_
  rintro ⟨x, y⟩ ⟨hcop, k, hk, hxy⟩
  have h := (hbound x y hcop k hk hxy).trans (Int.le_ceil _)
  have hx : |x| ≤ R := by exact_mod_cast (le_max_left _ _).trans h
  have hy : |y| ≤ R := by exact_mod_cast (le_max_right _ _).trans h
  exact ⟨abs_le.mp hx, abs_le.mp hy⟩

/-- **Finiteness of the solutions of a Thue–Mahler equation from Győry's theorem.** Suppose that
for every finitely generated subgroup `Γ` of `Kˣ` and all `a, b ≠ 0` the unit equation
`a X + b Y = 1` has finitely many solutions in `Γ²`. Let `g ∈ ℤ[X]` have three distinct roots
`θ 0, θ 1, θ 2 ∈ 𝓞 K`, let `n ≥ natDegree g`, `G` the homogenization of `g` of degree `n`,
`S` a finite set of natural numbers and `m ≠ 0`. Then the Thue–Mahler equation `G(x, y) = m * k`,
with `k` a product of primes of `S`, has only finitely many coprime integer solutions `(x, y)`. -/
theorem finite_setOf_isCoprime_eval_homogenize_eq_mul_of_forall_finite
    (hfin : ∀ Γ : Subgroup Kˣ, Γ.FG → ∀ a b : K, a ≠ 0 → b ≠ 0 →
      {XY : Kˣ × Kˣ | XY.1 ∈ Γ ∧ XY.2 ∈ Γ ∧ a * XY.1 + b * XY.2 = 1}.Finite)
    {g : ℤ[X]} {n : ℕ} (hn : g.natDegree ≤ n) {θ : Fin 3 → 𝓞 K}
    (hg : ∀ i, Polynomial.aeval (θ i) g = 0) (hθ : Function.Injective θ) (S : Finset ℕ)
    {m : ℤ} (hm : m ≠ 0) :
    {xy : ℤ × ℤ | IsCoprime xy.1 xy.2 ∧
      ∃ k ∈ Nat.factoredNumbers S,
        MvPolynomial.eval ![xy.1, xy.2] (g.homogenize n) = m * k}.Finite := by
  classical
  -- `P` is the finite set of primes of `𝓞 K` above the primes of `S`.
  set N : ℕ := ∏ p ∈ S with p.Prime, p
  have hN : (N : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.mpr
    (Finset.prod_ne_zero_iff.mpr fun p hp ↦ (Finset.mem_filter.mp hp).2.ne_zero)
  have hPfin := Ideal.finite_factors (R := 𝓞 K) (I := Ideal.span {(N : 𝓞 K)})
    (by rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])
  set P : Finset (HeightOneSpectrum (𝓞 K)) := hPfin.toFinset
  have hP : ∀ v ∉ (P : Set (HeightOneSpectrum (𝓞 K))), ∀ p ∈ S, p.Prime →
      (p : 𝓞 K) ∉ v.asIdeal := by
    intro v hv p hp hpp hpv
    refine hv (hPfin.mem_toFinset.mpr ?_)
    rw [Set.mem_ofPred_eq, Ideal.dvd_span_singleton]
    exact Ideal.mem_of_dvd _
      (Nat.cast_dvd_cast (Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨hp, hpp⟩))) hpv
  obtain ⟨M, Γ, hΓ, -, hMΓ⟩ := exists_finset_subgroup_forall_eq_mul P (m := (m : 𝓞 K))
    (Int.cast_ne_zero.mpr hm)
  have hθK {i j : Fin 3} (hij : i ≠ j) : (θ i : K) - θ j ≠ 0 :=
    sub_ne_zero.mpr fun h ↦ hij (hθ (RingOfIntegers.coe_injective h))
  refine finite_setOf_isCoprime_eval_homogenize_eq_mul hP hm M.finite_toSet
    (fun β hβ hv ↦ hMΓ β hβ fun v hvP ↦ hv v hvP) hn hg (hθ.ne (by decide)) (hθ.ne (by decide))
    fun μ hμ ↦ hfin Γ hΓ _ _ ?_ ?_
  all_goals
    have hμK (i : Fin 3) : (μ i : K) ≠ 0 := by simpa using (hμ i).2
    simp only [ne_eq, mul_eq_zero, div_eq_zero_iff, not_or]
    exact ⟨⟨hθK (by decide), hθK (by decide)⟩, hμK _, hμK _⟩

end TauCeti.NumberField
