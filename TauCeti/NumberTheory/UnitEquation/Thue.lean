/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Field.LinearFractional
public import TauCeti.Algebra.Polynomial.Homogenize
public import TauCeti.NumberTheory.NumberField.Units.Balanced
public import Mathlib.NumberTheory.Height.NumberField

import TauCeti.NumberTheory.Height.Basic
import TauCeti.NumberTheory.Height.House
import TauCeti.NumberTheory.Height.NumberField
import TauCeti.NumberTheory.Height.Rat
import TauCeti.NumberTheory.NumberField.Units.Height
import TauCeti.NumberTheory.NumberField.Units.House

/-!
# Thue equations via unit equations

Let `K` be a number field, let `u` be a family of `rank K` units of maximal rank, and let
`θ₀, θ₁, θ₂, x, y, m ∈ 𝓞 K` with `θ₁ ≠ θ₀`, `m ≠ 0` and each `x - θᵢ y` dividing `m`. By the
balancing argument (`TauCeti.NumberField.Units.exists_mem_boundedDivisors_of_dvd`), each factor
is `x - θᵢ y = εᵢ μᵢ` with `εᵢ` a unit and `μᵢ` in the finite set `boundedDivisors u m`. Siegel's
identity

  `(θ₁ - θ₂) (x - θ₀ y) + (θ₂ - θ₀) (x - θ₁ y) + (θ₀ - θ₁) (x - θ₂ y) = 0`

then shows that the pair of units `(ε₀ / ε₂, ε₁ / ε₂)` solves the unit equation `a X + b Y = 1`
with coefficients

  `a = (θ₁ - θ₂) / (θ₁ - θ₀) · μ₀ / μ₂`,  `b = (θ₂ - θ₀) / (θ₁ - θ₀) · μ₁ / μ₂`.

As `μ` ranges over the finite set `(boundedDivisors u m)³`, only finitely many such unit
equations occur. Conversely, if `y ≠ 0` and `θ₀ ≠ θ₂`, the quotient
`t = (x - θ₀ y) / (x - θ₂ y) = (μ₀ / μ₂) (ε₀ / ε₂)` determines `x / y = (θ₀ - t θ₂) / (1 - t)`.
The field identities behind both directions, `TauCeti.siegel_identity` and
`TauCeti.div_eq_sub_mul_div_one_sub_of_mul_sub_mul_eq`, are in
`TauCeti/Algebra/Field/LinearFractional.lean`.

This applies to the Thue equation `G(x, y) = m` with `x, y, m ∈ ℤ`, `m ≠ 0`, and `G` the
homogenization of a polynomial `g ∈ ℤ[X]` with three distinct roots `θ₀, θ₁, θ₂ ∈ 𝓞 K`: each
`x - θᵢ y` divides `G(x, y)` in `𝓞 K`. An exponent bound for the solutions of unit equations,
such as `TauCeti.NumberField.Units.max_abs_le_of_mul_add_mul_eq_one`, then bounds the units
`ε₀ / ε₂` and `ε₁ / ε₂`, and hence the ratio `x / y`.

Explicitly, take `u = fundSystem K` and `c₁ = rank K * ∑ j, ‖log u j‖`, and suppose that the
exponents of `ε₀ / ε₂ = ζ ∏ j, u j ^ e j` (with `ζ` a root of unity) satisfy `|e j| ≤ B` for every
solution of each of these unit equations. The height of `ε₀ / ε₂` is then at most
`[K : ℚ] B ∑ j, log (house (u j))`, each `μᵢ` has house at most `exp c₁ · |m|` and so height at
most `[K : ℚ] (c₁ + log |m|)`, and the formula for `x / y` bounds its height over `ℚ`:

  `h(x / y) ≤ 4 (c₁ + log |m|) + 2 B ∑ j, log (house (u j)) + log⁺ (house θ₀) +
    log⁺ (house θ₂) + 2 log 2`.

Since `gcd(x, y) ^ deg G` divides `m`, this bounds `max(|x|, |y|)` by
`|m| ^ (1 / deg G)` times the exponential of the right-hand side, so the solutions of the Thue
equation lie in an explicit finite box.

## Main results

* `TauCeti.NumberField.Units.exists_mem_boundedDivisors_mul_add_mul_eq_one`: if each
  `x - θᵢ y` divides `m ≠ 0`, the factors are units times bounded divisors of `m`, and the
  unit quotients solve one of finitely many unit equations.
* `TauCeti.NumberField.Units.exists_mem_boundedDivisors_mul_add_mul_eq_one_of_eval_homogenize_eq`:
  the same conclusion for an integer solution of a Thue equation `G(x, y) = m`.
* `TauCeti.NumberField.Units.logHeight₁_div_le_of_eval_homogenize_eq`: the height bound for
  `x / y` above, given the exponent bound `B` for the unit equations.
* `TauCeti.NumberField.Units.max_abs_le_of_eval_homogenize_eq`: the resulting bound for
  `max(|x|, |y|)`.

## References

* [J.-H. Evertse, *Diophantine Approximation*, lecture notes, Leiden/Mastermath, 2019],
  Chapter 5, Theorem 5.13 and its proof, pp. 96–98.
-/

public section

open Module NumberField NumberField.Units
open scoped NumberField Polynomial

namespace TauCeti

namespace NumberField.Units

variable {K : Type*} [Field K] [NumberField K]

/-- **Reduction to unit equations** (Evertse, proof of Theorem 5.13). Let `u` be a family of
units of maximal rank, `θ : Fin 3 → 𝓞 K` with `θ 1 ≠ θ 0`, and `x, y, m ∈ 𝓞 K` with `m ≠ 0`
such that each `x - θ i * y` divides `m`. Then `x - θ i * y = ε i * μ i` with `μ i` in the
finite set `boundedDivisors u m` and `ε i` units, and the units `ε 0 / ε 2` and `ε 1 / ε 2` solve
the unit equation `a X + b Y = 1` with `a = (θ 1 - θ 2) / (θ 1 - θ 0) · μ 0 / μ 2` and
`b = (θ 2 - θ 0) / (θ 1 - θ 0) · μ 1 / μ 2`. -/
theorem exists_mem_boundedDivisors_mul_add_mul_eq_one {u : Fin (rank K) → (𝓞 K)ˣ}
    (hu : IsMaxRank u) {θ : Fin 3 → 𝓞 K} (hθ : θ 1 ≠ θ 0) {x y m : 𝓞 K} (hm : m ≠ 0)
    (hdvd : ∀ i, x - θ i * y ∣ m) :
    ∃ μ : Fin 3 → 𝓞 K, (∀ i, μ i ∈ boundedDivisors u m) ∧ ∃ ε : Fin 3 → (𝓞 K)ˣ,
      (∀ i, x - θ i * y = ε i * μ i) ∧
      ((θ 1 : K) - θ 2) / ((θ 1 : K) - θ 0) * ((μ 0 : K) / μ 2) * ((ε 0 / ε 2 : (𝓞 K)ˣ) : K) +
        ((θ 2 : K) - θ 0) / ((θ 1 : K) - θ 0) * ((μ 1 : K) / μ 2) *
          ((ε 1 / ε 2 : (𝓞 K)ˣ) : K) = 1 := by
  choose μ hμ ε hε using fun i ↦ exists_mem_boundedDivisors_of_dvd hu hm (hdvd i)
  refine ⟨μ, hμ, ε, hε, ?_⟩
  -- `μ 2` divides `x - θ 2 * y`, a nonzero divisor of `m`.
  have hμ2 : (μ 2 : K) ≠ 0 := by
    rw [ne_eq, RingOfIntegers.coe_eq_zero_iff]
    rintro h0
    have := hdvd 2
    rw [hε 2, h0, mul_zero, zero_dvd_iff] at this
    exact hm this
  have hθ' : (θ 1 : K) ≠ θ 0 := fun h ↦ hθ (RingOfIntegers.coe_injective h)
  have hε' (i : Fin 3) : (x : K) - θ i * y = ε i * μ i := by
    simpa using congrArg (algebraMap (𝓞 K) K) (hε i)
  have hdiv (i : Fin 3) : ((ε i / ε 2 : (𝓞 K)ˣ) : K) = ε i / ε 2 := by
    rw [div_eq_mul_inv, coe_mul, map_units_inv (algebraMap (𝓞 K) K), div_eq_mul_inv]
  have h := siegel_identity (θ₂ := (θ 2 : K)) (x := (x : K)) (y := y) hθ'
    (by rw [hε' 2]; exact mul_ne_zero (coe_ne_zero (ε 2)) hμ2)
  rw [hε' 0, hε' 1, hε' 2] at h
  rw [hdiv, hdiv, ← h]
  ring

/-- **Thue equations reduce to unit equations** (Evertse, Theorem 5.13). Let `g ∈ ℤ[X]` have
roots `θ 0, θ 1, θ 2 ∈ 𝓞 K` with `θ 1 ≠ θ 0`, let `n ≥ natDegree g`, and let `G` be the
homogenization of `g` of degree `n`. If `x, y ∈ ℤ` solve the Thue equation `G(x, y) = m` with
`m ≠ 0`, then `x - θ i * y = ε i * μ i` with `μ i` in the finite set `boundedDivisors u m` and
`ε i` units, and `ε 0 / ε 2`, `ε 1 / ε 2` solve the unit equation `a X + b Y = 1` with
`a = (θ 1 - θ 2) / (θ 1 - θ 0) · μ 0 / μ 2` and `b = (θ 2 - θ 0) / (θ 1 - θ 0) · μ 1 / μ 2`. -/
theorem exists_mem_boundedDivisors_mul_add_mul_eq_one_of_eval_homogenize_eq
    {u : Fin (rank K) → (𝓞 K)ˣ} (hu : IsMaxRank u) {g : ℤ[X]} {n : ℕ} (hn : g.natDegree ≤ n)
    {θ : Fin 3 → 𝓞 K} (hg : ∀ i, Polynomial.aeval (θ i) g = 0) (hθ : θ 1 ≠ θ 0) {m : ℤ}
    (hm : m ≠ 0) {x y : ℤ} (hxy : MvPolynomial.eval ![x, y] (g.homogenize n) = m) :
    ∃ μ : Fin 3 → 𝓞 K, (∀ i, μ i ∈ boundedDivisors u (m : 𝓞 K)) ∧ ∃ ε : Fin 3 → (𝓞 K)ˣ,
      (∀ i, (x : 𝓞 K) - θ i * y = ε i * μ i) ∧
      ((θ 1 : K) - θ 2) / ((θ 1 : K) - θ 0) * ((μ 0 : K) / μ 2) * ((ε 0 / ε 2 : (𝓞 K)ˣ) : K) +
        ((θ 2 : K) - θ 0) / ((θ 1 : K) - θ 0) * ((μ 1 : K) / μ 2) *
          ((ε 1 / ε 2 : (𝓞 K)ˣ) : K) = 1 := by
  refine exists_mem_boundedDivisors_mul_add_mul_eq_one hu hθ (Int.cast_ne_zero.2 hm) fun i ↦ ?_
  -- In `𝓞 K`, `m = G(x, y)` is the value of the homogenization of `g` mapped to `𝓞 K`.
  have hm' : ((m : ℤ) : 𝓞 K) = MvPolynomial.eval ![(x : 𝓞 K), y]
      ((g.map (algebraMap ℤ (𝓞 K))).homogenize n) := by
    have hv : algebraMap ℤ (𝓞 K) ∘ ![x, y] = ![(x : 𝓞 K), y] := by
      ext j
      fin_cases j <;> simp
    rw [← hxy, ← eq_intCast (algebraMap ℤ (𝓞 K)), MvPolynomial.map_eval, hv,
      Polynomial.homogenize_map]
  rw [hm']
  exact Polynomial.sub_mul_dvd_eval_homogenize
    (by rw [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def, hg i])
    (Polynomial.natDegree_map_le.trans hn) _

section Height

open Height
open scoped Real

/-- A unit `ζ ∏ j, u j ^ e j` with `ζ` a root of unity and every `|e j| ≤ B` has relative height
at most `[K : ℚ] * B * ∑ j, log (house (u j))`. -/
private theorem logHeight₁_mul_prod_zpow_le {u : Fin (rank K) → (𝓞 K)ˣ} {ζ : (𝓞 K)ˣ}
    (hζ : ζ ∈ torsion K) {e : Fin (rank K) → ℤ} {B : ℝ} (he : ∀ j, |(e j : ℝ)| ≤ B) :
    logHeight₁ ((ζ * ∏ j, u j ^ e j : (𝓞 K)ˣ) : K) ≤
      finrank ℚ K * (B * ∑ j, Real.log (NumberField.house (u j : K))) := by
  have hcoe : ((ζ * ∏ j, u j ^ e j : (𝓞 K)ˣ) : K) = (ζ : K) * ∏ j, (u j : K) ^ e j := by
    rw [coe_mul]
    congr 1
    simp only [← coe_zpow]
    exact map_prod ((Units.coeHom K).comp (Units.map (algebraMap (𝓞 K) K).toMonoidHom)) _ _
  have hζ0 : logHeight₁ (ζ : K) = 0 := (logHeight₁_eq_zero_iff ζ).mpr hζ
  -- Each `u j` is an algebraic integer of house at least `1`.
  have hu (j : Fin (rank K)) :
      logHeight₁ (u j : K) ≤ finrank ℚ K * Real.log (NumberField.house (u j : K)) := by
    have h := logHeight₁_le_finrank_mul_posLog_house (u j : 𝓞 K).isIntegral_coe
    rwa [Real.posLog_eq_log (by
      rw [abs_of_nonneg (NumberField.house_nonneg _)]
      exact Units.one_le_house _)] at h
  calc logHeight₁ ((ζ * ∏ j, u j ^ e j : (𝓞 K)ˣ) : K)
      ≤ logHeight₁ (ζ : K) + ∑ j, logHeight₁ ((u j : K) ^ e j) := by
        rw [hcoe]
        exact (logHeight₁_mul_le _ _).trans (add_le_add le_rfl (logHeight₁_prod_le _ _))
    _ = ∑ j, |(e j : ℝ)| * logHeight₁ (u j : K) := by
        rw [hζ0, zero_add]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [logHeight₁_zpow, Nat.cast_natAbs, Int.cast_abs]
    _ ≤ ∑ j, B * (finrank ℚ K * Real.log (NumberField.house (u j : K))) :=
        Finset.sum_le_sum fun j _ ↦ mul_le_mul (he j) (hu j) (zero_le_logHeight₁ _)
          ((abs_nonneg _).trans (he j))
    _ = finrank ℚ K * (B * ∑ j, Real.log (NumberField.house (u j : K))) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        ring

open scoped Classical in
/-- A divisor `μ` of a nonzero integer `m` in `boundedDivisors u m` has relative height at most
`[K : ℚ] * (c₁ + log |m|)`, where `c₁ = rank K * ∑ j, ‖log u j‖`: its house is at most
`exp c₁ * |N(m)| ^ (1 / [K : ℚ]) = exp c₁ * |m|`. -/
private theorem logHeight₁_le_of_mem_boundedDivisors {u : Fin (rank K) → (𝓞 K)ˣ} {m : ℤ}
    (hm : m ≠ 0) {μ : 𝓞 K} (hμ : μ ∈ boundedDivisors u (m : 𝓞 K)) :
    logHeight₁ (μ : K) ≤ finrank ℚ K *
      (rank K * ∑ j, ‖logEmbedding K (Additive.ofMul (u j))‖ + Real.log |(m : ℝ)|) := by
  set c₁ : ℝ := rank K * ∑ j, ‖logEmbedding K (Additive.ofMul (u j))‖
  have hc₁ : 0 ≤ c₁ := by positivity
  have hm1 : 1 ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm
  have hnorm : |(Algebra.norm ℚ ((m : 𝓞 K) : K) : ℝ)| ^ (1 / (finrank ℚ K : ℝ)) = |(m : ℝ)| := by
    rw [show ((m : 𝓞 K) : K) = algebraMap ℚ K m by simp, Algebra.norm_algebraMap, Rat.cast_pow,
      abs_pow, Rat.cast_intCast, one_div, Real.pow_rpow_inv_natCast (abs_nonneg _) finrank_pos.ne']
  have hhouse := (mem_boundedDivisors.mp hμ).2
  rw [hnorm] at hhouse
  have h1 : 1 ≤ Real.exp c₁ * |(m : ℝ)| :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_exp hc₁) hm1
  refine (logHeight₁_le_finrank_mul_posLog_house μ.isIntegral_coe).trans
    (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  rw [← Real.log_exp c₁, ← Real.log_mul (Real.exp_pos _).ne' (by positivity),
    ← Real.posLog_eq_log (by rwa [abs_of_nonneg (by positivity)])]
  exact Real.posLog_le_posLog (by linarith [NumberField.house_nonneg (μ : K)]) hhouse

/-- If `t (x - θ₂ y) = x - θ₀ y` with `θ₀ ≠ θ₂` and `y ≠ 0`, so that
`x / y = (θ₀ - t θ₂) / (1 - t)`, then
`h(x / y) ≤ 2 h(t) + h(θ₀) + h(θ₂) + 2 [K : ℚ] log 2` for the relative height `h` over `K`. -/
private theorem logHeight₁_div_le_of_mul_sub_mul_eq {θ₀ θ₂ x y t : K} (hθ : θ₀ ≠ θ₂)
    (hy : y ≠ 0) (ht : t * (x - θ₂ * y) = x - θ₀ * y) :
    logHeight₁ (x / y) ≤ 2 * logHeight₁ t + logHeight₁ θ₀ + logHeight₁ θ₂ +
      2 * (finrank ℚ K * Real.log 2) := by
  have hw : ((totalWeight K : ℕ) : ℝ) = finrank ℚ K := by rw [totalWeight_eq_finrank]
  have h1t := logHeight₁_sub_le (1 : K) t
  have h0t := logHeight₁_sub_le θ₀ (t * θ₂)
  rw [hw, logHeight₁_one] at h1t
  rw [hw] at h0t
  rw [div_eq_sub_mul_div_one_sub_of_mul_sub_mul_eq hθ hy ht]
  linarith [logHeight₁_div_le (θ₀ - t * θ₂) (1 - t), logHeight₁_mul_le t θ₂]

open scoped Classical in
/-- **A height bound for the solutions of a Thue equation** (Evertse, Theorem 5.13). Let
`g ∈ ℤ[X]` have roots `θ 0, θ 1, θ 2 ∈ 𝓞 K` with `θ 1 ≠ θ 0` and `θ 0 ≠ θ 2`, let
`n ≥ natDegree g`, let `G` be the homogenization of `g` of degree `n`, and let `m ≠ 0`. Write
`u = fundSystem K` and `c₁ = rank K * ∑ j, ‖log u j‖`. Suppose that every solution `(X, Y)` of
each of the finitely many unit equations `a X + b Y = 1` given by
`exists_mem_boundedDivisors_mul_add_mul_eq_one_of_eval_homogenize_eq`, with
`μ ∈ (boundedDivisors u m)³`, has `X = ζ ∏ j, u j ^ e j` with all `|e j| ≤ B`. Then every
integer solution of `G(x, y) = m` satisfies

`h(x / y) ≤ 4 (c₁ + log |m|) + 2 B ∑ j, log (house (u j)) + log⁺ (house (θ 0)) +
  log⁺ (house (θ 2)) + 2 log 2`,

where `h` is the logarithmic height over `ℚ`. An exponent bound for the unit equations, such as
`TauCeti.NumberField.Units.max_abs_le_of_mul_add_mul_eq_one` with a constant from Baker's theory,
supplies `B`. -/
theorem logHeight₁_div_le_of_eval_homogenize_eq {g : ℤ[X]} {n : ℕ} (hn : g.natDegree ≤ n)
    {θ : Fin 3 → 𝓞 K} (hg : ∀ i, Polynomial.aeval (θ i) g = 0) (hθ₁₀ : θ 1 ≠ θ 0)
    (hθ₀₂ : θ 0 ≠ θ 2) {m : ℤ} (hm : m ≠ 0) {B : ℝ}
    (hB : ∀ μ : Fin 3 → 𝓞 K, (∀ i, μ i ∈ boundedDivisors (fundSystem K) (m : 𝓞 K)) →
      ∀ X Y : (𝓞 K)ˣ,
        ((θ 1 : K) - θ 2) / ((θ 1 : K) - θ 0) * ((μ 0 : K) / μ 2) * (X : K) +
          ((θ 2 : K) - θ 0) / ((θ 1 : K) - θ 0) * ((μ 1 : K) / μ 2) * (Y : K) = 1 →
        ∀ ζ ∈ torsion K, ∀ e : Fin (rank K) → ℤ, X = ζ * ∏ j, fundSystem K j ^ e j →
          ∀ j, |(e j : ℝ)| ≤ B)
    {x y : ℤ} (hxy : MvPolynomial.eval ![x, y] (g.homogenize n) = m) :
    logHeight₁ ((x : ℚ) / y) ≤
      4 * (rank K * ∑ j, ‖logEmbedding K (Additive.ofMul (fundSystem K j))‖ +
          Real.log |(m : ℝ)|) +
        2 * B * ∑ j, Real.log (NumberField.house (fundSystem K j : K)) +
        log⁺ (NumberField.house (θ 0 : K)) + log⁺ (NumberField.house (θ 2 : K)) +
        2 * Real.log 2 := by
  set c₁ := rank K * ∑ j, ‖logEmbedding K (Additive.ofMul (fundSystem K j))‖
  set L := ∑ j, Real.log (NumberField.house (fundSystem K j : K))
  set D : ℝ := (finrank ℚ K : ℝ)
  have hD : 0 < D := Nat.cast_pos.mpr finrank_pos
  obtain ⟨μ, hμ, ε, hε, hunit⟩ :=
    exists_mem_boundedDivisors_mul_add_mul_eq_one_of_eval_homogenize_eq (isMaxRank_fundSystem K)
      hn hg hθ₁₀ hm hxy
  -- The unit `ε 0 / ε 2` solves a unit equation, so its exponents are bounded by `B`.
  obtain ⟨⟨ζ, e⟩, hζe, -⟩ := exist_unique_eq_mul_prod K (ε 0 / ε 2)
  have hX : logHeight₁ ((ε 0 / ε 2 : (𝓞 K)ˣ) : K) ≤ D * (B * L) := by
    rw [hζe]
    exact logHeight₁_mul_prod_zpow_le ζ.2 (hB μ hμ _ _ hunit ζ ζ.2 e hζe)
  have hBL : 0 ≤ B * L := (mul_nonneg_iff_of_pos_left hD).mp ((zero_le_logHeight₁ _).trans hX)
  have hc₁ : 0 ≤ c₁ := by positivity
  have hlogm : 0 ≤ Real.log |(m : ℝ)| := Real.log_nonneg (by exact_mod_cast Int.one_le_abs hm)
  have hθ₀ := Real.posLog_nonneg (x := NumberField.house (θ 0 : K))
  have hθ₂ := Real.posLog_nonneg (x := NumberField.house (θ 2 : K))
  have hlog2 := Real.log_pos one_lt_two
  rcases eq_or_ne y 0 with rfl | hy
  · rw [Int.cast_zero, div_zero, logHeight₁_zero]
    nlinarith
  -- With `t = (μ 0 / μ 2) (ε 0 / ε 2) = (x - θ 0 y) / (x - θ 2 y)`, `t` determines `x / y`.
  have hεK (i : Fin 3) : (x : K) - θ i * y = ε i * μ i := by
    simpa using congrArg (algebraMap (𝓞 K) K) (hε i)
  have hμ2 : (μ 2 : K) ≠ 0 := by
    rw [ne_eq, RingOfIntegers.coe_eq_zero_iff]
    rintro h0
    have := (mem_boundedDivisors.mp (hμ 2)).1
    rw [h0, zero_dvd_iff, Int.cast_eq_zero] at this
    exact hm this
  set t : K := (μ 0 : K) / μ 2 * ((ε 0 / ε 2 : (𝓞 K)ˣ) : K)
  have ht : t * ((x : K) - θ 2 * y) = x - θ 0 * y := by
    have hdiv : ((ε 0 / ε 2 : (𝓞 K)ˣ) : K) = ε 0 / ε 2 := by
      rw [div_eq_mul_inv, coe_mul, map_units_inv (algebraMap (𝓞 K) K), div_eq_mul_inv]
    have ht' : t = (μ 0 : K) / μ 2 * ((ε 0 : K) / ε 2) := by rw [← hdiv]
    rw [hεK 2, hεK 0, ht']
    field_simp [coe_ne_zero (ε 2)]
  have hK := logHeight₁_div_le_of_mul_sub_mul_eq
    (fun h ↦ hθ₀₂ (RingOfIntegers.coe_injective h)) (Int.cast_ne_zero.mpr hy) ht
  -- Bound the heights over `K` of `t`, `θ 0` and `θ 2`.
  have hth : logHeight₁ t ≤ 2 * (D * (c₁ + Real.log |(m : ℝ)|)) + D * (B * L) := by
    linarith [logHeight₁_mul_le ((μ 0 : K) / μ 2) ((ε 0 / ε 2 : (𝓞 K)ˣ) : K),
      logHeight₁_div_le (μ 0 : K) (μ 2), logHeight₁_le_of_mem_boundedDivisors hm (hμ 0),
      logHeight₁_le_of_mem_boundedDivisors hm (hμ 2)]
  have hθh (i : Fin 3) : logHeight₁ (θ i : K) ≤ D * log⁺ (NumberField.house (θ i : K)) :=
    logHeight₁_le_finrank_mul_posLog_house (θ i).isIntegral_coe
  -- Heights over `K` are `D` times heights over `ℚ`.
  have hQ : logHeight₁ ((x : K) / y) = D * logHeight₁ ((x : ℚ) / y) := by
    rw [← logHeight₁_algebraMap (L := K)]
    simp
  rw [hQ] at hK
  refine le_of_mul_le_mul_left (hK.trans ?_) hD
  linear_combination 2 * hth + hθh 0 + hθh 2

open scoped Classical in
/-- **A bound for the solutions of a Thue equation** (Evertse, Theorem 5.13). Under the
hypotheses of `logHeight₁_div_le_of_eval_homogenize_eq`, every integer solution of
`G(x, y) = m` satisfies `max(|x|, |y|) ≤ |m| ^ (1 / n) * exp h_T`, where `h_T` is the height
bound for `x / y` given there. Hence the solutions lie in an explicit finite box. -/
theorem max_abs_le_of_eval_homogenize_eq {g : ℤ[X]} {n : ℕ} (hn : g.natDegree ≤ n)
    {θ : Fin 3 → 𝓞 K} (hg : ∀ i, Polynomial.aeval (θ i) g = 0) (hθ₁₀ : θ 1 ≠ θ 0)
    (hθ₀₂ : θ 0 ≠ θ 2) {m : ℤ} (hm : m ≠ 0) {B : ℝ}
    (hB : ∀ μ : Fin 3 → 𝓞 K, (∀ i, μ i ∈ boundedDivisors (fundSystem K) (m : 𝓞 K)) →
      ∀ X Y : (𝓞 K)ˣ,
        ((θ 1 : K) - θ 2) / ((θ 1 : K) - θ 0) * ((μ 0 : K) / μ 2) * (X : K) +
          ((θ 2 : K) - θ 0) / ((θ 1 : K) - θ 0) * ((μ 1 : K) / μ 2) * (Y : K) = 1 →
        ∀ ζ ∈ torsion K, ∀ e : Fin (rank K) → ℤ, X = ζ * ∏ j, fundSystem K j ^ e j →
          ∀ j, |(e j : ℝ)| ≤ B)
    {x y : ℤ} (hxy : MvPolynomial.eval ![x, y] (g.homogenize n) = m) :
    max |(x : ℝ)| |(y : ℝ)| ≤ |(m : ℝ)| ^ (1 / (n : ℝ)) * Real.exp
      (4 * (rank K * ∑ j, ‖logEmbedding K (Additive.ofMul (fundSystem K j))‖ +
          Real.log |(m : ℝ)|) +
        2 * B * ∑ j, Real.log (NumberField.house (fundSystem K j : K)) +
        log⁺ (NumberField.house (θ 0 : K)) + log⁺ (NumberField.house (θ 2 : K)) +
        2 * Real.log 2) := by
  -- `n ≠ 0`: otherwise `g` is a constant with a root, hence `0`, and `G(x, y) = 0 ≠ m`.
  have hn0 : n ≠ 0 := by
    rintro rfl
    have hg0 : g = Polynomial.C (g.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hn
    have hc : g.coeff 0 = 0 := by
      have h := hg 0
      rwa [hg0, Polynomial.aeval_C, algebraMap_int_eq, eq_intCast, Int.cast_eq_zero] at h
    rw [hg0, hc, map_zero, Polynomial.homogenize_zero, map_zero] at hxy
    exact hm hxy.symm
  have h := (Polynomial.isHomogeneous_homogenize (n := n) g).max_abs_le_abs_eval_rpow_mul_mulHeight₁
    hn0 (hxy ▸ hm)
  rw [hxy] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rw [← Real.exp_log (mulHeight₁_pos _)]
  exact Real.exp_le_exp.mpr (logHeight₁_div_le_of_eval_homogenize_eq hn hg hθ₁₀ hθ₀₂ hm hB hxy)

end Height

end NumberField.Units

end TauCeti
