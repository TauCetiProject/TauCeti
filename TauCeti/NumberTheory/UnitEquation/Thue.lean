/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Field.LinearFractional
public import TauCeti.Algebra.Polynomial.Homogenize
public import TauCeti.NumberTheory.NumberField.Units.Balanced

/-!
# Reduction of Thue equations to unit equations

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

## Main results

* `TauCeti.NumberField.Units.exists_mem_boundedDivisors_mul_add_mul_eq_one`: if each
  `x - θᵢ y` divides `m ≠ 0`, the factors are units times bounded divisors of `m`, and the
  unit quotients solve one of finitely many unit equations.
* `TauCeti.NumberField.Units.exists_mem_boundedDivisors_mul_add_mul_eq_one_of_eval_homogenize_eq`:
  the same conclusion for an integer solution of a Thue equation `G(x, y) = m`.

## References

* [J.-H. Evertse, *Diophantine Approximation*, lecture notes, Leiden/Mastermath, 2019],
  Chapter 5, Theorem 5.13 and its proof, pp. 96–98.
-/

public section

open NumberField NumberField.Units
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

end NumberField.Units

end TauCeti
