/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Homogenize
public import TauCeti.NumberTheory.NumberField.Units.Balanced

/-!
# Reduction of Thue equations to unit equations

Let `G` be the homogenization of `g ∈ ℤ[X]` of degree `n ≥ natDegree g`, and `m ≠ 0`. If
`θ₀, θ₁, θ₂` are roots of `g` in the ring of integers `𝓞 K` of a number field `K`, then at every
solution of the Thue equation `G(x, y) = m` the three linear forms `x - θᵢ y` divide `m` in `𝓞 K`.
By the balancing argument each of them is a unit `εᵢ` times one of the finitely many
representatives `μᵢ` in `boundedDivisors u m`. Siegel's identity

  `(θ₁ - θ₂) (x - θ₀ y) + (θ₂ - θ₀) (x - θ₁ y) + (θ₀ - θ₁) (x - θ₂ y) = 0`

then shows that `(ε₀ / ε₂, ε₁ / ε₂)` solves the unit equation `a X + b Y = 1` with coefficients

  `a = (θ₁ - θ₂) / (θ₁ - θ₀) * (μ₀ / μ₂)`,   `b = (θ₂ - θ₀) / (θ₁ - θ₀) * (μ₁ / μ₂)`,

which take only finitely many values. Conversely, when `y ≠ 0` and `θ₀ ≠ θ₂`, the quotient
`λ = (x - θ₀ y) / (x - θ₂ y) = (μ₀ / μ₂) (ε₀ / ε₂)` determines `x / y = (θ₀ - λ θ₂) / (1 - λ)`.
So bounding the solutions of finitely many unit equations bounds the solutions of the Thue
equation, which is how Baker's lower bounds for linear forms in logarithms make Thue's theorem
effective.

## Main results

* `TauCeti.siegel_identity`: Siegel's identity in a commutative ring.
* `TauCeti.siegel_identity_div`: Siegel's identity, divided by `(θ₁ - θ₀) (x - θ₂ y)`.
* `TauCeti.div_eq_sub_mul_div_one_sub`: recovery of `x / y` from the quotient `λ`.
* `TauCeti.NumberField.Units.exists_mem_boundedDivisors_mul_add_mul_eq_one`: if the three linear
  forms `x - θᵢ y` divide `m ≠ 0`, they are units times members of `boundedDivisors u m`, and the
  unit quotients solve the unit equation above.
* `TauCeti.NumberField.Units.exists_mem_boundedDivisors_mul_add_mul_eq_one_of_eval_homogenize_eq`:
  the same conclusion at the integer solutions of a Thue equation `G(x, y) = m`.

## References

* [J.-H. Evertse, *Diophantine Approximation*, lecture notes, Leiden/Mastermath, 2019],
  Chapter 5, Theorem 5.13 and its proof, pp. 96–98.
-/

public section

open Module NumberField NumberField.Units
open scoped NumberField

namespace TauCeti

/-- **Siegel's identity.** In a commutative ring, the three linear forms `x - θᵢ y` satisfy
`(θ₁ - θ₂) (x - θ₀ y) + (θ₂ - θ₀) (x - θ₁ y) + (θ₀ - θ₁) (x - θ₂ y) = 0`. -/
theorem siegel_identity {R : Type*} [CommRing R] (θ₀ θ₁ θ₂ x y : R) :
    (θ₁ - θ₂) * (x - θ₀ * y) + (θ₂ - θ₀) * (x - θ₁ * y) + (θ₀ - θ₁) * (x - θ₂ * y) = 0 := by
  ring

variable {F : Type*} [Field F]

/-- **Siegel's identity**, divided by `(θ₁ - θ₀) (x - θ₂ y)`: for `θ₀ ≠ θ₁` and `x - θ₂ y ≠ 0` in
a field, `(θ₁ - θ₂) / (θ₁ - θ₀) * ((x - θ₀ y) / (x - θ₂ y))` and
`(θ₂ - θ₀) / (θ₁ - θ₀) * ((x - θ₁ y) / (x - θ₂ y))` sum to `1`. -/
theorem siegel_identity_div {θ₀ θ₁ θ₂ x y : F} (h₀₁ : θ₀ ≠ θ₁) (h₂ : x - θ₂ * y ≠ 0) :
    (θ₁ - θ₂) / (θ₁ - θ₀) * ((x - θ₀ * y) / (x - θ₂ * y)) +
      (θ₂ - θ₀) / (θ₁ - θ₀) * ((x - θ₁ * y) / (x - θ₂ * y)) = 1 := by
  have h : θ₁ - θ₀ ≠ 0 := sub_ne_zero.mpr h₀₁.symm
  field_simp
  linear_combination siegel_identity θ₀ θ₁ θ₂ x y

/-- If `θ₀ ≠ θ₂`, `y ≠ 0` and `l (x - θ₂ y) = x - θ₀ y`, then `x / y = (θ₀ - l θ₂) / (1 - l)`,
where `l ≠ 1`: the quotient `l` of two non-proportional linear forms at `(x, y)` determines the
ratio `x / y`. -/
theorem div_eq_sub_mul_div_one_sub {θ₀ θ₂ x y l : F} (h₀₂ : θ₀ ≠ θ₂) (hy : y ≠ 0)
    (hl : l * (x - θ₂ * y) = x - θ₀ * y) : x / y = (θ₀ - l * θ₂) / (1 - l) := by
  have hl1 : 1 - l ≠ 0 := by
    rintro h
    obtain rfl : l = 1 := (sub_eq_zero.mp h).symm
    exact h₀₂ (mul_right_cancel₀ hy (by linear_combination hl))
  rw [div_eq_div_iff hy hl1]
  linear_combination -hl

end TauCeti

namespace TauCeti.NumberField.Units

variable {K : Type*} [Field K] [NumberField K]

/-- **Reduction to a unit equation.** Let `u` be a family of units of maximal rank, `m ≠ 0`, and
`θ₀ ≠ θ₁`. If the three linear forms `x - θᵢ y` divide `m` in `𝓞 K`, then
`x - θᵢ y = εᵢ μᵢ` with units `εᵢ` and `μᵢ ∈ boundedDivisors u m`, and `(ε₀ / ε₂, ε₁ / ε₂)` solves
the unit equation `a X + b Y = 1` with `a = (θ₁ - θ₂) / (θ₁ - θ₀) * (μ₀ / μ₂)` and
`b = (θ₂ - θ₀) / (θ₁ - θ₀) * (μ₁ / μ₂)`. Since `boundedDivisors u m` is finite, only finitely
many unit equations arise. -/
theorem exists_mem_boundedDivisors_mul_add_mul_eq_one {u : Fin (rank K) → (𝓞 K)ˣ}
    (hu : IsMaxRank u) {m : 𝓞 K} (hm : m ≠ 0) {θ₀ θ₁ θ₂ x y : 𝓞 K} (h₀₁ : θ₀ ≠ θ₁)
    (h₀ : x - θ₀ * y ∣ m) (h₁ : x - θ₁ * y ∣ m) (h₂ : x - θ₂ * y ∣ m) :
    ∃ μ₀ ∈ boundedDivisors u m, ∃ μ₁ ∈ boundedDivisors u m, ∃ μ₂ ∈ boundedDivisors u m,
      ∃ ε₀ ε₁ ε₂ : (𝓞 K)ˣ, x - θ₀ * y = ε₀ * μ₀ ∧ x - θ₁ * y = ε₁ * μ₁ ∧
        x - θ₂ * y = ε₂ * μ₂ ∧
        ((θ₁ : K) - θ₂) / ((θ₁ : K) - θ₀) * ((μ₀ : K) / μ₂) * ((ε₀ / ε₂ : (𝓞 K)ˣ) : K) +
          ((θ₂ : K) - θ₀) / ((θ₁ : K) - θ₀) * ((μ₁ : K) / μ₂) * ((ε₁ / ε₂ : (𝓞 K)ˣ) : K) =
            1 := by
  obtain ⟨μ₀, hμ₀, ε₀, he₀⟩ := exists_mem_boundedDivisors_of_dvd hu hm h₀
  obtain ⟨μ₁, hμ₁, ε₁, he₁⟩ := exists_mem_boundedDivisors_of_dvd hu hm h₁
  obtain ⟨μ₂, hμ₂, ε₂, he₂⟩ := exists_mem_boundedDivisors_of_dvd hu hm h₂
  refine ⟨μ₀, hμ₀, μ₁, hμ₁, μ₂, hμ₂, ε₀, ε₁, ε₂, he₀, he₁, he₂, ?_⟩
  have hcoe {θ : 𝓞 K} {ε : (𝓞 K)ˣ} {μ : 𝓞 K} (h : x - θ * y = ε * μ) :
      (x : K) - θ * y = ε * μ := by
    simpa using congrArg ((↑) : 𝓞 K → K) h
  -- `μ₂ ≠ 0` because it divides `m ≠ 0`.
  have hμ₂0 : (μ₂ : K) ≠ 0 := by
    rintro h
    rw [RingOfIntegers.coe_eq_zero_iff] at h
    exact hm (zero_dvd_iff.mp (h ▸ boundedDivisors_subset_dvd u m hμ₂))
  have h := siegel_identity_div (RingOfIntegers.coe_injective.ne h₀₁)
    (x := (x : K)) (y := y) (by rw [hcoe he₂]; exact mul_ne_zero (by simp) hμ₂0)
  have hε₂ : ((ε₂ : 𝓞 K) : K) ≠ 0 := by simp
  have hdiv (ε : (𝓞 K)ˣ) : (((ε / ε₂ : (𝓞 K)ˣ) : 𝓞 K) : K) = (ε : K) / ε₂ := by
    rw [eq_div_iff hε₂]
    norm_cast
    simp
  rw [hcoe he₀, hcoe he₁, hcoe he₂] at h
  simp only [← RingOfIntegers.coe_eq_algebraMap] at h hdiv ⊢
  rw [← h, hdiv, hdiv]
  field_simp

/-- **Thue equations reduce to unit equations.** Let `G` be the homogenization of degree
`n ≥ natDegree g` of `g ∈ ℤ[X]`, let `θ₀ ≠ θ₁` and `θ₂` be roots of `g` in `𝓞 K`, and let `u` be
a family of units of maximal rank. At every solution `(x, y) ∈ ℤ²` of the Thue equation
`G(x, y) = m` with `m ≠ 0`, we have `x - θᵢ y = εᵢ μᵢ` with units `εᵢ` and
`μᵢ ∈ boundedDivisors u m`, and `(ε₀ / ε₂, ε₁ / ε₂)` solves the unit equation `a X + b Y = 1` with
`a = (θ₁ - θ₂) / (θ₁ - θ₀) * (μ₀ / μ₂)` and `b = (θ₂ - θ₀) / (θ₁ - θ₀) * (μ₁ / μ₂)`. -/
theorem exists_mem_boundedDivisors_mul_add_mul_eq_one_of_eval_homogenize_eq
    {u : Fin (rank K) → (𝓞 K)ˣ} (hu : IsMaxRank u) {g : Polynomial ℤ} {n : ℕ}
    (hn : g.natDegree ≤ n) {θ₀ θ₁ θ₂ : 𝓞 K} (hθ₀ : Polynomial.aeval θ₀ g = 0)
    (hθ₁ : Polynomial.aeval θ₁ g = 0) (hθ₂ : Polynomial.aeval θ₂ g = 0) (h₀₁ : θ₀ ≠ θ₁)
    {x y m : ℤ} (hm : m ≠ 0) (hxy : MvPolynomial.eval ![x, y] (g.homogenize n) = m) :
    ∃ μ₀ ∈ boundedDivisors u (m : 𝓞 K), ∃ μ₁ ∈ boundedDivisors u (m : 𝓞 K),
      ∃ μ₂ ∈ boundedDivisors u (m : 𝓞 K), ∃ ε₀ ε₁ ε₂ : (𝓞 K)ˣ,
        (x - θ₀ * y : 𝓞 K) = ε₀ * μ₀ ∧ (x - θ₁ * y : 𝓞 K) = ε₁ * μ₁ ∧
        (x - θ₂ * y : 𝓞 K) = ε₂ * μ₂ ∧
        ((θ₁ : K) - θ₂) / ((θ₁ : K) - θ₀) * ((μ₀ : K) / μ₂) * ((ε₀ / ε₂ : (𝓞 K)ˣ) : K) +
          ((θ₂ : K) - θ₀) / ((θ₁ : K) - θ₀) * ((μ₁ : K) / μ₂) * ((ε₁ / ε₂ : (𝓞 K)ˣ) : K) =
            1 := by
  have hdvd {θ : 𝓞 K} (hθ : Polynomial.aeval θ g = 0) : (x - θ * y : 𝓞 K) ∣ m := by
    simpa [hxy] using
      Polynomial.algebraMap_sub_mul_algebraMap_dvd_algebraMap_eval_homogenize hθ hn ![x, y]
  exact exists_mem_boundedDivisors_mul_add_mul_eq_one hu (Int.cast_ne_zero.mpr hm) h₀₁
    (hdvd hθ₀) (hdvd hθ₁) (hdvd hθ₂)

end TauCeti.NumberField.Units
