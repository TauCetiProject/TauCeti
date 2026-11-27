/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.Factorization
import TauCeti.RingTheory.Valuation.Integers

/-!
# Integrality of a pairing after division

Let `R` be a Dedekind domain with fraction field `K`, let `c : K →+* K` be a ring endomorphism
and let `B : V →ₗ[K] W →ₛₗ[c] K` be a pairing that is `K`-linear in `V` and `c`-semilinear in `W`.
Let `N ⊆ V` and `X ⊆ W`, and let `τ : HeightOneSpectrum R →₀ ℤ`. Suppose that at every height
one prime `v` of `R` there is a set `S v ⊆ W` such that

* `X` lies in the span of `S v` over the ring of `e : K` with `c e` integral at `v`, and
* the values of `B` on `N × S v` have `v`-adic valuation at most `exp (-τ v)`.

Then `B` takes integral values on `N′ × X`, where `N′` is the `R`-span of the products `a • n`
with `n ∈ N` and `a` in the fractional ideal `∏ᵥ v ^ (-τ v)`: dividing `N` by `∏ᵥ v ^ τ v` keeps
the pairing integral.

The bound at `v` is only needed on the set `S v`, which may change with `v`, and the division is
paid for at the prime `v` itself: when `c` is not the identity, a value of the pairing on `N × X`
divisible by `v` need not be divisible by `c v`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.pairing_smul_integral_of_localDivision`: the value of `B` at
  `(a • n, x)` is integral for `a ∈ ∏ᵥ v ^ (-τ v)`, `n ∈ N` and `x ∈ X`.
* `IsDedekindDomain.HeightOneSpectrum.pairing_integral_of_localDivision`: the same for every
  element of the `R`-span of these `a • n`.

## Implementation notes

The hypothesis is stated with the sets `S v` and with valuations of the values of `B` on them.
Data presented, as in a typical application, by `S v = j v '' M v` for maps `j v : U v → W` and
sets `M v ⊆ U v`, with values `P v φ Υ = ζ v * B φ (j v Υ)` for `v`-adic units `ζ v`, and with a
real lower bound `σ v` for the additive valuation of the nonzero values `P v φ Υ`, give this
hypothesis for any integers `τ v ≤ ⌈σ v⌉`: the multiplicative valuation of a product is the product
of the valuations, and additive valuations are integers.

## References

* L. Alpöge, the Lean formalization of the Riemann hypothesis for Dirichlet `L`-functions,
  <https://github.com/leanprover-community/riemann-hypothesis> (commit
  `40e56bab026552e089d7afcfeff08d2defb9c005`): the statement over the ring of integers of a number
  field is `Formalism.DivisionValues.DivIntoDualShift`
  (`src/Formalism/QuotientMetricDivisors/DivIntoDualShift.lean`), and the proof here follows its
  route: pull the local bound back along the span, then add the valuation of the divisor.
-/

public section

namespace IsDedekindDomain.HeightOneSpectrum

open scoped nonZeroDivisors

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {c : K →+* K} {V W : Type*} [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- **Integrality after division, for one product.** Let `B` be `K`-linear in `V` and
`c`-semilinear in `W`. If at every height one prime `v` the set `X` lies in the span of `S v` over
the ring of `e` with `c e` integral at `v`, and the values of `B` on `N × S v` have valuation at
most `exp (-τ v)`, then `B (a • φ) x` is integral for `a ∈ ∏ᵥ v ^ (-τ v)`, `φ ∈ N` and `x ∈ X`. -/
theorem pairing_smul_integral_of_localDivision (B : V →ₗ[K] W →ₛₗ[c] K) {N : Set V} {X : Set W}
    {S : HeightOneSpectrum R → Set W}
    (hX : ∀ v : HeightOneSpectrum R, X ⊆ Submodule.span ((v.valuation K).comap c).integer (S v))
    (τ : HeightOneSpectrum R →₀ ℤ)
    (hS : ∀ v : HeightOneSpectrum R, ∀ φ ∈ N, ∀ y ∈ S v,
      v.valuation K (B φ y) ≤ WithZero.exp (-τ v))
    {a : K} (ha : a ∈ ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^ (-τ v))
    {φ : V} (hφ : φ ∈ N) {x : W} (hx : x ∈ X) :
    B (a • φ) x ∈ (algebraMap R K).range := by
  refine mem_integers_of_valuation_le_one K _ fun v ↦ ?_
  have hB := (v.valuation K).map_apply_le_of_mem_span_comap_integer (B φ) (hS v φ hφ) (hX v hx)
  have ha' := FractionalIdeal.valuation_le_exp_neg_count_of_mem v ha
  rw [FractionalIdeal.count_finprod K v _ (Filter.eventually_cofinite.mpr
    (τ.support.finite_toSet.subset fun w hw ↦ by simpa using hw)), neg_neg] at ha'
  rw [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul, map_mul]
  calc _ ≤ WithZero.exp (τ v) * WithZero.exp (-τ v) := mul_le_mul' ha' hB
    _ = 1 := by rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]

/-- **Integrality after division.** Let `B` be `K`-linear in `V` and `c`-semilinear in `W`. If at
every height one prime `v` the set `X` lies in the span of `S v` over the ring of `e` with `c e`
integral at `v`, and the values of `B` on `N × S v` have valuation at most `exp (-τ v)`, then `B`
is integral on `N′ × X`, where `N′` is the `R`-span of the `a • n` with `n ∈ N` and `a` in the
fractional ideal `∏ᵥ v ^ (-τ v)`. -/
theorem pairing_integral_of_localDivision [Module R V] [IsScalarTower R K V]
    (B : V →ₗ[K] W →ₛₗ[c] K) {N : Set V} {X : Set W} {S : HeightOneSpectrum R → Set W}
    (hX : ∀ v : HeightOneSpectrum R, X ⊆ Submodule.span ((v.valuation K).comap c).integer (S v))
    (τ : HeightOneSpectrum R →₀ ℤ)
    (hS : ∀ v : HeightOneSpectrum R, ∀ φ ∈ N, ∀ y ∈ S v,
      v.valuation K (B φ y) ≤ WithZero.exp (-τ v)) :
    ∀ φ ∈ Submodule.span R {y : V | ∃ a ∈ (∏ᶠ v : HeightOneSpectrum R,
        (v.asIdeal : FractionalIdeal R⁰ K) ^ (-τ v)), ∃ n ∈ N, y = a • n},
      ∀ x ∈ X, B φ x ∈ (algebraMap R K).range := by
  intro φ hφ x hx
  induction hφ using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, n, hn, rfl⟩ := hy
    exact pairing_smul_integral_of_localDivision B hX τ hS ha hn hx
  | zero => exact ⟨0, by simp⟩
  | add y z _ _ hy hz =>
    rw [map_add, LinearMap.add_apply]
    exact add_mem hy hz
  | smul r y _ hy =>
    rw [← algebraMap_smul K r y, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact mul_mem ⟨r, rfl⟩ hy

end IsDedekindDomain.HeightOneSpectrum
