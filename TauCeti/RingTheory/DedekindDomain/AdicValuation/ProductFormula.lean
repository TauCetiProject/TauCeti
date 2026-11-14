/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.NumberTheory.NumberField.ProductFormula
import TauCeti.RingTheory.Ideal.Norm.AbsNorm

/-!
# Finite-place products of adic absolute values over Dedekind domains

Let `R` be a Dedekind domain with finite quotients and fraction field `K`. Each height-one prime
`v` of `R` defines the normalized `v`-adic absolute value
`NumberField.HeightOneSpectrum.adicAbv K v : AbsoluteValue K ℝ`. Mathlib proves the product
formula `NumberField.FinitePlace.prod_eq_inv_abs_norm` for `FinitePlace K` over a number field `K`,
and `TauCeti.GlobalNumberFields.finprod_normalizedAbsValue_inl` transports it to
`HeightOneSpectrum (𝓞 K)`. Because `adicAbv` is defined directly for `HeightOneSpectrum R` (for
instance `R = ℤ` rather than `𝓞 ℚ`), downstream global products indexed by `HeightOneSpectrum R`
consume a product formula at the same Dedekind-domain generality.

For any nonzero `x : R`, the product of `adicAbv K v (algebraMap R K x)` over all height-one
primes `v` of `R` is `(Ideal.absNorm (Ideal.span {x}))⁻¹`. Passing to fractions gives the ratio of
ideal norms for any nonzero element of `K`, and specializing to `R = ℤ` yields the rational
finite-place product formula indexed by `HeightOneSpectrum ℤ`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.adicAbv_eq_absNorm_zpow`: at a nonzero element `x ∈ K`,
  `adicAbv K v x = (Ideal.absNorm v.asIdeal : ℝ) ^ WithZero.log (v.valuation K x)`.
* `IsDedekindDomain.HeightOneSpectrum.hasFiniteMulSupport_adicAbv`: for `x ≠ 0` in `K`, only
  finitely many height-one primes have `adicAbv K v x ≠ 1`.
* `IsDedekindDomain.HeightOneSpectrum.finprod_adicAbv_algebraMap`: for `x ≠ 0` in `R`,
  `∏ᶠ v : HeightOneSpectrum R, adicAbv K v (algebraMap R K x) = (Ideal.absNorm (Ideal.span {x}))⁻¹`.
* `IsDedekindDomain.HeightOneSpectrum.finprod_adicAbv_div`: for nonzero `a, b ∈ R`, the finite
  product of `adicAbv K v (algebraMap R K a / algebraMap R K b)` is
  `Ideal.absNorm (Ideal.span {b}) / Ideal.absNorm (Ideal.span {a})`.
* `IsDedekindDomain.HeightOneSpectrum.finprod_adicAbv_rat` and
  `IsDedekindDomain.HeightOneSpectrum.abs_mul_finprod_adicAbv_rat`: the rational product formula
  over `HeightOneSpectrum ℤ`.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter III, §1.

## Provenance

`finprod_adicAbv_algebraMap` generalizes `NumberField.FinitePlace.prod_eq_inv_abs_norm_int` in
`Mathlib.NumberTheory.NumberField.ProductFormula` from `𝓞 K` to any Dedekind domain `R` satisfying
`Ring.HasFiniteQuotients R`.
-/

public section

open Function Ideal NumberField NumberField.HeightOneSpectrum

namespace IsDedekindDomain.HeightOneSpectrum

section DedekindDomain

variable (R : Type*) [CommRing R] [IsDedekindDomain R] [Ring.HasFiniteQuotients R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- At a nonzero element of `K`, the normalized `v`-adic absolute value is the absolute norm of
`v` raised to the additive exponent `WithZero.log (v.valuation K x)`. -/
theorem adicAbv_eq_absNorm_zpow (v : HeightOneSpectrum R) {x : K} (hx : x ≠ 0) :
    NumberField.HeightOneSpectrum.adicAbv K v x =
      (absNorm v.asIdeal : ℝ) ^ WithZero.log (v.valuation K x) := by
  rw [NumberField.HeightOneSpectrum.adicAbv_def,
    WithZeroMulInt.toNNReal_neg_apply (NumberField.HeightOneSpectrum.absNorm_ne_zero v)
      ((v.valuation K).ne_zero_iff.mpr hx)]
  norm_cast

/-- For a nonzero element of `R`, only finitely many height-one primes have nontrivial `v`-adic
absolute value. -/
theorem hasFiniteMulSupport_adicAbv_algebraMap {x : R} (hx : x ≠ 0) :
    (fun v : HeightOneSpectrum R ↦
      NumberField.HeightOneSpectrum.adicAbv K v (algebraMap R K x)).HasFiniteMulSupport := by
  have hspan : span ({x} : Set R) ≠ 0 := by simpa using hx
  refine (Ideal.finite_factors hspan).subset fun v hv ↦ ?_
  rw [mem_mulSupport, ne_eq, ← FinitePlace.norm_embedding, FinitePlace.norm_eq_one_iff_notMem,
    not_not] at hv
  rwa [Set.mem_ofPred_eq, Ideal.dvd_span_singleton]

variable {R} in
/-- For a nonzero element of `K`, only finitely many height-one primes of `R` have nontrivial
`v`-adic absolute value. -/
theorem hasFiniteMulSupport_adicAbv {x : K} (hx : x ≠ 0) :
    (fun v : HeightOneSpectrum R ↦
      NumberField.HeightOneSpectrum.adicAbv K v x).HasFiniteMulSupport := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : (b : R) ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := fun h ↦ hx (by simp [h])
  simp_rw [map_div₀]
  exact (hasFiniteMulSupport_adicAbv_algebraMap R (K := K) ha0).fun_div
    (hasFiniteMulSupport_adicAbv_algebraMap R (K := K) hb0)

/-- **Finite-place product formula on `R`**: for a nonzero `x ∈ R`, the product of the normalized
`v`-adic absolute values of `algebraMap R K x` over all height-one primes `v` of `R` is the
reciprocal of the absolute norm of `Ideal.span {x}`. -/
theorem finprod_adicAbv_algebraMap {x : R} (hx : x ≠ 0) :
    (∏ᶠ v : HeightOneSpectrum R,
      NumberField.HeightOneSpectrum.adicAbv K v (algebraMap R K x)) =
      (absNorm (span ({x} : Set R)) : ℝ)⁻¹ := by
  have hspan : span ({x} : Set R) ≠ 0 := by simpa using hx
  have hfin₁ := hasFiniteMulSupport_adicAbv_algebraMap R (K := K) hx
  have hfin₂ : (fun v : HeightOneSpectrum R ↦
      (absNorm (v.maxPowDividing (span {x})) : ℝ)).HasFiniteMulSupport := by
    refine (Ideal.finite_factors hspan).subset ?_
    simp only [mulSupport_subset_iff, Set.mem_ofPred_eq, maxPowDividing]
    intro v hv
    simp only [map_pow, Nat.cast_pow, ← pow_zero (absNorm v.asIdeal : ℝ)] at hv
    refine (Associates.count_ne_zero_iff_dvd hspan v.irreducible).1 fun h ↦ hv ?_
    congr
  refine eq_inv_of_mul_eq_one_left ?_
  have hprod : (absNorm (∏ᶠ v : HeightOneSpectrum R, v.maxPowDividing (span {x})) : ℝ) =
      ∏ᶠ v : HeightOneSpectrum R, (absNorm (v.maxPowDividing (span {x})) : ℝ) :=
    ((Nat.castRingHom ℝ).toMonoidHom.comp absNorm.toMonoidHom).map_finprod_of_preimage_one
      (by simp) _
  rw [← Ideal.finprod_heightOneSpectrum_factorization hspan, hprod,
    ← finprod_mul_distrib hfin₁ hfin₂]
  refine finprod_eq_one_of_forall_eq_one fun v ↦ ?_
  rw [← FinitePlace.norm_embedding]
  exact NumberField.HeightOneSpectrum.embedding_mul_absNorm K v hx

/-- **Finite-place product formula on fractions**: for nonzero `a, b ∈ R`, the product of
`adicAbv K v (algebraMap R K a / algebraMap R K b)` over all height-one primes of `R` is
`absNorm (span {b}) / absNorm (span {a})`. -/
theorem finprod_adicAbv_div {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) :
    (∏ᶠ v : HeightOneSpectrum R,
      NumberField.HeightOneSpectrum.adicAbv K v (algebraMap R K a / algebraMap R K b)) =
      (absNorm (span ({b} : Set R)) : ℝ) / absNorm (span ({a} : Set R)) := by
  simp_rw [map_div₀]
  rw [finprod_div_distrib (hasFiniteMulSupport_adicAbv_algebraMap R ha)
    (hasFiniteMulSupport_adicAbv_algebraMap R hb),
    finprod_adicAbv_algebraMap R ha, finprod_adicAbv_algebraMap R hb, inv_div_inv]

end DedekindDomain

section Rational

/-- **The finite-place product of `p`-adic absolute values of a nonzero rational**: over
`HeightOneSpectrum ℤ`, the product of `adicAbv ℚ v x` equals `|x|⁻¹`. -/
theorem finprod_adicAbv_rat {x : ℚ} (hx : x ≠ 0) :
    (∏ᶠ v : HeightOneSpectrum ℤ, NumberField.HeightOneSpectrum.adicAbv ℚ v x) = |(x : ℝ)|⁻¹ := by
  have hnum : x.num ≠ 0 := Rat.num_ne_zero.mpr hx
  have hden : (x.den : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr x.den_nz
  have hcast : |(x : ℝ)| = (x.num.natAbs : ℝ) / x.den := by
    conv_lhs => rw [← Rat.num_div_den x]
    rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, abs_div, ← Int.cast_abs,
      Int.abs_eq_natAbs, Int.cast_natCast, Nat.abs_cast]
  have hx' : x = algebraMap ℤ ℚ x.num / algebraMap ℤ ℚ (x.den : ℤ) := by
    simp [Rat.num_div_den]
  conv_lhs => rw [hx']
  rw [finprod_adicAbv_div ℤ hnum hden, Int.absNorm_span_singleton, Int.absNorm_span_singleton,
    Int.natAbs_natCast, hcast, inv_div]

/-- **The rational product formula indexed by `HeightOneSpectrum ℤ`**: for a nonzero `x ∈ ℚ`,
`|x|_∞ · ∏_p |x|_p = 1`. -/
theorem abs_mul_finprod_adicAbv_rat {x : ℚ} (hx : x ≠ 0) :
    |(x : ℝ)| * (∏ᶠ v : HeightOneSpectrum ℤ, NumberField.HeightOneSpectrum.adicAbv ℚ v x) = 1 := by
  have hxR : |(x : ℝ)| ≠ 0 := abs_ne_zero.mpr (Rat.cast_ne_zero.mpr hx)
  rw [finprod_adicAbv_rat hx, mul_inv_cancel₀ hxR]

end Rational

end IsDedekindDomain.HeightOneSpectrum

end
