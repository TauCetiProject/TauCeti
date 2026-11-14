/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

/-!
# The finite-place product formula for normalized absolute values on adic completions

Let `R` be a Dedekind domain with fraction field `K`. At a height-one prime `v` of `R` with finite
residue field, the completion `K_v = v.adicCompletion K` is a nonarchimedean local field and
carries the rational-valued normalized absolute value `TauCeti.normalizedAbsoluteValue K_v`.

For a nonzero `a ∈ R`, the local factor `|a|_v` in `ℚ≥0` is the inverse of the absolute norm of
the `v`-primary factor `v.maxPowDividing (Ideal.span {a})` of the principal ideal `(a)`. When `R`
has finite quotients, ideal factorization (`Ideal.finprod_heightOneSpectrum_factorization`)
assembles these local factors into the finite-place product formula

`∏ᶠ v : HeightOneSpectrum R, |a|_v = (Ideal.absNorm (Ideal.span {a}))⁻¹`

in `ℚ≥0`, without passing through `ℝ` or assuming `R` is the ring of integers of a number field
(compare Mathlib's `NumberField.FinitePlace.prod_eq_inv_abs_norm`, which takes values in `ℝ` on
`NumberField.FinitePlace K`, whereas `TauCeti.normalizedAbsoluteValue` takes exact rational values
in `ℚ≥0` on `v.adicCompletion K` and also covers global function fields). When `R` is finite and
free over `ℤ`, `Ideal.absNorm (Ideal.span {a})` is `|N_{R/ℤ}(a)|`. Over `ℚ` (`R = ℤ`), dividing
numerators by denominators gives `∏ᶠ v : HeightOneSpectrum ℤ, |x|_v = |x|⁻¹` in `ℚ` for every
nonzero rational number `x`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.finite_quotient_asIdeal`: when `R` has finite quotients,
  every height-one prime `v` of `R` has finite residue field `R ⧸ v.asIdeal`.
* `IsDedekindDomain.HeightOneSpectrum.normalizedAbsoluteValue_algebraMap_ring_eq_one_iff`: for
  `a : R`, `|a|_v = 1` in `K_v` if and only if `a ∉ v.asIdeal`.
* `IsDedekindDomain.HeightOneSpectrum.normalizedAbsoluteValue_algebraMap_ring_eq_inv_absNorm` and
  `normalizedAbsoluteValue_algebraMap_ring_mul_absNorm`: for `a ≠ 0` in `R`, `|a|_v` is the
  inverse of `Ideal.absNorm (v.maxPowDividing (Ideal.span {a}))`.
* `TauCeti.hasFiniteMulSupport_normalizedAbsoluteValue_algebraMap_ring` and
  `TauCeti.hasFiniteMulSupport_normalizedAbsoluteValue_algebraMap`: for nonzero elements of `R` or
  `K`, `|x|_v = 1` outside finitely many height-one primes of `R`.
* `TauCeti.finprod_normalizedAbsoluteValue_algebraMap_ring` and
  `TauCeti.finprod_normalizedAbsoluteValue_algebraMap_ring_eq_inv_natAbs_norm`: the finite-place
  product formula in `ℚ≥0` on `R \ {0}`.
* `TauCeti.finprod_normalizedAbsoluteValue_rat` and
  `TauCeti.finprod_inv_normalizedAbsoluteValue_rat`: for `x : ℚ` with `x ≠ 0`,
  `∏ᶠ v : HeightOneSpectrum ℤ, |x|_v = |x|⁻¹` and `∏ᶠ v : HeightOneSpectrum ℤ, |x|_v⁻¹ = |x|`.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter III, §1.
* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter II, §1.
-/

public section

open scoped NNRat WithZero

open IsDedekindDomain

namespace IsDedekindDomain.HeightOneSpectrum

/-- In a commutative ring with finite quotients, the quotient by every height-one prime is finite.
Together with `isNonarchimedeanLocalField_adicCompletion`, this supplies the local-field structure
on `v.adicCompletion K` automatically. -/
instance finite_quotient_asIdeal {R : Type*} [CommRing R] [Ring.HasFiniteQuotients R]
    (v : HeightOneSpectrum R) :
    Finite (R ⧸ v.asIdeal) :=
  Ring.HasFiniteQuotients.finiteQuotient v.ne_bot

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable (K) (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)]

/-- **An element of `R` has normalized absolute value `1` in `K_v` exactly when it lies outside
`v`.** The equivalence holds for `a = 0` as well, since `0 ∈ v.asIdeal` and `|0|_v = 0`. -/
theorem normalizedAbsoluteValue_algebraMap_ring_eq_one_iff (a : R) :
    TauCeti.normalizedAbsoluteValue (v.adicCompletion K)
        (algebraMap R (v.adicCompletion K) a) = 1 ↔
      a ∉ v.asIdeal := by
  rcases eq_or_ne a 0 with rfl | _
  · simp [zero_mem]
  have hequiv := ValuativeRel.isEquiv (ValuativeRel.valuation (v.adicCompletion K))
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
  rw [IsScalarTower.algebraMap_apply R K (v.adicCompletion K),
    TauCeti.normalizedAbsoluteValue_eq_one_iff, hequiv.eq_one_iff_eq_one,
    algebraMap_adicCompletion, Function.comp_apply, valuedAdicCompletion_eq_valuation',
    Algebra.algebraMap_self_apply, v.valuation_of_algebraMap, ← not_iff_not, not_not,
    ← v.intValuation_lt_one_iff_mem]
  exact ⟨fun h ↦ lt_of_le_of_ne (v.intValuation_le_one a) h, ne_of_lt⟩

/-- **The normalized absolute value in `K_v` of a nonzero `a ∈ R` is the inverse of the norm of
its `v`-primary factor.** -/
theorem normalizedAbsoluteValue_algebraMap_ring_eq_inv_absNorm {a : R} (ha : a ≠ 0) :
    TauCeti.normalizedAbsoluteValue (v.adicCompletion K)
        (algebraMap R (v.adicCompletion K) a) =
      (Ideal.absNorm (v.maxPowDividing (Ideal.span {a})) : ℚ≥0)⁻¹ := by
  have haK : algebraMap R K a ≠ 0 := by
    rwa [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]
  have hx : algebraMap K (v.adicCompletion K) (algebraMap R K a) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K (v.adicCompletion K)).injective).mpr haK
  set e : ℕ := (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a})).factors
  have hval : (TauCeti.normalizedValuation (v.adicCompletion K)
      (Units.mk0 (algebraMap K (v.adicCompletion K) (algebraMap R K a)) hx)).toAdd = (e : ℤ) := by
    have hcoe := v.coe_normalizedValuation_unitsMap_algebraMap (Units.mk0 (algebraMap R K a) haK)
    have hunit : Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K)
        (Units.mk0 (algebraMap R K a) haK) =
      Units.mk0 (algebraMap K (v.adicCompletion K) (algebraMap R K a)) hx := Units.ext rfl
    rw [hunit, Units.val_mk0, v.valuation_of_algebraMap, v.intValuation_if_neg ha,
      ← WithZero.exp_neg, neg_neg, WithZero.exp_eq_coe_ofAdd, WithZero.coe_inj] at hcoe
    exact congrArg Multiplicative.toAdd hcoe
  rw [IsScalarTower.algebraMap_apply R K (v.adicCompletion K),
    TauCeti.normalizedAbsoluteValue_apply_ne_zero _ hx, hval,
    v.natCard_residueField_adicCompletion_eq_absNorm, zpow_neg, zpow_natCast, maxPowDividing,
    map_pow, Nat.cast_pow]

/-- **Local norm-cancellation identity**: for `a ≠ 0` in `R`, `|a|_v` times the absolute norm of
the `v`-primary part of `(a)` is `1` in `ℚ≥0`. -/
theorem normalizedAbsoluteValue_algebraMap_ring_mul_absNorm {a : R} (ha : a ≠ 0) :
    TauCeti.normalizedAbsoluteValue (v.adicCompletion K)
        (algebraMap R (v.adicCompletion K) a) *
      Ideal.absNorm (v.maxPowDividing (Ideal.span {a})) = 1 := by
  have h0 : (Ideal.absNorm (v.maxPowDividing (Ideal.span {a})) : ℚ≥0) ≠ 0 := by
    rw [Nat.cast_ne_zero, maxPowDividing, map_pow,
      ← v.natCard_residueField_adicCompletion_eq_absNorm (K := K)]
    exact pow_ne_zero _ Nat.card_pos.ne'
  rw [v.normalizedAbsoluteValue_algebraMap_ring_eq_inv_absNorm K ha, inv_mul_cancel₀ h0]

end IsDedekindDomain.HeightOneSpectrum

namespace TauCeti

section HasFiniteQuotients

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Ring.HasFiniteQuotients R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

variable (K) in
/-- **Finite multiplicative support on `R \ {0}`**: a nonzero element of `R` has normalized
absolute value `1` in `K_v` at all but finitely many height-one primes `v` of `R`. -/
theorem hasFiniteMulSupport_normalizedAbsoluteValue_algebraMap_ring {a : R} (ha : a ≠ 0) :
    Function.HasFiniteMulSupport (fun v : HeightOneSpectrum R ↦
      normalizedAbsoluteValue (v.adicCompletion K) (algebraMap R (v.adicCompletion K) a)) := by
  have hspan : Ideal.span {a} ≠ 0 := by simp [ha]
  have hfin : {v : HeightOneSpectrum R | a ∈ v.asIdeal}.Finite := by
    simpa only [← Ideal.dvd_span_singleton] using Ideal.finite_factors hspan
  refine hfin.subset fun v hv ↦ ?_
  rwa [Function.mem_mulSupport, ne_eq,
    v.normalizedAbsoluteValue_algebraMap_ring_eq_one_iff K, not_not] at hv

variable (R) in
/-- **Finite multiplicative support on `K \ {0}`**: a nonzero element of the fraction field `K` has
normalized absolute value `1` in `K_v` at all but finitely many height-one primes `v` of `R`. -/
theorem hasFiniteMulSupport_normalizedAbsoluteValue_algebraMap {x : K} (hx : x ≠ 0) :
    Function.HasFiniteMulSupport (fun v : HeightOneSpectrum R ↦
      normalizedAbsoluteValue (v.adicCompletion K) (algebraMap K (v.adicCompletion K) x)) := by
  rcases IsFractionRing.div_surjective R x with ⟨a, b, hb, rfl⟩
  have hb0 : (b : R) ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hx
  refine ((hasFiniteMulSupport_normalizedAbsoluteValue_algebraMap_ring K ha0).union
    (hasFiniteMulSupport_normalizedAbsoluteValue_algebraMap_ring K hb0)).subset fun v hv ↦ ?_
  rw [Function.mem_mulSupport] at hv
  by_contra hnot
  rw [Set.mem_union, Function.mem_mulSupport, Function.mem_mulSupport, not_or, not_not,
    not_not] at hnot
  refine hv ?_
  rw [map_div₀, map_div₀, ← IsScalarTower.algebraMap_apply R K (v.adicCompletion K),
    ← IsScalarTower.algebraMap_apply R K (v.adicCompletion K), hnot.1, hnot.2, div_one]

variable (K) in
/-- **The finite-place product formula on `R \ {0}`**: for a Dedekind domain `R` with finite
quotients and `a ≠ 0` in `R`, the product over all height-one primes `v` of `R` of the normalized
absolute value `|a|_v` in `K_v` is `(Ideal.absNorm (Ideal.span {a}))⁻¹` in `ℚ≥0`. -/
theorem finprod_normalizedAbsoluteValue_algebraMap_ring {a : R} (ha : a ≠ 0) :
    ∏ᶠ v : HeightOneSpectrum R,
        normalizedAbsoluteValue (v.adicCompletion K) (algebraMap R (v.adicCompletion K) a) =
      (Ideal.absNorm (Ideal.span {a}) : ℚ≥0)⁻¹ := by
  have hspan : Ideal.span {a} ≠ 0 := by simp [ha]
  have hprod :
      (Ideal.absNorm (∏ᶠ v : HeightOneSpectrum R, v.maxPowDividing (Ideal.span {a})) : ℚ≥0) =
        ∏ᶠ v : HeightOneSpectrum R, (Ideal.absNorm (v.maxPowDividing (Ideal.span {a})) : ℚ≥0) :=
    ((Nat.castRingHom ℚ≥0).toMonoidHom.comp Ideal.absNorm.toMonoidHom).map_finprod_of_preimage_one
      (by simp) _
  simp_rw [HeightOneSpectrum.normalizedAbsoluteValue_algebraMap_ring_eq_inv_absNorm K _ ha]
  rw [finprod_inv_distrib, ← hprod, Ideal.finprod_heightOneSpectrum_factorization hspan]

/-- **The finite-place product formula on `R \ {0}` in terms of `Algebra.norm ℤ`**: when `R` is a
Dedekind domain finite and free as a `ℤ`-module, `∏ᶠ v, |a|_v = |N_{R/ℤ}(a)|⁻¹` in `ℚ≥0`. -/
theorem finprod_normalizedAbsoluteValue_algebraMap_ring_eq_inv_natAbs_norm (K : Type*) [Field K]
    [Algebra R K] [IsFractionRing R K] [Module.Free ℤ R] [Module.Finite ℤ R] {a : R} (ha : a ≠ 0) :
    ∏ᶠ v : HeightOneSpectrum R,
        normalizedAbsoluteValue (v.adicCompletion K) (algebraMap R (v.adicCompletion K) a) =
      ((Algebra.norm ℤ a).natAbs : ℚ≥0)⁻¹ := by
  rw [finprod_normalizedAbsoluteValue_algebraMap_ring K ha, Ideal.absNorm_span_singleton]

end HasFiniteQuotients

section Rat

/-- **The finite-place product formula over `ℚ`**: for every nonzero `x : ℚ`, the product over all
maximal ideals `v` of `ℤ` of the `v`-adic normalized absolute value of `x` equals `|x|⁻¹` in `ℚ`.
Together with the archimedean factor `|x|` this is Ostrowski's product formula `|x|_∞ ∏_p |x|_p = 1`
with rational values. -/
theorem finprod_normalizedAbsoluteValue_rat {x : ℚ} (hx : x ≠ 0) :
    ∏ᶠ v : HeightOneSpectrum ℤ,
        (normalizedAbsoluteValue (v.adicCompletion ℚ) (algebraMap ℚ (v.adicCompletion ℚ) x) : ℚ) =
      |x|⁻¹ := by
  rcases IsFractionRing.div_surjective ℤ x with ⟨a, b, hb, rfl⟩
  have hb0 : (b : ℤ) ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hx
  have hcast : ∀ n : ℤ, n ≠ 0 →
      ∏ᶠ v : HeightOneSpectrum ℤ,
        (normalizedAbsoluteValue (v.adicCompletion ℚ)
          (algebraMap ℤ (v.adicCompletion ℚ) n) : ℚ) = |(n : ℚ)|⁻¹ := by
    intro n hn
    have h := congrArg ((↑) : ℚ≥0 → ℚ)
      (finprod_normalizedAbsoluteValue_algebraMap_ring_eq_inv_natAbs_norm ℚ hn)
    have hmap :
        ((∏ᶠ v : HeightOneSpectrum ℤ,
            normalizedAbsoluteValue (v.adicCompletion ℚ)
              (algebraMap ℤ (v.adicCompletion ℚ) n) : ℚ≥0) : ℚ) =
          ∏ᶠ v : HeightOneSpectrum ℤ,
            (normalizedAbsoluteValue (v.adicCompletion ℚ)
              (algebraMap ℤ (v.adicCompletion ℚ) n) : ℚ) :=
      (NNRat.castHom ℚ).toMonoidHom.map_finprod_of_preimage_one
        (fun _ h ↦ NNRat.coe_injective (by simpa using h)) _
    rw [hmap, NNRat.cast_inv, NNRat.cast_natCast, Algebra.norm_self, MonoidHom.id_apply,
      Nat.cast_natAbs, Int.cast_abs] at h
    exact h
  have hsupp (n : ℤ) (hn : n ≠ 0) :
      Function.HasFiniteMulSupport (fun v : HeightOneSpectrum ℤ ↦
        (normalizedAbsoluteValue (v.adicCompletion ℚ)
          (algebraMap ℤ (v.adicCompletion ℚ) n) : ℚ)) :=
    (hasFiniteMulSupport_normalizedAbsoluteValue_algebraMap_ring ℚ hn).subset fun v hv ↦ by
      rw [Function.mem_mulSupport] at hv ⊢
      exact_mod_cast hv
  simp_rw [map_div₀, ← IsScalarTower.algebraMap_apply ℤ ℚ (HeightOneSpectrum.adicCompletion ℚ _),
    NNRat.cast_div]
  rw [finprod_div_distrib (hsupp a ha0) (hsupp b hb0), hcast a ha0, hcast b hb0,
    algebraMap_int_eq, eq_intCast, eq_intCast, abs_div, inv_div_inv, ← inv_div]

/-- **Inverted finite-place product formula over `ℚ`**: for `x ≠ 0` in `ℚ`, the product over all
finite places `v` of `ℤ` of `|x|_v⁻¹` equals `|x|`. -/
theorem finprod_inv_normalizedAbsoluteValue_rat {x : ℚ} (hx : x ≠ 0) :
    ∏ᶠ v : HeightOneSpectrum ℤ,
        (normalizedAbsoluteValue (v.adicCompletion ℚ)
          (algebraMap ℚ (v.adicCompletion ℚ) x) : ℚ)⁻¹ =
      |x| := by
  rw [finprod_inv_distrib, finprod_normalizedAbsoluteValue_rat hx, inv_inv]

end Rat

end TauCeti

end
