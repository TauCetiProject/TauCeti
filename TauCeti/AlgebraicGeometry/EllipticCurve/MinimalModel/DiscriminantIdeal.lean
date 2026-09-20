/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Factorization
public import TauCeti.AlgebraicGeometry.EllipticCurve.GlobalMinimalModel
public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Valuation
import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralModel

/-!
# The minimal discriminant ideal of an elliptic curve over a Dedekind domain

Let `O` be a Dedekind domain with fraction field `K` and let `W` be an elliptic Weierstrass
equation over `K`. At each height-one prime `v` of `O` the localisation
`Oᵥ = Localization.AtPrime v.asIdeal` is a discrete valuation ring, and
`WeierstrassCurve.localMinimalDiscriminantValuation` reads off the exponent `v (Δ_min,ᵥ)` of a
Weierstrass equation minimal over `Oᵥ`. This file assembles those exponents into a single ideal of
`O`,

`𝔇_{E/K} = ∏ᵥ 𝔭ᵥ ^ v (Δ_min,ᵥ)`,

the **minimal discriminant ideal** (Silverman, *The Arithmetic of Elliptic Curves*, VIII.8).

Each exponent is invariant under a change of variables, so the ideal depends only on the
`K`-isomorphism class of the curve and not on the equation presenting it. Against an equation that
is already integral over `O` it is comparable with the actual discriminant: the local exponents
never exceed those of `Δ W`, with equality at `v` exactly when `W` is minimal there, so
`𝔇_{E/K} = (Δ W)` characterises global minimality among integral equations. Integrality is not
optional in that characterisation — translating a globally minimal equation by `r = 1 / 2` leaves
`Δ` alone and destroys integrality, so the ideal identity would hold for an equation that is
neither minimal nor integral.

The obstruction exponents `(v (Δ W) − v (Δ_min,ᵥ)) / 12` of an integral equation, the integral
defect ideal they assemble into, and its class in `ClassGroup O` are not defined here.

## Main definitions

* `WeierstrassCurve.minimalDiscriminantIdeal`: the ideal `∏ᵥ 𝔭ᵥ ^ v (Δ_min,ᵥ)` of `O`.

## Main results

* `WeierstrassCurve.count_span_Δ_eq_localMinimalDiscriminantValuation`: at a prime where the
  equation is minimal, the exponent of `𝔭ᵥ` in `(Δ W)` is `v (Δ_min,ᵥ)`.
* `WeierstrassCurve.localMinimalDiscriminantValuation_le_count_span_Δ`: for an integral equation
  the local minimal exponent never exceeds that of `Δ W`.
* `WeierstrassCurve.minimalDiscriminantIdeal_smul`: the ideal is invariant under a change of
  variables, hence an invariant of the curve rather than of the equation.
* `WeierstrassCurve.hasFiniteMulSupport_pow_localMinimalDiscriminantValuation` and
  `WeierstrassCurve.minimalDiscriminantIdeal_ne_bot`: the defining product is finite and nonzero.
* `WeierstrassCurve.minimalDiscriminantIdeal_eq_span_of_isGlobalMinimal` and
  `WeierstrassCurve.isGlobalMinimal_iff_minimalDiscriminantIdeal_eq_span`: a globally minimal
  equation computes the ideal as `(Δ W)`, and among integral equations that identity holds only
  for the globally minimal ones.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VIII.8.
-/

public section

namespace WeierstrassCurve

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable (O : Type*) [CommRing O] [IsDedekindDomain O]
  {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]

/-- **The discriminant of an equation minimal at `v` has `v`-adic valuation `exp (-v (Δ_min,ᵥ))`.**
This is `valuation_Δ_eq_exp_neg_of_isMinimal_smul` read through the `v`-adic valuation of `O`
rather than through the discrete valuation of `Oᵥ`. -/
theorem valuation_Δ_eq_exp_neg_localMinimalDiscriminantValuation (v : HeightOneSpectrum O)
    (W : WeierstrassCurve K) [W.IsElliptic] {W' : WeierstrassCurve K}
    [IsMinimal (Localization.AtPrime v.asIdeal) W'] (D : VariableChange K) (hD : D • W = W') :
    v.valuation K W'.Δ =
      WithZero.exp
        (-(W.localMinimalDiscriminantValuation (Localization.AtPrime v.asIdeal) : ℤ)) := by
  rw [← v.valuation_maximalIdeal_localizationAtPrime W'.Δ]
  exact W.valuation_Δ_eq_exp_neg_of_isMinimal_smul _ D hD

variable {O}

omit [IsDedekindDomain O] [IsFractionRing O K] in
/-- An integral representative of the discriminant of an elliptic equation is nonzero. -/
private theorem ne_zero_of_algebraMap_eq_Δ {W : WeierstrassCurve K} [W.IsElliptic] {d : O}
    (hd : algebraMap O K d = W.Δ) : d ≠ 0 :=
  fun h => W.isUnit_Δ.ne_zero (by rw [← hd, h, map_zero])

/-- The `v`-adic valuation of a discriminant, in terms of the exponent of `𝔭ᵥ` in the ideal it
generates. -/
private theorem valuation_Δ_eq_exp_neg_count (v : HeightOneSpectrum O) {W : WeierstrassCurve K}
    [W.IsElliptic] {d : O} (hd : algebraMap O K d = W.Δ) :
    v.valuation K W.Δ = WithZero.exp
      (-((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {d})).factors : ℤ)) := by
  rw [← hd, valuation_of_algebraMap, v.intValuation_if_neg (ne_zero_of_algebraMap_eq_Δ hd)]

/-- **At a prime where the equation is minimal, the exponent of `𝔭ᵥ` in the discriminant is
`v (Δ_min,ᵥ)`.** Here `d` is the integral representative of `Δ W`, which exists because a minimal
equation is integral. -/
theorem count_span_Δ_eq_localMinimalDiscriminantValuation (v : HeightOneSpectrum O)
    {W : WeierstrassCurve K} [W.IsElliptic] {d : O} (hd : algebraMap O K d = W.Δ)
    (hv : IsMinimal (Localization.AtPrime v.asIdeal) W) :
    (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {d})).factors =
      W.localMinimalDiscriminantValuation (Localization.AtPrime v.asIdeal) := by
  have := hv -- minimality at `v` is what the next line resolves as an instance
  have hexp := valuation_Δ_eq_exp_neg_localMinimalDiscriminantValuation O v W
    (1 : VariableChange K) (one_smul _ W)
  rw [valuation_Δ_eq_exp_neg_count v hd, WithZero.exp_inj, neg_inj, Nat.cast_inj] at hexp
  exact hexp

/-- **An integral equation has discriminant exponent at least the local minimal one at every
prime.** Minimality maximises the multiplicative valuation of the discriminant, which is to
minimise its exponent. -/
theorem localMinimalDiscriminantValuation_le_count_span_Δ (v : HeightOneSpectrum O)
    {W : WeierstrassCurve K} [W.IsElliptic] [IsIntegral O W] {d : O}
    (hd : algebraMap O K d = W.Δ) :
    W.localMinimalDiscriminantValuation (Localization.AtPrime v.asIdeal) ≤
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {d})).factors := by
  have : IsIntegral (Localization.AtPrime v.asIdeal) W :=
    IsIntegral.of_isScalarTower (R := O) W
  obtain ⟨C, hC⟩ := W.exists_smul_eq_minimal (Localization.AtPrime v.asIdeal)
  have hCinv : C⁻¹ • W.minimal (Localization.AtPrime v.asIdeal) = W := by
    rw [← hC, inv_smul_smul]
  have hle := valuation_Δ_le_of_isMinimal_smul (Localization.AtPrime v.asIdeal) C⁻¹ hCinv
  rw [v.valuation_maximalIdeal_localizationAtPrime, v.valuation_maximalIdeal_localizationAtPrime,
    valuation_Δ_eq_exp_neg_localMinimalDiscriminantValuation O v W C hC,
    valuation_Δ_eq_exp_neg_count v hd, WithZero.exp_le_exp, neg_le_neg_iff, Nat.cast_le] at hle
  exact hle

omit [IsDedekindDomain O] [IsFractionRing O K] in
/-- A power of a height-one prime is the unit ideal only in the trivial case. -/
private theorem pow_asIdeal_eq_one_iff (v : HeightOneSpectrum O) (n : ℕ) :
    v.asIdeal ^ n = 1 ↔ n = 0 := by
  refine ⟨fun hn => by_contra fun hn0 => ?_, fun hn => by rw [hn, pow_zero]⟩
  rw [Ideal.one_eq_top] at hn
  exact v.isPrime.ne_top (top_le_iff.mp (hn ▸ Ideal.pow_le_self hn0))

omit [IsFractionRing O K] in
/-- A family of prime powers bounded by the factorisation of a nonzero ideal has finite support. -/
private theorem hasFiniteMulSupport_pow_asIdeal {I : Ideal O} (hI : I ≠ 0)
    (e : HeightOneSpectrum O → ℕ)
    (he : ∀ v, e v ≤ (Associates.mk v.asIdeal).count (Associates.mk I).factors) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum O => v.asIdeal ^ e v := by
  have hsupp : {v : HeightOneSpectrum O |
      (Associates.mk v.asIdeal).count (Associates.mk I).factors ≠ 0}.Finite := by
    simpa using Filter.eventually_cofinite.mp (Associates.finite_factors hI)
  refine hsupp.subset fun v hv hcount => ?_
  exact hv ((pow_asIdeal_eq_one_iff v _).2 (Nat.le_zero.1 (hcount ▸ he v)))

variable (O)

/-- **The minimal discriminant ideal** `𝔇_{E/K} = ∏ᵥ 𝔭ᵥ ^ v (Δ_min,ᵥ)`: the product over the
height-one primes of `O` of the local minimal discriminants of `W`. The product is finite
(`hasFiniteMulSupport_pow_localMinimalDiscriminantValuation`), since all but finitely many primes
divide no discriminant. -/
noncomputable def minimalDiscriminantIdeal (W : WeierstrassCurve K) [W.IsElliptic] : Ideal O :=
  ∏ᶠ v : HeightOneSpectrum O,
    v.asIdeal ^ W.localMinimalDiscriminantValuation (Localization.AtPrime v.asIdeal)

/-- The defining product of `minimalDiscriminantIdeal`. -/
theorem minimalDiscriminantIdeal_def (W : WeierstrassCurve K) [W.IsElliptic] :
    minimalDiscriminantIdeal O W = ∏ᶠ v : HeightOneSpectrum O,
      v.asIdeal ^ W.localMinimalDiscriminantValuation (Localization.AtPrime v.asIdeal) := (rfl)

/-- **The minimal discriminant ideal is invariant under a change of variables**, so it is an
invariant of the curve and not of the equation presenting it. -/
@[simp]
theorem minimalDiscriminantIdeal_smul (D : VariableChange K) (W : WeierstrassCurve K)
    [W.IsElliptic] :
    minimalDiscriminantIdeal O (D • W) = minimalDiscriminantIdeal O W := by
  simp only [minimalDiscriminantIdeal, localMinimalDiscriminantValuation_smul]

/-- **The product defining the minimal discriminant ideal is finite.** Every equation has an
integral model, whose discriminant is divisible by only finitely many primes, and each local
minimal exponent is at most the exponent there. -/
theorem hasFiniteMulSupport_pow_localMinimalDiscriminantValuation (W : WeierstrassCurve K)
    [W.IsElliptic] :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum O =>
      v.asIdeal ^ W.localMinimalDiscriminantValuation (Localization.AtPrime v.asIdeal) := by
  obtain ⟨C, hC⟩ := exists_smul_isIntegral O W
  have := hC -- the integral model of `W` supplied by the change of variables `C`
  obtain ⟨d, hd⟩ := Δ_integral_of_isIntegral O (C • W)
  refine hasFiniteMulSupport_pow_asIdeal
    (Submodule.span_singleton_eq_bot.mp.mt (ne_zero_of_algebraMap_eq_Δ hd)) _ fun v => ?_
  rw [← localMinimalDiscriminantValuation_smul _ C W]
  exact localMinimalDiscriminantValuation_le_count_span_Δ v hd

/-- **The minimal discriminant ideal is nonzero.** -/
theorem minimalDiscriminantIdeal_ne_bot (W : WeierstrassCurve K) [W.IsElliptic] :
    minimalDiscriminantIdeal O W ≠ 0 := by
  rw [minimalDiscriminantIdeal,
    finprod_eq_prod _ (hasFiniteMulSupport_pow_localMinimalDiscriminantValuation O W)]
  exact Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ v.ne_bot

variable {O}

/-- **A globally minimal equation computes the minimal discriminant ideal as `(Δ W)`.** -/
theorem minimalDiscriminantIdeal_eq_span_of_isGlobalMinimal {W : WeierstrassCurve K}
    [W.IsElliptic] (h : IsGlobalMinimal O W) {d : O} (hd : algebraMap O K d = W.Δ) :
    minimalDiscriminantIdeal O W = Ideal.span {d} := by
  have hspan : Ideal.span {d} ≠ 0 :=
    Submodule.span_singleton_eq_bot.mp.mt (ne_zero_of_algebraMap_eq_Δ hd)
  rw [minimalDiscriminantIdeal, ← Ideal.finprod_heightOneSpectrum_factorization hspan]
  exact finprod_congr fun v =>
    congrArg _ (count_span_Δ_eq_localMinimalDiscriminantValuation v hd (h.isMinimal v)).symm

/-- If the minimal discriminant ideal of an integral equation is already `(Δ W)`, every local
exponent agrees with the exponent in `(Δ W)`. Splitting the factorisation of `(Δ W)` as
`𝔇 · ∏ᵥ 𝔭ᵥ ^ (v (Δ W) − v (Δ_min,ᵥ))` and cancelling `𝔇` leaves the unit ideal, which no proper
prime power divides. -/
private theorem count_eq_localMinimalDiscriminantValuation_of_eq_span {W : WeierstrassCurve K}
    [W.IsElliptic] [IsIntegral O W] {d : O} (hd : algebraMap O K d = W.Δ)
    (h : minimalDiscriminantIdeal O W = Ideal.span {d}) (v : HeightOneSpectrum O) :
    (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {d})).factors =
      W.localMinimalDiscriminantValuation (Localization.AtPrime v.asIdeal) := by
  set c : HeightOneSpectrum O → ℕ := fun w =>
    (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {d})).factors
  set l : HeightOneSpectrum O → ℕ := fun w =>
    W.localMinimalDiscriminantValuation (Localization.AtPrime w.asIdeal)
  have hspan : Ideal.span {d} ≠ 0 :=
    Submodule.span_singleton_eq_bot.mp.mt (ne_zero_of_algebraMap_eq_Δ hd)
  have hle : ∀ w, l w ≤ c w := fun w => localMinimalDiscriminantValuation_le_count_span_Δ w hd
  -- Split the factorisation of `(Δ W)` into `𝔇` and the excess, then cancel `𝔇`.
  have hsplit : Ideal.span {d} = minimalDiscriminantIdeal O W *
      ∏ᶠ w : HeightOneSpectrum O, w.asIdeal ^ (c w - l w) := by
    conv_lhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hspan]
    rw [minimalDiscriminantIdeal, ← finprod_mul_distrib
      (hasFiniteMulSupport_pow_asIdeal hspan l hle)
      (hasFiniteMulSupport_pow_asIdeal hspan _ fun w => Nat.sub_le _ _)]
    exact finprod_congr fun w => by
      rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, ← pow_add,
        Nat.add_sub_cancel' (hle w)]
  have hone : (∏ᶠ w : HeightOneSpectrum O, w.asIdeal ^ (c w - l w)) = 1 :=
    mul_left_cancel₀ (h ▸ hspan) (by rw [mul_one, ← hsplit, h])
  -- The unit ideal has no proper prime power as a factor, so the excess vanishes at every prime.
  refine Nat.le_antisymm (Nat.le_of_sub_eq_zero ?_) (hle v)
  by_contra hk
  have hfin : (Function.mulSupport fun w : HeightOneSpectrum O =>
      w.asIdeal ^ (c w - l w)).Finite :=
    hasFiniteMulSupport_pow_asIdeal hspan _ fun w => Nat.sub_le (c w) (l w)
  have hmem : v ∈ hfin.toFinset := by
    rw [Set.Finite.mem_toFinset, Function.mem_mulSupport]
    exact fun hv => hk ((pow_asIdeal_eq_one_iff v _).1 hv)
  have hdvd : v.asIdeal ^ (c v - l v) ∣ (1 : Ideal O) := by
    rw [← hone, finprod_eq_prod_of_mulSupport_toFinset_subset _ hfin subset_rfl]
    exact Finset.dvd_prod_of_mem _ hmem
  exact hk ((pow_asIdeal_eq_one_iff v _).1
    ((Ideal.isUnit_iff.1 (isUnit_of_dvd_one hdvd)).trans Ideal.one_eq_top.symm))

/-- **Among integral equations, `𝔇_{E/K} = (Δ W)` holds exactly for the globally minimal ones.**
Integrality is not optional: a non-integral change of variables can fix `Δ` while destroying
minimality. -/
theorem isGlobalMinimal_iff_minimalDiscriminantIdeal_eq_span {W : WeierstrassCurve K}
    [W.IsElliptic] [IsIntegral O W] {d : O} (hd : algebraMap O K d = W.Δ) :
    IsGlobalMinimal O W ↔ minimalDiscriminantIdeal O W = Ideal.span {d} := by
  refine ⟨fun h => minimalDiscriminantIdeal_eq_span_of_isGlobalMinimal h hd,
    fun h => IsGlobalMinimal.of_forall_isMinimal fun v => ?_⟩
  have : IsIntegral (Localization.AtPrime v.asIdeal) W :=
    IsIntegral.of_isScalarTower (R := O) W
  obtain ⟨C, hC⟩ := W.exists_smul_eq_minimal (Localization.AtPrime v.asIdeal)
  have hCinv : C⁻¹ • W.minimal (Localization.AtPrime v.asIdeal) = W := by
    rw [← hC, inv_smul_smul]
  refine isMinimal_of_valuation_Δ_eq_of_isMinimal_smul _ C⁻¹ hCinv ?_
  rw [v.valuation_maximalIdeal_localizationAtPrime, v.valuation_maximalIdeal_localizationAtPrime,
    valuation_Δ_eq_exp_neg_localMinimalDiscriminantValuation O v W C hC,
    valuation_Δ_eq_exp_neg_count v hd, WithZero.exp_inj, neg_inj, Nat.cast_inj]
  exact count_eq_localMinimalDiscriminantValuation_of_eq_span hd h v

end WeierstrassCurve

end
