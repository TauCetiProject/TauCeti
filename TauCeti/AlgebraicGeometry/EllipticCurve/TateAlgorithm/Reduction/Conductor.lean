/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.DiscriminantIdeal
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Reduction.Curve
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Radical.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Weierstrass
import TauCeti.RingTheory.DedekindDomain.Factorization

/-!
# The algorithmic conductor of an elliptic curve over a Dedekind domain

Let `O` be a Dedekind domain with fraction field `K` whose localisations at height-one primes have
perfect residue fields, and let `W` be an elliptic curve over `K`. At each height-one prime `v`,
Tate's algorithm on a minimal equation over `Oᵥ = Localization.AtPrime v.asIdeal` produces the
algorithmic Ogg exponent `fᵥ = v (Δ_min,ᵥ) − mᵥ + 1`
(`WeierstrassCurve.algorithmicOggExponent`). This file assembles those exponents into a single
ideal of `O`,

`𝔑 = ∏ᵥ 𝔭ᵥ ^ fᵥ`,

the **algorithmic conductor** of `W` (Silverman, *Advanced Topics*, IV.10). By Ogg's formula it
is the conductor of `W`; that identification with the ramification-theoretic conductor is not made
here, which is why the ideal is named after the algorithm that computes it.

The exponent `fᵥ` is `0` at good reduction, `1` at multiplicative reduction and at least `2` at
additive reduction, and it never exceeds `v (Δ_min,ᵥ)`. Accordingly, the primes dividing `𝔑` are
exactly the primes of bad reduction, `𝔑` divides the minimal discriminant ideal, `𝔑 = 1` exactly
when `W` has good reduction everywhere, and `𝔑` is squarefree exactly when `W` is semistable,
in which case `𝔑` is the radical of the minimal discriminant ideal.
Like the minimal discriminant ideal, `𝔑` depends only on the `K`-isomorphism class of `W`.

## Main definitions

* `WeierstrassCurve.algorithmicConductor`: the ideal `∏ᵥ 𝔭ᵥ ^ fᵥ` of `O`.

## Main results

* `WeierstrassCurve.hasFiniteMulSupport_pow_algorithmicOggExponent` and
  `WeierstrassCurve.algorithmicConductor_ne_bot`: the defining product is finite and nonzero.
* `WeierstrassCurve.count_algorithmicConductor`: the exponent of `𝔭ᵥ` in `𝔑` is `fᵥ`.
* `WeierstrassCurve.algorithmicConductor_smul`: `𝔑` is invariant under a change of variables.
* `WeierstrassCurve.pow_dvd_algorithmicConductor_iff`: `𝔭ᵥ ^ n ∣ 𝔑` exactly when `n ≤ fᵥ`.
* `WeierstrassCurve.dvd_algorithmicConductor_iff` and
  `WeierstrassCurve.dvd_algorithmicConductor_iff_dvd_minimalDiscriminantIdeal`: `𝔭ᵥ ∣ 𝔑` exactly
  when `W` has bad reduction at `v`, that is, when `𝔭ᵥ` divides the minimal discriminant ideal.
* `WeierstrassCurve.algorithmicConductor_dvd_minimalDiscriminantIdeal`: `𝔑` divides the minimal
  discriminant ideal.
* `WeierstrassCurve.algorithmicConductor_eq_top_iff`: `𝔑 = 1` exactly when `W` has good reduction
  at every height-one prime.
* `WeierstrassCurve.isSemistable_iff_squarefree_algorithmicConductor` and
  `WeierstrassCurve.isSemistable_iff_algorithmicConductor_eq_radical`: `W` is semistable exactly
  when `𝔑` is squarefree, equivalently when `𝔑` is the radical of the minimal discriminant ideal.
* `WeierstrassCurve.IsGlobalMinimal.dvd_algorithmicConductor_iff` and
  `WeierstrassCurve.IsGlobalMinimal.sq_dvd_algorithmicConductor_iff`: for a globally minimal
  equation, `𝔭ᵥ ∣ 𝔑` exactly when `v` contains its discriminant, and `𝔭ᵥ² ∣ 𝔑` exactly when `v`
  also contains its `c₄`.
* `WeierstrassCurve.one_lt_absNorm_algorithmicConductor_iff`: over `ℚ`, the norm of `𝔑` exceeds `1`
  exactly when `W` has bad reduction at some prime.
* `WeierstrassCurve.pow_dvd_absNorm_algorithmicConductor_iff`: over `ℚ`, the exponent of `p` in the
  norm of `𝔑` is the algorithmic Ogg exponent at `(p)`.
* `WeierstrassCurve.IsGlobalMinimal.dvd_absNorm_algorithmicConductor_iff` and
  `WeierstrassCurve.IsGlobalMinimal.sq_dvd_absNorm_algorithmicConductor_iff`: over `ℚ`, a prime `p`
  divides the norm of `𝔑` exactly when it divides the discriminant of a globally minimal integral
  equation, and `p²` does exactly when `p` also divides its `c₄`.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, IV.9–IV.11.
* J. Tate, *Algorithm for determining the type of a singular fibre in an elliptic pencil*, in
  *Modular Functions of One Variable IV*, LNM 476 (1975), 33–52.
-/

public section

namespace WeierstrassCurve

open IsLocalRing IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable (O : Type*) [CommRing O] [IsDedekindDomain O]
  [∀ v : HeightOneSpectrum O, PerfectField (ResidueField (Localization.AtPrime v.asIdeal))]
  {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]

/-- **The product defining the algorithmic conductor is finite.** Each algorithmic Ogg exponent is
bounded by the local minimal discriminant exponent, and those have finite support. -/
theorem hasFiniteMulSupport_pow_algorithmicOggExponent (W : WeierstrassCurve K) [W.IsElliptic] :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum O =>
      v.asIdeal ^ W.algorithmicOggExponent (Localization.AtPrime v.asIdeal) := by
  refine Ideal.hasFiniteMulSupport_asIdeal_pow_of_le_count
    (minimalDiscriminantIdeal_ne_bot O W) _ fun v => ?_
  rw [count_minimalDiscriminantIdeal_eq_localMinimalDiscriminantValuation]
  exact W.algorithmicOggExponent_le_localMinimalDiscriminantValuation

/-- **The algorithmic conductor** `∏ᵥ 𝔭ᵥ ^ fᵥ` of an elliptic curve over the fraction field of a
Dedekind domain `O`: the product over the height-one primes of `O` of the prime powers whose
exponents are the algorithmic Ogg exponents `fᵥ = v (Δ_min,ᵥ) − mᵥ + 1` read off Tate's algorithm.
The product is finite (`hasFiniteMulSupport_pow_algorithmicOggExponent`). -/
noncomputable def algorithmicConductor (W : WeierstrassCurve K) [W.IsElliptic] : Ideal O :=
  ∏ᶠ v : HeightOneSpectrum O,
    v.asIdeal ^ W.algorithmicOggExponent (Localization.AtPrime v.asIdeal)

/-- The defining prime-power factorisation of the algorithmic conductor. Outside this module the
body of `algorithmicConductor` is not exposed, so this is the interface for unfolding it. -/
theorem algorithmicConductor_def (W : WeierstrassCurve K) [W.IsElliptic] :
    algorithmicConductor O W = ∏ᶠ v : HeightOneSpectrum O,
      v.asIdeal ^ W.algorithmicOggExponent (Localization.AtPrime v.asIdeal) := by
  rw [algorithmicConductor]

/-- **The algorithmic conductor is nonzero.** -/
theorem algorithmicConductor_ne_bot (W : WeierstrassCurve K) [W.IsElliptic] :
    algorithmicConductor O W ≠ ⊥ :=
  finprod_ne_zero fun v => pow_ne_zero _ v.ne_bot

/-- **The exponent of `𝔭ᵥ` in the algorithmic conductor is the algorithmic Ogg exponent at `v`.**
This reads the local exponents back off the ideal, so results about the conductor can be proved
without unfolding the defining product. -/
@[simp]
theorem count_algorithmicConductor (W : WeierstrassCurve K) [W.IsElliptic]
    (v : HeightOneSpectrum O) :
    (Associates.mk v.asIdeal).count (Associates.mk (algorithmicConductor O W)).factors =
      W.algorithmicOggExponent (Localization.AtPrime v.asIdeal) :=
  Ideal.count_finprod_asIdeal_pow (hasFiniteMulSupport_pow_algorithmicOggExponent O W) v

/-- **The algorithmic conductor is invariant under a change of variables**, so it is an invariant
of the curve and not of the equation presenting it. -/
@[simp]
theorem algorithmicConductor_smul (D : VariableChange K) (W : WeierstrassCurve K)
    [W.IsElliptic] : algorithmicConductor O (D • W) = algorithmicConductor O W := by
  simp only [algorithmicConductor_def, algorithmicOggExponent_smul]

variable {O}

/-- **`𝔭ᵥ ^ n` divides the algorithmic conductor exactly when `n` is at most the algorithmic Ogg
exponent at `v`.** -/
theorem pow_dvd_algorithmicConductor_iff (W : WeierstrassCurve K) [W.IsElliptic]
    (v : HeightOneSpectrum O) (n : ℕ) :
    v.asIdeal ^ n ∣ algorithmicConductor O W ↔
      n ≤ W.algorithmicOggExponent (Localization.AtPrime v.asIdeal) := by
  rw [← count_algorithmicConductor,
    le_count_associates_iff_le_pow v (algorithmicConductor_ne_bot O W), Ideal.dvd_iff_le]

/-- **A prime divides the algorithmic conductor exactly when the curve has bad reduction there.**
-/
theorem dvd_algorithmicConductor_iff (W : WeierstrassCurve K) [W.IsElliptic]
    (v : HeightOneSpectrum O) :
    v.asIdeal ∣ algorithmicConductor O W ↔
      ¬ (W.minimal (Localization.AtPrime v.asIdeal)).HasGoodReduction
        (Localization.AtPrime v.asIdeal) := by
  have h := pow_dvd_algorithmicConductor_iff W v 1
  rw [pow_one] at h
  exact h.trans W.algorithmicOggExponent_pos_iff

/-- **The algorithmic conductor and the minimal discriminant ideal have the same prime divisors**,
the primes of bad reduction. -/
theorem dvd_algorithmicConductor_iff_dvd_minimalDiscriminantIdeal (W : WeierstrassCurve K)
    [W.IsElliptic] (v : HeightOneSpectrum O) :
    v.asIdeal ∣ algorithmicConductor O W ↔ v.asIdeal ∣ minimalDiscriminantIdeal O W := by
  rw [dvd_algorithmicConductor_iff, dvd_minimalDiscriminantIdeal_iff]

/-- **The algorithmic conductor divides the minimal discriminant ideal**, as each algorithmic Ogg
exponent is at most the valuation of the local minimal discriminant. -/
theorem algorithmicConductor_dvd_minimalDiscriminantIdeal (W : WeierstrassCurve K)
    [W.IsElliptic] : algorithmicConductor O W ∣ minimalDiscriminantIdeal O W := by
  rw [Ideal.dvd_iff_le, algorithmicConductor_def, minimalDiscriminantIdeal_def]
  exact finprod_le_finprod (hasFiniteMulSupport_pow_localMinimalDiscriminantValuation O W)
    (hasFiniteMulSupport_pow_algorithmicOggExponent O W) fun v =>
      Ideal.pow_le_pow_right W.algorithmicOggExponent_le_localMinimalDiscriminantValuation

/-- **The algorithmic conductor is trivial exactly when the curve has good reduction at every
height-one prime.** -/
theorem algorithmicConductor_eq_top_iff (W : WeierstrassCurve K) [W.IsElliptic] :
    algorithmicConductor O W = ⊤ ↔ ∀ v : HeightOneSpectrum O,
      (W.minimal (Localization.AtPrime v.asIdeal)).HasGoodReduction
        (Localization.AtPrime v.asIdeal) := by
  refine ⟨fun h v => ?_, fun h => ?_⟩
  · by_contra hv
    rw [← dvd_algorithmicConductor_iff, h, Ideal.dvd_iff_le, top_le_iff] at hv
    exact v.isPrime.ne_top hv
  · rw [algorithmicConductor_def, ← Ideal.one_eq_top]
    simp_rw [(algorithmicOggExponent_eq_zero_iff _).2 (h _), pow_zero, finprod_one]

/-- **A curve is semistable exactly when its algorithmic conductor is squarefree**, since the
algorithmic Ogg exponent is at least `2` exactly at additive reduction. -/
theorem isSemistable_iff_squarefree_algorithmicConductor (W : WeierstrassCurve K)
    [W.IsElliptic] : IsSemistable O W ↔ Squarefree (algorithmicConductor O W) := by
  rw [squarefree_iff_irreducible_sq_not_dvd_of_ne_zero
    (by rw [Ideal.zero_eq_bot]; exact algorithmicConductor_ne_bot O W)]
  refine ⟨fun h x hx => ?_,
    fun h => IsSemistable.of_forall_not_hasAdditiveReduction fun v => ?_⟩
  · -- An irreducible ideal is a nonzero prime ideal, that is, a height-one prime.
    obtain ⟨v, rfl⟩ : ∃ v : HeightOneSpectrum O, v.asIdeal = x := ⟨.ofPrime hx.prime, rfl⟩
    rw [← sq, pow_dvd_algorithmicConductor_iff, two_le_algorithmicOggExponent_iff]
    exact h.not_hasAdditiveReduction v
  · rw [← two_le_algorithmicOggExponent_iff, ← pow_dvd_algorithmicConductor_iff, sq]
    exact h _ v.irreducible

open UniqueFactorizationMonoid in
/-- **A curve is semistable exactly when its algorithmic conductor is the radical of its minimal
discriminant ideal**, that is, the product of its primes of bad reduction. -/
theorem isSemistable_iff_algorithmicConductor_eq_radical (W : WeierstrassCurve K) [W.IsElliptic] :
    IsSemistable O W ↔ algorithmicConductor O W = radical (minimalDiscriminantIdeal O W) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hN := (isSemistable_iff_squarefree_algorithmicConductor W).1 h
    have hN₀ : algorithmicConductor O W ≠ 0 := algorithmicConductor_ne_bot O W
    have h𝔇₀ := minimalDiscriminantIdeal_ne_bot O W
    refine dvd_antisymm ((dvd_radical_iff hN.isRadical h𝔇₀).2
      (algorithmicConductor_dvd_minimalDiscriminantIdeal W)) ?_
    -- Every prime factor of the minimal discriminant ideal is a prime of bad reduction, which
    -- divides the conductor.
    rw [radical_dvd_iff_primeFactors_subset hN₀]
    intro x hx
    rw [mem_primeFactors, mem_normalizedFactors_iff' h𝔇₀] at hx
    rw [mem_primeFactors, mem_normalizedFactors_iff' hN₀]
    obtain ⟨hirr, hnorm, hdvd⟩ := hx
    obtain ⟨v, rfl⟩ : ∃ v : HeightOneSpectrum O, v.asIdeal = x := ⟨.ofPrime hirr.prime, rfl⟩
    exact ⟨hirr, hnorm, (dvd_algorithmicConductor_iff_dvd_minimalDiscriminantIdeal W v).2 hdvd⟩
  · rw [isSemistable_iff_squarefree_algorithmicConductor, h]
    exact squarefree_radical

/-- **A prime divides the algorithmic conductor of a globally minimal equation exactly when it
contains the discriminant** of its integral model, that is, when the curve has bad reduction
there. -/
theorem IsGlobalMinimal.dvd_algorithmicConductor_iff {W : WeierstrassCurve K} [W.IsElliptic]
    (h : IsGlobalMinimal O W) {W₀ : WeierstrassCurve O} (hW₀ : W₀.baseChange K = W)
    (v : HeightOneSpectrum O) : v.asIdeal ∣ algorithmicConductor O W ↔ W₀.Δ ∈ v.asIdeal := by
  rw [dvd_algorithmicConductor_iff_dvd_minimalDiscriminantIdeal,
    minimalDiscriminantIdeal_eq_span_of_isGlobalMinimal h (algebraMap_Δ_of_baseChange_eq hW₀),
    Ideal.dvd_span_singleton]

/-- **The square of a prime divides the algorithmic conductor of a globally minimal equation
exactly when the prime contains both the discriminant and `c₄`** of its integral model, that is,
when the curve has additive reduction there. -/
theorem IsGlobalMinimal.sq_dvd_algorithmicConductor_iff {W : WeierstrassCurve K} [W.IsElliptic]
    (h : IsGlobalMinimal O W) {W₀ : WeierstrassCurve O} (hW₀ : W₀.baseChange K = W)
    (v : HeightOneSpectrum O) :
    v.asIdeal ^ 2 ∣ algorithmicConductor O W ↔ W₀.Δ ∈ v.asIdeal ∧ W₀.c₄ ∈ v.asIdeal := by
  rw [pow_dvd_algorithmicConductor_iff, two_le_algorithmicOggExponent_iff,
    h.hasAdditiveReduction_minimal_iff hW₀]

section Rat

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]

/-- **The algorithmic conductor of a curve over `ℚ` exceeds `1` exactly when the curve has bad
reduction at some prime.** This is the condition under which the Szpiro ratio is defined. -/
theorem one_lt_absNorm_algorithmicConductor_iff :
    1 < Ideal.absNorm (algorithmicConductor ℤ E) ↔ ∃ v : IsDedekindDomain.HeightOneSpectrum ℤ,
      ¬ (E.minimal (Localization.AtPrime v.asIdeal)).HasGoodReduction
        (Localization.AtPrime v.asIdeal) := by
  have h0 : Ideal.absNorm (algorithmicConductor ℤ E) ≠ 0 :=
    Ideal.absNorm_eq_zero_iff.not.2 (algorithmicConductor_ne_bot ℤ E)
  rw [← not_iff_not, not_exists, not_lt, Nat.le_one_iff_eq_zero_or_eq_one, or_iff_right h0,
    Ideal.absNorm_eq_one_iff, algorithmicConductor_eq_top_iff]
  simp only [not_not]

variable {E}

/-- **The local exponents of the algorithmic conductor over `ℚ` are `p`-adic valuations of its
norm**: for the height-one prime `v = (p)` of `ℤ`, `p ^ n` divides `N = |𝔑|` exactly when
`n ≤ f_p`. -/
theorem pow_dvd_absNorm_algorithmicConductor_iff {p : ℕ} {v : HeightOneSpectrum ℤ}
    (hv : v.asIdeal = Ideal.span {(p : ℤ)}) (n : ℕ) :
    p ^ n ∣ Ideal.absNorm (algorithmicConductor ℤ E) ↔
      n ≤ E.algorithmicOggExponent (Localization.AtPrime v.asIdeal) := by
  rw [← pow_dvd_algorithmicConductor_iff E v n, hv, Ideal.span_singleton_pow,
    ← Int.natCast_dvd_natCast, Nat.cast_pow, ← Ideal.span_singleton_dvd_span_singleton_iff_dvd,
    Int.ideal_span_absNorm_eq_self]

/-- A rational prime `p` gives the height-one prime `(p)` of `ℤ`. -/
private theorem exists_heightOneSpectrum_asIdeal_eq_span {p : ℕ} (hp : p.Prime) :
    ∃ v : HeightOneSpectrum ℤ, v.asIdeal = Ideal.span {(p : ℤ)} :=
  ⟨.ofPrime (Ideal.prime_span_singleton_iff.2 (Nat.prime_iff_prime_int.1 hp)),
    HeightOneSpectrum.ofPrime_asIdeal _⟩

/-- **A prime divides the conductor of a globally minimal equation over `ℚ` exactly when it
divides the discriminant** of its integral model, that is, when the curve has bad reduction
there. -/
theorem IsGlobalMinimal.dvd_absNorm_algorithmicConductor_iff (h : IsGlobalMinimal ℤ E)
    {W₀ : WeierstrassCurve ℤ} (hW₀ : W₀.baseChange ℚ = E) {p : ℕ} (hp : p.Prime) :
    p ∣ Ideal.absNorm (algorithmicConductor ℤ E) ↔ (p : ℤ) ∣ W₀.Δ := by
  obtain ⟨v, hv⟩ := exists_heightOneSpectrum_asIdeal_eq_span hp
  rw [← pow_one p, pow_dvd_absNorm_algorithmicConductor_iff hv, ← pow_dvd_algorithmicConductor_iff,
    pow_one, h.dvd_algorithmicConductor_iff hW₀, hv, Ideal.mem_span_singleton, pow_one]

/-- **The square of a prime divides the conductor of a globally minimal equation over `ℚ`
exactly when the prime divides both the discriminant and `c₄`** of its integral model, that is,
when the curve has additive reduction there. -/
theorem IsGlobalMinimal.sq_dvd_absNorm_algorithmicConductor_iff (h : IsGlobalMinimal ℤ E)
    {W₀ : WeierstrassCurve ℤ} (hW₀ : W₀.baseChange ℚ = E) {p : ℕ} (hp : p.Prime) :
    p ^ 2 ∣ Ideal.absNorm (algorithmicConductor ℤ E) ↔ (p : ℤ) ∣ W₀.Δ ∧ (p : ℤ) ∣ W₀.c₄ := by
  obtain ⟨v, hv⟩ := exists_heightOneSpectrum_asIdeal_eq_span hp
  rw [pow_dvd_absNorm_algorithmicConductor_iff hv, ← pow_dvd_algorithmicConductor_iff,
    h.sq_dvd_algorithmicConductor_iff hW₀, hv, Ideal.mem_span_singleton, Ideal.mem_span_singleton]

end Rat

end WeierstrassCurve

end
