/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite

/-!
# Complements on Dedekind-domain factorization

Facts about `Associates.count` and `FractionalIdeal.count` that Mathlib does not carry, together
with unit-level factorization of invertible fractional ideals and the finiteness, up to units, of
the divisors of a nonzero element. All of them hold in an arbitrary Dedekind domain.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.unitOfPrime`: a height-one prime regarded as an invertible
  fractional ideal.
* `IsDedekindDomain.HeightOneSpectrum.le_count_associates_iff_le_pow`: the multiplicity of `v` in
  a nonzero ideal `J` is at least `k` exactly when `v ^ k` contains `J`. The multiplicity here is
  `Associates.count`, as in Mathlib's `Ideal.count_associates_factors_eq`, and the statement turns
  it into a containment of ideals rather than a divisibility of `Associates`.
* `IsDedekindDomain.exists_finset_forall_dvd_exists_associated`: a nonzero element of a Dedekind
  domain has finitely many divisors up to units, because its principal ideal has finitely many
  ideal divisors.
* `Ideal.hasFiniteMulSupport_asIdeal_pow_of_le_count`: a family of prime powers whose exponents
  are bounded by the multiplicities of a fixed nonzero ideal has finite multiplicative support.
  Mathlib's `Ideal.hasFiniteMulSupport` is the case of the multiplicities themselves; the bounded
  form is what shows that an ideal `∏ᵥ 𝔭ᵥ ^ e v` is a finite product when the exponents are only
  known to be dominated by an actual factorization.
* `Ideal.count_finprod_asIdeal_pow`: an ideal defined as a finite product `∏ᵥ 𝔭ᵥ ^ e v` has
  multiplicity `e v` at `v`. Mathlib's `FractionalIdeal.count_finprod` is the fractional-ideal form
  with integer exponents.
* `FractionalIdeal.hasFiniteMulSupport_zpow_count`: a family of powers indexed by the height one
  primes, with the multiplicities of a fixed fractional ideal as exponents, has finite
  multiplicative support. The bases are an arbitrary family in an arbitrary `DivInvMonoid`, since
  only the vanishing of almost all exponents matters.
* `FractionalIdeal.finprod_unitOfPrime_zpow_count`: unique factorization of an invertible
  fractional ideal as a finite product of powers of the `unitOfPrime`s.
* `FractionalIdeal.units_ext_count`: invertible fractional ideals with the same multiplicities at
  every height one prime are equal.
* `FractionalIdeal.mem_closure_unitOfPrime_of_count_eq_zero`: an invertible fractional ideal
  whose multiplicities vanish outside a set `T` of height one primes lies in the subgroup generated
  by the primes of `T`.
* `FractionalIdeal.count_div`: the multiplicity of `I / J` is the difference of the multiplicities
  of `I` and `J`, for nonzero `I` and `J`. Mathlib's `count` API has `count_mul`, `count_inv`,
  `count_pow` and `count_zpow` but no division form.
* `FractionalIdeal.count_spanSingleton_div`: the same for principal fractional ideals.
* `FractionalIdeal.count_spanSingleton_algebraMap_eq_neg_log_intValuation`: the multiplicity at
  `v` of the principal fractional ideal of `r : A` is `-WithZero.log (v.intValuation r)`.
* `FractionalIdeal.count_spanSingleton_algebraMap_eq_zero_of_notMem`: an element of `A` outside a
  height one prime generates a principal fractional ideal of multiplicity zero at that prime.
* `FractionalIdeal.count_toPrincipalIdeal_eq_neg_log_valuation`: the multiplicity at `v` of the
  principal fractional ideal of `u : Kˣ` is `-WithZero.log (v.valuation K u)`. This links Mathlib's
  `count` and the adic valuation.
* `FractionalIdeal.valuation_le_one_of_mem_of_count_nonneg`: nonnegative multiplicity makes
  every element of a fractional ideal integral at that prime.

`le_count_associates_iff_le_pow` is adapted from Michael Stoll's elliptic-curves formalization
(`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/Basic.lean:381` at
commit `66889eada51a`, Apache 2.0), and the unit-level prime factorization
`FractionalIdeal.finprod_unitOfPrime_zpow_count` from `EllipticCurves/Mathlib/FractionalIdeal.lean`
at the same commit of that repository.
-/
public section

namespace IsDedekindDomain.HeightOneSpectrum

open scoped nonZeroDivisors

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- A height-one prime, regarded as an invertible fractional ideal. -/
noncomputable def unitOfPrime (v : HeightOneSpectrum R) (K : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] : (FractionalIdeal R⁰ K)ˣ :=
  Units.mk0 (v.asIdeal : FractionalIdeal R⁰ K) (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)

/-- The fractional ideal underlying `v.unitOfPrime K` is `v.asIdeal`. -/
@[simp]
theorem coe_unitOfPrime (v : HeightOneSpectrum R) (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K] :
    (v.unitOfPrime K : FractionalIdeal R⁰ K) = v.asIdeal := by
  rw [unitOfPrime]
  exact Units.val_mk0 _

/-- The multiplicity of `v` in a nonzero ideal `J` is at least `k` exactly when `v ^ k` contains
`J`. -/
theorem le_count_associates_iff_le_pow {A : Type*} [CommRing A] [IsDedekindDomain A]
    (v : HeightOneSpectrum A) {J : Ideal A} (hJ : J ≠ ⊥) (k : ℕ) :
    k ≤ (Associates.mk v.asIdeal).count (Associates.mk J).factors ↔ J ≤ v.asIdeal ^ k := by
  rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hJ) v.associates_irreducible,
    ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le]

end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- A nonzero element `n` of a Dedekind domain has only finitely many divisors up to units: there
is a finite set `M` of divisors of `n` such that every divisor of `n` is associated to an element
of `M`. -/
theorem exists_finset_forall_dvd_exists_associated {n : R} (hn : n ≠ 0) :
    ∃ M : Finset R, (∀ μ ∈ M, μ ∣ n) ∧ ∀ μ, μ ∣ n → ∃ μ₀ ∈ M, Associated μ₀ μ := by
  classical
  have hn' : Ideal.span {n} ≠ 0 := by
    rwa [Ideal.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot]
  -- The principal ideals of the divisors of `n` divide `(n)`, and `(n)` has finitely many divisors.
  have : Fintype {I : Ideal R // I ∣ Ideal.span {n}} :=
    UniqueFactorizationMonoid.fintypeSubtypeDvd _ hn'
  have hfin : ((fun μ : R ↦ Ideal.span {μ}) '' {μ | μ ∣ n}).Finite := by
    refine (Set.toFinite {I : Ideal R | I ∣ Ideal.span {n}}).subset ?_
    rintro _ ⟨μ, hμ, rfl⟩
    exact Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr hμ
  obtain ⟨u, hus, hbij⟩ := Set.exists_subset_bijOn {μ : R | μ ∣ n} fun μ ↦ Ideal.span {μ}
  have hu : u.Finite := Set.Finite.of_finite_image (hbij.image_eq ▸ hfin) hbij.injOn
  refine ⟨hu.toFinset, fun μ hμ ↦ hus (hu.mem_toFinset.mp hμ), fun μ hμ ↦ ?_⟩
  obtain ⟨μ₀, hμ₀, he⟩ := hbij.surjOn ⟨μ, hμ, rfl⟩
  exact ⟨μ₀, hu.mem_toFinset.mpr hμ₀, Ideal.span_singleton_eq_span_singleton.mp he⟩

end IsDedekindDomain

namespace Ideal

-- `Ideal.IsDedekindDomain` also exists, so the root namespace has to be named explicitly.
open _root_.IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- **A family of prime powers whose exponents are bounded by the multiplicities of a nonzero
ideal has finite multiplicative support.** This permits products of such prime powers to be
handled as finite products. -/
theorem hasFiniteMulSupport_asIdeal_pow_of_le_count {I : Ideal R} (hI : I ≠ 0)
    (e : HeightOneSpectrum R → ℕ)
    (he : ∀ v, e v ≤ (Associates.mk v.asIdeal).count (Associates.mk I).factors) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum R => v.asIdeal ^ e v := by
  refine (Ideal.hasFiniteMulSupport hI).subset fun v hv => ?_
  simp only [Function.mem_mulSupport, ne_eq, IsDedekindDomain.HeightOneSpectrum.maxPowDividing,
    Ideal.one_eq_top, Ideal.pow_eq_top_iff, v.isPrime.ne_top, false_or] at hv ⊢
  exact fun hcount => hv (Nat.le_zero.1 (hcount ▸ he v))

/-- **The multiplicity of `v` in a finite product `∏ᵥ 𝔭ᵥ ^ e v` is `e v`.** This reads the
exponents of an ideal defined by its prime-power factorisation back off the ideal. -/
theorem count_finprod_asIdeal_pow {e : HeightOneSpectrum R → ℕ}
    (he : Function.HasFiniteMulSupport fun v : HeightOneSpectrum R => v.asIdeal ^ e v)
    (v : HeightOneSpectrum R) :
    (Associates.mk v.asIdeal).count
      (Associates.mk (∏ᶠ w : HeightOneSpectrum R, w.asIdeal ^ e w)).factors = e v := by
  have hexp : ∀ᶠ w : HeightOneSpectrum R in Filter.cofinite, (e w : ℤ) = 0 := by
    rw [Filter.eventually_cofinite]
    refine he.subset fun w hw => ?_
    simp only [Set.mem_ofPred_eq, Nat.cast_eq_zero, Function.mem_mulSupport, ne_eq,
      Ideal.one_eq_top, Ideal.pow_eq_top_iff, w.isPrime.ne_top, false_or] at hw ⊢
    exact hw
  rw [← Nat.cast_inj (R := ℤ),
    ← FractionalIdeal.count_coeIdeal (FractionRing R) v
      (finprod_ne_zero fun w => pow_ne_zero _ w.ne_bot),
    FractionalIdeal.coeIdeal_finprod (nonZeroDivisors R) (FractionRing R) le_rfl]
  simp_rw [FractionalIdeal.coeIdeal_pow, ← zpow_natCast]
  exact FractionalIdeal.count_finprod (FractionRing R) v _ hexp

end Ideal

namespace FractionalIdeal

open IsDedekindDomain

open scoped nonZeroDivisors

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- **A prime-indexed family of powers with the multiplicities of a fractional ideal as exponents
has finite multiplicative support.** Only finitely many primes occur in a fractional ideal, so
only finitely many exponents are nonzero, whatever `DivInvMonoid` the bases live in. -/
lemma hasFiniteMulSupport_zpow_count {G : Type*} [DivInvMonoid G] (I : FractionalIdeal R⁰ K)
    (f : HeightOneSpectrum R → G) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum R ↦ f v ^ count K v I := by
  refine (Filter.eventually_cofinite.mp (finite_factors I)).subset fun v hv hc ↦ ?_
  exact hv (by simp only [hc, zpow_zero])

/-- Unique factorization of an invertible fractional ideal as a product of prime powers. -/
lemma finprod_unitOfPrime_zpow_count (I : (FractionalIdeal R⁰ K)ˣ) :
    I = ∏ᶠ v : HeightOneSpectrum R,
      v.unitOfPrime K ^ count K v (I : FractionalIdeal R⁰ K) := by
  refine Units.ext ?_
  -- Push the coercion to fractional ideals through the product. Only the right-hand side is
  -- rewritten, since `count` also contains a coercion of `I`.
  conv_rhs => rw [← Units.coeHom_apply,
    MonoidHom.map_finprod _ (hasFiniteMulSupport_zpow_count _ _)]
  simp only [Units.coeHom_apply, Units.val_zpow_eq_zpow_val, HeightOneSpectrum.coe_unitOfPrime]
  exact (finprod_heightOneSpectrum_factorization' (K := K)
    (I := (I : FractionalIdeal R⁰ K)) (Units.ne_zero I)).symm

/-- Invertible fractional ideals are equal if their multiplicities agree at every prime. -/
lemma units_ext_count {I J : (FractionalIdeal R⁰ K)ˣ}
    (h : ∀ v, count K v (I : FractionalIdeal R⁰ K) = count K v (J : FractionalIdeal R⁰ K)) :
    I = J := by
  calc
    I = ∏ᶠ v : HeightOneSpectrum R,
        v.unitOfPrime K ^ count K v (I : FractionalIdeal R⁰ K) :=
      finprod_unitOfPrime_zpow_count I
    _ = ∏ᶠ v : HeightOneSpectrum R,
        v.unitOfPrime K ^ count K v (J : FractionalIdeal R⁰ K) :=
      finprod_congr fun v ↦ congrArg (fun n : ℤ ↦ v.unitOfPrime K ^ n) (h v)
    _ = J := (finprod_unitOfPrime_zpow_count J).symm

/-- **An invertible fractional ideal whose multiplicities vanish outside `T` lies in the subgroup
generated by the primes of `T`.** -/
lemma mem_closure_unitOfPrime_of_count_eq_zero {T : Set (HeightOneSpectrum R)}
    {I : (FractionalIdeal R⁰ K)ˣ} (h : ∀ v ∉ T, count K v (I : FractionalIdeal R⁰ K) = 0) :
    I ∈ Subgroup.closure ((fun v : HeightOneSpectrum R ↦ v.unitOfPrime K) '' T) := by
  classical
  have hfin := hasFiniteMulSupport_zpow_count (I : FractionalIdeal R⁰ K) (·.unitOfPrime K)
  rw [finprod_unitOfPrime_zpow_count I,
    finprod_eq_prod_of_mulSupport_toFinset_subset _ hfin subset_rfl]
  refine Subgroup.prod_mem _ fun v hv ↦
    Subgroup.zpow_mem _ (Subgroup.subset_closure (Set.mem_image_of_mem _ ?_)) _
  by_contra hvT
  exact hfin.mem_toFinset.mp hv (by simp only [h v hvT, zpow_zero])

/-- **The multiplicity of a quotient of nonzero fractional ideals is the difference of the
multiplicities.** Mathlib's `count` API has `count_mul`, `count_inv`, `count_pow` and `count_zpow`
but no division form. -/
theorem count_div {A : Type*} [CommRing A] [IsDedekindDomain A] (K : Type*) [Field K] [Algebra A K]
    [IsFractionRing A K] (w : HeightOneSpectrum A) {I J : FractionalIdeal A⁰ K} (hI : I ≠ 0)
    (hJ : J ≠ 0) : count K w (I / J) = count K w I - count K w J := by
  rw [div_eq_mul_inv, count_mul K w hI (inv_ne_zero hJ), count_inv]
  ring

/-- The multiplicity of `x / y` is the difference of the multiplicities of `x` and `y`, for nonzero
`x` and `y`: `count_div` read on principal fractional ideals. -/
theorem count_spanSingleton_div {A : Type*} [CommRing A] [IsDedekindDomain A] (K : Type*) [Field K]
    [Algebra A K] [IsFractionRing A K] (w : HeightOneSpectrum A) {x y : K} (hx : x ≠ 0)
    (hy : y ≠ 0) :
    count K w (spanSingleton A⁰ (x / y)) =
      count K w (spanSingleton A⁰ x) - count K w (spanSingleton A⁰ y) := by
  rw [← spanSingleton_div_spanSingleton, count_div K w (spanSingleton_ne_zero_iff.mpr hx)
    (spanSingleton_ne_zero_iff.mpr hy)]

section PrincipalIdeal

variable {A : Type*} [CommRing A] [IsDedekindDomain A] (K : Type*) [Field K] [Algebra A K]
  [IsFractionRing A K]

/-- **The multiplicity of the principal fractional ideal generated by an element of `A` is the
sign-flipped logarithm of its integer valuation.** For `r = 0` both sides are `0`. -/
theorem count_spanSingleton_algebraMap_eq_neg_log_intValuation (v : HeightOneSpectrum A) (r : A) :
    count K v (spanSingleton A⁰ (algebraMap A K r)) = -WithZero.log (v.intValuation r) := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp [count_zero]
  have hspan : (Ideal.span {r} : Ideal A) ≠ 0 := by
    simpa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hr
  rw [← coeIdeal_span_singleton (S := A⁰) (P := K) r, count_coeIdeal K v hspan,
    v.intValuation_if_neg hr, WithZero.log_exp]
  ring

/-- The principal fractional ideal generated by an element outside a height-one prime has
zero multiplicity at that prime. -/
theorem count_spanSingleton_algebraMap_eq_zero_of_notMem (v : HeightOneSpectrum A) {a : A}
    (ha : a ∉ v.asIdeal) :
    count K v (spanSingleton A⁰ (algebraMap A K a)) = 0 := by
  simpa [HeightOneSpectrum.intValuation_eq_one_iff.mpr ha] using
    count_spanSingleton_algebraMap_eq_neg_log_intValuation K v a

/-- **The multiplicity of a principal fractional ideal is the sign-flipped logarithm of the
valuation.** Stated at the multiplicative-units level `u : Kˣ`, matching Mathlib's
`toPrincipalIdeal A K : Kˣ →* _`. -/
theorem count_toPrincipalIdeal_eq_neg_log_valuation (v : HeightOneSpectrum A) (u : Kˣ) :
    count K v (toPrincipalIdeal A K u : FractionalIdeal A⁰ K) =
      -WithZero.log (v.valuation K (u : K)) := by
  obtain ⟨n, d, hnd⟩ := IsLocalization.exists_mk'_eq A⁰ (u : K)
  have hn : n ≠ 0 := by
    intro hn
    apply u.ne_zero
    rw [← hnd, hn, IsFractionRing.mk'_eq_div, map_zero, zero_div]
  have hd : (d : A) ≠ 0 := nonZeroDivisors.ne_zero d.2
  have hval : v.valuation K (u : K) = v.intValuation n / v.intValuation (d : A) :=
    hnd ▸ v.valuation_of_mk'
  rw [hval, coe_toPrincipalIdeal, ← hnd, IsFractionRing.mk'_eq_div,
    count_spanSingleton_div K v ((not_congr IsFractionRing.to_map_eq_zero_iff).mpr hn)
      ((not_congr IsFractionRing.to_map_eq_zero_iff).mpr hd),
    count_spanSingleton_algebraMap_eq_neg_log_intValuation K v n,
    count_spanSingleton_algebraMap_eq_neg_log_intValuation K v (d : A),
    WithZero.log_div (v.intValuation_ne_zero n hn) (v.intValuation_ne_zero (d : A) hd)]
  ring

end PrincipalIdeal

/-- Nonnegative multiplicity at a prime makes every element of a fractional ideal integral
at that prime. -/
theorem valuation_le_one_of_mem_of_count_nonneg {R K : Type*} [CommRing R]
    [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (I : FractionalIdeal R⁰ K) (v : HeightOneSpectrum R) (hI : 0 ≤ count K v I)
    {x : K} (hx : x ∈ I) : v.valuation K x ≤ 1 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  have hcount := count_mono K v (spanSingleton_ne_zero_iff.mpr hx0)
    (spanSingleton_le_iff_mem.mpr hx)
  have hprincipal := count_toPrincipalIdeal_eq_neg_log_valuation K v (Units.mk0 x hx0)
  rw [coe_toPrincipalIdeal, Units.val_mk0] at hprincipal
  rw [hprincipal] at hcount
  exact WithZero.le_exp_of_log_le (neg_nonneg.mp (hI.trans hcount))

end FractionalIdeal

end
