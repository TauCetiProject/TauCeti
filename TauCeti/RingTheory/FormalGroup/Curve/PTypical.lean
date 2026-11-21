/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Curve.Rescale
import Mathlib.Data.Nat.Factors
import TauCeti.Algebra.Algebra.NatCast

/-!
# `p`-typical curves and Cartier's typicalization projector

Let `F` be a commutative one-dimensional formal group law over a commutative ring `R`, and let
`p` be a natural number (in applications a prime). A curve `γ ∈ F.Curve` is **`p`-typical**
(`FormalGroup.Curve.IsPTypical`) if it is killed by Cartier's Frobenius operator `f_q` at every
prime `q ≠ p`. Because `f_{m q} = f_m ∘ f_q`, a `p`-typical curve is automatically killed by `f_n`
for every nonzero `n` not of the form `p^m`, and in particular for every `n > 1` coprime to `p`.
The `p`-typical curves form an additive subgroup `FormalGroup.pTypicalCurveSubgroup F p` of
`F.Curve`, stable under all Frobenius operators `f_n`, all curve homotheties `[c]`, and (when `p`
is prime) the Verschiebung operators `V_{p^k}`. Over a `ℚ`-algebra with `p` prime, `γ` is
`p`-typical if and only if its formal logarithm `log_F(γ(T))` has all coefficients outside the
degrees `p^m` equal to zero.

When every prime `q ≠ p` is invertible in `R` (for instance over any `ℚ`-algebra, any local ring of
residue characteristic `p`, or any `ℤ_{(p)}`-algebra), the finite-stage partial products
`FormalGroup.partialPTypicalProjectorCurve` of the elementary Cartier projectors
`1 - V_q [q]⁻¹ f_q` at primes `q ≠ p` stabilize coefficientwise because `V_q` raises order to at
least `q`. Their coefficientwise limit defines **Cartier's `p`-typicalization projector**
`FormalGroup.pTypicalProjectorCurve F p hunit : F.Curve →+ F.Curve`. Over an arbitrary commutative
ring `R` in which primes `q ≠ p` are units (including rings with `p`-torsion),
`pTypicalProjectorCurve`:

* commutes with base change, formal-group homomorphisms, curve homotheties `[c]`, and (when `p` is
  prime) `f_{p^k}` and `V_{p^k}`;
* has image equal to the subgroup of `p`-typical curves, fixes a curve if and only if it is
  `p`-typical, and is idempotent;
* annihilates `V_n γ` whenever `n` has a prime divisor `q ≠ p` (in particular whenever `n > 1` is
  coprime to `p`);
* preserves divisibility by `X ^ m` (so its degree-`k` coefficient depends only on coefficients up
  to degree `k`), preserves the linear coefficient `coeff 1` (and more generally any degree
  strictly below every prime `q ≠ p`), deletes precisely the degrees divisible by primes `q ≠ p` on
  `𝔾ₐ`, and over a `ℚ`-algebra with `p` prime deletes precisely the non-`p`-power coefficients of
  `log_F(γ(T))`.

## Main definitions

* `FormalGroup.Curve.IsPTypical`: predicate that `f_q γ = 0` for every prime `q ≠ p`.
* `FormalGroup.pTypicalCurveSubgroup`: the additive subgroup of `p`-typical curves on `F`.
* `FormalGroup.partialPTypicalProjectorCurve`: finite-stage partial product of the elementary
  Cartier projectors at primes `q ≤ n` with `q ≠ p`.
* `FormalGroup.pTypicalProjectorCurve`: Cartier's `p`-typicalization projector on `F.Curve` when
  every prime `q ≠ p` is invertible in `R`.

## Main results

* `FormalGroup.Curve.isPTypical_iff_frobeniusCurve_eq_zero_of_forall_pow_ne` and
  `FormalGroup.Curve.isPTypical_iff_frobeniusCurve_eq_zero_of_coprime`: characterizations of
  `p`-typical curves via Frobenius outside powers of `p` and via indices coprime to `p`.
* `FormalGroup.Curve.isPTypical_iff_forall_coeff_subst_log_eq_zero`: rational logarithm
  characterization of `p`-typical curves when `p` is prime.
* `FormalGroup.coeff_pTypicalProjectorCurve_eq_partialPTypicalProjectorCurve`,
  `FormalGroup.X_pow_dvd_toPowerSeries_pTypicalProjectorCurve`, and
  `FormalGroup.coeff_pTypicalProjectorCurve_congr`: finite-stage stabilization and degree
  congruence for `pTypicalProjectorCurve` over arbitrary commutative rings.
* `FormalGroup.isPTypical_pTypicalProjectorCurve`,
  `FormalGroup.pTypicalProjectorCurve_eq_self_iff`, and
  `FormalGroup.pTypicalProjectorCurve_pTypicalProjectorCurve`: image, fixed-point characterization,
  and idempotency of Cartier's `p`-typicalization projector over arbitrary commutative rings with
  primes `q ≠ p` invertible.
* `FormalGroup.coeff_toPowerSeries_pTypicalProjectorCurve_𝔾ₐ` and
  `FormalGroup.coeff_subst_pTypicalProjectorCurve_log`: action of `pTypicalProjectorCurve` on `𝔾ₐ`
  and on the formal logarithm over a `ℚ`-algebra.

## References

* P. Cartier, *Modules associés à un groupe formel commutatif. Courbes typiques*, C. R. Acad. Sci.
  Paris Sér. A-B 265 (1967), A129–A132.
* D. Quillen, *On the formal group laws of unoriented and complex cobordism theory*, Bull. Amer.
  Math. Soc. 75 (1969), 1293–1298.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapter III, §16.3.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Academic Press (1986),
  Appendix A2.1.20–A2.1.21.
-/

public section

namespace FormalGroup

variable {R S : Type*} [CommRing R] [CommRing S]

private theorem exists_prime_ne_and_dvd_zero (p : ℕ) :
    ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ q ∣ 0 := by
  by_cases h2 : 2 = p
  · exact ⟨3, Nat.prime_three, by omega, dvd_zero 3⟩
  · exact ⟨2, Nat.prime_two, h2, dvd_zero 2⟩

private theorem exists_prime_ne_and_dvd_of_coprime {n p : ℕ} (hn1 : 1 < n)
    (hcop : n.Coprime p) : ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ q ∣ n := by
  obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hn1.ne'
  exact ⟨q, hq, fun hqp ↦ hq.ne_one (Nat.eq_one_of_dvd_coprimes hcop hqdvd (hqp ▸ dvd_rfl)),
    hqdvd⟩

private theorem exists_prime_ne_and_dvd_of_forall_pow_ne {k p : ℕ}
    (hpow : ∀ m : ℕ, p ^ m ≠ k) : ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ q ∣ k := by
  rcases eq_or_ne k 0 with rfl | hk0
  · exact exists_prime_ne_and_dvd_zero p
  · by_contra hall
    push Not at hall
    exact hpow k.primeFactorsList.length
      (Nat.eq_prime_pow_of_unique_prime_dvd hk0 fun {q} hq hdvd ↦ by
        by_contra hqp
        exact hall q hq hqp hdvd).symm

private theorem forall_pow_ne_of_prime_ne_dvd {p q k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hqp : q ≠ p) (hdvd : q ∣ k) (m : ℕ) : p ^ m ≠ k :=
  fun hm ↦ hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow (hm ▸ hdvd)))

private theorem exists_prime_ne_and_dvd_iff_forall_pow_ne {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (∃ q : ℕ, q.Prime ∧ q ≠ p ∧ q ∣ k) ↔ ∀ m : ℕ, p ^ m ≠ k :=
  ⟨fun ⟨_, hq, hqp, hdvd⟩ ↦ forall_pow_ne_of_prime_ne_dvd hp hq hqp hdvd,
    exists_prime_ne_and_dvd_of_forall_pow_ne⟩

/-! ### `p`-typical curves -/

namespace Curve

section IsPTypical

variable {F : FormalGroup R} [F.IsComm]

/-- A curve `γ` on a commutative formal group law `F` is **`p`-typical** if it is killed by
Cartier's Frobenius operator `f_q` at every prime `q ≠ p`. -/
def IsPTypical (γ : F.Curve) (p : ℕ) : Prop :=
  ∀ q : ℕ, ∀ hq : q.Prime, q ≠ p → F.frobeniusCurve q hq.ne_zero γ = 0

/-- Unfold `FormalGroup.Curve.IsPTypical`. -/
theorem isPTypical_def (γ : F.Curve) (p : ℕ) :
    γ.IsPTypical p ↔
      ∀ q : ℕ, ∀ hq : q.Prime, q ≠ p → F.frobeniusCurve q hq.ne_zero γ = 0 :=
  (Iff.rfl)

/-- A `p`-typical curve is killed by `f_n` whenever `n` has a prime divisor `q ≠ p`. -/
theorem IsPTypical.frobeniusCurve_eq_zero_of_prime_dvd {γ : F.Curve} {p : ℕ} (hγ : γ.IsPTypical p)
    {q n : ℕ} (hq : q.Prime) (hqp : q ≠ p) (hdvd : q ∣ n) (hn : n ≠ 0) :
    F.frobeniusCurve n hn γ = 0 := by
  obtain ⟨m, rfl⟩ := exists_eq_mul_left_of_dvd hdvd
  have hm : m ≠ 0 := left_ne_zero_of_mul hn
  rw [← F.frobeniusCurve_frobeniusCurve hm hq.ne_zero, hγ q hq hqp, map_zero]

/-- A `p`-typical curve is killed by `f_n` for every `n > 1` coprime to `p`. -/
theorem IsPTypical.frobeniusCurve_eq_zero_of_coprime {γ : F.Curve} {p : ℕ} (hγ : γ.IsPTypical p)
    {n : ℕ} (hn1 : 1 < n) (hcop : n.Coprime p) (hn : n ≠ 0) :
    F.frobeniusCurve n hn γ = 0 := by
  obtain ⟨q, hq, hqp, hqdvd⟩ := exists_prime_ne_and_dvd_of_coprime hn1 hcop
  exact hγ.frobeniusCurve_eq_zero_of_prime_dvd hq hqp hqdvd hn

/-- When `p` is prime, `γ` is `p`-typical if and only if `f_n γ = 0` for every `n > 1` coprime to
`p`. -/
theorem isPTypical_iff_frobeniusCurve_eq_zero_of_coprime (γ : F.Curve) {p : ℕ} (hp : p.Prime) :
    γ.IsPTypical p ↔
      ∀ n : ℕ, 1 < n → n.Coprime p → ∀ hn : n ≠ 0, F.frobeniusCurve n hn γ = 0 := by
  refine ⟨fun hγ n hn1 hcop hn ↦ hγ.frobeniusCurve_eq_zero_of_coprime hn1 hcop hn, fun h q hq hqp ↦
    h q hq.one_lt ((Nat.coprime_primes hq hp).mpr hqp) hq.ne_zero⟩

/-- A `p`-typical curve is killed by `f_n` at every nonzero index `n` that is not a power of
`p`. -/
theorem IsPTypical.frobeniusCurve_eq_zero_of_forall_pow_ne {γ : F.Curve} {p : ℕ}
    (hγ : γ.IsPTypical p) {n : ℕ} (hn : n ≠ 0) (hpow : ∀ m : ℕ, p ^ m ≠ n) :
    F.frobeniusCurve n hn γ = 0 := by
  obtain ⟨q, hq, hqp, hdvd⟩ := exists_prime_ne_and_dvd_of_forall_pow_ne hpow
  exact hγ.frobeniusCurve_eq_zero_of_prime_dvd hq hqp hdvd hn

/-- A curve `γ` is `p`-typical if and only if `f_n γ = 0` for every nonzero `n` that is not a
power of `p`. -/
theorem isPTypical_iff_frobeniusCurve_eq_zero_of_forall_pow_ne (γ : F.Curve) (p : ℕ) :
    γ.IsPTypical p ↔
      ∀ n : ℕ, ∀ hn : n ≠ 0, (∀ m : ℕ, p ^ m ≠ n) → F.frobeniusCurve n hn γ = 0 :=
  ⟨fun hγ _ hn hpow ↦ hγ.frobeniusCurve_eq_zero_of_forall_pow_ne hn hpow,
    fun h q hq hqp ↦ h q hq.ne_zero fun _ hm ↦ hqp (hq.pow_eq_iff.mp hm).1.symm⟩

/-- The zero curve is `p`-typical. -/
@[simp]
theorem isPTypical_zero (p : ℕ) : (0 : F.Curve).IsPTypical p :=
  fun q hq _ ↦ map_zero (F.frobeniusCurve q hq.ne_zero)

/-- Sums of `p`-typical curves are `p`-typical. -/
theorem IsPTypical.add {γ₁ γ₂ : F.Curve} {p : ℕ} (h₁ : γ₁.IsPTypical p) (h₂ : γ₂.IsPTypical p) :
    (γ₁ + γ₂).IsPTypical p :=
  fun q hq hqp ↦ by rw [map_add, h₁ q hq hqp, h₂ q hq hqp, _root_.add_zero]

/-- Negatives of `p`-typical curves are `p`-typical. -/
theorem IsPTypical.neg {γ : F.Curve} {p : ℕ} (h : γ.IsPTypical p) : (-γ).IsPTypical p :=
  fun q hq hqp ↦ by rw [map_neg, h q hq hqp, neg_zero]

/-- Differences of `p`-typical curves are `p`-typical. -/
theorem IsPTypical.sub {γ₁ γ₂ : F.Curve} {p : ℕ} (h₁ : γ₁.IsPTypical p) (h₂ : γ₂.IsPTypical p) :
    (γ₁ - γ₂).IsPTypical p :=
  fun q hq hqp ↦ by rw [map_sub, h₁ q hq hqp, h₂ q hq hqp, sub_zero]

/-- Natural multiples of `p`-typical curves are `p`-typical. -/
theorem IsPTypical.nsmul {γ : F.Curve} {p : ℕ} (h : γ.IsPTypical p) (n : ℕ) :
    (n • γ).IsPTypical p :=
  fun q hq hqp ↦ by rw [map_nsmul, h q hq hqp, smul_zero]

/-- Integer multiples of `p`-typical curves are `p`-typical. -/
theorem IsPTypical.zsmul {γ : F.Curve} {p : ℕ} (h : γ.IsPTypical p) (n : ℤ) :
    (n • γ).IsPTypical p :=
  fun q hq hqp ↦ by rw [map_zsmul, h q hq hqp, zsmul_zero]

/-- Applying any Frobenius operator `f_n` preserves `p`-typicality. -/
theorem IsPTypical.frobeniusCurve {γ : F.Curve} {p : ℕ} (h : γ.IsPTypical p) (n : ℕ)
    (hn : n ≠ 0) : (F.frobeniusCurve n hn γ).IsPTypical p := by
  intro q hq hqp
  rw [F.frobeniusCurve_frobeniusCurve, F.frobeniusCurve_congr (Nat.mul_comm q n) _
      (mul_ne_zero hn hq.ne_zero),
    ← F.frobeniusCurve_frobeniusCurve hn hq.ne_zero, h q hq hqp, map_zero]

/-- When `p` is prime, Verschiebung `V_{p^k}` preserves `p`-typicality. -/
theorem IsPTypical.verschiebungCurve_pow {γ : F.Curve} {p : ℕ} (hp : p.Prime) (h : γ.IsPTypical p)
    (k : ℕ) : (F.verschiebungCurve (p ^ k) (pow_ne_zero k hp.ne_zero) γ).IsPTypical p := by
  intro q hq hqp
  have hcop : q.Coprime (p ^ k) := ((Nat.coprime_primes hq hp).mpr hqp).pow_right k
  rw [F.frobeniusCurve_verschiebungCurve_of_coprime hq.ne_zero (pow_ne_zero k hp.ne_zero) hcop,
    h q hq hqp, map_zero]

/-- Rescaling the curve parameter preserves `p`-typicality. -/
theorem IsPTypical.rescaleCurve {γ : F.Curve} {p : ℕ} (h : γ.IsPTypical p) (c : R) :
    (F.rescaleCurve c γ).IsPTypical p :=
  fun q hq hqp ↦ by rw [F.frobeniusCurve_rescaleCurve, h q hq hqp, map_zero]

/-- Every elementary Cartier projector preserves `p`-typicality. -/
theorem IsPTypical.cartierProjectorCurve {γ : F.Curve} {p : ℕ} (h : γ.IsPTypical p) (n : ℕ)
    (hn : n ≠ 0) (hunit : IsUnit (n : R)) :
    (F.cartierProjectorCurve n hn hunit γ).IsPTypical p := by
  by_cases hdvd : ∃ q', q'.Prime ∧ q' ≠ p ∧ q' ∣ n
  · obtain ⟨q', hq', hq'p, hq'n⟩ := hdvd
    rw [F.cartierProjectorCurve_eq_self n hn hunit
      (h.frobeniusCurve_eq_zero_of_prime_dvd hq' hq'p hq'n hn)]
    exact h
  · push Not at hdvd
    intro q hq hqp
    have hcop : q.Coprime n := hq.coprime_iff_not_dvd.mpr (hdvd q hq hqp)
    rw [F.frobeniusCurve_cartierProjectorCurve_of_coprime hq.ne_zero hn hunit hcop,
      h q hq hqp, map_zero]

/-- Base change preserves `p`-typicality of curves. -/
theorem IsPTypical.map {γ : F.Curve} {p : ℕ} (h : γ.IsPTypical p) (φ : R →+* S) :
    (Curve.map φ γ).IsPTypical p :=
  fun q hq hqp ↦ by rw [← F.map_frobeniusCurve φ q hq.ne_zero, h q hq hqp, map_zero]

/-- Base change along an injective ring homomorphism reflects and preserves `p`-typicality of
curves. -/
@[simp]
theorem isPTypical_map_iff {φ : R →+* S} (hφ : Function.Injective φ) {γ : F.Curve} {p : ℕ} :
    (Curve.map φ γ).IsPTypical p ↔ γ.IsPTypical p := by
  refine ⟨fun h q hq hqp ↦ Curve.map_injective hφ ?_, fun h ↦ h.map φ⟩
  rw [F.map_frobeniusCurve φ q hq.ne_zero, h q hq hqp, map_zero]

/-- On the additive formal group law, any curve supported in the degrees `p^m` is `p`-typical when
`p` is prime. -/
theorem isPTypical_𝔾ₐ_of_forall_coeff_eq_zero {p : ℕ} (hp : p.Prime)
    {γ : (𝔾ₐ (R := R)).Curve}
    (hγ : ∀ k : ℕ, (∀ m : ℕ, p ^ m ≠ k) → PowerSeries.coeff k γ.toPowerSeries = 0) :
    γ.IsPTypical p := by
  intro q hq hqp
  apply Curve.ext
  ext k
  rw [toPowerSeries_frobeniusCurve_𝔾ₐ, toPowerSeries_zero, PowerSeries.coeff_smul,
    PowerSeries.coeff_cartier, Nat.add_zero, map_zero,
    hγ (q * k) (forall_pow_ne_of_prime_ne_dvd hp hq hqp (dvd_mul_right q k)), smul_zero]

/-- On the additive formal group law, if every prime `q ≠ p` is left-regular in `R`, then a
`p`-typical curve has zero coefficients outside the degrees `p^m`. -/
theorem IsPTypical.coeff_toPowerSeries_𝔾ₐ_eq_zero {γ : (𝔾ₐ (R := R)).Curve} {p : ℕ}
    (hγ : γ.IsPTypical p) (hreg : ∀ q : ℕ, q.Prime → q ≠ p → IsLeftRegular (q : R))
    {k : ℕ} (hk : ∀ m : ℕ, p ^ m ≠ k) :
    PowerSeries.coeff k γ.toPowerSeries = 0 := by
  obtain ⟨q, hq, hqp, m, rfl⟩ := exists_prime_ne_and_dvd_of_forall_pow_ne hk
  have hcoeff := congrArg (PowerSeries.coeff m ∘ Curve.toPowerSeries) (hγ q hq hqp)
  simp only [Function.comp_apply, toPowerSeries_frobeniusCurve_𝔾ₐ, toPowerSeries_zero,
    PowerSeries.coeff_smul, PowerSeries.coeff_cartier, Nat.add_zero, smul_eq_mul,
    map_zero] at hcoeff
  exact (hreg q hq hqp) (hcoeff.trans (mul_zero _).symm)

end IsPTypical

end Curve

/-- Homomorphisms of commutative formal group laws preserve `p`-typical curves. -/
theorem _root_.TauCeti.FormalGroupHom.isPTypical_mapCurve {F G : FormalGroup R}
    [F.IsComm] [G.IsComm] (f : TauCeti.FormalGroupHom F G) {γ : F.Curve} {p : ℕ}
    (h : γ.IsPTypical p) : (f.mapCurve γ).IsPTypical p :=
  fun q hq hqp ↦ by rw [← f.mapCurve_frobeniusCurve q hq.ne_zero, h q hq hqp, map_zero]

/-- The forward homomorphism of an isomorphism of commutative formal group laws preserves and
reflects `p`-typical curves. -/
@[simp]
theorem _root_.TauCeti.FormalGroupIso.isPTypical_mapCurve_toHom_iff {F G : FormalGroup R}
    [F.IsComm] [G.IsComm] (e : TauCeti.FormalGroupIso F G) {γ : F.Curve} {p : ℕ} :
    (e.toHom.mapCurve γ).IsPTypical p ↔ γ.IsPTypical p := by
  refine ⟨fun h ↦ ?_, e.toHom.isPTypical_mapCurve⟩
  simpa only [← e.curveEquiv_apply, ← e.curveEquiv_symm_apply, AddEquiv.symm_apply_apply] using
    e.invHom.isPTypical_mapCurve h

/-- The inverse homomorphism of an isomorphism of commutative formal group laws preserves and
reflects `p`-typical curves. -/
@[simp]
theorem _root_.TauCeti.FormalGroupIso.isPTypical_mapCurve_invHom_iff {F G : FormalGroup R}
    [F.IsComm] [G.IsComm] (e : TauCeti.FormalGroupIso F G) {γ : G.Curve} {p : ℕ} :
    (e.invHom.mapCurve γ).IsPTypical p ↔ γ.IsPTypical p := by
  rw [← e.symm_toHom, e.symm.isPTypical_mapCurve_toHom_iff]

/-- Isomorphisms of commutative formal group laws preserve and reflect `p`-typical curves. -/
theorem _root_.TauCeti.FormalGroupIso.isPTypical_curveEquiv_iff {F G : FormalGroup R}
    [F.IsComm] [G.IsComm] (e : TauCeti.FormalGroupIso F G) {γ : F.Curve} {p : ℕ} :
    (e.curveEquiv γ).IsPTypical p ↔ γ.IsPTypical p := by
  rw [e.curveEquiv_apply, e.isPTypical_mapCurve_toHom_iff]

/-- Over a `ℚ`-algebra, the formal logarithm of a `p`-typical curve vanishes outside the degrees
`p^m`. -/
theorem Curve.IsPTypical.coeff_subst_log_eq_zero [Algebra ℚ R] {F : FormalGroup R} [F.IsComm]
    {γ : F.Curve} {p : ℕ} (hγ : γ.IsPTypical p) {k : ℕ} (hk : ∀ m : ℕ, p ^ m ≠ k) :
    PowerSeries.coeff k (PowerSeries.subst γ.toPowerSeries F.log) = 0 := by
  simpa only [TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries] using
    (F.logHom.isPTypical_mapCurve hγ).coeff_toPowerSeries_𝔾ₐ_eq_zero
      (fun _ hq _ ↦ (TauCeti.isUnit_natCast_of_ne_zero hq.ne_zero).isRegular.left) hk

/-- Over a `ℚ`-algebra, when `p` is prime, a curve `γ` on `F` is `p`-typical if and only if
`log_F(γ(T))` has no nonzero coefficients outside the degrees `p^m`. -/
theorem Curve.isPTypical_iff_forall_coeff_subst_log_eq_zero [Algebra ℚ R] {F : FormalGroup R}
    [F.IsComm] {p : ℕ} (hp : p.Prime) (γ : F.Curve) :
    γ.IsPTypical p ↔
      ∀ k : ℕ, (∀ m : ℕ, p ^ m ≠ k) →
        PowerSeries.coeff k (PowerSeries.subst γ.toPowerSeries F.log) = 0 := by
  refine ⟨fun hγ k hk ↦ hγ.coeff_subst_log_eq_zero hk, fun h ↦ ?_⟩
  rw [← F.logIso.isPTypical_curveEquiv_iff]
  apply Curve.isPTypical_𝔾ₐ_of_forall_coeff_eq_zero hp
  simpa only [TauCeti.FormalGroupIso.curveEquiv_apply, logIso_toHom,
    TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries] using h

/-- The additive subgroup of `p`-typical curves on a commutative formal group law `F`. -/
noncomputable def pTypicalCurveSubgroup (F : FormalGroup R) [F.IsComm] (p : ℕ) :
    AddSubgroup F.Curve where
  carrier := {γ | γ.IsPTypical p}
  zero_mem' := Curve.isPTypical_zero p
  add_mem' h₁ h₂ := h₁.add h₂
  neg_mem' h := h.neg

/-- Membership in `FormalGroup.pTypicalCurveSubgroup` is `FormalGroup.Curve.IsPTypical`. -/
@[simp]
theorem mem_pTypicalCurveSubgroup (F : FormalGroup R) [F.IsComm] (p : ℕ) {γ : F.Curve} :
    γ ∈ F.pTypicalCurveSubgroup p ↔ γ.IsPTypical p :=
  (Iff.rfl)

/-- The subgroup of `p`-typical curves is the intersection of the Frobenius kernels `ker f_q` over
all primes `q ≠ p`. -/
theorem pTypicalCurveSubgroup_eq_iInf_ker (F : FormalGroup R) [F.IsComm] (p : ℕ) :
    F.pTypicalCurveSubgroup p =
      ⨅ (q : ℕ) (hq : q.Prime) (_ : q ≠ p), (F.frobeniusCurve q hq.ne_zero).ker := by
  ext γ
  simp [Curve.isPTypical_def, AddSubgroup.mem_iInf]

/-! ### Cartier's `p`-typicalization projector -/

section Projector

variable (F : FormalGroup R) [F.IsComm]

/-- Finite-stage partial product of the elementary Cartier projectors `1 - V_q [q]⁻¹ f_q` over
primes `q ≤ n` with `q ≠ p`. -/
noncomputable def partialPTypicalProjectorCurve (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) : ℕ → F.Curve →+ F.Curve
  | 0 => AddMonoidHom.id F.Curve
  | n + 1 =>
    if h : (n + 1).Prime ∧ n + 1 ≠ p then
      (F.cartierProjectorCurve (n + 1) (Nat.succ_ne_zero n) (hunit (n + 1) h.1 h.2)).comp
        (partialPTypicalProjectorCurve p hunit n)
    else
      partialPTypicalProjectorCurve p hunit n

/-- Stage `0` of `FormalGroup.partialPTypicalProjectorCurve` is the identity on curves. -/
@[simp]
theorem partialPTypicalProjectorCurve_zero (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    F.partialPTypicalProjectorCurve p hunit 0 = AddMonoidHom.id F.Curve :=
  (rfl)

/-- Recursive step of `FormalGroup.partialPTypicalProjectorCurve` at stage `n + 1`. -/
theorem partialPTypicalProjectorCurve_succ (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (n : ℕ) :
    F.partialPTypicalProjectorCurve p hunit (n + 1) =
      if h : (n + 1).Prime ∧ n + 1 ≠ p then
        (F.cartierProjectorCurve (n + 1) (Nat.succ_ne_zero n) (hunit (n + 1) h.1 h.2)).comp
          (F.partialPTypicalProjectorCurve p hunit n)
      else
        F.partialPTypicalProjectorCurve p hunit n :=
  (rfl)

/-- At a prime stage `n + 1 ≠ p`, `FormalGroup.partialPTypicalProjectorCurve` composes with the
elementary Cartier projector at `n + 1`. -/
theorem partialPTypicalProjectorCurve_succ_of_prime_ne (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {n : ℕ} (hq : (n + 1).Prime)
    (hqp : n + 1 ≠ p) :
    F.partialPTypicalProjectorCurve p hunit (n + 1) =
      (F.cartierProjectorCurve (n + 1) (Nat.succ_ne_zero n) (hunit (n + 1) hq hqp)).comp
        (F.partialPTypicalProjectorCurve p hunit n) := by
  rw [partialPTypicalProjectorCurve_succ, dite_eq_left ⟨hq, hqp⟩]

/-- At a non-prime stage `n + 1`, `FormalGroup.partialPTypicalProjectorCurve` is unchanged. -/
theorem partialPTypicalProjectorCurve_succ_of_not_prime (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {n : ℕ} (hn : ¬ (n + 1).Prime) :
    F.partialPTypicalProjectorCurve p hunit (n + 1) =
      F.partialPTypicalProjectorCurve p hunit n := by
  rw [partialPTypicalProjectorCurve_succ, dite_eq_right (fun h ↦ hn h.1)]

/-- At stage `n + 1 = p`, `FormalGroup.partialPTypicalProjectorCurve` is unchanged. -/
theorem partialPTypicalProjectorCurve_succ_of_eq (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {n : ℕ} (hn : n + 1 = p) :
    F.partialPTypicalProjectorCurve p hunit (n + 1) =
      F.partialPTypicalProjectorCurve p hunit n := by
  rw [partialPTypicalProjectorCurve_succ, dite_eq_right (fun h ↦ h.2 hn)]

/-- Advancing `FormalGroup.partialPTypicalProjectorCurve` from stage `n` to `n + 1` leaves all
coefficients of degree `k ≤ n` unchanged. -/
theorem coeff_partialPTypicalProjectorCurve_succ_of_le (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {k n : ℕ} (hk : k ≤ n) (γ : F.Curve) :
    PowerSeries.coeff k (F.partialPTypicalProjectorCurve p hunit (n + 1) γ).toPowerSeries =
      PowerSeries.coeff k (F.partialPTypicalProjectorCurve p hunit n γ).toPowerSeries := by
  rw [partialPTypicalProjectorCurve_succ]
  split_ifs with h
  · exact F.coeff_cartierProjectorCurve_of_lt (n + 1) (Nat.succ_ne_zero n)
      (hunit (n + 1) h.1 h.2) (Nat.lt_succ_of_le hk) _
  · rfl

/-- For `k ≤ m`, the degree-`k` coefficient of `FormalGroup.partialPTypicalProjectorCurve`
stabilizes by stage `k`. -/
theorem coeff_partialPTypicalProjectorCurve_of_le (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {k m : ℕ} (hkm : k ≤ m) (γ : F.Curve) :
    PowerSeries.coeff k (F.partialPTypicalProjectorCurve p hunit m γ).toPowerSeries =
      PowerSeries.coeff k (F.partialPTypicalProjectorCurve p hunit k γ).toPowerSeries :=
  Nat.le_induction rfl
    (fun _ hkn ih ↦ (F.coeff_partialPTypicalProjectorCurve_succ_of_le p hunit hkn γ).trans ih) m
    hkm

/-- **Cartier's `p`-typicalization projector** on curves of a commutative formal group law `F`,
when every prime `q ≠ p` is invertible in `R`. It is the coefficientwise limit of the finite
products of the elementary Cartier projectors `1 - V_q [q]⁻¹ f_q` over primes `q ≠ p`. -/
noncomputable def pTypicalProjectorCurve (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) : F.Curve →+ F.Curve where
  toFun γ :=
    { toPowerSeries := PowerSeries.mk fun k ↦
        PowerSeries.coeff k (F.partialPTypicalProjectorCurve p hunit k γ).toPowerSeries
      constantCoeff_toPowerSeries := by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
        exact (F.partialPTypicalProjectorCurve p hunit 0 γ).coeff_zero_toPowerSeries }
  map_zero' := Curve.ext <| PowerSeries.ext fun k ↦ by
    simp
  map_add' γ₁ γ₂ := Curve.ext <| PowerSeries.ext fun k ↦ by
    simp only [PowerSeries.coeff_mk, map_add]
    exact Curve.coeff_add_congr
      (fun i hi ↦ by
        rw [PowerSeries.coeff_mk]
        exact F.coeff_partialPTypicalProjectorCurve_of_le p hunit hi γ₁)
      (fun i hi ↦ by
        rw [PowerSeries.coeff_mk]
        exact F.coeff_partialPTypicalProjectorCurve_of_le p hunit hi γ₂)

/-- In degree `k ≤ m`, Cartier's `p`-typicalization projector agrees with the `m`-th finite-stage
partial projector `FormalGroup.partialPTypicalProjectorCurve`. -/
theorem coeff_pTypicalProjectorCurve_eq_partialPTypicalProjectorCurve (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {k m : ℕ} (hkm : k ≤ m) (γ : F.Curve) :
    PowerSeries.coeff k (F.pTypicalProjectorCurve p hunit γ).toPowerSeries =
      PowerSeries.coeff k (F.partialPTypicalProjectorCurve p hunit m γ).toPowerSeries := by
  dsimp only [pTypicalProjectorCurve, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [PowerSeries.coeff_mk]
  exact (F.coeff_partialPTypicalProjectorCurve_of_le p hunit hkm γ).symm

/-- Below every prime `q ≠ p`, Cartier's `p`-typicalization projector leaves all curve coefficients
unchanged. -/
theorem coeff_pTypicalProjectorCurve_of_forall_prime_gt (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {k : ℕ}
    (hk : ∀ q : ℕ, q.Prime → q ≠ p → k < q) (γ : F.Curve) :
    PowerSeries.coeff k (F.pTypicalProjectorCurve p hunit γ).toPowerSeries =
      PowerSeries.coeff k γ.toPowerSeries := by
  have hpart : ∀ n ≤ k, F.partialPTypicalProjectorCurve p hunit n γ = γ := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [partialPTypicalProjectorCurve_succ]
      split_ifs with h
      · exact absurd (hk (n + 1) h.1 h.2) (by omega)
      · exact ih (Nat.le_of_succ_le hn)
  rw [F.coeff_pTypicalProjectorCurve_eq_partialPTypicalProjectorCurve p hunit (le_refl k),
    hpart k (le_refl k)]

/-- Cartier's `p`-typicalization projector preserves the linear coefficient of every curve. -/
@[simp]
theorem coeff_one_pTypicalProjectorCurve (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    PowerSeries.coeff 1 (F.pTypicalProjectorCurve p hunit γ).toPowerSeries =
      PowerSeries.coeff 1 γ.toPowerSeries :=
  F.coeff_pTypicalProjectorCurve_of_forall_prime_gt p hunit (fun _ hq _ ↦ hq.one_lt) γ

/-- At `p = 2`, Cartier's `2`-typicalization projector also preserves the quadratic coefficient. -/
@[simp]
theorem coeff_two_pTypicalProjectorCurve_two
    (hunit : ∀ q : ℕ, q.Prime → q ≠ 2 → IsUnit (q : R)) (γ : F.Curve) :
    PowerSeries.coeff 2 (F.pTypicalProjectorCurve 2 hunit γ).toPowerSeries =
      PowerSeries.coeff 2 γ.toPowerSeries :=
  F.coeff_pTypicalProjectorCurve_of_forall_prime_gt 2 hunit
    (fun _ hq hq2 ↦ lt_of_le_of_ne hq.two_le hq2.symm) γ

/-- Base change commutes with the finite-stage partial `p`-typicalization projectors. -/
theorem map_partialPTypicalProjectorCurve (φ : R →+* S) (p : ℕ)
    (hR : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (n : ℕ) (γ : F.Curve) :
    Curve.map φ (F.partialPTypicalProjectorCurve p hR n γ) =
      (F.map φ).partialPTypicalProjectorCurve p
        (fun q hq hqp ↦ by simpa using (hR q hq hqp).map φ) n (Curve.map φ γ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [partialPTypicalProjectorCurve_succ]
    split_ifs with h
    · rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, F.map_cartierProjectorCurve, ih]
    · exact ih

/-- Base change commutes with Cartier's `p`-typicalization projector. -/
theorem map_pTypicalProjectorCurve (φ : R →+* S) (p : ℕ)
    (hR : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    Curve.map φ (F.pTypicalProjectorCurve p hR γ) =
      (F.map φ).pTypicalProjectorCurve p
        (fun q hq hqp ↦ by simpa using (hR q hq hqp).map φ) (Curve.map φ γ) := by
  ext k
  rw [Curve.toPowerSeries_map, PowerSeries.coeff_map,
    F.coeff_pTypicalProjectorCurve_eq_partialPTypicalProjectorCurve p hR (le_refl k),
    (F.map φ).coeff_pTypicalProjectorCurve_eq_partialPTypicalProjectorCurve p _ (le_refl k),
    ← F.map_partialPTypicalProjectorCurve φ p hR k γ, Curve.toPowerSeries_map,
    PowerSeries.coeff_map]

/-- Homomorphisms of commutative formal group laws commute with the finite-stage partial
`p`-typicalization projectors. -/
theorem _root_.TauCeti.FormalGroupHom.mapCurve_partialPTypicalProjectorCurve
    {F G : FormalGroup R} [F.IsComm] [G.IsComm] (f : TauCeti.FormalGroupHom F G) (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (n : ℕ) (γ : F.Curve) :
    f.mapCurve (F.partialPTypicalProjectorCurve p hunit n γ) =
      G.partialPTypicalProjectorCurve p hunit n (f.mapCurve γ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [partialPTypicalProjectorCurve_succ]
    split_ifs with h
    · rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, f.mapCurve_cartierProjectorCurve, ih]
    · exact ih

/-- Homomorphisms of commutative formal group laws commute with Cartier's `p`-typicalization
projector. -/
theorem _root_.TauCeti.FormalGroupHom.mapCurve_pTypicalProjectorCurve {F G : FormalGroup R}
    [F.IsComm] [G.IsComm] (f : TauCeti.FormalGroupHom F G) (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    f.mapCurve (F.pTypicalProjectorCurve p hunit γ) =
      G.pTypicalProjectorCurve p hunit (f.mapCurve γ) := by
  ext k
  have hdvd : PowerSeries.X ^ (k + 1) ∣
      (F.pTypicalProjectorCurve p hunit γ).toPowerSeries -
        (F.partialPTypicalProjectorCurve p hunit k γ).toPowerSeries :=
    PowerSeries.X_pow_dvd_iff.mpr fun i hi ↦ by
      rw [map_sub, F.coeff_pTypicalProjectorCurve_eq_partialPTypicalProjectorCurve p hunit
          (Nat.lt_succ_iff.mp hi),
        sub_self]
  have hsub := PowerSeries.X_pow_dvd_subst_sub_subst
    (F.pTypicalProjectorCurve p hunit γ).constantCoeff_toPowerSeries hdvd f.toPowerSeries
  have hk := PowerSeries.X_pow_dvd_iff.mp hsub k (Nat.lt_succ_self k)
  rw [map_sub, sub_eq_zero] at hk
  rw [TauCeti.FormalGroupHom.toPowerSeries_mapCurve, hk,
    ← TauCeti.FormalGroupHom.toPowerSeries_mapCurve,
    f.mapCurve_partialPTypicalProjectorCurve p hunit k γ,
    G.coeff_pTypicalProjectorCurve_eq_partialPTypicalProjectorCurve p hunit (le_refl k)]

/-- Cartier's `p`-typicalization projector commutes with rescaling the curve parameter. -/
theorem pTypicalProjectorCurve_rescaleCurve (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (c : R) (γ : F.Curve) :
    F.pTypicalProjectorCurve p hunit (F.rescaleCurve c γ) =
      F.rescaleCurve c (F.pTypicalProjectorCurve p hunit γ) := by
  have hpart : ∀ n : ℕ, F.partialPTypicalProjectorCurve p hunit n (F.rescaleCurve c γ) =
      F.rescaleCurve c (F.partialPTypicalProjectorCurve p hunit n γ) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [partialPTypicalProjectorCurve_succ]
      split_ifs with h
      · rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ih,
          F.cartierProjectorCurve_rescaleCurve]
      · exact ih
  ext k
  rw [F.coeff_pTypicalProjectorCurve_eq_partialPTypicalProjectorCurve p hunit (le_refl k), hpart k,
    toPowerSeries_rescaleCurve, toPowerSeries_rescaleCurve, PowerSeries.coeff_rescale,
    PowerSeries.coeff_rescale,
    F.coeff_pTypicalProjectorCurve_eq_partialPTypicalProjectorCurve p hunit (le_refl k)]

private theorem coeff_toPowerSeries_partialPTypicalProjectorCurve_𝔾ₐ (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (n k : ℕ)
    (γ : (𝔾ₐ (R := R)).Curve) :
    PowerSeries.coeff k
        ((𝔾ₐ (R := R)).partialPTypicalProjectorCurve p hunit n γ).toPowerSeries =
      if ∃ q ≤ n, q.Prime ∧ q ≠ p ∧ q ∣ k then 0
      else PowerSeries.coeff k γ.toPowerSeries := by
  induction n with
  | zero =>
    have hfalse : ¬ ∃ q ≤ 0, q.Prime ∧ q ≠ p ∧ q ∣ k := by
      rintro ⟨q, hq0, hq, -⟩
      exact absurd hq.pos (by omega)
    rw [ite_eq_right hfalse]
    rfl
  | succ n ih =>
    have hcart (h : (n + 1).Prime ∧ n + 1 ≠ p) (δ : (𝔾ₐ (R := R)).Curve) :
        PowerSeries.coeff k
            ((𝔾ₐ (R := R)).cartierProjectorCurve (n + 1) (Nat.succ_ne_zero n)
              (hunit (n + 1) h.1 h.2) δ).toPowerSeries =
          if (n + 1) ∣ k then 0 else PowerSeries.coeff k δ.toPowerSeries := by
      rw [toPowerSeries_cartierProjectorCurve_𝔾ₐ, map_sub, PowerSeries.coeff_expand]
      split_ifs with hdvd
      · rw [PowerSeries.coeff_cartier, Nat.add_zero, Nat.mul_div_cancel' hdvd, sub_self]
      · rw [sub_zero]
    rw [partialPTypicalProjectorCurve_succ]
    split_ifs with h hle hle
    · rw [AddMonoidHom.comp_apply, hcart h, ih]
      split_ifs with hdvd hex
      · rfl
      · rfl
      · exfalso
        obtain ⟨q, hqn, hq, hqp, hqk⟩ := hle
        rcases Nat.of_le_succ hqn with hqn' | rfl
        · exact hex ⟨q, hqn', hq, hqp, hqk⟩
        · exact hdvd hqk
    · rw [AddMonoidHom.comp_apply, hcart h, ih]
      have hndvd : ¬ (n + 1) ∣ k := fun hdvd ↦ hle ⟨n + 1, le_refl _, h.1, h.2, hdvd⟩
      have hn : ¬ ∃ q ≤ n, q.Prime ∧ q ≠ p ∧ q ∣ k := fun ⟨q, hqn, hq, hqp, hqk⟩ ↦
        hle ⟨q, Nat.le_succ_of_le hqn, hq, hqp, hqk⟩
      rw [ite_eq_right hndvd, ite_eq_right hn]
    · rw [ih]
      have hex : ∃ q ≤ n, q.Prime ∧ q ≠ p ∧ q ∣ k := by
        obtain ⟨q, hqn, hq, hqp, hqk⟩ := hle
        rcases Nat.of_le_succ hqn with hqn' | rfl
        · exact ⟨q, hqn', hq, hqp, hqk⟩
        · exact absurd ⟨hq, hqp⟩ h
      rw [ite_eq_left hex]
    · rw [ih]
      have hn : ¬ ∃ q ≤ n, q.Prime ∧ q ≠ p ∧ q ∣ k := fun ⟨q, hqn, hq, hqp, hqk⟩ ↦
        hle ⟨q, Nat.le_succ_of_le hqn, hq, hqp, hqk⟩
      rw [ite_eq_right hn]

open Classical in
/-- On the additive formal group law, Cartier's `p`-typicalization projector deletes precisely the
coefficients in degrees divisible by some prime `q ≠ p`. -/
theorem coeff_toPowerSeries_pTypicalProjectorCurve_𝔾ₐ_eq_ite_prime_dvd (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (k : ℕ)
    (γ : (𝔾ₐ (R := R)).Curve) :
    PowerSeries.coeff k
        ((𝔾ₐ (R := R)).pTypicalProjectorCurve p hunit γ).toPowerSeries =
      if ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ q ∣ k then 0
      else PowerSeries.coeff k γ.toPowerSeries := by
  rcases eq_or_ne k 0 with rfl | hk0
  · rw [ite_eq_left (exists_prime_ne_and_dvd_zero p)]
    exact ((𝔾ₐ (R := R)).pTypicalProjectorCurve p hunit γ).coeff_zero_toPowerSeries
  · rw [(𝔾ₐ (R := R)).coeff_pTypicalProjectorCurve_eq_partialPTypicalProjectorCurve p hunit
        (le_refl k),
      coeff_toPowerSeries_partialPTypicalProjectorCurve_𝔾ₐ]
    have heq : (∃ q ≤ k, q.Prime ∧ q ≠ p ∧ q ∣ k) ↔ (∃ q : ℕ, q.Prime ∧ q ≠ p ∧ q ∣ k) :=
      ⟨fun ⟨q, _, hq⟩ ↦ ⟨q, hq⟩,
        fun ⟨q, hq, hqp, hqk⟩ ↦ ⟨q, Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hqk, hq, hqp, hqk⟩⟩
    by_cases hex : ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ q ∣ k
    · rw [ite_eq_left (heq.mpr hex), ite_eq_left hex]
    · rw [ite_eq_right (mt heq.mp hex), ite_eq_right hex]

open Classical in
/-- On the additive formal group law, when `p` is prime, Cartier's `p`-typicalization projector
deletes precisely the coefficients outside the degrees `p^m`. -/
theorem coeff_toPowerSeries_pTypicalProjectorCurve_𝔾ₐ {p : ℕ} (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (k : ℕ)
    (γ : (𝔾ₐ (R := R)).Curve) :
    PowerSeries.coeff k
        ((𝔾ₐ (R := R)).pTypicalProjectorCurve p hunit γ).toPowerSeries =
      if ∀ m : ℕ, p ^ m ≠ k then 0
      else PowerSeries.coeff k γ.toPowerSeries := by
  rw [coeff_toPowerSeries_pTypicalProjectorCurve_𝔾ₐ_eq_ite_prime_dvd p hunit k γ]
  by_cases hpow : ∀ m : ℕ, p ^ m ≠ k
  · rw [ite_eq_left ((exists_prime_ne_and_dvd_iff_forall_pow_ne hp k).mpr hpow), ite_eq_left hpow]
  · rw [ite_eq_right (mt (exists_prime_ne_and_dvd_iff_forall_pow_ne hp k).mp hpow),
      ite_eq_right hpow]

/-- On the additive formal group law, when `p` is prime, Cartier's `p`-typicalization projector
preserves the coefficients in all degrees `p^m`. -/
@[simp]
theorem coeff_pow_toPowerSeries_pTypicalProjectorCurve_𝔾ₐ {p : ℕ} (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (m : ℕ)
    (γ : (𝔾ₐ (R := R)).Curve) :
    PowerSeries.coeff (p ^ m)
        ((𝔾ₐ (R := R)).pTypicalProjectorCurve p hunit γ).toPowerSeries =
      PowerSeries.coeff (p ^ m) γ.toPowerSeries := by
  classical
  rw [coeff_toPowerSeries_pTypicalProjectorCurve_𝔾ₐ hp hunit (p ^ m) γ,
    ite_eq_right (not_forall.mpr ⟨m, not_not.mpr rfl⟩)]

/-- On the additive formal group law, Cartier's `p`-typicalization projector zeroes out the
coefficients outside the degrees `p^m`. -/
theorem coeff_toPowerSeries_pTypicalProjectorCurve_𝔾ₐ_eq_zero (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {k : ℕ} (hk : ∀ m : ℕ, p ^ m ≠ k)
    (γ : (𝔾ₐ (R := R)).Curve) :
    PowerSeries.coeff k
        ((𝔾ₐ (R := R)).pTypicalProjectorCurve p hunit γ).toPowerSeries = 0 := by
  classical
  rw [coeff_toPowerSeries_pTypicalProjectorCurve_𝔾ₐ_eq_ite_prime_dvd p hunit k γ,
    ite_eq_left (exists_prime_ne_and_dvd_of_forall_pow_ne hk)]

open Classical in
/-- Over a `ℚ`-algebra, Cartier's `p`-typicalization projector deletes from `log_F(γ(T))`
precisely the coefficients in degrees divisible by some prime `q ≠ p`. -/
theorem coeff_subst_pTypicalProjectorCurve_log_eq_ite_prime_dvd [Algebra ℚ R] (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (k : ℕ) (γ : F.Curve) :
    PowerSeries.coeff k
        (PowerSeries.subst (F.pTypicalProjectorCurve p hunit γ).toPowerSeries F.log) =
      if ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ q ∣ k then 0
      else PowerSeries.coeff k (PowerSeries.subst γ.toPowerSeries F.log) := by
  simpa only [Function.comp_apply, TauCeti.FormalGroupHom.toPowerSeries_mapCurve,
    logHom_toPowerSeries, coeff_toPowerSeries_pTypicalProjectorCurve_𝔾ₐ_eq_ite_prime_dvd] using
    congrArg (PowerSeries.coeff k ∘ Curve.toPowerSeries)
      (F.logHom.mapCurve_pTypicalProjectorCurve p hunit γ)

open Classical in
/-- Over a `ℚ`-algebra, when `p` is prime, Cartier's `p`-typicalization projector deletes precisely
the coefficients of `log_F(γ(T))` outside the degrees `p^m`. -/
theorem coeff_subst_pTypicalProjectorCurve_log [Algebra ℚ R] {p : ℕ} (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (k : ℕ) (γ : F.Curve) :
    PowerSeries.coeff k
        (PowerSeries.subst (F.pTypicalProjectorCurve p hunit γ).toPowerSeries F.log) =
      if ∀ m : ℕ, p ^ m ≠ k then 0
      else PowerSeries.coeff k (PowerSeries.subst γ.toPowerSeries F.log) := by
  simpa only [Function.comp_apply, TauCeti.FormalGroupHom.toPowerSeries_mapCurve,
    logHom_toPowerSeries, coeff_toPowerSeries_pTypicalProjectorCurve_𝔾ₐ hp] using
    congrArg (PowerSeries.coeff k ∘ Curve.toPowerSeries)
      (F.logHom.mapCurve_pTypicalProjectorCurve p hunit γ)

/-- Over a `ℚ`-algebra, when `p` is prime, Cartier's `p`-typicalization projector preserves the
coefficients of `log_F(γ(T))` in all degrees `p^m`. -/
@[simp]
theorem coeff_pow_subst_pTypicalProjectorCurve_log [Algebra ℚ R] {p : ℕ} (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (m : ℕ) (γ : F.Curve) :
    PowerSeries.coeff (p ^ m)
        (PowerSeries.subst (F.pTypicalProjectorCurve p hunit γ).toPowerSeries F.log) =
      PowerSeries.coeff (p ^ m) (PowerSeries.subst γ.toPowerSeries F.log) := by
  classical
  rw [F.coeff_subst_pTypicalProjectorCurve_log hp hunit (p ^ m) γ,
    ite_eq_right (not_forall.mpr ⟨m, not_not.mpr rfl⟩)]

private theorem X_pow_dvd_toPowerSeries_mapCurve {B : Type*} [CommRing B]
    {G H : FormalGroup B} (f : TauCeti.FormalGroupHom G H) {m : ℕ} {c : G.Curve}
    (hc : PowerSeries.X ^ m ∣ c.toPowerSeries) :
    PowerSeries.X ^ m ∣ (f.mapCurve c).toPowerSeries := by
  have hsub := PowerSeries.X_pow_dvd_subst_sub_subst (b := (0 : G.Curve).toPowerSeries)
    c.constantCoeff_toPowerSeries
    (by simpa only [Curve.toPowerSeries_zero, sub_zero] using hc) f.toPowerSeries
  rwa [← TauCeti.FormalGroupHom.toPowerSeries_mapCurve,
    ← TauCeti.FormalGroupHom.toPowerSeries_mapCurve, map_zero, Curve.toPowerSeries_zero,
    sub_zero] at hsub

/-- Cartier's `p`-typicalization projector preserves divisibility of curves by `X ^ m`. -/
theorem X_pow_dvd_toPowerSeries_pTypicalProjectorCurve (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {m : ℕ} {γ : F.Curve}
    (hγ : PowerSeries.X ^ m ∣ γ.toPowerSeries) :
    PowerSeries.X ^ m ∣ (F.pTypicalProjectorCurve p hunit γ).toPowerSeries := by
  rcases eq_or_ne m 0 with rfl | hm0
  · rw [pow_zero]
    exact one_dvd _
  · obtain ⟨A, Q, _, _, _, j, hj, hSA, F₀, _, γ₀, π, e, hγ₀⟩ :=
      Curve.exists_lift_of_isUnit_natCast F γ {q : ℕ | q.Prime ∧ q ≠ p}
        (fun _ hq ↦ hq.1.ne_zero) (fun q hq ↦ hunit q hq.1 hq.2)
    let δ₀ : F₀.Curve :=
      ⟨PowerSeries.mk fun i ↦ if i < m then 0 else PowerSeries.coeff i γ₀.toPowerSeries, by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk,
          ite_eq_left (Nat.pos_of_ne_zero hm0)]⟩
    have hπγ₀ : Curve.map π γ₀ = e.invHom.mapCurve γ := by
      rw [← hγ₀, ← TauCeti.FormalGroupHom.comp_mapCurve, e.invHom_comp_toHom,
        TauCeti.FormalGroupHom.id_mapCurve]
    have hdvd_πγ₀ : PowerSeries.X ^ m ∣ (Curve.map π γ₀).toPowerSeries := by
      rw [hπγ₀]
      exact X_pow_dvd_toPowerSeries_mapCurve e.invHom hγ
    have hπδ₀ : Curve.map π δ₀ = Curve.map π γ₀ := by
      ext i
      rw [Curve.toPowerSeries_map, PowerSeries.coeff_map, PowerSeries.coeff_mk]
      split_ifs with hi
      · rw [map_zero, PowerSeries.X_pow_dvd_iff.mp hdvd_πγ₀ i hi]
      · rw [Curve.toPowerSeries_map, PowerSeries.coeff_map]
    have hγ_eq : e.toHom.mapCurve (Curve.map π δ₀) = γ := by
      rw [hπδ₀, hγ₀]
    let hA : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : A) := fun q hq hqp ↦ hSA q ⟨hq, hqp⟩
    let hQ : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : Q) :=
      fun q hq hqp ↦ by simpa using (hA q hq hqp).map j
    have hdvd_jδ₀ : PowerSeries.X ^ m ∣ (Curve.map j δ₀).toPowerSeries :=
      PowerSeries.X_pow_dvd_iff.mpr fun i hi ↦ by
        rw [Curve.toPowerSeries_map, PowerSeries.coeff_map, PowerSeries.coeff_mk, ite_eq_left hi,
          map_zero]
    have hdvd_Q :
        PowerSeries.X ^ m ∣
          ((F₀.map j).pTypicalProjectorCurve p hQ (Curve.map j δ₀)).toPowerSeries := by
      have hdvd_log := X_pow_dvd_toPowerSeries_mapCurve (F₀.map j).logHom hdvd_jδ₀
      have hdvd_proj_log : PowerSeries.X ^ m ∣
          ((F₀.map j).logHom.mapCurve
            ((F₀.map j).pTypicalProjectorCurve p hQ (Curve.map j δ₀))).toPowerSeries :=
        PowerSeries.X_pow_dvd_iff.mpr fun i hi ↦ by
          classical
          rw [TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries,
            (F₀.map j).coeff_subst_pTypicalProjectorCurve_log_eq_ite_prime_dvd]
          split_ifs
          · rfl
          · simpa only [TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries] using
              PowerSeries.X_pow_dvd_iff.mp hdvd_log i hi
      have hexp := X_pow_dvd_toPowerSeries_mapCurve (F₀.map j).logIso.invHom hdvd_proj_log
      rwa [← logIso_toHom (F₀.map j), ← TauCeti.FormalGroupHom.comp_mapCurve,
        (F₀.map j).logIso.invHom_comp_toHom, TauCeti.FormalGroupHom.id_mapCurve] at hexp
    have hdvd_A : PowerSeries.X ^ m ∣ (F₀.pTypicalProjectorCurve p hA δ₀).toPowerSeries :=
      PowerSeries.X_pow_dvd_iff.mpr fun i hi ↦ hj <| by
        have hiQ := PowerSeries.X_pow_dvd_iff.mp hdvd_Q i hi
        rwa [← F₀.map_pTypicalProjectorCurve j p hA δ₀, Curve.toPowerSeries_map,
          PowerSeries.coeff_map, ← map_zero j] at hiQ
    have hdvd_π : PowerSeries.X ^ m ∣
        (Curve.map π (F₀.pTypicalProjectorCurve p hA δ₀)).toPowerSeries :=
      PowerSeries.X_pow_dvd_iff.mpr fun i hi ↦ by
        rw [Curve.toPowerSeries_map, PowerSeries.coeff_map,
          PowerSeries.X_pow_dvd_iff.mp hdvd_A i hi, map_zero]
    rw [← hγ_eq, ← e.toHom.mapCurve_pTypicalProjectorCurve, ← F₀.map_pTypicalProjectorCurve π p hA]
    exact X_pow_dvd_toPowerSeries_mapCurve e.toHom hdvd_π

/-- Degree-`k` coefficients of Cartier's `p`-typicalization projector depend only on curve
coefficients up to degree `k`. -/
theorem coeff_pTypicalProjectorCurve_congr (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {k : ℕ} {γ₁ γ₂ : F.Curve}
    (h : ∀ i ≤ k, PowerSeries.coeff i γ₁.toPowerSeries = PowerSeries.coeff i γ₂.toPowerSeries) :
    PowerSeries.coeff k (F.pTypicalProjectorCurve p hunit γ₁).toPowerSeries =
      PowerSeries.coeff k (F.pTypicalProjectorCurve p hunit γ₂).toPowerSeries := by
  have hdvd_sub : PowerSeries.X ^ (k + 1) ∣ (γ₁ - γ₂).toPowerSeries :=
    PowerSeries.X_pow_dvd_iff.mpr fun i hi ↦ by
      rw [sub_eq_add_neg]
      have hadd := Curve.coeff_add_congr (γ₁ := γ₁) (γ₁' := γ₂) (γ₂ := -γ₂) (γ₂' := -γ₂) (k := i)
        (fun j hj ↦ h j (hj.trans (Nat.lt_succ_iff.mp hi))) (fun _ _ ↦ rfl)
      rw [add_neg_cancel, Curve.toPowerSeries_zero, map_zero] at hadd
      exact hadd
  have hdvd_proj := F.X_pow_dvd_toPowerSeries_pTypicalProjectorCurve p hunit hdvd_sub
  have hdecomp : F.pTypicalProjectorCurve p hunit γ₁ =
      F.pTypicalProjectorCurve p hunit γ₂ + F.pTypicalProjectorCurve p hunit (γ₁ - γ₂) := by
    rw [← map_add, add_sub_cancel]
  rw [hdecomp]
  exact Curve.coeff_add_eq_left_of_forall_lt_coeff_eq_zero _ _ (Nat.lt_succ_self k)
    (PowerSeries.X_pow_dvd_iff.mp hdvd_proj)

/-- The image of Cartier's `p`-typicalization projector is killed by `f_q` for every prime
`q ≠ p`. -/
@[simp]
theorem frobeniusCurve_pTypicalProjectorCurve_eq_zero_of_prime_ne (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (γ : F.Curve) :
    F.frobeniusCurve q hq.ne_zero (F.pTypicalProjectorCurve p hunit γ) = 0 :=
  Curve.eq_of_forall_ratAlgebra F γ {r : ℕ | r.Prime ∧ r ≠ p}
    (fun r hr ↦ hunit r hr.1 hr.2)
    (fun G _ h δ ↦ G.frobeniusCurve q hq.ne_zero
      (G.pTypicalProjectorCurve p (fun r hr hrp ↦ h r ⟨hr, hrp⟩) δ))
    (fun _ _ _ _ ↦ 0)
    (fun G _ _ δ ↦ by
      classical
      apply G.logIso.curveEquiv.injective
      ext k
      simp only [TauCeti.FormalGroupIso.curveEquiv_apply, logIso_toHom,
        TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries,
        subst_frobeniusCurve_log, PowerSeries.coeff_smul, PowerSeries.coeff_cartier, Nat.add_zero,
        G.coeff_subst_pTypicalProjectorCurve_log_eq_ite_prime_dvd, map_zero,
        Curve.toPowerSeries_zero]
      rw [ite_eq_left ⟨q, hq, hqp, dvd_mul_right q k⟩, smul_zero])
    (fun G _ _ _ _ _ ↦ by rw [G.map_frobeniusCurve, G.map_pTypicalProjectorCurve])
    (fun _ _ _ _ φ _ ↦ map_zero (Curve.map φ))
    (fun _ f _ ↦ by rw [f.mapCurve_frobeniusCurve, f.mapCurve_pTypicalProjectorCurve])
    (fun _ f _ ↦ map_zero f.mapCurve)

/-- Every curve in the image of Cartier's `p`-typicalization projector is `p`-typical. -/
@[simp]
theorem isPTypical_pTypicalProjectorCurve (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    (F.pTypicalProjectorCurve p hunit γ).IsPTypical p :=
  fun _ hq hqp ↦ F.frobeniusCurve_pTypicalProjectorCurve_eq_zero_of_prime_ne p hunit hq hqp γ

/-- Over a `ℚ`-algebra, Cartier's `p`-typicalization projector zeroes out the coefficients of
`log_F(γ(T))` outside the degrees `p^m`. -/
theorem coeff_subst_pTypicalProjectorCurve_log_eq_zero [Algebra ℚ R] (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {k : ℕ} (hk : ∀ m : ℕ, p ^ m ≠ k)
    (γ : F.Curve) :
    PowerSeries.coeff k
        (PowerSeries.subst (F.pTypicalProjectorCurve p hunit γ).toPowerSeries F.log) = 0 :=
  (F.isPTypical_pTypicalProjectorCurve p hunit γ).coeff_subst_log_eq_zero hk

/-- A `p`-typical curve is fixed by Cartier's `p`-typicalization projector. -/
theorem pTypicalProjectorCurve_eq_self (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {γ : F.Curve} (hγ : γ.IsPTypical p) :
    F.pTypicalProjectorCurve p hunit γ = γ := by
  have hpart : ∀ n : ℕ, F.partialPTypicalProjectorCurve p hunit n γ = γ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [partialPTypicalProjectorCurve_succ]
      split_ifs with h
      · rw [AddMonoidHom.comp_apply, ih]
        exact F.cartierProjectorCurve_eq_self (n + 1) (Nat.succ_ne_zero n)
          (hunit (n + 1) h.1 h.2) (hγ (n + 1) h.1 h.2)
      · exact ih
  ext k
  rw [F.coeff_pTypicalProjectorCurve_eq_partialPTypicalProjectorCurve p hunit (le_refl k), hpart k]

/-- The fixed points of Cartier's `p`-typicalization projector are precisely the `p`-typical
curves. -/
@[simp]
theorem pTypicalProjectorCurve_eq_self_iff (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    F.pTypicalProjectorCurve p hunit γ = γ ↔ γ.IsPTypical p :=
  ⟨fun h ↦ h ▸ F.isPTypical_pTypicalProjectorCurve p hunit γ,
    F.pTypicalProjectorCurve_eq_self p hunit⟩

/-- Cartier's `p`-typicalization projector is idempotent. -/
@[simp]
theorem pTypicalProjectorCurve_pTypicalProjectorCurve (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    F.pTypicalProjectorCurve p hunit (F.pTypicalProjectorCurve p hunit γ) =
      F.pTypicalProjectorCurve p hunit γ :=
  F.pTypicalProjectorCurve_eq_self p hunit (F.isPTypical_pTypicalProjectorCurve p hunit γ)

/-- Cartier's `p`-typicalization projector is an idempotent in `AddMonoid.End F.Curve`. -/
@[simp]
theorem isIdempotentElem_pTypicalProjectorCurve (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    IsIdempotentElem (M := AddMonoid.End F.Curve) (F.pTypicalProjectorCurve p hunit) := by
  apply AddMonoidHom.ext
  exact F.pTypicalProjectorCurve_pTypicalProjectorCurve p hunit

/-- The range of Cartier's `p`-typicalization projector is the subgroup of `p`-typical curves. -/
@[simp]
theorem range_pTypicalProjectorCurve (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalProjectorCurve p hunit).range = F.pTypicalCurveSubgroup p := by
  ext γ
  simp only [AddMonoidHom.mem_range, mem_pTypicalCurveSubgroup]
  exact ⟨fun ⟨δ, hδ⟩ ↦ hδ ▸ F.isPTypical_pTypicalProjectorCurve p hunit δ,
    fun hγ ↦ ⟨γ, F.pTypicalProjectorCurve_eq_self p hunit hγ⟩⟩

/-- Cartier's `p`-typicalization projector absorbs the elementary Cartier projector at any prime
`q ≠ p`. -/
@[simp]
theorem pTypicalProjectorCurve_cartierProjectorCurve_of_prime (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (γ : F.Curve) :
    F.pTypicalProjectorCurve p hunit
        (F.cartierProjectorCurve q hq.ne_zero (hunit q hq hqp) γ) =
      F.pTypicalProjectorCurve p hunit γ :=
  Curve.eq_of_forall_ratAlgebra F γ {r : ℕ | r.Prime ∧ r ≠ p}
    (fun r hr ↦ hunit r hr.1 hr.2)
    (fun G _ h δ ↦ G.pTypicalProjectorCurve p (fun r hr hrp ↦ h r ⟨hr, hrp⟩)
      (G.cartierProjectorCurve q hq.ne_zero (h q ⟨hq, hqp⟩) δ))
    (fun G _ h δ ↦ G.pTypicalProjectorCurve p (fun r hr hrp ↦ h r ⟨hr, hrp⟩) δ)
    (fun G _ _ δ ↦ by
      classical
      apply G.logIso.curveEquiv.injective
      ext k
      simp only [TauCeti.FormalGroupIso.curveEquiv_apply, logIso_toHom,
        TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries,
        G.coeff_subst_pTypicalProjectorCurve_log_eq_ite_prime_dvd]
      split_ifs with hex
      · rfl
      · rw [G.coeff_subst_cartierProjectorCurve_log,
          ite_eq_right (fun hdvd ↦ hex ⟨q, hq, hqp, hdvd⟩)])
    (fun G _ _ _ _ _ ↦ by rw [G.map_pTypicalProjectorCurve, G.map_cartierProjectorCurve])
    (fun G _ _ _ _ _ ↦ G.map_pTypicalProjectorCurve _ _ _ _)
    (fun _ f _ ↦ by rw [f.mapCurve_pTypicalProjectorCurve, f.mapCurve_cartierProjectorCurve])
    (fun _ f δ ↦ f.mapCurve_pTypicalProjectorCurve p _ δ)

/-- Cartier's `p`-typicalization projector annihilates `V_n γ` whenever `n` has a prime divisor
`q ≠ p`. -/
theorem pTypicalProjectorCurve_verschiebungCurve_eq_zero_of_prime_dvd (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {q n : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (hdvd : q ∣ n) (hn : n ≠ 0) (γ : F.Curve) :
    F.pTypicalProjectorCurve p hunit (F.verschiebungCurve n hn γ) = 0 := by
  obtain ⟨m, rfl⟩ := hdvd
  have hm : m ≠ 0 := right_ne_zero_of_mul hn
  rw [← F.verschiebungCurve_verschiebungCurve hq.ne_zero hm,
    ← F.pTypicalProjectorCurve_cartierProjectorCurve_of_prime p hunit hq hqp,
    F.cartierProjectorCurve_verschiebungCurve, map_zero]

/-- Cartier's `p`-typicalization projector annihilates `V_n γ` for every `n > 1` coprime to `p`. -/
theorem pTypicalProjectorCurve_verschiebungCurve_eq_zero_of_coprime (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {n : ℕ} (hn1 : 1 < n)
    (hcop : n.Coprime p) (hn : n ≠ 0) (γ : F.Curve) :
    F.pTypicalProjectorCurve p hunit (F.verschiebungCurve n hn γ) = 0 := by
  obtain ⟨q, hq, hqp, hqdvd⟩ := exists_prime_ne_and_dvd_of_coprime hn1 hcop
  exact F.pTypicalProjectorCurve_verschiebungCurve_eq_zero_of_prime_dvd p hunit hq hqp hqdvd hn γ

/-- When `p` is prime, Cartier's `p`-typicalization projector commutes with `V_{p^r}`. -/
theorem pTypicalProjectorCurve_verschiebungCurve_pow {p : ℕ} (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (r : ℕ) (γ : F.Curve) :
    F.pTypicalProjectorCurve p hunit
        (F.verschiebungCurve (p ^ r) (pow_ne_zero r hp.ne_zero) γ) =
      F.verschiebungCurve (p ^ r) (pow_ne_zero r hp.ne_zero)
        (F.pTypicalProjectorCurve p hunit γ) := by
  have hpr : p ^ r ≠ 0 := pow_ne_zero r hp.ne_zero
  have hpart : ∀ n : ℕ,
      F.partialPTypicalProjectorCurve p hunit n (F.verschiebungCurve (p ^ r) hpr γ) =
        F.verschiebungCurve (p ^ r) hpr (F.partialPTypicalProjectorCurve p hunit n γ) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [partialPTypicalProjectorCurve_succ]
      split_ifs with h
      · have hcop : (n + 1).Coprime (p ^ r) := ((Nat.coprime_primes h.1 hp).mpr h.2).pow_right r
        rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ih,
          F.cartierProjectorCurve_verschiebungCurve_of_coprime (Nat.succ_ne_zero n) hpr
            (hunit (n + 1) h.1 h.2) hcop]
      · exact ih
  ext k
  rw [F.coeff_pTypicalProjectorCurve_eq_partialPTypicalProjectorCurve p hunit (le_refl k), hpart k,
    toPowerSeries_verschiebungCurve, toPowerSeries_verschiebungCurve,
    PowerSeries.coeff_expand, PowerSeries.coeff_expand]
  split_ifs with hdvd
  · have hle : k / p ^ r ≤ k := Nat.div_le_self k (p ^ r)
    exact (F.coeff_pTypicalProjectorCurve_eq_partialPTypicalProjectorCurve p hunit hle γ).symm
  · rfl

/-- When `p` is prime, Cartier's `p`-typicalization projector commutes with `f_{p^r}`. -/
theorem frobeniusCurve_pow_pTypicalProjectorCurve {p : ℕ} (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (r : ℕ) (γ : F.Curve) :
    F.frobeniusCurve (p ^ r) (pow_ne_zero r hp.ne_zero) (F.pTypicalProjectorCurve p hunit γ) =
      F.pTypicalProjectorCurve p hunit
        (F.frobeniusCurve (p ^ r) (pow_ne_zero r hp.ne_zero) γ) := by
  have hpr : p ^ r ≠ 0 := pow_ne_zero r hp.ne_zero
  exact Curve.eq_of_forall_ratAlgebra F γ {q : ℕ | q.Prime ∧ q ≠ p}
    (fun q hq ↦ hunit q hq.1 hq.2)
    (fun G _ h δ ↦ G.frobeniusCurve (p ^ r) hpr
      (G.pTypicalProjectorCurve p (fun q hq hqp ↦ h q ⟨hq, hqp⟩) δ))
    (fun G _ h δ ↦ G.pTypicalProjectorCurve p (fun q hq hqp ↦ h q ⟨hq, hqp⟩)
      (G.frobeniusCurve (p ^ r) hpr δ))
    (fun G _ _ δ ↦ by
      classical
      apply G.logIso.curveEquiv.injective
      ext k
      simp only [TauCeti.FormalGroupIso.curveEquiv_apply, logIso_toHom,
        TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries,
        subst_frobeniusCurve_log, PowerSeries.coeff_smul, PowerSeries.coeff_cartier, Nat.add_zero,
        G.coeff_subst_pTypicalProjectorCurve_log hp]
      have hpow_iff : (∀ m : ℕ, p ^ m ≠ p ^ r * k) ↔ (∀ m : ℕ, p ^ m ≠ k) := by
        refine ⟨fun h m hm ↦ h (r + m) (by rw [pow_add, hm]), fun h m hm ↦ ?_⟩
        obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp ⟨p ^ r, hm.trans (mul_comm _ _)⟩
        exact h j rfl
      by_cases hk : ∀ m : ℕ, p ^ m ≠ k
      · rw [ite_eq_left (hpow_iff.mpr hk), ite_eq_left hk, smul_zero]
      · rw [ite_eq_right (mt hpow_iff.mp hk), ite_eq_right hk])
    (fun G _ _ _ _ _ ↦ by rw [G.map_frobeniusCurve, G.map_pTypicalProjectorCurve])
    (fun G _ _ _ _ _ ↦ by rw [G.map_pTypicalProjectorCurve, G.map_frobeniusCurve])
    (fun _ f _ ↦ by rw [f.mapCurve_frobeniusCurve, f.mapCurve_pTypicalProjectorCurve])
    (fun _ f _ ↦ by rw [f.mapCurve_pTypicalProjectorCurve, f.mapCurve_frobeniusCurve])

end Projector

end FormalGroup
