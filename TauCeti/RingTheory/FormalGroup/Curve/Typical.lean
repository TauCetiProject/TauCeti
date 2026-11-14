/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Log
public import TauCeti.RingTheory.FormalGroup.Curve.Projector
public import TauCeti.RingTheory.FormalGroup.Hazewinkel.Integral
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Typical curves, Cartier's infinite projector, and canonical `p`-typicalization

Let `F(X, Y)` be a one-dimensional commutative formal group law over a commutative ring `R`, and
fix a natural number `p` (in applications a prime). Following Cartier (1967), a curve
`γ(T) ∈ R⟦T⟧` on `F` is **`p`-typical** (`FormalGroup.Curve.IsPTypical`) if Cartier's Frobenius
operator `f_q` kills `γ` for every prime `q ≠ p`. By Cartier's composition law `f_{m n} = f_m ∘ f_n`
on curves, a `p`-typical curve is automatically killed by `f_n` for every composite index `n`
divisible by a prime `q ≠ p`, and in particular for every `n > 1` coprime to `p` (without assuming
`p` is prime); when `p` is prime, the prime and coprime formulations are equivalent.

`p`-typical curves form an additive subgroup `FormalGroup.pTypicalCurveSubgroup F p` of `F.Curve`,
stable under all Frobenius operators `f_n`, under Verschiebung `V_{p^k}` when `p` is prime, under
every elementary Cartier projector, and under base change and homomorphisms of formal group laws.
Over a `ℚ`-algebra, `γ` is `p`-typical precisely when `log_F(γ(T))` has zero coefficients in every
degree divisible by a prime `q ≠ p` (equivalently, when `p` is prime, in every degree outside the
powers `p^n`).

When every prime `q ≠ p` is invertible in `R`, iterating the commuting elementary Cartier projectors
`1 - V_q [q]⁻¹ f_q` from `FormalGroup.cartierProjectorCurve` across primes `q ≠ p` stabilizes in
each power-series degree `k` as soon as all primes `q ≤ k` have been applied, because `V_q` vanishes
below degree `q`. Taking the stabilized coefficient in each degree constructs **Cartier's
`p`-typicalization projector** `FormalGroup.pTypicalProjectorCurve`: an idempotent additive
endomorphism `F.Curve →+ F.Curve` with image `F.pTypicalCurveSubgroup p` that preserves linear
coefficients and commutes with base change, homomorphisms of formal group laws, elementary Cartier
projectors, and (for `p` prime) `f_{p^r}` and `V_{p^r}`.

A commutative formal group law `F` is **`p`-typical** (`FormalGroup.IsPTypical`) if its tautological
curve `T` is `p`-typical. Over any commutative ring (including rings with `p`-torsion and prime
characteristic), the additive law `𝔾ₐ` and Hazewinkel's integral law
`TauCeti.hazewinkelIntegralFormalGroup p v` are `p`-typical; over a `ℚ`-algebra and for `p` prime,
the `p`-typical formal group laws are precisely the laws `TauCeti.hazewinkelFormalGroup p v`, each
for a unique generator family `v`.

Applying `F.pTypicalProjectorCurve` to `F.tautologicalCurve` produces a `p`-typical curve with
linear coefficient `1`. Its compositional inverse `FormalGroup.pTypicalCoordinate` is Cartier and
Quillen's canonical strict coordinate transporting `F` via `FormalGroup.pTypicalIso` to the
`p`-typical formal group law `FormalGroup.pTypicalFormalGroup`. Over a `ℚ`-algebra, the logarithm of
`F.pTypicalFormalGroup` is obtained from `F.log` by deleting all degrees divisible by a prime
`q ≠ p` and keeping the `p^n`-th coefficients unchanged.

## Main definitions

* `FormalGroup.Curve.IsPTypical`: predicate that a curve `γ` on `F` satisfies `f_q γ = 0` for every
  prime `q ≠ p`.
* `FormalGroup.pTypicalCurveSubgroup`: the additive subgroup of `p`-typical curves in `F.Curve`.
* `FormalGroup.pTypicalProjectorCurve`: Cartier's idempotent `p`-typicalization projector
  `F.Curve →+ F.Curve` when every prime `q ≠ p` is a unit in `R`.
* `FormalGroup.IsPTypical`: predicate that a commutative formal group law has `p`-typical
  tautological curve.
* `FormalGroup.pTypicalCoordinate`, `FormalGroup.pTypicalFormalGroup`, and
  `FormalGroup.pTypicalIso`: Cartier–Quillen's canonical strict formal coordinate, `p`-typicalized
  formal group law, and strict isomorphism `F ≅ F.pTypicalFormalGroup`.

## Main results

* `FormalGroup.Curve.IsPTypical.frobeniusCurve_eq_zero_of_coprime` and
  `FormalGroup.Curve.isPTypical_iff_forall_coprime`: vanishing at coprime indices `n > 1`, and
  equivalence when `p` is prime.
* `FormalGroup.Curve.isPTypical_iff_coeff_subst_log_eq_zero_of_prime`: rational logarithm
  characterization of `p`-typical curves.
* `FormalGroup.isPTypical_pTypicalProjectorCurve`, `FormalGroup.pTypicalProjectorCurve_eq_self_iff`,
  `FormalGroup.pTypicalProjectorCurve_pTypicalProjectorCurve`, and
  `FormalGroup.range_pTypicalProjectorCurve`: Cartier's projector lands in `p`-typical curves, fixes
  precisely the `p`-typical curves, and is idempotent.
* `FormalGroup.isPTypical_iff_exists_eq_hazewinkelFormalGroup` and
  `TauCeti.isPTypical_hazewinkelIntegralFormalGroup`: rational classification by Hazewinkel's laws
  and unconditional `p`-typicality of Hazewinkel's integral law over any commutative ring.
* `FormalGroup.isPTypical_pTypicalFormalGroup`,
  `FormalGroup.pTypicalFormalGroup_pTypicalFormalGroup`, and
  `FormalGroup.coeff_log_pTypicalFormalGroup`: `p`-typicality, idempotence, and Quillen's
  logarithm formula for the canonical `p`-typicalization.

## References

* P. Cartier, *Modules associés à un groupe formel commutatif. Courbes typiques*, C. R. Acad. Sci.
  Paris Sér. A-B 265 (1967), A129–A132.
* D. Quillen, *On the formal group laws of unoriented and complex cobordism theory*, Bull. Amer.
  Math. Soc. 75 (1969), 1293–1298.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapter III, §16.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Academic Press (1986),
  Appendix A2.1.20–A2.1.26.
-/

public section

namespace FormalGroup

variable {R S : Type*} [CommRing R] [CommRing S]

/-! ### Prime-divisor helpers for powers of a prime -/

/-- A nonzero natural number has no prime divisor distinct from a prime `p` if and only if it is a
power of `p`. -/
private theorem forall_prime_ne_not_dvd_iff_exists_pow_eq {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    (∀ q : ℕ, q.Prime → q ≠ p → ¬ q ∣ k) ↔ ∃ n : ℕ, p ^ n = k := by
  refine ⟨fun hno ↦ ?_, fun ⟨n, hn⟩ q hq hqp hqd ↦
    hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow (hn ▸ hqd)))⟩
  obtain ⟨n, m, hpm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk p hp.ne_one
  rcases eq_or_ne m 1 with rfl | hm1
  · exact ⟨n, (mul_one (p ^ n)).symm⟩
  · exact (hno m.minFac (Nat.minFac_prime hm1) (fun heq ↦ hpm (heq ▸ Nat.minFac_dvd m))
      (dvd_mul_of_dvd_right (Nat.minFac_dvd m) _)).elim

private theorem exists_prime_ne_dvd_pow_mul_iff {p : ℕ} (hp : p.Prime) (r m : ℕ) :
    (∃ q : ℕ, q.Prime ∧ q ≠ p ∧ q ∣ p ^ r * m) ↔ ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ q ∣ m :=
  ⟨fun ⟨q, hq, hqp, hqd⟩ ↦ ⟨q, hq, hqp, (hq.dvd_mul.mp hqd).resolve_left fun hqp' ↦
      hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hqp'))⟩,
    fun ⟨q, hq, hqp, hqd⟩ ↦ ⟨q, hq, hqp, dvd_mul_of_dvd_right hqd _⟩⟩

/-! ### `p`-typical curves -/

namespace Curve

section IsPTypical

variable {F G : FormalGroup R} [F.IsComm] [G.IsComm]

/-- A curve `γ` on a commutative formal group law `F` is **`p`-typical** if Cartier's Frobenius
operator `f_q` kills `γ` for every prime `q ≠ p`. -/
def IsPTypical (p : ℕ) (γ : F.Curve) : Prop :=
  ∀ q : ℕ, (hq : q.Prime) → q ≠ p → F.frobeniusCurve q hq.ne_zero γ = 0

/-- Unfold `FormalGroup.Curve.IsPTypical`. -/
theorem isPTypical_def (p : ℕ) (γ : F.Curve) :
    γ.IsPTypical p ↔ ∀ q : ℕ, (hq : q.Prime) → q ≠ p → F.frobeniusCurve q hq.ne_zero γ = 0 :=
  ⟨id, id⟩

/-- A `p`-typical curve is killed by `f_q` for every prime `q ≠ p`. -/
theorem IsPTypical.frobeniusCurve_eq_zero {p q : ℕ} {γ : F.Curve} (hγ : γ.IsPTypical p)
    (hq : q.Prime) (hqp : q ≠ p) : F.frobeniusCurve q hq.ne_zero γ = 0 :=
  hγ q hq hqp

/-- A `p`-typical curve is killed by `f_n` whenever `n ≠ 0` has a prime divisor `q ≠ p`. -/
theorem IsPTypical.frobeniusCurve_eq_zero_of_dvd {p q n : ℕ} {γ : F.Curve} (hγ : γ.IsPTypical p)
    (hq : q.Prime) (hqp : q ≠ p) (hqn : q ∣ n) (hn : n ≠ 0) :
    F.frobeniusCurve n hn γ = 0 := by
  have hdiv : n / q ≠ 0 := fun h0 ↦ hn <| by
    have := Nat.div_mul_cancel hqn
    rw [h0, zero_mul] at this
    exact this.symm
  rw [F.frobeniusCurve_congr (Nat.div_mul_cancel hqn).symm hn (mul_ne_zero hdiv hq.ne_zero),
    ← F.frobeniusCurve_frobeniusCurve hdiv hq.ne_zero, hγ q hq hqp, map_zero]

/-- A `p`-typical curve is killed by `f_n` for every `n > 1` coprime to `p`, without assuming `p`
is prime. -/
theorem IsPTypical.frobeniusCurve_eq_zero_of_coprime {p n : ℕ} {γ : F.Curve} (hγ : γ.IsPTypical p)
    (hn : 1 < n) (hcop : n.Coprime p) :
    F.frobeniusCurve n (Nat.ne_zero_of_lt hn) γ = 0 := by
  have hq : n.minFac.Prime := Nat.minFac_prime (Nat.ne_of_gt hn)
  have hqp : n.minFac ≠ p := fun heq ↦
    hq.not_dvd_one (hcop ▸ Nat.dvd_gcd (Nat.minFac_dvd n) (heq ▸ dvd_rfl))
  exact hγ.frobeniusCurve_eq_zero_of_dvd hq hqp (Nat.minFac_dvd n) (Nat.ne_zero_of_lt hn)

/-- When `p` is prime, a curve is `p`-typical if and only if it is killed by `f_n` for every
`n > 1` coprime to `p`. -/
theorem isPTypical_iff_forall_coprime {p : ℕ} (hp : p.Prime) (γ : F.Curve) :
    γ.IsPTypical p ↔
      ∀ n : ℕ, (hn : 1 < n) → n.Coprime p → F.frobeniusCurve n (Nat.ne_zero_of_lt hn) γ = 0 :=
  ⟨fun hγ _ hn hcop ↦ hγ.frobeniusCurve_eq_zero_of_coprime hn hcop,
    fun h q hq hqp ↦ h q hq.one_lt ((Nat.coprime_primes hq hp).mpr hqp)⟩

/-- The zero curve is `p`-typical. -/
@[simp]
theorem IsPTypical.zero (p : ℕ) : (0 : F.Curve).IsPTypical p :=
  fun _ _ _ ↦ map_zero _

/-- The formal-group sum of two `p`-typical curves is `p`-typical. -/
theorem IsPTypical.add {p : ℕ} {γ δ : F.Curve} (hγ : γ.IsPTypical p) (hδ : δ.IsPTypical p) :
    (γ + δ).IsPTypical p :=
  fun q hq hqp ↦ by rw [map_add, hγ q hq hqp, hδ q hq hqp, _root_.add_zero]

/-- The formal-group inverse of a `p`-typical curve is `p`-typical. -/
theorem IsPTypical.neg {p : ℕ} {γ : F.Curve} (hγ : γ.IsPTypical p) : (-γ).IsPTypical p :=
  fun q hq hqp ↦ by rw [map_neg, hγ q hq hqp, neg_zero]

/-- Negation preserves and reflects `p`-typicality of curves. -/
@[simp]
theorem isPTypical_neg_iff (p : ℕ) (γ : F.Curve) : (-γ).IsPTypical p ↔ γ.IsPTypical p :=
  ⟨fun h ↦ neg_neg γ ▸ h.neg, IsPTypical.neg⟩

/-- The formal-group difference of two `p`-typical curves is `p`-typical. -/
theorem IsPTypical.sub {p : ℕ} {γ δ : F.Curve} (hγ : γ.IsPTypical p) (hδ : δ.IsPTypical p) :
    (γ - δ).IsPTypical p :=
  fun q hq hqp ↦ by rw [map_sub, hγ q hq hqp, hδ q hq hqp, sub_zero]

/-- Natural-number scalar multiples of a `p`-typical curve are `p`-typical. -/
theorem IsPTypical.nsmul {p : ℕ} {γ : F.Curve} (hγ : γ.IsPTypical p) (n : ℕ) :
    (n • γ).IsPTypical p :=
  fun q hq hqp ↦ by rw [map_nsmul, hγ q hq hqp, smul_zero]

/-- Integer scalar multiples of a `p`-typical curve are `p`-typical. -/
theorem IsPTypical.zsmul {p : ℕ} {γ : F.Curve} (hγ : γ.IsPTypical p) (n : ℤ) :
    (n • γ).IsPTypical p :=
  fun q hq hqp ↦ by rw [map_zsmul, hγ q hq hqp, zsmul_zero]

/-- Division by an invertible natural number preserves `p`-typicality of curves. -/
theorem IsPTypical.nsmulCurveEquiv_symm {p : ℕ} {γ : F.Curve} (hγ : γ.IsPTypical p)
    (n : ℕ) (hunit : IsUnit (n : R)) :
    ((F.nsmulCurveEquiv n hunit).symm γ).IsPTypical p :=
  fun q hq hqp ↦ by
    rw [F.map_nsmulCurveEquiv_symm (F.frobeniusCurve q hq.ne_zero) n hunit hunit,
      hγ q hq hqp, map_zero]

/-- Every Frobenius operator `f_n` preserves `p`-typicality of curves. -/
theorem IsPTypical.frobeniusCurve {p : ℕ} {γ : F.Curve} (hγ : γ.IsPTypical p)
    (n : ℕ) (hn : n ≠ 0) : (F.frobeniusCurve n hn γ).IsPTypical p :=
  fun q hq hqp ↦ by
    rw [F.frobeniusCurve_frobeniusCurve hq.ne_zero hn,
      F.frobeniusCurve_congr (Nat.mul_comm q n) _ (mul_ne_zero hn hq.ne_zero),
      ← F.frobeniusCurve_frobeniusCurve hn hq.ne_zero, hγ q hq hqp, map_zero]

/-- Verschiebung `V_m` preserves `p`-typicality whenever `m` is coprime to every prime `q ≠ p`. -/
theorem IsPTypical.verschiebungCurve_of_forall_coprime {p m : ℕ} {γ : F.Curve}
    (hγ : γ.IsPTypical p) (hm : m ≠ 0) (hcop : ∀ q : ℕ, q.Prime → q ≠ p → q.Coprime m) :
    (F.verschiebungCurve m hm γ).IsPTypical p :=
  fun q hq hqp ↦ by
    rw [F.frobeniusCurve_verschiebungCurve_of_coprime hq.ne_zero hm (hcop q hq hqp),
      hγ q hq hqp, map_zero]

/-- When `p` is prime, Verschiebung `V_{p^k}` of any `p`-power index preserves `p`-typicality. -/
theorem IsPTypical.verschiebungCurve_pow {p : ℕ} (hp : p.Prime) {γ : F.Curve}
    (hγ : γ.IsPTypical p) (k : ℕ) :
    (F.verschiebungCurve (p ^ k) (pow_ne_zero k hp.ne_zero) γ).IsPTypical p :=
  hγ.verschiebungCurve_of_forall_coprime (pow_ne_zero k hp.ne_zero) fun _ hq hqp ↦
    ((Nat.coprime_primes hq hp).mpr hqp).pow_right k

/-- Every elementary Cartier projector preserves `p`-typicality of curves. -/
theorem IsPTypical.cartierProjectorCurve {p : ℕ} {γ : F.Curve} (hγ : γ.IsPTypical p)
    (n : ℕ) (hn : n ≠ 0) (hunit : IsUnit (n : R)) :
    (F.cartierProjectorCurve n hn hunit γ).IsPTypical p :=
  fun q hq hqp ↦ by
    by_cases hqn : q ∣ n
    · rw [F.cartierProjectorCurve_eq_self n hn hunit
        (hγ.frobeniusCurve_eq_zero_of_dvd hq hqp hqn hn), hγ q hq hqp]
    · rw [F.frobeniusCurve_cartierProjectorCurve_of_coprime hq.ne_zero hn hunit
        (hq.coprime_iff_not_dvd.mpr hqn), hγ q hq hqp, map_zero]

/-- Base change along a ring homomorphism preserves `p`-typicality of curves. -/
theorem IsPTypical.map {p : ℕ} {γ : F.Curve} (hγ : γ.IsPTypical p) (φ : R →+* S) :
    (Curve.map φ γ).IsPTypical p :=
  fun q hq hqp ↦ by rw [← F.map_frobeniusCurve φ q hq.ne_zero, hγ q hq hqp, map_zero]

/-- Base change along an injective ring homomorphism preserves and reflects `p`-typicality. -/
theorem isPTypical_map_iff {φ : R →+* S} (hφ : Function.Injective φ) (p : ℕ) (γ : F.Curve) :
    (Curve.map φ γ).IsPTypical p ↔ γ.IsPTypical p := by
  refine ⟨fun h q hq hqp ↦ Curve.map_injective hφ ?_, fun h ↦ h.map φ⟩
  rw [F.map_frobeniusCurve φ q hq.ne_zero, h q hq hqp, map_zero]

/-- Pushing forward along a homomorphism of formal group laws preserves `p`-typicality. -/
theorem IsPTypical.mapCurve {p : ℕ} {γ : F.Curve} (hγ : γ.IsPTypical p)
    (f : TauCeti.FormalGroupHom F G) : (f.mapCurve γ).IsPTypical p :=
  fun q hq hqp ↦ by rw [← f.mapCurve_frobeniusCurve q hq.ne_zero, hγ q hq hqp, map_zero]

/-- An isomorphism of formal group laws preserves and reflects `p`-typicality of curves. -/
theorem isPTypical_curveEquiv_iff (e : TauCeti.FormalGroupIso F G) (p : ℕ) (γ : F.Curve) :
    (e.curveEquiv γ).IsPTypical p ↔ γ.IsPTypical p := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h' := h.mapCurve e.invHom
    rwa [← TauCeti.FormalGroupIso.curveEquiv_symm_apply, e.curveEquiv.symm_apply_apply] at h'
  · rw [TauCeti.FormalGroupIso.curveEquiv_apply]
    exact h.mapCurve e.toHom

/-- Pushing forward along the forward homomorphism of a formal-group isomorphism preserves and
reflects `p`-typicality of curves. -/
@[simp]
theorem isPTypical_toHom_mapCurve_iff (e : TauCeti.FormalGroupIso F G) (p : ℕ) (γ : F.Curve) :
    (e.toHom.mapCurve γ).IsPTypical p ↔ γ.IsPTypical p := by
  rw [← TauCeti.FormalGroupIso.curveEquiv_apply, isPTypical_curveEquiv_iff]

/-- On the additive formal group law over any commutative ring, a curve whose nonzero-degree
coefficients vanish at all multiples of primes `q ≠ p` is `p`-typical. -/
theorem isPTypical_𝔾ₐ_of_coeff_eq_zero (p : ℕ) {γ : (𝔾ₐ (R := R)).Curve}
    (hγ : ∀ q : ℕ, q.Prime → q ≠ p → ∀ k : ℕ, k ≠ 0 → q ∣ k →
      PowerSeries.coeff k γ.toPowerSeries = 0) :
    γ.IsPTypical p := by
  intro q hq hqp
  ext k
  rw [toPowerSeries_frobeniusCurve_𝔾ₐ, toPowerSeries_zero, map_zero, PowerSeries.coeff_smul,
    PowerSeries.coeff_cartier, Nat.add_zero, smul_eq_mul]
  rcases eq_or_ne k 0 with rfl | hk
  · rw [mul_zero, γ.coeff_zero_toPowerSeries, mul_zero]
  · rw [hγ q hq hqp (q * k) (mul_ne_zero hq.ne_zero hk) ⟨k, rfl⟩, mul_zero]

/-- On the additive formal group law over any commutative ring, the monomial curve `T^(p^m)` is
`p`-typical for every prime `p` and `m : ℕ`. -/
theorem isPTypical_𝔾ₐ_X_pow {p : ℕ} (hp : p.Prime) (m : ℕ) :
    (⟨PowerSeries.X ^ p ^ m, by simp [hp.ne_zero]⟩ : (𝔾ₐ (R := R)).Curve).IsPTypical p := by
  refine isPTypical_𝔾ₐ_of_coeff_eq_zero p fun q hq hqp k hk hqk ↦ ?_
  rw [PowerSeries.coeff_X_pow]
  refine ite_eq_right fun hkp ↦ ?_
  exact (forall_prime_ne_not_dvd_iff_exists_pow_eq hp hk).mpr ⟨m, hkp.symm⟩ q hq hqp hqk

/-- On the additive formal group law, when every prime `q ≠ p` is invertible in `R`, a curve is
`p`-typical if and only if its nonzero-degree coefficients vanish at all multiples of primes
`q ≠ p`. -/
theorem isPTypical_𝔾ₐ_iff_of_forall_isUnit (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (γ : (𝔾ₐ (R := R)).Curve) :
    γ.IsPTypical p ↔
      ∀ q : ℕ, q.Prime → q ≠ p → ∀ k : ℕ, k ≠ 0 → q ∣ k →
        PowerSeries.coeff k γ.toPowerSeries = 0 := by
  refine ⟨?_, isPTypical_𝔾ₐ_of_coeff_eq_zero p⟩
  rintro hγ q hq hqp _ _ ⟨m, rfl⟩
  have h0 := congrArg (fun δ : (𝔾ₐ (R := R)).Curve ↦ PowerSeries.coeff m δ.toPowerSeries)
    (hγ q hq hqp)
  simp only [toPowerSeries_frobeniusCurve_𝔾ₐ, toPowerSeries_zero, map_zero,
    PowerSeries.coeff_smul, PowerSeries.coeff_cartier, Nat.add_zero] at h0
  exact (hunit q hq hqp).smul_eq_zero.mp h0

/-- Over a `ℚ`-algebra, a curve `γ` on `F` is `p`-typical if and only if `log_F(γ(T))` has zero
coefficient in every nonzero degree divisible by a prime `q ≠ p`. -/
theorem isPTypical_iff_coeff_subst_log_eq_zero [Algebra ℚ R] (p : ℕ) (γ : F.Curve) :
    γ.IsPTypical p ↔
      ∀ q : ℕ, q.Prime → q ≠ p → ∀ k : ℕ, k ≠ 0 → q ∣ k →
        PowerSeries.coeff k (PowerSeries.subst γ.toPowerSeries F.log) = 0 := by
  have hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R) := fun q hq _ ↦ by
    have hqQ : IsUnit (q : ℚ) := Ne.isUnit (Nat.cast_ne_zero.mpr hq.ne_zero)
    simpa only [map_natCast] using hqQ.map (algebraMap ℚ R)
  rw [← isPTypical_curveEquiv_iff F.logIso p γ,
    isPTypical_𝔾ₐ_iff_of_forall_isUnit p hunit (F.logIso.curveEquiv γ)]
  simp only [TauCeti.FormalGroupIso.curveEquiv_apply, logIso_toHom,
    TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries]

/-- Over a `ℚ`-algebra and for `p` prime, a curve `γ` on `F` is `p`-typical if and only if
`log_F(γ(T))` vanishes outside the degrees `p^n`. -/
theorem isPTypical_iff_coeff_subst_log_eq_zero_of_prime [Algebra ℚ R] {p : ℕ} (hp : p.Prime)
    (γ : F.Curve) :
    γ.IsPTypical p ↔
      ∀ k : ℕ, (∀ n : ℕ, p ^ n ≠ k) →
        PowerSeries.coeff k (PowerSeries.subst γ.toPowerSeries F.log) = 0 := by
  rw [isPTypical_iff_coeff_subst_log_eq_zero p γ]
  constructor
  · intro h k hk
    rcases eq_or_ne k 0 with rfl | hk0
    · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact PowerSeries.constantCoeff_subst_eq_zero γ.constantCoeff_toPowerSeries F.log
        F.constantCoeff_log
    · have hnot : ¬ ∀ q : ℕ, q.Prime → q ≠ p → ¬ q ∣ k :=
        mt (forall_prime_ne_not_dvd_iff_exists_pow_eq hp hk0).mp (by push Not; exact hk)
      push Not at hnot
      obtain ⟨q, hq, hqp, hqk⟩ := hnot
      exact h q hq hqp k hk0 hqk
  · intro h q hq hqp k hk0 hqk
    refine h k fun n hpn ↦ ?_
    exact (forall_prime_ne_not_dvd_iff_exists_pow_eq hp hk0).mpr ⟨n, hpn⟩ q hq hqp hqk

end IsPTypical

end Curve

/-- The additive subgroup of `p`-typical curves on a commutative formal group law `F`. -/
noncomputable def pTypicalCurveSubgroup (F : FormalGroup R) [F.IsComm] (p : ℕ) :
    AddSubgroup F.Curve where
  carrier := {γ | γ.IsPTypical p}
  zero_mem' := Curve.IsPTypical.zero p
  add_mem' h₁ h₂ := h₁.add h₂
  neg_mem' h := h.neg

@[simp]
theorem mem_pTypicalCurveSubgroup (F : FormalGroup R) [F.IsComm] (p : ℕ) (γ : F.Curve) :
    γ ∈ F.pTypicalCurveSubgroup p ↔ γ.IsPTypical p :=
  ⟨id, id⟩

/-- The subgroup of `p`-typical curves is the intersection of the kernels of `f_q` over all primes
`q ≠ p`. -/
theorem pTypicalCurveSubgroup_eq_iInf_ker (F : FormalGroup R) [F.IsComm] (p : ℕ) :
    F.pTypicalCurveSubgroup p =
      ⨅ (q : ℕ) (hq : q.Prime) (_ : q ≠ p), (F.frobeniusCurve q hq.ne_zero).ker := by
  ext γ
  simp [mem_pTypicalCurveSubgroup, Curve.isPTypical_def]

/-! ### Cartier's infinite `p`-typicalization projector -/

section Projector

variable (F : FormalGroup R) [F.IsComm]

/-- Finite-stage approximation to Cartier's `p`-typicalization projector, applying the elementary
Cartier projectors `1 - V_q [q]⁻¹ f_q` at all primes `q ≤ N` with `q ≠ p`. -/
private noncomputable def pTypicalProjectorStage (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) : ℕ → (F.Curve →+ F.Curve)
  | 0 => AddMonoidHom.id F.Curve
  | N + 1 =>
    if h : (N + 1).Prime ∧ N + 1 ≠ p then
      (F.cartierProjectorCurve (N + 1) h.1.ne_zero (hunit (N + 1) h.1 h.2)).comp
        (pTypicalProjectorStage p hunit N)
    else
      pTypicalProjectorStage p hunit N

private theorem coeff_pTypicalProjectorStage_succ_of_le (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {k N : ℕ} (hk : k ≤ N) (γ : F.Curve) :
    PowerSeries.coeff k (pTypicalProjectorStage F p hunit (N + 1) γ).toPowerSeries =
      PowerSeries.coeff k (pTypicalProjectorStage F p hunit N γ).toPowerSeries := by
  rw [pTypicalProjectorStage]
  split_ifs with h
  · exact F.coeff_cartierProjectorCurve_of_lt (N + 1) h.1.ne_zero (hunit (N + 1) h.1 h.2)
      (Nat.lt_succ_of_le hk) _
  · rfl

private theorem coeff_pTypicalProjectorStage_eq_of_le (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {k N M : ℕ} (hk : k ≤ N) (hNM : N ≤ M)
    (γ : F.Curve) :
    PowerSeries.coeff k (pTypicalProjectorStage F p hunit M γ).toPowerSeries =
      PowerSeries.coeff k (pTypicalProjectorStage F p hunit N γ).toPowerSeries := by
  induction M, hNM using Nat.le_induction with
  | base => rfl
  | succ m hNm ih =>
    rw [coeff_pTypicalProjectorStage_succ_of_le F p hunit (hk.trans hNm), ih]

private theorem pTypicalProjectorStage_eq_self_of_forall_prime_gt (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {N : ℕ}
    (hgt : ∀ q : ℕ, q.Prime → q ≠ p → N < q) (γ : F.Curve) :
    pTypicalProjectorStage F p hunit N γ = γ := by
  induction N with
  | zero => rfl
  | succ n ih =>
    rw [pTypicalProjectorStage]
    split_ifs with h
    · exact absurd (hgt (n + 1) h.1 h.2) (Nat.lt_irrefl _)
    · exact ih fun q hq hqp ↦ Nat.lt_of_succ_lt (hgt q hq hqp)

private theorem pTypicalProjectorStage_eq_self (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {γ : F.Curve} (hγ : γ.IsPTypical p) :
    ∀ N : ℕ, pTypicalProjectorStage F p hunit N γ = γ
  | 0 => rfl
  | N + 1 => by
    rw [pTypicalProjectorStage]
    split_ifs with h
    · rw [AddMonoidHom.comp_apply, pTypicalProjectorStage_eq_self p hunit hγ N]
      exact F.cartierProjectorCurve_eq_self (N + 1) h.1.ne_zero (hunit (N + 1) h.1 h.2)
        (hγ (N + 1) h.1 h.2)
    · exact pTypicalProjectorStage_eq_self p hunit hγ N

private theorem map_pTypicalProjectorStage (φ : R →+* S) (p : ℕ)
    (hR : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R))
    (hS : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : S)) (N : ℕ) (γ : F.Curve) :
    Curve.map φ (pTypicalProjectorStage F p hR N γ) =
      pTypicalProjectorStage (F.map φ) p hS N (Curve.map φ γ) := by
  induction N with
  | zero => rfl
  | succ n ih =>
    simp only [pTypicalProjectorStage]
    split_ifs with h
    · rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, F.map_cartierProjectorCurve, ih]
    · exact ih

private theorem mapCurve_pTypicalProjectorStage {G : FormalGroup R} [G.IsComm]
    (f : TauCeti.FormalGroupHom F G) (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (N : ℕ) (γ : F.Curve) :
    f.mapCurve (pTypicalProjectorStage F p hunit N γ) =
      pTypicalProjectorStage G p hunit N (f.mapCurve γ) := by
  induction N with
  | zero => rfl
  | succ n ih =>
    simp only [pTypicalProjectorStage]
    split_ifs with h
    · rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, f.mapCurve_cartierProjectorCurve, ih]
    · exact ih

open scoped Classical in
private theorem coeff_pTypicalProjectorStage_𝔾ₐ (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (N k : ℕ) (γ : (𝔾ₐ (R := R)).Curve) :
    PowerSeries.coeff k (pTypicalProjectorStage (𝔾ₐ (R := R)) p hunit N γ).toPowerSeries =
      if ∃ q : ℕ, q ≤ N ∧ q.Prime ∧ q ≠ p ∧ q ∣ k then 0
      else PowerSeries.coeff k γ.toPowerSeries := by
  induction N generalizing k with
  | zero =>
    have hno : ¬ ∃ q : ℕ, q ≤ 0 ∧ q.Prime ∧ q ≠ p ∧ q ∣ k := by
      rintro ⟨q, hq0, hq, -⟩
      exact absurd (hq.two_le.trans hq0) (by omega)
    rw [ite_eq_right hno]
    rfl
  | succ n ih =>
    rw [pTypicalProjectorStage]
    by_cases h : (n + 1).Prime ∧ n + 1 ≠ p
    · rw [dite_eq_left h, AddMonoidHom.comp_apply, toPowerSeries_cartierProjectorCurve_𝔾ₐ, map_sub,
        PowerSeries.coeff_expand]
      by_cases hdvd : n + 1 ∣ k
      · have hex : ∃ q : ℕ, q ≤ n + 1 ∧ q.Prime ∧ q ≠ p ∧ q ∣ k :=
          ⟨n + 1, le_rfl, h.1, h.2, hdvd⟩
        rw [ite_eq_left hdvd, PowerSeries.coeff_cartier, Nat.add_zero,
          Nat.mul_div_cancel' hdvd, sub_self, ite_eq_left hex]
      · rw [ite_eq_right hdvd, sub_zero, ih k]
        refine if_congr ⟨fun ⟨q, hqn, hq, hqp, hqk⟩ ↦ ⟨q, Nat.le_succ_of_le hqn, hq, hqp, hqk⟩,
          fun ⟨q, hqn1, hq, hqp, hqk⟩ ↦
            ⟨q, Nat.le_of_lt_succ (lt_of_le_of_ne hqn1 fun heq ↦ hdvd (by subst heq; exact hqk)),
              hq, hqp, hqk⟩⟩ rfl rfl
    · rw [dite_eq_right h, ih k]
      refine if_congr ⟨fun ⟨q, hqn, hq, hqp, hqk⟩ ↦ ⟨q, Nat.le_succ_of_le hqn, hq, hqp, hqk⟩,
        fun ⟨q, hqn1, hq, hqp, hqk⟩ ↦
          ⟨q, Nat.le_of_lt_succ (lt_of_le_of_ne hqn1 fun heq ↦ h (by subst heq; exact ⟨hq, hqp⟩)),
            hq, hqp, hqk⟩⟩ rfl rfl

/-- **Cartier's `p`-typicalization projector** on curves of a commutative formal group law `F`,
when every prime `q ≠ p` is invertible in `R`. Defined coefficientwise by the stabilizing finite
products of elementary Cartier projectors `1 - V_q [q]⁻¹ f_q` over primes `q ≠ p`, it is an
idempotent additive endomorphism projecting `F.Curve` onto the `p`-typical curves. -/
noncomputable def pTypicalProjectorCurve (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) : F.Curve →+ F.Curve where
  toFun γ :=
    { toPowerSeries := PowerSeries.mk fun k ↦
        PowerSeries.coeff k (pTypicalProjectorStage F p hunit k γ).toPowerSeries
      constantCoeff_toPowerSeries := by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
        exact γ.coeff_zero_toPowerSeries }
  map_zero' := Curve.ext <| PowerSeries.ext fun k ↦ by
    simp [map_zero]
  map_add' γ₁ γ₂ := Curve.ext <| PowerSeries.ext fun k ↦ by
    simp only [PowerSeries.coeff_mk]
    rw [map_add (pTypicalProjectorStage F p hunit k)]
    exact Curve.coeff_add_congr
      (fun i hi ↦ by
        dsimp only
        rw [PowerSeries.coeff_mk, coeff_pTypicalProjectorStage_eq_of_le F p hunit le_rfl hi])
      (fun i hi ↦ by
        dsimp only
        rw [PowerSeries.coeff_mk, coeff_pTypicalProjectorStage_eq_of_le F p hunit le_rfl hi])

private theorem coeff_pTypicalProjectorCurve_eq_stage (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {k N : ℕ} (hk : k ≤ N) (γ : F.Curve) :
    PowerSeries.coeff k (F.pTypicalProjectorCurve p hunit γ).toPowerSeries =
      PowerSeries.coeff k (pTypicalProjectorStage F p hunit N γ).toPowerSeries := by
  dsimp only [pTypicalProjectorCurve, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [PowerSeries.coeff_mk, ← coeff_pTypicalProjectorStage_eq_of_le F p hunit le_rfl hk γ]

/-- Below every prime `q ≠ p`, Cartier's `p`-typicalization projector leaves power-series
coefficients unchanged. -/
theorem coeff_pTypicalProjectorCurve_of_forall_prime_gt (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {k : ℕ}
    (hgt : ∀ q : ℕ, q.Prime → q ≠ p → k < q) (γ : F.Curve) :
    PowerSeries.coeff k (F.pTypicalProjectorCurve p hunit γ).toPowerSeries =
      PowerSeries.coeff k γ.toPowerSeries := by
  rw [coeff_pTypicalProjectorCurve_eq_stage F p hunit le_rfl,
    pTypicalProjectorStage_eq_self_of_forall_prime_gt F p hunit hgt]

/-- Cartier's `p`-typicalization projector preserves the linear coefficient of every curve. -/
@[simp]
theorem coeff_one_pTypicalProjectorCurve (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    PowerSeries.coeff 1 (F.pTypicalProjectorCurve p hunit γ).toPowerSeries =
      PowerSeries.coeff 1 γ.toPowerSeries :=
  F.coeff_pTypicalProjectorCurve_of_forall_prime_gt p hunit (fun _ hq _ ↦ hq.one_lt) γ

/-- Base change along a ring homomorphism commutes with Cartier's `p`-typicalization projector. -/
theorem map_pTypicalProjectorCurve (φ : R →+* S) (p : ℕ)
    (hR : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    Curve.map φ (F.pTypicalProjectorCurve p hR γ) =
      (F.map φ).pTypicalProjectorCurve p
        (fun q hq hqp ↦ by simpa only [map_natCast] using (hR q hq hqp).map φ)
        (Curve.map φ γ) := by
  ext k
  rw [Curve.toPowerSeries_map, PowerSeries.coeff_map,
    coeff_pTypicalProjectorCurve_eq_stage F p hR le_rfl,
    coeff_pTypicalProjectorCurve_eq_stage (F.map φ) p _ le_rfl,
    ← map_pTypicalProjectorStage F φ p hR _ k γ, Curve.toPowerSeries_map, PowerSeries.coeff_map]

/-- Formal-group homomorphisms commute with Cartier's `p`-typicalization projector. -/
theorem _root_.TauCeti.FormalGroupHom.mapCurve_pTypicalProjectorCurve
    {F G : FormalGroup R} [F.IsComm] [G.IsComm] (f : TauCeti.FormalGroupHom F G) (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    f.mapCurve (F.pTypicalProjectorCurve p hunit γ) =
      G.pTypicalProjectorCurve p hunit (f.mapCurve γ) := by
  ext k
  have hdvd : PowerSeries.X ^ (k + 1) ∣
      (F.pTypicalProjectorCurve p hunit γ).toPowerSeries -
        (pTypicalProjectorStage F p hunit k γ).toPowerSeries :=
    PowerSeries.X_pow_dvd_iff.mpr fun i hi ↦ by
      rw [map_sub, coeff_pTypicalProjectorCurve_eq_stage F p hunit (Nat.le_of_lt_succ hi),
        sub_self]
  have hsub := PowerSeries.X_pow_dvd_iff.mp
    (PowerSeries.X_pow_dvd_subst_sub_subst
      (F.pTypicalProjectorCurve p hunit γ).constantCoeff_toPowerSeries hdvd f.toPowerSeries)
    k (Nat.lt_succ_self k)
  have heq : PowerSeries.coeff k
      (PowerSeries.subst (F.pTypicalProjectorCurve p hunit γ).toPowerSeries f.toPowerSeries) =
      PowerSeries.coeff k
        (PowerSeries.subst (pTypicalProjectorStage F p hunit k γ).toPowerSeries f.toPowerSeries) :=
    sub_eq_zero.mp (by simpa only [map_sub] using hsub)
  rw [TauCeti.FormalGroupHom.toPowerSeries_mapCurve, heq,
    ← TauCeti.FormalGroupHom.toPowerSeries_mapCurve,
    mapCurve_pTypicalProjectorStage F f p hunit k γ,
    coeff_pTypicalProjectorCurve_eq_stage G p hunit le_rfl]

/-- Formal-group isomorphisms commute with Cartier's `p`-typicalization projector. -/
theorem _root_.TauCeti.FormalGroupIso.curveEquiv_pTypicalProjectorCurve
    {F G : FormalGroup R} [F.IsComm] [G.IsComm] (e : TauCeti.FormalGroupIso F G) (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    e.curveEquiv (F.pTypicalProjectorCurve p hunit γ) =
      G.pTypicalProjectorCurve p hunit (e.curveEquiv γ) := by
  rw [TauCeti.FormalGroupIso.curveEquiv_apply, TauCeti.FormalGroupIso.curveEquiv_apply,
    e.toHom.mapCurve_pTypicalProjectorCurve]

open scoped Classical in
/-- On the additive formal group law, Cartier's `p`-typicalization projector deletes precisely the
coefficients whose degrees are divisible by a prime `q ≠ p`. -/
theorem coeff_pTypicalProjectorCurve_𝔾ₐ (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (k : ℕ) (γ : (𝔾ₐ (R := R)).Curve) :
    PowerSeries.coeff k ((𝔾ₐ (R := R)).pTypicalProjectorCurve p hunit γ).toPowerSeries =
      if ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ q ∣ k then 0 else PowerSeries.coeff k γ.toPowerSeries := by
  rcases eq_or_ne k 0 with rfl | hk0
  · rw [((𝔾ₐ (R := R)).pTypicalProjectorCurve p hunit γ).coeff_zero_toPowerSeries,
      γ.coeff_zero_toPowerSeries, ite_self]
  · rw [coeff_pTypicalProjectorCurve_eq_stage (𝔾ₐ (R := R)) p hunit le_rfl,
      coeff_pTypicalProjectorStage_𝔾ₐ]
    exact if_congr ⟨fun ⟨q, _, hq, hqp, hqk⟩ ↦ ⟨q, hq, hqp, hqk⟩,
      fun ⟨q, hq, hqp, hqk⟩ ↦ ⟨q, Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hqk, hq, hqp, hqk⟩⟩
      rfl rfl

open scoped Classical in
/-- Over a `ℚ`-algebra, Cartier's `p`-typicalization projector acts on the formal logarithm by
deleting precisely the degrees divisible by a prime `q ≠ p`. -/
theorem coeff_subst_pTypicalProjectorCurve_log [Algebra ℚ R] (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (k : ℕ) (γ : F.Curve) :
    PowerSeries.coeff k (PowerSeries.subst
      (F.pTypicalProjectorCurve p hunit γ).toPowerSeries F.log) =
      if ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ q ∣ k then 0
      else PowerSeries.coeff k (PowerSeries.subst γ.toPowerSeries F.log) := by
  have h := congrArg (fun δ : (𝔾ₐ (R := R)).Curve ↦ PowerSeries.coeff k δ.toPowerSeries)
    (F.logHom.mapCurve_pTypicalProjectorCurve p hunit γ)
  simpa only [TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries,
    coeff_pTypicalProjectorCurve_𝔾ₐ] using h

/-- Over a `ℚ`-algebra and for `p` prime, Cartier's `p`-typicalization projector acts on the formal
logarithm by keeping precisely the `p^n`-th degree terms. -/
theorem coeff_subst_pTypicalProjectorCurve_log_of_prime [Algebra ℚ R] {p : ℕ} (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (k : ℕ) (γ : F.Curve) :
    PowerSeries.coeff k (PowerSeries.subst
      (F.pTypicalProjectorCurve p hunit γ).toPowerSeries F.log) =
      if p ^ Nat.log p k = k then PowerSeries.coeff k (PowerSeries.subst γ.toPowerSeries F.log)
      else 0 := by
  rcases eq_or_ne k 0 with rfl | hk0
  · have h0 := (F.logHom.mapCurve (F.pTypicalProjectorCurve p hunit γ)).coeff_zero_toPowerSeries
    simpa only [TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries,
      Nat.log_zero_right, pow_zero, ite_eq_right one_ne_zero] using h0
  · rw [F.coeff_subst_pTypicalProjectorCurve_log p hunit k γ]
    by_cases hpow : p ^ Nat.log p k = k
    · have hno : ¬ ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ q ∣ k := by
        rintro ⟨q, hq, hqp, hqk⟩
        exact (forall_prime_ne_not_dvd_iff_exists_pow_eq hp hk0).mpr ⟨Nat.log p k, hpow⟩
          q hq hqp hqk
      rw [ite_eq_right hno, ite_eq_left hpow]
    · have hex : ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ q ∣ k := by
        by_contra hno
        push Not at hno
        obtain ⟨n, rfl⟩ := (forall_prime_ne_not_dvd_iff_exists_pow_eq hp hk0).mp hno
        exact hpow (by rw [Nat.log_pow hp.one_lt])
      rw [ite_eq_left hex, ite_eq_right hpow]

/-- Over a `ℚ`-algebra and for `p` prime, Cartier's `p`-typicalization projector leaves the
`p^n`-th logarithm coefficients unchanged. -/
theorem coeff_pow_subst_pTypicalProjectorCurve_log [Algebra ℚ R] {p : ℕ} (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (n : ℕ) (γ : F.Curve) :
    PowerSeries.coeff (p ^ n) (PowerSeries.subst
      (F.pTypicalProjectorCurve p hunit γ).toPowerSeries F.log) =
      PowerSeries.coeff (p ^ n) (PowerSeries.subst γ.toPowerSeries F.log) := by
  rw [F.coeff_subst_pTypicalProjectorCurve_log_of_prime hp hunit (p ^ n) γ,
    ite_eq_left (by rw [Nat.log_pow hp.one_lt])]

/-- Every prime Frobenius operator `f_q` with `q ≠ p` kills the image of Cartier's
`p`-typicalization projector. -/
@[simp]
theorem frobeniusCurve_pTypicalProjectorCurve (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (γ : F.Curve) :
    F.frobeniusCurve q hq.ne_zero (F.pTypicalProjectorCurve p hunit γ) = 0 :=
  Curve.eq_of_forall_ratAlgebra F γ {r : ℕ | r.Prime ∧ r ≠ p}
    (fun r hr ↦ hunit r hr.1 hr.2)
    (fun G _ h δ ↦ G.frobeniusCurve q hq.ne_zero
      (G.pTypicalProjectorCurve p (fun r hr hrp ↦ h r ⟨hr, hrp⟩) δ))
    (fun _ _ _ _ ↦ 0)
    (fun G _ _ δ ↦ by
      apply G.logIso.curveEquiv.injective
      ext k
      simp only [TauCeti.FormalGroupIso.curveEquiv_apply, logIso_toHom,
        TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries, map_zero,
        Curve.toPowerSeries_zero, G.subst_frobeniusCurve_log q hq.ne_zero,
        PowerSeries.coeff_smul, PowerSeries.coeff_cartier, Nat.add_zero, smul_eq_mul,
        G.coeff_subst_pTypicalProjectorCurve_log p _ (q * k)]
      have hex : ∃ r : ℕ, r.Prime ∧ r ≠ p ∧ r ∣ q * k := ⟨q, hq, hqp, ⟨k, rfl⟩⟩
      rw [ite_eq_left hex, mul_zero])
    (fun G _ _ _ φ δ ↦ by rw [G.map_frobeniusCurve, G.map_pTypicalProjectorCurve])
    (fun _ _ _ _ φ _ ↦ map_zero (Curve.map φ))
    (fun _ f δ ↦ by rw [f.mapCurve_frobeniusCurve, f.mapCurve_pTypicalProjectorCurve])
    (fun _ f _ ↦ map_zero f.mapCurve)

/-- The image of any curve under Cartier's `p`-typicalization projector is `p`-typical. -/
@[simp]
theorem isPTypical_pTypicalProjectorCurve (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    (F.pTypicalProjectorCurve p hunit γ).IsPTypical p :=
  fun _ hq hqp ↦ F.frobeniusCurve_pTypicalProjectorCurve p hunit hq hqp γ

/-- Cartier's `p`-typicalization projector fixes every `p`-typical curve. -/
theorem pTypicalProjectorCurve_eq_self (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {γ : F.Curve} (hγ : γ.IsPTypical p) :
    F.pTypicalProjectorCurve p hunit γ = γ := by
  ext k
  rw [coeff_pTypicalProjectorCurve_eq_stage F p hunit le_rfl,
    pTypicalProjectorStage_eq_self F p hunit hγ k]

/-- A curve is fixed by Cartier's `p`-typicalization projector if and only if it is `p`-typical. -/
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

/-- Cartier's `p`-typicalization projector is an idempotent in the endomorphism ring of curves. -/
@[simp]
theorem isIdempotentElem_pTypicalProjectorCurve (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    IsIdempotentElem (M := AddMonoid.End F.Curve) (F.pTypicalProjectorCurve p hunit) :=
  AddMonoidHom.ext (F.pTypicalProjectorCurve_pTypicalProjectorCurve p hunit)

/-- The image of Cartier's `p`-typicalization projector is precisely the subgroup of `p`-typical
curves. -/
@[simp]
theorem range_pTypicalProjectorCurve (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalProjectorCurve p hunit).range = F.pTypicalCurveSubgroup p := by
  ext γ
  simp only [AddMonoidHom.mem_range, mem_pTypicalCurveSubgroup]
  exact ⟨fun ⟨δ, hδ⟩ ↦ hδ ▸ F.isPTypical_pTypicalProjectorCurve p hunit δ,
    fun hγ ↦ ⟨γ, F.pTypicalProjectorCurve_eq_self p hunit hγ⟩⟩

/-- Cartier's `p`-typicalization projector kills `V_n γ` whenever `n ≠ 0` is divisible by a prime
`q ≠ p`. -/
theorem pTypicalProjectorCurve_verschiebungCurve_of_dvd (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {q n : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (hqn : q ∣ n) (hn : n ≠ 0) (γ : F.Curve) :
    F.pTypicalProjectorCurve p hunit (F.verschiebungCurve n hn γ) = 0 :=
  Curve.eq_of_forall_ratAlgebra F γ {r : ℕ | r.Prime ∧ r ≠ p}
    (fun r hr ↦ hunit r hr.1 hr.2)
    (fun G _ h δ ↦ G.pTypicalProjectorCurve p (fun r hr hrp ↦ h r ⟨hr, hrp⟩)
      (G.verschiebungCurve n hn δ))
    (fun _ _ _ _ ↦ 0)
    (fun G _ _ δ ↦ by
      apply G.logIso.curveEquiv.injective
      ext k
      simp only [TauCeti.FormalGroupIso.curveEquiv_apply, logIso_toHom,
        TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries, map_zero,
        Curve.toPowerSeries_zero]
      rw [G.coeff_subst_pTypicalProjectorCurve_log p _ k, G.subst_verschiebungCurve_log n hn,
        PowerSeries.coeff_expand]
      split_ifs with hex hdvd
      · rfl
      · exact (hex ⟨q, hq, hqp, hqn.trans hdvd⟩).elim
      · rfl)
    (fun G _ _ _ φ δ ↦ by rw [G.map_pTypicalProjectorCurve, G.map_verschiebungCurve])
    (fun _ _ _ _ φ _ ↦ map_zero (Curve.map φ))
    (fun _ f δ ↦ by rw [f.mapCurve_pTypicalProjectorCurve, f.mapCurve_verschiebungCurve])
    (fun _ f _ ↦ map_zero f.mapCurve)

/-- Cartier's `p`-typicalization projector kills `V_q γ` for every prime `q ≠ p`. -/
@[simp]
theorem pTypicalProjectorCurve_verschiebungCurve (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (γ : F.Curve) :
    F.pTypicalProjectorCurve p hunit (F.verschiebungCurve q hq.ne_zero γ) = 0 :=
  F.pTypicalProjectorCurve_verschiebungCurve_of_dvd p hunit hq hqp dvd_rfl hq.ne_zero γ

/-- Cartier's `p`-typicalization projector commutes with every elementary Cartier projector. -/
theorem cartierProjectorCurve_pTypicalProjectorCurve (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (n : ℕ) (hn : n ≠ 0)
    (hn_unit : IsUnit (n : R)) (γ : F.Curve) :
    F.cartierProjectorCurve n hn hn_unit (F.pTypicalProjectorCurve p hunit γ) =
      F.pTypicalProjectorCurve p hunit (F.cartierProjectorCurve n hn hn_unit γ) :=
  Curve.eq_of_forall_ratAlgebra F γ (insert n {r : ℕ | r.Prime ∧ r ≠ p})
    (by
      rintro m (rfl | ⟨hm, hmp⟩)
      · exact hn_unit
      · exact hunit m hm hmp)
    (fun G _ h δ ↦ G.cartierProjectorCurve n hn (h n (Set.mem_insert _ _))
      (G.pTypicalProjectorCurve p (fun r hr hrp ↦ h r (Set.mem_insert_of_mem _ ⟨hr, hrp⟩)) δ))
    (fun G _ h δ ↦ G.pTypicalProjectorCurve p
      (fun r hr hrp ↦ h r (Set.mem_insert_of_mem _ ⟨hr, hrp⟩))
      (G.cartierProjectorCurve n hn (h n (Set.mem_insert _ _)) δ))
    (fun G _ _ δ ↦ by
      apply G.logIso.curveEquiv.injective
      ext k
      simp only [TauCeti.FormalGroupIso.curveEquiv_apply, logIso_toHom,
        TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries,
        G.coeff_subst_cartierProjectorCurve_log n hn, G.coeff_subst_pTypicalProjectorCurve_log]
      split_ifs <;> rfl)
    (fun G _ _ _ φ δ ↦ by rw [G.map_cartierProjectorCurve, G.map_pTypicalProjectorCurve])
    (fun G _ _ _ φ δ ↦ by rw [G.map_pTypicalProjectorCurve, G.map_cartierProjectorCurve])
    (fun _ f δ ↦ by rw [f.mapCurve_cartierProjectorCurve, f.mapCurve_pTypicalProjectorCurve])
    (fun _ f δ ↦ by rw [f.mapCurve_pTypicalProjectorCurve, f.mapCurve_cartierProjectorCurve])

/-- When `p` is prime, Frobenius `f_{p^r}` of any `p`-power index commutes with Cartier's
`p`-typicalization projector. -/
theorem frobeniusCurve_pow_pTypicalProjectorCurve {p : ℕ} (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (r : ℕ) (γ : F.Curve) :
    F.frobeniusCurve (p ^ r) (pow_ne_zero r hp.ne_zero) (F.pTypicalProjectorCurve p hunit γ) =
      F.pTypicalProjectorCurve p hunit (F.frobeniusCurve (p ^ r) (pow_ne_zero r hp.ne_zero) γ) :=
  Curve.eq_of_forall_ratAlgebra F γ {q : ℕ | q.Prime ∧ q ≠ p}
    (fun q hq ↦ hunit q hq.1 hq.2)
    (fun G _ h δ ↦ G.frobeniusCurve (p ^ r) (pow_ne_zero r hp.ne_zero)
      (G.pTypicalProjectorCurve p (fun q hq hqp ↦ h q ⟨hq, hqp⟩) δ))
    (fun G _ h δ ↦ G.pTypicalProjectorCurve p (fun q hq hqp ↦ h q ⟨hq, hqp⟩)
      (G.frobeniusCurve (p ^ r) (pow_ne_zero r hp.ne_zero) δ))
    (fun G _ _ δ ↦ by
      apply G.logIso.curveEquiv.injective
      ext k
      simp only [TauCeti.FormalGroupIso.curveEquiv_apply, logIso_toHom,
        TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries,
        G.subst_frobeniusCurve_log, G.coeff_subst_pTypicalProjectorCurve_log,
        PowerSeries.coeff_smul, PowerSeries.coeff_cartier, Nat.add_zero, smul_eq_mul]
      rw [propext (exists_prime_ne_dvd_pow_mul_iff hp r k)]
      split_ifs <;> simp)
    (fun G _ _ _ φ δ ↦ by rw [G.map_frobeniusCurve, G.map_pTypicalProjectorCurve])
    (fun G _ _ _ φ δ ↦ by rw [G.map_pTypicalProjectorCurve, G.map_frobeniusCurve])
    (fun _ f δ ↦ by rw [f.mapCurve_frobeniusCurve, f.mapCurve_pTypicalProjectorCurve])
    (fun _ f δ ↦ by rw [f.mapCurve_pTypicalProjectorCurve, f.mapCurve_frobeniusCurve])

/-- When `p` is prime, Verschiebung `V_{p^r}` of any `p`-power index commutes with Cartier's
`p`-typicalization projector. -/
theorem pTypicalProjectorCurve_verschiebungCurve_pow {p : ℕ} (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (r : ℕ) (γ : F.Curve) :
    F.pTypicalProjectorCurve p hunit (F.verschiebungCurve (p ^ r) (pow_ne_zero r hp.ne_zero) γ) =
      F.verschiebungCurve (p ^ r) (pow_ne_zero r hp.ne_zero)
        (F.pTypicalProjectorCurve p hunit γ) :=
  Curve.eq_of_forall_ratAlgebra F γ {q : ℕ | q.Prime ∧ q ≠ p}
    (fun q hq ↦ hunit q hq.1 hq.2)
    (fun G _ h δ ↦ G.pTypicalProjectorCurve p (fun q hq hqp ↦ h q ⟨hq, hqp⟩)
      (G.verschiebungCurve (p ^ r) (pow_ne_zero r hp.ne_zero) δ))
    (fun G _ h δ ↦ G.verschiebungCurve (p ^ r) (pow_ne_zero r hp.ne_zero)
      (G.pTypicalProjectorCurve p (fun q hq hqp ↦ h q ⟨hq, hqp⟩) δ))
    (fun G _ _ δ ↦ by
      apply G.logIso.curveEquiv.injective
      ext k
      simp only [TauCeti.FormalGroupIso.curveEquiv_apply, logIso_toHom,
        TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries]
      by_cases hpr : p ^ r ∣ k
      · obtain ⟨m, rfl⟩ := hpr
        have hdvd' : p ^ r ∣ p ^ r * m := ⟨m, rfl⟩
        have hdiv : p ^ r * m / p ^ r = m := Nat.mul_div_cancel_left m (pow_pos hp.pos r)
        rw [G.coeff_subst_pTypicalProjectorCurve_log, G.subst_verschiebungCurve_log,
          PowerSeries.coeff_expand, ite_eq_left hdvd', G.subst_verschiebungCurve_log,
          PowerSeries.coeff_expand, ite_eq_left hdvd', hdiv,
          G.coeff_subst_pTypicalProjectorCurve_log,
          propext (exists_prime_ne_dvd_pow_mul_iff hp r m)]
      · rw [G.coeff_subst_pTypicalProjectorCurve_log, G.subst_verschiebungCurve_log,
          PowerSeries.coeff_expand, ite_eq_right hpr, G.subst_verschiebungCurve_log,
          PowerSeries.coeff_expand, ite_eq_right hpr, ite_self])
    (fun G _ _ _ φ δ ↦ by rw [G.map_pTypicalProjectorCurve, G.map_verschiebungCurve])
    (fun G _ _ _ φ δ ↦ by rw [G.map_verschiebungCurve, G.map_pTypicalProjectorCurve])
    (fun _ f δ ↦ by rw [f.mapCurve_pTypicalProjectorCurve, f.mapCurve_verschiebungCurve])
    (fun _ f δ ↦ by rw [f.mapCurve_verschiebungCurve, f.mapCurve_pTypicalProjectorCurve])

end Projector

/-! ### `p`-typical formal group laws and Hazewinkel comparison -/

section IsPTypicalLaw

/-- A commutative formal group law `F` is **`p`-typical** if its tautological curve `T` is
`p`-typical, i.e. `f_q T = 0` for every prime `q ≠ p`. -/
def IsPTypical (F : FormalGroup R) [F.IsComm] (p : ℕ) : Prop :=
  F.tautologicalCurve.IsPTypical p

/-- Unfold `FormalGroup.IsPTypical`. -/
theorem isPTypical_def (F : FormalGroup R) [F.IsComm] (p : ℕ) :
    F.IsPTypical p ↔ F.tautologicalCurve.IsPTypical p :=
  ⟨id, id⟩

/-- Equal commutative formal group laws have equivalent `p`-typicality predicates. -/
theorem isPTypical_congr {F G : FormalGroup R} [F.IsComm] [G.IsComm] (h : F = G) (p : ℕ) :
    F.IsPTypical p ↔ G.IsPTypical p := by
  subst h
  rfl

/-- The tautological curve of a `p`-typical formal group law is `p`-typical. -/
theorem IsPTypical.tautologicalCurve {F : FormalGroup R} [F.IsComm] {p : ℕ}
    (hF : F.IsPTypical p) : F.tautologicalCurve.IsPTypical p :=
  hF

/-- Base change along a ring homomorphism preserves `p`-typicality of formal group laws. -/
theorem IsPTypical.map {F : FormalGroup R} [F.IsComm] {p : ℕ} (hF : F.IsPTypical p)
    (φ : R →+* S) : (F.map φ).IsPTypical p := by
  rw [isPTypical_def, ← F.map_tautologicalCurve φ]
  exact Curve.IsPTypical.map hF φ

/-- Base change along an injective ring homomorphism preserves and reflects `p`-typicality of
formal group laws. -/
theorem isPTypical_map_iff {F : FormalGroup R} [F.IsComm] {φ : R →+* S}
    (hφ : Function.Injective φ) (p : ℕ) :
    (F.map φ).IsPTypical p ↔ F.IsPTypical p := by
  rw [isPTypical_def, isPTypical_def, ← F.map_tautologicalCurve φ, Curve.isPTypical_map_iff hφ]

/-- Transporting `F` along a formal coordinate `c` produces a `p`-typical formal group law if and
only if the inverse coordinate `c⁻¹` is a `p`-typical curve on `F`. -/
theorem isPTypical_smul_iff (F : FormalGroup R) [F.IsComm] (c : TauCeti.FormalCoordinate R)
    (p : ℕ) :
    (c • F).IsPTypical p ↔
      (⟨c⁻¹.toPowerSeries, c⁻¹.constantCoeff_toPowerSeries⟩ : F.Curve).IsPTypical p := by
  have htaut : (smulIso c F).curveEquiv ⟨c⁻¹.toPowerSeries, c⁻¹.constantCoeff_toPowerSeries⟩ =
      (c • F).tautologicalCurve := by
    ext1
    rw [TauCeti.FormalGroupIso.curveEquiv_apply, TauCeti.FormalGroupHom.toPowerSeries_mapCurve,
      smulIso_toHom_toPowerSeries, ← TauCeti.FormalCoordinate.toPowerSeries_mul, mul_inv_cancel,
      TauCeti.FormalCoordinate.toPowerSeries_one, toPowerSeries_tautologicalCurve]
  rw [isPTypical_def, ← htaut, Curve.isPTypical_curveEquiv_iff]

/-- The additive formal group law `𝔾ₐ` is `p`-typical over every commutative ring and for every
`p : ℕ`. -/
@[simp]
theorem isPTypical_𝔾ₐ (p : ℕ) : (𝔾ₐ (R := R)).IsPTypical p := by
  refine Curve.isPTypical_𝔾ₐ_of_coeff_eq_zero p fun q hq _ k _ hqk ↦ ?_
  rw [toPowerSeries_tautologicalCurve, PowerSeries.coeff_X]
  exact ite_eq_right fun hk1 : k = 1 ↦ hq.not_dvd_one (hk1 ▸ hqk)

/-- Over a `ℚ`-algebra, a commutative formal group law `F` is `p`-typical if and only if `F.log`
has zero coefficient in every nonzero degree divisible by a prime `q ≠ p`. -/
theorem isPTypical_iff_coeff_log_eq_zero [Algebra ℚ R] (F : FormalGroup R) [F.IsComm] (p : ℕ) :
    F.IsPTypical p ↔
      ∀ q : ℕ, q.Prime → q ≠ p → ∀ k : ℕ, k ≠ 0 → q ∣ k → PowerSeries.coeff k F.log = 0 := by
  rw [isPTypical_def, Curve.isPTypical_iff_coeff_subst_log_eq_zero,
    toPowerSeries_tautologicalCurve, PowerSeries.X_subst]

/-- Over a `ℚ`-algebra and for `p` prime, a commutative formal group law `F` is `p`-typical if and
only if its logarithm has no terms outside the degrees `p^n`. -/
theorem isPTypical_iff_coeff_log_eq_zero_of_prime [Algebra ℚ R] (F : FormalGroup R) [F.IsComm]
    {p : ℕ} (hp : p.Prime) :
    F.IsPTypical p ↔ ∀ k : ℕ, (∀ n : ℕ, p ^ n ≠ k) → PowerSeries.coeff k F.log = 0 := by
  rw [isPTypical_def, Curve.isPTypical_iff_coeff_subst_log_eq_zero_of_prime hp,
    toPowerSeries_tautologicalCurve, PowerSeries.X_subst]

/-- Over a `ℚ`-algebra, Hazewinkel's formal group law `TauCeti.hazewinkelFormalGroup p v` is
`p`-typical for every prime `p` and generator family `v`. -/
@[simp]
theorem _root_.TauCeti.isPTypical_hazewinkelFormalGroup [Algebra ℚ R] {p : ℕ} (hp : p.Prime)
    (v : ℕ+ → R) : (TauCeti.hazewinkelFormalGroup p v).IsPTypical p := by
  rw [isPTypical_iff_coeff_log_eq_zero_of_prime _ hp, TauCeti.log_hazewinkelFormalGroup]
  exact fun _ hk ↦ TauCeti.coeff_hazewinkelLog_eq_zero v hk

/-- **Classification of `p`-typical formal group laws over `ℚ`-algebras**: for `p` prime, a
commutative formal group law over a `ℚ`-algebra is `p`-typical if and only if it is Hazewinkel's
formal group law of some generator family `v`. -/
theorem isPTypical_iff_exists_eq_hazewinkelFormalGroup [Algebra ℚ R] (F : FormalGroup R) [F.IsComm]
    {p : ℕ} (hp : p.Prime) :
    F.IsPTypical p ↔ ∃ v : ℕ+ → R, F = TauCeti.hazewinkelFormalGroup p v :=
  ⟨fun hF ↦ (TauCeti.existsUnique_eq_hazewinkelFormalGroup hp.one_lt
      ((isPTypical_iff_coeff_log_eq_zero_of_prime F hp).mp hF)).exists,
    fun ⟨v, hv⟩ ↦ (isPTypical_congr hv p).mpr (TauCeti.isPTypical_hazewinkelFormalGroup hp v)⟩

/-- Every `p`-typical formal group law over a `ℚ`-algebra (with `p` prime) arises from a unique
family of Hazewinkel generators. -/
theorem IsPTypical.existsUnique_eq_hazewinkelFormalGroup [Algebra ℚ R] {F : FormalGroup R}
    [F.IsComm] {p : ℕ} (hp : p.Prime) (hF : F.IsPTypical p) :
    ∃! v : ℕ+ → R, F = TauCeti.hazewinkelFormalGroup p v :=
  TauCeti.existsUnique_eq_hazewinkelFormalGroup hp.one_lt
    ((isPTypical_iff_coeff_log_eq_zero_of_prime F hp).mp hF)

/-- Hazewinkel's universal integral formal group law over `ℤ[v₁, v₂, …]` is `p`-typical. -/
@[simp]
theorem _root_.TauCeti.isPTypical_universalHazewinkelIntegralFormalGroup (p : ℕ)
    [hp : Fact p.Prime] :
    (TauCeti.universalHazewinkelIntegralFormalGroup p).IsPTypical p := by
  rw [← isPTypical_map_iff (MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective) p]
  exact (isPTypical_congr (TauCeti.map_intCast_universalHazewinkelIntegralFormalGroup p) p).mpr
    (TauCeti.isPTypical_hazewinkelFormalGroup hp.out MvPolynomial.X)

/-- Hazewinkel's integral formal group law `TauCeti.hazewinkelIntegralFormalGroup p v` is
`p`-typical over any commutative ring `R` (including rings with torsion and prime
characteristic). -/
@[simp]
theorem _root_.TauCeti.isPTypical_hazewinkelIntegralFormalGroup (p : ℕ) [Fact p.Prime]
    (v : ℕ+ → R) : (TauCeti.hazewinkelIntegralFormalGroup p v).IsPTypical p :=
  (isPTypical_congr (TauCeti.hazewinkelIntegralFormalGroup_def p v) p).mpr
    ((TauCeti.isPTypical_universalHazewinkelIntegralFormalGroup p).map _)

/-- Over `ℤ`, specializing Hazewinkel's integral formal group law at `vᵢ = 1` gives a non-additive
`p`-typical formal group law. -/
theorem _root_.TauCeti.hazewinkelIntegralFormalGroup_const_one_ne_𝔾ₐ (p : ℕ) [hp : Fact p.Prime] :
    TauCeti.hazewinkelIntegralFormalGroup p (fun _ : ℕ+ ↦ (1 : ℤ)) ≠ 𝔾ₐ := by
  intro heq
  have hQ := congrArg (fun G : FormalGroup ℤ ↦ PowerSeries.coeff p (G.map (Int.castRingHom ℚ)).log)
    heq
  simp only [TauCeti.map_hazewinkelIntegralFormalGroup, Function.comp_def, map_one,
    TauCeti.hazewinkelIntegralFormalGroup_eq_hazewinkelFormalGroup,
    TauCeti.log_hazewinkelFormalGroup, pow_one (a := p) ▸
      TauCeti.coeff_hazewinkelLog_pow (fun _ : ℕ+ ↦ (1 : ℚ)) hp.out.one_lt 1,
    TauCeti.hazewinkelLogCoeff_one, smul_eq_mul, mul_one, map_𝔾ₐ, log_𝔾ₐ,
    PowerSeries.coeff_X, ite_eq_right hp.out.ne_one] at hQ
  exact inv_ne_zero (Nat.cast_ne_zero.mpr hp.out.ne_zero) hQ

end IsPTypicalLaw

/-! ### Cartier–Quillen canonical strict `p`-typicalization -/

section CanonicalTypicalization

variable (F : FormalGroup R) [F.IsComm]

/-- The strict formal coordinate whose power series is the Cartier `p`-typicalization of the
tautological curve `T`. -/
private noncomputable def pTypicalCurveCoord (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) : TauCeti.FormalCoordinate R where
  toPowerSeries := (F.pTypicalProjectorCurve p hunit F.tautologicalCurve).toPowerSeries
  constantCoeff_toPowerSeries :=
    (F.pTypicalProjectorCurve p hunit F.tautologicalCurve).constantCoeff_toPowerSeries
  isUnit_coeff_one := by
    rw [F.coeff_one_pTypicalProjectorCurve p hunit, toPowerSeries_tautologicalCurve,
      PowerSeries.coeff_one_X]
    exact isUnit_one

/-- **Cartier–Quillen's canonical `p`-typicalization coordinate**: the strict formal coordinate
whose inverse is the `p`-typical projection of `F.tautologicalCurve`, transporting `F` to a
`p`-typical formal group law. -/
noncomputable def pTypicalCoordinate (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) : TauCeti.FormalCoordinate R :=
  (pTypicalCurveCoord F p hunit)⁻¹

/-- The inverse of `F.pTypicalCoordinate` has underlying series equal to the `p`-typical projection
of the tautological curve `T`. -/
theorem inv_pTypicalCoordinate_toPowerSeries (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalCoordinate p hunit)⁻¹.toPowerSeries =
      (F.pTypicalProjectorCurve p hunit F.tautologicalCurve).toPowerSeries := by
  rw [pTypicalCoordinate, inv_inv]
  rfl

/-- `F.pTypicalCoordinate` is a strict formal coordinate: its linear coefficient is `1`. -/
@[simp]
theorem linearCoeff_pTypicalCoordinate (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    TauCeti.FormalCoordinate.linearCoeff (F.pTypicalCoordinate p hunit) = 1 := by
  rw [pTypicalCoordinate, map_inv, inv_eq_one]
  ext
  simp [pTypicalCurveCoord]

@[simp]
theorem coeff_one_pTypicalCoordinate (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    PowerSeries.coeff 1 (F.pTypicalCoordinate p hunit).toPowerSeries = 1 := by
  rw [← TauCeti.FormalCoordinate.val_linearCoeff, linearCoeff_pTypicalCoordinate, Units.val_one]

/-- Base change commutes with `F.pTypicalCoordinate`. -/
theorem map_pTypicalCoordinate (φ : R →+* S) (p : ℕ)
    (hR : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    TauCeti.FormalCoordinate.map φ (F.pTypicalCoordinate p hR) =
      (F.map φ).pTypicalCoordinate p
        (fun q hq hqp ↦ by simpa only [map_natCast] using (hR q hq hqp).map φ) := by
  rw [pTypicalCoordinate, pTypicalCoordinate, map_inv]
  congr 1
  ext1
  simp only [TauCeti.FormalCoordinate.toPowerSeries_map, pTypicalCurveCoord]
  rw [← Curve.toPowerSeries_map, F.map_pTypicalProjectorCurve φ p hR, F.map_tautologicalCurve]

/-- **Cartier–Quillen's canonical `p`-typicalization** of a commutative formal group law `F` over a
ring in which every prime `q ≠ p` is invertible, obtained by transporting `F` along
`F.pTypicalCoordinate`. -/
noncomputable def pTypicalFormalGroup (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) : FormalGroup R :=
  F.pTypicalCoordinate p hunit • F

/-- Unfold `FormalGroup.pTypicalFormalGroup` as coordinate transport along
`F.pTypicalCoordinate`. -/
theorem pTypicalFormalGroup_def (p : ℕ) (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    F.pTypicalFormalGroup p hunit = F.pTypicalCoordinate p hunit • F :=
  (rfl)

instance (p : ℕ) (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalFormalGroup p hunit).IsComm := by
  rw [pTypicalFormalGroup_def]
  infer_instance

/-- **Cartier–Quillen's canonical strict isomorphism** from `F` to its `p`-typicalization
`F.pTypicalFormalGroup`. -/
noncomputable def pTypicalIso (p : ℕ) (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    TauCeti.FormalGroupIso F (F.pTypicalFormalGroup p hunit) :=
  smulIso (F.pTypicalCoordinate p hunit) F

instance (p : ℕ) (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalIso p hunit).IsStrict :=
  (isStrict_smulIso_iff (F.pTypicalCoordinate p hunit) F).mpr
    (F.linearCoeff_pTypicalCoordinate p hunit)

@[simp]
theorem pTypicalIso_toHom_toPowerSeries (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalIso p hunit).toHom.toPowerSeries =
      (F.pTypicalCoordinate p hunit).toPowerSeries :=
  smulIso_toHom_toPowerSeries _ _

@[simp]
theorem pTypicalIso_invHom_toPowerSeries (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalIso p hunit).invHom.toPowerSeries =
      (F.pTypicalProjectorCurve p hunit F.tautologicalCurve).toPowerSeries := by
  rw [pTypicalIso, smulIso_invHom_toPowerSeries, inv_pTypicalCoordinate_toPowerSeries]

/-- `F.pTypicalIso` carries the `p`-typical projection of `F.tautologicalCurve` to the tautological
curve of `F.pTypicalFormalGroup`. -/
theorem pTypicalIso_curveEquiv_pTypicalProjectorCurve_tautologicalCurve (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalIso p hunit).curveEquiv (F.pTypicalProjectorCurve p hunit F.tautologicalCurve) =
      (F.pTypicalFormalGroup p hunit).tautologicalCurve := by
  ext1
  rw [TauCeti.FormalGroupIso.curveEquiv_apply, TauCeti.FormalGroupHom.toPowerSeries_mapCurve,
    pTypicalIso_toHom_toPowerSeries, ← inv_pTypicalCoordinate_toPowerSeries,
    ← TauCeti.FormalCoordinate.toPowerSeries_mul, mul_inv_cancel,
    TauCeti.FormalCoordinate.toPowerSeries_one, toPowerSeries_tautologicalCurve]

@[simp]
theorem pTypicalIso_toHom_mapCurve_pTypicalProjectorCurve_tautologicalCurve (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalIso p hunit).toHom.mapCurve (F.pTypicalProjectorCurve p hunit F.tautologicalCurve) =
      (F.pTypicalFormalGroup p hunit).tautologicalCurve := by
  rw [← TauCeti.FormalGroupIso.curveEquiv_apply,
    pTypicalIso_curveEquiv_pTypicalProjectorCurve_tautologicalCurve]

/-- The canonical `p`-typicalization `F.pTypicalFormalGroup` is a `p`-typical formal group law. -/
@[simp]
theorem isPTypical_pTypicalFormalGroup (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalFormalGroup p hunit).IsPTypical p := by
  rw [(isPTypical_congr (F.pTypicalFormalGroup_def p hunit) p), isPTypical_smul_iff]
  simpa only [inv_pTypicalCoordinate_toPowerSeries] using
    F.isPTypical_pTypicalProjectorCurve p hunit F.tautologicalCurve

/-- When `F` is already `p`-typical, its canonical `p`-typicalization coordinate is the identity
coordinate `1`. -/
theorem pTypicalCoordinate_eq_one_of_isPTypical (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (hF : F.IsPTypical p) :
    F.pTypicalCoordinate p hunit = 1 := by
  apply inv_injective
  ext1
  rw [inv_one, inv_pTypicalCoordinate_toPowerSeries, F.pTypicalProjectorCurve_eq_self p hunit hF,
    toPowerSeries_tautologicalCurve, TauCeti.FormalCoordinate.toPowerSeries_one]

/-- `F.pTypicalCoordinate` is the identity coordinate if and only if `F` is `p`-typical. -/
@[simp]
theorem pTypicalCoordinate_eq_one_iff (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    F.pTypicalCoordinate p hunit = 1 ↔ F.IsPTypical p := by
  refine ⟨fun h ↦ ?_, F.pTypicalCoordinate_eq_one_of_isPTypical p hunit⟩
  have h1 : F.pTypicalFormalGroup p hunit = F := by
    rw [pTypicalFormalGroup_def, h, one_smul]
  exact (isPTypical_congr h1 p).mp (F.isPTypical_pTypicalFormalGroup p hunit)

/-- When `F` is already `p`-typical, its canonical `p`-typicalization is `F` itself. -/
theorem pTypicalFormalGroup_eq_self_of_isPTypical (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (hF : F.IsPTypical p) :
    F.pTypicalFormalGroup p hunit = F := by
  rw [pTypicalFormalGroup_def, F.pTypicalCoordinate_eq_one_of_isPTypical p hunit hF, one_smul]

/-- A commutative formal group law is fixed by canonical `p`-typicalization if and only if it is
`p`-typical. -/
theorem pTypicalFormalGroup_eq_self_iff (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    F.pTypicalFormalGroup p hunit = F ↔ F.IsPTypical p :=
  ⟨fun h ↦ (isPTypical_congr h p).mp (F.isPTypical_pTypicalFormalGroup p hunit),
    F.pTypicalFormalGroup_eq_self_of_isPTypical p hunit⟩

/-- Canonical `p`-typicalization of formal group laws is idempotent. -/
@[simp]
theorem pTypicalFormalGroup_pTypicalFormalGroup (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalFormalGroup p hunit).pTypicalFormalGroup p hunit =
      F.pTypicalFormalGroup p hunit :=
  (F.pTypicalFormalGroup p hunit).pTypicalFormalGroup_eq_self_of_isPTypical p hunit
    (F.isPTypical_pTypicalFormalGroup p hunit)

/-- Base change commutes with canonical `p`-typicalization of formal group laws. -/
theorem map_pTypicalFormalGroup (φ : R →+* S) (p : ℕ)
    (hR : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalFormalGroup p hR).map φ =
      (F.map φ).pTypicalFormalGroup p
        (fun q hq hqp ↦ by simpa only [map_natCast] using (hR q hq hqp).map φ) := by
  rw [pTypicalFormalGroup_def, pTypicalFormalGroup_def, map_smul, F.map_pTypicalCoordinate φ p hR]

/-- Over a `ℚ`-algebra, the logarithm of `F.pTypicalFormalGroup` is the logarithm of `F` evaluated
at the `p`-typical projection of the tautological curve. -/
theorem log_pTypicalFormalGroup [Algebra ℚ R] (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalFormalGroup p hunit).log =
      PowerSeries.subst (F.pTypicalProjectorCurve p hunit F.tautologicalCurve).toPowerSeries
        F.log := by
  rw [pTypicalFormalGroup_def, log_smul, linearCoeff_pTypicalCoordinate, Units.val_one, one_smul,
    inv_pTypicalCoordinate_toPowerSeries]

open scoped Classical in
/-- **Quillen's logarithm formula**: over a `ℚ`-algebra, the logarithm of `F.pTypicalFormalGroup`
is obtained from `F.log` by deleting every degree divisible by a prime `q ≠ p` and leaving all other
coefficients unchanged. -/
theorem coeff_log_pTypicalFormalGroup [Algebra ℚ R] (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (k : ℕ) :
    PowerSeries.coeff k (F.pTypicalFormalGroup p hunit).log =
      if ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ q ∣ k then 0 else PowerSeries.coeff k F.log := by
  rw [F.log_pTypicalFormalGroup p hunit, F.coeff_subst_pTypicalProjectorCurve_log p hunit k,
    toPowerSeries_tautologicalCurve, PowerSeries.X_subst]

/-- Over a `ℚ`-algebra and for `p` prime, the logarithm of `F.pTypicalFormalGroup` keeps precisely
the `p^n`-th degree terms of `F.log`. -/
theorem coeff_log_pTypicalFormalGroup_of_prime [Algebra ℚ R] {p : ℕ} (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (k : ℕ) :
    PowerSeries.coeff k (F.pTypicalFormalGroup p hunit).log =
      if p ^ Nat.log p k = k then PowerSeries.coeff k F.log else 0 := by
  rw [F.log_pTypicalFormalGroup p hunit,
    F.coeff_subst_pTypicalProjectorCurve_log_of_prime hp hunit k,
    toPowerSeries_tautologicalCurve, PowerSeries.X_subst]

/-- Over a `ℚ`-algebra and for `p` prime, `F.pTypicalFormalGroup` has the same `p^n`-th logarithm
coefficients as `F`. -/
@[simp]
theorem coeff_pow_log_pTypicalFormalGroup [Algebra ℚ R] {p : ℕ} (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (n : ℕ) :
    PowerSeries.coeff (p ^ n) (F.pTypicalFormalGroup p hunit).log =
      PowerSeries.coeff (p ^ n) F.log := by
  rw [F.log_pTypicalFormalGroup p hunit, F.coeff_pow_subst_pTypicalProjectorCurve_log hp hunit n,
    toPowerSeries_tautologicalCurve, PowerSeries.X_subst]

end CanonicalTypicalization

end FormalGroup
