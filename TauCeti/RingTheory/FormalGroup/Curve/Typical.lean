/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Log
public import TauCeti.RingTheory.FormalGroup.Curve.Projector
import TauCeti.Data.Nat.Factorization.Basic
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Typical curves and Cartier's `p`-typicalization projector

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
nonzero degree divisible by a prime `q ≠ p` (equivalently, when `p` is prime, in every degree
outside the powers `p^n`).

When every prime `q ≠ p` is invertible in `R`, iterating the commuting elementary Cartier projectors
`1 - V_q [q]⁻¹ f_q` from `FormalGroup.cartierProjectorCurve` across primes `q ≠ p` stabilizes in
each power-series degree `k` as soon as all primes `q ≤ k` have been applied, because `V_q` vanishes
below degree `q`. Taking the stabilized coefficient in each degree constructs **Cartier's
`p`-typicalization projector** `FormalGroup.pTypicalProjectorCurve`: an idempotent additive
endomorphism `F.Curve →+ F.Curve` with image `F.pTypicalCurveSubgroup p` that preserves linear
coefficients, annihilates `V_n` whenever a prime `q ≠ p` divides `n`, and commutes with base change,
homomorphisms of formal group laws, elementary Cartier projectors, and (for `p` prime) `f_{p^r}` and
`V_{p^r}`. See `TauCeti.RingTheory.FormalGroup.Typical` for `p`-typical formal group laws, the
Hazewinkel classification, and Cartier–Quillen's canonical strict `p`-typicalization.

## Main definitions

* `FormalGroup.Curve.IsPTypical`: predicate that a curve `γ` on `F` satisfies `f_q γ = 0` for every
  prime `q ≠ p`.
* `FormalGroup.pTypicalCurveSubgroup`: the additive subgroup of `p`-typical curves in `F.Curve`.
* `FormalGroup.pTypicalProjectorCurve`: Cartier's idempotent `p`-typicalization projector
  `F.Curve →+ F.Curve` when every prime `q ≠ p` is a unit in `R`.

## Main results

* `FormalGroup.Curve.IsPTypical.frobeniusCurve_eq_zero_of_coprime` and
  `FormalGroup.Curve.isPTypical_iff_forall_coprime`: vanishing at coprime indices `n > 1`, and
  equivalence when `p` is prime.
* `FormalGroup.Curve.isPTypical_iff_coeff_subst_log_eq_zero_of_prime`: rational logarithm
  characterization of `p`-typical curves.
* `FormalGroup.isPTypical_pTypicalProjectorCurve`, `FormalGroup.pTypicalProjectorCurve_eq_self_iff`,
  `FormalGroup.pTypicalProjectorCurve_pTypicalProjectorCurve`, and
  `FormalGroup.range_pTypicalProjectorCurve`: Cartier's projector lands in `p`-typical curves, fixes
  precisely the `p`-typical curves, and is idempotent with image `F.pTypicalCurveSubgroup p`.
* `FormalGroup.frobeniusCurve_pow_pTypicalProjectorCurve` and
  `FormalGroup.pTypicalProjectorCurve_verschiebungCurve_pow`: commutation of Cartier's projector
  with `f_{p^r}` and `V_{p^r}` when `p` is prime.

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
  refine isPTypical_𝔾ₐ_of_coeff_eq_zero p fun q hq hqp k _ hqk ↦ ?_
  rw [PowerSeries.coeff_X_pow]
  refine ite_eq_right fun hkp ↦ ?_
  exact hp.forall_prime_ne_not_dvd_iff_exists_pow_eq.mpr ⟨m, hkp.symm⟩ q hq hqp hqk

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
        mt hp.forall_prime_ne_not_dvd_iff_exists_pow_eq.mp (by push Not; exact hk)
      push Not at hnot
      obtain ⟨q, hq, hqp, hqk⟩ := hnot
      exact h q hq hqp k hk0 hqk
  · intro h q hq hqp k _ hqk
    refine h k fun n hpn ↦ ?_
    exact hp.forall_prime_ne_not_dvd_iff_exists_pow_eq.mpr ⟨n, hpn⟩ q hq hqp hqk

end IsPTypical

end Curve

/-- The additive subgroup of `p`-typical curves on a commutative formal group law `F`. -/
noncomputable def pTypicalCurveSubgroup (F : FormalGroup R) [F.IsComm] (p : ℕ) :
    AddSubgroup F.Curve where
  carrier := {γ | γ.IsPTypical p}
  zero_mem' := Curve.IsPTypical.zero p
  add_mem' h₁ h₂ := h₁.add h₂
  neg_mem' h := h.neg

/-- Membership in `F.pTypicalCurveSubgroup p` is `p`-typicality. -/
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
        exact hp.forall_prime_ne_not_dvd_iff_exists_pow_eq.mpr ⟨Nat.log p k, hpow⟩ q hq hqp hqk
      rw [ite_eq_right hno, ite_eq_left hpow]
    · have hex : ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ q ∣ k := by
        by_contra hno
        push Not at hno
        obtain ⟨n, rfl⟩ := hp.forall_prime_ne_not_dvd_iff_exists_pow_eq.mp hno
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
      classical
      apply G.logIso.curveEquiv.injective
      ext k
      simp only [TauCeti.FormalGroupIso.curveEquiv_apply, logIso_toHom,
        TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries,
        G.subst_frobeniusCurve_log, G.coeff_subst_pTypicalProjectorCurve_log,
        PowerSeries.coeff_smul, PowerSeries.coeff_cartier, Nat.add_zero, smul_eq_mul]
      have hiff : (∃ q : ℕ, q.Prime ∧ q ≠ p ∧ q ∣ p ^ r * k) ↔
          ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ q ∣ k :=
        exists_congr fun q ↦ and_congr_right fun hq ↦ and_congr_right fun hqp ↦
          (((Nat.coprime_primes hq hp).mpr hqp).pow_right r).dvd_mul_left
      rw [if_congr hiff rfl rfl]
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
      classical
      apply G.logIso.curveEquiv.injective
      ext k
      simp only [TauCeti.FormalGroupIso.curveEquiv_apply, logIso_toHom,
        TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries]
      by_cases hpr : p ^ r ∣ k
      · obtain ⟨m, rfl⟩ := hpr
        have hdvd' : p ^ r ∣ p ^ r * m := ⟨m, rfl⟩
        have hdiv : p ^ r * m / p ^ r = m := Nat.mul_div_cancel_left m (pow_pos hp.pos r)
        have hiff : (∃ q : ℕ, q.Prime ∧ q ≠ p ∧ q ∣ p ^ r * m) ↔
            ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ q ∣ m :=
          exists_congr fun q ↦ and_congr_right fun hq ↦ and_congr_right fun hqp ↦
            (((Nat.coprime_primes hq hp).mpr hqp).pow_right r).dvd_mul_left
        rw [G.coeff_subst_pTypicalProjectorCurve_log, G.subst_verschiebungCurve_log,
          PowerSeries.coeff_expand, ite_eq_left hdvd', G.subst_verschiebungCurve_log,
          PowerSeries.coeff_expand, ite_eq_left hdvd', hdiv,
          G.coeff_subst_pTypicalProjectorCurve_log]
        exact if_congr hiff rfl rfl
      · rw [G.coeff_subst_pTypicalProjectorCurve_log, G.subst_verschiebungCurve_log,
          PowerSeries.coeff_expand, ite_eq_right hpr, G.subst_verschiebungCurve_log,
          PowerSeries.coeff_expand, ite_eq_right hpr, ite_self])
    (fun G _ _ _ φ δ ↦ by rw [G.map_pTypicalProjectorCurve, G.map_verschiebungCurve])
    (fun G _ _ _ φ δ ↦ by rw [G.map_verschiebungCurve, G.map_pTypicalProjectorCurve])
    (fun _ f δ ↦ by rw [f.mapCurve_pTypicalProjectorCurve, f.mapCurve_verschiebungCurve])
    (fun _ f δ ↦ by rw [f.mapCurve_verschiebungCurve, f.mapCurve_pTypicalProjectorCurve])

end Projector

end FormalGroup
