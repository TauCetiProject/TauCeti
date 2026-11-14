/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Curve.Projector
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log

/-!
# `p`-typical curves and Cartier's prime-to-`p` projector

Let `F` be a commutative one-dimensional formal group law over a commutative ring `R`, and let
`p` be a natural number (in applications a prime). A curve `γ ∈ F.Curve` is **`p`-typical**
(`FormalGroup.Curve.IsPTypical`) if Cartier's Frobenius operator `f_q` annihilates `γ` for every
prime `q ≠ p`. When `p` is prime, Cartier's composition law `f_m ∘ f_n = f_{m n}` implies that a
curve is `p`-typical if and only if `f_n γ = 0` for every nonzero `n` that is not a power of `p`,
over an arbitrary commutative ring without any torsion-freeness assumption.

`p`-typical curves form an additive subgroup `FormalGroup.pTypicalCurves F p` of `F.Curve`. They
are preserved by base change (and reflected along injective ring homomorphisms), by homomorphisms
of formal group laws, by all Frobenius operators `f_n`, and by Verschiebung operators `V_n` whose
index is coprime to every prime `q ≠ p` (in particular by `V_{p ^ k}` when `p` is prime). Over a
`ℚ`-algebra, for `p` prime, a curve `γ` is `p`-typical if and only if `log_F(γ(T))` has nonzero
coefficients only in degrees `p ^ m`.

When every prime `q ≠ p` is invertible in `R` (for instance when `R` is a `ℤ_{(p)}`-algebra or a
`ℚ`-algebra), the elementary Cartier projectors `π_q = 1 - V_q [q]⁻¹ f_q` for primes `q ≠ p`
commute pairwise and leave coefficients below degree `q` unchanged. Their `X`-adic infinite
composite defines **Cartier's prime-to-`p` projector** (`FormalGroup.pTypicalProjectorCurve`), an
idempotent additive endomorphism `Π_p : F.Curve →+ F.Curve` with image `F.pTypicalCurves p` that
absorbs every `π_q` (`q ≠ p` prime), kills every `V_q γ` (`q ≠ p` prime), commutes with `V_n` and
`f_n` whenever `n` is coprime to all primes `q ≠ p` (in particular with `V_{p ^ k}` and
`f_{p ^ k}` when `p` is prime), preserves linear coefficients, commutes with base change and
formal-group homomorphisms, and over a `ℚ`-algebra deletes all non-`p`-power degrees of
`log_F(γ(T))`.

## Main definitions

* `FormalGroup.Curve.IsPTypical`: `γ` is `p`-typical if `f_q γ = 0` for all primes `q ≠ p`.
* `FormalGroup.pTypicalCurves`: the additive subgroup of `p`-typical curves on `F`.
* `TauCeti.FormalGroupIso.pTypicalCurvesEquiv`: equivalence of `p`-typical curve subgroups induced
  by an isomorphism of formal group laws.
* `FormalGroup.pTypicalProjectorCurve`: Cartier's prime-to-`p` idempotent projector
  `F.Curve →+ F.Curve` when primes `q ≠ p` are invertible in `R`.
* `FormalGroup.pTypicalCurveEquiv`: the direct-sum decomposition
  `F.Curve ≃+ F.pTypicalCurves p × (F.pTypicalProjectorCurve p hunit).ker`.

## Main results

* `FormalGroup.Curve.isPTypical_iff_forall_frobeniusCurve_eq_zero`: for `p` prime, `γ` is
  `p`-typical iff `f_n γ = 0` whenever `n ≠ 0` is not a power of `p`.
* `FormalGroup.Curve.isPTypical_verschiebungCurve_pow_iff`: for `p` prime, `V_{p ^ k} γ` is
  `p`-typical iff `γ` is `p`-typical.
* `FormalGroup.Curve.isPTypical_iff_coeff_subst_log_eq_zero`: over a `ℚ`-algebra and for `p` prime,
  `γ` is `p`-typical iff `log_F(γ(T))` vanishes outside degrees `p ^ m`.
* `FormalGroup.isPTypical_pTypicalProjectorCurve`,
  `FormalGroup.pTypicalProjectorCurve_eq_self_iff`, and
  `FormalGroup.isIdempotentElem_pTypicalProjectorCurve`: `Π_p` lands in `p`-typical curves, fixes
  precisely the `p`-typical curves, and is idempotent.
* `FormalGroup.pTypicalProjectorCurve_verschiebungCurve_pow` and
  `FormalGroup.frobeniusCurve_pTypicalProjectorCurve_pow`: for `p` prime, `Π_p` commutes with
  `V_{p ^ k}` and `f_{p ^ k}`.
* `FormalGroup.map_pTypicalProjectorCurve` and
  `TauCeti.FormalGroupHom.mapCurve_pTypicalProjectorCurve`: naturality of `Π_p`.
* `FormalGroup.coeff_subst_pTypicalProjectorCurve_log_of_prime`: over a `ℚ`-algebra and for `p`
  prime, `log_F((Π_p γ)(T))` retains the `p ^ m`-coefficients of `log_F(γ(T))` and zeroes all
  others.

## References

* P. Cartier, *Modules associés à un groupe formel commutatif. Courbes typiques*, C. R. Acad. Sci.
  Paris Sér. A-B 265 (1967), A129–A132.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapter III, §16.3.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Academic Press (1986),
  Appendix A2.1.21–A2.1.23.
-/

public section

namespace FormalGroup

variable {R S : Type*} [CommRing R] [CommRing S]

/-- For a prime `p`, a natural number `k` has no prime divisor distinct from `p` if and only if
`k` is a power of `p`. -/
private theorem forall_prime_ne_not_dvd_iff_exists_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (∀ q : ℕ, q.Prime → q ≠ p → ¬ q ∣ k) ↔ ∃ m : ℕ, p ^ m = k := by
  constructor
  · intro hk
    rcases eq_or_ne k 0 with rfl | hk0
    · obtain ⟨q, hqp1, hq⟩ := Nat.exists_infinite_primes (p + 1)
      exact False.elim (hk q hq (by omega) (dvd_zero q))
    · by_cases h1 : ordCompl[p] k = 1
      · exact ⟨k.factorization p, by
          simpa only [h1, mul_one] using Nat.ordProj_mul_ordCompl_eq_self k p⟩
      · obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd h1
        have hqp : q ≠ p := fun hEq ↦ Nat.not_dvd_ordCompl hp hk0 (hEq ▸ hqd)
        exact False.elim (hk q hq hqp (hqd.trans (Nat.ordCompl_dvd k p)))
  · rintro ⟨m, rfl⟩ q hq hqp hqd
    exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hqd))

private theorem pow_log_eq_self_iff_exists_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    p ^ Nat.log p k = k ↔ ∃ m : ℕ, p ^ m = k :=
  ⟨fun h ↦ ⟨Nat.log p k, h⟩, fun ⟨m, hm⟩ ↦ hm ▸ by rw [Nat.log_pow hp.one_lt]⟩

/-! ### `p`-typical curves -/

namespace Curve

variable {F : FormalGroup R} [F.IsComm]

/-- A curve `γ` on a commutative formal group law `F` is **`p`-typical** if Cartier's Frobenius
operator `f_q` annihilates `γ` for every prime `q ≠ p`. -/
def IsPTypical (γ : F.Curve) (p : ℕ) : Prop :=
  ∀ q : ℕ, (hq : q.Prime) → q ≠ p → F.frobeniusCurve q hq.ne_zero γ = 0

/-- Unfold `FormalGroup.Curve.IsPTypical`. -/
theorem isPTypical_iff {γ : F.Curve} {p : ℕ} :
    γ.IsPTypical p ↔ ∀ q : ℕ, (hq : q.Prime) → q ≠ p → F.frobeniusCurve q hq.ne_zero γ = 0 :=
  Iff.rfl

/-- If `γ` is `p`-typical, then `f_n γ = 0` whenever `n` is divisible by a prime `q ≠ p`. -/
theorem IsPTypical.frobeniusCurve_eq_zero_of_prime_dvd {γ : F.Curve} {p : ℕ} (hγ : γ.IsPTypical p)
    {n q : ℕ} (hn : n ≠ 0) (hq : q.Prime) (hqp : q ≠ p) (hqn : q ∣ n) :
    F.frobeniusCurve n hn γ = 0 := by
  obtain ⟨m, rfl⟩ := hqn
  have hm : m ≠ 0 := right_ne_zero_of_mul hn
  rw [F.frobeniusCurve_congr (Nat.mul_comm q m) hn (mul_ne_zero hm hq.ne_zero),
    ← F.frobeniusCurve_frobeniusCurve hm hq.ne_zero, hγ q hq hqp, map_zero]

/-- For a prime `p`, a curve `γ` on a commutative formal group law over any commutative ring is
`p`-typical if and only if `f_n γ = 0` for every nonzero `n` that is not a power of `p`. -/
theorem isPTypical_iff_forall_frobeniusCurve_eq_zero {γ : F.Curve} {p : ℕ} (hp : p.Prime) :
    γ.IsPTypical p ↔
      ∀ n : ℕ, (hn : n ≠ 0) → (∀ k : ℕ, p ^ k ≠ n) → F.frobeniusCurve n hn γ = 0 := by
  constructor
  · intro hγ n hn hpow
    have hnot : ¬ ∀ q : ℕ, q.Prime → q ≠ p → ¬ q ∣ n :=
      mt (forall_prime_ne_not_dvd_iff_exists_pow hp n).mp (not_exists.mpr hpow)
    push Not at hnot
    obtain ⟨q, hq, hqp, hqn⟩ := hnot
    exact hγ.frobeniusCurve_eq_zero_of_prime_dvd hn hq hqp hqn
  · intro h q hq hqp
    refine h q hq.ne_zero fun k hk ↦ hqp ?_
    exact (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow (dvd_of_eq hk.symm))

@[simp]
theorem IsPTypical.zero (p : ℕ) : (0 : F.Curve).IsPTypical p :=
  fun q hq _ ↦ map_zero (F.frobeniusCurve q hq.ne_zero)

theorem IsPTypical.add {γ₁ γ₂ : F.Curve} {p : ℕ} (h₁ : γ₁.IsPTypical p) (h₂ : γ₂.IsPTypical p) :
    (γ₁ + γ₂).IsPTypical p :=
  fun q hq hqp ↦ by rw [map_add, h₁ q hq hqp, h₂ q hq hqp, _root_.add_zero]

theorem IsPTypical.neg {γ : F.Curve} {p : ℕ} (hγ : γ.IsPTypical p) : (-γ).IsPTypical p :=
  fun q hq hqp ↦ by rw [map_neg, hγ q hq hqp, neg_zero]

@[simp]
theorem isPTypical_neg_iff {γ : F.Curve} {p : ℕ} : (-γ).IsPTypical p ↔ γ.IsPTypical p :=
  ⟨fun h ↦ neg_neg γ ▸ h.neg, IsPTypical.neg⟩

theorem IsPTypical.sub {γ₁ γ₂ : F.Curve} {p : ℕ} (h₁ : γ₁.IsPTypical p) (h₂ : γ₂.IsPTypical p) :
    (γ₁ - γ₂).IsPTypical p :=
  fun q hq hqp ↦ by rw [map_sub, h₁ q hq hqp, h₂ q hq hqp, sub_zero]

theorem IsPTypical.nsmul {γ : F.Curve} {p : ℕ} (hγ : γ.IsPTypical p) (n : ℕ) :
    (n • γ).IsPTypical p :=
  fun q hq hqp ↦ by rw [map_nsmul, hγ q hq hqp, smul_zero]

theorem IsPTypical.zsmul {γ : F.Curve} {p : ℕ} (hγ : γ.IsPTypical p) (n : ℤ) :
    (n • γ).IsPTypical p :=
  fun q hq hqp ↦ by rw [map_zsmul, hγ q hq hqp, smul_zero]

/-- Base change preserves `p`-typicality of curves. -/
theorem IsPTypical.map {γ : F.Curve} {p : ℕ} (hγ : γ.IsPTypical p) (φ : R →+* S) :
    (Curve.map φ γ).IsPTypical p := fun q hq hqp ↦ by
  rw [← F.map_frobeniusCurve φ q hq.ne_zero, hγ q hq hqp, map_zero]

/-- Base change along an injective ring homomorphism preserves and reflects `p`-typicality of
curves. -/
@[simp]
theorem isPTypical_map_iff {γ : F.Curve} {p : ℕ} {φ : R →+* S} (hφ : Function.Injective φ) :
    (Curve.map φ γ).IsPTypical p ↔ γ.IsPTypical p := by
  refine ⟨fun h q hq hqp ↦ Curve.map_injective hφ ?_, fun h ↦ h.map φ⟩
  rw [F.map_frobeniusCurve φ q hq.ne_zero, h q hq hqp, map_zero]

/-- Every Frobenius operator `f_n` preserves `p`-typical curves. -/
theorem IsPTypical.frobeniusCurve {γ : F.Curve} {p : ℕ} (hγ : γ.IsPTypical p) (n : ℕ)
    (hn : n ≠ 0) : (F.frobeniusCurve n hn γ).IsPTypical p := fun q hq hqp ↦ by
  rw [F.frobeniusCurve_frobeniusCurve hq.ne_zero hn,
    F.frobeniusCurve_congr (Nat.mul_comm q n) (mul_ne_zero hq.ne_zero hn)
      (mul_ne_zero hn hq.ne_zero),
    ← F.frobeniusCurve_frobeniusCurve hn hq.ne_zero, hγ q hq hqp, map_zero]

/-- Verschiebung `V_n` preserves and reflects `p`-typicality whenever `n` is coprime to every prime
`q ≠ p`. -/
theorem isPTypical_verschiebungCurve_iff_of_coprime {γ : F.Curve} {p n : ℕ} (hn : n ≠ 0)
    (hcop : ∀ q : ℕ, q.Prime → q ≠ p → q.Coprime n) :
    (F.verschiebungCurve n hn γ).IsPTypical p ↔ γ.IsPTypical p := by
  constructor
  · intro h q hq hqp
    apply F.verschiebungCurve_injective n hn
    rw [map_zero, ← F.frobeniusCurve_verschiebungCurve_of_coprime hq.ne_zero hn (hcop q hq hqp)]
    exact h q hq hqp
  · intro h q hq hqp
    rw [F.frobeniusCurve_verschiebungCurve_of_coprime hq.ne_zero hn (hcop q hq hqp),
      h q hq hqp, map_zero]

/-- Verschiebung `V_n` preserves `p`-typical curves whenever `n` is coprime to every prime
`q ≠ p`. -/
theorem IsPTypical.verschiebungCurve_of_coprime {γ : F.Curve} {p : ℕ} (hγ : γ.IsPTypical p)
    {n : ℕ} (hn : n ≠ 0) (hcop : ∀ q : ℕ, q.Prime → q ≠ p → q.Coprime n) :
    (F.verschiebungCurve n hn γ).IsPTypical p :=
  (isPTypical_verschiebungCurve_iff_of_coprime hn hcop).mpr hγ

/-- For a prime `p`, `V_{p ^ k} γ` is `p`-typical if and only if `γ` is `p`-typical. -/
@[simp]
theorem isPTypical_verschiebungCurve_pow_iff {γ : F.Curve} {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (F.verschiebungCurve (p ^ k) (pow_ne_zero k hp.ne_zero) γ).IsPTypical p ↔ γ.IsPTypical p :=
  isPTypical_verschiebungCurve_iff_of_coprime (pow_ne_zero k hp.ne_zero) fun q hq hqp ↦ by
    simpa only [pow_one] using Nat.coprime_pow_primes 1 k hq hp hqp

/-- On the additive formal group law over a ring in which every prime `q ≠ p` is invertible, a
curve is `p`-typical if and only if its coefficients vanish in all degrees divisible by a prime
`q ≠ p`. -/
theorem isPTypical_𝔾ₐ_iff (p : ℕ) (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R))
    (γ : (𝔾ₐ (R := R)).Curve) :
    γ.IsPTypical p ↔
      ∀ k : ℕ, (∃ q : ℕ, q.Prime ∧ q ≠ p ∧ q ∣ k) → PowerSeries.coeff k γ.toPowerSeries = 0 := by
  constructor
  · rintro hγ k ⟨q, hq, hqp, m, rfl⟩
    have h0 := congrArg (PowerSeries.coeff m ∘ Curve.toPowerSeries) (hγ q hq hqp)
    simp only [Function.comp_apply, toPowerSeries_frobeniusCurve_𝔾ₐ, toPowerSeries_zero,
      PowerSeries.coeff_smul, PowerSeries.coeff_cartier, Nat.add_zero, map_zero,
      smul_eq_mul] at h0
    exact (hunit q hq hqp).mul_right_eq_zero.mp h0
  · intro h q hq hqp
    ext k
    simp only [toPowerSeries_frobeniusCurve_𝔾ₐ, toPowerSeries_zero, PowerSeries.coeff_smul,
      PowerSeries.coeff_cartier, Nat.add_zero, map_zero, smul_eq_mul]
    rw [h (q * k) ⟨q, hq, hqp, dvd_mul_right q k⟩, mul_zero]

/-- On the additive formal group law over a ring in which every prime `q ≠ p` is invertible, for
`p` prime, a curve is `p`-typical if and only if its underlying power series is supported in the
degrees `p ^ m`. -/
theorem isPTypical_𝔾ₐ_iff_of_prime {p : ℕ} (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (γ : (𝔾ₐ (R := R)).Curve) :
    γ.IsPTypical p ↔ ∀ k : ℕ, (∀ m : ℕ, p ^ m ≠ k) → PowerSeries.coeff k γ.toPowerSeries = 0 := by
  rw [isPTypical_𝔾ₐ_iff p hunit]
  refine forall_congr' fun k ↦ imp_congr_left ?_
  rw [← not_exists, ← forall_prime_ne_not_dvd_iff_exists_pow hp k]
  push Not
  rfl

end Curve

/-- The additive subgroup of `p`-typical curves on a commutative formal group law `F`. -/
noncomputable def pTypicalCurves (F : FormalGroup R) [F.IsComm] (p : ℕ) : AddSubgroup F.Curve where
  carrier := {γ | γ.IsPTypical p}
  zero_mem' := Curve.IsPTypical.zero p
  add_mem' := Curve.IsPTypical.add
  neg_mem' := Curve.IsPTypical.neg

@[simp]
theorem mem_pTypicalCurves (F : FormalGroup R) [F.IsComm] (p : ℕ) (γ : F.Curve) :
    γ ∈ F.pTypicalCurves p ↔ γ.IsPTypical p :=
  Iff.rfl

end FormalGroup

namespace TauCeti

section Hom

variable {R : Type*} [CommRing R] {F G : FormalGroup R} [F.IsComm] [G.IsComm]

/-- Homomorphisms of formal group laws carry `p`-typical curves to `p`-typical curves. -/
theorem FormalGroupHom.mapCurve_isPTypical (f : FormalGroupHom F G) {γ : F.Curve} {p : ℕ}
    (hγ : γ.IsPTypical p) : (f.mapCurve γ).IsPTypical p := fun q hq hqp ↦ by
  rw [← f.mapCurve_frobeniusCurve q hq.ne_zero, hγ q hq hqp, map_zero]

/-- Isomorphisms of formal group laws preserve and reflect `p`-typicality of curves. -/
@[simp]
theorem FormalGroupIso.mapCurve_toHom_isPTypical_iff (e : FormalGroupIso F G) {γ : F.Curve}
    {p : ℕ} : (e.toHom.mapCurve γ).IsPTypical p ↔ γ.IsPTypical p := by
  refine ⟨fun h ↦ ?_, e.toHom.mapCurve_isPTypical⟩
  have h' := e.invHom.mapCurve_isPTypical h
  rwa [← e.curveEquiv_apply, ← e.curveEquiv_symm_apply, e.curveEquiv.symm_apply_apply] at h'

/-- Isomorphisms of formal group laws preserve and reflect `p`-typicality of curves. -/
theorem FormalGroupIso.curveEquiv_isPTypical_iff (e : FormalGroupIso F G) {γ : F.Curve} {p : ℕ} :
    (e.curveEquiv γ).IsPTypical p ↔ γ.IsPTypical p := by
  rw [e.curveEquiv_apply, e.mapCurve_toHom_isPTypical_iff]

/-- An isomorphism of commutative formal group laws induces an additive equivalence between their
subgroups of `p`-typical curves. -/
noncomputable def FormalGroupIso.pTypicalCurvesEquiv (e : FormalGroupIso F G) (p : ℕ) :
    F.pTypicalCurves p ≃+ G.pTypicalCurves p where
  toFun γ :=
    ⟨e.curveEquiv γ.1, (FormalGroup.mem_pTypicalCurves G p _).mpr
      (e.curveEquiv_isPTypical_iff.mpr ((FormalGroup.mem_pTypicalCurves F p _).mp γ.2))⟩
  invFun γ :=
    ⟨e.curveEquiv.symm γ.1, (FormalGroup.mem_pTypicalCurves F p _).mpr <| by
      rw [← e.curveEquiv_symm]
      exact e.symm.curveEquiv_isPTypical_iff.mpr ((FormalGroup.mem_pTypicalCurves G p _).mp γ.2)⟩
  left_inv γ := Subtype.ext (e.curveEquiv.symm_apply_apply γ.1)
  right_inv γ := Subtype.ext (e.curveEquiv.apply_symm_apply γ.1)
  map_add' γ₁ γ₂ := Subtype.ext (map_add e.curveEquiv γ₁.1 γ₂.1)

@[simp]
theorem FormalGroupIso.coe_pTypicalCurvesEquiv (e : FormalGroupIso F G) (p : ℕ)
    (γ : F.pTypicalCurves p) : (e.pTypicalCurvesEquiv p γ : G.Curve) = e.curveEquiv γ.1 :=
  (rfl)

theorem FormalGroupIso.coe_pTypicalCurvesEquiv_symm (e : FormalGroupIso F G) (p : ℕ)
    (γ : G.pTypicalCurves p) :
    ((e.pTypicalCurvesEquiv p).symm γ : F.Curve) = e.curveEquiv.symm γ.1 :=
  (rfl)

@[simp]
theorem FormalGroupIso.pTypicalCurvesEquiv_symm (e : FormalGroupIso F G) (p : ℕ) :
    (e.pTypicalCurvesEquiv p).symm = e.symm.pTypicalCurvesEquiv p :=
  AddEquiv.ext fun _ ↦ Subtype.ext (by simp [coe_pTypicalCurvesEquiv_symm])

end Hom

end TauCeti

namespace FormalGroup

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Over a `ℚ`-algebra, for `p` prime, a curve `γ` on a commutative formal group law `F` is
`p`-typical if and only if `log_F(γ(T))` has nonzero coefficients only in degrees `p ^ m`. -/
theorem Curve.isPTypical_iff_coeff_subst_log_eq_zero [Algebra ℚ R] {F : FormalGroup R} [F.IsComm]
    {p : ℕ} (hp : p.Prime) {γ : F.Curve} :
    γ.IsPTypical p ↔
      ∀ k : ℕ, (∀ m : ℕ, p ^ m ≠ k) →
        PowerSeries.coeff k (PowerSeries.subst γ.toPowerSeries F.log) = 0 := by
  have hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R) := fun q hq _ ↦ by
    simpa only [map_natCast] using
      (Ne.isUnit (Nat.cast_ne_zero.mpr hq.ne_zero : (q : ℚ) ≠ 0)).map (algebraMap ℚ R)
  rw [← F.logIso.curveEquiv_isPTypical_iff, Curve.isPTypical_𝔾ₐ_iff_of_prime hp hunit]
  simp [TauCeti.FormalGroupIso.curveEquiv_apply, logIso_toHom]

/-! ### Cartier's prime-to-`p` projector on curves -/

section Projector

variable (F : FormalGroup R) [F.IsComm] (p : ℕ)

/-- Finite stage `N` of Cartier's prime-to-`p` projector, composing the elementary Cartier
projectors `π_q` over primes `q ≤ N` with `q ≠ p`. -/
private noncomputable def stagePTypicalProjectorCurve
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) : ℕ → (F.Curve →+ F.Curve)
  | 0 => AddMonoidHom.id F.Curve
  | N + 1 =>
    let prev := stagePTypicalProjectorCurve hunit N
    if h : (N + 1).Prime ∧ N + 1 ≠ p then
      (F.cartierProjectorCurve (N + 1) (Nat.succ_ne_zero N) (hunit (N + 1) h.1 h.2)).comp prev
    else
      prev

private theorem coeff_stagePTypicalProjectorCurve_succ_of_le
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (N : ℕ) {k : ℕ} (hk : k ≤ N)
    (γ : F.Curve) :
    PowerSeries.coeff k (stagePTypicalProjectorCurve F p hunit (N + 1) γ).toPowerSeries =
      PowerSeries.coeff k (stagePTypicalProjectorCurve F p hunit N γ).toPowerSeries := by
  dsimp only [stagePTypicalProjectorCurve]
  split_ifs with h
  · exact F.coeff_cartierProjectorCurve_of_lt (N + 1) (Nat.succ_ne_zero N)
      (hunit (N + 1) h.1 h.2) (Nat.lt_succ_of_le hk) _
  · rfl

private theorem coeff_stagePTypicalProjectorCurve_eq_of_le
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {N M k : ℕ} (hk : k ≤ N) (hNM : N ≤ M)
    (γ : F.Curve) :
    PowerSeries.coeff k (stagePTypicalProjectorCurve F p hunit M γ).toPowerSeries =
      PowerSeries.coeff k (stagePTypicalProjectorCurve F p hunit N γ).toPowerSeries := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNM
  clear hNM
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [Nat.add_succ, coeff_stagePTypicalProjectorCurve_succ_of_le F p hunit (N + d) (by omega), ih]

private theorem frobeniusCurve_stagePTypicalProjectorCurve_of_le
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {q N : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (hqN : q ≤ N) (γ : F.Curve) :
    F.frobeniusCurve q hq.ne_zero (stagePTypicalProjectorCurve F p hunit N γ) = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hqN
  clear hqN
  induction d with
  | zero =>
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne_zero
    rw [Nat.add_zero]
    dsimp only [stagePTypicalProjectorCurve]
    rw [dite_eq_left ⟨hq, hqp⟩, AddMonoidHom.comp_apply]
    exact F.frobeniusCurve_cartierProjectorCurve (m + 1) hq.ne_zero (hunit (m + 1) hq hqp) _
  | succ d ih =>
    rw [Nat.add_succ]
    dsimp only [stagePTypicalProjectorCurve]
    split_ifs with h
    · have hcop : q.Coprime (q + d + 1) :=
        (Nat.coprime_primes hq h.1).mpr (by omega)
      rw [AddMonoidHom.comp_apply,
        F.frobeniusCurve_cartierProjectorCurve_of_coprime hq.ne_zero (Nat.succ_ne_zero _)
          (hunit _ h.1 h.2) hcop,
        ih, map_zero]
    · exact ih

private theorem stagePTypicalProjectorCurve_cartierProjectorCurve_comm
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (N : ℕ) (γ : F.Curve) :
    stagePTypicalProjectorCurve F p hunit N
        (F.cartierProjectorCurve q hq.ne_zero (hunit q hq hqp) γ) =
      F.cartierProjectorCurve q hq.ne_zero (hunit q hq hqp)
        (stagePTypicalProjectorCurve F p hunit N γ) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    dsimp only [stagePTypicalProjectorCurve]
    split_ifs with h
    · rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ih, F.cartierProjectorCurve_comm]
    · exact ih

private theorem map_stagePTypicalProjectorCurve
    (hR : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (φ : R →+* S) (N : ℕ) (γ : F.Curve) :
    Curve.map φ (stagePTypicalProjectorCurve F p hR N γ) =
      stagePTypicalProjectorCurve (F.map φ) p
        (fun q hq hqp ↦ by simpa only [map_natCast] using (hR q hq hqp).map φ)
        N (Curve.map φ γ) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    dsimp only [stagePTypicalProjectorCurve]
    split_ifs with h
    · rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, F.map_cartierProjectorCurve, ih]
    · exact ih

private theorem mapCurve_stagePTypicalProjectorCurve {G : FormalGroup R} [G.IsComm]
    (f : TauCeti.FormalGroupHom F G) (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R))
    (N : ℕ) (γ : F.Curve) :
    f.mapCurve (stagePTypicalProjectorCurve F p hunit N γ) =
      stagePTypicalProjectorCurve G p hunit N (f.mapCurve γ) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    dsimp only [stagePTypicalProjectorCurve]
    split_ifs with h
    · rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
        f.mapCurve_cartierProjectorCurve, ih]
    · exact ih

/-- **Cartier's prime-to-`p` projector** on curves of a commutative formal group law `F`, when
every prime `q ≠ p` is invertible in `R`: the `X`-adic infinite composite of the elementary
Cartier projectors `1 - V_q [q]⁻¹ f_q` over all primes `q ≠ p`. -/
noncomputable def pTypicalProjectorCurve (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    F.Curve →+ F.Curve where
  toFun γ :=
    ⟨PowerSeries.mk fun k ↦
      PowerSeries.coeff k (stagePTypicalProjectorCurve F p hunit k γ).toPowerSeries, by
      simp [← PowerSeries.coeff_zero_eq_constantCoeff_apply, stagePTypicalProjectorCurve]⟩
  map_zero' := Curve.ext <| by
    ext k
    simp [PowerSeries.coeff_mk]
  map_add' γ₁ γ₂ := Curve.ext <| by
    ext k
    rw [PowerSeries.coeff_mk, map_add]
    exact (Curve.coeff_add_congr
      (fun i hi ↦ by
        rw [PowerSeries.coeff_mk]
        exact (coeff_stagePTypicalProjectorCurve_eq_of_le F p hunit le_rfl hi γ₁).symm)
      (fun i hi ↦ by
        rw [PowerSeries.coeff_mk]
        exact (coeff_stagePTypicalProjectorCurve_eq_of_le F p hunit le_rfl hi γ₂).symm)).symm

private theorem coeff_pTypicalProjectorCurve_eq_stage
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {k N : ℕ} (hk : k ≤ N) (γ : F.Curve) :
    PowerSeries.coeff k (F.pTypicalProjectorCurve p hunit γ).toPowerSeries =
      PowerSeries.coeff k (stagePTypicalProjectorCurve F p hunit N γ).toPowerSeries := by
  rw [pTypicalProjectorCurve, AddMonoidHom.coe_mk, ZeroHom.coe_mk, PowerSeries.coeff_mk]
  exact (coeff_stagePTypicalProjectorCurve_eq_of_le F p hunit le_rfl hk γ).symm

/-- The image of any curve under Cartier's prime-to-`p` projector is `p`-typical. -/
theorem isPTypical_pTypicalProjectorCurve (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R))
    (γ : F.Curve) : (F.pTypicalProjectorCurve p hunit γ).IsPTypical p := by
  intro q hq hqp
  ext k
  rcases eq_or_ne k 0 with rfl | hk0
  · simp
  · have hqN : q ≤ k * q := Nat.le_mul_of_pos_left q (Nat.pos_of_ne_zero hk0)
    rw [F.coeff_frobeniusCurve_congr q hq.ne_zero
      (fun i hi ↦ coeff_pTypicalProjectorCurve_eq_stage F p hunit hi γ),
      frobeniusCurve_stagePTypicalProjectorCurve_of_le F p hunit hq hqp hqN γ,
      Curve.toPowerSeries_zero, map_zero]

/-- Every `p`-typical curve is fixed by Cartier's prime-to-`p` projector. -/
theorem pTypicalProjectorCurve_eq_self (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R))
    {γ : F.Curve} (hγ : γ.IsPTypical p) :
    F.pTypicalProjectorCurve p hunit γ = γ := by
  have hstage (N : ℕ) : stagePTypicalProjectorCurve F p hunit N γ = γ := by
    induction N with
    | zero => rfl
    | succ N ih =>
      dsimp only [stagePTypicalProjectorCurve]
      split_ifs with h
      · rw [AddMonoidHom.comp_apply, ih]
        exact F.cartierProjectorCurve_eq_self (N + 1) (Nat.succ_ne_zero N)
          (hunit (N + 1) h.1 h.2) (hγ (N + 1) h.1 h.2)
      · exact ih
  ext k
  rw [coeff_pTypicalProjectorCurve_eq_stage F p hunit le_rfl γ, hstage k]

/-- The fixed curves of Cartier's prime-to-`p` projector are precisely the `p`-typical curves. -/
@[simp]
theorem pTypicalProjectorCurve_eq_self_iff (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R))
    (γ : F.Curve) :
    F.pTypicalProjectorCurve p hunit γ = γ ↔ γ.IsPTypical p :=
  ⟨fun h ↦ h ▸ F.isPTypical_pTypicalProjectorCurve p hunit γ,
    F.pTypicalProjectorCurve_eq_self p hunit⟩

/-- Cartier's prime-to-`p` projector is idempotent on curves. -/
@[simp]
theorem pTypicalProjectorCurve_pTypicalProjectorCurve
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    F.pTypicalProjectorCurve p hunit (F.pTypicalProjectorCurve p hunit γ) =
      F.pTypicalProjectorCurve p hunit γ :=
  F.pTypicalProjectorCurve_eq_self p hunit (F.isPTypical_pTypicalProjectorCurve p hunit γ)

/-- Cartier's prime-to-`p` projector is an idempotent in the endomorphism ring of curves. -/
@[simp]
theorem isIdempotentElem_pTypicalProjectorCurve
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    IsIdempotentElem (M := AddMonoid.End F.Curve) (F.pTypicalProjectorCurve p hunit) :=
  AddMonoidHom.ext (F.pTypicalProjectorCurve_pTypicalProjectorCurve p hunit)

/-- The image of Cartier's prime-to-`p` projector is precisely the subgroup of `p`-typical
curves. -/
@[simp]
theorem range_pTypicalProjectorCurve (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalProjectorCurve p hunit).range = F.pTypicalCurves p := by
  ext γ
  simp only [AddMonoidHom.mem_range, mem_pTypicalCurves]
  exact ⟨fun ⟨δ, hδ⟩ ↦ hδ ▸ F.isPTypical_pTypicalProjectorCurve p hunit δ,
    fun hγ ↦ ⟨γ, F.pTypicalProjectorCurve_eq_self p hunit hγ⟩⟩

/-- When every prime `q ≠ p` is invertible in `R`, every curve on `F` decomposes uniquely as the
sum of a `p`-typical curve and a curve in the kernel of Cartier's prime-to-`p` projector. -/
noncomputable def pTypicalCurveEquiv (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    F.Curve ≃+ F.pTypicalCurves p × (F.pTypicalProjectorCurve p hunit).ker where
  toFun γ :=
    (⟨F.pTypicalProjectorCurve p hunit γ,
        (F.mem_pTypicalCurves p _).mpr (F.isPTypical_pTypicalProjectorCurve p hunit γ)⟩,
      ⟨γ - F.pTypicalProjectorCurve p hunit γ, by
        rw [AddMonoidHom.mem_ker, map_sub, pTypicalProjectorCurve_pTypicalProjectorCurve,
          sub_self]⟩)
  invFun δ := δ.1.val + δ.2.val
  left_inv γ := add_sub_cancel _ _
  right_inv := by
    rintro ⟨⟨δ₁, h₁⟩, ⟨δ₂, h₂⟩⟩
    rw [AddMonoidHom.mem_ker] at h₂
    have hproj : F.pTypicalProjectorCurve p hunit (δ₁ + δ₂) = δ₁ := by
      rw [map_add, F.pTypicalProjectorCurve_eq_self p hunit ((F.mem_pTypicalCurves p _).mp h₁),
        h₂, _root_.add_zero]
    apply Prod.ext
    · exact Subtype.ext hproj
    · exact Subtype.ext (by dsimp only; rw [hproj, add_sub_cancel_left])
  map_add' γ₁ γ₂ := by
    apply Prod.ext
    · exact Subtype.ext (map_add _ γ₁ γ₂)
    · refine Subtype.ext ?_
      change _ - _ = (_ - _) + (_ - _)
      rw [map_add]
      abel

@[simp]
theorem coe_pTypicalCurveEquiv_fst (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R))
    (γ : F.Curve) :
    ((F.pTypicalCurveEquiv p hunit γ).1 : F.Curve) = F.pTypicalProjectorCurve p hunit γ :=
  (rfl)

@[simp]
theorem coe_pTypicalCurveEquiv_snd (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R))
    (γ : F.Curve) :
    ((F.pTypicalCurveEquiv p hunit γ).2 : F.Curve) = γ - F.pTypicalProjectorCurve p hunit γ :=
  (rfl)

theorem pTypicalCurveEquiv_symm_apply (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R))
    (δ : F.pTypicalCurves p × (F.pTypicalProjectorCurve p hunit).ker) :
    (F.pTypicalCurveEquiv p hunit).symm δ = δ.1.val + δ.2.val :=
  (rfl)

/-- Cartier's prime-to-`p` projector absorbs any elementary Cartier projector at a prime `q ≠ p`
on the right. -/
@[simp]
theorem pTypicalProjectorCurve_cartierProjectorCurve_of_prime
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (hqR : IsUnit (q : R)) (γ : F.Curve) :
    F.pTypicalProjectorCurve p hunit (F.cartierProjectorCurve q hq.ne_zero hqR γ) =
      F.pTypicalProjectorCurve p hunit γ := by
  ext k
  let N := max k q
  rw [coeff_pTypicalProjectorCurve_eq_stage F p hunit (le_max_left k q),
    coeff_pTypicalProjectorCurve_eq_stage F p hunit (le_max_left k q),
    stagePTypicalProjectorCurve_cartierProjectorCurve_comm F p hunit hq hqp N γ,
    F.cartierProjectorCurve_eq_self q hq.ne_zero (hunit q hq hqp)
      (frobeniusCurve_stagePTypicalProjectorCurve_of_le F p hunit hq hqp (le_max_right k q) γ)]

/-- Any elementary Cartier projector at a prime `q ≠ p` fixes the image of Cartier's prime-to-`p`
projector. -/
@[simp]
theorem cartierProjectorCurve_pTypicalProjectorCurve_of_prime
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (hqR : IsUnit (q : R)) (γ : F.Curve) :
    F.cartierProjectorCurve q hq.ne_zero hqR (F.pTypicalProjectorCurve p hunit γ) =
      F.pTypicalProjectorCurve p hunit γ :=
  F.cartierProjectorCurve_eq_self q hq.ne_zero hqR
    (F.isPTypical_pTypicalProjectorCurve p hunit γ q hq hqp)

/-- Cartier's Frobenius at any prime `q ≠ p` annihilates the image of Cartier's prime-to-`p`
projector. -/
@[simp]
theorem frobeniusCurve_pTypicalProjectorCurve_of_prime
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (γ : F.Curve) :
    F.frobeniusCurve q hq.ne_zero (F.pTypicalProjectorCurve p hunit γ) = 0 :=
  F.isPTypical_pTypicalProjectorCurve p hunit γ q hq hqp

/-- Cartier's prime-to-`p` projector kills every Verschiebung at a prime `q ≠ p`. -/
@[simp]
theorem pTypicalProjectorCurve_verschiebungCurve_of_prime
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (γ : F.Curve) :
    F.pTypicalProjectorCurve p hunit (F.verschiebungCurve q hq.ne_zero γ) = 0 := by
  rw [← F.pTypicalProjectorCurve_cartierProjectorCurve_of_prime p hunit hq hqp (hunit q hq hqp),
    F.cartierProjectorCurve_verschiebungCurve, map_zero]

/-- Cartier's prime-to-`p` projector commutes with Verschiebung `V_n` whenever `n` is coprime to
every prime `q ≠ p`. -/
theorem pTypicalProjectorCurve_verschiebungCurve_of_coprime
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {n : ℕ} (hn : n ≠ 0)
    (hcop : ∀ q : ℕ, q.Prime → q ≠ p → q.Coprime n) (γ : F.Curve) :
    F.pTypicalProjectorCurve p hunit (F.verschiebungCurve n hn γ) =
      F.verschiebungCurve n hn (F.pTypicalProjectorCurve p hunit γ) := by
  have hstage (N : ℕ) :
      stagePTypicalProjectorCurve F p hunit N (F.verschiebungCurve n hn γ) =
        F.verschiebungCurve n hn (stagePTypicalProjectorCurve F p hunit N γ) := by
    induction N with
    | zero => rfl
    | succ N ih =>
      dsimp only [stagePTypicalProjectorCurve]
      split_ifs with h
      · rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ih,
          F.cartierProjectorCurve_verschiebungCurve_of_coprime (Nat.succ_ne_zero N) hn
            (hunit (N + 1) h.1 h.2) (hcop (N + 1) h.1 h.2)]
      · exact ih
  ext k
  rw [coeff_pTypicalProjectorCurve_eq_stage F p hunit le_rfl, hstage k]
  exact F.coeff_verschiebungCurve_congr n hn fun i hi ↦
    (coeff_pTypicalProjectorCurve_eq_stage F p hunit (hi.trans (Nat.div_le_self k n)) γ).symm

/-- For a prime `p`, Cartier's prime-to-`p` projector commutes with `V_{p ^ k}`. -/
theorem pTypicalProjectorCurve_verschiebungCurve_pow {p : ℕ} (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (k : ℕ) (γ : F.Curve) :
    F.pTypicalProjectorCurve p hunit (F.verschiebungCurve (p ^ k) (pow_ne_zero k hp.ne_zero) γ) =
      F.verschiebungCurve (p ^ k) (pow_ne_zero k hp.ne_zero)
        (F.pTypicalProjectorCurve p hunit γ) :=
  F.pTypicalProjectorCurve_verschiebungCurve_of_coprime p hunit (pow_ne_zero k hp.ne_zero)
    (fun q hq hqp ↦ by simpa only [pow_one] using Nat.coprime_pow_primes 1 k hq hp hqp) γ

/-- Cartier's prime-to-`p` projector commutes with Frobenius `f_n` whenever `n` is coprime to every
prime `q ≠ p`. -/
theorem frobeniusCurve_pTypicalProjectorCurve_of_coprime
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {n : ℕ} (hn : n ≠ 0)
    (hcop : ∀ q : ℕ, q.Prime → q ≠ p → q.Coprime n) (γ : F.Curve) :
    F.frobeniusCurve n hn (F.pTypicalProjectorCurve p hunit γ) =
      F.pTypicalProjectorCurve p hunit (F.frobeniusCurve n hn γ) := by
  have hstage (N : ℕ) :
      F.frobeniusCurve n hn (stagePTypicalProjectorCurve F p hunit N γ) =
        stagePTypicalProjectorCurve F p hunit N (F.frobeniusCurve n hn γ) := by
    induction N with
    | zero => rfl
    | succ N ih =>
      dsimp only [stagePTypicalProjectorCurve]
      split_ifs with h
      · rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
          F.frobeniusCurve_cartierProjectorCurve_of_coprime hn (Nat.succ_ne_zero N)
            (hunit (N + 1) h.1 h.2) (hcop (N + 1) h.1 h.2).symm,
          ih]
      · exact ih
  ext k
  rw [F.coeff_frobeniusCurve_congr n hn
      (fun i hi ↦ coeff_pTypicalProjectorCurve_eq_stage F p hunit hi γ),
    hstage (k * n),
    ← coeff_pTypicalProjectorCurve_eq_stage F p hunit
      (Nat.le_mul_of_pos_right k (Nat.pos_of_ne_zero hn))]

/-- For a prime `p`, Cartier's prime-to-`p` projector commutes with `f_{p ^ k}`. -/
theorem frobeniusCurve_pTypicalProjectorCurve_pow {p : ℕ} (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (k : ℕ) (γ : F.Curve) :
    F.frobeniusCurve (p ^ k) (pow_ne_zero k hp.ne_zero) (F.pTypicalProjectorCurve p hunit γ) =
      F.pTypicalProjectorCurve p hunit
        (F.frobeniusCurve (p ^ k) (pow_ne_zero k hp.ne_zero) γ) :=
  F.frobeniusCurve_pTypicalProjectorCurve_of_coprime p hunit (pow_ne_zero k hp.ne_zero)
    (fun q hq hqp ↦ by simpa only [pow_one] using Nat.coprime_pow_primes 1 k hq hp hqp) γ

/-- Cartier's prime-to-`p` projector leaves coefficients unchanged in any degree `k` strictly below
every prime `q ≠ p`. -/
theorem coeff_pTypicalProjectorCurve_of_forall_lt
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {k : ℕ}
    (hk : ∀ q : ℕ, q.Prime → q ≠ p → k < q) (γ : F.Curve) :
    PowerSeries.coeff k (F.pTypicalProjectorCurve p hunit γ).toPowerSeries =
      PowerSeries.coeff k γ.toPowerSeries := by
  have hstage (N : ℕ) :
      PowerSeries.coeff k (stagePTypicalProjectorCurve F p hunit N γ).toPowerSeries =
        PowerSeries.coeff k γ.toPowerSeries := by
    induction N with
    | zero => rfl
    | succ N ih =>
      dsimp only [stagePTypicalProjectorCurve]
      split_ifs with h
      · rw [AddMonoidHom.comp_apply,
          F.coeff_cartierProjectorCurve_of_lt (N + 1) (Nat.succ_ne_zero N)
            (hunit (N + 1) h.1 h.2) (hk (N + 1) h.1 h.2),
          ih]
      · exact ih
  rw [coeff_pTypicalProjectorCurve_eq_stage F p hunit le_rfl, hstage k]

/-- Cartier's prime-to-`p` projector preserves linear coefficients. -/
@[simp]
theorem coeff_one_pTypicalProjectorCurve (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R))
    (γ : F.Curve) :
    PowerSeries.coeff 1 (F.pTypicalProjectorCurve p hunit γ).toPowerSeries =
      PowerSeries.coeff 1 γ.toPowerSeries :=
  F.coeff_pTypicalProjectorCurve_of_forall_lt p hunit (fun _ hq _ ↦ hq.one_lt) γ

/-- Base change commutes with Cartier's prime-to-`p` projector. -/
theorem map_pTypicalProjectorCurve
    (hR : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (φ : R →+* S) (γ : F.Curve) :
    Curve.map φ (F.pTypicalProjectorCurve p hR γ) =
      (F.map φ).pTypicalProjectorCurve p
        (fun q hq hqp ↦ by simpa only [map_natCast] using (hR q hq hqp).map φ)
        (Curve.map φ γ) := by
  ext k
  rw [Curve.toPowerSeries_map, PowerSeries.coeff_map,
    coeff_pTypicalProjectorCurve_eq_stage F p hR le_rfl,
    coeff_pTypicalProjectorCurve_eq_stage (F.map φ) p _ le_rfl,
    ← map_stagePTypicalProjectorCurve F p hR φ k γ, Curve.toPowerSeries_map, PowerSeries.coeff_map]

/-- Formal-group homomorphisms commute with Cartier's prime-to-`p` projector. -/
theorem _root_.TauCeti.FormalGroupHom.mapCurve_pTypicalProjectorCurve
    {F G : FormalGroup R} [F.IsComm] [G.IsComm] (f : TauCeti.FormalGroupHom F G) (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    f.mapCurve (F.pTypicalProjectorCurve p hunit γ) =
      G.pTypicalProjectorCurve p hunit (f.mapCurve γ) := by
  ext k
  rw [f.coeff_mapCurve_congr
      (fun i hi ↦ coeff_pTypicalProjectorCurve_eq_stage F p hunit hi γ),
    mapCurve_stagePTypicalProjectorCurve F p f hunit k γ,
    coeff_pTypicalProjectorCurve_eq_stage G p hunit le_rfl]

/-- On the additive formal group law, Cartier's prime-to-`p` projector leaves unchanged any
coefficient whose degree has no prime divisor distinct from `p`. -/
theorem coeff_toPowerSeries_pTypicalProjectorCurve_𝔾ₐ_of_forall_not_dvd
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {k : ℕ}
    (hk : ∀ q : ℕ, q.Prime → q ≠ p → ¬ q ∣ k) (γ : (𝔾ₐ (R := R)).Curve) :
    PowerSeries.coeff k ((𝔾ₐ (R := R)).pTypicalProjectorCurve p hunit γ).toPowerSeries =
      PowerSeries.coeff k γ.toPowerSeries := by
  have hstage (N : ℕ) :
      PowerSeries.coeff k
        (stagePTypicalProjectorCurve (𝔾ₐ (R := R)) p hunit N γ).toPowerSeries =
        PowerSeries.coeff k γ.toPowerSeries := by
    induction N with
    | zero => rfl
    | succ N ih =>
      dsimp only [stagePTypicalProjectorCurve]
      split_ifs with h
      · rw [AddMonoidHom.comp_apply, toPowerSeries_cartierProjectorCurve_𝔾ₐ, map_sub,
          PowerSeries.coeff_expand, ite_eq_right (hk (N + 1) h.1 h.2), sub_zero, ih]
      · exact ih
  rw [coeff_pTypicalProjectorCurve_eq_stage (𝔾ₐ (R := R)) p hunit le_rfl, hstage k]

/-- On the additive formal group law, Cartier's prime-to-`p` projector zeroes every coefficient
whose degree is divisible by a prime `q ≠ p`. -/
theorem coeff_toPowerSeries_pTypicalProjectorCurve_𝔾ₐ_eq_zero_of_prime_dvd
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {k q : ℕ}
    (hq : q.Prime) (hqp : q ≠ p) (hqk : q ∣ k) (γ : (𝔾ₐ (R := R)).Curve) :
    PowerSeries.coeff k ((𝔾ₐ (R := R)).pTypicalProjectorCurve p hunit γ).toPowerSeries = 0 :=
  (Curve.isPTypical_𝔾ₐ_iff p hunit _).mp
    ((𝔾ₐ (R := R)).isPTypical_pTypicalProjectorCurve p hunit γ) k ⟨q, hq, hqp, hqk⟩

/-- On the additive formal group law, for `p` prime, Cartier's prime-to-`p` projector retains
precisely the coefficients in degrees `p ^ m` and zeroes all others. -/
theorem coeff_toPowerSeries_pTypicalProjectorCurve_𝔾ₐ_of_prime {p : ℕ} (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (k : ℕ) (γ : (𝔾ₐ (R := R)).Curve) :
    PowerSeries.coeff k ((𝔾ₐ (R := R)).pTypicalProjectorCurve p hunit γ).toPowerSeries =
      if p ^ Nat.log p k = k then PowerSeries.coeff k γ.toPowerSeries else 0 := by
  split_ifs with hk
  · exact coeff_toPowerSeries_pTypicalProjectorCurve_𝔾ₐ_of_forall_not_dvd p hunit
      ((forall_prime_ne_not_dvd_iff_exists_pow hp k).mpr
        ((pow_log_eq_self_iff_exists_pow hp k).mp hk)) γ
  · have hnot : ¬ ∀ q : ℕ, q.Prime → q ≠ p → ¬ q ∣ k :=
      mt (forall_prime_ne_not_dvd_iff_exists_pow hp k).mp
        (mt (pow_log_eq_self_iff_exists_pow hp k).mpr hk)
    push Not at hnot
    obtain ⟨q, hq, hqp, hqk⟩ := hnot
    exact coeff_toPowerSeries_pTypicalProjectorCurve_𝔾ₐ_eq_zero_of_prime_dvd
      p hunit hq hqp hqk γ

/-- Over a `ℚ`-algebra, Cartier's prime-to-`p` projector leaves unchanged any formal-logarithm
coefficient whose degree has no prime divisor distinct from `p`. -/
theorem coeff_subst_pTypicalProjectorCurve_log_of_forall_not_dvd [Algebra ℚ R]
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {k : ℕ}
    (hk : ∀ q : ℕ, q.Prime → q ≠ p → ¬ q ∣ k) (γ : F.Curve) :
    PowerSeries.coeff k
        (PowerSeries.subst (F.pTypicalProjectorCurve p hunit γ).toPowerSeries F.log) =
      PowerSeries.coeff k (PowerSeries.subst γ.toPowerSeries F.log) := by
  have h := congrArg (PowerSeries.coeff k ∘ Curve.toPowerSeries)
    (F.logHom.mapCurve_pTypicalProjectorCurve p hunit γ)
  simpa only [Function.comp_apply, TauCeti.FormalGroupHom.toPowerSeries_mapCurve,
    logHom_toPowerSeries,
    coeff_toPowerSeries_pTypicalProjectorCurve_𝔾ₐ_of_forall_not_dvd p hunit hk] using h

/-- Over a `ℚ`-algebra, Cartier's prime-to-`p` projector zeroes every formal-logarithm coefficient
whose degree is divisible by a prime `q ≠ p`. -/
theorem coeff_subst_pTypicalProjectorCurve_log_eq_zero_of_prime_dvd [Algebra ℚ R]
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {k q : ℕ}
    (hq : q.Prime) (hqp : q ≠ p) (hqk : q ∣ k) (γ : F.Curve) :
    PowerSeries.coeff k
        (PowerSeries.subst (F.pTypicalProjectorCurve p hunit γ).toPowerSeries F.log) = 0 := by
  have h := congrArg (PowerSeries.coeff k ∘ Curve.toPowerSeries)
    (F.logHom.mapCurve_pTypicalProjectorCurve p hunit γ)
  simpa only [Function.comp_apply, TauCeti.FormalGroupHom.toPowerSeries_mapCurve,
    logHom_toPowerSeries,
    coeff_toPowerSeries_pTypicalProjectorCurve_𝔾ₐ_eq_zero_of_prime_dvd p hunit hq hqp hqk] using h

/-- Over a `ℚ`-algebra, for `p` prime, Cartier's prime-to-`p` projector acts on the formal
logarithm of a curve by retaining the coefficients in degrees `p ^ m` and zeroing all others. -/
theorem coeff_subst_pTypicalProjectorCurve_log_of_prime [Algebra ℚ R] {p : ℕ} (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (k : ℕ) (γ : F.Curve) :
    PowerSeries.coeff k
        (PowerSeries.subst (F.pTypicalProjectorCurve p hunit γ).toPowerSeries F.log) =
      if p ^ Nat.log p k = k then
        PowerSeries.coeff k (PowerSeries.subst γ.toPowerSeries F.log) else 0 := by
  have h := congrArg (PowerSeries.coeff k ∘ Curve.toPowerSeries)
    (F.logHom.mapCurve_pTypicalProjectorCurve p hunit γ)
  simpa only [Function.comp_apply, TauCeti.FormalGroupHom.toPowerSeries_mapCurve,
    logHom_toPowerSeries,
    coeff_toPowerSeries_pTypicalProjectorCurve_𝔾ₐ_of_prime hp hunit k] using h

@[simp]
theorem coeff_pow_subst_pTypicalProjectorCurve_log [Algebra ℚ R] {p : ℕ} (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (m : ℕ) (γ : F.Curve) :
    PowerSeries.coeff (p ^ m)
        (PowerSeries.subst (F.pTypicalProjectorCurve p hunit γ).toPowerSeries F.log) =
      PowerSeries.coeff (p ^ m) (PowerSeries.subst γ.toPowerSeries F.log) := by
  rw [F.coeff_subst_pTypicalProjectorCurve_log_of_prime hp hunit (p ^ m) γ,
    Nat.log_pow hp.one_lt, ite_eq_left rfl]

@[simp]
theorem coeff_subst_pTypicalProjectorCurve_log_eq_zero [Algebra ℚ R] {p : ℕ} (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {k : ℕ} (hk : ∀ m : ℕ, p ^ m ≠ k)
    (γ : F.Curve) :
    PowerSeries.coeff k
        (PowerSeries.subst (F.pTypicalProjectorCurve p hunit γ).toPowerSeries F.log) = 0 := by
  rw [F.coeff_subst_pTypicalProjectorCurve_log_of_prime hp hunit k γ,
    ite_eq_right (hk (Nat.log p k))]

end Projector

end FormalGroup
