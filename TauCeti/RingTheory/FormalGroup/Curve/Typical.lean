/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Curve.Projector
import TauCeti.Data.Nat.Factorization.Basic

/-!
# Typical curves and Cartier's infinite typical projector

A curve `γ ∈ F.Curve` on a commutative formal group law `F` over `R` is **`p`-typical**
(`FormalGroup.Curve.IsTypical`) if `f_q γ = 0` for every prime `q ∤ p` (equivalently `f_n γ = 0`
whenever `n` has a prime factor not dividing `p`, in particular for coprime `n > 1`). The
`p`-typical curves form an additive subgroup `FormalGroup.typicalCurveSubgroup F p` stable under
`f_n`, `[r]`, and `V_n` when all prime factors of `n` divide `p`. Over a `ℚ`-algebra, `γ` is
`p`-typical iff `log_F(γ(T))` is supported in degrees whose prime factors divide `p` (`p^r` for
prime `p`).

When every prime `q ∤ p` is a unit in `R`, composing `1 - V_q [q]_F⁻¹ f_q` over primes `q ∤ p`
stabilizes coefficientwise, defining Cartier's idempotent **typical projector**
`FormalGroup.typicalProjectorCurve F p hunit` with image `F.typicalCurveSubgroup p`. It preserves
`coeff 1`, commutes with base change, formal-group homomorphisms, homotheties `[r]`, `V_p`, and
`f_p`, annihilates `V_n` on the right and is annihilated by `f_n` on the left whenever `n` has a
prime factor not dividing `p` (in particular at coprime indices `n > 1`), and projects `log_F(γ)`
onto degrees whose prime factors divide `p` over `ℚ`-algebras.

## Main definitions and results

* `FormalGroup.Curve.IsTypical`, `FormalGroup.typicalCurveSubgroup`,
  `FormalGroup.Curve.isTypical_iff_of_prime`, `FormalGroup.Curve.isTypical_iff_forall_coprime`,
  `FormalGroup.Curve.isTypical_iff_coeff_subst_log_eq_zero`,
  `FormalGroup.Curve.isTypical_iff_coeff_subst_log_eq_zero_of_prime`: `p`-typical curves and
  Frobenius / rational-logarithm characterizations.
* `FormalGroup.typicalProjectorCurve`, `FormalGroup.map_typicalProjectorCurve`,
  `TauCeti.FormalGroupHom.mapCurve_typicalProjectorCurve`,
  `FormalGroup.typicalProjectorCurve_homothetyCurve`: Cartier's typical projector and naturality.
* `FormalGroup.coeff_subst_typicalProjectorCurve_log`,
  `FormalGroup.isTypical_typicalProjectorCurve`, `FormalGroup.typicalProjectorCurve_eq_self_iff`,
  `FormalGroup.typicalProjectorCurve_typicalProjectorCurve`,
  `FormalGroup.range_typicalProjectorCurve`: logarithm action, idempotence, and image over any
  commutative ring where every prime `q ∤ p` is invertible.
* `FormalGroup.frobeniusCurve_typicalProjectorCurve_eq_zero`,
  `FormalGroup.typicalProjectorCurve_verschiebungCurve_eq_zero`,
  `FormalGroup.typicalProjectorCurve_verschiebungCurve_self`,
  `FormalGroup.frobeniusCurve_typicalProjectorCurve_self`: interaction with `V_n` and `f_n`.

## References

* P. Cartier, *Modules associés à un groupe formel commutatif. Courbes typiques*, C. R. Acad. Sci.
  Paris Sér. A-B 265 (1967), A129–A132.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapter III, §16.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres* (1986), A2.1.19–A2.1.25.
-/

public section

namespace FormalGroup

open TauCeti (FormalGroupHom FormalGroupIso)

variable {R S : Type*} [CommRing R] [CommRing S]

/-! ### Typical curves -/

namespace Curve

section IsTypical

variable {F : FormalGroup R} [F.IsComm]

/-- A curve `γ` on `F` is **`p`-typical** if `f_q γ = 0` for every prime `q ∤ p`. -/
def IsTypical (γ : F.Curve) (p : ℕ) : Prop :=
  ∀ (q : ℕ) (hq : q.Prime), ¬ q ∣ p → F.frobeniusCurve q hq.ne_zero γ = 0

/-- Unfold `FormalGroup.Curve.IsTypical`. -/
theorem isTypical_def (γ : F.Curve) (p : ℕ) :
    γ.IsTypical p ↔ ∀ (q : ℕ) (hq : q.Prime), ¬ q ∣ p → F.frobeniusCurve q hq.ne_zero γ = 0 :=
  Iff.rfl

/-- For a prime `p`, a curve is `p`-typical precisely when `f_q γ = 0` for every prime `q ≠ p`. -/
theorem isTypical_iff_of_prime {γ : F.Curve} {p : ℕ} (hp : p.Prime) :
    γ.IsTypical p ↔ ∀ (q : ℕ) (hq : q.Prime), q ≠ p → F.frobeniusCurve q hq.ne_zero γ = 0 :=
  forall_congr' fun q ↦ forall_congr' fun hq ↦ by rw [Nat.prime_dvd_prime_iff_eq hq hp]

/-- A `p`-typical curve is annihilated by `f_n` whenever `n` has a prime factor not dividing `p`. -/
theorem IsTypical.frobeniusCurve_eq_zero {γ : F.Curve} {p : ℕ} (hγ : γ.IsTypical p)
    {n : ℕ} (hn : n ≠ 0) (hq : ∃ q ∈ n.primeFactors, ¬ q ∣ p) : F.frobeniusCurve n hn γ = 0 := by
  obtain ⟨q, hqn, hqp⟩ := hq
  obtain ⟨hq_prime, ⟨m, rfl⟩, hqm0⟩ := Nat.mem_primeFactors.mp hqn
  have hm : m ≠ 0 := right_ne_zero_of_mul hqm0
  rw [F.frobeniusCurve_congr (Nat.mul_comm q m) hn (mul_ne_zero hm hq_prime.ne_zero),
    ← F.frobeniusCurve_frobeniusCurve hm hq_prime.ne_zero, hγ q hq_prime hqp, map_zero]

/-- A `p`-typical curve is annihilated by `f_n` for every `n > 1` coprime to `p`. -/
theorem IsTypical.frobeniusCurve_eq_zero_of_coprime {γ : F.Curve} {p : ℕ} (hγ : γ.IsTypical p)
    {n : ℕ} (hn : 1 < n) (hcop : n.Coprime p) : F.frobeniusCurve n (by omega) γ = 0 :=
  hγ.frobeniusCurve_eq_zero (by omega) (hcop.exists_mem_primeFactors_not_dvd hn)

/-- A curve is `p`-typical iff `f_n γ = 0` for every integer `n > 1` coprime to `p`. -/
theorem isTypical_iff_forall_coprime {γ : F.Curve} {p : ℕ} :
    γ.IsTypical p ↔ ∀ (n : ℕ) (hn : 1 < n), n.Coprime p → F.frobeniusCurve n (by omega) γ = 0 :=
  ⟨fun hγ _ hn hcop ↦ hγ.frobeniusCurve_eq_zero_of_coprime hn hcop,
    fun h q hq hqp ↦ h q hq.one_lt (hq.coprime_iff_not_dvd.mpr hqp)⟩

/-- The zero curve is `p`-typical. -/
@[simp]
theorem IsTypical.zero (p : ℕ) : (0 : F.Curve).IsTypical p :=
  fun q hq _ ↦ map_zero (F.frobeniusCurve q hq.ne_zero)

/-- Every curve is `0`-typical, since every prime divides `0`. -/
@[simp]
theorem isTypical_zero_right (γ : F.Curve) : γ.IsTypical 0 := fun _ _ hq ↦ absurd (dvd_zero _) hq

/-- Sums of `p`-typical curves are `p`-typical. -/
theorem IsTypical.add {γ δ : F.Curve} {p : ℕ} (hγ : γ.IsTypical p) (hδ : δ.IsTypical p) :
    (γ + δ).IsTypical p := fun q hq hqp ↦ by rw [map_add, hγ q hq hqp, hδ q hq hqp, _root_.add_zero]

/-- Negatives of `p`-typical curves are `p`-typical. -/
theorem IsTypical.neg {γ : F.Curve} {p : ℕ} (hγ : γ.IsTypical p) : (-γ).IsTypical p :=
  fun q hq hqp ↦ by rw [map_neg, hγ q hq hqp, neg_zero]

/-- Negating a curve preserves and reflects `p`-typicality. -/
@[simp]
theorem isTypical_neg_iff {γ : F.Curve} {p : ℕ} : (-γ).IsTypical p ↔ γ.IsTypical p :=
  ⟨fun h ↦ neg_neg γ ▸ h.neg, IsTypical.neg⟩

/-- Differences of `p`-typical curves are `p`-typical. -/
theorem IsTypical.sub {γ δ : F.Curve} {p : ℕ} (hγ : γ.IsTypical p) (hδ : δ.IsTypical p) :
    (γ - δ).IsTypical p := fun q hq hqp ↦ by rw [map_sub, hγ q hq hqp, hδ q hq hqp, sub_zero]

/-- Natural-number multiples of `p`-typical curves are `p`-typical. -/
theorem IsTypical.nsmul {γ : F.Curve} {p : ℕ} (hγ : γ.IsTypical p) (n : ℕ) : (n • γ).IsTypical p :=
  fun q hq hqp ↦ by rw [map_nsmul, hγ q hq hqp, smul_zero]

/-- Integer multiples of `p`-typical curves are `p`-typical. -/
theorem IsTypical.zsmul {γ : F.Curve} {p : ℕ} (hγ : γ.IsTypical p) (n : ℤ) : (n • γ).IsTypical p :=
  fun q hq hqp ↦ by rw [map_zsmul, hγ q hq hqp, smul_zero]

/-- Frobenius operators of arbitrary nonzero index preserve `p`-typicality. -/
theorem IsTypical.frobeniusCurve {γ : F.Curve} {p : ℕ} (hγ : γ.IsTypical p) {n : ℕ} (hn : n ≠ 0) :
    (F.frobeniusCurve n hn γ).IsTypical p := fun q hq hqp ↦ by
  rw [F.frobeniusCurve_frobeniusCurve, F.frobeniusCurve_congr (Nat.mul_comm q n)
      (mul_ne_zero hq.ne_zero hn) (mul_ne_zero hn hq.ne_zero),
    ← F.frobeniusCurve_frobeniusCurve hn hq.ne_zero, hγ q hq hqp, map_zero]

/-- `V_n` preserves and reflects `p`-typicality when every prime factor of `n` divides `p`. -/
theorem isTypical_verschiebungCurve_iff_of_forall_prime_dvd {γ : F.Curve} {p n : ℕ} (hn : n ≠ 0)
    (hdvd : ∀ q : ℕ, q.Prime → q ∣ n → q ∣ p) :
    (F.verschiebungCurve n hn γ).IsTypical p ↔ γ.IsTypical p := by
  refine forall_congr' fun q ↦ forall_congr' fun hq ↦ imp_congr_right fun hqp ↦ ?_
  have hcop : q.Coprime n := hq.coprime_iff_not_dvd.mpr fun hqn ↦ hqp (hdvd q hq hqn)
  rw [F.frobeniusCurve_verschiebungCurve_of_coprime hq.ne_zero hn hcop]
  exact ⟨fun h ↦ F.verschiebungCurve_injective n hn (h.trans (map_zero _).symm),
    fun h ↦ by rw [h, map_zero]⟩

/-- `V_n` preserves `p`-typicality whenever every prime factor of `n` divides `p`. -/
theorem IsTypical.verschiebungCurve_of_forall_prime_dvd {γ : F.Curve} {p n : ℕ}
    (hγ : γ.IsTypical p) (hn : n ≠ 0) (hdvd : ∀ q : ℕ, q.Prime → q ∣ n → q ∣ p) :
    (F.verschiebungCurve n hn γ).IsTypical p :=
  (isTypical_verschiebungCurve_iff_of_forall_prime_dvd hn hdvd).mpr hγ

/-- Verschiebung `V_p` preserves and reflects `p`-typicality for `p ≠ 0`. -/
@[simp]
theorem isTypical_verschiebungCurve_self_iff {γ : F.Curve} {p : ℕ} (hp : p ≠ 0) :
    (F.verschiebungCurve p hp γ).IsTypical p ↔ γ.IsTypical p :=
  isTypical_verschiebungCurve_iff_of_forall_prime_dvd hp fun _ _ h ↦ h

/-- Verschiebung `V_p` preserves `p`-typicality for `p ≠ 0`. -/
theorem IsTypical.verschiebungCurve_self {γ : F.Curve} {p : ℕ} (hγ : γ.IsTypical p) (hp : p ≠ 0) :
    (F.verschiebungCurve p hp γ).IsTypical p := (isTypical_verschiebungCurve_self_iff hp).mpr hγ

/-- Iterated Verschiebung `V_{p^r}` preserves and reflects `p`-typicality for `p ≠ 0`. -/
@[simp]
theorem isTypical_verschiebungCurve_pow_iff {γ : F.Curve} {p : ℕ} (hp : p ≠ 0) (r : ℕ) :
    (F.verschiebungCurve (p ^ r) (pow_ne_zero r hp) γ).IsTypical p ↔ γ.IsTypical p :=
  isTypical_verschiebungCurve_iff_of_forall_prime_dvd (pow_ne_zero r hp)
    fun _ hq hqr ↦ hq.dvd_of_dvd_pow hqr

/-- Iterated Verschiebung `V_{p^r}` preserves `p`-typicality for `p ≠ 0`. -/
theorem IsTypical.verschiebungCurve_pow {γ : F.Curve} {p : ℕ} (hγ : γ.IsTypical p) (hp : p ≠ 0)
    (r : ℕ) : (F.verschiebungCurve (p ^ r) (pow_ne_zero r hp) γ).IsTypical p :=
  (isTypical_verschiebungCurve_pow_iff hp r).mpr hγ

/-- Cartier's homothety operator `[r]` preserves `p`-typicality of curves. -/
theorem IsTypical.homothetyCurve {γ : F.Curve} {p : ℕ} (hγ : γ.IsTypical p) (r : R) :
    (F.homothetyCurve r γ).IsTypical p :=
  fun q hq hqp ↦ by rw [F.frobeniusCurve_homothetyCurve, hγ q hq hqp, map_zero]

/-- Base change of rings preserves `p`-typicality of curves. -/
theorem IsTypical.map {γ : F.Curve} {p : ℕ} (hγ : γ.IsTypical p) (φ : R →+* S) :
    (Curve.map φ γ).IsTypical p :=
  fun q hq hqp ↦ by rw [← F.map_frobeniusCurve φ q hq.ne_zero, hγ q hq hqp, map_zero]

/-- Base change along an injective ring homomorphism preserves and reflects `p`-typicality. -/
theorem isTypical_map_iff_of_injective {γ : F.Curve} {p : ℕ} {φ : R →+* S}
    (hφ : Function.Injective φ) : (Curve.map φ γ).IsTypical p ↔ γ.IsTypical p :=
  ⟨fun h q hq hqp ↦ Curve.map_injective hφ <| by rw [F.map_frobeniusCurve, h q hq hqp, map_zero],
    fun h ↦ h.map φ⟩

end IsTypical

end Curve

/-- The additive subgroup of `p`-typical curves on a commutative formal group law `F`. -/
noncomputable def typicalCurveSubgroup (F : FormalGroup R) [F.IsComm] (p : ℕ) :
    AddSubgroup F.Curve where
  carrier := {γ : F.Curve | γ.IsTypical p}
  zero_mem' := Curve.IsTypical.zero p
  add_mem' hγ hδ := hγ.add hδ
  neg_mem' hγ := hγ.neg

/-- Membership in `F.typicalCurveSubgroup p` unfolds to `Curve.IsTypical`. -/
@[simp]
theorem mem_typicalCurveSubgroup {F : FormalGroup R} [F.IsComm] {p : ℕ} {γ : F.Curve} :
    γ ∈ F.typicalCurveSubgroup p ↔ γ.IsTypical p := Iff.rfl

/-- Formal-group homomorphisms preserve `p`-typicality of curves. -/
theorem _root_.TauCeti.FormalGroupHom.isTypical_mapCurve {F G : FormalGroup R} [F.IsComm]
    [G.IsComm] (f : FormalGroupHom F G) {γ : F.Curve} {p : ℕ} (hγ : γ.IsTypical p) :
    (f.mapCurve γ).IsTypical p :=
  fun q hq hqp ↦ by rw [← f.mapCurve_frobeniusCurve q hq.ne_zero, hγ q hq hqp, map_zero]

/-- A formal-group isomorphism's underlying homomorphism preserves and reflects `p`-typicality. -/
@[simp]
theorem _root_.TauCeti.FormalGroupIso.isTypical_toHom_mapCurve_iff {F G : FormalGroup R} [F.IsComm]
    [G.IsComm] (e : FormalGroupIso F G) {γ : F.Curve} {p : ℕ} :
    (e.toHom.mapCurve γ).IsTypical p ↔ γ.IsTypical p :=
  ⟨fun h ↦ by simpa [← FormalGroupHom.comp_mapCurve, e.invHom_comp_toHom] using
      e.invHom.isTypical_mapCurve h,
    fun h ↦ e.toHom.isTypical_mapCurve h⟩

namespace Curve

/-! ### Additive and rational-logarithm characterizations of `p`-typicality -/

/-- On `𝔾ₐ`, any curve supported in degrees whose prime factors divide `p` is `p`-typical. -/
theorem isTypical_𝔾ₐ_of_coeff_eq_zero {γ : (𝔾ₐ (R := R)).Curve} {p : ℕ}
    (hγ : ∀ k : ℕ, (∃ q ∈ k.primeFactors, ¬ q ∣ p) → PowerSeries.coeff k γ.toPowerSeries = 0) :
    γ.IsTypical p := fun q hq hqp ↦ Curve.ext <| PowerSeries.ext fun m ↦ by
  rw [toPowerSeries_frobeniusCurve_𝔾ₐ, PowerSeries.coeff_smul, PowerSeries.coeff_cartier,
    Nat.add_zero, toPowerSeries_zero, map_zero]
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · rw [hγ (q * m) ⟨q, Nat.mem_primeFactors.mpr ⟨hq, dvd_mul_right q m,
      mul_ne_zero hq.ne_zero hm⟩, hqp⟩, smul_zero]

/-- On `𝔾ₐ`, when every prime `q ∤ p` is regular on `R`, `γ` is `p`-typical iff its coefficients
vanish in every degree having a prime factor not dividing `p`. -/
theorem isTypical_𝔾ₐ_iff {γ : (𝔾ₐ (R := R)).Curve} {p : ℕ}
    (hreg : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsSMulRegular R (q : R)) :
    γ.IsTypical p ↔
      ∀ k : ℕ, (∃ q ∈ k.primeFactors, ¬ q ∣ p) → PowerSeries.coeff k γ.toPowerSeries = 0 := by
  refine ⟨fun hγ k ⟨q, hqk, hqp⟩ ↦ ?_, isTypical_𝔾ₐ_of_coeff_eq_zero⟩
  obtain ⟨hq, ⟨m, rfl⟩, _⟩ := Nat.mem_primeFactors.mp hqk
  apply hreg q hq hqp
  simpa only [toPowerSeries_frobeniusCurve_𝔾ₐ, PowerSeries.coeff_smul, PowerSeries.coeff_cartier,
    Nat.add_zero, toPowerSeries_zero, map_zero, smul_zero] using
    congrArg (fun δ : (𝔾ₐ (R := R)).Curve ↦ PowerSeries.coeff m δ.toPowerSeries) (hγ q hq hqp)

/-- Over a `ℚ`-algebra, `γ` is `p`-typical iff `log_F(γ(T))` has zero coefficient in every degree
divisible by a prime not dividing `p`. -/
theorem isTypical_iff_coeff_subst_log_eq_zero [Algebra ℚ R] {F : FormalGroup R} [F.IsComm]
    {γ : F.Curve} {p : ℕ} :
    γ.IsTypical p ↔ ∀ k : ℕ, (∃ q ∈ k.primeFactors, ¬ q ∣ p) →
      PowerSeries.coeff k (PowerSeries.subst γ.toPowerSeries F.log) = 0 := by
  have hreg : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsSMulRegular R (q : R) := fun q hq _ ↦
    (by simpa only [map_natCast] using
      (Ne.isUnit (Nat.cast_ne_zero.mpr hq.ne_zero) : IsUnit (q : ℚ)).map (algebraMap ℚ R) :
      IsUnit (q : R)).isSMulRegular R
  rw [← F.logIso.isTypical_toHom_mapCurve_iff, isTypical_𝔾ₐ_iff hreg]
  simp only [logIso_toHom, FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries]

/-- Over a `ℚ`-algebra, for a prime `p`, `γ` is `p`-typical iff `log_F(γ(T))` is supported in
degrees `p^r`. -/
theorem isTypical_iff_coeff_subst_log_eq_zero_of_prime [Algebra ℚ R] {F : FormalGroup R}
    [F.IsComm] {γ : F.Curve} {p : ℕ} (hp : p.Prime) :
    γ.IsTypical p ↔ ∀ k : ℕ, (∀ r : ℕ, p ^ r ≠ k) →
      PowerSeries.coeff k (PowerSeries.subst γ.toPowerSeries F.log) = 0 := by
  rw [isTypical_iff_coeff_subst_log_eq_zero]
  refine forall_congr' fun k ↦ ?_
  rcases eq_or_ne k 0 with rfl | hk0
  · have h0 := (F.logHom.mapCurve γ).coeff_zero_toPowerSeries
    simp_all [FormalGroupHom.toPowerSeries_mapCurve]
  · refine imp_congr_left (not_iff_not.mp ?_)
    push Not
    exact (hp.forall_mem_primeFactors_dvd_iff_exists_eq_pow hk0).trans
      (exists_congr fun _ ↦ eq_comm)

end Curve

/-! ### Cartier's infinite typical projector -/

section TypicalProjector

variable (F : FormalGroup R) [F.IsComm]

/-- Finite stage `n` of Cartier's typical projector, composing `1 - V_q [q]⁻¹ f_q` over primes
`q ≤ n` not dividing `p`. -/
private noncomputable def typicalProjectorStage (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) : ℕ → (F.Curve →+ F.Curve)
  | 0 => AddMonoidHom.id F.Curve
  | n + 1 =>
    if hq : (n + 1).Prime ∧ ¬ (n + 1) ∣ p then
      (F.cartierProjectorCurve (n + 1) (Nat.succ_ne_zero n) (hunit (n + 1) hq.1 hq.2)).comp
        (typicalProjectorStage p hunit n)
    else typicalProjectorStage p hunit n

private theorem commute_typicalProjectorStage {G : FormalGroup S} [G.IsComm]
    (Φ : F.Curve → G.Curve) (p : ℕ)
    (hR : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R))
    (hS : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : S))
    (hstep : ∀ q (hq : q.Prime) (hqp : ¬ q ∣ p) (δ : F.Curve),
      Φ (F.cartierProjectorCurve q hq.ne_zero (hR q hq hqp) δ) =
        G.cartierProjectorCurve q hq.ne_zero (hS q hq hqp) (Φ δ))
    (n : ℕ) (γ : F.Curve) :
    Φ (F.typicalProjectorStage p hR n γ) = G.typicalProjectorStage p hS n (Φ γ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [typicalProjectorStage, typicalProjectorStage]
    split_ifs with hq
    · rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, hstep _ hq.1 hq.2, ih]
    · exact ih

section FixedPrime

variable (p : ℕ) (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R))

private theorem coeff_typicalProjectorStage_succ_of_le {k n : ℕ} (hkn : k ≤ n) (γ : F.Curve) :
    PowerSeries.coeff k (F.typicalProjectorStage p hunit (n + 1) γ).toPowerSeries =
      PowerSeries.coeff k (F.typicalProjectorStage p hunit n γ).toPowerSeries := by
  rw [typicalProjectorStage]
  split_ifs with hq
  · exact F.coeff_cartierProjectorCurve_of_lt (n + 1) (Nat.succ_ne_zero n)
      (hunit (n + 1) hq.1 hq.2) (Nat.lt_succ_of_le hkn) _
  · rfl

private theorem coeff_typicalProjectorStage_of_le {k m n : ℕ} (hkm : k ≤ m) (hmn : m ≤ n)
    (γ : F.Curve) :
    PowerSeries.coeff k (F.typicalProjectorStage p hunit n γ).toPowerSeries =
      PowerSeries.coeff k (F.typicalProjectorStage p hunit m γ).toPowerSeries := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih => rw [F.coeff_typicalProjectorStage_succ_of_le p hunit (hkm.trans hmn), ih]

/-- **Cartier's typical projector** on curves of `F` when every prime `q ∤ p` is a unit in `R`:
degree `k` comes from composing `1 - V_q [q]_F⁻¹ f_q` over primes `q ≤ k` with `q ∤ p`. -/
noncomputable def typicalProjectorCurve : F.Curve →+ F.Curve where
  toFun γ :=
    { toPowerSeries := PowerSeries.mk fun k ↦
        PowerSeries.coeff k (F.typicalProjectorStage p hunit k γ).toPowerSeries
      constantCoeff_toPowerSeries := by
        simp [← PowerSeries.coeff_zero_eq_constantCoeff_apply, typicalProjectorStage] }
  map_zero' := Curve.ext <| PowerSeries.ext fun _ ↦ by
    simp only [PowerSeries.coeff_mk, map_zero, Curve.toPowerSeries_zero]
  map_add' γ₁ γ₂ := Curve.ext <| PowerSeries.ext fun k ↦ by
    simp only [PowerSeries.coeff_mk, map_add]
    exact Curve.coeff_add_congr
      (fun i hik ↦ by simpa only [PowerSeries.coeff_mk] using
        F.coeff_typicalProjectorStage_of_le p hunit (le_refl i) hik γ₁)
      (fun i hik ↦ by simpa only [PowerSeries.coeff_mk] using
        F.coeff_typicalProjectorStage_of_le p hunit (le_refl i) hik γ₂)

private theorem coeff_typicalProjectorCurve_eq_stage {k n : ℕ} (hkn : k ≤ n) (γ : F.Curve) :
    PowerSeries.coeff k (F.typicalProjectorCurve p hunit γ).toPowerSeries =
      PowerSeries.coeff k (F.typicalProjectorStage p hunit n γ).toPowerSeries := by
  simp only [typicalProjectorCurve, AddMonoidHom.coe_mk, ZeroHom.coe_mk, PowerSeries.coeff_mk]
  exact (F.coeff_typicalProjectorStage_of_le p hunit (le_refl k) hkn γ).symm

/-- Below the least prime `∤ p`, Cartier's typical projector leaves coefficients fixed. -/
theorem coeff_typicalProjectorCurve_of_forall_prime_le_dvd {k : ℕ}
    (hk : ∀ q : ℕ, q ≤ k → q.Prime → q ∣ p) (γ : F.Curve) :
    PowerSeries.coeff k (F.typicalProjectorCurve p hunit γ).toPowerSeries =
      PowerSeries.coeff k γ.toPowerSeries := by
  have hstage : ∀ n ≤ k, F.typicalProjectorStage p hunit n γ = γ := fun n hn ↦ by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [typicalProjectorStage, dite_eq_right fun hq ↦ hq.2 (hk (n + 1) hn hq.1),
        ih (Nat.le_of_succ_le hn)]
  rw [F.coeff_typicalProjectorCurve_eq_stage p hunit (le_refl k), hstage k (le_refl k)]

/-- Cartier's typical projector preserves the linear coefficient `coeff 1` of every curve. -/
@[simp]
theorem coeff_one_typicalProjectorCurve (γ : F.Curve) :
    PowerSeries.coeff 1 (F.typicalProjectorCurve p hunit γ).toPowerSeries =
      PowerSeries.coeff 1 γ.toPowerSeries :=
  F.coeff_typicalProjectorCurve_of_forall_prime_le_dvd p hunit
    (fun _ hq1 hq ↦ absurd hq1 (not_le_of_gt hq.one_lt)) γ

end FixedPrime

/-- At `p = 0`, Cartier's typical projector is the identity. -/
@[simp]
theorem typicalProjectorCurve_zero (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ 0 → IsUnit (q : R)) :
    F.typicalProjectorCurve 0 hunit = AddMonoidHom.id F.Curve := by
  ext γ k
  exact F.coeff_typicalProjectorCurve_of_forall_prime_le_dvd 0 hunit (fun _ _ _ ↦ dvd_zero _) γ

/-- Base change of rings commutes with Cartier's typical projector. -/
theorem map_typicalProjectorCurve (φ : R →+* S) (p : ℕ)
    (hR : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) (γ : F.Curve) :
    Curve.map φ (F.typicalProjectorCurve p hR γ) =
      (F.map φ).typicalProjectorCurve p
        (fun q hq hqp ↦ by simpa only [map_natCast] using (hR q hq hqp).map φ)
        (Curve.map φ γ) := by
  let hS : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : S) := fun q hq hqp ↦ by
    simpa only [map_natCast] using (hR q hq hqp).map φ
  ext k
  have hstage := F.commute_typicalProjectorStage (Curve.map φ) p hR hS
    (fun q hq hqp δ ↦ F.map_cartierProjectorCurve φ q hq.ne_zero (hR q hq hqp) δ) k γ
  rw [Curve.toPowerSeries_map, PowerSeries.coeff_map,
    F.coeff_typicalProjectorCurve_eq_stage p hR (le_refl k),
    (F.map φ).coeff_typicalProjectorCurve_eq_stage p hS (le_refl k),
    ← hstage, Curve.toPowerSeries_map, PowerSeries.coeff_map]

/-- Formal-group homomorphisms commute with Cartier's typical projector. -/
theorem _root_.TauCeti.FormalGroupHom.mapCurve_typicalProjectorCurve
    {F G : FormalGroup R} [F.IsComm] [G.IsComm] (f : FormalGroupHom F G) (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) (γ : F.Curve) :
    f.mapCurve (F.typicalProjectorCurve p hunit γ) =
      G.typicalProjectorCurve p hunit (f.mapCurve γ) := by
  ext k
  have htrunc : PowerSeries.trunc (k + 1) (F.typicalProjectorCurve p hunit γ).toPowerSeries =
      PowerSeries.trunc (k + 1) (F.typicalProjectorStage p hunit k γ).toPowerSeries := by
    ext i
    simp only [PowerSeries.coeff_trunc]
    split_ifs with hi
    · exact F.coeff_typicalProjectorCurve_eq_stage p hunit (by omega) γ
    · rfl
  have hstage := F.commute_typicalProjectorStage f.mapCurve p hunit hunit
    (fun q hq hqp δ ↦ f.mapCurve_cartierProjectorCurve q hq.ne_zero (hunit q hq hqp) δ) k γ
  rw [FormalGroupHom.toPowerSeries_mapCurve,
    ← PowerSeries.coeff_trunc_comp_trunc f.toPowerSeries
      (F.typicalProjectorCurve p hunit γ).constantCoeff_toPowerSeries (Nat.lt_succ_self k)
      (Nat.lt_succ_self k), htrunc, PowerSeries.coeff_trunc_comp_trunc f.toPowerSeries
      (F.typicalProjectorStage p hunit k γ).constantCoeff_toPowerSeries (Nat.lt_succ_self k)
      (Nat.lt_succ_self k), ← FormalGroupHom.toPowerSeries_mapCurve, hstage,
    G.coeff_typicalProjectorCurve_eq_stage p hunit (le_refl k)]

/-! ### Action on `𝔾ₐ` and on the formal logarithm -/

private theorem coeff_typicalProjectorStage_𝔾ₐ (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) (n k : ℕ)
    (γ : (𝔾ₐ (R := R)).Curve) :
    PowerSeries.coeff k ((𝔾ₐ (R := R)).typicalProjectorStage p hunit n γ).toPowerSeries =
      if ∀ q ∈ k.primeFactors, q ≤ n → q ∣ p then PowerSeries.coeff k γ.toPowerSeries else 0 := by
  induction n with
  | zero =>
    rw [typicalProjectorStage, AddMonoidHom.id_apply,
      ite_eq_left fun q hqk hq0 ↦ absurd hq0 (not_le_of_gt (Nat.pos_of_mem_primeFactors hqk))]
  | succ n ih =>
    rw [typicalProjectorStage]
    by_cases hq : (n + 1).Prime ∧ ¬ (n + 1) ∣ p
    · rw [dite_eq_left hq, AddMonoidHom.comp_apply, toPowerSeries_cartierProjectorCurve_𝔾ₐ,
        map_sub, PowerSeries.coeff_expand]
      by_cases hdvd : (n + 1) ∣ k
      · rw [ite_eq_left hdvd, PowerSeries.coeff_cartier, Nat.add_zero, Nat.mul_div_cancel' hdvd,
          sub_self]
        rcases eq_or_ne k 0 with rfl | hk0
        · simp
        · exact (ite_eq_right fun hall ↦
            hq.2 (hall (n + 1) (Nat.mem_primeFactors.mpr ⟨hq.1, hdvd, hk0⟩) (le_refl _))).symm
      · rw [ite_eq_right hdvd, sub_zero, ih]
        exact if_congr ⟨fun hall q hqk hqle ↦ (Nat.of_le_succ hqle).elim (hall q hqk)
            fun h ↦ by subst h; exact absurd (Nat.dvd_of_mem_primeFactors hqk) hdvd,
          fun hall q hqk hqn ↦ hall q hqk (Nat.le_succ_of_le hqn)⟩ rfl rfl
    · rw [dite_eq_right hq, ih]
      exact if_congr ⟨fun hall q hqk hqle ↦ (Nat.of_le_succ hqle).elim (hall q hqk) fun h ↦ by
          subst h; exact Classical.byContradiction fun hnp ↦
            hq ⟨Nat.prime_of_mem_primeFactors hqk, hnp⟩,
        fun hall q hqk hqn ↦ hall q hqk (Nat.le_succ_of_le hqn)⟩ rfl rfl

/-- On `𝔾ₐ`, Cartier's typical projector retains degrees whose prime factors all divide `p` and
zeroes out all other degrees. -/
@[simp]
theorem coeff_typicalProjectorCurve_𝔾ₐ (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) (k : ℕ) (γ : (𝔾ₐ (R := R)).Curve) :
    PowerSeries.coeff k ((𝔾ₐ (R := R)).typicalProjectorCurve p hunit γ).toPowerSeries =
      if ∀ q ∈ k.primeFactors, q ∣ p then PowerSeries.coeff k γ.toPowerSeries else 0 := by
  rw [(𝔾ₐ (R := R)).coeff_typicalProjectorCurve_eq_stage p hunit (le_refl k),
    coeff_typicalProjectorStage_𝔾ₐ]
  exact if_congr ⟨fun h q hqk ↦ h q hqk (Nat.le_of_mem_primeFactors hqk),
    fun h q hqk _ ↦ h q hqk⟩ rfl rfl

/-- Over a `ℚ`-algebra, Cartier's typical projector retains precisely those coefficients of
`log_F(γ(T))` whose degrees have all prime factors dividing `p`. -/
theorem coeff_subst_typicalProjectorCurve_log [Algebra ℚ R] (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) (k : ℕ) (γ : F.Curve) :
    PowerSeries.coeff k
        (PowerSeries.subst (F.typicalProjectorCurve p hunit γ).toPowerSeries F.log) =
      if ∀ q ∈ k.primeFactors, q ∣ p then
        PowerSeries.coeff k (PowerSeries.subst γ.toPowerSeries F.log)
      else 0 := by
  simpa only [FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries,
    coeff_typicalProjectorCurve_𝔾ₐ] using
    congrArg (fun δ : (𝔾ₐ (R := R)).Curve ↦ PowerSeries.coeff k δ.toPowerSeries)
      (F.logHom.mapCurve_typicalProjectorCurve p hunit γ)

/-- Over a `ℚ`-algebra, for a prime `p`, Cartier's typical projector retains degrees `p^r` of
`log_F(γ(T))` and deletes all other degrees. -/
theorem coeff_subst_typicalProjectorCurve_log_of_prime [Algebra ℚ R] {p : ℕ} (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) (k : ℕ) (γ : F.Curve) :
    PowerSeries.coeff k
        (PowerSeries.subst (F.typicalProjectorCurve p hunit γ).toPowerSeries F.log) =
      if p ^ Nat.log p k = k then PowerSeries.coeff k (PowerSeries.subst γ.toPowerSeries F.log)
      else 0 := by
  rw [F.coeff_subst_typicalProjectorCurve_log p hunit k γ]
  rcases eq_or_ne k 0 with rfl | hk0
  · have h0 := (F.logHom.mapCurve γ).coeff_zero_toPowerSeries
    simp_all [FormalGroupHom.toPowerSeries_mapCurve]
  · refine if_congr ((hp.forall_mem_primeFactors_dvd_iff_exists_eq_pow hk0).trans
      ⟨fun ⟨r, hr⟩ ↦ by rw [hr, Nat.log_pow hp.one_lt], fun h ↦ ⟨Nat.log p k, h.symm⟩⟩) rfl rfl

/-- Over a `ℚ`-algebra, Cartier's typical projector preserves degree-`p^r` log coefficients. -/
@[simp]
theorem coeff_subst_typicalProjectorCurve_log_pow [Algebra ℚ R] (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) (r : ℕ) (γ : F.Curve) :
    PowerSeries.coeff (p ^ r)
        (PowerSeries.subst (F.typicalProjectorCurve p hunit γ).toPowerSeries F.log) =
      PowerSeries.coeff (p ^ r) (PowerSeries.subst γ.toPowerSeries F.log) := by
  rw [F.coeff_subst_typicalProjectorCurve_log p hunit,
    ite_eq_left fun _ hq ↦ (Nat.prime_of_mem_primeFactors hq).dvd_of_dvd_pow
      (Nat.dvd_of_mem_primeFactors hq)]

/-- Over a `ℚ`-algebra, for a prime `p`, Cartier's typical projector zeroes out all logarithm
coefficients in degrees not of the form `p^r`. -/
@[simp]
theorem coeff_subst_typicalProjectorCurve_log_eq_zero [Algebra ℚ R] {p : ℕ} (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) {k : ℕ} (hk : ∀ r : ℕ, p ^ r ≠ k)
    (γ : F.Curve) :
    PowerSeries.coeff k
        (PowerSeries.subst (F.typicalProjectorCurve p hunit γ).toPowerSeries F.log) = 0 := by
  rw [F.coeff_subst_typicalProjectorCurve_log_of_prime hp hunit, ite_eq_right (hk _)]

/-! ### Operator identities and idempotence when primes not dividing `p` are invertible -/

section FixedPrime

variable (p : ℕ) (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R))

/-- `f_n` annihilates `F.typicalProjectorCurve p hunit` whenever `n` has a prime factor `∤ p`. -/
theorem frobeniusCurve_typicalProjectorCurve_eq_zero {n : ℕ} (hn : n ≠ 0)
    (hq : ∃ q ∈ n.primeFactors, ¬ q ∣ p) (γ : F.Curve) :
    F.frobeniusCurve n hn (F.typicalProjectorCurve p hunit γ) = 0 :=
  Curve.eq_of_forall_ratAlgebra F γ {q : ℕ | q.Prime ∧ ¬ q ∣ p} (fun q hq ↦ hunit q hq.1 hq.2)
    (fun G _ hB δ ↦ G.frobeniusCurve n hn
      (G.typicalProjectorCurve p (fun q hq hqp ↦ hB q ⟨hq, hqp⟩) δ))
    (fun _ _ _ _ ↦ 0)
    (fun G _ _ δ ↦ Curve.eq_zero_of_coeff_subst_log_eq_zero fun {k} hk0 ↦ by
      obtain ⟨q, hqn, hqp⟩ := hq
      obtain ⟨hq_prime, hqdvd, _⟩ := Nat.mem_primeFactors.mp hqn
      have hqk : q ∈ (n * k).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hq_prime, dvd_mul_of_dvd_left hqdvd k, mul_ne_zero hn hk0⟩
      simp only [subst_frobeniusCurve_log, PowerSeries.coeff_smul, PowerSeries.coeff_cartier,
        Nat.add_zero, coeff_subst_typicalProjectorCurve_log, smul_eq_mul]
      rw [ite_eq_right fun hall ↦ hqp (hall q hqk), mul_zero])
    (fun G _ _ _ φ _ ↦ by rw [G.map_frobeniusCurve, G.map_typicalProjectorCurve φ p])
    (fun _ _ _ _ φ _ ↦ map_zero (Curve.map φ))
    (fun _ f _ ↦ by rw [f.mapCurve_frobeniusCurve, f.mapCurve_typicalProjectorCurve])
    (fun _ f _ ↦ map_zero f.mapCurve)

/-- `f_n` annihilates `F.typicalProjectorCurve p hunit` for every `n > 1` coprime to `p`. -/
theorem frobeniusCurve_typicalProjectorCurve_of_coprime {n : ℕ} (hn1 : 1 < n) (hcop : n.Coprime p)
    (γ : F.Curve) : F.frobeniusCurve n (by omega) (F.typicalProjectorCurve p hunit γ) = 0 :=
  F.frobeniusCurve_typicalProjectorCurve_eq_zero p hunit (by omega)
    (hcop.exists_mem_primeFactors_not_dvd hn1) γ

/-- `f_q` annihilates `F.typicalProjectorCurve p hunit` for every prime `q ∤ p`. -/
@[simp]
theorem frobeniusCurve_typicalProjectorCurve_of_not_dvd {q : ℕ} (hq : q.Prime) (hqp : ¬ q ∣ p)
    (γ : F.Curve) : F.frobeniusCurve q hq.ne_zero (F.typicalProjectorCurve p hunit γ) = 0 :=
  F.frobeniusCurve_typicalProjectorCurve_eq_zero p hunit hq.ne_zero
    ⟨q, Nat.mem_primeFactors.mpr ⟨hq, dvd_rfl, hq.ne_zero⟩, hqp⟩ γ

/-- Every curve in the image of Cartier's typical projector is `p`-typical. -/
@[simp]
theorem isTypical_typicalProjectorCurve (γ : F.Curve) :
    (F.typicalProjectorCurve p hunit γ).IsTypical p :=
  fun _ hq hqp ↦ F.frobeniusCurve_typicalProjectorCurve_of_not_dvd p hunit hq hqp γ

/-- Every `p`-typical curve is fixed by Cartier's typical projector. -/
theorem typicalProjectorCurve_eq_self {γ : F.Curve} (hγ : γ.IsTypical p) :
    F.typicalProjectorCurve p hunit γ = γ := by
  have hstage : ∀ n, F.typicalProjectorStage p hunit n γ = γ := fun n ↦ by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [typicalProjectorStage]
      split_ifs with hq
      · rw [AddMonoidHom.comp_apply, ih]
        exact F.cartierProjectorCurve_eq_self (n + 1) (Nat.succ_ne_zero n)
          (hunit (n + 1) hq.1 hq.2) (hγ (n + 1) hq.1 hq.2)
      · exact ih
  ext k
  rw [F.coeff_typicalProjectorCurve_eq_stage p hunit (le_refl k), hstage k]

/-- The fixed points of Cartier's typical projector are precisely the `p`-typical curves. -/
@[simp]
theorem typicalProjectorCurve_eq_self_iff (γ : F.Curve) :
    F.typicalProjectorCurve p hunit γ = γ ↔ γ.IsTypical p :=
  ⟨fun h ↦ h ▸ F.isTypical_typicalProjectorCurve p hunit γ, F.typicalProjectorCurve_eq_self p hunit⟩

/-- Cartier's typical projector is idempotent on curves. -/
@[simp]
theorem typicalProjectorCurve_typicalProjectorCurve (γ : F.Curve) :
    F.typicalProjectorCurve p hunit (F.typicalProjectorCurve p hunit γ) =
      F.typicalProjectorCurve p hunit γ :=
  F.typicalProjectorCurve_eq_self p hunit (F.isTypical_typicalProjectorCurve p hunit γ)

/-- Cartier's typical projector is an idempotent in the endomorphism ring of `F.Curve`. -/
@[simp]
theorem isIdempotentElem_typicalProjectorCurve :
    IsIdempotentElem (M := AddMonoid.End F.Curve) (F.typicalProjectorCurve p hunit) :=
  AddMonoidHom.ext (F.typicalProjectorCurve_typicalProjectorCurve p hunit)

/-- The image of Cartier's typical projector is the subgroup of `p`-typical curves. -/
@[simp]
theorem range_typicalProjectorCurve :
    (F.typicalProjectorCurve p hunit).range = F.typicalCurveSubgroup p :=
  SetLike.ext fun γ ↦ (AddMonoidHom.mem_range).trans
    ⟨by rintro ⟨δ, rfl⟩; exact F.isTypical_typicalProjectorCurve p hunit δ,
      fun hγ ↦ ⟨γ, F.typicalProjectorCurve_eq_self p hunit hγ⟩⟩

/-- `V_n` is annihilated by `typicalProjectorCurve` whenever `n` has a prime factor `∤ p`. -/
theorem typicalProjectorCurve_verschiebungCurve_eq_zero {n : ℕ} (hn : n ≠ 0)
    (hq : ∃ q ∈ n.primeFactors, ¬ q ∣ p) (γ : F.Curve) :
    F.typicalProjectorCurve p hunit (F.verschiebungCurve n hn γ) = 0 :=
  Curve.eq_of_forall_ratAlgebra F γ {q : ℕ | q.Prime ∧ ¬ q ∣ p} (fun q hq ↦ hunit q hq.1 hq.2)
    (fun G _ hB δ ↦ G.typicalProjectorCurve p (fun q hq hqp ↦ hB q ⟨hq, hqp⟩)
      (G.verschiebungCurve n hn δ))
    (fun _ _ _ _ ↦ 0)
    (fun G _ _ δ ↦ Curve.eq_zero_of_coeff_subst_log_eq_zero fun {k} hk0 ↦ by
      simp only [coeff_subst_typicalProjectorCurve_log, subst_verschiebungCurve_log,
        PowerSeries.coeff_expand]
      split_ifs with hprime hdvd
      · obtain ⟨m, rfl⟩ := hdvd
        obtain ⟨q, hqn, hqp⟩ := hq
        obtain ⟨hq_prime, hqdvd, _⟩ := Nat.mem_primeFactors.mp hqn
        exact absurd (hprime q (Nat.mem_primeFactors.mpr
          ⟨hq_prime, dvd_mul_of_dvd_left hqdvd m, mul_ne_zero hn (right_ne_zero_of_mul hk0)⟩)) hqp
      all_goals rfl)
    (fun G _ _ _ φ _ ↦ by rw [G.map_typicalProjectorCurve φ p, G.map_verschiebungCurve])
    (fun _ _ _ _ φ _ ↦ map_zero (Curve.map φ))
    (fun _ f _ ↦ by rw [f.mapCurve_typicalProjectorCurve, f.mapCurve_verschiebungCurve])
    (fun _ f _ ↦ map_zero f.mapCurve)

/-- `V_n` is annihilated by `F.typicalProjectorCurve p hunit` for every `n > 1` coprime to `p`. -/
theorem typicalProjectorCurve_verschiebungCurve_of_coprime {n : ℕ} (hn1 : 1 < n)
    (hcop : n.Coprime p) (γ : F.Curve) :
    F.typicalProjectorCurve p hunit (F.verschiebungCurve n (by omega) γ) = 0 :=
  F.typicalProjectorCurve_verschiebungCurve_eq_zero p hunit (by omega)
    (hcop.exists_mem_primeFactors_not_dvd hn1) γ

/-- Cartier's typical projector commutes with `V_n` when every prime factor of `n` divides `p`. -/
theorem typicalProjectorCurve_verschiebungCurve_of_forall_prime_dvd {n : ℕ} (hn : n ≠ 0)
    (hdvd : ∀ q : ℕ, q.Prime → q ∣ n → q ∣ p) (γ : F.Curve) :
    F.typicalProjectorCurve p hunit (F.verschiebungCurve n hn γ) =
      F.verschiebungCurve n hn (F.typicalProjectorCurve p hunit γ) := by
  ext k
  have hstage := (F.commute_typicalProjectorStage (F.verschiebungCurve n hn) p hunit hunit
    (fun q hq hqp δ ↦ (F.cartierProjectorCurve_verschiebungCurve_of_coprime hq.ne_zero hn
      (hunit q hq hqp) (hq.coprime_iff_not_dvd.mpr fun hqn ↦ hqp (hdvd q hq hqn)) δ).symm)
    k γ).symm
  rw [F.coeff_typicalProjectorCurve_eq_stage p hunit (le_refl k), hstage,
    toPowerSeries_verschiebungCurve, toPowerSeries_verschiebungCurve,
    PowerSeries.coeff_expand, PowerSeries.coeff_expand]
  split_ifs with hnk
  · exact (F.coeff_typicalProjectorCurve_eq_stage p hunit (Nat.div_le_self k n) γ).symm
  · rfl

/-- Cartier's typical projector commutes with `f_n` when every prime factor of `n` divides `p`. -/
theorem frobeniusCurve_typicalProjectorCurve_of_forall_prime_dvd {n : ℕ} (hn : n ≠ 0)
    (hdvd : ∀ q : ℕ, q.Prime → q ∣ n → q ∣ p) (γ : F.Curve) :
    F.frobeniusCurve n hn (F.typicalProjectorCurve p hunit γ) =
      F.typicalProjectorCurve p hunit (F.frobeniusCurve n hn γ) :=
  Curve.eq_of_forall_ratAlgebra F γ {q : ℕ | q.Prime ∧ ¬ q ∣ p} (fun q hq ↦ hunit q hq.1 hq.2)
    (fun G _ hB δ ↦ G.frobeniusCurve n hn
      (G.typicalProjectorCurve p (fun q hq hqp ↦ hB q ⟨hq, hqp⟩) δ))
    (fun G _ hB δ ↦ G.typicalProjectorCurve p (fun q hq hqp ↦ hB q ⟨hq, hqp⟩)
      (G.frobeniusCurve n hn δ))
    (fun G _ _ δ ↦ Curve.eq_of_coeff_subst_log_eq fun {k} hk0 ↦ by
      simp only [subst_frobeniusCurve_log, coeff_subst_typicalProjectorCurve_log,
        PowerSeries.coeff_smul, PowerSeries.coeff_cartier, Nat.add_zero, smul_eq_mul]
      have hiff : (∀ q ∈ (n * k).primeFactors, q ∣ p) ↔ ∀ q ∈ k.primeFactors, q ∣ p :=
        ⟨fun h q hqk ↦ h q (Nat.primeFactors_mono (dvd_mul_left k n) (mul_ne_zero hn hk0) hqk),
          fun h q hqnk ↦ by
            obtain ⟨hq, hq_dvd, _⟩ := Nat.mem_primeFactors.mp hqnk
            exact (hq.dvd_mul.mp hq_dvd).elim (hdvd q hq)
              fun hqk ↦ h q (Nat.mem_primeFactors.mpr ⟨hq, hqk, hk0⟩)⟩
      rw [if_congr hiff rfl rfl]
      split_ifs <;> simp)
    (fun G _ _ _ φ _ ↦ by rw [G.map_frobeniusCurve, G.map_typicalProjectorCurve φ p])
    (fun G _ _ _ φ _ ↦ by rw [G.map_typicalProjectorCurve φ p, G.map_frobeniusCurve])
    (fun _ f _ ↦ by rw [f.mapCurve_frobeniusCurve, f.mapCurve_typicalProjectorCurve])
    (fun _ f _ ↦ by rw [f.mapCurve_typicalProjectorCurve, f.mapCurve_frobeniusCurve])

/-- Elementary projector `ε_n` fixes `typicalProjectorCurve` when `n` has a prime `∤ p`. -/
theorem cartierProjectorCurve_typicalProjectorCurve {n : ℕ} (hn : n ≠ 0)
    (hq : ∃ q ∈ n.primeFactors, ¬ q ∣ p) (hn_unit : IsUnit (n : R)) (γ : F.Curve) :
    F.cartierProjectorCurve n hn hn_unit (F.typicalProjectorCurve p hunit γ) =
      F.typicalProjectorCurve p hunit γ :=
  F.cartierProjectorCurve_eq_self n hn hn_unit
    (F.frobeniusCurve_typicalProjectorCurve_eq_zero p hunit hn hq γ)

/-- `F.typicalProjectorCurve p hunit` absorbs `ε_n` when `n` has a prime factor `∤ p`. -/
theorem typicalProjectorCurve_cartierProjectorCurve {n : ℕ} (hn : n ≠ 0)
    (hq : ∃ q ∈ n.primeFactors, ¬ q ∣ p) (hn_unit : IsUnit (n : R)) (γ : F.Curve) :
    F.typicalProjectorCurve p hunit (F.cartierProjectorCurve n hn hn_unit γ) =
      F.typicalProjectorCurve p hunit γ := by
  rw [cartierProjectorCurve_apply, map_sub,
    F.typicalProjectorCurve_verschiebungCurve_eq_zero p hunit hn hq, sub_zero]

/-- Cartier's typical projector commutes with Cartier's homothety operator `[r]`. -/
theorem typicalProjectorCurve_homothetyCurve (r : R) (γ : F.Curve) :
    F.typicalProjectorCurve p hunit (F.homothetyCurve r γ) =
      F.homothetyCurve r (F.typicalProjectorCurve p hunit γ) := by
  ext k
  have hstage := (F.commute_typicalProjectorStage (F.homothetyCurve r) p hunit hunit
    (fun q hq hqp δ ↦ (F.cartierProjectorCurve_homothetyCurve r q hq.ne_zero
      (hunit q hq hqp) δ).symm) k γ).symm
  rw [F.coeff_typicalProjectorCurve_eq_stage p hunit (le_refl k), hstage,
    toPowerSeries_homothetyCurve, toPowerSeries_homothetyCurve, PowerSeries.coeff_rescale,
    PowerSeries.coeff_rescale, F.coeff_typicalProjectorCurve_eq_stage p hunit (le_refl k)]

/-- `δ` is the typical projection of `γ` iff `δ` is `p`-typical and `γ - δ` is in the kernel. -/
theorem typicalProjectorCurve_eq_iff {γ δ : F.Curve} :
    F.typicalProjectorCurve p hunit γ = δ ↔
      δ.IsTypical p ∧ γ - δ ∈ (F.typicalProjectorCurve p hunit).ker := by
  rw [AddMonoidHom.mem_ker, map_sub]
  exact ⟨by rintro rfl; exact ⟨F.isTypical_typicalProjectorCurve p hunit γ,
      by rw [F.typicalProjectorCurve_typicalProjectorCurve, sub_self]⟩,
    fun ⟨hδ, hker⟩ ↦ sub_eq_zero.mp (F.typicalProjectorCurve_eq_self p hunit hδ ▸ hker)⟩

end FixedPrime

section NonzeroPrime

variable {p : ℕ} (hp : p ≠ 0) (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R))

/-- Cartier's typical projector commutes with `V_p` for `p ≠ 0`. -/
theorem typicalProjectorCurve_verschiebungCurve_self (γ : F.Curve) :
    F.typicalProjectorCurve p hunit (F.verschiebungCurve p hp γ) =
      F.verschiebungCurve p hp (F.typicalProjectorCurve p hunit γ) :=
  F.typicalProjectorCurve_verschiebungCurve_of_forall_prime_dvd p hunit hp (fun _ _ h ↦ h) γ

/-- Cartier's typical projector commutes with `V_{p^r}` for `p ≠ 0`. -/
theorem typicalProjectorCurve_verschiebungCurve_pow (r : ℕ) (γ : F.Curve) :
    F.typicalProjectorCurve p hunit (F.verschiebungCurve (p ^ r) (pow_ne_zero r hp) γ) =
      F.verschiebungCurve (p ^ r) (pow_ne_zero r hp) (F.typicalProjectorCurve p hunit γ) :=
  F.typicalProjectorCurve_verschiebungCurve_of_forall_prime_dvd p hunit (pow_ne_zero r hp)
    (fun _ hq hqr ↦ hq.dvd_of_dvd_pow hqr) γ

/-- Cartier's typical projector commutes with `f_p` for `p ≠ 0`. -/
theorem frobeniusCurve_typicalProjectorCurve_self (γ : F.Curve) :
    F.frobeniusCurve p hp (F.typicalProjectorCurve p hunit γ) =
      F.typicalProjectorCurve p hunit (F.frobeniusCurve p hp γ) :=
  F.frobeniusCurve_typicalProjectorCurve_of_forall_prime_dvd p hunit hp (fun _ _ h ↦ h) γ

/-- Cartier's typical projector commutes with `f_{p^r}` for `p ≠ 0`. -/
theorem frobeniusCurve_typicalProjectorCurve_pow (r : ℕ) (γ : F.Curve) :
    F.frobeniusCurve (p ^ r) (pow_ne_zero r hp) (F.typicalProjectorCurve p hunit γ) =
      F.typicalProjectorCurve p hunit (F.frobeniusCurve (p ^ r) (pow_ne_zero r hp) γ) :=
  F.frobeniusCurve_typicalProjectorCurve_of_forall_prime_dvd p hunit (pow_ne_zero r hp)
    (fun _ hq hqr ↦ hq.dvd_of_dvd_pow hqr) γ

end NonzeroPrime

end TypicalProjector

end FormalGroup
