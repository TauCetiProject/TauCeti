/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Curve.Projector
import TauCeti.Algebra.Module.Rat
import TauCeti.Data.Nat.Pow

/-!
# `p`-typical curves and Cartier's `p`-typical curve projector

Let `F(X, Y)` be a one-dimensional commutative formal group law over a commutative ring `R`, and
let `p` be a natural number (in applications, a prime). Following Cartier, a curve `γ ∈ F.Curve` is
**`p`-typical** (`FormalGroup.Curve.IsPTypical`) if it is annihilated by Cartier's Frobenius
operator `f_q` at every prime `q ≠ p`:

  `f_q γ = 0` for all primes `q ≠ p`.

Since `f_{mn} = f_m ∘ f_n`, this is equivalent (for every `p : ℕ`) to `f_n γ = 0` for all nonzero
`n` that are not powers of `p`, and when `p` is prime it is also equivalent to `f_n γ = 0` for all
`n > 1` coprime to `p`. The `p`-typical curves form an additive subgroup
`FormalGroup.pTypicalCurveSubgroup` stable under all Frobenius operators `f_n` and, when `p` is
prime, preserved and reflected by `V_{p^k}`. Over a `ℚ`-algebra, `γ` is `p`-typical (for `p` prime)
if and only if `log_F(γ(T))` has nonzero coefficients only in degrees `p^k`.

When every prime `q ≠ p` is invertible in `R`, the elementary Cartier projectors
`1 - V_q [q]⁻¹ f_q` (`FormalGroup.cartierProjectorCurve`) at primes `q ≠ p` commute pairwise and
leave all coefficients below degree `q` unchanged. Their coefficientwise infinite composition
defines **Cartier's `p`-typical curve projector** (`FormalGroup.pTypicalProjectorCurve`), an
idempotent additive endomorphism of `F.Curve` whose image and fixed-point subgroup are the
`p`-typical curves, and whose kernel contains `V_n(F.Curve)` for every nonzero `n` not of the form
`p^k`. Over a `ℚ`-algebra (for `p` prime), applying `pTypicalProjectorCurve` to `γ` retains the
`T^(p^k)` coefficients of `log_F(γ(T))` and deletes all other degrees.

## Main definitions

* `FormalGroup.Curve.IsPTypical`: the predicate that `f_q γ = 0` for every prime `q ≠ p`.
* `FormalGroup.pTypicalCurveSubgroup`: the additive subgroup of `p`-typical curves on `F`.
* `FormalGroup.pTypicalProjectorCurve`: Cartier's idempotent projection onto `p`-typical curves
  when all primes `q ≠ p` are invertible in `R`.

## Main results

* `FormalGroup.Curve.isPTypical_iff_forall_ne_pow` and
  `FormalGroup.Curve.isPTypical_iff_forall_coprime`: characterizations of `p`-typical curves via
  non-powers of `p` and via indices coprime to `p`.
* `FormalGroup.Curve.isPTypical_verschiebungCurve_pow_iff` and
  `FormalGroup.Curve.IsPTypical.frobeniusCurve`: action of `V_{p^k}` and `f_n` on `p`-typical
  curves.
* `FormalGroup.Curve.isPTypical_iff_coeff_subst_log_eq_zero`: rational logarithm characterization
  of `p`-typical curves.
* `FormalGroup.isPTypical_pTypicalProjectorCurve`,
  `FormalGroup.pTypicalProjectorCurve_eq_self_iff`, and
  `FormalGroup.range_pTypicalProjectorCurve`: Cartier's projector lands in and fixes precisely the
  `p`-typical curves.
* `FormalGroup.pTypicalProjectorCurve_verschiebungCurve_eq_zero_of_forall_ne_pow`: Cartier's
  projector kills `V_n` whenever `n ≠ 0` is not a power of `p`.
* `FormalGroup.map_pTypicalProjectorCurve` and
  `TauCeti.FormalGroupHom.mapCurve_pTypicalProjectorCurve`: naturality under base change and
  homomorphisms of formal group laws.
* `FormalGroup.coeff_subst_pTypicalProjectorCurve_log_pow` and
  `FormalGroup.coeff_subst_pTypicalProjectorCurve_log_eq_zero`: action of Cartier's projector on
  the formal logarithm over a `ℚ`-algebra.

## References

* P. Cartier, *Modules associés à un groupe formel commutatif. Courbes typiques*, C. R. Acad. Sci.
  Paris Sér. A-B 265 (1967), A129–A132.
* D. Quillen, *On the formal group laws of unoriented and complex cobordism theory*, Bull. Amer.
  Math. Soc. 75 (1969), 1293–1298.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapter III, §16.2–16.3.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Academic Press (1986),
  Appendix A2.1.21–A2.1.23.
-/

public section

namespace FormalGroup

variable {R S : Type*} [CommRing R] [CommRing S]

/-! ### `p`-typical curves -/

namespace Curve

section IsPTypical

variable {F : FormalGroup R} [F.IsComm]

/-- A curve `γ` on a commutative formal group law `F` is **`p`-typical** if Cartier's Frobenius
operator `f_q` annihilates `γ` at every prime `q ≠ p`. -/
def IsPTypical (γ : F.Curve) (p : ℕ) : Prop :=
  ∀ ⦃q : ℕ⦄ (hq : q.Prime), q ≠ p → F.frobeniusCurve q hq.ne_zero γ = 0

/-- Defining equivalence for `FormalGroup.Curve.IsPTypical`. -/
theorem isPTypical_def (γ : F.Curve) (p : ℕ) :
    γ.IsPTypical p ↔ ∀ ⦃q : ℕ⦄ (hq : q.Prime), q ≠ p → F.frobeniusCurve q hq.ne_zero γ = 0 :=
  (Iff.rfl)

/-- A `p`-typical curve is killed by `f_q` at every prime `q ≠ p`. -/
theorem IsPTypical.frobeniusCurve_eq_zero {γ : F.Curve} {p : ℕ} (hγ : γ.IsPTypical p)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) :
    F.frobeniusCurve q hq.ne_zero γ = 0 :=
  hγ hq hqp

/-- A `p`-typical curve is killed by `f_n` at every nonzero `n` that is not a power of `p`. -/
theorem IsPTypical.frobeniusCurve_eq_zero_of_forall_ne_pow {γ : F.Curve} {p : ℕ}
    (hγ : γ.IsPTypical p) {n : ℕ} (hn : n ≠ 0) (hpow : ∀ k, n ≠ p ^ k) :
    F.frobeniusCurve n hn γ = 0 := by
  obtain ⟨q, hq, ⟨m, rfl⟩, hqp⟩ := Nat.exists_prime_dvd_ne_of_forall_ne_pow hn hpow
  have hm : m ≠ 0 := right_ne_zero_of_mul hn
  rw [F.frobeniusCurve_congr (Nat.mul_comm q m) hn (mul_ne_zero hm hq.ne_zero),
    ← frobeniusCurve_frobeniusCurve F hm hq.ne_zero, hγ hq hqp, map_zero]

/-- A curve is `p`-typical if and only if `f_n γ = 0` for all nonzero `n` not of the form `p^k`. -/
theorem isPTypical_iff_forall_ne_pow (γ : F.Curve) (p : ℕ) :
    γ.IsPTypical p ↔ ∀ ⦃n : ℕ⦄ (hn : n ≠ 0), (∀ k, n ≠ p ^ k) → F.frobeniusCurve n hn γ = 0 := by
  refine ⟨fun hγ _ hn hpow ↦ hγ.frobeniusCurve_eq_zero_of_forall_ne_pow hn hpow, fun h q hq hqp ↦
    h hq.ne_zero fun k hqk ↦ ?_⟩
  rcases eq_or_ne k 0 with rfl | hk
  · exact hq.ne_one hqk
  · rcases hq.eq_one_or_self_of_dvd p (hqk ▸ dvd_pow_self p hk) with rfl | rfl
    · exact hq.ne_one (hqk.trans (one_pow k))
    · exact hqp rfl

/-- A `p`-typical curve is killed by `f_n` at every `n > 1` coprime to `p`. -/
theorem IsPTypical.frobeniusCurve_eq_zero_of_coprime {γ : F.Curve} {p : ℕ}
    (hγ : γ.IsPTypical p) {n : ℕ} (hn : 1 < n) (hcop : p.Coprime n) :
    F.frobeniusCurve n (by omega) γ = 0 := by
  refine hγ.frobeniusCurve_eq_zero_of_forall_ne_pow (by omega) fun k hnk ↦ ?_
  rcases eq_or_ne k 0 with rfl | hk
  · simp at hnk
    omega
  · have hp1 : p = 1 := (Nat.gcd_eq_left (hnk ▸ dvd_pow_self p hk)).symm.trans hcop
    subst hp1
    simp at hnk
    omega

/-- For a prime `p`, a curve is `p`-typical if and only if `f_n γ = 0` for all `n > 1` coprime to
`p`. -/
theorem isPTypical_iff_forall_coprime (γ : F.Curve) {p : ℕ} (hp : p.Prime) :
    γ.IsPTypical p ↔ ∀ ⦃n : ℕ⦄ (hn : 1 < n), p.Coprime n → F.frobeniusCurve n (by omega) γ = 0 :=
  ⟨fun hγ _ hn hcop ↦ hγ.frobeniusCurve_eq_zero_of_coprime hn hcop,
   fun h _ hq hqp ↦ h hq.one_lt ((Nat.coprime_primes hp hq).mpr hqp.symm)⟩

/-- The zero curve is `p`-typical. -/
@[simp]
theorem isPTypical_zero (p : ℕ) : (0 : F.Curve).IsPTypical p :=
  fun _ _ _ ↦ map_zero _

/-- Sums of `p`-typical curves are `p`-typical. -/
theorem IsPTypical.add {γ₁ γ₂ : F.Curve} {p : ℕ} (h₁ : γ₁.IsPTypical p) (h₂ : γ₂.IsPTypical p) :
    (γ₁ + γ₂).IsPTypical p :=
  fun _ hq hqp ↦ by rw [map_add, h₁ hq hqp, h₂ hq hqp, _root_.add_zero]

/-- Negatives of `p`-typical curves are `p`-typical. -/
theorem IsPTypical.neg {γ : F.Curve} {p : ℕ} (hγ : γ.IsPTypical p) : (-γ).IsPTypical p :=
  fun _ hq hqp ↦ by rw [map_neg, hγ hq hqp, neg_zero]

/-- Negation preserves and reflects `p`-typical curves. -/
@[simp]
theorem isPTypical_neg_iff {γ : F.Curve} {p : ℕ} : (-γ).IsPTypical p ↔ γ.IsPTypical p :=
  ⟨fun h ↦ neg_neg γ ▸ h.neg, IsPTypical.neg⟩

/-- Differences of `p`-typical curves are `p`-typical. -/
theorem IsPTypical.sub {γ₁ γ₂ : F.Curve} {p : ℕ} (h₁ : γ₁.IsPTypical p) (h₂ : γ₂.IsPTypical p) :
    (γ₁ - γ₂).IsPTypical p :=
  sub_eq_add_neg γ₁ γ₂ ▸ h₁.add h₂.neg

/-- Natural-number multiples of `p`-typical curves are `p`-typical. -/
theorem IsPTypical.nsmul {γ : F.Curve} {p : ℕ} (hγ : γ.IsPTypical p) (n : ℕ) :
    (n • γ).IsPTypical p :=
  fun _ hq hqp ↦ by rw [map_nsmul, hγ hq hqp, smul_zero]

/-- Integer multiples of `p`-typical curves are `p`-typical. -/
theorem IsPTypical.zsmul {γ : F.Curve} {p : ℕ} (hγ : γ.IsPTypical p) (n : ℤ) :
    (n • γ).IsPTypical p :=
  fun _ hq hqp ↦ by rw [map_zsmul, hγ hq hqp, smul_zero]

/-- Cartier's Frobenius operators preserve `p`-typicality at every nonzero index. -/
theorem IsPTypical.frobeniusCurve {γ : F.Curve} {p : ℕ} (hγ : γ.IsPTypical p)
    (n : ℕ) (hn : n ≠ 0) : (F.frobeniusCurve n hn γ).IsPTypical p := by
  intro q hq hqp
  rw [frobeniusCurve_frobeniusCurve,
    F.frobeniusCurve_congr (Nat.mul_comm q n) (mul_ne_zero hq.ne_zero hn)
      (mul_ne_zero hn hq.ne_zero),
    ← frobeniusCurve_frobeniusCurve F hn hq.ne_zero, hγ hq hqp, map_zero]

/-- Verschiebung `V_n` preserves and reflects `p`-typicality whenever `n` is coprime to every prime
`q ≠ p`. -/
theorem isPTypical_verschiebungCurve_iff_of_forall_prime_coprime {p n : ℕ} (hn : n ≠ 0)
    (hcop : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → q.Coprime n) (γ : F.Curve) :
    (F.verschiebungCurve n hn γ).IsPTypical p ↔ γ.IsPTypical p := by
  refine ⟨fun h q hq hqp ↦ ?_, fun h q hq hqp ↦ ?_⟩
  · apply F.verschiebungCurve_injective n hn
    rw [map_zero, ← frobeniusCurve_verschiebungCurve_of_coprime F hq.ne_zero hn (hcop hq hqp)]
    exact h hq hqp
  · rw [frobeniusCurve_verschiebungCurve_of_coprime F hq.ne_zero hn (hcop hq hqp), h hq hqp,
      map_zero]

/-- For a prime `p`, `V_{p^k} γ` is `p`-typical if and only if `γ` is `p`-typical. -/
@[simp]
theorem isPTypical_verschiebungCurve_pow_iff {p : ℕ} (hp : p.Prime) (k : ℕ) (γ : F.Curve) :
    (F.verschiebungCurve (p ^ k) (pow_ne_zero k hp.ne_zero) γ).IsPTypical p ↔ γ.IsPTypical p :=
  isPTypical_verschiebungCurve_iff_of_forall_prime_coprime (pow_ne_zero k hp.ne_zero)
    (fun _ hq hqp ↦ ((Nat.coprime_primes hq hp).mpr hqp).pow_right k) γ

/-- For a prime `p`, `V_{p^k}` preserves `p`-typicality. -/
theorem IsPTypical.verschiebungCurve_pow {γ : F.Curve} {p : ℕ} (hp : p.Prime)
    (hγ : γ.IsPTypical p) (k : ℕ) :
    (F.verschiebungCurve (p ^ k) (pow_ne_zero k hp.ne_zero) γ).IsPTypical p :=
  (isPTypical_verschiebungCurve_pow_iff hp k γ).mpr hγ

/-- Base change along a ring homomorphism preserves `p`-typical curves. -/
theorem IsPTypical.map (φ : R →+* S) {γ : F.Curve} {p : ℕ} (hγ : γ.IsPTypical p) :
    (Curve.map φ γ).IsPTypical p := by
  intro q hq hqp
  rw [← map_frobeniusCurve, hγ hq hqp, map_zero]

/-- Base change along an injective ring homomorphism preserves and reflects `p`-typical curves. -/
theorem isPTypical_map_iff {φ : R →+* S} (hφ : Function.Injective φ) (γ : F.Curve) (p : ℕ) :
    (Curve.map φ γ).IsPTypical p ↔ γ.IsPTypical p := by
  refine ⟨fun h q hq hqp ↦ ?_, IsPTypical.map φ⟩
  apply Curve.map_injective hφ
  rw [map_zero, map_frobeniusCurve]
  exact h hq hqp

end IsPTypical

section Additive

/-- On the additive formal group law `𝔾ₐ`, a curve whose nonzero coefficients occur only in
degrees `p^n` (for `p` prime) is `p`-typical over any commutative ring. -/
theorem isPTypical_𝔾ₐ_of_coeff_eq_zero {p : ℕ} (hp : p.Prime) {γ : (𝔾ₐ (R := R)).Curve}
    (h : ∀ k, (∀ n, p ^ n ≠ k) → PowerSeries.coeff k γ.toPowerSeries = 0) :
    γ.IsPTypical p := by
  intro q hq hqp
  ext k
  rw [toPowerSeries_frobeniusCurve_𝔾ₐ, toPowerSeries_zero, map_zero, PowerSeries.coeff_smul,
    PowerSeries.coeff_cartier, Nat.add_zero]
  rcases eq_or_ne k 0 with rfl | _
  · simp
  · have hpow : ∀ n, p ^ n ≠ q * k := fun n hnk ↦
      hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow (hnk ▸ dvd_mul_right q k)))
    rw [h (q * k) hpow, smul_zero]

/-- When all primes `q ≠ p` are units in `R`, every `p`-typical curve on `𝔾ₐ` has zero
coefficients outside degrees `p^n`. -/
theorem IsPTypical.coeff_𝔾ₐ_eq_zero {p : ℕ}
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R))
    {γ : (𝔾ₐ (R := R)).Curve} (hγ : γ.IsPTypical p) {k : ℕ} (hk : ∀ n, p ^ n ≠ k) :
    PowerSeries.coeff k γ.toPowerSeries = 0 := by
  rcases eq_or_ne k 0 with rfl | hk0
  · exact γ.coeff_zero_toPowerSeries
  · obtain ⟨q, hq, ⟨j, rfl⟩, hqp⟩ := Nat.exists_prime_dvd_ne_of_forall_ne_pow hk0 fun n hkn ↦
      hk n hkn.symm
    have hf : PowerSeries.coeff j ((𝔾ₐ (R := R)).frobeniusCurve q hq.ne_zero γ).toPowerSeries = 0 :=
      by rw [hγ hq hqp, toPowerSeries_zero, map_zero]
    rw [toPowerSeries_frobeniusCurve_𝔾ₐ, PowerSeries.coeff_smul, PowerSeries.coeff_cartier,
      Nat.add_zero] at hf
    exact (hunit hq hqp).smul_eq_zero.mp hf

/-- For a prime `p` when all primes `q ≠ p` are units in `R`, a curve on `𝔾ₐ` is `p`-typical if
and only if its coefficients vanish outside degrees `p^n`. -/
theorem isPTypical_𝔾ₐ_iff {p : ℕ} (hp : p.Prime)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) (γ : (𝔾ₐ (R := R)).Curve) :
    γ.IsPTypical p ↔ ∀ k, (∀ n, p ^ n ≠ k) → PowerSeries.coeff k γ.toPowerSeries = 0 :=
  ⟨fun hγ _ hk ↦ hγ.coeff_𝔾ₐ_eq_zero hunit hk, isPTypical_𝔾ₐ_of_coeff_eq_zero hp⟩

end Additive

end Curve

/-- The additive subgroup of `p`-typical curves on a commutative formal group law `F`. -/
def pTypicalCurveSubgroup (F : FormalGroup R) [F.IsComm] (p : ℕ) : AddSubgroup F.Curve where
  carrier := {γ | γ.IsPTypical p}
  zero_mem' := Curve.isPTypical_zero p
  add_mem' h₁ h₂ := h₁.add h₂
  neg_mem' h := h.neg

/-- Membership in `FormalGroup.pTypicalCurveSubgroup` is `FormalGroup.Curve.IsPTypical`. -/
@[simp]
theorem mem_pTypicalCurveSubgroup (F : FormalGroup R) [F.IsComm] {p : ℕ} {γ : F.Curve} :
    γ ∈ F.pTypicalCurveSubgroup p ↔ γ.IsPTypical p :=
  (Iff.rfl)

end FormalGroup

namespace TauCeti

section Hom

variable {R : Type*} [CommRing R] {F G : FormalGroup R} [F.IsComm] [G.IsComm]

namespace FormalGroupHom

/-- Homomorphisms of commutative formal group laws push `p`-typical curves to `p`-typical
curves. -/
theorem mapCurve_isPTypical (f : FormalGroupHom F G) {γ : F.Curve} {p : ℕ}
    (hγ : γ.IsPTypical p) : (f.mapCurve γ).IsPTypical p := by
  intro q hq hqp
  rw [← f.mapCurve_frobeniusCurve, hγ hq hqp, map_zero]

end FormalGroupHom

namespace FormalGroupIso

/-- Pushforward along the forward homomorphism of an isomorphism of commutative formal group laws
preserves and reflects `p`-typical curves. -/
@[simp]
theorem isPTypical_mapCurve_toHom_iff (e : FormalGroupIso F G) (γ : F.Curve) (p : ℕ) :
    (e.toHom.mapCurve γ).IsPTypical p ↔ γ.IsPTypical p :=
  ⟨fun h ↦ by
    simpa [← FormalGroupHom.comp_mapCurve] using e.invHom.mapCurve_isPTypical h,
   e.toHom.mapCurve_isPTypical⟩

/-- Pushforward along the inverse homomorphism of an isomorphism of commutative formal group laws
preserves and reflects `p`-typical curves. -/
@[simp]
theorem isPTypical_mapCurve_invHom_iff (e : FormalGroupIso F G) (γ : G.Curve) (p : ℕ) :
    (e.invHom.mapCurve γ).IsPTypical p ↔ γ.IsPTypical p := by
  simpa using e.symm.isPTypical_mapCurve_toHom_iff γ p

/-- The curve equivalence attached to an isomorphism of commutative formal group laws preserves and
reflects `p`-typical curves. -/
theorem isPTypical_curveEquiv_iff (e : FormalGroupIso F G) (γ : F.Curve) (p : ℕ) :
    (e.curveEquiv γ).IsPTypical p ↔ γ.IsPTypical p := by
  rw [curveEquiv_apply, isPTypical_mapCurve_toHom_iff]

end FormalGroupIso

end Hom

end TauCeti

namespace FormalGroup

variable {R S : Type*} [CommRing R] [CommRing S]

namespace Curve

section Logarithm

variable [Algebra ℚ R] {F : FormalGroup R} [F.IsComm]

/-- Over a `ℚ`-algebra, the formal logarithm of a `p`-typical curve vanishes outside degrees
`p^n`. -/
theorem IsPTypical.coeff_subst_log_eq_zero {γ : F.Curve} {p : ℕ} (hγ : γ.IsPTypical p)
    {k : ℕ} (hk : ∀ n, p ^ n ≠ k) :
    PowerSeries.coeff k (PowerSeries.subst γ.toPowerSeries F.log) = 0 := by
  simpa only [TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logIso_toHom,
    logHom_toPowerSeries] using
    (F.logIso.toHom.mapCurve_isPTypical hγ).coeff_𝔾ₐ_eq_zero
      (fun _ hq _ ↦ TauCeti.isUnit_natCast_of_ne_zero hq.ne_zero) hk

/-- Over a `ℚ`-algebra and for a prime `p`, a curve `γ` on `F` is `p`-typical if and only if
`log_F(γ(T))` has zero coefficients outside degrees `p^n`. -/
theorem isPTypical_iff_coeff_subst_log_eq_zero {p : ℕ} (hp : p.Prime) (γ : F.Curve) :
    γ.IsPTypical p ↔
      ∀ k, (∀ n, p ^ n ≠ k) →
        PowerSeries.coeff k (PowerSeries.subst γ.toPowerSeries F.log) = 0 := by
  rw [← F.logIso.isPTypical_mapCurve_toHom_iff,
    isPTypical_𝔾ₐ_iff hp (fun _ hq _ ↦ TauCeti.isUnit_natCast_of_ne_zero hq.ne_zero)]
  simp [logIso_toHom, logHom_toPowerSeries]

end Logarithm

end Curve

/-! ### Cartier's `p`-typical curve projector -/

section Projector

variable (F : FormalGroup R) [F.IsComm]

/-- Finite-stage partial product of the elementary Cartier projectors `1 - V_q [q]⁻¹ f_q` over all
primes `q < N` with `q ≠ p`. -/
private noncomputable def pTypicalProjectorStage (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) : ℕ → (F.Curve →+ F.Curve)
  | 0 => AddMonoidHom.id F.Curve
  | n + 1 =>
    if h : n.Prime ∧ n ≠ p then
      (F.cartierProjectorCurve n h.1.ne_zero (hunit h.1 h.2)).comp
        (pTypicalProjectorStage p hunit n)
    else
      pTypicalProjectorStage p hunit n

private theorem coeff_pTypicalProjectorStage_of_lt {p : ℕ}
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) {k m N : ℕ}
    (hkm : k < m) (hmN : m ≤ N) (γ : F.Curve) :
    PowerSeries.coeff k (F.pTypicalProjectorStage p hunit N γ).toPowerSeries =
      PowerSeries.coeff k (F.pTypicalProjectorStage p hunit m γ).toPowerSeries := by
  induction N with
  | zero =>
    obtain rfl : m = 0 := Nat.eq_zero_of_le_zero hmN
    omega
  | succ n ih =>
    rcases Nat.of_le_succ hmN with hmn | rfl
    · simp only [pTypicalProjectorStage]
      split_ifs with h
      · rw [AddMonoidHom.comp_apply,
          F.coeff_cartierProjectorCurve_of_lt n h.1.ne_zero (hunit h.1 h.2) (hkm.trans_le hmn),
          ih hmn]
      · exact ih hmn
    · rfl

/-- Underlying curve map of `FormalGroup.pTypicalProjectorCurve`, taking the degree-`k` coefficient
from stage `k + 1` after stabilization. -/
private noncomputable def pTypicalProjectorFun (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) : F.Curve where
  toPowerSeries := PowerSeries.mk fun k ↦
    PowerSeries.coeff k (F.pTypicalProjectorStage p hunit (k + 1) γ).toPowerSeries
  constantCoeff_toPowerSeries := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk,
      Curve.coeff_zero_toPowerSeries]

private theorem coeff_pTypicalProjectorFun_eq_stage {p : ℕ}
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) {k N : ℕ} (hk : k < N)
    (γ : F.Curve) :
    PowerSeries.coeff k (F.pTypicalProjectorFun p hunit γ).toPowerSeries =
      PowerSeries.coeff k (F.pTypicalProjectorStage p hunit N γ).toPowerSeries := by
  rw [pTypicalProjectorFun, PowerSeries.coeff_mk]
  exact (F.coeff_pTypicalProjectorStage_of_lt hunit (Nat.lt_succ_self k) hk γ).symm

/-- **Cartier's `p`-typical curve projector** on a commutative formal group law `F`, when all
primes `q ≠ p` are units in `R`: the coefficientwise infinite composition of the elementary Cartier
projectors `1 - V_q [q]⁻¹ f_q` over all primes `q ≠ p`. -/
noncomputable def pTypicalProjectorCurve (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) : F.Curve →+ F.Curve where
  toFun := F.pTypicalProjectorFun p hunit
  map_zero' := by
    ext k
    rw [F.coeff_pTypicalProjectorFun_eq_stage hunit (Nat.lt_succ_self k), map_zero,
      Curve.toPowerSeries_zero, map_zero]
  map_add' γ₁ γ₂ := by
    ext k
    have h₁ : ∀ i ≤ k,
        PowerSeries.coeff i (F.pTypicalProjectorFun p hunit γ₁).toPowerSeries =
          PowerSeries.coeff i (F.pTypicalProjectorStage p hunit (k + 1) γ₁).toPowerSeries :=
      fun i hi ↦ F.coeff_pTypicalProjectorFun_eq_stage hunit (Nat.lt_succ_of_le hi) γ₁
    have h₂ : ∀ i ≤ k,
        PowerSeries.coeff i (F.pTypicalProjectorFun p hunit γ₂).toPowerSeries =
          PowerSeries.coeff i (F.pTypicalProjectorStage p hunit (k + 1) γ₂).toPowerSeries :=
      fun i hi ↦ F.coeff_pTypicalProjectorFun_eq_stage hunit (Nat.lt_succ_of_le hi) γ₂
    rw [F.coeff_pTypicalProjectorFun_eq_stage hunit (Nat.lt_succ_self k), map_add,
      Curve.coeff_add_congr h₁ h₂]

private theorem coeff_pTypicalProjectorCurve_eq_stage {p : ℕ}
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) {k N : ℕ} (hk : k < N)
    (γ : F.Curve) :
    PowerSeries.coeff k (F.pTypicalProjectorCurve p hunit γ).toPowerSeries =
      PowerSeries.coeff k (F.pTypicalProjectorStage p hunit N γ).toPowerSeries :=
  F.coeff_pTypicalProjectorFun_eq_stage hunit hk γ

/-- Cartier's `p`-typical projector leaves unchanged every coefficient of degree strictly smaller
than every prime `q ≠ p`. -/
theorem coeff_pTypicalProjectorCurve_of_forall_prime_gt {p k : ℕ}
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R))
    (hk : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → k < q) (γ : F.Curve) :
    PowerSeries.coeff k (F.pTypicalProjectorCurve p hunit γ).toPowerSeries =
      PowerSeries.coeff k γ.toPowerSeries := by
  have hstage : ∀ N,
      PowerSeries.coeff k (F.pTypicalProjectorStage p hunit N γ).toPowerSeries =
        PowerSeries.coeff k γ.toPowerSeries := fun N ↦ by
    induction N with
    | zero => rfl
    | succ n ih =>
      simp only [pTypicalProjectorStage]
      split_ifs with h
      · rw [AddMonoidHom.comp_apply,
          F.coeff_cartierProjectorCurve_of_lt n h.1.ne_zero (hunit h.1 h.2) (hk h.1 h.2), ih]
      · exact ih
  rw [F.coeff_pTypicalProjectorCurve_eq_stage hunit (Nat.lt_succ_self k), hstage]

/-- Cartier's `p`-typical projector preserves the linear coefficient of every curve. -/
@[simp]
theorem coeff_one_pTypicalProjectorCurve (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    PowerSeries.coeff 1 (F.pTypicalProjectorCurve p hunit γ).toPowerSeries =
      PowerSeries.coeff 1 γ.toPowerSeries :=
  F.coeff_pTypicalProjectorCurve_of_forall_prime_gt hunit (fun _ hq _ ↦ hq.one_lt) γ

private theorem frobeniusCurve_pTypicalProjectorStage_eq_zero {p q N : ℕ}
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R))
    (hq : q.Prime) (hqp : q ≠ p) (hqN : q < N) (γ : F.Curve) :
    F.frobeniusCurve q hq.ne_zero (F.pTypicalProjectorStage p hunit N γ) = 0 := by
  induction N with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hqN with hqn | rfl
    · simp only [pTypicalProjectorStage]
      split_ifs with h
      · rw [AddMonoidHom.comp_apply,
          F.frobeniusCurve_cartierProjectorCurve_of_coprime hq.ne_zero h.1.ne_zero
            (hunit h.1 h.2) ((Nat.coprime_primes hq h.1).mpr (Nat.ne_of_lt hqn)),
          ih hqn, map_zero]
      · exact ih hqn
    · simp only [pTypicalProjectorStage, dite_eq_left (And.intro hq hqp), AddMonoidHom.comp_apply,
        frobeniusCurve_cartierProjectorCurve]

/-- The image of every curve under Cartier's `p`-typical projector is `p`-typical. -/
theorem isPTypical_pTypicalProjectorCurve (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    (F.pTypicalProjectorCurve p hunit γ).IsPTypical p := by
  intro q hq hqp
  ext k
  let N := max (q + 1) (k * q + 1)
  have hqN : q < N := (Nat.lt_succ_self q).trans_le (le_max_left _ _)
  have hcongr : ∀ i ≤ k * q,
      PowerSeries.coeff i (F.pTypicalProjectorCurve p hunit γ).toPowerSeries =
        PowerSeries.coeff i (F.pTypicalProjectorStage p hunit N γ).toPowerSeries :=
    fun i hi ↦ F.coeff_pTypicalProjectorCurve_eq_stage hunit
      ((Nat.lt_succ_of_le hi).trans_le (le_max_right _ _)) γ
  rw [F.coeff_frobeniusCurve_congr hq.ne_zero hcongr,
    F.frobeniusCurve_pTypicalProjectorStage_eq_zero hunit hq hqp hqN γ,
    Curve.toPowerSeries_zero, map_zero]

/-- Every `p`-typical curve is fixed by Cartier's `p`-typical projector. -/
theorem pTypicalProjectorCurve_eq_self {p : ℕ}
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) {γ : F.Curve}
    (hγ : γ.IsPTypical p) :
    F.pTypicalProjectorCurve p hunit γ = γ := by
  have hstage : ∀ N, F.pTypicalProjectorStage p hunit N γ = γ := fun N ↦ by
    induction N with
    | zero => rfl
    | succ n ih =>
      simp only [pTypicalProjectorStage]
      split_ifs with h
      · rw [AddMonoidHom.comp_apply, ih,
          F.cartierProjectorCurve_eq_self n h.1.ne_zero (hunit h.1 h.2) (hγ h.1 h.2)]
      · exact ih
  ext k
  rw [F.coeff_pTypicalProjectorCurve_eq_stage hunit (Nat.lt_succ_self k), hstage]

/-- A curve is fixed by Cartier's `p`-typical projector if and only if it is `p`-typical. -/
@[simp]
theorem pTypicalProjectorCurve_eq_self_iff (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    F.pTypicalProjectorCurve p hunit γ = γ ↔ γ.IsPTypical p :=
  ⟨fun h ↦ h ▸ F.isPTypical_pTypicalProjectorCurve p hunit γ,
   F.pTypicalProjectorCurve_eq_self hunit⟩

/-- Cartier's `p`-typical projector is idempotent. -/
@[simp]
theorem pTypicalProjectorCurve_pTypicalProjectorCurve (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    F.pTypicalProjectorCurve p hunit (F.pTypicalProjectorCurve p hunit γ) =
      F.pTypicalProjectorCurve p hunit γ :=
  F.pTypicalProjectorCurve_eq_self hunit (F.isPTypical_pTypicalProjectorCurve p hunit γ)

/-- Cartier's `p`-typical projector is an idempotent in the endomorphism ring of curves. -/
@[simp]
theorem isIdempotentElem_pTypicalProjectorCurve (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    IsIdempotentElem (M := AddMonoid.End F.Curve) (F.pTypicalProjectorCurve p hunit) :=
  AddMonoidHom.ext (F.pTypicalProjectorCurve_pTypicalProjectorCurve p hunit)

/-- The image of Cartier's `p`-typical projector is precisely the subgroup of `p`-typical
curves. -/
@[simp]
theorem range_pTypicalProjectorCurve (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalProjectorCurve p hunit).range = F.pTypicalCurveSubgroup p := by
  ext γ
  simp only [AddMonoidHom.mem_range, mem_pTypicalCurveSubgroup]
  exact ⟨fun ⟨δ, hδ⟩ ↦ hδ ▸ F.isPTypical_pTypicalProjectorCurve p hunit δ,
    fun hγ ↦ ⟨γ, F.pTypicalProjectorCurve_eq_self hunit hγ⟩⟩

private theorem pTypicalProjectorStage_cartierProjectorCurve_comm {p m N : ℕ}
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R))
    (hm : m ≠ 0) (hm_unit : IsUnit (m : R)) (γ : F.Curve) :
    F.pTypicalProjectorStage p hunit N (F.cartierProjectorCurve m hm hm_unit γ) =
      F.cartierProjectorCurve m hm hm_unit (F.pTypicalProjectorStage p hunit N γ) := by
  induction N with
  | zero => rfl
  | succ n ih =>
    simp only [pTypicalProjectorStage]
    split_ifs with h
    · rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ih,
        F.cartierProjectorCurve_comm h.1.ne_zero hm (hunit h.1 h.2) hm_unit]
    · exact ih

/-- Cartier's `p`-typical projector annihilates `V_q γ` for every prime `q ≠ p`. -/
@[simp]
theorem pTypicalProjectorCurve_verschiebungCurve_eq_zero {p q : ℕ}
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R))
    (hq : q.Prime) (hqp : q ≠ p) (γ : F.Curve) :
    F.pTypicalProjectorCurve p hunit (F.verschiebungCurve q hq.ne_zero γ) = 0 := by
  have hzero : ∀ N > q,
      F.pTypicalProjectorStage p hunit N (F.verschiebungCurve q hq.ne_zero γ) = 0 := fun N hN ↦ by
    induction N with
    | zero => omega
    | succ n ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hN with hqn | rfl
      · simp only [pTypicalProjectorStage]
        split_ifs with h
        · rw [AddMonoidHom.comp_apply, ih hqn, map_zero]
        · exact ih hqn
      · simp only [pTypicalProjectorStage, dite_eq_left (And.intro hq hqp), AddMonoidHom.comp_apply,
          ← F.pTypicalProjectorStage_cartierProjectorCurve_comm hunit hq.ne_zero (hunit hq hqp),
          cartierProjectorCurve_verschiebungCurve, map_zero]
  ext k
  let N := max (q + 1) (k + 1)
  rw [F.coeff_pTypicalProjectorCurve_eq_stage hunit
      ((Nat.lt_succ_self k).trans_le (le_max_right _ _)),
    hzero N ((Nat.lt_succ_self q).trans_le (le_max_left _ _)),
    Curve.toPowerSeries_zero, map_zero]

/-- Cartier's `p`-typical projector annihilates `V_n γ` for every nonzero `n` not of the form
`p^k`. -/
theorem pTypicalProjectorCurve_verschiebungCurve_eq_zero_of_forall_ne_pow {p n : ℕ}
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R))
    (hn : n ≠ 0) (hpow : ∀ k, n ≠ p ^ k) (γ : F.Curve) :
    F.pTypicalProjectorCurve p hunit (F.verschiebungCurve n hn γ) = 0 := by
  obtain ⟨q, hq, ⟨m, rfl⟩, hqp⟩ := Nat.exists_prime_dvd_ne_of_forall_ne_pow hn hpow
  have hm : m ≠ 0 := right_ne_zero_of_mul hn
  rw [← F.verschiebungCurve_verschiebungCurve hq.ne_zero hm,
    F.pTypicalProjectorCurve_verschiebungCurve_eq_zero hunit hq hqp]

/-- Cartier's `p`-typical projector commutes with `V_n` whenever `n` is coprime to every prime
`q ≠ p`. -/
theorem pTypicalProjectorCurve_verschiebungCurve_of_forall_prime_coprime {p n : ℕ}
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R))
    (hn : n ≠ 0) (hcop : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → q.Coprime n) (γ : F.Curve) :
    F.pTypicalProjectorCurve p hunit (F.verschiebungCurve n hn γ) =
      F.verschiebungCurve n hn (F.pTypicalProjectorCurve p hunit γ) := by
  have hstage : ∀ N,
      F.pTypicalProjectorStage p hunit N (F.verschiebungCurve n hn γ) =
        F.verschiebungCurve n hn (F.pTypicalProjectorStage p hunit N γ) := fun N ↦ by
    induction N with
    | zero => rfl
    | succ m ih =>
      simp only [pTypicalProjectorStage]
      split_ifs with h
      · rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ih,
          F.cartierProjectorCurve_verschiebungCurve_of_coprime h.1.ne_zero hn
            (hunit h.1 h.2) (hcop h.1 h.2)]
      · exact ih
  ext k
  rw [F.coeff_pTypicalProjectorCurve_eq_stage hunit (Nat.lt_succ_self k), hstage,
    toPowerSeries_verschiebungCurve, toPowerSeries_verschiebungCurve,
    PowerSeries.coeff_expand, PowerSeries.coeff_expand]
  split_ifs with hdvd
  · exact (F.coeff_pTypicalProjectorCurve_eq_stage hunit
      (Nat.lt_succ_of_le (Nat.div_le_self k n)) γ).symm
  · rfl

/-- For a prime `p`, Cartier's `p`-typical projector commutes with `V_{p^k}`. -/
theorem pTypicalProjectorCurve_verschiebungCurve_pow {p : ℕ} (hp : p.Prime)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) (k : ℕ) (γ : F.Curve) :
    F.pTypicalProjectorCurve p hunit (F.verschiebungCurve (p ^ k) (pow_ne_zero k hp.ne_zero) γ) =
      F.verschiebungCurve (p ^ k) (pow_ne_zero k hp.ne_zero)
        (F.pTypicalProjectorCurve p hunit γ) :=
  F.pTypicalProjectorCurve_verschiebungCurve_of_forall_prime_coprime hunit
    (pow_ne_zero k hp.ne_zero) (fun _ hq hqp ↦ ((Nat.coprime_primes hq hp).mpr hqp).pow_right k) γ

/-- Cartier's `p`-typical projector commutes with `f_n` whenever `n` is coprime to every prime
`q ≠ p`. -/
theorem frobeniusCurve_pTypicalProjectorCurve_of_forall_prime_coprime {p n : ℕ}
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R))
    (hn : n ≠ 0) (hcop : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → q.Coprime n) (γ : F.Curve) :
    F.frobeniusCurve n hn (F.pTypicalProjectorCurve p hunit γ) =
      F.pTypicalProjectorCurve p hunit (F.frobeniusCurve n hn γ) := by
  have hstage : ∀ N,
      F.frobeniusCurve n hn (F.pTypicalProjectorStage p hunit N γ) =
        F.pTypicalProjectorStage p hunit N (F.frobeniusCurve n hn γ) := fun N ↦ by
    induction N with
    | zero => rfl
    | succ m ih =>
      simp only [pTypicalProjectorStage]
      split_ifs with h
      · rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
          F.frobeniusCurve_cartierProjectorCurve_of_coprime hn h.1.ne_zero
            (hunit h.1 h.2) (hcop h.1 h.2).symm,
          ih]
      · exact ih
  ext k
  let N := max (k + 1) (k * n + 1)
  have hcongr : ∀ i ≤ k * n,
      PowerSeries.coeff i (F.pTypicalProjectorCurve p hunit γ).toPowerSeries =
        PowerSeries.coeff i (F.pTypicalProjectorStage p hunit N γ).toPowerSeries :=
    fun i hi ↦ F.coeff_pTypicalProjectorCurve_eq_stage hunit
      ((Nat.lt_succ_of_le hi).trans_le (le_max_right _ _)) γ
  rw [F.coeff_frobeniusCurve_congr hn hcongr, hstage,
    F.coeff_pTypicalProjectorCurve_eq_stage hunit
      ((Nat.lt_succ_self k).trans_le (le_max_left _ _))]

/-- For a prime `p`, Cartier's `p`-typical projector commutes with `f_{p^k}`. -/
theorem frobeniusCurve_pow_pTypicalProjectorCurve {p : ℕ} (hp : p.Prime)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) (k : ℕ) (γ : F.Curve) :
    F.frobeniusCurve (p ^ k) (pow_ne_zero k hp.ne_zero) (F.pTypicalProjectorCurve p hunit γ) =
      F.pTypicalProjectorCurve p hunit
        (F.frobeniusCurve (p ^ k) (pow_ne_zero k hp.ne_zero) γ) :=
  F.frobeniusCurve_pTypicalProjectorCurve_of_forall_prime_coprime hunit
    (pow_ne_zero k hp.ne_zero) (fun _ hq hqp ↦ ((Nat.coprime_primes hq hp).mpr hqp).pow_right k) γ

/-- Base change along a ring homomorphism commutes with Cartier's `p`-typical projector. -/
theorem map_pTypicalProjectorCurve (φ : R →+* S) (p : ℕ)
    (hR : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    Curve.map φ (F.pTypicalProjectorCurve p hR γ) =
      (F.map φ).pTypicalProjectorCurve p
        (fun _ hq hqp ↦ by simpa using (hR hq hqp).map φ) (Curve.map φ γ) := by
  let hS : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : S) :=
    fun _ hq hqp ↦ by simpa using (hR hq hqp).map φ
  have hstage : ∀ N,
      Curve.map φ (F.pTypicalProjectorStage p hR N γ) =
        (F.map φ).pTypicalProjectorStage p hS N (Curve.map φ γ) := fun N ↦ by
    induction N with
    | zero => rfl
    | succ n ih =>
      simp only [pTypicalProjectorStage]
      split_ifs with h
      · rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, map_cartierProjectorCurve, ih]
      · exact ih
  ext k
  rw [Curve.toPowerSeries_map, PowerSeries.coeff_map,
    F.coeff_pTypicalProjectorCurve_eq_stage hR (Nat.lt_succ_self k),
    (F.map φ).coeff_pTypicalProjectorCurve_eq_stage hS (Nat.lt_succ_self k),
    ← hstage, Curve.toPowerSeries_map, PowerSeries.coeff_map]

/-- Homomorphisms of commutative formal group laws commute with Cartier's `p`-typical projector. -/
theorem _root_.TauCeti.FormalGroupHom.mapCurve_pTypicalProjectorCurve
    {F G : FormalGroup R} [F.IsComm] [G.IsComm] (f : TauCeti.FormalGroupHom F G)
    (p : ℕ) (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    f.mapCurve (F.pTypicalProjectorCurve p hunit γ) =
      G.pTypicalProjectorCurve p hunit (f.mapCurve γ) := by
  have hstage : ∀ N,
      f.mapCurve (F.pTypicalProjectorStage p hunit N γ) =
        G.pTypicalProjectorStage p hunit N (f.mapCurve γ) := fun N ↦ by
    induction N with
    | zero => rfl
    | succ n ih =>
      simp only [pTypicalProjectorStage]
      split_ifs with h
      · rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
          f.mapCurve_cartierProjectorCurve, ih]
      · exact ih
  ext k
  let N := k + 1
  have hcongr : PowerSeries.X ^ N ∣
      (F.pTypicalProjectorCurve p hunit γ).toPowerSeries -
        (F.pTypicalProjectorStage p hunit N γ).toPowerSeries :=
    PowerSeries.X_pow_dvd_iff.mpr fun i hi ↦ by
      rw [map_sub, F.coeff_pTypicalProjectorCurve_eq_stage hunit hi, sub_self]
  have hdvd := PowerSeries.X_pow_dvd_subst_sub_subst
    (F.pTypicalProjectorCurve p hunit γ).constantCoeff_toPowerSeries hcongr f.toPowerSeries
  have heq : PowerSeries.coeff k (f.mapCurve (F.pTypicalProjectorCurve p hunit γ)).toPowerSeries =
      PowerSeries.coeff k (f.mapCurve (F.pTypicalProjectorStage p hunit N γ)).toPowerSeries :=
    sub_eq_zero.mp <| by
      simpa only [map_sub, TauCeti.FormalGroupHom.toPowerSeries_mapCurve] using
        PowerSeries.X_pow_dvd_iff.mp hdvd k (Nat.lt_succ_self k)
  rw [heq, hstage, G.coeff_pTypicalProjectorCurve_eq_stage hunit (Nat.lt_succ_self k)]

/-- On the additive formal group law `𝔾ₐ`, Cartier's `p`-typical projector deletes every
coefficient outside degrees `p^n`. -/
theorem coeff_pTypicalProjectorCurve_𝔾ₐ_eq_zero {p k : ℕ}
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R))
    (hk : ∀ n, p ^ n ≠ k) (γ : (𝔾ₐ (R := R)).Curve) :
    PowerSeries.coeff k ((𝔾ₐ (R := R)).pTypicalProjectorCurve p hunit γ).toPowerSeries = 0 :=
  ((𝔾ₐ (R := R)).isPTypical_pTypicalProjectorCurve p hunit γ).coeff_𝔾ₐ_eq_zero hunit hk

/-- On the additive formal group law `𝔾ₐ` and for a prime `p`, Cartier's `p`-typical projector
leaves every degree-`p^n` coefficient unchanged. -/
@[simp]
theorem coeff_pTypicalProjectorCurve_𝔾ₐ_pow {p : ℕ} (hp : p.Prime)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R))
    (n : ℕ) (γ : (𝔾ₐ (R := R)).Curve) :
    PowerSeries.coeff (p ^ n) ((𝔾ₐ (R := R)).pTypicalProjectorCurve p hunit γ).toPowerSeries =
      PowerSeries.coeff (p ^ n) γ.toPowerSeries := by
  have hstage : ∀ N,
      PowerSeries.coeff (p ^ n)
          ((𝔾ₐ (R := R)).pTypicalProjectorStage p hunit N γ).toPowerSeries =
        PowerSeries.coeff (p ^ n) γ.toPowerSeries := fun N ↦ by
    induction N with
    | zero => rfl
    | succ m ih =>
      simp only [pTypicalProjectorStage]
      split_ifs with h
      · have hndvd : ¬ m ∣ p ^ n := fun hdvd ↦
          h.2 ((Nat.prime_dvd_prime_iff_eq h.1 hp).mp (h.1.dvd_of_dvd_pow hdvd))
        rw [AddMonoidHom.comp_apply, toPowerSeries_cartierProjectorCurve_𝔾ₐ, map_sub,
          PowerSeries.coeff_expand, ite_eq_right hndvd, sub_zero, ih]
      · exact ih
  rw [(𝔾ₐ (R := R)).coeff_pTypicalProjectorCurve_eq_stage hunit (Nat.lt_succ_self (p ^ n)), hstage]

/-- Over a `ℚ`-algebra, Cartier's `p`-typical projector deletes every formal-logarithm coefficient
outside degrees `p^n`. -/
theorem coeff_subst_pTypicalProjectorCurve_log_eq_zero [Algebra ℚ R] {p k : ℕ}
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R))
    (hk : ∀ n, p ^ n ≠ k) (γ : F.Curve) :
    PowerSeries.coeff k
      (PowerSeries.subst (F.pTypicalProjectorCurve p hunit γ).toPowerSeries F.log) = 0 :=
  (F.isPTypical_pTypicalProjectorCurve p hunit γ).coeff_subst_log_eq_zero hk

/-- Over a `ℚ`-algebra and for a prime `p`, Cartier's `p`-typical projector preserves every
degree-`p^n` formal-logarithm coefficient. -/
theorem coeff_subst_pTypicalProjectorCurve_log_pow [Algebra ℚ R] {p : ℕ} (hp : p.Prime)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R))
    (n : ℕ) (γ : F.Curve) :
    PowerSeries.coeff (p ^ n)
        (PowerSeries.subst (F.pTypicalProjectorCurve p hunit γ).toPowerSeries F.log) =
      PowerSeries.coeff (p ^ n) (PowerSeries.subst γ.toPowerSeries F.log) := by
  simpa only [TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries,
    coeff_pTypicalProjectorCurve_𝔾ₐ_pow hp hunit] using
    congrArg (fun δ : (𝔾ₐ (R := R)).Curve ↦ PowerSeries.coeff (p ^ n) δ.toPowerSeries)
      (F.logHom.mapCurve_pTypicalProjectorCurve p hunit γ)

end Projector

end FormalGroup
