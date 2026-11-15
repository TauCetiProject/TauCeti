/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Prime.Defs
public import TauCeti.RingTheory.FormalGroup.Curve.Projector
import Mathlib.Data.Nat.Prime.Basic
import TauCeti.Algebra.Algebra.NatCast
import TauCeti.Data.Nat.Factorization.Basic
import TauCeti.Data.Nat.Log

/-!
# `p`-typical curves and Cartier's typicalization projector

For a commutative formal group law `F` over a commutative ring `R` and a natural number `p` (in
applications a prime), a curve `γ` on `F` is **`p`-typical** (`FormalGroup.Curve.IsPTypical`) if
Cartier's Frobenius operator `f_q` annihilates `γ` for every prime `q ≠ p`. Equivalently,
`f_n γ = 0` for every nonzero natural number `n` that is not a power of `p`. The `p`-typical
curves form an additive subgroup `FormalGroup.pTypicalCurveSubgroup F p` of `F.Curve`, stable
under all Frobenius operators `f_n` and, when `p` is prime, under Verschiebung operators
`V_{p^k}` of `p`-power index. Over a `ℚ`-algebra with `p` prime, a curve is `p`-typical if and
only if its formal logarithm `log_F(γ(T))` is supported in degrees of the form `p^n`.

When every prime `q ≠ p` is invertible in `R` (for example over `ℤ_(p)`-algebras, `ℚ`-algebras, or
rings of prime characteristic `p`), the elementary Cartier projectors
`FormalGroup.cartierProjectorCurve F q` at primes `q ≠ p` commute pairwise and leave coefficients
below degree `q` unchanged. Their coefficientwise limit defines **Cartier's `p`-typicalization
projector** `FormalGroup.pTypicalProjectorCurve F p hunit : F.Curve →+ F.Curve`, an idempotent
endomorphism projecting `F.Curve` onto the subgroup of `p`-typical curves, commuting with all
elementary Cartier projectors and absorbing those outside powers of `p`, annihilating every
Verschiebung `V_n` whose index `n` is not a power of `p`, and preserving linear coefficients. Over
any commutative ring in which primes `q ≠ p` are invertible (with `p` prime), on the additive
formal group law `𝔾ₐ` it retains precisely the terms of degree `p^n` and zeroes all other degrees;
over a `ℚ`-algebra, the formal logarithm transports the same formula to `log_F(γ(T))`.

## Main definitions

* `FormalGroup.Curve.IsPTypical`: the predicate that a curve `γ` on `F` is annihilated by `f_q`
  for every prime `q ≠ p`.
* `FormalGroup.pTypicalCurveSubgroup`: the additive subgroup of `p`-typical curves in `F.Curve`.
* `FormalGroup.pTypicalProjectorCurve`: Cartier's idempotent projection onto `p`-typical curves
  when all primes `q ≠ p` are units in `R`.

## Main results

* `FormalGroup.Curve.isPTypical_iff_forall_frobeniusCurve_eq_zero`: a curve is `p`-typical if and
  only if `f_n γ = 0` for all `n ≠ 0` not of the form `p^k`.
* `FormalGroup.Curve.isPTypical_iff_forall_coeff_subst_log_eq_zero`: over a `ℚ`-algebra with `p`
  prime, `γ` is `p`-typical if and only if `log_F(γ(T))` vanishes outside degrees `p^n`.
* `FormalGroup.coeff_pTypicalProjectorCurve_eq_self_of_forall_le` and
  `FormalGroup.coeff_one_pTypicalProjectorCurve`: Cartier's projector leaves degree `k` unchanged
  whenever `f_q γ = 0` for all primes `q ≤ k` distinct from `p`, and preserves linear coefficients.
* `FormalGroup.map_pTypicalProjectorCurve` and
  `TauCeti.FormalGroupHom.mapCurve_pTypicalProjectorCurve`: compatibility of Cartier's projector
  with ring base change and homomorphisms of formal group laws.
* `FormalGroup.coeff_toPowerSeries_pTypicalProjectorCurve_𝔾ₐ` and
  `FormalGroup.coeff_subst_pTypicalProjectorCurve_log`: for `p` prime, Cartier's projector retains
  precisely the `p`-power coefficients on `𝔾ₐ` (without `[Algebra ℚ R]`) and on `log_F(γ(T))` over
  `ℚ`-algebras.
* `FormalGroup.isPTypical_pTypicalProjectorCurve`, `FormalGroup.pTypicalProjectorCurve_eq_self_iff`,
  `FormalGroup.isIdempotentElem_pTypicalProjectorCurve`, and
  `FormalGroup.cartierProjectorCurve_pTypicalProjectorCurve`: the image of Cartier's projector is
  `p`-typical, its fixed points are the `p`-typical curves, it is idempotent, and it commutes with
  elementary Cartier projectors while absorbing those outside powers of `p`.

## References

* P. Cartier, *Modules associés à un groupe formel commutatif. Courbes typiques*, C. R. Acad. Sci.
  Paris Sér. A-B 265 (1967), A129–A132.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapter III, §16.
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
operator `f_q` annihilates `γ` for every prime `q ≠ p`. -/
def IsPTypical (γ : F.Curve) (p : ℕ) : Prop :=
  ∀ ⦃q : ℕ⦄ (hq : q.Prime), q ≠ p → F.frobeniusCurve q hq.ne_zero γ = 0

/-- Unfolding characterization of `p`-typical curves. -/
theorem isPTypical_def {γ : F.Curve} {p : ℕ} :
    γ.IsPTypical p ↔ ∀ ⦃q : ℕ⦄ (hq : q.Prime), q ≠ p → F.frobeniusCurve q hq.ne_zero γ = 0 :=
  Iff.rfl

/-- If `γ` is `p`-typical and `n` is divisible by a prime `q ≠ p`, then `f_n γ = 0`. -/
theorem IsPTypical.frobeniusCurve_eq_zero_of_prime_dvd {γ : F.Curve} {p n q : ℕ}
    (hγ : γ.IsPTypical p) (hn : n ≠ 0) (hq : q.Prime) (hqp : q ≠ p) (hqn : q ∣ n) :
    F.frobeniusCurve n hn γ = 0 := by
  obtain ⟨m, rfl⟩ := hqn
  have hm : m ≠ 0 := right_ne_zero_of_mul hn
  rw [F.frobeniusCurve_congr (Nat.mul_comm q m) hn (mul_ne_zero hm hq.ne_zero),
    ← F.frobeniusCurve_frobeniusCurve hm hq.ne_zero, hγ hq hqp, map_zero]

/-- A `p`-typical curve is annihilated by `f_n` for every nonzero `n` not of the form `p^k`. -/
theorem IsPTypical.frobeniusCurve_eq_zero {γ : F.Curve} {p n : ℕ} (hγ : γ.IsPTypical p)
    (hn : n ≠ 0) (hnp : ∀ k, p ^ k ≠ n) :
    F.frobeniusCurve n hn γ = 0 := by
  obtain ⟨q, hq, hqp, hqn⟩ := Nat.exists_prime_ne_and_dvd hnp
  exact hγ.frobeniusCurve_eq_zero_of_prime_dvd hn hq hqp hqn

/-- A curve is `p`-typical if and only if `f_n γ = 0` for every nonzero `n` that is not a power
of `p`. -/
theorem isPTypical_iff_forall_frobeniusCurve_eq_zero {γ : F.Curve} {p : ℕ} :
    γ.IsPTypical p ↔ ∀ ⦃n : ℕ⦄ (hn : n ≠ 0), (∀ k, p ^ k ≠ n) → F.frobeniusCurve n hn γ = 0 := by
  refine ⟨fun hγ _ hn hnp ↦ hγ.frobeniusCurve_eq_zero hn hnp, fun h q hq hqp ↦ ?_⟩
  refine h hq.ne_zero fun k hpk ↦ hqp ?_
  have hk1 : k = 1 := Nat.Prime.eq_one_of_pow (hpk ▸ hq)
  simpa [hk1] using hpk.symm

/-- A `p`-typical curve is annihilated by `f_n` for every `n > 1` coprime to `p`. -/
theorem IsPTypical.frobeniusCurve_eq_zero_of_coprime {γ : F.Curve} {p n : ℕ}
    (hγ : γ.IsPTypical p) (hn0 : n ≠ 0) (hn1 : n ≠ 1) (hcop : p.Coprime n) :
    F.frobeniusCurve n hn0 γ = 0 := by
  refine hγ.frobeniusCurve_eq_zero hn0 ?_
  rintro (_ | k) rfl
  · exact hn1 rfl
  · rcases eq_or_ne p 1 with rfl | hp1
    · exact hn1 (one_pow _)
    · exact hp1 (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl (dvd_pow_self p (Nat.succ_ne_zero k)))

/-- The zero curve is `p`-typical. -/
@[simp]
theorem isPTypical_zero (p : ℕ) : (0 : F.Curve).IsPTypical p :=
  fun _ _ _ ↦ map_zero _

/-- Sums of `p`-typical curves are `p`-typical. -/
theorem IsPTypical.add {γ δ : F.Curve} {p : ℕ} (hγ : γ.IsPTypical p) (hδ : δ.IsPTypical p) :
    (γ + δ).IsPTypical p :=
  fun q hq hqp ↦ by rw [map_add, hγ hq hqp, hδ hq hqp, _root_.add_zero]

/-- Negatives of `p`-typical curves are `p`-typical. -/
theorem IsPTypical.neg {γ : F.Curve} {p : ℕ} (hγ : γ.IsPTypical p) : (-γ).IsPTypical p :=
  fun q hq hqp ↦ by rw [map_neg, hγ hq hqp, _root_.neg_zero]

/-- Negation preserves and reflects `p`-typicality of curves. -/
@[simp]
theorem isPTypical_neg_iff {γ : F.Curve} {p : ℕ} : (-γ).IsPTypical p ↔ γ.IsPTypical p :=
  ⟨fun h ↦ neg_neg γ ▸ h.neg, IsPTypical.neg⟩

/-- Differences of `p`-typical curves are `p`-typical. -/
theorem IsPTypical.sub {γ δ : F.Curve} {p : ℕ} (hγ : γ.IsPTypical p) (hδ : δ.IsPTypical p) :
    (γ - δ).IsPTypical p :=
  fun q hq hqp ↦ by rw [map_sub, hγ hq hqp, hδ hq hqp, _root_.sub_zero]

/-- Natural-number multiples of `p`-typical curves are `p`-typical. -/
theorem IsPTypical.nsmul {γ : F.Curve} {p : ℕ} (n : ℕ) (hγ : γ.IsPTypical p) :
    (n • γ).IsPTypical p :=
  fun q hq hqp ↦ by rw [map_nsmul, hγ hq hqp, smul_zero]

/-- Integer multiples of `p`-typical curves are `p`-typical. -/
theorem IsPTypical.zsmul {γ : F.Curve} {p : ℕ} (n : ℤ) (hγ : γ.IsPTypical p) :
    (n • γ).IsPTypical p :=
  fun q hq hqp ↦ by rw [map_zsmul, hγ hq hqp, smul_zero]

/-- Every Frobenius operator `f_n` preserves `p`-typicality. -/
theorem IsPTypical.frobeniusCurve {γ : F.Curve} {p : ℕ} (hγ : γ.IsPTypical p) (n : ℕ)
    (hn : n ≠ 0) : (F.frobeniusCurve n hn γ).IsPTypical p := by
  intro q hq hqp
  rw [F.frobeniusCurve_frobeniusCurve hq.ne_zero hn,
    F.frobeniusCurve_congr (Nat.mul_comm q n) _ (mul_ne_zero hn hq.ne_zero),
    ← F.frobeniusCurve_frobeniusCurve hn hq.ne_zero, hγ hq hqp, map_zero]

/-- For a prime `p`, `p`-power Verschiebung operators `V_{p^k}` preserve `p`-typicality. -/
theorem IsPTypical.verschiebungCurve_pow {γ : F.Curve} {p : ℕ} (hp : p.Prime) (k : ℕ)
    (hγ : γ.IsPTypical p) :
    (F.verschiebungCurve (p ^ k) (pow_ne_zero k hp.ne_zero) γ).IsPTypical p := by
  intro q hq hqp
  have hcop : q.Coprime (p ^ k) := ((Nat.coprime_primes hq hp).mpr hqp).pow_right k
  rw [F.frobeniusCurve_verschiebungCurve_of_coprime hq.ne_zero (pow_ne_zero k hp.ne_zero) hcop,
    hγ hq hqp, map_zero]

/-- Base change preserves `p`-typicality of curves. -/
theorem IsPTypical.map (φ : R →+* S) {γ : F.Curve} {p : ℕ} (hγ : γ.IsPTypical p) :
    (Curve.map φ γ).IsPTypical p := by
  intro q hq hqp
  rw [← F.map_frobeniusCurve φ q hq.ne_zero γ, hγ hq hqp, map_zero]

/-- Along an injective ring homomorphism, base change reflects and preserves `p`-typicality. -/
theorem isPTypical_map_iff_of_injective {φ : R →+* S} (hφ : Function.Injective φ)
    {γ : F.Curve} {p : ℕ} :
    (Curve.map φ γ).IsPTypical p ↔ γ.IsPTypical p := by
  refine ⟨fun h q hq hqp ↦ Curve.map_injective hφ ?_, IsPTypical.map φ⟩
  rw [F.map_frobeniusCurve φ q hq.ne_zero γ, h hq hqp, map_zero]

/-- Over a `ℚ`-algebra, the formal logarithm of a `p`-typical curve vanishes outside degrees of
the form `p^n`. -/
theorem IsPTypical.coeff_subst_log_eq_zero [Algebra ℚ R] {γ : F.Curve} {p : ℕ}
    (hγ : γ.IsPTypical p) {k : ℕ} (hk : ∀ n, p ^ n ≠ k) :
    PowerSeries.coeff k (PowerSeries.subst γ.toPowerSeries F.log) = 0 := by
  rcases eq_or_ne k 0 with rfl | hk0
  · simpa using (F.logHom.mapCurve γ).coeff_zero_toPowerSeries
  · obtain ⟨q, hq, hqp, m, rfl⟩ := Nat.exists_prime_ne_and_dvd hk
    have hlog := congrArg (PowerSeries.coeff m) (F.subst_frobeniusCurve_log q hq.ne_zero γ)
    rw [hγ hq hqp, Curve.toPowerSeries_zero, PowerSeries.subst_zero_of_constantCoeff_zero
      F.constantCoeff_log, map_zero, PowerSeries.coeff_smul, PowerSeries.coeff_cartier,
      Nat.add_zero, smul_eq_mul] at hlog
    exact (TauCeti.isUnit_natCast_of_ne_zero (K := R) hq.ne_zero).mul_right_eq_zero.mp hlog.symm

/-- Over a `ℚ`-algebra, for `p` prime, a curve `γ` is `p`-typical if and only if `log_F(γ(T))`
has no nonzero terms outside the degrees `p^n`. -/
theorem isPTypical_iff_forall_coeff_subst_log_eq_zero [Algebra ℚ R] {γ : F.Curve} {p : ℕ}
    (hp : p.Prime) :
    γ.IsPTypical p ↔
      ∀ k, (∀ n, p ^ n ≠ k) →
        PowerSeries.coeff k (PowerSeries.subst γ.toPowerSeries F.log) = 0 := by
  refine ⟨fun hγ k hk ↦ hγ.coeff_subst_log_eq_zero hk, fun hlog q hq hqp ↦ ?_⟩
  apply F.logIso.curveEquiv.injective
  rw [map_zero]
  ext m
  simp only [TauCeti.FormalGroupIso.curveEquiv_apply, logIso_toHom,
    TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries,
    subst_frobeniusCurve_log, Curve.toPowerSeries_zero, map_zero,
    PowerSeries.coeff_smul, PowerSeries.coeff_cartier, Nat.add_zero, smul_eq_mul]
  rw [hlog (q * m) fun n hpn ↦
      hqp (Nat.prime_eq_prime_of_dvd_pow hq hp (hpn ▸ dvd_mul_right q m)),
    mul_zero]

end IsPTypical

end Curve

/-- Formal-group homomorphisms preserve `p`-typicality of curves. -/
theorem _root_.TauCeti.FormalGroupHom.isPTypical_mapCurve {F G : FormalGroup R}
    [F.IsComm] [G.IsComm] (f : TauCeti.FormalGroupHom F G) {γ : F.Curve} {p : ℕ}
    (hγ : γ.IsPTypical p) :
    (f.mapCurve γ).IsPTypical p := by
  intro q hq hqp
  rw [← f.mapCurve_frobeniusCurve q hq.ne_zero γ, hγ hq hqp, map_zero]

/-- The forward homomorphism of an isomorphism of formal group laws preserves and reflects
`p`-typicality of curves. -/
@[simp]
theorem _root_.TauCeti.FormalGroupIso.isPTypical_toHom_mapCurve_iff {F G : FormalGroup R}
    [F.IsComm] [G.IsComm] (e : TauCeti.FormalGroupIso F G) (γ : F.Curve) (p : ℕ) :
    (e.toHom.mapCurve γ).IsPTypical p ↔ γ.IsPTypical p := by
  refine ⟨fun h ↦ ?_, e.toHom.isPTypical_mapCurve⟩
  have h' := e.invHom.isPTypical_mapCurve h
  rwa [← TauCeti.FormalGroupHom.comp_mapCurve, e.invHom_comp_toHom,
    TauCeti.FormalGroupHom.id_mapCurve] at h'

/-- The inverse homomorphism of an isomorphism of formal group laws preserves and reflects
`p`-typicality of curves. -/
@[simp]
theorem _root_.TauCeti.FormalGroupIso.isPTypical_invHom_mapCurve_iff {F G : FormalGroup R}
    [F.IsComm] [G.IsComm] (e : TauCeti.FormalGroupIso F G) (γ : G.Curve) (p : ℕ) :
    (e.invHom.mapCurve γ).IsPTypical p ↔ γ.IsPTypical p :=
  e.symm_toHom ▸ e.symm.isPTypical_toHom_mapCurve_iff γ p

/-- Formal-group isomorphisms preserve and reflect `p`-typicality of curves. -/
theorem _root_.TauCeti.FormalGroupIso.isPTypical_curveEquiv_iff {F G : FormalGroup R}
    [F.IsComm] [G.IsComm] (e : TauCeti.FormalGroupIso F G) (γ : F.Curve) (p : ℕ) :
    (e.curveEquiv γ).IsPTypical p ↔ γ.IsPTypical p := by
  rw [TauCeti.FormalGroupIso.curveEquiv_apply, e.isPTypical_toHom_mapCurve_iff]

/-- The additive subgroup of `p`-typical curves on a commutative formal group law `F`. -/
def pTypicalCurveSubgroup (F : FormalGroup R) [F.IsComm] (p : ℕ) : AddSubgroup F.Curve where
  carrier := {γ | γ.IsPTypical p}
  zero_mem' := Curve.isPTypical_zero p
  add_mem' := Curve.IsPTypical.add
  neg_mem' := Curve.IsPTypical.neg

/-- Membership in `F.pTypicalCurveSubgroup p` is `p`-typicality. -/
@[simp]
theorem mem_pTypicalCurveSubgroup_iff (F : FormalGroup R) [F.IsComm] (p : ℕ) (γ : F.Curve) :
    γ ∈ F.pTypicalCurveSubgroup p ↔ γ.IsPTypical p :=
  Iff.rfl

/-! ### Cartier's `p`-typicalization projector -/

section Projector

variable (F : FormalGroup R) [F.IsComm]

/-- Finite-stage approximation to Cartier's `p`-typicalization projector, composing the elementary
Cartier projectors at all primes `q < N` distinct from `p`. -/
private noncomputable def pTypicalProjectorStage (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) : ℕ → F.Curve →+ F.Curve
  | 0 => AddMonoidHom.id F.Curve
  | N + 1 =>
    if h : N.Prime ∧ N ≠ p then
      (F.cartierProjectorCurve N h.1.ne_zero (hunit h.1 h.2)).comp
        (pTypicalProjectorStage p hunit N)
    else
      pTypicalProjectorStage p hunit N

private theorem coeff_pTypicalProjectorStage_eq_of_lt (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) {N M k : ℕ} (hk : k < N)
    (hNM : N ≤ M) (γ : F.Curve) :
    PowerSeries.coeff k (pTypicalProjectorStage F p hunit M γ).toPowerSeries =
      PowerSeries.coeff k (pTypicalProjectorStage F p hunit N γ).toPowerSeries := by
  induction hNM with
  | refl => rfl
  | @step m hNm ih =>
    rw [pTypicalProjectorStage]
    split_ifs with h
    · rw [AddMonoidHom.comp_apply, F.coeff_cartierProjectorCurve_of_lt m h.1.ne_zero
        (hunit h.1 h.2) (lt_of_lt_of_le hk hNm), ih]
    · exact ih

private theorem pTypicalProjectorStage_eq_self_of_forall_lt (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) {N : ℕ} {γ : F.Curve}
    (hN : ∀ ⦃q : ℕ⦄ (hq : q.Prime), q < N → q ≠ p → F.frobeniusCurve q hq.ne_zero γ = 0) :
    pTypicalProjectorStage F p hunit N γ = γ := by
  induction N with
  | zero => rfl
  | succ m ih =>
    rw [pTypicalProjectorStage]
    split_ifs with h
    · rw [AddMonoidHom.comp_apply, ih fun _ hq hqm ↦ hN hq (Nat.lt_succ_of_lt hqm)]
      exact F.cartierProjectorCurve_eq_self m h.1.ne_zero (hunit h.1 h.2)
        (hN h.1 (Nat.lt_succ_self m) h.2)
    · exact ih fun _ hq hqm ↦ hN hq (Nat.lt_succ_of_lt hqm)

private theorem map_pTypicalProjectorStage (φ : R →+* S) (p : ℕ)
    (hR : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) (N : ℕ) (γ : F.Curve) :
    Curve.map φ (pTypicalProjectorStage F p hR N γ) =
      pTypicalProjectorStage (F.map φ) p
        (fun _ hq hqp ↦ by simpa using (hR hq hqp).map φ) N (Curve.map φ γ) := by
  induction N with
  | zero => rfl
  | succ m ih =>
    simp only [pTypicalProjectorStage]
    split_ifs with h
    · rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, F.map_cartierProjectorCurve, ih]
    · exact ih

private theorem mapCurve_pTypicalProjectorStage {G : FormalGroup R} [G.IsComm]
    (f : TauCeti.FormalGroupHom F G) (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) (N : ℕ) (γ : F.Curve) :
    f.mapCurve (pTypicalProjectorStage F p hunit N γ) =
      pTypicalProjectorStage G p hunit N (f.mapCurve γ) := by
  induction N with
  | zero => rfl
  | succ m ih =>
    simp only [pTypicalProjectorStage]
    split_ifs with h
    · rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
        f.mapCurve_cartierProjectorCurve, ih]
    · exact ih

/-- **Cartier's `p`-typicalization projector** on curves of a commutative formal group law `F` over
a ring `R` in which every prime `q ≠ p` is a unit. Each degree-`k` coefficient is computed after
applying all elementary Cartier projectors at primes `q ≤ k` distinct from `p`, beyond which further
factors leave degree `k` unchanged. -/
noncomputable def pTypicalProjectorCurve (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) : F.Curve →+ F.Curve where
  toFun γ :=
    { toPowerSeries := PowerSeries.mk fun k ↦
        PowerSeries.coeff k (pTypicalProjectorStage F p hunit (k + 1) γ).toPowerSeries
      constantCoeff_toPowerSeries := by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk,
          Curve.coeff_zero_toPowerSeries] }
  map_zero' := Curve.ext <| PowerSeries.ext fun k ↦ by
    simp only [PowerSeries.coeff_mk, map_zero, Curve.toPowerSeries_zero]
  map_add' γ₁ γ₂ := Curve.ext <| PowerSeries.ext fun k ↦ by
    have hle (δ : F.Curve) (i : ℕ) (hi : i ≤ k) :
        PowerSeries.coeff i (PowerSeries.mk fun m ↦
          PowerSeries.coeff m (pTypicalProjectorStage F p hunit (m + 1) δ).toPowerSeries) =
          PowerSeries.coeff i (pTypicalProjectorStage F p hunit (k + 1) δ).toPowerSeries := by
      rw [PowerSeries.coeff_mk]
      exact (coeff_pTypicalProjectorStage_eq_of_lt F p hunit (Nat.lt_succ_self i)
        (Nat.succ_le_succ hi) δ).symm
    rw [PowerSeries.coeff_mk, map_add]
    exact (Curve.coeff_add_congr (hle γ₁) (hle γ₂)).symm

private theorem coeff_pTypicalProjectorCurve_eq_stage (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) {N k : ℕ} (hk : k < N)
    (γ : F.Curve) :
    PowerSeries.coeff k (F.pTypicalProjectorCurve p hunit γ).toPowerSeries =
      PowerSeries.coeff k (pTypicalProjectorStage F p hunit N γ).toPowerSeries := by
  dsimp only [pTypicalProjectorCurve, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [PowerSeries.coeff_mk]
  exact (coeff_pTypicalProjectorStage_eq_of_lt F p hunit (Nat.lt_succ_self k) hk γ).symm

private theorem coeff_subst_pTypicalProjectorCurve_eq_stage (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) (f : PowerSeries R) (k : ℕ)
    (γ : F.Curve) :
    PowerSeries.coeff k
      (PowerSeries.subst (F.pTypicalProjectorCurve p hunit γ).toPowerSeries f) =
      PowerSeries.coeff k
        (PowerSeries.subst (pTypicalProjectorStage F p hunit (k + 1) γ).toPowerSeries f) := by
  have hdvd : PowerSeries.X ^ (k + 1) ∣
      (F.pTypicalProjectorCurve p hunit γ).toPowerSeries -
        (pTypicalProjectorStage F p hunit (k + 1) γ).toPowerSeries :=
    PowerSeries.X_pow_dvd_iff.mpr fun i hi ↦ by
      rw [map_sub, coeff_pTypicalProjectorCurve_eq_stage F p hunit hi γ, sub_self]
  have hsub := PowerSeries.X_pow_dvd_subst_sub_subst
    (F.pTypicalProjectorCurve p hunit γ).constantCoeff_toPowerSeries hdvd f
  exact sub_eq_zero.mp (by
    simpa only [map_sub] using PowerSeries.X_pow_dvd_iff.mp hsub k (Nat.lt_succ_self k))

/-- Cartier's `p`-typicalization projector leaves the degree-`k` coefficient of `γ` unchanged
whenever `f_q γ = 0` for all primes `q ≤ k` distinct from `p`. -/
theorem coeff_pTypicalProjectorCurve_eq_self_of_forall_le (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) {k : ℕ} {γ : F.Curve}
    (hk : ∀ ⦃q : ℕ⦄ (hq : q.Prime), q ≤ k → q ≠ p → F.frobeniusCurve q hq.ne_zero γ = 0) :
    PowerSeries.coeff k (F.pTypicalProjectorCurve p hunit γ).toPowerSeries =
      PowerSeries.coeff k γ.toPowerSeries := by
  rw [coeff_pTypicalProjectorCurve_eq_stage F p hunit (Nat.lt_succ_self k),
    pTypicalProjectorStage_eq_self_of_forall_lt F p hunit
      (fun _ hq hqk ↦ hk hq (Nat.lt_succ_iff.mp hqk))]

/-- Cartier's `p`-typicalization projector leaves unchanged every coefficient of degree strictly
below all primes `q ≠ p`. -/
theorem coeff_pTypicalProjectorCurve_of_forall_prime_ne (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) {k : ℕ}
    (hk : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → k < q) (γ : F.Curve) :
    PowerSeries.coeff k (F.pTypicalProjectorCurve p hunit γ).toPowerSeries =
      PowerSeries.coeff k γ.toPowerSeries :=
  F.coeff_pTypicalProjectorCurve_eq_self_of_forall_le p hunit fun _ hq hqk hqp ↦
    absurd hqk (not_le.mpr (hk hq hqp))

/-- Cartier's `p`-typicalization projector preserves the linear coefficient of every curve. -/
@[simp]
theorem coeff_one_pTypicalProjectorCurve (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    PowerSeries.coeff 1 (F.pTypicalProjectorCurve p hunit γ).toPowerSeries =
      PowerSeries.coeff 1 γ.toPowerSeries :=
  F.coeff_pTypicalProjectorCurve_of_forall_prime_ne p hunit (fun _ hq _ ↦ hq.one_lt) γ

/-- Base change commutes with Cartier's `p`-typicalization projector. -/
theorem map_pTypicalProjectorCurve (φ : R →+* S) (p : ℕ)
    (hR : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    Curve.map φ (F.pTypicalProjectorCurve p hR γ) =
      (F.map φ).pTypicalProjectorCurve p
        (fun _ hq hqp ↦ by simpa using (hR hq hqp).map φ) (Curve.map φ γ) := by
  ext k
  rw [Curve.toPowerSeries_map, PowerSeries.coeff_map,
    coeff_pTypicalProjectorCurve_eq_stage F p hR (Nat.lt_succ_self k),
    coeff_pTypicalProjectorCurve_eq_stage (F.map φ) p _ (Nat.lt_succ_self k),
    ← PowerSeries.coeff_map, ← Curve.toPowerSeries_map, map_pTypicalProjectorStage]

/-- Formal-group homomorphisms commute with Cartier's `p`-typicalization projector. -/
theorem _root_.TauCeti.FormalGroupHom.mapCurve_pTypicalProjectorCurve {F G : FormalGroup R}
    [F.IsComm] [G.IsComm] (f : TauCeti.FormalGroupHom F G) (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    f.mapCurve (F.pTypicalProjectorCurve p hunit γ) =
      G.pTypicalProjectorCurve p hunit (f.mapCurve γ) := by
  ext k
  rw [TauCeti.FormalGroupHom.toPowerSeries_mapCurve,
    coeff_subst_pTypicalProjectorCurve_eq_stage F p hunit f.toPowerSeries k γ,
    ← TauCeti.FormalGroupHom.toPowerSeries_mapCurve,
    mapCurve_pTypicalProjectorStage F f p hunit (k + 1) γ,
    ← coeff_pTypicalProjectorCurve_eq_stage G p hunit (Nat.lt_succ_self k)]

end Projector

section AdditiveProjector

private theorem coeff_toPowerSeries_cartierProjectorCurve_𝔾ₐ (n : ℕ) (hn : n ≠ 0)
    (hunit : IsUnit (n : R)) (k : ℕ) (γ : (𝔾ₐ (R := R)).Curve) :
    PowerSeries.coeff k ((𝔾ₐ (R := R)).cartierProjectorCurve n hn hunit γ).toPowerSeries =
      if n ∣ k then 0 else PowerSeries.coeff k γ.toPowerSeries := by
  rw [toPowerSeries_cartierProjectorCurve_𝔾ₐ, map_sub, PowerSeries.coeff_expand]
  split_ifs with hdvd
  · rw [PowerSeries.coeff_cartier, Nat.add_zero, Nat.mul_div_cancel' hdvd, sub_self]
  · rw [sub_zero]

private theorem coeff_toPowerSeries_pTypicalProjectorStage_𝔾ₐ_eq_zero (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) {N k q : ℕ} (hqN : q < N)
    (hq : q.Prime) (hqp : q ≠ p) (hqk : q ∣ k) (γ : (𝔾ₐ (R := R)).Curve) :
    PowerSeries.coeff k
      (pTypicalProjectorStage (𝔾ₐ (R := R)) p hunit N γ).toPowerSeries = 0 := by
  induction N with
  | zero => exact absurd hqN (Nat.not_lt_zero q)
  | succ m ih =>
    rw [pTypicalProjectorStage]
    split_ifs with hm
    · rw [AddMonoidHom.comp_apply, coeff_toPowerSeries_cartierProjectorCurve_𝔾ₐ]
      split_ifs with hmk
      · rfl
      · rcases eq_or_lt_of_le (Nat.le_of_lt_succ hqN) with rfl | hlt
        · exact absurd hqk hmk
        · exact ih hlt
    · rcases eq_or_lt_of_le (Nat.le_of_lt_succ hqN) with rfl | hlt
      · exact absurd ⟨hq, hqp⟩ hm
      · exact ih hlt

private theorem coeff_toPowerSeries_pTypicalProjectorStage_𝔾ₐ_eq_self (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) (N k : ℕ)
    (hk : ∀ ⦃q : ℕ⦄, q < N → q.Prime → q ≠ p → ¬ q ∣ k) (γ : (𝔾ₐ (R := R)).Curve) :
    PowerSeries.coeff k
      (pTypicalProjectorStage (𝔾ₐ (R := R)) p hunit N γ).toPowerSeries =
      PowerSeries.coeff k γ.toPowerSeries := by
  induction N with
  | zero => rfl
  | succ m ih =>
    rw [pTypicalProjectorStage]
    split_ifs with hm
    · rw [AddMonoidHom.comp_apply, coeff_toPowerSeries_cartierProjectorCurve_𝔾ₐ,
        ite_eq_right (hk (Nat.lt_succ_self m) hm.1 hm.2),
        ih fun _ hqm ↦ hk (Nat.lt_succ_of_lt hqm)]
    · exact ih fun _ hqm ↦ hk (Nat.lt_succ_of_lt hqm)

/-- On the additive formal group law `𝔾ₐ`, Cartier's `p`-typicalization projector deletes every
coefficient whose degree is divisible by a prime `q ≠ p`. -/
theorem coeff_toPowerSeries_pTypicalProjectorCurve_𝔾ₐ_eq_zero_of_prime_dvd {p k q : ℕ}
    (hq : q.Prime) (hqp : q ≠ p) (hqk : q ∣ k)
    (hunit : ∀ ⦃r : ℕ⦄, r.Prime → r ≠ p → IsUnit (r : R)) (γ : (𝔾ₐ (R := R)).Curve) :
    PowerSeries.coeff k ((𝔾ₐ (R := R)).pTypicalProjectorCurve p hunit γ).toPowerSeries = 0 := by
  rcases eq_or_ne k 0 with rfl | hk0
  · exact ((𝔾ₐ (R := R)).pTypicalProjectorCurve p hunit γ).coeff_zero_toPowerSeries
  · rw [coeff_pTypicalProjectorCurve_eq_stage (𝔾ₐ (R := R)) p hunit (Nat.lt_succ_self k)]
    exact coeff_toPowerSeries_pTypicalProjectorStage_𝔾ₐ_eq_zero p hunit
      (Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hqk)) hq hqp hqk γ

/-- On the additive formal group law `𝔾ₐ`, Cartier's `p`-typicalization projector preserves every
coefficient whose degree has no prime factor distinct from `p`. -/
theorem coeff_toPowerSeries_pTypicalProjectorCurve_𝔾ₐ_eq_self (p k : ℕ)
    (hk : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → ¬ q ∣ k)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) (γ : (𝔾ₐ (R := R)).Curve) :
    PowerSeries.coeff k ((𝔾ₐ (R := R)).pTypicalProjectorCurve p hunit γ).toPowerSeries =
      PowerSeries.coeff k γ.toPowerSeries := by
  rw [coeff_pTypicalProjectorCurve_eq_stage (𝔾ₐ (R := R)) p hunit (Nat.lt_succ_self k)]
  exact coeff_toPowerSeries_pTypicalProjectorStage_𝔾ₐ_eq_self p hunit (k + 1) k
    (fun _ _ hq hqp ↦ hk hq hqp) γ

/-- On the additive formal group law `𝔾ₐ`, Cartier's `p`-typicalization projector annihilates every
coefficient outside the degrees `p^n`. -/
theorem coeff_toPowerSeries_pTypicalProjectorCurve_𝔾ₐ_eq_zero {p k : ℕ}
    (hk : ∀ n, p ^ n ≠ k) (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R))
    (γ : (𝔾ₐ (R := R)).Curve) :
    PowerSeries.coeff k ((𝔾ₐ (R := R)).pTypicalProjectorCurve p hunit γ).toPowerSeries = 0 := by
  obtain ⟨q, hq, hqp, hqk⟩ := Nat.exists_prime_ne_and_dvd hk
  exact coeff_toPowerSeries_pTypicalProjectorCurve_𝔾ₐ_eq_zero_of_prime_dvd hq hqp hqk hunit γ

/-- On the additive formal group law `𝔾ₐ`, for `p` prime, Cartier's `p`-typicalization projector
retains precisely the `p`-power coefficients of `γ` and zeroes all other degrees. -/
theorem coeff_toPowerSeries_pTypicalProjectorCurve_𝔾ₐ {p : ℕ} (hp : p.Prime)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) (k : ℕ)
    (γ : (𝔾ₐ (R := R)).Curve) :
    PowerSeries.coeff k ((𝔾ₐ (R := R)).pTypicalProjectorCurve p hunit γ).toPowerSeries =
      if p ^ Nat.log p k = k then PowerSeries.coeff k γ.toPowerSeries else 0 := by
  split_ifs with hpow
  · exact coeff_toPowerSeries_pTypicalProjectorCurve_𝔾ₐ_eq_self p k
      (fun q hq hqp hqk ↦ hqp (Nat.prime_eq_prime_of_dvd_pow hq hp (hpow.symm ▸ hqk))) hunit γ
  · exact coeff_toPowerSeries_pTypicalProjectorCurve_𝔾ₐ_eq_zero
      (fun n hn ↦ hpow (by rw [← hn, Nat.log_pow hp.one_lt])) hunit γ

/-- On the additive formal group law `𝔾ₐ`, for `p` prime, Cartier's `p`-typicalization projector
preserves the degree-`p^n` coefficient of `γ`. -/
@[simp]
theorem coeff_toPowerSeries_pTypicalProjectorCurve_𝔾ₐ_pow {p : ℕ} (hp : p.Prime)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) (n : ℕ)
    (γ : (𝔾ₐ (R := R)).Curve) :
    PowerSeries.coeff (p ^ n) ((𝔾ₐ (R := R)).pTypicalProjectorCurve p hunit γ).toPowerSeries =
      PowerSeries.coeff (p ^ n) γ.toPowerSeries := by
  rw [coeff_toPowerSeries_pTypicalProjectorCurve_𝔾ₐ hp hunit (p ^ n) γ,
    ite_eq_left (by rw [Nat.log_pow hp.one_lt])]

end AdditiveProjector

section ProjectorProperties

variable (F : FormalGroup R) [F.IsComm]

/-- Over a `ℚ`-algebra, the formal logarithm linearises Cartier's `p`-typicalization projector into
the `p`-typicalization projector on `𝔾ₐ`. -/
theorem subst_pTypicalProjectorCurve_log [Algebra ℚ R] (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    PowerSeries.subst (F.pTypicalProjectorCurve p hunit γ).toPowerSeries F.log =
      ((𝔾ₐ (R := R)).pTypicalProjectorCurve p hunit (F.logHom.mapCurve γ)).toPowerSeries := by
  simpa only [TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries] using
    congrArg Curve.toPowerSeries (F.logHom.mapCurve_pTypicalProjectorCurve p hunit γ)

/-- Over a `ℚ`-algebra, Cartier's `p`-typicalization projector deletes from `log_F(γ(T))` every
degree divisible by a prime `q ≠ p`. -/
theorem coeff_subst_pTypicalProjectorCurve_log_eq_zero_of_prime_dvd [Algebra ℚ R] {p k q : ℕ}
    (hq : q.Prime) (hqp : q ≠ p) (hqk : q ∣ k)
    (hunit : ∀ ⦃r : ℕ⦄, r.Prime → r ≠ p → IsUnit (r : R)) (γ : F.Curve) :
    PowerSeries.coeff k
      (PowerSeries.subst (F.pTypicalProjectorCurve p hunit γ).toPowerSeries F.log) = 0 := by
  rw [F.subst_pTypicalProjectorCurve_log,
    coeff_toPowerSeries_pTypicalProjectorCurve_𝔾ₐ_eq_zero_of_prime_dvd hq hqp hqk]

/-- Over a `ℚ`-algebra, Cartier's `p`-typicalization projector preserves every coefficient of
`log_F(γ(T))` whose degree has no prime factor distinct from `p`. -/
theorem coeff_subst_pTypicalProjectorCurve_log_eq_self [Algebra ℚ R] (p k : ℕ)
    (hk : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → ¬ q ∣ k)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    PowerSeries.coeff k
      (PowerSeries.subst (F.pTypicalProjectorCurve p hunit γ).toPowerSeries F.log) =
      PowerSeries.coeff k (PowerSeries.subst γ.toPowerSeries F.log) := by
  rw [F.subst_pTypicalProjectorCurve_log,
    coeff_toPowerSeries_pTypicalProjectorCurve_𝔾ₐ_eq_self p k hk,
    TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries]

/-- Over a `ℚ`-algebra, for `p` prime, Cartier's `p`-typicalization projector retains precisely the
`p`-power coefficients of `log_F(γ(T))` and zeroes all other degrees. -/
theorem coeff_subst_pTypicalProjectorCurve_log [Algebra ℚ R] {p : ℕ} (hp : p.Prime)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) (k : ℕ) (γ : F.Curve) :
    PowerSeries.coeff k
      (PowerSeries.subst (F.pTypicalProjectorCurve p hunit γ).toPowerSeries F.log) =
      if p ^ Nat.log p k = k then
        PowerSeries.coeff k (PowerSeries.subst γ.toPowerSeries F.log)
      else 0 := by
  rw [F.subst_pTypicalProjectorCurve_log, coeff_toPowerSeries_pTypicalProjectorCurve_𝔾ₐ hp,
    TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries]

/-- Over a `ℚ`-algebra, for `p` prime, Cartier's `p`-typicalization projector preserves the degree
`p^n` coefficient of `log_F(γ(T))`. -/
@[simp]
theorem coeff_subst_pTypicalProjectorCurve_log_pow [Algebra ℚ R] {p : ℕ} (hp : p.Prime)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) (n : ℕ) (γ : F.Curve) :
    PowerSeries.coeff (p ^ n)
      (PowerSeries.subst (F.pTypicalProjectorCurve p hunit γ).toPowerSeries F.log) =
      PowerSeries.coeff (p ^ n) (PowerSeries.subst γ.toPowerSeries F.log) := by
  rw [F.subst_pTypicalProjectorCurve_log, coeff_toPowerSeries_pTypicalProjectorCurve_𝔾ₐ_pow hp,
    TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries]

/-- Over a `ℚ`-algebra, Cartier's `p`-typicalization projector annihilates every coefficient of
`log_F(γ(T))` outside the degrees `p^n`. -/
theorem coeff_subst_pTypicalProjectorCurve_log_eq_zero [Algebra ℚ R] {p k : ℕ}
    (hk : ∀ n, p ^ n ≠ k) (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    PowerSeries.coeff k
      (PowerSeries.subst (F.pTypicalProjectorCurve p hunit γ).toPowerSeries F.log) = 0 := by
  rw [F.subst_pTypicalProjectorCurve_log,
    coeff_toPowerSeries_pTypicalProjectorCurve_𝔾ₐ_eq_zero hk]

/-- For every prime `q ≠ p`, Frobenius `f_q` annihilates the image of Cartier's `p`-typicalization
projector. -/
@[simp]
theorem frobeniusCurve_pTypicalProjectorCurve {p q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (hunit : ∀ ⦃r : ℕ⦄, r.Prime → r ≠ p → IsUnit (r : R)) (γ : F.Curve) :
    F.frobeniusCurve q hq.ne_zero (F.pTypicalProjectorCurve p hunit γ) = 0 :=
  Curve.eq_of_forall_ratAlgebra F γ {r : ℕ | r.Prime ∧ r ≠ p}
    (fun _ hr ↦ hunit hr.1 hr.2)
    (fun G _ hB δ ↦ G.frobeniusCurve q hq.ne_zero
      (G.pTypicalProjectorCurve p (fun _ hr hrp ↦ hB _ ⟨hr, hrp⟩) δ))
    (fun _ _ _ _ ↦ 0)
    (fun G _ hB δ ↦ by
      apply G.logIso.curveEquiv.injective
      rw [map_zero]
      ext k
      simp only [TauCeti.FormalGroupIso.curveEquiv_apply, logIso_toHom,
        TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries,
        subst_frobeniusCurve_log, Curve.toPowerSeries_zero, map_zero, PowerSeries.coeff_smul,
        PowerSeries.coeff_cartier, Nat.add_zero, smul_eq_mul]
      rw [G.coeff_subst_pTypicalProjectorCurve_log_eq_zero_of_prime_dvd hq hqp
        (dvd_mul_right q k), mul_zero])
    (fun G _ _ _ φ δ ↦ by rw [G.map_frobeniusCurve, G.map_pTypicalProjectorCurve])
    (fun _ _ _ _ φ _ ↦ map_zero (Curve.map φ))
    (fun _ f δ ↦ by rw [f.mapCurve_frobeniusCurve, f.mapCurve_pTypicalProjectorCurve])
    (fun _ f _ ↦ map_zero f.mapCurve)

/-- Every curve in the image of Cartier's `p`-typicalization projector is `p`-typical. -/
@[simp]
theorem isPTypical_pTypicalProjectorCurve (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    (F.pTypicalProjectorCurve p hunit γ).IsPTypical p :=
  fun _ hq hqp ↦ F.frobeniusCurve_pTypicalProjectorCurve hq hqp hunit γ

/-- Every `p`-typical curve is fixed by Cartier's `p`-typicalization projector. -/
theorem pTypicalProjectorCurve_eq_self (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) {γ : F.Curve}
    (hγ : γ.IsPTypical p) :
    F.pTypicalProjectorCurve p hunit γ = γ := by
  ext k
  exact F.coeff_pTypicalProjectorCurve_eq_self_of_forall_le p hunit fun _ hq _ hqp ↦ hγ hq hqp

/-- The fixed points of Cartier's `p`-typicalization projector are precisely the `p`-typical
curves. -/
@[simp]
theorem pTypicalProjectorCurve_eq_self_iff (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    F.pTypicalProjectorCurve p hunit γ = γ ↔ γ.IsPTypical p :=
  ⟨fun h ↦ h ▸ F.isPTypical_pTypicalProjectorCurve p hunit γ,
    F.pTypicalProjectorCurve_eq_self p hunit⟩

/-- Cartier's `p`-typicalization projector is idempotent on curves. -/
@[simp]
theorem pTypicalProjectorCurve_pTypicalProjectorCurve (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    F.pTypicalProjectorCurve p hunit (F.pTypicalProjectorCurve p hunit γ) =
      F.pTypicalProjectorCurve p hunit γ :=
  F.pTypicalProjectorCurve_eq_self p hunit (F.isPTypical_pTypicalProjectorCurve p hunit γ)

/-- Cartier's `p`-typicalization projector is an idempotent in `AddMonoid.End F.Curve`. -/
@[simp]
theorem isIdempotentElem_pTypicalProjectorCurve (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    IsIdempotentElem (M := AddMonoid.End F.Curve) (F.pTypicalProjectorCurve p hunit) :=
  AddMonoidHom.ext (F.pTypicalProjectorCurve_pTypicalProjectorCurve p hunit)

/-- The range of Cartier's `p`-typicalization projector is the subgroup of `p`-typical curves. -/
@[simp]
theorem range_pTypicalProjectorCurve (p : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalProjectorCurve p hunit).range = F.pTypicalCurveSubgroup p := by
  ext γ
  simp only [AddMonoidHom.mem_range, mem_pTypicalCurveSubgroup_iff]
  exact ⟨fun ⟨δ, hδ⟩ ↦ hδ ▸ F.isPTypical_pTypicalProjectorCurve p hunit δ,
    fun hγ ↦ ⟨γ, F.pTypicalProjectorCurve_eq_self p hunit hγ⟩⟩

/-- Cartier's `p`-typicalization projector annihilates `V_n γ` for every nonzero `n` that is not a
power of `p`. -/
theorem pTypicalProjectorCurve_verschiebungCurve {p n : ℕ} (hn : n ≠ 0) (hnp : ∀ k, p ^ k ≠ n)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    F.pTypicalProjectorCurve p hunit (F.verschiebungCurve n hn γ) = 0 := by
  obtain ⟨q, hq, hqp, m, rfl⟩ := Nat.exists_prime_ne_and_dvd hnp
  exact Curve.eq_of_forall_ratAlgebra F γ {r : ℕ | r.Prime ∧ r ≠ p}
    (fun _ hr ↦ hunit hr.1 hr.2)
    (fun G _ hB δ ↦ G.pTypicalProjectorCurve p (fun _ hr hrp ↦ hB _ ⟨hr, hrp⟩)
      (G.verschiebungCurve (q * m) hn δ))
    (fun _ _ _ _ ↦ 0)
    (fun G _ hB δ ↦ by
      apply G.logIso.curveEquiv.injective
      rw [map_zero]
      ext k
      simp only [TauCeti.FormalGroupIso.curveEquiv_apply, logIso_toHom,
        TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries,
        Curve.toPowerSeries_zero, map_zero]
      by_cases hex : ∃ r, r.Prime ∧ r ≠ p ∧ r ∣ k
      · obtain ⟨r, hr, hrp, hrk⟩ := hex
        exact G.coeff_subst_pTypicalProjectorCurve_log_eq_zero_of_prime_dvd hr hrp hrk _ _
      · push Not at hex
        rw [G.coeff_subst_pTypicalProjectorCurve_log_eq_self p k hex,
          subst_verschiebungCurve_log, PowerSeries.coeff_expand,
          ite_eq_right fun hdvd ↦ hex q hq hqp ((dvd_mul_right q m).trans hdvd)])
    (fun G _ _ _ φ δ ↦ by rw [G.map_pTypicalProjectorCurve, G.map_verschiebungCurve])
    (fun _ _ _ _ φ _ ↦ map_zero (Curve.map φ))
    (fun _ f δ ↦ by rw [f.mapCurve_pTypicalProjectorCurve, f.mapCurve_verschiebungCurve])
    (fun _ f _ ↦ map_zero f.mapCurve)

/-- Elementary Cartier projectors commute with Cartier's `p`-typicalization projector at every
nonzero invertible index `n`. -/
theorem cartierProjectorCurve_pTypicalProjectorCurve {p n : ℕ} (hn : n ≠ 0) (hnR : IsUnit (n : R))
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    F.cartierProjectorCurve n hn hnR (F.pTypicalProjectorCurve p hunit γ) =
      F.pTypicalProjectorCurve p hunit (F.cartierProjectorCurve n hn hnR γ) :=
  Curve.eq_of_forall_ratAlgebra F γ (insert n {r : ℕ | r.Prime ∧ r ≠ p})
    (by rintro _ (rfl | ⟨hr, hrp⟩); exacts [hnR, hunit hr hrp])
    (fun G _ hB δ ↦ G.cartierProjectorCurve n hn (hB n (Set.mem_insert _ _))
      (G.pTypicalProjectorCurve p (fun _ hr hrp ↦ hB _ (Set.mem_insert_of_mem _ ⟨hr, hrp⟩)) δ))
    (fun G _ hB δ ↦ G.pTypicalProjectorCurve p
      (fun _ hr hrp ↦ hB _ (Set.mem_insert_of_mem _ ⟨hr, hrp⟩))
      (G.cartierProjectorCurve n hn (hB n (Set.mem_insert _ _)) δ))
    (fun G _ hB δ ↦ by
      apply G.logIso.curveEquiv.injective
      ext k
      simp only [TauCeti.FormalGroupIso.curveEquiv_apply, logIso_toHom,
        TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries,
        G.coeff_subst_cartierProjectorCurve_log]
      by_cases hex : ∃ r, r.Prime ∧ r ≠ p ∧ r ∣ k
      · obtain ⟨r, hr, hrp, hrk⟩ := hex
        rw [G.coeff_subst_pTypicalProjectorCurve_log_eq_zero_of_prime_dvd hr hrp hrk,
          G.coeff_subst_pTypicalProjectorCurve_log_eq_zero_of_prime_dvd hr hrp hrk, ite_self]
      · push Not at hex
        rw [G.coeff_subst_pTypicalProjectorCurve_log_eq_self p k hex,
          G.coeff_subst_pTypicalProjectorCurve_log_eq_self p k hex,
          G.coeff_subst_cartierProjectorCurve_log])
    (fun G _ _ _ φ δ ↦ by rw [G.map_cartierProjectorCurve, G.map_pTypicalProjectorCurve])
    (fun G _ _ _ φ δ ↦ by rw [G.map_pTypicalProjectorCurve, G.map_cartierProjectorCurve])
    (fun _ f δ ↦ by rw [f.mapCurve_cartierProjectorCurve, f.mapCurve_pTypicalProjectorCurve])
    (fun _ f δ ↦ by rw [f.mapCurve_pTypicalProjectorCurve, f.mapCurve_cartierProjectorCurve])

/-- Every elementary Cartier projector whose index is not a power of `p` fixes the image of
Cartier's `p`-typicalization projector. -/
theorem cartierProjectorCurve_pTypicalProjectorCurve_eq_self {p n : ℕ} (hn : n ≠ 0)
    (hnp : ∀ k, p ^ k ≠ n) (hnR : IsUnit (n : R))
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    F.cartierProjectorCurve n hn hnR (F.pTypicalProjectorCurve p hunit γ) =
      F.pTypicalProjectorCurve p hunit γ :=
  F.cartierProjectorCurve_eq_self n hn hnR
    ((F.isPTypical_pTypicalProjectorCurve p hunit γ).frobeniusCurve_eq_zero hn hnp)

/-- For every prime `q ≠ p`, the elementary Cartier projector at `q` fixes the image of Cartier's
`p`-typicalization projector. -/
@[simp]
theorem cartierProjectorCurve_pTypicalProjectorCurve_of_prime {p q : ℕ} (hq : q.Prime)
    (hqp : q ≠ p) (hqR : IsUnit (q : R))
    (hunit : ∀ ⦃r : ℕ⦄, r.Prime → r ≠ p → IsUnit (r : R)) (γ : F.Curve) :
    F.cartierProjectorCurve q hq.ne_zero hqR (F.pTypicalProjectorCurve p hunit γ) =
      F.pTypicalProjectorCurve p hunit γ :=
  F.cartierProjectorCurve_eq_self q hq.ne_zero hqR
    (F.frobeniusCurve_pTypicalProjectorCurve hq hqp hunit γ)

/-- Cartier's `p`-typicalization projector absorbs every precomposed elementary Cartier projector
whose index is not a power of `p`. -/
theorem pTypicalProjectorCurve_cartierProjectorCurve {p n : ℕ} (hn : n ≠ 0)
    (hnp : ∀ k, p ^ k ≠ n) (hnR : IsUnit (n : R))
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    F.pTypicalProjectorCurve p hunit (F.cartierProjectorCurve n hn hnR γ) =
      F.pTypicalProjectorCurve p hunit γ := by
  rw [cartierProjectorCurve_apply, map_sub, F.pTypicalProjectorCurve_verschiebungCurve hn hnp hunit,
    sub_zero]

/-- For every prime `q ≠ p`, Cartier's `p`-typicalization projector absorbs the precomposed
elementary Cartier projector at `q`. -/
@[simp]
theorem pTypicalProjectorCurve_cartierProjectorCurve_of_prime {p q : ℕ} (hq : q.Prime)
    (hqp : q ≠ p) (hqR : IsUnit (q : R))
    (hunit : ∀ ⦃r : ℕ⦄, r.Prime → r ≠ p → IsUnit (r : R)) (γ : F.Curve) :
    F.pTypicalProjectorCurve p hunit (F.cartierProjectorCurve q hq.ne_zero hqR γ) =
      F.pTypicalProjectorCurve p hunit γ := by
  rw [← F.cartierProjectorCurve_pTypicalProjectorCurve hq.ne_zero hqR hunit,
    F.cartierProjectorCurve_pTypicalProjectorCurve_of_prime hq hqp hqR hunit]

/-- For a prime `p`, Cartier's `p`-typicalization projector commutes with `p`-power Verschiebung
operators `V_{p^k}`. -/
theorem pTypicalProjectorCurve_verschiebungCurve_pow {p : ℕ} (hp : p.Prime) (k : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    F.pTypicalProjectorCurve p hunit (F.verschiebungCurve (p ^ k) (pow_ne_zero k hp.ne_zero) γ) =
      F.verschiebungCurve (p ^ k) (pow_ne_zero k hp.ne_zero)
        (F.pTypicalProjectorCurve p hunit γ) :=
  Curve.eq_of_forall_ratAlgebra F γ {r : ℕ | r.Prime ∧ r ≠ p}
    (fun _ hr ↦ hunit hr.1 hr.2)
    (fun G _ hB δ ↦ G.pTypicalProjectorCurve p (fun _ hr hrp ↦ hB _ ⟨hr, hrp⟩)
      (G.verschiebungCurve (p ^ k) (pow_ne_zero k hp.ne_zero) δ))
    (fun G _ hB δ ↦ G.verschiebungCurve (p ^ k) (pow_ne_zero k hp.ne_zero)
      (G.pTypicalProjectorCurve p (fun _ hr hrp ↦ hB _ ⟨hr, hrp⟩) δ))
    (fun G _ hB δ ↦ by
      apply G.logIso.curveEquiv.injective
      ext m
      rw [TauCeti.FormalGroupIso.curveEquiv_apply, TauCeti.FormalGroupIso.curveEquiv_apply,
        logIso_toHom, TauCeti.FormalGroupHom.toPowerSeries_mapCurve,
        TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries,
        G.coeff_subst_pTypicalProjectorCurve_log hp _ m,
        subst_verschiebungCurve_log, subst_verschiebungCurve_log,
        PowerSeries.coeff_expand, PowerSeries.coeff_expand]
      by_cases hdvd : p ^ k ∣ m
      · obtain ⟨u, rfl⟩ := hdvd
        have hpk : p ^ k ∣ p ^ k * u := dvd_mul_right (p ^ k) u
        rw [ite_eq_left hpk, ite_eq_left hpk, Nat.mul_div_cancel_left u (pow_pos hp.pos k),
          G.coeff_subst_pTypicalProjectorCurve_log hp _ u]
        by_cases hu : p ^ Nat.log p u = u
        · rw [ite_eq_left ((Nat.pow_log_mul_eq_iff hp.ne_zero k u).mpr hu), ite_eq_left hu]
        · rw [ite_eq_right (mt (Nat.pow_log_mul_eq_iff hp.ne_zero k u).mp hu), ite_eq_right hu]
      · rw [ite_eq_right hdvd, ite_eq_right hdvd, ite_self])
    (fun G _ _ _ φ δ ↦ by rw [G.map_pTypicalProjectorCurve, G.map_verschiebungCurve])
    (fun G _ _ _ φ δ ↦ by rw [G.map_verschiebungCurve, G.map_pTypicalProjectorCurve])
    (fun _ f δ ↦ by rw [f.mapCurve_pTypicalProjectorCurve, f.mapCurve_verschiebungCurve])
    (fun _ f δ ↦ by rw [f.mapCurve_verschiebungCurve, f.mapCurve_pTypicalProjectorCurve])

/-- For a prime `p`, Cartier's `p`-typicalization projector commutes with `p`-power Frobenius
operators `f_{p^k}`. -/
theorem frobeniusCurve_pow_pTypicalProjectorCurve {p : ℕ} (hp : p.Prime) (k : ℕ)
    (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    F.frobeniusCurve (p ^ k) (pow_ne_zero k hp.ne_zero) (F.pTypicalProjectorCurve p hunit γ) =
      F.pTypicalProjectorCurve p hunit
        (F.frobeniusCurve (p ^ k) (pow_ne_zero k hp.ne_zero) γ) :=
  Curve.eq_of_forall_ratAlgebra F γ {r : ℕ | r.Prime ∧ r ≠ p}
    (fun _ hr ↦ hunit hr.1 hr.2)
    (fun G _ hB δ ↦ G.frobeniusCurve (p ^ k) (pow_ne_zero k hp.ne_zero)
      (G.pTypicalProjectorCurve p (fun _ hr hrp ↦ hB _ ⟨hr, hrp⟩) δ))
    (fun G _ hB δ ↦ G.pTypicalProjectorCurve p (fun _ hr hrp ↦ hB _ ⟨hr, hrp⟩)
      (G.frobeniusCurve (p ^ k) (pow_ne_zero k hp.ne_zero) δ))
    (fun G _ hB δ ↦ by
      apply G.logIso.curveEquiv.injective
      ext m
      simp only [TauCeti.FormalGroupIso.curveEquiv_apply, logIso_toHom,
        TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries,
        subst_frobeniusCurve_log, G.coeff_subst_pTypicalProjectorCurve_log hp,
        PowerSeries.coeff_smul, PowerSeries.coeff_cartier, Nat.add_zero, smul_eq_mul]
      by_cases hm : p ^ Nat.log p m = m
      · rw [ite_eq_left ((Nat.pow_log_mul_eq_iff hp.ne_zero k m).mpr hm), ite_eq_left hm]
      · rw [ite_eq_right (mt (Nat.pow_log_mul_eq_iff hp.ne_zero k m).mp hm),
          ite_eq_right hm, mul_zero])
    (fun G _ _ _ φ δ ↦ by rw [G.map_frobeniusCurve, G.map_pTypicalProjectorCurve])
    (fun G _ _ _ φ δ ↦ by rw [G.map_pTypicalProjectorCurve, G.map_frobeniusCurve])
    (fun _ f δ ↦ by rw [f.mapCurve_frobeniusCurve, f.mapCurve_pTypicalProjectorCurve])
    (fun _ f δ ↦ by rw [f.mapCurve_pTypicalProjectorCurve, f.mapCurve_frobeniusCurve])

end ProjectorProperties

end FormalGroup
