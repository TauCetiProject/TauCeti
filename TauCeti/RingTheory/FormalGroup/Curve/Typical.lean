/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Curve.Projector
import TauCeti.RingTheory.FormalGroup.LazardRing.Polynomial

/-!
# Typical curves and Cartier's infinite typical projector

For a commutative formal group law `F` over a commutative ring `R` and a natural number `p` (in
applications a prime), a curve `γ ∈ F.Curve` is **`p`-typical** (`FormalGroup.Curve.IsTypical`) if
it is annihilated by Cartier's Frobenius operator `f_q` for every prime `q` not dividing `p`,
equivalently by `f_n` for every integer `n > 1` coprime to `p`. Alongside Verschiebung `V_n` and
Frobenius `f_n`, Cartier's homothety operator `FormalGroup.homothetyCurve F r` (`γ(T) ↦ γ(r T)`)
satisfies `[r] ∘ V_n = V_n ∘ [r^n]` and `f_n ∘ [r] = [r^n] ∘ f_n`. The `p`-typical curves form an
additive subgroup `FormalGroup.typicalCurveSubgroup F p` stable under all Frobenius and homothety
operators and under Verschiebung operators whose prime factors divide `p` (in particular `V_p` and
`V_{p^r}`). Over a `ℚ`-algebra, `γ` is `p`-typical precisely when `log_F(γ(T))` is supported in
degrees whose prime factors all divide `p` — for `p` prime, the powers `p^r`.

When every prime `q` not dividing `p` is invertible in `R`, composing the commuting elementary
Cartier projectors `1 - V_q [q]_F⁻¹ f_q` over primes `q ∤ p` stabilizes in degree `k` once all
primes `≤ k` have been applied, because `V_q` vanishes below degree `q`. Taking the coefficientwise
limit defines Cartier's **typical projector** `FormalGroup.typicalProjectorCurve F p hunit`, an
idempotent additive endomorphism of `F.Curve` with image `F.typicalCurveSubgroup p`. It preserves
the linear coefficient `coeff 1`, commutes with ring base change, formal-group homomorphisms, and
curve homotheties `[r]`, annihilates `V_n` and `f_n` at coprime indices `n > 1`, and commutes with
`V_p` and `f_p`. Over a `ℚ`-algebra, its effect on `log_F(γ(T))` is to retain degrees whose prime
factors all divide `p` and delete all other degrees.

## Main definitions

* `FormalGroup.homothetyCurve`: Cartier's homothety operator `[r] : γ(T) ↦ γ(r T)` on `F.Curve`.
* `FormalGroup.Curve.IsTypical`: `p`-typical curves on a commutative formal group law.
* `FormalGroup.typicalCurveSubgroup`: the additive subgroup of `p`-typical curves on `F`.
* `FormalGroup.typicalProjectorCurve`: Cartier's idempotent projection `F.Curve →+ F.Curve` onto
  `p`-typical curves when every prime not dividing `p` is a unit in `R`.

## Main results

* `FormalGroup.homothetyCurve_verschiebungCurve`, `FormalGroup.frobeniusCurve_homothetyCurve`:
  Cartier's commutation relations `[r] ∘ V_n = V_n ∘ [r^n]` and `f_n ∘ [r] = [r^n] ∘ f_n`.
* `FormalGroup.Curve.isTypical_iff_of_prime`, `FormalGroup.Curve.isTypical_iff_forall_coprime`:
  prime and coprime Frobenius characterizations of `p`-typicality.
* `FormalGroup.Curve.isTypical_iff_coeff_subst_log_eq_zero`,
  `FormalGroup.Curve.isTypical_iff_coeff_subst_log_eq_zero_of_prime`: logarithm characterizations
  over `ℚ`-algebras.
* `FormalGroup.map_typicalProjectorCurve`,
  `TauCeti.FormalGroupHom.mapCurve_typicalProjectorCurve`,
  `FormalGroup.typicalProjectorCurve_homothetyCurve`: naturality of the typical projector under
  base change, formal-group homomorphisms, and curve homotheties.
* `FormalGroup.coeff_subst_typicalProjectorCurve_log`: action of the typical projector on the
  formal logarithm over a `ℚ`-algebra.
* `FormalGroup.isTypical_typicalProjectorCurve`, `FormalGroup.typicalProjectorCurve_eq_self_iff`,
  `FormalGroup.typicalProjectorCurve_typicalProjectorCurve`,
  `FormalGroup.range_typicalProjectorCurve`: idempotence and image over arbitrary commutative rings
  via the rational-algebra transfer principle `FormalGroup.Curve.eq_of_forall_ratAlgebra`.
* `FormalGroup.typicalProjectorCurve_verschiebungCurve_of_coprime`,
  `FormalGroup.typicalProjectorCurve_verschiebungCurve_self`,
  `FormalGroup.frobeniusCurve_typicalProjectorCurve_self`: interaction with Cartier's `V_n` and
  `f_n` operators.

## References

* P. Cartier, *Modules associés à un groupe formel commutatif. Courbes typiques*, C. R. Acad. Sci.
  Paris Sér. A-B 265 (1967), A129–A132.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapter III, §16.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Academic Press (1986),
  Appendix A2.1.19–A2.1.25.
-/

public section

namespace FormalGroup

variable {R S : Type*} [CommRing R] [CommRing S]

/-! ### Cartier's homothety operator on curves -/

/-- **Cartier's homothety operator** `[r]` on curves of a formal group law `F`, sending `γ(T)` to
`([r] γ)(T) = γ(r T)` (`PowerSeries.rescale r`). -/
noncomputable def homothetyCurve (F : FormalGroup R) (r : R) : F.Curve →+ F.Curve where
  toFun γ := ⟨PowerSeries.rescale r γ.toPowerSeries, by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale]
    simp⟩
  map_zero' := Curve.ext (by simp)
  map_add' γ₁ γ₂ := Curve.ext <| by
    have ha := PowerSeries.hasSubst_pair γ₁.constantCoeff_toPowerSeries
      γ₂.constantCoeff_toPowerSeries
    simp only [Curve.toPowerSeries_add, PowerSeries.rescale_eq_subst, PowerSeries.subst_def,
      MvPowerSeries.subst_comp_subst_apply ha (PowerSeries.HasSubst.smul_X' r).const]
    congr 1
    exact funext <| Fin.forall_fin_two.mpr ⟨by simp, by simp⟩

/-- The underlying power series of `F.homothetyCurve r γ` is
`PowerSeries.rescale r γ.toPowerSeries`. -/
@[simp]
theorem toPowerSeries_homothetyCurve (F : FormalGroup R) (r : R) (γ : F.Curve) :
    (F.homothetyCurve r γ).toPowerSeries = PowerSeries.rescale r γ.toPowerSeries :=
  (rfl)

/-- Homothety by `1` is the identity on curves. -/
@[simp]
theorem homothetyCurve_one (F : FormalGroup R) (γ : F.Curve) :
    F.homothetyCurve 1 γ = γ :=
  Curve.ext (by simp)

/-- Homothety by `0` sends every curve to `0`. -/
@[simp]
theorem homothetyCurve_zero (F : FormalGroup R) (γ : F.Curve) :
    F.homothetyCurve 0 γ = 0 :=
  Curve.ext <| PowerSeries.ext fun k ↦ by
    rw [toPowerSeries_homothetyCurve, PowerSeries.coeff_rescale, Curve.toPowerSeries_zero,
      map_zero]
    rcases eq_or_ne k 0 with rfl | hk
    · simp
    · rw [zero_pow hk, zero_mul]

/-- Composing curve homotheties multiplies the scalars: `[r] ([s] γ) = [r * s] γ`. -/
theorem homothetyCurve_homothetyCurve (F : FormalGroup R) (r s : R) (γ : F.Curve) :
    F.homothetyCurve r (F.homothetyCurve s γ) = F.homothetyCurve (r * s) γ :=
  Curve.ext <| PowerSeries.ext fun k ↦ by
    simp only [toPowerSeries_homothetyCurve, PowerSeries.coeff_rescale]
    ring

/-- Base change commutes with Cartier's homothety operator on curves. -/
theorem map_homothetyCurve (F : FormalGroup R) (φ : R →+* S) (r : R) (γ : F.Curve) :
    Curve.map φ (F.homothetyCurve r γ) = (F.map φ).homothetyCurve (φ r) (Curve.map φ γ) :=
  Curve.ext <| PowerSeries.ext fun k ↦ by simp [PowerSeries.coeff_rescale]

/-- Formal-group homomorphisms commute with Cartier's homothety operator on curves. -/
theorem _root_.TauCeti.FormalGroupHom.mapCurve_homothetyCurve {F G : FormalGroup R}
    (f : TauCeti.FormalGroupHom F G) (r : R) (γ : F.Curve) :
    f.mapCurve (F.homothetyCurve r γ) = G.homothetyCurve r (f.mapCurve γ) :=
  Curve.ext <| by
    rw [TauCeti.FormalGroupHom.toPowerSeries_mapCurve, toPowerSeries_homothetyCurve,
      toPowerSeries_homothetyCurve, TauCeti.FormalGroupHom.toPowerSeries_mapCurve,
      PowerSeries.rescale_eq_subst, PowerSeries.rescale_eq_subst,
      PowerSeries.subst_comp_subst_apply γ.hasSubst (PowerSeries.HasSubst.smul_X' r)]

/-- Cartier's commutation relation `[r] ∘ V_n = V_n ∘ [r^n]`. -/
theorem homothetyCurve_verschiebungCurve (F : FormalGroup R) (r : R) {n : ℕ} (hn : n ≠ 0)
    (γ : F.Curve) :
    F.homothetyCurve r (F.verschiebungCurve n hn γ) =
      F.verschiebungCurve n hn (F.homothetyCurve (r ^ n) γ) :=
  Curve.ext <| PowerSeries.ext fun k ↦ by
    simp only [toPowerSeries_homothetyCurve, toPowerSeries_verschiebungCurve,
      PowerSeries.coeff_rescale, PowerSeries.coeff_expand]
    split_ifs with hnk
    · obtain ⟨m, rfl⟩ := hnk
      rw [Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hn), pow_mul]
    · exact mul_zero _

private theorem frobeniusCurve_homothetyCurve_ratAlgebra [Algebra ℚ R] (F : FormalGroup R)
    [F.IsComm] (r : R) {n : ℕ} (hn : n ≠ 0) (γ : F.Curve) :
    F.frobeniusCurve n hn (F.homothetyCurve r γ) =
      F.homothetyCurve (r ^ n) (F.frobeniusCurve n hn γ) := by
  have hresc (s : R) (δ : F.Curve) :
      PowerSeries.subst (PowerSeries.rescale s δ.toPowerSeries) F.log =
        PowerSeries.rescale s (PowerSeries.subst δ.toPowerSeries F.log) := by
    rw [PowerSeries.rescale_eq_subst,
      ← PowerSeries.subst_comp_subst_apply δ.hasSubst (PowerSeries.HasSubst.smul_X' s),
      ← PowerSeries.rescale_eq_subst]
  apply F.logIso.curveEquiv.injective
  ext k
  simp only [TauCeti.FormalGroupIso.curveEquiv_apply, logIso_toHom,
    TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries,
    subst_frobeniusCurve_log, toPowerSeries_homothetyCurve, hresc,
    PowerSeries.coeff_smul, PowerSeries.coeff_cartier, Nat.add_zero,
    PowerSeries.coeff_rescale, smul_eq_mul]
  rw [pow_mul]
  ring

/-- Cartier's commutation relation `f_n ∘ [r] = [r^n] ∘ f_n`. -/
theorem frobeniusCurve_homothetyCurve (F : FormalGroup R) [F.IsComm] (r : R) {n : ℕ} (hn : n ≠ 0)
    (γ : F.Curve) :
    F.frobeniusCurve n hn (F.homothetyCurve r γ) =
      F.homothetyCurve (r ^ n) (F.frobeniusCurve n hn γ) := by
  -- Prove the identity for the universal formal group law and curve by embedding into a ℚ-algebra.
  let U : Type := MvPolynomial (Option ℕ) TauCeti.LazardRing
  let Q : Type := MvPolynomial (Option ℕ) (MvPolynomial ℕ+ ℚ)
  let j₀ : TauCeti.LazardRing →+* MvPolynomial ℕ+ ℚ :=
    (MvPolynomial.map (Int.castRingHom ℚ)).comp TauCeti.LazardRing.mvPolynomialEquiv.symm.toRingHom
  have hj₀ : Function.Injective j₀ :=
    (MvPolynomial.map_injective _ Int.cast_injective).comp
      TauCeti.LazardRing.mvPolynomialEquiv.symm.injective
  let j : U →+* Q := MvPolynomial.map j₀
  have hj : Function.Injective j := MvPolynomial.map_injective j₀ hj₀
  let F_U : FormalGroup U := TauCeti.LazardRing.formalGroup.map MvPolynomial.C
  let γ_U : F_U.Curve :=
    ⟨PowerSeries.mk fun k ↦ if k = 0 then 0 else MvPolynomial.X (some k),
      by simp [← PowerSeries.coeff_zero_eq_constantCoeff_apply]⟩
  have hU : F_U.frobeniusCurve n hn (F_U.homothetyCurve (MvPolynomial.X none) γ_U) =
      F_U.homothetyCurve (MvPolynomial.X none ^ n) (F_U.frobeniusCurve n hn γ_U) := by
    refine Curve.map_injective (F := F_U) (φ := j) hj ?_
    rw [F_U.map_frobeniusCurve, F_U.map_homothetyCurve, F_U.map_homothetyCurve,
      F_U.map_frobeniusCurve, map_pow]
    exact frobeniusCurve_homothetyCurve_ratAlgebra (F_U.map j) (j (MvPolynomial.X none)) hn
      (Curve.map j γ_U)
  -- Specialize the universal identity along the evaluation map to `R`.
  let π : U →+* R :=
    MvPolynomial.eval₂Hom (TauCeti.LazardRing.lift ⟨F, inferInstance⟩)
      (fun o : Option ℕ ↦ o.elim r fun k ↦ PowerSeries.coeff k γ.toPowerSeries)
  have hF_U : F_U.map π = F := by
    dsimp only [F_U]
    rw [FormalGroup.map_comp]
    have hC : π.comp MvPolynomial.C = TauCeti.LazardRing.lift ⟨F, inferInstance⟩ :=
      RingHom.ext fun _ ↦ MvPolynomial.eval₂Hom_C _ _ _
    rw [hC, TauCeti.LazardRing.map_lift]
  obtain ⟨e, he⟩ : ∃ e : TauCeti.FormalGroupIso (F_U.map π) F,
      e.toHom.toPowerSeries = PowerSeries.X := hF_U ▸ ⟨.refl _, by simp⟩
  have hγ_U : e.toHom.mapCurve (Curve.map π γ_U) = γ := Curve.ext <| PowerSeries.ext fun k ↦ by
    rw [TauCeti.FormalGroupHom.toPowerSeries_mapCurve, he,
      PowerSeries.subst_X (Curve.map π γ_U).hasSubst, Curve.toPowerSeries_map,
      PowerSeries.coeff_map]
    rcases eq_or_ne k 0 with rfl | hk0
    · simp [γ_U]
    · dsimp only [U, γ_U, π]
      simp [hk0]
  have hmap := congrArg (fun δ ↦ e.toHom.mapCurve (Curve.map π δ)) hU
  have hπX : π (MvPolynomial.X none) = r := MvPolynomial.eval₂Hom_X' _ _ none
  simpa only [F_U.map_frobeniusCurve, F_U.map_homothetyCurve, map_pow, hπX,
    e.toHom.mapCurve_frobeniusCurve, e.toHom.mapCurve_homothetyCurve, hγ_U] using hmap

/-- Elementary Cartier projectors commute with Cartier's homothety operator `[r]`. -/
theorem cartierProjectorCurve_homothetyCurve (F : FormalGroup R) [F.IsComm] (r : R) (n : ℕ)
    (hn : n ≠ 0) (hunit : IsUnit (n : R)) (γ : F.Curve) :
    F.cartierProjectorCurve n hn hunit (F.homothetyCurve r γ) =
      F.homothetyCurve r (F.cartierProjectorCurve n hn hunit γ) := by
  rw [cartierProjectorCurve_apply, cartierProjectorCurve_apply, map_sub,
    F.frobeniusCurve_homothetyCurve,
    ← F.map_nsmulCurveEquiv_symm (F.homothetyCurve (r ^ n)) n hunit hunit,
    ← F.homothetyCurve_verschiebungCurve]

/-! ### Typical curves -/

namespace Curve

section IsTypical

variable {F : FormalGroup R} [F.IsComm]

/-- A curve `γ` on a commutative formal group law `F` is **`p`-typical** if Cartier's Frobenius
operator `f_q` annihilates `γ` for every prime `q` not dividing `p`. -/
def IsTypical (γ : F.Curve) (p : ℕ) : Prop :=
  ∀ (q : ℕ) (hq : q.Prime), ¬ q ∣ p → F.frobeniusCurve q hq.ne_zero γ = 0

/-- Unfold `FormalGroup.Curve.IsTypical`. -/
theorem isTypical_def (γ : F.Curve) (p : ℕ) :
    γ.IsTypical p ↔ ∀ (q : ℕ) (hq : q.Prime), ¬ q ∣ p → F.frobeniusCurve q hq.ne_zero γ = 0 :=
  Iff.rfl

/-- For a prime `p`, a curve is `p`-typical precisely when `f_q γ = 0` for every prime `q ≠ p`. -/
theorem isTypical_iff_of_prime {γ : F.Curve} {p : ℕ} (hp : p.Prime) :
    γ.IsTypical p ↔ ∀ (q : ℕ) (hq : q.Prime), q ≠ p → F.frobeniusCurve q hq.ne_zero γ = 0 := by
  refine forall_congr' fun q ↦ forall_congr' fun hq ↦ ?_
  rw [Nat.prime_dvd_prime_iff_eq hq hp]

/-- A `p`-typical curve is annihilated by `f_n` for every `n > 1` coprime to `p`. -/
theorem IsTypical.frobeniusCurve_eq_zero_of_coprime {γ : F.Curve} {p : ℕ} (hγ : γ.IsTypical p)
    {n : ℕ} (hn : 1 < n) (hcop : n.Coprime p) :
    F.frobeniusCurve n (by omega) γ = 0 := by
  obtain ⟨q, hq, ⟨m, rfl⟩⟩ := Nat.exists_prime_and_dvd hn.ne'
  have hm : m ≠ 0 := by rintro rfl; simp at hn
  have hqp : ¬ q ∣ p := hq.coprime_iff_not_dvd.mp (hcop.coprime_dvd_left ⟨m, rfl⟩)
  rw [F.frobeniusCurve_congr (Nat.mul_comm q m) (by omega) (mul_ne_zero hm hq.ne_zero),
    ← F.frobeniusCurve_frobeniusCurve hm hq.ne_zero, hγ q hq hqp, map_zero]

/-- A curve is `p`-typical iff `f_n γ = 0` for every integer `n > 1` coprime to `p`. -/
theorem isTypical_iff_forall_coprime {γ : F.Curve} {p : ℕ} :
    γ.IsTypical p ↔
      ∀ (n : ℕ) (hn : 1 < n), n.Coprime p → F.frobeniusCurve n (by omega) γ = 0 :=
  ⟨fun hγ _ hn hcop ↦ hγ.frobeniusCurve_eq_zero_of_coprime hn hcop,
    fun h q hq hqp ↦ h q hq.one_lt (hq.coprime_iff_not_dvd.mpr hqp)⟩

/-- The zero curve is `p`-typical. -/
@[simp]
theorem IsTypical.zero (p : ℕ) : (0 : F.Curve).IsTypical p :=
  fun q hq _ ↦ map_zero (F.frobeniusCurve q hq.ne_zero)

/-- Every curve is `0`-typical, since every prime divides `0`. -/
@[simp]
theorem isTypical_zero_right (γ : F.Curve) : γ.IsTypical 0 :=
  fun _ _ hq ↦ absurd (dvd_zero _) hq

/-- Sums of `p`-typical curves are `p`-typical. -/
theorem IsTypical.add {γ δ : F.Curve} {p : ℕ} (hγ : γ.IsTypical p) (hδ : δ.IsTypical p) :
    (γ + δ).IsTypical p :=
  fun q hq hqp ↦ by rw [map_add, hγ q hq hqp, hδ q hq hqp, _root_.add_zero]

/-- Negatives of `p`-typical curves are `p`-typical. -/
theorem IsTypical.neg {γ : F.Curve} {p : ℕ} (hγ : γ.IsTypical p) : (-γ).IsTypical p :=
  fun q hq hqp ↦ by rw [map_neg, hγ q hq hqp, neg_zero]

/-- Negating a curve preserves and reflects `p`-typicality. -/
@[simp]
theorem isTypical_neg_iff {γ : F.Curve} {p : ℕ} : (-γ).IsTypical p ↔ γ.IsTypical p :=
  ⟨fun h ↦ neg_neg γ ▸ h.neg, IsTypical.neg⟩

/-- Differences of `p`-typical curves are `p`-typical. -/
theorem IsTypical.sub {γ δ : F.Curve} {p : ℕ} (hγ : γ.IsTypical p) (hδ : δ.IsTypical p) :
    (γ - δ).IsTypical p :=
  fun q hq hqp ↦ by rw [map_sub, hγ q hq hqp, hδ q hq hqp, sub_zero]

/-- Natural-number multiples of `p`-typical curves are `p`-typical. -/
theorem IsTypical.nsmul {γ : F.Curve} {p : ℕ} (hγ : γ.IsTypical p) (n : ℕ) :
    (n • γ).IsTypical p :=
  fun q hq hqp ↦ by rw [map_nsmul, hγ q hq hqp, smul_zero]

/-- Integer multiples of `p`-typical curves are `p`-typical. -/
theorem IsTypical.zsmul {γ : F.Curve} {p : ℕ} (hγ : γ.IsTypical p) (n : ℤ) :
    (n • γ).IsTypical p :=
  fun q hq hqp ↦ by rw [map_zsmul, hγ q hq hqp, smul_zero]

/-- Frobenius operators of arbitrary nonzero index preserve `p`-typicality. -/
theorem IsTypical.frobeniusCurve {γ : F.Curve} {p : ℕ} (hγ : γ.IsTypical p) {n : ℕ}
    (hn : n ≠ 0) : (F.frobeniusCurve n hn γ).IsTypical p :=
  fun q hq hqp ↦ by
    rw [F.frobeniusCurve_frobeniusCurve,
      F.frobeniusCurve_congr (Nat.mul_comm q n) (mul_ne_zero hq.ne_zero hn)
        (mul_ne_zero hn hq.ne_zero),
      ← F.frobeniusCurve_frobeniusCurve hn hq.ne_zero, hγ q hq hqp, map_zero]

/-- Verschiebung `V_n` preserves and reflects `p`-typicality whenever every prime factor of `n`
divides `p`. -/
theorem isTypical_verschiebungCurve_iff_of_forall_prime_dvd {γ : F.Curve} {p n : ℕ} (hn : n ≠ 0)
    (hdvd : ∀ q : ℕ, q.Prime → q ∣ n → q ∣ p) :
    (F.verschiebungCurve n hn γ).IsTypical p ↔ γ.IsTypical p := by
  refine forall_congr' fun q ↦ forall_congr' fun hq ↦ imp_congr_right fun hqp ↦ ?_
  have hcop : q.Coprime n := hq.coprime_iff_not_dvd.mpr fun hqn ↦ hqp (hdvd q hq hqn)
  rw [F.frobeniusCurve_verschiebungCurve_of_coprime hq.ne_zero hn hcop]
  exact ⟨fun h ↦ F.verschiebungCurve_injective n hn (h.trans (map_zero _).symm),
    fun h ↦ by rw [h, map_zero]⟩

/-- Verschiebung `V_n` preserves `p`-typicality whenever every prime factor of `n` divides `p`. -/
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
theorem IsTypical.verschiebungCurve_self {γ : F.Curve} {p : ℕ} (hγ : γ.IsTypical p)
    (hp : p ≠ 0) : (F.verschiebungCurve p hp γ).IsTypical p :=
  (isTypical_verschiebungCurve_self_iff hp).mpr hγ

/-- Iterated Verschiebung `V_{p^r}` preserves and reflects `p`-typicality for `p ≠ 0`. -/
@[simp]
theorem isTypical_verschiebungCurve_pow_iff {γ : F.Curve} {p : ℕ} (hp : p ≠ 0) (r : ℕ) :
    (F.verschiebungCurve (p ^ r) (pow_ne_zero r hp) γ).IsTypical p ↔ γ.IsTypical p :=
  isTypical_verschiebungCurve_iff_of_forall_prime_dvd (pow_ne_zero r hp)
    fun _ hq hqr ↦ hq.dvd_of_dvd_pow hqr

/-- Iterated Verschiebung `V_{p^r}` preserves `p`-typicality for `p ≠ 0`. -/
theorem IsTypical.verschiebungCurve_pow {γ : F.Curve} {p : ℕ} (hγ : γ.IsTypical p)
    (hp : p ≠ 0) (r : ℕ) : (F.verschiebungCurve (p ^ r) (pow_ne_zero r hp) γ).IsTypical p :=
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
  ⟨fun h q hq hqp ↦ Curve.map_injective hφ <| by
      rw [F.map_frobeniusCurve, h q hq hqp, map_zero],
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
    γ ∈ F.typicalCurveSubgroup p ↔ γ.IsTypical p :=
  Iff.rfl

/-- Formal-group homomorphisms preserve `p`-typicality of curves. -/
theorem _root_.TauCeti.FormalGroupHom.mapCurve_isTypical {F G : FormalGroup R} [F.IsComm]
    [G.IsComm] (f : TauCeti.FormalGroupHom F G) {γ : F.Curve} {p : ℕ} (hγ : γ.IsTypical p) :
    (f.mapCurve γ).IsTypical p :=
  fun q hq hqp ↦ by rw [← f.mapCurve_frobeniusCurve q hq.ne_zero, hγ q hq hqp, map_zero]

/-- The underlying homomorphism of a formal-group isomorphism preserves and reflects
`p`-typicality of curves. -/
@[simp]
theorem _root_.TauCeti.FormalGroupIso.isTypical_toHom_mapCurve_iff {F G : FormalGroup R} [F.IsComm]
    [G.IsComm] (e : TauCeti.FormalGroupIso F G) {γ : F.Curve} {p : ℕ} :
    (e.toHom.mapCurve γ).IsTypical p ↔ γ.IsTypical p :=
  ⟨fun h ↦ by
      have h' := e.invHom.mapCurve_isTypical h
      rwa [← TauCeti.FormalGroupHom.comp_mapCurve, e.invHom_comp_toHom,
        TauCeti.FormalGroupHom.id_mapCurve] at h',
    fun h ↦ e.toHom.mapCurve_isTypical h⟩

/-- Formal-group isomorphisms preserve and reflect `p`-typicality of curves. -/
theorem _root_.TauCeti.FormalGroupIso.isTypical_curveEquiv_iff {F G : FormalGroup R} [F.IsComm]
    [G.IsComm] (e : TauCeti.FormalGroupIso F G) {γ : F.Curve} {p : ℕ} :
    (e.curveEquiv γ).IsTypical p ↔ γ.IsTypical p := by
  rw [TauCeti.FormalGroupIso.curveEquiv_apply, e.isTypical_toHom_mapCurve_iff]

namespace Curve

/-! ### Additive and rational-logarithm characterizations of `p`-typicality -/

/-- On `𝔾ₐ`, any curve supported in degrees whose prime factors divide `p` is `p`-typical. -/
theorem isTypical_𝔾ₐ_of_coeff_eq_zero {γ : (𝔾ₐ (R := R)).Curve} {p : ℕ}
    (hγ : ∀ k : ℕ, (∃ q ∈ k.primeFactors, ¬ q ∣ p) → PowerSeries.coeff k γ.toPowerSeries = 0) :
    γ.IsTypical p := by
  intro q hq hqp
  ext m
  rw [toPowerSeries_frobeniusCurve_𝔾ₐ, PowerSeries.coeff_smul, PowerSeries.coeff_cartier,
    Nat.add_zero, toPowerSeries_zero, map_zero]
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · rw [hγ (q * m) ⟨q, Nat.mem_primeFactors.mpr ⟨hq, dvd_mul_right q m,
      mul_ne_zero hq.ne_zero hm⟩, hqp⟩, smul_zero]

/-- On `𝔾ₐ`, when scalar multiplication by every prime not dividing `p` is regular on `R`, a curve
is `p`-typical iff its coefficients vanish in every degree having a prime factor not dividing
`p`. -/
theorem isTypical_𝔾ₐ_iff {γ : (𝔾ₐ (R := R)).Curve} {p : ℕ}
    (hreg : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsSMulRegular R (q : R)) :
    γ.IsTypical p ↔
      ∀ k : ℕ, (∃ q ∈ k.primeFactors, ¬ q ∣ p) → PowerSeries.coeff k γ.toPowerSeries = 0 := by
  refine ⟨fun hγ k ⟨q, hqk, hqp⟩ ↦ ?_, isTypical_𝔾ₐ_of_coeff_eq_zero⟩
  obtain ⟨hq, ⟨m, rfl⟩, _⟩ := Nat.mem_primeFactors.mp hqk
  apply hreg q hq hqp
  have hm := congrArg (fun δ : (𝔾ₐ (R := R)).Curve ↦ PowerSeries.coeff m δ.toPowerSeries)
    (hγ q hq hqp)
  simpa only [toPowerSeries_frobeniusCurve_𝔾ₐ, PowerSeries.coeff_smul, PowerSeries.coeff_cartier,
    Nat.add_zero, toPowerSeries_zero, map_zero, smul_zero] using hm

/-- Over a `ℚ`-algebra, a curve `γ` on `F` is `p`-typical iff `log_F(γ(T))` has zero coefficient in
every degree divisible by a prime not dividing `p`. -/
theorem isTypical_iff_coeff_subst_log_eq_zero [Algebra ℚ R] {F : FormalGroup R} [F.IsComm]
    {γ : F.Curve} {p : ℕ} :
    γ.IsTypical p ↔ ∀ k : ℕ, (∃ q ∈ k.primeFactors, ¬ q ∣ p) →
      PowerSeries.coeff k (PowerSeries.subst γ.toPowerSeries F.log) = 0 := by
  have hreg : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsSMulRegular R (q : R) := fun q hq _ ↦ by
    have hqQ : IsUnit (q : ℚ) := Ne.isUnit (Nat.cast_ne_zero.mpr hq.ne_zero)
    have hqR : IsUnit (q : R) := by simpa only [map_natCast] using hqQ.map (algebraMap ℚ R)
    exact hqR.isSMulRegular R
  rw [← F.logIso.isTypical_curveEquiv_iff, isTypical_𝔾ₐ_iff hreg]
  simp only [TauCeti.FormalGroupIso.curveEquiv_apply, logIso_toHom,
    TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries]

/-- Over a `ℚ`-algebra, for a prime `p`, a curve `γ` on `F` is `p`-typical iff `log_F(γ(T))` is
supported in the prime-power degrees `p^r`. -/
theorem isTypical_iff_coeff_subst_log_eq_zero_of_prime [Algebra ℚ R] {F : FormalGroup R}
    [F.IsComm] {γ : F.Curve} {p : ℕ} (hp : p.Prime) :
    γ.IsTypical p ↔
      ∀ k : ℕ, (∀ r : ℕ, p ^ r ≠ k) →
        PowerSeries.coeff k (PowerSeries.subst γ.toPowerSeries F.log) = 0 := by
  rw [isTypical_iff_coeff_subst_log_eq_zero]
  constructor
  · intro h k hk
    rcases eq_or_ne k 0 with rfl | hk0
    · have h0 := (F.logHom.mapCurve γ).coeff_zero_toPowerSeries
      rwa [TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries] at h0
    · refine h k ?_
      by_contra! hall
      exact hk k.primeFactorsList.length
        (Nat.eq_prime_pow_of_unique_prime_dvd hk0 fun {q} hq hqk ↦
          (Nat.prime_dvd_prime_iff_eq hq hp).mp
            (hall q (Nat.mem_primeFactors.mpr ⟨hq, hqk, hk0⟩))).symm
  · intro h k ⟨q, hqk, hqp⟩
    obtain ⟨hq, hqdvd, _⟩ := Nat.mem_primeFactors.mp hqk
    exact h k fun r hpow ↦ hqp <| by
      rw [← hpow] at hqdvd
      exact dvd_of_eq ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hqdvd))

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
    else
      typicalProjectorStage p hunit n

private theorem coeff_typicalProjectorStage_succ_of_le (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) {k n : ℕ} (hkn : k ≤ n)
    (γ : F.Curve) :
    PowerSeries.coeff k (F.typicalProjectorStage p hunit (n + 1) γ).toPowerSeries =
      PowerSeries.coeff k (F.typicalProjectorStage p hunit n γ).toPowerSeries := by
  rw [typicalProjectorStage]
  split_ifs with hq
  · exact F.coeff_cartierProjectorCurve_of_lt (n + 1) (Nat.succ_ne_zero n)
      (hunit (n + 1) hq.1 hq.2) (Nat.lt_succ_of_le hkn) _
  · rfl

private theorem coeff_typicalProjectorStage_of_le (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) {k m n : ℕ} (hkm : k ≤ m)
    (hmn : m ≤ n) (γ : F.Curve) :
    PowerSeries.coeff k (F.typicalProjectorStage p hunit n γ).toPowerSeries =
      PowerSeries.coeff k (F.typicalProjectorStage p hunit m γ).toPowerSeries := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
    rw [F.coeff_typicalProjectorStage_succ_of_le p hunit (hkm.trans hmn), ih]

private theorem map_typicalProjectorStage (φ : R →+* S) (p : ℕ)
    (hR : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R))
    (hS : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : S)) (n : ℕ) (γ : F.Curve) :
    Curve.map φ (F.typicalProjectorStage p hR n γ) =
      (F.map φ).typicalProjectorStage p hS n (Curve.map φ γ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [typicalProjectorStage, typicalProjectorStage]
    split_ifs with hq
    · simp only [AddMonoidHom.comp_apply, F.map_cartierProjectorCurve, ih]
    · exact ih

private theorem mapCurve_typicalProjectorStage {G : FormalGroup R} [G.IsComm]
    (f : TauCeti.FormalGroupHom F G) (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) (n : ℕ) (γ : F.Curve) :
    f.mapCurve (F.typicalProjectorStage p hunit n γ) =
      G.typicalProjectorStage p hunit n (f.mapCurve γ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [typicalProjectorStage, typicalProjectorStage]
    split_ifs with hq
    · simp only [AddMonoidHom.comp_apply, f.mapCurve_cartierProjectorCurve, ih]
    · exact ih

/-- **Cartier's typical projector** on curves of a commutative formal group law `F`, defined
whenever every prime `q` not dividing `p` is invertible in `R`. Its degree-`k` coefficient is the
degree-`k` coefficient of the composite of `1 - V_q [q]_F⁻¹ f_q` over all primes `q ≤ k` not
dividing `p`. -/
noncomputable def typicalProjectorCurve (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) : F.Curve →+ F.Curve where
  toFun γ :=
    { toPowerSeries := PowerSeries.mk fun k ↦
        PowerSeries.coeff k (F.typicalProjectorStage p hunit k γ).toPowerSeries
      constantCoeff_toPowerSeries := by
        simp [← PowerSeries.coeff_zero_eq_constantCoeff_apply, typicalProjectorStage] }
  map_zero' := Curve.ext <| PowerSeries.ext fun k ↦ by
    simp only [PowerSeries.coeff_mk, map_zero, Curve.toPowerSeries_zero]
  map_add' γ₁ γ₂ := Curve.ext <| PowerSeries.ext fun k ↦ by
    simp only [PowerSeries.coeff_mk, map_add]
    exact Curve.coeff_add_congr
      (fun i hik ↦ by
        simp only [PowerSeries.coeff_mk]
        exact F.coeff_typicalProjectorStage_of_le p hunit (le_refl i) hik γ₁)
      (fun i hik ↦ by
        simp only [PowerSeries.coeff_mk]
        exact F.coeff_typicalProjectorStage_of_le p hunit (le_refl i) hik γ₂)

private theorem coeff_typicalProjectorCurve_eq_stage (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) {k n : ℕ} (hkn : k ≤ n)
    (γ : F.Curve) :
    PowerSeries.coeff k (F.typicalProjectorCurve p hunit γ).toPowerSeries =
      PowerSeries.coeff k (F.typicalProjectorStage p hunit n γ).toPowerSeries := by
  simp only [typicalProjectorCurve, AddMonoidHom.coe_mk, ZeroHom.coe_mk, PowerSeries.coeff_mk]
  exact (F.coeff_typicalProjectorStage_of_le p hunit (le_refl k) hkn γ).symm

/-- Below the least prime not dividing `p`, Cartier's typical projector leaves coefficients
unchanged. -/
theorem coeff_typicalProjectorCurve_of_forall_prime_le_dvd (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) {k : ℕ}
    (hk : ∀ q : ℕ, q ≤ k → q.Prime → q ∣ p) (γ : F.Curve) :
    PowerSeries.coeff k (F.typicalProjectorCurve p hunit γ).toPowerSeries =
      PowerSeries.coeff k γ.toPowerSeries := by
  have hstage : ∀ n ≤ k, F.typicalProjectorStage p hunit n γ = γ := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [typicalProjectorStage, dite_eq_right fun hq ↦ hq.2 (hk (n + 1) hn hq.1)]
      exact ih (Nat.le_of_succ_le hn)
  rw [F.coeff_typicalProjectorCurve_eq_stage p hunit (le_refl k), hstage k (le_refl k)]

/-- Cartier's typical projector preserves the linear coefficient `coeff 1` of every curve. -/
@[simp]
theorem coeff_one_typicalProjectorCurve (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) (γ : F.Curve) :
    PowerSeries.coeff 1 (F.typicalProjectorCurve p hunit γ).toPowerSeries =
      PowerSeries.coeff 1 γ.toPowerSeries :=
  F.coeff_typicalProjectorCurve_of_forall_prime_le_dvd p hunit
    (fun _ hq1 hq ↦ absurd hq1 (not_le_of_gt hq.one_lt)) γ

/-- At `p = 0`, Cartier's typical projector is the identity. -/
@[simp]
theorem typicalProjectorCurve_zero (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ 0 → IsUnit (q : R)) :
    F.typicalProjectorCurve 0 hunit = AddMonoidHom.id F.Curve := by
  ext γ k
  exact F.coeff_typicalProjectorCurve_of_forall_prime_le_dvd 0 hunit (fun _ _ _ ↦ dvd_zero _) γ

/-- Base change of rings commutes with Cartier's typical projector. -/
theorem map_typicalProjectorCurve (φ : R →+* S) (p : ℕ)
    (hR : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R))
    (hS : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : S)) (γ : F.Curve) :
    Curve.map φ (F.typicalProjectorCurve p hR γ) =
      (F.map φ).typicalProjectorCurve p hS (Curve.map φ γ) := by
  ext k
  rw [Curve.toPowerSeries_map, PowerSeries.coeff_map,
    F.coeff_typicalProjectorCurve_eq_stage p hR (le_refl k),
    (F.map φ).coeff_typicalProjectorCurve_eq_stage p hS (le_refl k),
    ← F.map_typicalProjectorStage φ p hR hS k γ, Curve.toPowerSeries_map, PowerSeries.coeff_map]

/-- Formal-group homomorphisms commute with Cartier's typical projector. -/
theorem _root_.TauCeti.FormalGroupHom.mapCurve_typicalProjectorCurve
    {F G : FormalGroup R} [F.IsComm] [G.IsComm] (f : TauCeti.FormalGroupHom F G) (p : ℕ)
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
  rw [TauCeti.FormalGroupHom.toPowerSeries_mapCurve,
    ← PowerSeries.coeff_trunc_comp_trunc f.toPowerSeries
      (F.typicalProjectorCurve p hunit γ).constantCoeff_toPowerSeries
      (Nat.lt_succ_self k) (Nat.lt_succ_self k),
    htrunc,
    PowerSeries.coeff_trunc_comp_trunc f.toPowerSeries
      (F.typicalProjectorStage p hunit k γ).constantCoeff_toPowerSeries
      (Nat.lt_succ_self k) (Nat.lt_succ_self k),
    ← TauCeti.FormalGroupHom.toPowerSeries_mapCurve,
    F.mapCurve_typicalProjectorStage f p hunit k γ,
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
        refine if_congr ⟨fun hall q hqk hqle ↦ ?_,
          fun hall q hqk hqn ↦ hall q hqk (Nat.le_succ_of_le hqn)⟩ rfl rfl
        rcases Nat.of_le_succ hqle with hqn | rfl
        · exact hall q hqk hqn
        · exact absurd (Nat.dvd_of_mem_primeFactors hqk) hdvd
    · rw [dite_eq_right hq, ih]
      refine if_congr ⟨fun hall q hqk hqle ↦ ?_,
        fun hall q hqk hqn ↦ hall q hqk (Nat.le_succ_of_le hqn)⟩ rfl rfl
      rcases Nat.of_le_succ hqle with hqn | rfl
      · exact hall q hqk hqn
      · exact Classical.byContradiction fun hnp ↦ hq ⟨Nat.prime_of_mem_primeFactors hqk, hnp⟩

/-- On the additive formal group law `𝔾ₐ`, Cartier's typical projector retains degrees whose prime
factors all divide `p` and zeroes out all other degrees. -/
@[simp]
theorem coeff_typicalProjectorCurve_𝔾ₐ (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) (k : ℕ)
    (γ : (𝔾ₐ (R := R)).Curve) :
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
  simpa only [TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries,
    coeff_typicalProjectorCurve_𝔾ₐ] using
    congrArg (fun δ : (𝔾ₐ (R := R)).Curve ↦ PowerSeries.coeff k δ.toPowerSeries)
      (F.logHom.mapCurve_typicalProjectorCurve p hunit γ)

/-- Over a `ℚ`-algebra, for a prime `p`, Cartier's typical projector retains the prime-power
degrees `p^r` of `log_F(γ(T))` and deletes all other degrees. -/
theorem coeff_subst_typicalProjectorCurve_log_of_prime [Algebra ℚ R] {p : ℕ} (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) (k : ℕ) (γ : F.Curve) :
    PowerSeries.coeff k
        (PowerSeries.subst (F.typicalProjectorCurve p hunit γ).toPowerSeries F.log) =
      if p ^ Nat.log p k = k then
        PowerSeries.coeff k (PowerSeries.subst γ.toPowerSeries F.log)
      else 0 := by
  rw [F.coeff_subst_typicalProjectorCurve_log p hunit k γ]
  rcases eq_or_ne k 0 with rfl | hk0
  · have h0 := (F.logHom.mapCurve γ).coeff_zero_toPowerSeries
    rw [TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries] at h0
    simp [h0]
  · refine if_congr ⟨fun h ↦ ?_, fun h q hq ↦ ?_⟩ rfl rfl
    · have hr := Nat.eq_prime_pow_of_unique_prime_dvd hk0 fun {q} hq hqk ↦
        (Nat.prime_dvd_prime_iff_eq hq hp).mp (h q (Nat.mem_primeFactors.mpr ⟨hq, hqk, hk0⟩))
      conv_lhs => rw [hr, Nat.log_pow hp.one_lt]
      exact hr.symm
    · obtain ⟨hq_prime, hqk, _⟩ := Nat.mem_primeFactors.mp hq
      rw [← h] at hqk
      exact dvd_of_eq ((Nat.prime_dvd_prime_iff_eq hq_prime hp).mp (hq_prime.dvd_of_dvd_pow hqk))

/-- Over a `ℚ`-algebra, for a prime `p`, Cartier's typical projector leaves the degree-`p^r`
logarithm coefficients of every curve unchanged. -/
@[simp]
theorem coeff_subst_typicalProjectorCurve_log_pow [Algebra ℚ R] {p : ℕ} (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) (r : ℕ) (γ : F.Curve) :
    PowerSeries.coeff (p ^ r)
        (PowerSeries.subst (F.typicalProjectorCurve p hunit γ).toPowerSeries F.log) =
      PowerSeries.coeff (p ^ r) (PowerSeries.subst γ.toPowerSeries F.log) := by
  rw [F.coeff_subst_typicalProjectorCurve_log_of_prime hp hunit,
    ite_eq_left (by rw [Nat.log_pow hp.one_lt])]

/-- Over a `ℚ`-algebra, for a prime `p`, Cartier's typical projector zeroes out all non-prime-power
logarithm coefficients of every curve. -/
@[simp]
theorem coeff_subst_typicalProjectorCurve_log_eq_zero [Algebra ℚ R] {p : ℕ} (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) {k : ℕ} (hk : ∀ r : ℕ, p ^ r ≠ k)
    (γ : F.Curve) :
    PowerSeries.coeff k
        (PowerSeries.subst (F.typicalProjectorCurve p hunit γ).toPowerSeries F.log) = 0 := by
  rw [F.coeff_subst_typicalProjectorCurve_log_of_prime hp hunit, ite_eq_right (hk _)]

/-! ### Operator identities and idempotence over arbitrary commutative rings -/

private theorem frobeniusCurve_typicalProjectorCurve_of_coprime_ratAlgebra [Algebra ℚ R]
    (p : ℕ) (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) {n : ℕ} (hn1 : 1 < n)
    (hcop : n.Coprime p) (γ : F.Curve) :
    F.frobeniusCurve n (by omega) (F.typicalProjectorCurve p hunit γ) = 0 := by
  apply F.logIso.curveEquiv.injective
  ext k
  simp only [TauCeti.FormalGroupIso.curveEquiv_apply, logIso_toHom,
    TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries,
    subst_frobeniusCurve_log, PowerSeries.coeff_smul, PowerSeries.coeff_cartier, Nat.add_zero,
    coeff_subst_typicalProjectorCurve_log, map_zero, Curve.toPowerSeries_zero, smul_eq_mul]
  rcases eq_or_ne k 0 with rfl | hk0
  · have h0 := (F.logHom.mapCurve γ).coeff_zero_toPowerSeries
    rw [TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries] at h0
    simp [h0]
  · obtain ⟨q, hq, hqn⟩ := Nat.exists_prime_and_dvd hn1.ne'
    have hqk : q ∈ (n * k).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hq, dvd_mul_of_dvd_left hqn k, mul_ne_zero (by omega) hk0⟩
    have hqp : ¬ q ∣ p := hq.coprime_iff_not_dvd.mp (hcop.coprime_dvd_left hqn)
    rw [ite_eq_right fun hall ↦ hqp (hall q hqk), mul_zero]

/-- Frobenius of any index `n > 1` coprime to `p` annihilates the image of Cartier's typical
projector. -/
theorem frobeniusCurve_typicalProjectorCurve_of_coprime (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) {n : ℕ} (hn1 : 1 < n)
    (hcop : n.Coprime p) (γ : F.Curve) :
    F.frobeniusCurve n (by omega) (F.typicalProjectorCurve p hunit γ) = 0 :=
  Curve.eq_of_forall_ratAlgebra F γ {q : ℕ | q.Prime ∧ ¬ q ∣ p}
    (fun q hq ↦ hunit q hq.1 hq.2)
    (fun G _ hB δ ↦ G.frobeniusCurve n (by omega)
      (G.typicalProjectorCurve p (fun q hq hqp ↦ hB q ⟨hq, hqp⟩) δ))
    (fun _ _ _ _ ↦ 0)
    (fun G _ hB δ ↦
      G.frobeniusCurve_typicalProjectorCurve_of_coprime_ratAlgebra p
        (fun q hq hqp ↦ hB q ⟨hq, hqp⟩) hn1 hcop δ)
    (fun G _ hB hC φ δ ↦ by
      rw [G.map_frobeniusCurve, G.map_typicalProjectorCurve φ p
        (fun q hq hqp ↦ hB q ⟨hq, hqp⟩) (fun q hq hqp ↦ hC q ⟨hq, hqp⟩)])
    (fun _ _ _ _ φ _ ↦ map_zero (Curve.map φ))
    (fun _ f δ ↦ by rw [f.mapCurve_frobeniusCurve, f.mapCurve_typicalProjectorCurve])
    (fun _ f _ ↦ map_zero f.mapCurve)

/-- Frobenius at any prime `q` not dividing `p` annihilates the image of Cartier's typical
projector. -/
@[simp]
theorem frobeniusCurve_typicalProjectorCurve_of_not_dvd (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) {q : ℕ} (hq : q.Prime)
    (hqp : ¬ q ∣ p) (γ : F.Curve) :
    F.frobeniusCurve q hq.ne_zero (F.typicalProjectorCurve p hunit γ) = 0 :=
  F.frobeniusCurve_typicalProjectorCurve_of_coprime p hunit hq.one_lt
    (hq.coprime_iff_not_dvd.mpr hqp) γ

/-- Every curve in the image of Cartier's typical projector is `p`-typical. -/
@[simp]
theorem isTypical_typicalProjectorCurve (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) (γ : F.Curve) :
    (F.typicalProjectorCurve p hunit γ).IsTypical p :=
  fun _ hq hqp ↦ F.frobeniusCurve_typicalProjectorCurve_of_not_dvd p hunit hq hqp γ

/-- Every `p`-typical curve is fixed by Cartier's typical projector. -/
theorem typicalProjectorCurve_eq_self (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) {γ : F.Curve}
    (hγ : γ.IsTypical p) :
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
theorem typicalProjectorCurve_eq_self_iff (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) (γ : F.Curve) :
    F.typicalProjectorCurve p hunit γ = γ ↔ γ.IsTypical p :=
  ⟨fun h ↦ h ▸ F.isTypical_typicalProjectorCurve p hunit γ,
    F.typicalProjectorCurve_eq_self p hunit⟩

/-- Cartier's typical projector is idempotent on curves. -/
@[simp]
theorem typicalProjectorCurve_typicalProjectorCurve (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) (γ : F.Curve) :
    F.typicalProjectorCurve p hunit (F.typicalProjectorCurve p hunit γ) =
      F.typicalProjectorCurve p hunit γ :=
  F.typicalProjectorCurve_eq_self p hunit (F.isTypical_typicalProjectorCurve p hunit γ)

/-- Cartier's typical projector is an idempotent in the endomorphism ring of `F.Curve`. -/
@[simp]
theorem isIdempotentElem_typicalProjectorCurve (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) :
    IsIdempotentElem (M := AddMonoid.End F.Curve) (F.typicalProjectorCurve p hunit) :=
  AddMonoidHom.ext (F.typicalProjectorCurve_typicalProjectorCurve p hunit)

/-- The image of Cartier's typical projector is the subgroup of `p`-typical curves. -/
@[simp]
theorem range_typicalProjectorCurve (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) :
    (F.typicalProjectorCurve p hunit).range = F.typicalCurveSubgroup p := by
  ext γ
  simp only [AddMonoidHom.mem_range, mem_typicalCurveSubgroup]
  exact ⟨by rintro ⟨δ, rfl⟩; exact F.isTypical_typicalProjectorCurve p hunit δ,
    fun hγ ↦ ⟨γ, F.typicalProjectorCurve_eq_self p hunit hγ⟩⟩

/-- Verschiebung `V_n` is annihilated by Cartier's typical projector whenever `n > 1` is coprime to
`p`. -/
theorem typicalProjectorCurve_verschiebungCurve_of_coprime (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) {n : ℕ} (hn1 : 1 < n)
    (hcop : n.Coprime p) (γ : F.Curve) :
    F.typicalProjectorCurve p hunit (F.verschiebungCurve n (by omega) γ) = 0 :=
  Curve.eq_of_forall_ratAlgebra F γ {q : ℕ | q.Prime ∧ ¬ q ∣ p}
    (fun q hq ↦ hunit q hq.1 hq.2)
    (fun G _ hB δ ↦ G.typicalProjectorCurve p (fun q hq hqp ↦ hB q ⟨hq, hqp⟩)
      (G.verschiebungCurve n (by omega) δ))
    (fun _ _ _ _ ↦ 0)
    (fun G _ hB δ ↦ by
      apply G.logIso.curveEquiv.injective
      ext k
      simp only [TauCeti.FormalGroupIso.curveEquiv_apply, logIso_toHom,
        TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries,
        coeff_subst_typicalProjectorCurve_log, subst_verschiebungCurve_log,
        PowerSeries.coeff_expand, map_zero, Curve.toPowerSeries_zero]
      split_ifs with hprime hdvd
      · rcases eq_or_ne k 0 with rfl | hk0
        · have h0 := (G.logHom.mapCurve δ).coeff_zero_toPowerSeries
          rw [TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries] at h0
          simp [h0]
        · obtain ⟨m, rfl⟩ := hdvd
          obtain ⟨q, hq, hqn⟩ := Nat.exists_prime_and_dvd hn1.ne'
          have hqk : q ∈ (n * m).primeFactors :=
            Nat.mem_primeFactors.mpr
              ⟨hq, dvd_mul_of_dvd_left hqn m, mul_ne_zero (by omega) (right_ne_zero_of_mul hk0)⟩
          exact absurd (hprime q hqk) (hq.coprime_iff_not_dvd.mp (hcop.coprime_dvd_left hqn))
      · rfl
      · rfl)
    (fun G _ hB hC φ δ ↦ by
      rw [G.map_typicalProjectorCurve φ p (fun q hq hqp ↦ hB q ⟨hq, hqp⟩)
        (fun q hq hqp ↦ hC q ⟨hq, hqp⟩), G.map_verschiebungCurve])
    (fun _ _ _ _ φ _ ↦ map_zero (Curve.map φ))
    (fun _ f δ ↦ by rw [f.mapCurve_typicalProjectorCurve, f.mapCurve_verschiebungCurve])
    (fun _ f _ ↦ map_zero f.mapCurve)

/-- Cartier's typical projector commutes with `V_n` whenever every prime factor of `n` divides
`p`. -/
theorem typicalProjectorCurve_verschiebungCurve_of_forall_prime_dvd (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) {n : ℕ} (hn : n ≠ 0)
    (hdvd : ∀ q : ℕ, q.Prime → q ∣ n → q ∣ p) (γ : F.Curve) :
    F.typicalProjectorCurve p hunit (F.verschiebungCurve n hn γ) =
      F.verschiebungCurve n hn (F.typicalProjectorCurve p hunit γ) := by
  have hstage : ∀ m, F.typicalProjectorStage p hunit m (F.verschiebungCurve n hn γ) =
      F.verschiebungCurve n hn (F.typicalProjectorStage p hunit m γ) := fun m ↦ by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [typicalProjectorStage]
      split_ifs with hq
      · have hcop : (m + 1).Coprime n :=
          hq.1.coprime_iff_not_dvd.mpr fun hmn ↦ hq.2 (hdvd (m + 1) hq.1 hmn)
        rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ih,
          F.cartierProjectorCurve_verschiebungCurve_of_coprime (Nat.succ_ne_zero m) hn
            (hunit (m + 1) hq.1 hq.2) hcop]
      · exact ih
  ext k
  rw [F.coeff_typicalProjectorCurve_eq_stage p hunit (le_refl k), hstage k,
    toPowerSeries_verschiebungCurve, toPowerSeries_verschiebungCurve,
    PowerSeries.coeff_expand, PowerSeries.coeff_expand]
  split_ifs with hnk
  · exact (F.coeff_typicalProjectorCurve_eq_stage p hunit (Nat.div_le_self k n) γ).symm
  · rfl

/-- Cartier's typical projector commutes with `V_p` for `p ≠ 0`. -/
theorem typicalProjectorCurve_verschiebungCurve_self {p : ℕ} (hp : p ≠ 0)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) (γ : F.Curve) :
    F.typicalProjectorCurve p hunit (F.verschiebungCurve p hp γ) =
      F.verschiebungCurve p hp (F.typicalProjectorCurve p hunit γ) :=
  F.typicalProjectorCurve_verschiebungCurve_of_forall_prime_dvd p hunit hp (fun _ _ h ↦ h) γ

/-- Cartier's typical projector commutes with `V_{p^r}` for `p ≠ 0`. -/
theorem typicalProjectorCurve_verschiebungCurve_pow {p : ℕ} (hp : p ≠ 0) (r : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) (γ : F.Curve) :
    F.typicalProjectorCurve p hunit (F.verschiebungCurve (p ^ r) (pow_ne_zero r hp) γ) =
      F.verschiebungCurve (p ^ r) (pow_ne_zero r hp) (F.typicalProjectorCurve p hunit γ) :=
  F.typicalProjectorCurve_verschiebungCurve_of_forall_prime_dvd p hunit (pow_ne_zero r hp)
    (fun _ hq hqr ↦ hq.dvd_of_dvd_pow hqr) γ

/-- Cartier's typical projector commutes with `f_n` whenever every prime factor of `n` divides
`p`. -/
theorem frobeniusCurve_typicalProjectorCurve_of_forall_prime_dvd (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) {n : ℕ} (hn : n ≠ 0)
    (hdvd : ∀ q : ℕ, q.Prime → q ∣ n → q ∣ p) (γ : F.Curve) :
    F.frobeniusCurve n hn (F.typicalProjectorCurve p hunit γ) =
      F.typicalProjectorCurve p hunit (F.frobeniusCurve n hn γ) :=
  Curve.eq_of_forall_ratAlgebra F γ {q : ℕ | q.Prime ∧ ¬ q ∣ p}
    (fun q hq ↦ hunit q hq.1 hq.2)
    (fun G _ hB δ ↦ G.frobeniusCurve n hn
      (G.typicalProjectorCurve p (fun q hq hqp ↦ hB q ⟨hq, hqp⟩) δ))
    (fun G _ hB δ ↦ G.typicalProjectorCurve p (fun q hq hqp ↦ hB q ⟨hq, hqp⟩)
      (G.frobeniusCurve n hn δ))
    (fun G _ hB δ ↦ by
      apply G.logIso.curveEquiv.injective
      ext k
      simp only [TauCeti.FormalGroupIso.curveEquiv_apply, logIso_toHom,
        TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries,
        subst_frobeniusCurve_log, coeff_subst_typicalProjectorCurve_log,
        PowerSeries.coeff_smul, PowerSeries.coeff_cartier, Nat.add_zero, smul_eq_mul]
      rcases eq_or_ne k 0 with rfl | hk0
      · have h0 := (G.logHom.mapCurve δ).coeff_zero_toPowerSeries
        rw [TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries] at h0
        simp [h0]
      · have hiff : (∀ q ∈ (n * k).primeFactors, q ∣ p) ↔ ∀ q ∈ k.primeFactors, q ∣ p :=
          ⟨fun h q hqk ↦ h q (Nat.primeFactors_mono (dvd_mul_left k n) (mul_ne_zero hn hk0) hqk),
            fun h q hqnk ↦ by
              obtain ⟨hq, hq_dvd, _⟩ := Nat.mem_primeFactors.mp hqnk
              rcases hq.dvd_mul.mp hq_dvd with hqn | hqk
              · exact hdvd q hq hqn
              · exact h q (Nat.mem_primeFactors.mpr ⟨hq, hqk, hk0⟩)⟩
        rw [if_congr hiff rfl rfl]
        split_ifs <;> simp)
    (fun G _ hB hC φ δ ↦ by
      rw [G.map_frobeniusCurve, G.map_typicalProjectorCurve φ p
        (fun q hq hqp ↦ hB q ⟨hq, hqp⟩) (fun q hq hqp ↦ hC q ⟨hq, hqp⟩)])
    (fun G _ hB hC φ δ ↦ by
      rw [G.map_typicalProjectorCurve φ p (fun q hq hqp ↦ hB q ⟨hq, hqp⟩)
        (fun q hq hqp ↦ hC q ⟨hq, hqp⟩), G.map_frobeniusCurve])
    (fun _ f δ ↦ by rw [f.mapCurve_frobeniusCurve, f.mapCurve_typicalProjectorCurve])
    (fun _ f δ ↦ by rw [f.mapCurve_typicalProjectorCurve, f.mapCurve_frobeniusCurve])

/-- Cartier's typical projector commutes with `f_p` for `p ≠ 0`. -/
theorem frobeniusCurve_typicalProjectorCurve_self {p : ℕ} (hp : p ≠ 0)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) (γ : F.Curve) :
    F.frobeniusCurve p hp (F.typicalProjectorCurve p hunit γ) =
      F.typicalProjectorCurve p hunit (F.frobeniusCurve p hp γ) :=
  F.frobeniusCurve_typicalProjectorCurve_of_forall_prime_dvd p hunit hp (fun _ _ h ↦ h) γ

/-- Cartier's typical projector commutes with `f_{p^r}` for `p ≠ 0`. -/
theorem frobeniusCurve_typicalProjectorCurve_pow {p : ℕ} (hp : p ≠ 0) (r : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) (γ : F.Curve) :
    F.frobeniusCurve (p ^ r) (pow_ne_zero r hp) (F.typicalProjectorCurve p hunit γ) =
      F.typicalProjectorCurve p hunit (F.frobeniusCurve (p ^ r) (pow_ne_zero r hp) γ) :=
  F.frobeniusCurve_typicalProjectorCurve_of_forall_prime_dvd p hunit (pow_ne_zero r hp)
    (fun _ hq hqr ↦ hq.dvd_of_dvd_pow hqr) γ

/-- Every elementary Cartier projector of coprime index `n > 1` fixes the image of Cartier's
typical projector. -/
theorem cartierProjectorCurve_typicalProjectorCurve_of_coprime (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) {n : ℕ} (hn1 : 1 < n)
    (hcop : n.Coprime p) (hn_unit : IsUnit (n : R)) (γ : F.Curve) :
    F.cartierProjectorCurve n (by omega) hn_unit (F.typicalProjectorCurve p hunit γ) =
      F.typicalProjectorCurve p hunit γ :=
  F.cartierProjectorCurve_eq_self n (by omega) hn_unit
    (F.frobeniusCurve_typicalProjectorCurve_of_coprime p hunit hn1 hcop γ)

/-- Cartier's typical projector absorbs every elementary Cartier projector of coprime index
`n > 1`. -/
theorem typicalProjectorCurve_cartierProjectorCurve_of_coprime (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) {n : ℕ} (hn1 : 1 < n)
    (hcop : n.Coprime p) (hn_unit : IsUnit (n : R)) (γ : F.Curve) :
    F.typicalProjectorCurve p hunit (F.cartierProjectorCurve n (by omega) hn_unit γ) =
      F.typicalProjectorCurve p hunit γ := by
  rw [cartierProjectorCurve_apply, map_sub,
    F.typicalProjectorCurve_verschiebungCurve_of_coprime p hunit hn1 hcop, sub_zero]

/-- Cartier's typical projector commutes with Cartier's homothety operator `[r]`. -/
theorem typicalProjectorCurve_homothetyCurve (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) (r : R) (γ : F.Curve) :
    F.typicalProjectorCurve p hunit (F.homothetyCurve r γ) =
      F.homothetyCurve r (F.typicalProjectorCurve p hunit γ) := by
  have hstage : ∀ m, F.typicalProjectorStage p hunit m (F.homothetyCurve r γ) =
      F.homothetyCurve r (F.typicalProjectorStage p hunit m γ) := fun m ↦ by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [typicalProjectorStage]
      split_ifs with hq
      · rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ih,
          F.cartierProjectorCurve_homothetyCurve r (m + 1) (Nat.succ_ne_zero m)
            (hunit (m + 1) hq.1 hq.2)]
      · exact ih
  ext k
  rw [F.coeff_typicalProjectorCurve_eq_stage p hunit (le_refl k), hstage k,
    toPowerSeries_homothetyCurve, toPowerSeries_homothetyCurve,
    PowerSeries.coeff_rescale, PowerSeries.coeff_rescale,
    F.coeff_typicalProjectorCurve_eq_stage p hunit (le_refl k)]

/-- A curve `δ` equals Cartier's typical projection of `γ` if and only if `δ` is `p`-typical and
`γ - δ` lies in the kernel of Cartier's typical projector. -/
theorem typicalProjectorCurve_eq_iff (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) {γ δ : F.Curve} :
    F.typicalProjectorCurve p hunit γ = δ ↔
      δ.IsTypical p ∧ γ - δ ∈ (F.typicalProjectorCurve p hunit).ker := by
  rw [AddMonoidHom.mem_ker, map_sub]
  constructor
  · rintro rfl
    exact ⟨F.isTypical_typicalProjectorCurve p hunit γ,
      by rw [F.typicalProjectorCurve_typicalProjectorCurve, sub_self]⟩
  · rintro ⟨hδ, hker⟩
    rw [F.typicalProjectorCurve_eq_self p hunit hδ] at hker
    exact sub_eq_zero.mp hker

end TypicalProjector

end FormalGroup
