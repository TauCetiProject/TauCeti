/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Curve
import TauCeti.Algebra.Algebra.NatCast
import TauCeti.NumberTheory.ArithmeticFunction.Moebius
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# `p`-typical curves, `p`-typical formal group laws, and Cartier–Quillen `p`-typicalization

Let `F(X, Y)` be a commutative one-dimensional formal group law over a commutative ring `R`, and
let `p` be a natural number (typically a prime). Following Cartier (1967) and Quillen (1969):

* A curve `γ ∈ F.Curve` is **`p`-typical** (`FormalGroup.Curve.IsPTypical`) if Cartier's Frobenius
  operator `f_q` annihilates `γ` for every prime `q ≠ p`.
* The formal group law `F` itself is **`p`-typical** (`FormalGroup.IsPTypical`) if its tautological
  curve `γ(T) = T` is `p`-typical.

Over a `ℚ`-algebra, a curve `γ` on `F` (when `p` is prime) is `p`-typical if and only if the formal
logarithm series `log_F(γ(T))` is supported in degrees `pᵏ` (`k ≥ 0`); in particular, `F` is
`p`-typical if and only if `log_F(T) = ∑_{k ≥ 0} ℓ_k T^(pᵏ)`.

When every prime `q ≠ p` is invertible in `R` (for instance over a `ℤ_(p)`-algebra), every positive
integer `n` coprime to `p` is invertible in `R` (`Nat.Coprime.isUnit_natCast_of_prime`), so
multiplication `[n]_F` is an automorphism of `F` and admits an inverse `[1/n]_F` on curves
(`FormalGroup.divNatCurve`). Cartier's **`p`-typicalization operator** on curves is the infinite
formal-group sum

  `(ε_p γ)(T) = ∑_{gcd(n, p) = 1}^F μ(n) · V_n([1/n]_F(f_n γ))(T)`,

which converges coefficientwise because `V_n` vanishes below degree `n`. Applying `ε_p` to the
tautological curve yields a strict curve `(ε_p T)(T) = T + ⋯`; its compositional inverse is a
strict formal coordinate `F.pTypicalCoord p hunit` transporting `F` to a canonical strictly
isomorphic `p`-typical formal group law `F.pTypicalCoord p hunit • F`. Over a `ℚ`-algebra, its
formal logarithm is obtained from `log_F` by discarding all non-`p`-power terms.

## Main definitions

* `FormalGroup.Curve.IsPTypical`: `p`-typical curves `γ` on `F` (`f_q γ = 0` for primes `q ≠ p`).
* `FormalGroup.IsPTypical`: `p`-typical commutative formal group laws (`T` is `p`-typical on `F`).
* `FormalGroup.divNatCurve`: division by `n` on `F.Curve` when `(n : R)` is a unit.
* `FormalGroup.pTypicalCurve`: Cartier's `p`-typicalization operator `ε_p : F.Curve →+ F.Curve`.
* `FormalGroup.pTypicalCoord`: the canonical strict formal coordinate transporting `F` to a
  `p`-typical formal group law `F.pTypicalCoord p hunit • F`.

## Main results

* `FormalGroup.Curve.isPTypical_iff_coeff_subst_log_eq_zero` and
  `FormalGroup.isPTypical_iff_coeff_log_eq_zero`: logarithmic characterization over `ℚ`-algebras.
* `FormalGroup.isPTypical_smul_iff`: `(φ • F)` is `p`-typical if and only if `φ⁻¹` is a `p`-typical
  curve on `F`.
* `FormalGroup.coeff_subst_pTypicalCurve_log`: `log_F((ε_p γ)(T))` retains `pᵏ`-degree terms of
  `log_F(γ(T))` and kills all others.
* `FormalGroup.isPTypical_pTypicalCurve`, `FormalGroup.pTypicalCurve_eq_self_iff`,
  `FormalGroup.pTypicalCurve_pTypicalCurve`, and
  `FormalGroup.pTypicalCurve_verschiebungCurve_of_prime_ne`: idempotence and Verschiebung
  annihilation of `ε_p` over any ring inverting primes `q ≠ p`.
* `FormalGroup.isPTypical_pTypicalCoord_smul`, `FormalGroup.pTypicalCoord_eq_one_iff`, and
  `FormalGroup.coeff_log_pTypicalCoord_smul`: properties of the canonical `p`-typical coordinate
  change.

## References

* P. Cartier, *Modules associés à un groupe formel commutatif. Courbes typiques*, C. R. Acad. Sci.
  Paris Sér. A-B 265 (1967), A129–A132.
* D. Quillen, *On the formal group laws of unoriented and complex cobordism theory*, Bull. Amer.
  Math. Soc. 75 (1969), 1293–1298.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapters I §4 and II §15–16.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Academic Press (1986),
  Appendix A2.1.19–A2.1.25.
-/

public section

namespace FormalGroup

variable {R S : Type*} [CommRing R] [CommRing S]

/-! ### `p`-typical curves -/

namespace Curve

variable {F : FormalGroup R} [F.IsComm]

/-- A curve `γ` on a commutative formal group law `F` is **`p`-typical** if Cartier's Frobenius
operator `f_q` annihilates `γ` for every prime `q ≠ p`. -/
def IsPTypical (γ : F.Curve) (p : ℕ) : Prop :=
  ∀ ⦃q : ℕ⦄ (hq : q.Prime), q ≠ p → F.frobeniusCurve q hq.ne_zero γ = 0

theorem isPTypical_iff {γ : F.Curve} {p : ℕ} :
    γ.IsPTypical p ↔ ∀ ⦃q : ℕ⦄ (hq : q.Prime), q ≠ p → F.frobeniusCurve q hq.ne_zero γ = 0 :=
  Iff.rfl

@[simp]
theorem isPTypical_zero (p : ℕ) : (0 : F.Curve).IsPTypical p :=
  fun _ _ _ ↦ map_zero _

theorem IsPTypical.add {γ₁ γ₂ : F.Curve} {p : ℕ} (h₁ : γ₁.IsPTypical p) (h₂ : γ₂.IsPTypical p) :
    (γ₁ + γ₂).IsPTypical p :=
  fun q hq hne ↦ by rw [map_add, h₁ hq hne, h₂ hq hne, _root_.add_zero]

theorem IsPTypical.neg {γ : F.Curve} {p : ℕ} (h : γ.IsPTypical p) : (-γ).IsPTypical p :=
  fun q hq hne ↦ by rw [map_neg, h hq hne, neg_zero]

theorem IsPTypical.sub {γ₁ γ₂ : F.Curve} {p : ℕ} (h₁ : γ₁.IsPTypical p) (h₂ : γ₂.IsPTypical p) :
    (γ₁ - γ₂).IsPTypical p :=
  fun q hq hne ↦ by rw [map_sub, h₁ hq hne, h₂ hq hne, sub_zero]

theorem IsPTypical.nsmul {γ : F.Curve} {p : ℕ} (h : γ.IsPTypical p) (n : ℕ) :
    (n • γ).IsPTypical p :=
  fun q hq hne ↦ by rw [map_nsmul, h hq hne, nsmul_zero]

theorem IsPTypical.zsmul {γ : F.Curve} {p : ℕ} (h : γ.IsPTypical p) (n : ℤ) :
    (n • γ).IsPTypical p :=
  fun q hq hne ↦ by rw [map_zsmul, h hq hne, zsmul_zero]

/-- Cartier's Frobenius operators preserve `p`-typical curves. -/
theorem IsPTypical.frobeniusCurve {γ : F.Curve} {p : ℕ} (h : γ.IsPTypical p) (n : ℕ) (hn : n ≠ 0) :
    (F.frobeniusCurve n hn γ).IsPTypical p :=
  fun q hq hne ↦ by
    rw [F.frobeniusCurve_frobeniusCurve hq.ne_zero hn,
      F.frobeniusCurve_congr (mul_comm q n) (mul_ne_zero hq.ne_zero hn) (mul_ne_zero hn hq.ne_zero),
      ← F.frobeniusCurve_frobeniusCurve hn hq.ne_zero, h hq hne, map_zero]

/-- For a prime `p`, the `p`-power Verschiebung operators `V_{pᵏ}` preserve `p`-typical curves. -/
theorem IsPTypical.verschiebungCurve_pow {γ : F.Curve} {p : ℕ} (hp : p.Prime) (h : γ.IsPTypical p)
    (k : ℕ) : (F.verschiebungCurve (p ^ k) (pow_ne_zero k hp.ne_zero) γ).IsPTypical p :=
  fun q hq hne ↦ by
    have hcop : q.Coprime p :=
      hq.coprime_iff_not_dvd.mpr fun hdvd ↦ hne ((hp.dvd_iff_eq hq.ne_one).mp hdvd).symm
    rw [F.frobeniusCurve_verschiebungCurve_of_coprime hq.ne_zero (pow_ne_zero k hp.ne_zero)
      (hcop.pow_right k), h hq hne, map_zero]

/-- For a prime `p`, a curve `γ` is `p`-typical if and only if `f_n γ = 0` for every `n > 1`
coprime to `p`. -/
theorem isPTypical_iff_frobeniusCurve_eq_zero_of_coprime {γ : F.Curve} {p : ℕ} (hp : p.Prime) :
    γ.IsPTypical p ↔
      ∀ ⦃n : ℕ⦄ (hn : n ≠ 0), n.Coprime p → n ≠ 1 → F.frobeniusCurve n hn γ = 0 := by
  refine ⟨fun hγ n hn hcop hn1 ↦ ?_, fun h q hq hne ↦ ?_⟩
  · let q := n.minFac
    have hq : q.Prime := Nat.minFac_prime hn1
    have hdvd : q ∣ n := n.minFac_dvd
    have hq0 : q ≠ 0 := hq.ne_zero
    have hdiv0 : n / q ≠ 0 := fun h0 ↦ hn <| by
      have hmul := Nat.div_mul_cancel hdvd
      rw [h0, zero_mul] at hmul
      exact hmul.symm
    have hne : q ≠ p := fun hqp ↦ hp.ne_one <| by
      subst hqp
      exact Nat.dvd_one.mp (hcop.symm.dvd_of_dvd_mul_left (by simp [hdvd]))
    rw [F.frobeniusCurve_congr (Nat.div_mul_cancel hdvd).symm hn (mul_ne_zero hdiv0 hq0),
      ← F.frobeniusCurve_frobeniusCurve hdiv0 hq0, hγ hq hne, map_zero]
  · have hcop : q.Coprime p :=
      hq.coprime_iff_not_dvd.mpr fun hdvd ↦ hne ((hp.dvd_iff_eq hq.ne_one).mp hdvd).symm
    exact h hq.ne_zero hcop hq.ne_one

/-- Homomorphisms of commutative formal group laws preserve `p`-typical curves. -/
theorem IsPTypical.mapCurve {G : FormalGroup R} [G.IsComm] {γ : F.Curve} {p : ℕ}
    (h : γ.IsPTypical p) (f : TauCeti.FormalGroupHom F G) : (f.mapCurve γ).IsPTypical p :=
  fun q hq hne ↦ by rw [← f.mapCurve_frobeniusCurve, h hq hne, map_zero]

/-- Isomorphisms of commutative formal group laws preserve and reflect `p`-typical curves. -/
@[simp]
theorem _root_.TauCeti.FormalGroupIso.isPTypical_curveEquiv_iff {G : FormalGroup R} [G.IsComm]
    (e : TauCeti.FormalGroupIso F G) {γ : F.Curve} {p : ℕ} :
    (e.curveEquiv γ).IsPTypical p ↔ γ.IsPTypical p := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h' := h.mapCurve e.invHom
    rwa [e.curveEquiv_apply, ← TauCeti.FormalGroupHom.comp_mapCurve, e.invHom_comp_toHom,
      TauCeti.FormalGroupHom.id_mapCurve] at h'
  · rw [e.curveEquiv_apply]
    exact h.mapCurve e.toHom

/-- Base change preserves `p`-typical curves. -/
theorem IsPTypical.map {γ : F.Curve} {p : ℕ} (h : γ.IsPTypical p) (φ : R →+* S) :
    (Curve.map φ γ).IsPTypical p :=
  fun q hq hne ↦ by rw [← F.map_frobeniusCurve φ q hq.ne_zero, h hq hne, map_zero]

/-- Base change along an injective ring homomorphism reflects `p`-typicality of curves. -/
theorem isPTypical_map_iff {φ : R →+* S} (hφ : Function.Injective φ) {γ : F.Curve} {p : ℕ} :
    (Curve.map φ γ).IsPTypical p ↔ γ.IsPTypical p :=
  ⟨fun h q hq hne ↦ Curve.map_injective hφ <| by
    rw [F.map_frobeniusCurve φ q hq.ne_zero, h hq hne, map_zero],
    fun h ↦ h.map φ⟩

/-- Over a `ℚ`-algebra, for a prime `p`, a curve `γ` on `F` is `p`-typical if and only if
`log_F(γ(T))` has zero coefficient in every degree that is not a power of `p`. -/
theorem isPTypical_iff_coeff_subst_log_eq_zero [Algebra ℚ R] {γ : F.Curve} {p : ℕ} (hp : p.Prime) :
    γ.IsPTypical p ↔
      ∀ m : ℕ, (∀ k : ℕ, m ≠ p ^ k) →
        PowerSeries.coeff m (PowerSeries.subst γ.toPowerSeries F.log) = 0 := by
  refine ⟨fun hγ m hm ↦ ?_, fun hlog q hq hne ↦ ?_⟩
  · rcases eq_or_ne m 0 with rfl | hm0
    · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact PowerSeries.constantCoeff_subst_eq_zero γ.constantCoeff_toPowerSeries _
        F.constantCoeff_log
    · have hr1 : ordCompl[p] m ≠ 1 := fun h1 ↦ by
        obtain ⟨k, hk⟩ := (Nat.ordCompl_eq_one_iff_exists_eq_pow hp hm0).mp h1
        exact hm k hk
      let q := (ordCompl[p] m).minFac
      have hq : q.Prime := Nat.minFac_prime hr1
      have hqm : q ∣ m := dvd_trans (ordCompl[p] m).minFac_dvd (Nat.ordCompl_dvd m p)
      have hne : q ≠ p := fun hqp ↦ by
        have hdvd : p ∣ ordCompl[p] m := by
          conv_lhs => rw [← hqp]
          exact (ordCompl[p] m).minFac_dvd
        exact hp.not_dvd_one ((Nat.coprime_ordCompl hp hm0) ▸ Nat.dvd_gcd dvd_rfl hdvd)
      have hf := congrArg (PowerSeries.coeff (m / q)) (F.subst_frobeniusCurve_log q hq.ne_zero γ)
      rw [hγ hq hne, Curve.toPowerSeries_zero,
        PowerSeries.subst_zero_of_constantCoeff_zero F.constantCoeff_log, map_zero,
        PowerSeries.coeff_smul, PowerSeries.coeff_cartier, Nat.add_zero,
        Nat.mul_div_cancel' hqm, smul_eq_mul] at hf
      exact (TauCeti.isUnit_natCast_of_ne_zero (K := R) hq.ne_zero).mul_right_eq_zero.mp hf.symm
  · apply F.logIso.curveEquiv.injective
    rw [map_zero]
    ext k
    simp only [TauCeti.FormalGroupIso.curveEquiv_apply, logIso_toHom,
      TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries,
      F.subst_frobeniusCurve_log q hq.ne_zero γ, Curve.toPowerSeries_zero, map_zero,
      PowerSeries.coeff_smul, PowerSeries.coeff_cartier, Nat.add_zero, smul_eq_mul]
    rcases eq_or_ne k 0 with rfl | hk0
    · rw [mul_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply]
      have hc0 : PowerSeries.constantCoeff (PowerSeries.subst γ.toPowerSeries F.log) = 0 :=
        PowerSeries.constantCoeff_subst_eq_zero γ.constantCoeff_toPowerSeries _ F.constantCoeff_log
      rw [hc0, mul_zero]
    · have hnotpow : ∀ j : ℕ, q * k ≠ p ^ j := fun j hpow ↦ hne <| by
        have hqp : q ∣ p := hq.dvd_of_dvd_pow (hpow ▸ dvd_mul_right q k)
        exact ((hp.dvd_iff_eq hq.ne_one).mp hqp).symm
      rw [hlog (q * k) hnotpow, mul_zero]

end Curve

/-! ### `p`-typical formal group laws -/

/-- A commutative formal group law `F` over `R` is **`p`-typical** if its tautological curve
`γ(T) = T` is `p`-typical on `F`, i.e., `f_q T = 0` for every prime `q ≠ p`. -/
def IsPTypical (F : FormalGroup R) [F.IsComm] (p : ℕ) : Prop :=
  F.tautologicalCurve.IsPTypical p

theorem isPTypical_iff (F : FormalGroup R) [F.IsComm] (p : ℕ) :
    F.IsPTypical p ↔
      ∀ ⦃q : ℕ⦄ (hq : q.Prime), q ≠ p → F.frobeniusCurve q hq.ne_zero F.tautologicalCurve = 0 :=
  Iff.rfl

theorem IsPTypical.map {F : FormalGroup R} [F.IsComm] {p : ℕ} (h : F.IsPTypical p) (φ : R →+* S) :
    (F.map φ).IsPTypical p := by
  rw [IsPTypical, ← F.map_tautologicalCurve φ]
  exact Curve.IsPTypical.map h φ

theorem isPTypical_map_iff {F : FormalGroup R} [F.IsComm] {φ : R →+* S} (hφ : Function.Injective φ)
    {p : ℕ} : (F.map φ).IsPTypical p ↔ F.IsPTypical p := by
  rw [IsPTypical, IsPTypical, ← F.map_tautologicalCurve φ, Curve.isPTypical_map_iff hφ]

/-- The additive formal group law `𝔾ₐ` is `p`-typical for every `p : ℕ` over every commutative
ring. -/
theorem isPTypical_𝔾ₐ (p : ℕ) : (𝔾ₐ (R := R)).IsPTypical p := fun q hq _ ↦ by
  ext k
  simp only [toPowerSeries_frobeniusCurve_𝔾ₐ, toPowerSeries_tautologicalCurve,
    Curve.toPowerSeries_zero, map_zero, PowerSeries.coeff_smul, PowerSeries.coeff_cartier,
    Nat.add_zero, PowerSeries.coeff_X, smul_eq_mul]
  have h1 : q * k ≠ 1 := fun h ↦ hq.ne_one (Nat.eq_one_of_mul_eq_one_right h)
  rw [ite_eq_right h1, mul_zero]

/-- **Cartier's criterion for coordinate changes**: for a formal coordinate `φ` on a commutative
formal group law `F`, the transported formal group law `φ • F` is `p`-typical if and only if the
inverse coordinate `φ⁻¹(T)`, viewed as a curve on `F`, is `p`-typical. -/
theorem isPTypical_smul_iff (φ : TauCeti.FormalCoordinate R) (F : FormalGroup R) [F.IsComm]
    (p : ℕ) :
    (φ • F).IsPTypical p ↔
      (⟨φ⁻¹.toPowerSeries, φ⁻¹.constantCoeff_toPowerSeries⟩ : F.Curve).IsPTypical p := by
  have heq : (smulIso φ F).symm.curveEquiv (φ • F).tautologicalCurve =
      ⟨φ⁻¹.toPowerSeries, φ⁻¹.constantCoeff_toPowerSeries⟩ := by
    ext : 1
    simp
  rw [IsPTypical, ← (smulIso φ F).symm.isPTypical_curveEquiv_iff, heq]

/-- Over a `ℚ`-algebra, for a prime `p`, a commutative formal group law `F` is `p`-typical if and
only if its formal logarithm `log_F(X)` is supported in `p`-power degrees `X^(pᵏ)`. -/
theorem isPTypical_iff_coeff_log_eq_zero [Algebra ℚ R] (F : FormalGroup R) [F.IsComm] {p : ℕ}
    (hp : p.Prime) :
    F.IsPTypical p ↔ ∀ m : ℕ, (∀ k : ℕ, m ≠ p ^ k) → PowerSeries.coeff m F.log = 0 := by
  simp only [IsPTypical, Curve.isPTypical_iff_coeff_subst_log_eq_zero hp,
    toPowerSeries_tautologicalCurve, PowerSeries.X_subst]

/-! ### Division by invertible integers on curves -/

/-- When `(n : R)` is a unit in `R`, multiplication by `n` on a commutative formal group law `F` is
an automorphism of `F`; **division by `n`** (`FormalGroup.divNatCurve`) is the inverse additive
automorphism `[1/n]_F : F.Curve →+ F.Curve`. -/
noncomputable def divNatCurve (F : FormalGroup R) [F.IsComm] (n : ℕ) (hn : IsUnit (n : R)) :
    F.Curve →+ F.Curve :=
  ((F.nsmulHom n).toIso (by simpa [coeff_one_nsmulSeries] using hn)).curveEquiv.symm.toAddMonoidHom

@[simp]
theorem nsmul_divNatCurve (F : FormalGroup R) [F.IsComm] (n : ℕ) (hn : IsUnit (n : R))
    (γ : F.Curve) : n • F.divNatCurve n hn γ = γ := by
  let e := (F.nsmulHom n).toIso (by simpa [coeff_one_nsmulSeries] using hn)
  simpa [divNatCurve, e] using e.curveEquiv.apply_symm_apply γ

@[simp]
theorem divNatCurve_nsmul (F : FormalGroup R) [F.IsComm] (n : ℕ) (hn : IsUnit (n : R))
    (γ : F.Curve) : F.divNatCurve n hn (n • γ) = γ := by
  let e := (F.nsmulHom n).toIso (by simpa [coeff_one_nsmulSeries] using hn)
  simpa [divNatCurve, e] using e.curveEquiv.symm_apply_apply γ

theorem eq_divNatCurve_iff (F : FormalGroup R) [F.IsComm] (n : ℕ) (hn : IsUnit (n : R))
    {δ γ : F.Curve} : δ = F.divNatCurve n hn γ ↔ n • δ = γ :=
  ⟨fun h ↦ h ▸ F.nsmul_divNatCurve n hn γ, fun h ↦ h ▸ (F.divNatCurve_nsmul n hn δ).symm⟩

@[simp]
theorem divNatCurve_one (F : FormalGroup R) [F.IsComm] (h1 : IsUnit ((1 : ℕ) : R)) (γ : F.Curve) :
    F.divNatCurve 1 h1 γ = γ :=
  ((F.eq_divNatCurve_iff 1 h1).mpr (one_nsmul γ)).symm

theorem map_divNatCurve (F : FormalGroup R) [F.IsComm] (φ : R →+* S) (n : ℕ) (hn : IsUnit (n : R))
    (γ : F.Curve) :
    Curve.map φ (F.divNatCurve n hn γ) =
      (F.map φ).divNatCurve n (by simpa using hn.map φ) (Curve.map φ γ) :=
  ((F.map φ).eq_divNatCurve_iff n _).mpr <| by rw [← map_nsmul, F.nsmul_divNatCurve]

theorem _root_.TauCeti.FormalGroupHom.mapCurve_divNatCurve {F G : FormalGroup R}
    [F.IsComm] [G.IsComm] (f : TauCeti.FormalGroupHom F G) (n : ℕ) (hn : IsUnit (n : R))
    (γ : F.Curve) :
    f.mapCurve (F.divNatCurve n hn γ) = G.divNatCurve n hn (f.mapCurve γ) :=
  (G.eq_divNatCurve_iff n hn).mpr <| by rw [← map_nsmul, F.nsmul_divNatCurve]

/-! ### Cartier's `p`-typicalization operator on curves -/

section PTypicalCurve

private noncomputable def toPowerSeries𝔾ₐHom : (𝔾ₐ (R := R)).Curve →+ PowerSeries R where
  toFun := Curve.toPowerSeries
  map_zero' := Curve.toPowerSeries_zero
  map_add' := Curve.toPowerSeries_add_𝔾ₐ

@[simp]
private theorem toPowerSeries𝔾ₐHom_apply (γ : (𝔾ₐ (R := R)).Curve) :
    toPowerSeries𝔾ₐHom γ = γ.toPowerSeries := (rfl)

private noncomputable def substLogHom [Algebra ℚ R] (F : FormalGroup R) :
    F.Curve →+ PowerSeries R :=
  toPowerSeries𝔾ₐHom.comp F.logHom.mapCurve

@[simp]
private theorem substLogHom_apply [Algebra ℚ R] (F : FormalGroup R) (γ : F.Curve) :
    substLogHom F γ = PowerSeries.subst γ.toPowerSeries F.log := by
  simp [substLogHom]

/-- The `n`-th summand `V_n(μ(n) • [1/n]_F(f_n γ))` in Cartier's `p`-typicalization series. -/
private noncomputable def pTypicalTerm (F : FormalGroup R) [F.IsComm] (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R))
    (n : ℕ) (hn0 : n ≠ 0) (hcop : n.Coprime p) : F.Curve →+ F.Curve :=
  (F.verschiebungCurve n hn0).comp <|
    (zsmulAddGroupHom (ArithmeticFunction.moebius n)).comp <|
      (F.divNatCurve n (hcop.isUnit_natCast_of_prime hn0 hunit)).comp (F.frobeniusCurve n hn0)

private theorem pTypicalTerm_apply (F : FormalGroup R) [F.IsComm] (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R))
    (n : ℕ) (hn0 : n ≠ 0) (hcop : n.Coprime p) (γ : F.Curve) :
    pTypicalTerm F p hunit n hn0 hcop γ =
      F.verschiebungCurve n hn0
        (ArithmeticFunction.moebius n •
          F.divNatCurve n (hcop.isUnit_natCast_of_prime hn0 hunit) (F.frobeniusCurve n hn0 γ)) :=
  (rfl)

private theorem pTypicalTerm_one (F : FormalGroup R) [F.IsComm] (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    pTypicalTerm F p hunit 1 one_ne_zero (Nat.coprime_one_left p) γ = γ := by
  simp [pTypicalTerm_apply]

/-- Partial sum up to index `N` of Cartier's `p`-typicalization series. -/
private noncomputable def pTypicalApprox (F : FormalGroup R) [F.IsComm] (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) : ℕ → (F.Curve →+ F.Curve)
  | 0 => 0
  | N + 1 =>
    if hcop : (N + 1).Coprime p then
      pTypicalApprox F p hunit N + pTypicalTerm F p hunit (N + 1) (Nat.succ_ne_zero N) hcop
    else
      pTypicalApprox F p hunit N

private theorem pTypicalApprox_one (F : FormalGroup R) [F.IsComm] (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    pTypicalApprox F p hunit 1 γ = γ := by
  simp [pTypicalApprox, pTypicalTerm_one]

private theorem coeff_pTypicalApprox_succ_of_le (F : FormalGroup R) [F.IsComm] (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {k N : ℕ} (hk : k ≤ N) (γ : F.Curve) :
    PowerSeries.coeff k (pTypicalApprox F p hunit (N + 1) γ).toPowerSeries =
      PowerSeries.coeff k (pTypicalApprox F p hunit N γ).toPowerSeries := by
  simp only [pTypicalApprox]
  split_ifs with hcop
  · rw [AddMonoidHom.add_apply]
    exact Curve.coeff_add_eq_left_of_forall_lt_coeff_eq_zero _ _ (Nat.lt_succ_of_le hk)
      fun i hi ↦ F.coeff_verschiebungCurve_eq_zero_of_lt (Nat.succ_ne_zero N) hi _
  · rfl

private theorem coeff_pTypicalApprox_eq_of_le (F : FormalGroup R) [F.IsComm] (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {k N : ℕ} (hk : k ≤ N) (γ : F.Curve) :
    PowerSeries.coeff k (pTypicalApprox F p hunit N γ).toPowerSeries =
      PowerSeries.coeff k (pTypicalApprox F p hunit k γ).toPowerSeries := by
  induction N, hk using Nat.le_induction with
  | base => rfl
  | succ m hm ih => rw [coeff_pTypicalApprox_succ_of_le F p hunit hm, ih]

/-- Underlying curve of Cartier's `p`-typicalization operator `ε_p γ`. -/
private noncomputable def pTypicalCurveAux (F : FormalGroup R) [F.IsComm] (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) : F.Curve :=
  ⟨PowerSeries.mk fun k ↦ PowerSeries.coeff k (pTypicalApprox F p hunit k γ).toPowerSeries, by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
    simp [pTypicalApprox]⟩

private theorem coeff_pTypicalCurveAux (F : FormalGroup R) [F.IsComm] (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {k N : ℕ} (hk : k ≤ N) (γ : F.Curve) :
    PowerSeries.coeff k (pTypicalCurveAux F p hunit γ).toPowerSeries =
      PowerSeries.coeff k (pTypicalApprox F p hunit N γ).toPowerSeries := by
  rw [coeff_pTypicalApprox_eq_of_le F p hunit hk, pTypicalCurveAux, PowerSeries.coeff_mk]

/-- **Cartier's `p`-typicalization operator** `ε_p` on curves of a commutative formal group law `F`
over a commutative ring `R` in which every prime `q ≠ p` is invertible:

  `(ε_p γ)(T) = ∑_{gcd(n, p) = 1}^F μ(n) · V_n([1/n]_F(f_n γ))(T)`. -/
noncomputable def pTypicalCurve (F : FormalGroup R) [F.IsComm] (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) : F.Curve →+ F.Curve where
  toFun := pTypicalCurveAux F p hunit
  map_zero' := by
    ext k
    rw [coeff_pTypicalCurveAux F p hunit (le_refl k), (pTypicalApprox F p hunit k).map_zero,
      Curve.toPowerSeries_zero, map_zero]
  map_add' γ₁ γ₂ := by
    ext k
    rw [coeff_pTypicalCurveAux F p hunit (le_refl k), map_add]
    exact Curve.coeff_add_congr
      (fun i hi ↦ (coeff_pTypicalCurveAux F p hunit hi γ₁).symm)
      (fun i hi ↦ (coeff_pTypicalCurveAux F p hunit hi γ₂).symm)

private theorem coeff_pTypicalCurve_eq_coeff_pTypicalApprox (F : FormalGroup R) [F.IsComm] (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {k N : ℕ} (hk : k ≤ N) (γ : F.Curve) :
    PowerSeries.coeff k (F.pTypicalCurve p hunit γ).toPowerSeries =
      PowerSeries.coeff k (pTypicalApprox F p hunit N γ).toPowerSeries :=
  coeff_pTypicalCurveAux F p hunit hk γ

/-- Cartier's `p`-typicalization operator `ε_p` preserves the linear coefficient of every curve. -/
@[simp]
theorem coeff_one_pTypicalCurve (F : FormalGroup R) [F.IsComm] (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    PowerSeries.coeff 1 (F.pTypicalCurve p hunit γ).toPowerSeries =
      PowerSeries.coeff 1 γ.toPowerSeries := by
  rw [coeff_pTypicalCurve_eq_coeff_pTypicalApprox F p hunit (le_refl 1), pTypicalApprox_one]

private theorem map_pTypicalApprox (F : FormalGroup R) [F.IsComm] (φ : R →+* S) (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R))
    (hunitS : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : S)) (N : ℕ) (γ : F.Curve) :
    Curve.map φ (pTypicalApprox F p hunit N γ) =
      pTypicalApprox (F.map φ) p hunitS N (Curve.map φ γ) := by
  induction N with
  | zero => simp [pTypicalApprox]
  | succ N ih =>
    simp only [pTypicalApprox]
    split_ifs with hcop
    · simp only [AddMonoidHom.add_apply, map_add, ih, pTypicalTerm_apply,
        F.map_verschiebungCurve, map_zsmul, F.map_divNatCurve, F.map_frobeniusCurve]
    · exact ih

/-- Cartier's `p`-typicalization operator commutes with base change of the coefficient ring. -/
theorem map_pTypicalCurve (F : FormalGroup R) [F.IsComm] (φ : R →+* S) (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R))
    (hunitS : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : S)) (γ : F.Curve) :
    Curve.map φ (F.pTypicalCurve p hunit γ) =
      (F.map φ).pTypicalCurve p hunitS (Curve.map φ γ) := by
  ext k
  rw [Curve.toPowerSeries_map, PowerSeries.coeff_map,
    coeff_pTypicalCurve_eq_coeff_pTypicalApprox F p hunit (le_refl k),
    coeff_pTypicalCurve_eq_coeff_pTypicalApprox (F.map φ) p hunitS (le_refl k),
    ← map_pTypicalApprox F φ p hunit hunitS k γ, Curve.toPowerSeries_map, PowerSeries.coeff_map]

private theorem mapCurve_pTypicalApprox {F G : FormalGroup R} [F.IsComm] [G.IsComm]
    (f : TauCeti.FormalGroupHom F G) (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (N : ℕ) (γ : F.Curve) :
    f.mapCurve (pTypicalApprox F p hunit N γ) = pTypicalApprox G p hunit N (f.mapCurve γ) := by
  induction N with
  | zero => simp [pTypicalApprox]
  | succ N ih =>
    simp only [pTypicalApprox]
    split_ifs with hcop
    · simp only [AddMonoidHom.add_apply, map_add, ih, pTypicalTerm_apply,
        f.mapCurve_verschiebungCurve, map_zsmul, f.mapCurve_divNatCurve,
        f.mapCurve_frobeniusCurve]
    · exact ih

/-- Cartier's `p`-typicalization operator is natural with respect to homomorphisms of commutative
formal group laws. -/
theorem _root_.TauCeti.FormalGroupHom.mapCurve_pTypicalCurve {F G : FormalGroup R}
    [F.IsComm] [G.IsComm] (f : TauCeti.FormalGroupHom F G) (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    f.mapCurve (F.pTypicalCurve p hunit γ) = G.pTypicalCurve p hunit (f.mapCurve γ) := by
  ext k
  rw [coeff_pTypicalCurve_eq_coeff_pTypicalApprox G p hunit (le_refl k),
    ← mapCurve_pTypicalApprox f p hunit k γ, TauCeti.FormalGroupHom.toPowerSeries_mapCurve,
    TauCeti.FormalGroupHom.toPowerSeries_mapCurve]
  have hdvd : PowerSeries.X ^ (k + 1) ∣
      ((F.pTypicalCurve p hunit γ).toPowerSeries - (pTypicalApprox F p hunit k γ).toPowerSeries) :=
    PowerSeries.X_pow_dvd_iff.mpr fun i hi ↦ by
      rw [map_sub, coeff_pTypicalCurve_eq_coeff_pTypicalApprox F p hunit (Nat.le_of_lt_succ hi) γ,
        sub_self]
  have hsub := PowerSeries.X_pow_dvd_iff.mp
    (PowerSeries.X_pow_dvd_subst_sub_subst (Curve.constantCoeff_toPowerSeries _)
      (Curve.constantCoeff_toPowerSeries _) hdvd f.toPowerSeries) k (Nat.lt_succ_self k)
  rw [map_sub] at hsub
  exact sub_eq_zero.mp hsub

/-- Any `p`-typical curve (for prime `p`) is fixed by `ε_p`: for every `n > 1` coprime to `p`,
`f_n γ = 0`, so only the `n = 1` term survives in `ε_p γ`. -/
theorem pTypicalCurve_eq_self_of_isPTypical (F : FormalGroup R) [F.IsComm] {p : ℕ} (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {γ : F.Curve} (hγ : γ.IsPTypical p) :
    F.pTypicalCurve p hunit γ = γ := by
  have happrox : ∀ N : ℕ, 1 ≤ N → pTypicalApprox F p hunit N γ = γ := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => exact pTypicalApprox_one F p hunit γ
    | succ m hm ih =>
      simp only [pTypicalApprox]
      split_ifs with hcop
      · have hf0 : F.frobeniusCurve (m + 1) (Nat.succ_ne_zero m) γ = 0 :=
          (Curve.isPTypical_iff_frobeniusCurve_eq_zero_of_coprime hp).mp hγ
            (Nat.succ_ne_zero m) hcop (by omega)
        simp [AddMonoidHom.add_apply, ih, pTypicalTerm_apply, hf0]
      · exact ih
  ext k
  rcases eq_or_ne k 0 with rfl | hk0
  · simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  · rw [coeff_pTypicalCurve_eq_coeff_pTypicalApprox F p hunit (le_refl k),
      happrox k (Nat.pos_of_ne_zero hk0)]

private theorem coeff_substLogHom_pTypicalTerm [Algebra ℚ R] (F : FormalGroup R) [F.IsComm] (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R))
    (n : ℕ) (hn0 : n ≠ 0) (hcop : n.Coprime p) (m : ℕ) (γ : F.Curve) :
    PowerSeries.coeff m (substLogHom F (pTypicalTerm F p hunit n hn0 hcop γ)) =
      if n ∣ m then
        ArithmeticFunction.moebius n • PowerSeries.coeff m (substLogHom F γ)
      else 0 := by
  let hu := hcop.isUnit_natCast_of_prime hn0 hunit
  have hdiv : substLogHom F (F.divNatCurve n hu (F.frobeniusCurve n hn0 γ)) =
      PowerSeries.cartier R n 0 (substLogHom F γ) := by
    have hmul : (n : R) • substLogHom F (F.divNatCurve n hu (F.frobeniusCurve n hn0 γ)) =
        (n : R) • PowerSeries.cartier R n 0 (substLogHom F γ) := by
      rw [Nat.cast_smul_eq_nsmul, ← map_nsmul, F.nsmul_divNatCurve, substLogHom_apply,
        F.subst_frobeniusCurve_log n hn0 γ, substLogHom_apply]
    have hinv := congrArg ((hu.unit⁻¹ : Rˣ).val • ·) hmul
    simpa only [smul_smul, hu.val_inv_mul, one_smul] using hinv
  rw [pTypicalTerm_apply, substLogHom_apply, F.subst_verschiebungCurve_log, ← substLogHom_apply,
    map_zsmul, hdiv, map_zsmul, map_zsmul, PowerSeries.coeff_expand]
  split_ifs with hdvd
  · rw [PowerSeries.coeff_cartier, Nat.add_zero, Nat.mul_div_cancel' hdvd]
  · rw [smul_zero]

private theorem coeff_substLogHom_pTypicalApprox [Algebra ℚ R] (F : FormalGroup R) [F.IsComm]
    (p : ℕ) (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (N m : ℕ) (γ : F.Curve) :
    PowerSeries.coeff m (substLogHom F (pTypicalApprox F p hunit N γ)) =
      (∑ n ∈ (Finset.range (N + 1)).filter (fun n ↦ n ≠ 0 ∧ n.Coprime p ∧ n ∣ m),
        ArithmeticFunction.moebius n) • PowerSeries.coeff m (substLogHom F γ) := by
  induction N with
  | zero =>
    have hempty :
        (Finset.range 1).filter (fun n ↦ n ≠ 0 ∧ n.Coprime p ∧ n ∣ m) = ∅ := by
      ext n
      simp +contextual
    simp [pTypicalApprox, hempty]
  | succ N ih =>
    simp only [pTypicalApprox]
    split_ifs with hcop
    · rw [Finset.range_add_one, Finset.filter_insert, AddMonoidHom.add_apply, map_add, map_add, ih,
        coeff_substLogHom_pTypicalTerm F p hunit (N + 1) (Nat.succ_ne_zero N) hcop m γ]
      by_cases hdvd : (N + 1) ∣ m
      · have hmem : N + 1 ≠ 0 ∧ (N + 1).Coprime p ∧ N + 1 ∣ m :=
          ⟨Nat.succ_ne_zero N, hcop, hdvd⟩
        rw [ite_eq_left hdvd, ite_eq_left hmem, Finset.sum_insert (by simp), add_comm, add_zsmul]
      · have hnmem : ¬ (N + 1 ≠ 0 ∧ (N + 1).Coprime p ∧ N + 1 ∣ m) := fun h ↦ hdvd h.2.2
        rw [ite_eq_right hdvd, ite_eq_right hnmem, _root_.add_zero]
    · have hnmem : ¬ (N + 1 ≠ 0 ∧ (N + 1).Coprime p ∧ N + 1 ∣ m) := fun h ↦ hcop h.2.1
      rw [Finset.range_add_one, Finset.filter_insert, ite_eq_right hnmem, ih]

open Classical in
/-- **Logarithmic formula for Cartier's `p`-typicalization**: over a `ℚ`-algebra, for a prime `p`,
`log_F((ε_p γ)(T))` retains the `p`-power-degree coefficients of `log_F(γ(T))` and annihilates all
other coefficients. -/
theorem coeff_subst_pTypicalCurve_log [Algebra ℚ R] (F : FormalGroup R) [F.IsComm] {p : ℕ}
    (hp : p.Prime) (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) (m : ℕ) :
    PowerSeries.coeff m (PowerSeries.subst (F.pTypicalCurve p hunit γ).toPowerSeries F.log) =
      if ∃ k : ℕ, m = p ^ k then
        PowerSeries.coeff m (PowerSeries.subst γ.toPowerSeries F.log)
      else 0 := by
  rcases eq_or_ne m 0 with rfl | hm0
  · have hno : ¬ ∃ k : ℕ, 0 = p ^ k := fun ⟨k, hk⟩ ↦ pow_ne_zero k hp.ne_zero hk.symm
    rw [ite_eq_right hno, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact PowerSeries.constantCoeff_subst_eq_zero (Curve.constantCoeff_toPowerSeries _) _
      F.constantCoeff_log
  · have hdvd : PowerSeries.X ^ (m + 1) ∣
        ((F.pTypicalCurve p hunit γ).toPowerSeries -
          (pTypicalApprox F p hunit m γ).toPowerSeries) :=
      PowerSeries.X_pow_dvd_iff.mpr fun i hi ↦ by
        rw [map_sub, coeff_pTypicalCurve_eq_coeff_pTypicalApprox F p hunit (Nat.le_of_lt_succ hi) γ,
          sub_self]
    have hsub := PowerSeries.X_pow_dvd_iff.mp
      (PowerSeries.X_pow_dvd_subst_sub_subst (Curve.constantCoeff_toPowerSeries _)
        (Curve.constantCoeff_toPowerSeries _) hdvd F.log) m (Nat.lt_succ_self m)
    rw [map_sub] at hsub
    rw [sub_eq_zero.mp hsub, ← substLogHom_apply,
      coeff_substLogHom_pTypicalApprox F p hunit m m γ, substLogHom_apply]
    have hfinset : (Finset.range (m + 1)).filter (fun n ↦ n ≠ 0 ∧ n.Coprime p ∧ n ∣ m) =
        m.divisors.filter (·.Coprime p) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_divisors]
      exact ⟨fun ⟨_, _, hc, hd⟩ ↦ ⟨⟨hd, hm0⟩, hc⟩, fun ⟨⟨hd, _⟩, hc⟩ ↦
        ⟨Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hd),
          ne_of_gt (Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hm0)), hc, hd⟩⟩
    rw [hfinset, ArithmeticFunction.sum_divisors_filter_coprime_moebius hp hm0]
    split_ifs <;> simp

/-- **Cartier's theorem**: for a prime `p`, over any commutative ring in which every prime `q ≠ p`
is invertible, `ε_p γ` is `p`-typical for every curve `γ` on `F`. -/
theorem isPTypical_pTypicalCurve (F : FormalGroup R) [F.IsComm] {p : ℕ} (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    (F.pTypicalCurve p hunit γ).IsPTypical p := by
  let S₀ : Set ℕ := { q : ℕ | q.Prime ∧ q ≠ p }
  obtain ⟨A, Q, _, _, _, j, hj, hSA, F₀, _, γ₀, π, e, rfl⟩ :=
    Curve.exists_lift_of_isUnit_natCast F γ S₀ (fun _ hq ↦ hq.1.ne_zero)
      (fun q hq ↦ hunit q hq.1 hq.2)
  have hunitA : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : A) := fun q hq hne ↦ hSA q ⟨hq, hne⟩
  have hunitQ : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : Q) :=
    fun q hq _ ↦ TauCeti.isUnit_natCast_of_ne_zero hq.ne_zero
  have hQ : ((F₀.map j).pTypicalCurve p hunitQ (Curve.map j γ₀)).IsPTypical p := by
    rw [Curve.isPTypical_iff_coeff_subst_log_eq_zero hp]
    intro m hm
    rw [coeff_subst_pTypicalCurve_log (F₀.map j) hp hunitQ (Curve.map j γ₀) m,
      ite_eq_right (fun ⟨k, hk⟩ ↦ hm k hk)]
  have hA : (F₀.pTypicalCurve p hunitA γ₀).IsPTypical p := by
    rw [← Curve.isPTypical_map_iff hj, F₀.map_pTypicalCurve j p hunitA hunitQ γ₀]
    exact hQ
  rw [← e.toHom.mapCurve_pTypicalCurve p hunit, ← F₀.map_pTypicalCurve π p hunitA hunit γ₀]
  exact (hA.map π).mapCurve e.toHom

/-- A curve `γ` on `F` is fixed by `ε_p` (for prime `p`) if and only if `γ` is `p`-typical. -/
theorem pTypicalCurve_eq_self_iff (F : FormalGroup R) [F.IsComm] {p : ℕ} (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {γ : F.Curve} :
    F.pTypicalCurve p hunit γ = γ ↔ γ.IsPTypical p :=
  ⟨fun h ↦ h ▸ F.isPTypical_pTypicalCurve hp hunit γ,
    F.pTypicalCurve_eq_self_of_isPTypical hp hunit⟩

/-- **Idempotence of Cartier's `p`-typicalization operator**: `ε_p (ε_p γ) = ε_p γ`. -/
@[simp]
theorem pTypicalCurve_pTypicalCurve (F : FormalGroup R) [F.IsComm] {p : ℕ} (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    F.pTypicalCurve p hunit (F.pTypicalCurve p hunit γ) = F.pTypicalCurve p hunit γ :=
  F.pTypicalCurve_eq_self_of_isPTypical hp hunit (F.isPTypical_pTypicalCurve hp hunit γ)

/-- Cartier's `p`-typicalization operator `ε_p` annihilates `V_q γ` for every prime `q ≠ p`. -/
theorem pTypicalCurve_verschiebungCurve_of_prime_ne (F : FormalGroup R) [F.IsComm] {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hne : q ≠ p)
    (hunit : ∀ r : ℕ, r.Prime → r ≠ p → IsUnit (r : R)) (γ : F.Curve) :
    F.pTypicalCurve p hunit (F.verschiebungCurve q hq.ne_zero γ) = 0 := by
  let S₀ : Set ℕ := { r : ℕ | r.Prime ∧ r ≠ p }
  obtain ⟨A, Q, _, _, _, j, hj, hSA, F₀, _, γ₀, π, e, rfl⟩ :=
    Curve.exists_lift_of_isUnit_natCast F γ S₀ (fun _ hr ↦ hr.1.ne_zero)
      (fun r hr ↦ hunit r hr.1 hr.2)
  have hunitA : ∀ r : ℕ, r.Prime → r ≠ p → IsUnit (r : A) := fun r hr hne' ↦ hSA r ⟨hr, hne'⟩
  have hunitQ : ∀ r : ℕ, r.Prime → r ≠ p → IsUnit (r : Q) :=
    fun r hr _ ↦ TauCeti.isUnit_natCast_of_ne_zero hr.ne_zero
  have hQ : (F₀.map j).pTypicalCurve p hunitQ
      ((F₀.map j).verschiebungCurve q hq.ne_zero (Curve.map j γ₀)) = 0 := by
    apply (F₀.map j).logIso.curveEquiv.injective
    rw [map_zero]
    ext m
    simp only [TauCeti.FormalGroupIso.curveEquiv_apply, logIso_toHom,
      TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries, Curve.toPowerSeries_zero,
      map_zero, coeff_subst_pTypicalCurve_log (F₀.map j) hp hunitQ _ m]
    split_ifs with hpow
    · obtain ⟨k, rfl⟩ := hpow
      rw [(F₀.map j).subst_verschiebungCurve_log q hq.ne_zero]
      have hndvd : ¬ q ∣ p ^ k := fun hdvd ↦
        hne ((hp.dvd_iff_eq hq.ne_one).mp (hq.dvd_of_dvd_pow hdvd)).symm
      exact PowerSeries.coeff_expand_of_not_dvd q hq.ne_zero _ hndvd
    · rfl
  have hA : F₀.pTypicalCurve p hunitA (F₀.verschiebungCurve q hq.ne_zero γ₀) = 0 := by
    apply Curve.map_injective hj
    rw [map_zero, F₀.map_pTypicalCurve j p hunitA hunitQ, F₀.map_verschiebungCurve j q hq.ne_zero]
    exact hQ
  rw [← e.toHom.mapCurve_verschiebungCurve q hq.ne_zero, ← e.toHom.mapCurve_pTypicalCurve p hunit,
    ← F₀.map_verschiebungCurve π q hq.ne_zero, ← F₀.map_pTypicalCurve π p hunitA hunit, hA,
    map_zero, map_zero]

end PTypicalCurve

/-! ### Canonical `p`-typical coordinate change on formal group laws -/

/-- **Quillen's canonical `p`-typical coordinate** on a commutative formal group law `F` over a
ring `R` inverting primes `q ≠ p`: the compositional inverse of the strict curve `ε_p(T)`.
Transporting `F` along `F.pTypicalCoord p hunit` produces a canonical strictly isomorphic
`p`-typical formal group law `F.pTypicalCoord p hunit • F`. -/
noncomputable def pTypicalCoord (F : FormalGroup R) [F.IsComm] (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) : TauCeti.FormalCoordinate R :=
  (⟨(F.pTypicalCurve p hunit F.tautologicalCurve).toPowerSeries,
    Curve.constantCoeff_toPowerSeries _,
    by simp⟩ : TauCeti.FormalCoordinate R)⁻¹

@[simp]
theorem inv_pTypicalCoord_toPowerSeries (F : FormalGroup R) [F.IsComm] (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalCoord p hunit)⁻¹.toPowerSeries =
      (F.pTypicalCurve p hunit F.tautologicalCurve).toPowerSeries := by
  simp [pTypicalCoord]

@[simp]
theorem linearCoeff_pTypicalCoord (F : FormalGroup R) [F.IsComm] (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    TauCeti.FormalCoordinate.linearCoeff (F.pTypicalCoord p hunit) = 1 := by
  rw [← inv_eq_one, ← map_inv, ← Units.val_eq_one, TauCeti.FormalCoordinate.val_linearCoeff,
    inv_pTypicalCoord_toPowerSeries, coeff_one_pTypicalCurve, toPowerSeries_tautologicalCurve,
    PowerSeries.coeff_one_X]

instance isStrict_smulIso_pTypicalCoord (F : FormalGroup R) [F.IsComm] (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (smulIso (F.pTypicalCoord p hunit) F).IsStrict :=
  (isStrict_smulIso_iff _ F).mpr (F.linearCoeff_pTypicalCoord p hunit)

theorem map_pTypicalCoord (F : FormalGroup R) [F.IsComm] (φ : R →+* S) (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R))
    (hunitS : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : S)) :
    TauCeti.FormalCoordinate.map φ (F.pTypicalCoord p hunit) =
      (F.map φ).pTypicalCoord p hunitS := by
  apply inv_injective
  rw [← map_inv]
  ext : 1
  rw [TauCeti.FormalCoordinate.toPowerSeries_map, inv_pTypicalCoord_toPowerSeries,
    inv_pTypicalCoord_toPowerSeries, ← Curve.toPowerSeries_map,
    F.map_pTypicalCurve φ p hunit hunitS, F.map_tautologicalCurve]

/-- **Cartier–Quillen `p`-typicalization theorem**: for a prime `p`, transporting any commutative
formal group law `F` (over a ring inverting primes `q ≠ p`) along `F.pTypicalCoord p hunit`
produces a `p`-typical formal group law. -/
theorem isPTypical_pTypicalCoord_smul (F : FormalGroup R) [F.IsComm] {p : ℕ} (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    (F.pTypicalCoord p hunit • F).IsPTypical p := by
  rw [isPTypical_smul_iff]
  have hcurve :
      (⟨(F.pTypicalCoord p hunit)⁻¹.toPowerSeries,
        (F.pTypicalCoord p hunit)⁻¹.constantCoeff_toPowerSeries⟩ : F.Curve) =
        F.pTypicalCurve p hunit F.tautologicalCurve :=
    Curve.ext (F.inv_pTypicalCoord_toPowerSeries p hunit)
  rw [hcurve]
  exact F.isPTypical_pTypicalCurve hp hunit F.tautologicalCurve

/-- For a prime `p`, `F.pTypicalCoord p hunit` is the identity coordinate `1` if and only if `F` is
already `p`-typical. -/
theorem pTypicalCoord_eq_one_iff (F : FormalGroup R) [F.IsComm] {p : ℕ} (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    F.pTypicalCoord p hunit = 1 ↔ F.IsPTypical p := by
  rw [← inv_eq_one, TauCeti.FormalCoordinate.ext_iff, inv_pTypicalCoord_toPowerSeries,
    TauCeti.FormalCoordinate.toPowerSeries_one, ← toPowerSeries_tautologicalCurve F,
    ← Curve.ext_iff, F.pTypicalCurve_eq_self_iff hp hunit, IsPTypical]

open Classical in
/-- Over a `ℚ`-algebra, the formal logarithm of the canonical `p`-typicalization
`F.pTypicalCoord p hunit • F` retains the `pᵏ`-degree coefficients of `log_F` and kills all
others. -/
theorem coeff_log_pTypicalCoord_smul [Algebra ℚ R] (F : FormalGroup R) [F.IsComm] {p : ℕ}
    (hp : p.Prime) (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (m : ℕ) :
    PowerSeries.coeff m (F.pTypicalCoord p hunit • F).log =
      if ∃ k : ℕ, m = p ^ k then PowerSeries.coeff m F.log else 0 := by
  rw [F.log_smul (F.pTypicalCoord p hunit), F.linearCoeff_pTypicalCoord p hunit,
    Units.val_one, one_smul, F.inv_pTypicalCoord_toPowerSeries p hunit,
    F.coeff_subst_pTypicalCurve_log hp hunit F.tautologicalCurve m,
    toPowerSeries_tautologicalCurve, PowerSeries.X_subst]

end FormalGroup
