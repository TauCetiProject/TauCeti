/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Typical.Expansion
import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Araki coefficients of the p-series

For a commutative formal group law, take successive coefficients of the residual after
subtracting the preceding terms of its `p`-series by the formal group law. For a `p`-typical
law over a ring in which all primes other than `p` are units, this gives the full Araki
expansion of the `p`-series as a formal-group sum in the degrees `p ^ i`. The formula
is stated coefficientwise using finite sums, which specify all coefficients of the infinite sum.

Over a `ℚ`-algebra the Araki coefficients are triangular in the logarithm: `a_n` is
`(p - p ^ (p ^ n)) ℓ_n` plus a function of `ℓ_k` and `a_k` for `k < n`, where `ℓ_k` is the
degree-`p ^ k` coefficient of the logarithm (`FormalGroup.arakiCoeff_sub_arakiCoeff`).

## References

* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A2,
  equations (A2.2.2) and (A2.2.4).
-/

public section

open Finset
open PowerSeries (coeff)

namespace FormalGroup

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The Araki coefficient in degree `p ^ n`, obtained from the residual of the `p`-series
after subtracting the formal-group sum of the previous terms: the `p`-typical expansion coefficients
of the curve `[p]_F(X)`. -/
noncomputable def arakiCoeff (F : FormalGroup R) {p : ℕ} (hp : p.Prime) (n : ℕ) : R :=
  (p • F.tautologicalCurve).pTypicalCoeff hp.ne_zero n

variable (F : FormalGroup R) {p : ℕ} (hp : p.Prime)

/-- The Araki coefficients are the `p`-typical expansion coefficients of the `p`-series. -/
theorem arakiCoeff_eq_pTypicalCoeff (n : ℕ) :
    F.arakiCoeff hp n = (p • F.tautologicalCurve).pTypicalCoeff hp.ne_zero n := (rfl)

/-- The first Araki coefficient is the linear coefficient of the `p`-series, namely `p`. -/
@[simp]
theorem arakiCoeff_zero : F.arakiCoeff hp 0 = (p : R) := by
  simp [arakiCoeff_eq_pTypicalCoeff, Curve.toPowerSeries_nsmul]

/-- Araki coefficients commute with base change. -/
@[simp]
theorem map_arakiCoeff (φ : R →+* S) (n : ℕ) :
    φ (F.arakiCoeff hp n) = (F.map φ).arakiCoeff hp n := by
  simp only [arakiCoeff_eq_pTypicalCoeff, Curve.map_pTypicalCoeff, map_nsmul,
    map_tautologicalCurve]

variable [F.IsComm]

/-- The coefficient recursion for the formal-group expansion of the `p`-series. -/
theorem arakiCoeff_eq_coeff_sub_sum (n : ℕ) :
    F.arakiCoeff hp n = coeff (p ^ n)
      (p • F.tautologicalCurve -
        ∑ j ∈ range n, F.monomialCurve (p ^ j) (pow_ne_zero j hp.ne_zero)
          (F.arakiCoeff hp j)).toPowerSeries :=
  Curve.pTypicalCoeff_eq_coeff_sub_sum _ _ n

/-- **Araki's `p`-series formula.** In degrees below `p ^ n`, the `p`-series is the sum
in `F` of the monomials `a_j X ^ (p ^ j)` for `j < n`, where `a_j` are the Araki
coefficients of `F`. -/
theorem coeff_nsmulSeries_eq_sum_arakiCoeff (hF : F.IsPTypical p)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {n k : ℕ} (hk : k < p ^ n) :
    coeff k (F.nsmulSeries p) = coeff k
      (∑ j ∈ range n, F.monomialCurve (p ^ j) (pow_ne_zero j hp.ne_zero)
        (F.arakiCoeff hp j)).toPowerSeries := by
  simp only [arakiCoeff_eq_pTypicalCoeff,
    ← (hF.tautologicalCurve.nsmul p).coeff_eq_coeff_sum_pTypicalCoeff hF hp hunit hk,
    Curve.toPowerSeries_nsmul, toPowerSeries_tautologicalCurve, PowerSeries.X_subst]

/-- **Araki's logarithm recursion.** Writing `ℓ_i` for the degree-`p ^ i` coefficient
of the logarithm and `a_i` for the Araki coefficients, this is
`p * ℓ_n = ∑_{j = 0}^n ℓ_(n-j) * a_j ^ (p ^ (n-j))`. -/
theorem natCast_mul_coeff_log_eq_sum_arakiCoeff [Algebra ℚ R] (hF : F.IsPTypical p) (n : ℕ) :
    (p : R) * coeff (p ^ n) F.log =
      ∑ j ∈ range (n + 1), coeff (p ^ (n - j)) F.log * F.arakiCoeff hp j ^ (p ^ (n - j)) := by
  let L : F.Curve →+ PowerSeries R := Curve.additiveToPowerSeriesHom.comp F.logHom.mapCurve
  have hL (γ : F.Curve) : L γ = PowerSeries.subst γ.toPowerSeries F.log := by
    rw [AddMonoidHom.comp_apply, Curve.additiveToPowerSeriesHom_apply,
      TauCeti.FormalGroupHom.toPowerSeries_mapCurve, logHom_toPowerSeries]
  let t := p • F.tautologicalCurve
  let m (j : ℕ) := F.monomialCurve (p ^ j) (pow_ne_zero j hp.ne_zero) (F.arakiCoeff hp j)
  have ht : t.toPowerSeries = F.nsmulSeries p := by
    rw [Curve.toPowerSeries_nsmul, toPowerSeries_tautologicalCurve, PowerSeries.X_subst]
  have hunit (q : ℕ) (hq : q.Prime) (_ : q ≠ p) : IsUnit (q : R) := by
    have hu : IsUnit (q : ℚ) := isUnit_iff_ne_zero.mpr (by exact_mod_cast hq.ne_zero)
    simpa only [map_natCast] using hu.map (algebraMap ℚ R)
  have h : coeff (p ^ n) (L t) = coeff (p ^ n) (L (∑ j ∈ range (n + 1), m j)) := by
    simp only [L, AddMonoidHom.comp_apply, Curve.additiveToPowerSeriesHom_apply]
    apply TauCeti.FormalGroupHom.coeff_mapCurve_congr
    intro i hi
    rw [ht]
    exact F.coeff_nsmulSeries_eq_sum_arakiCoeff hp hF hunit
      (hi.trans_lt (Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self n)))
  rw [hL, ht, subst_nsmulSeries_log, map_nsmul, nsmul_eq_mul, map_sum, map_sum] at h
  refine h.trans (sum_congr rfl fun j hj ↦ ?_)
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
  have hjp : p ^ j ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hs : (PowerSeries.expand (p ^ j) hjp
      (PowerSeries.rescale (F.arakiCoeff hp j) F.log)) =
      PowerSeries.subst (m j).toPowerSeries F.log := by
    simp only [PowerSeries.expand_apply, PowerSeries.rescale_eq_subst,
      PowerSeries.subst_comp_subst_apply (.smul_X' _) (.X_pow hjp), m, toPowerSeries_monomialCurve,
      PowerSeries.subst_smul (.X_pow hjp), PowerSeries.subst_X (.X_pow hjp)]
  have hpow : p ^ n = p ^ j * p ^ (n - j) := by rw [← pow_add, Nat.add_sub_of_le hjn]
  rw [hL, ← hs, hpow, PowerSeries.coeff_expand_mul, PowerSeries.coeff_rescale, mul_comm]


/-- **The Araki coefficients are triangular in the logarithm.** Let `F` and `G` be `p`-typical laws
over a `ℚ`-algebra whose logarithms agree in the degrees `p ^ k` for `k < n`. Then
`a_n(F) - a_n(G) = (p - p ^ (p ^ n)) (ℓ_n(F) - ℓ_n(G))`, where `ℓ_n` is the degree-`p ^ n`
coefficient of the logarithm. In particular `a_n(F) = a_n(G)` when the logarithms also agree in
degree `p ^ n`. -/
theorem arakiCoeff_sub_arakiCoeff [Algebra ℚ R] (hF : F.IsPTypical p) (G : FormalGroup R)
    [G.IsComm] (hG : G.IsPTypical p) {n : ℕ}
    (h : ∀ k < n, coeff (p ^ k) F.log = coeff (p ^ k) G.log) :
    F.arakiCoeff hp n - G.arakiCoeff hp n =
      ((p : R) - (p : R) ^ p ^ n) * (coeff (p ^ n) F.log - coeff (p ^ n) G.log) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | m
    · simp
    -- split off the terms `j = m + 1` and `j = 0` of Araki's logarithm recursion
    have key (H : FormalGroup R) [H.IsComm] (hH : H.IsPTypical p) :
        ((p : R) - (p : R) ^ p ^ (m + 1)) * coeff (p ^ (m + 1)) H.log = H.arakiCoeff hp (m + 1) +
          ∑ j ∈ range m, coeff (p ^ (m - j)) H.log * H.arakiCoeff hp (j + 1) ^ p ^ (m - j) := by
      have e := H.natCast_mul_coeff_log_eq_sum_arakiCoeff hp hH (m + 1)
      rw [sum_range_succ, sum_range_succ'] at e
      simp only [Nat.sub_self, pow_zero, coeff_one_log, pow_one, one_mul, Nat.sub_zero,
        arakiCoeff_zero, Nat.add_sub_add_right] at e
      linear_combination e
    -- the lower Araki coefficients agree by induction
    have ha (j : ℕ) (hj : j ≤ m) : F.arakiCoeff hp j = G.arakiCoeff hp j := by
      have := ih j (by omega) fun k hk ↦ h k (by omega)
      rwa [h j (by omega), sub_self, mul_zero, sub_eq_zero] at this
    have hs : ∑ j ∈ range m, coeff (p ^ (m - j)) F.log * F.arakiCoeff hp (j + 1) ^ p ^ (m - j) =
        ∑ j ∈ range m, coeff (p ^ (m - j)) G.log * G.arakiCoeff hp (j + 1) ^ p ^ (m - j) :=
      sum_congr rfl fun j hj ↦ by
        rw [h _ (by omega), ha _ (by have := mem_range.1 hj; omega)]
    linear_combination key G hG - key F hF - hs

end FormalGroup
