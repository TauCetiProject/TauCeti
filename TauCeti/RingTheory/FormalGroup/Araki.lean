/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Typical
import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Araki coefficients of the p-series

For a commutative formal group law, take successive coefficients of the residual after
subtracting the preceding terms of its `p`-series by the formal group law. For a `p`-typical
law over a ring in which all primes other than `p` are units, this gives the full Araki
expansion of the `p`-series as a formal-group sum in the degrees `p ^ i`. The formula
is stated coefficientwise using finite sums, which specify all coefficients of the infinite sum.

## References

* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A2,
  equations (A2.2.2) and (A2.2.4).
-/

public section

open Finset
open PowerSeries (coeff)

namespace FormalGroup

variable {R S : Type*} [CommRing R] [CommRing S]

private noncomputable def arakiPartialSum (F : FormalGroup R) [F.IsComm] {p : ℕ}
    (hp : p.Prime) : ℕ → F.Curve
  | 0 => 0
  | n + 1 =>
      let s := arakiPartialSum F hp n
      s + F.monomialCurve (p ^ n) (pow_ne_zero n hp.ne_zero)
        (coeff (p ^ n) (p • F.tautologicalCurve - s).toPowerSeries)

/-- The Araki coefficient in degree `p ^ n`, obtained from the residual of the `p`-series
after subtracting the formal-group sum of the previous terms. -/
noncomputable def arakiCoeff (F : FormalGroup R) [F.IsComm] {p : ℕ} (hp : p.Prime) (n : ℕ) : R :=
  coeff (p ^ n) (p • F.tautologicalCurve - F.arakiPartialSum hp n).toPowerSeries

variable (F : FormalGroup R) [F.IsComm] {p : ℕ} (hp : p.Prime)

private theorem arakiPartialSum_succ (n : ℕ) :
    F.arakiPartialSum hp (n + 1) = F.arakiPartialSum hp n +
      F.monomialCurve (p ^ n) (pow_ne_zero n hp.ne_zero) (F.arakiCoeff hp n) := by
  rw [arakiPartialSum, arakiCoeff]

private theorem arakiPartialSum_eq_sum (n : ℕ) :
    F.arakiPartialSum hp n =
      ∑ j ∈ range n, F.monomialCurve (p ^ j) (pow_ne_zero j hp.ne_zero) (F.arakiCoeff hp j) := by
  induction n with
  | zero => simp [arakiPartialSum]
  | succ n ih => rw [arakiPartialSum_succ, sum_range_succ, ih]

/-- The first Araki coefficient is the linear coefficient of the `p`-series, namely `p`. -/
@[simp]
theorem arakiCoeff_zero : F.arakiCoeff hp 0 = (p : R) := by
  simp [arakiCoeff, arakiPartialSum, Curve.toPowerSeries_nsmul]

private theorem map_arakiPartialSum (φ : R →+* S) (n : ℕ) :
    Curve.map φ (F.arakiPartialSum hp n) = (F.map φ).arakiPartialSum hp n := by
  induction n with
  | zero => simp [arakiPartialSum]
  | succ n ih =>
    simp only [arakiPartialSum_succ, map_add, ih, map_monomialCurve, arakiCoeff,
      ← PowerSeries.coeff_map, ← Curve.toPowerSeries_map, map_sub, map_nsmul,
      map_tautologicalCurve]

/-- Araki coefficients commute with base change. -/
@[simp]
theorem map_arakiCoeff (φ : R →+* S) (n : ℕ) :
    φ (F.arakiCoeff hp n) = (F.map φ).arakiCoeff hp n := by
  simp only [arakiCoeff, ← PowerSeries.coeff_map, ← Curve.toPowerSeries_map, map_sub, map_nsmul,
    map_tautologicalCurve, map_arakiPartialSum]

/-- The coefficient recursion for the formal-group expansion of the `p`-series. -/
theorem arakiCoeff_eq_coeff_sub_sum (n : ℕ) :
    F.arakiCoeff hp n = coeff (p ^ n)
      (p • F.tautologicalCurve -
        ∑ j ∈ range n, F.monomialCurve (p ^ j) (pow_ne_zero j hp.ne_zero)
          (F.arakiCoeff hp j)).toPowerSeries := by
  rw [arakiCoeff, arakiPartialSum_eq_sum]

private theorem isPTypical_arakiPartialSum (hF : F.IsPTypical p) (n : ℕ) :
    (F.arakiPartialSum hp n).IsPTypical p := by
  induction n with
  | zero => simpa only [arakiPartialSum] using Curve.IsPTypical.zero (F := F) p
  | succ n ih =>
    rw [arakiPartialSum_succ]
    exact ih.add (hF.monomialCurve_pow hp n _)

private theorem coeff_arakiResidual_succ_of_le (n : ℕ)
    (h : ∀ k < p ^ n,
      coeff k (p • F.tautologicalCurve - F.arakiPartialSum hp n).toPowerSeries = 0)
    {k : ℕ} (hk : k ≤ p ^ n) :
    coeff k (p • F.tautologicalCurve - F.arakiPartialSum hp (n + 1)).toPowerSeries = 0 := by
  rw [arakiPartialSum_succ, ← sub_sub]
  let t := F.monomialCurve (p ^ n) (pow_ne_zero n hp.ne_zero) (F.arakiCoeff hp n)
  have ht (i : ℕ) (hi : i ≤ k) :
      coeff i (p • F.tautologicalCurve - F.arakiPartialSum hp n).toPowerSeries =
        coeff i t.toPowerSeries := by
    rcases (hi.trans hk).lt_or_eq with hil | rfl
    · simp [t, h i hil, PowerSeries.coeff_X_pow, hil.ne]
    · simp [t, arakiCoeff]
  rw [Curve.coeff_sub_congr ht (fun _ _ ↦ rfl), sub_self, Curve.toPowerSeries_zero, map_zero]

private theorem coeff_arakiResidual_eq_zero (hF : F.IsPTypical p)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (n : ℕ) :
    ∀ k < p ^ n,
      coeff k (p • F.tautologicalCurve - F.arakiPartialSum hp n).toPowerSeries = 0 := by
  induction n with
  | zero =>
    intro k hk
    simp only [pow_zero, Nat.lt_one_iff] at hk
    subst k
    exact Curve.coeff_zero_toPowerSeries _
  | succ n ih =>
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ihk =>
      intro hk
      by_cases hle : k ≤ p ^ n
      · exact F.coeff_arakiResidual_succ_of_le hp n ih hle
      have hpower (j : ℕ) : k ≠ p ^ j := by
        intro he
        rcases le_or_gt j n with hj | hj
        · exact hle (he.le.trans (Nat.pow_le_pow_right hp.pos hj))
        · exact (not_le_of_gt hk)
            ((Nat.pow_le_pow_right hp.pos (Nat.succ_le_of_lt hj)).trans he.ge)
      have hδ := (hF.tautologicalCurve.nsmul p).sub (F.isPTypical_arakiPartialSum hp hF (n + 1))
      exact hδ.coeff_eq_zero_of_forall_lt hunit hpower
        fun i hi ↦ ihk i hi (hi.trans hk)

/-- **Araki's `p`-series formula.** In degrees below `p ^ n`, the `p`-series is the sum
in `F` of the monomials `a_j X ^ (p ^ j)` for `j < n`, where `a_j` are the Araki
coefficients of `F`. -/
theorem coeff_nsmulSeries_eq_sum_arakiCoeff (hF : F.IsPTypical p)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {n k : ℕ} (hk : k < p ^ n) :
    coeff k (F.nsmulSeries p) = coeff k
      (∑ j ∈ range n, F.monomialCurve (p ^ j) (pow_ne_zero j hp.ne_zero)
        (F.arakiCoeff hp j)).toPowerSeries := by
  rw [← F.arakiPartialSum_eq_sum hp]
  let s := F.arakiPartialSum hp n
  have h := Curve.coeff_add_eq_left_of_forall_lt_coeff_eq_zero s (p • F.tautologicalCurve - s)
    hk (F.coeff_arakiResidual_eq_zero hp hF hunit n)
  rw [add_sub_cancel] at h
  rwa [Curve.toPowerSeries_nsmul, toPowerSeries_tautologicalCurve, PowerSeries.X_subst] at h

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

end FormalGroup
