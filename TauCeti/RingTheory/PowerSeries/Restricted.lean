/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.GaussNorm
public import Mathlib.RingTheory.PowerSeries.Restricted
public import Mathlib.RingTheory.PowerSeries.Trunc
public import TauCeti.Analysis.Asymptotics.Lemmas

/-!
# Restricted power series and their coefficient algebra

Mathlib's `PowerSeries.IsRestricted` asks the weighted coefficient norms of a power series to
tend to zero. A series whose coefficients vanish in every degree past some bound — a polynomial —
satisfies that condition at every radius, and a series restricted at one radius is restricted at
every smaller one. Without any ultrametric hypothesis, bounded weighted coefficients at one
radius make a series restricted at every strictly smaller radius, and products of series
restricted at one radius are restricted at every strictly smaller radius. Over an ultrametric
normed commutative ring, constant series give the restricted subring its coefficient algebra
structure. The polynomial inclusion is an algebra homomorphism;
it induces the polynomial-to-series comparisons used in Weierstrass division and its quotients.

## Main results

* `TauCeti.PowerSeries.isRestricted_of_forall_coeff_eq_zero`: a series with a vanishing tail is
  restricted at every radius.
* `TauCeti.PowerSeries.isRestricted_of_abs_le`: restrictedness passes to smaller radii, and
  `TauCeti.PowerSeries.isRestrictedSubring_le_of_abs_le` is the resulting containment of subrings.
* `TauCeti.PowerSeries.isRestricted_polynomial`: every polynomial is restricted.
* `PowerSeries.HasGaussNorm.isRestricted_of_abs_lt`: bounded weighted coefficients at `c'` give
  restrictedness at every `c` with `|c| < c'`.
* `PowerSeries.IsRestricted.mul_of_abs_lt`: over any normed ring, a product of series restricted
  at `c'` is restricted at every `c` with `|c| < |c'|`.
* `TauCeti.PowerSeries.not_isRestricted_mk_pow`: for `a ≠ 0` and a multiplicative norm, `∑ aⁿ Xⁿ`
  is not restricted at the radius `‖a‖⁻¹`.
* `PowerSeries.IsRestricted.rescale`: if `f(X)` is restricted at `‖a‖ * c`, then `f(aX)`
  is restricted at `c`.
* `TauCeti.PowerSeries.polynomialToRestricted`: the polynomial inclusion as an algebra map.
-/

public section

namespace TauCeti.PowerSeries

variable {R : Type*} [NormedRing R] {c : ℝ} {f : PowerSeries R}

/-- A power series whose coefficients vanish in every degree `≥ n` is restricted at every radius:
its weighted coefficient norms are eventually zero. Such a series is a polynomial of degree less
than `n`. -/
theorem isRestricted_of_forall_coeff_eq_zero {n : ℕ}
    (hf : ∀ m, n ≤ m → f.coeff m = 0) : f.IsRestricted c := by
  rw [PowerSeries.isRestricted_iff']
  have h : ∀ᶠ m in Filter.atTop, (0 : ℝ) = ‖f.coeff m‖ * c ^ m := by
    filter_upwards [Filter.eventually_ge_atTop n] with m hm
    simp [hf m hm]
  exact Filter.Tendsto.congr' h tendsto_const_nhds

/-- **Restrictedness passes to smaller radii.** If the weighted coefficient norms of `f` tend to
zero at the radius `c'`, they do so at every radius `c` with `|c| ≤ |c'|`, being dominated by the
former. -/
theorem isRestricted_of_abs_le {c' : ℝ} (hf : f.IsRestricted c') (h : |c| ≤ |c'|) :
    f.IsRestricted c := by
  rw [← PowerSeries.isRestricted_abs_iff, PowerSeries.isRestricted_iff'] at hf ⊢
  refine squeeze_zero (fun n ↦ by positivity) (fun n ↦ ?_) hf
  gcongr

/-- Over an ultrametric ring, the subring of series restricted at `c'` lies in the subring of
series restricted at any `c` with `|c| ≤ |c'|`. -/
theorem isRestrictedSubring_le_of_abs_le [IsUltrametricDist R] {c' : ℝ} (h : |c| ≤ |c'|) :
    PowerSeries.IsRestricted.subring (R := R) c' ≤ PowerSeries.IsRestricted.subring c :=
  fun _ hf ↦ isRestricted_of_abs_le hf h

/-- Every polynomial is restricted at every radius. -/
theorem isRestricted_polynomial (p : Polynomial R) : (p : PowerSeries R).IsRestricted c :=
  isRestricted_of_forall_coeff_eq_zero (n := p.natDegree + 1) fun m hm ↦ by
    rw [Polynomial.coeff_coe]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

/-- **Rescaling changes the radius.** If `f(X)` is restricted at the radius `‖a‖ * c`, then
`f(aX)` is restricted at the radius `c`. No multiplicativity of the norm is needed: the weighted
coefficient norms of `f(aX)` are eventually dominated by those of `f`. -/
theorem _root_.PowerSeries.IsRestricted.rescale {R : Type*} [NormedCommRing R] {c : ℝ}
    {f : PowerSeries R} {a : R}
    (hf : f.IsRestricted (‖a‖ * c)) : (PowerSeries.rescale a f).IsRestricted c := by
  rw [← PowerSeries.isRestricted_abs_iff, PowerSeries.isRestricted_iff'] at hf ⊢
  refine squeeze_zero' (.of_forall fun n ↦ by positivity) ?_ hf
  filter_upwards [eventually_norm_pow_le a] with n hn
  rw [PowerSeries.coeff_rescale, abs_mul, abs_norm, mul_pow, ← mul_assoc, mul_comm _ (‖a‖ ^ n)]
  gcongr
  exact (norm_mul_le _ _).trans (by gcongr)

/-- For `a ≠ 0` over a ring with multiplicative norm, the geometric series `∑ aⁿ Xⁿ` is not
restricted at the radius `‖a‖⁻¹`: all its weighted coefficient norms there equal `1`. -/
theorem not_isRestricted_mk_pow [NormMulClass R] {a : R} (ha : a ≠ 0) :
    ¬(PowerSeries.mk fun n ↦ a ^ n).IsRestricted ‖a‖⁻¹ := by
  intro hf
  have : Nontrivial R := ⟨⟨a, 0, ha⟩⟩
  have : NormOneClass R := NormMulClass.toNormOneClass
  have h := (PowerSeries.isRestricted_iff' _ _).mp hf
  simp only [PowerSeries.coeff_mk, norm_pow, ← mul_pow, mul_inv_cancel₀ (norm_ne_zero_iff.mpr ha),
    one_pow] at h
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h)

section Algebra

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {c : ℝ}

/-- The coefficient algebra structure on restricted power series, given by constant series. -/
noncomputable instance instAlgebraIsRestrictedSubring :
    Algebra R (PowerSeries.IsRestricted.subring (R := R) c) :=
  (PowerSeries.C.codRestrict _ (PowerSeries.isRestricted_C c)).toAlgebra

/-- The coefficient map of the restricted-series algebra is the constant series map. -/
@[simp]
theorem coe_algebraMap_isRestrictedSubring (a : R) :
    (algebraMap R (PowerSeries.IsRestricted.subring (R := R) c) a : PowerSeries R) =
      PowerSeries.C a := (rfl)

/-- The inclusion of polynomials into the algebra of restricted power series. -/
noncomputable def polynomialToRestricted (c : ℝ) :
    Polynomial R →ₐ[R] PowerSeries.IsRestricted.subring (R := R) c where
  __ := Polynomial.coeToPowerSeries.ringHom.codRestrict _ isRestricted_polynomial
  commutes' a := Subtype.ext (Polynomial.coe_C a)

/-- The polynomial inclusion has the usual underlying power series. -/
@[simp]
theorem coe_polynomialToRestricted (p : Polynomial R) :
    (polynomialToRestricted c p : PowerSeries R) = p := (rfl)

/-- A restricted series whose coefficients vanish from degree `s` onward is the polynomial
inclusion of its `s`-truncation. -/
theorem polynomialToRestricted_trunc_eq_of_coeff_eq_zero {s : ℕ}
    (r : PowerSeries.IsRestricted.subring (R := R) c)
    (hr : ∀ n, s ≤ n → (r : PowerSeries R).coeff n = 0) :
    polynomialToRestricted c (PowerSeries.trunc s (r : PowerSeries R)) = r := by
  apply Subtype.ext
  ext n
  simp only [coe_polynomialToRestricted, Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split_ifs with hn
  · rfl
  · exact (hr n (by omega)).symm

end Algebra

end TauCeti.PowerSeries

namespace PowerSeries

open Filter
open scoped Topology

variable {R : Type*} [NormedRing R] {c c' : ℝ} {f g : PowerSeries R}

/-- **Bounded weighted coefficients give restrictedness at smaller radii.** If the weighted
coefficient norms `‖aₙ‖ c'ⁿ` are bounded, then `‖aₙ‖ cⁿ → 0` for every `c` with `|c| < c'`, being
dominated by a multiple of `(|c| / c')ⁿ`. -/
theorem HasGaussNorm.isRestricted_of_abs_lt (hf : f.HasGaussNorm norm c') (h : |c| < c') :
    f.IsRestricted c := by
  rw [← isRestricted_abs_iff, isRestricted_iff']
  have hc' : 0 < c' := (abs_nonneg c).trans_lt h
  obtain ⟨B, hB⟩ := hf
  have hle (n : ℕ) : ‖coeff n f‖ * |c| ^ n ≤ B * (|c| / c') ^ n := by
    rw [div_pow, mul_div, le_div_iff₀ (by positivity), mul_assoc, ← mul_pow,
      mul_comm |c|, mul_pow, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hB ⟨n, rfl⟩) (by positivity)
  refine squeeze_zero (fun n ↦ by positivity) hle ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
    ((div_lt_one hc').mpr h)).const_mul B

/-- **Products of restricted series at a smaller radius.** Over any normed ring, if `f` and `g`
are restricted at the radius `c'`, then `f * g` is restricted at every radius `c` with
`|c| < |c'|`: the weighted coefficient norms of `f * g` at `c'` grow at most linearly, and the
geometric factor `(|c| / |c'|)ⁿ` absorbs this growth. Over an ultrametric ring no radius is lost
(`MvPowerSeries.IsRestricted.mul`). -/
theorem IsRestricted.mul_of_abs_lt (hf : f.IsRestricted c') (hg : g.IsRestricted c')
    (h : |c| < |c'|) : (f * g).IsRestricted c := by
  rw [← isRestricted_abs_iff] at hf hg ⊢
  rw [isRestricted_iff'] at hf hg ⊢
  set q := |c'|
  set ρ := |c| / q
  have hq : 0 < q := (abs_nonneg c).trans_lt h
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := (div_lt_one hq).mpr h
  obtain ⟨A, hA⟩ := hf.bddAbove_range
  obtain ⟨B, hB⟩ := hg.bddAbove_range
  have hAf (n : ℕ) : ‖coeff n f‖ * q ^ n ≤ A := hA ⟨n, rfl⟩
  have hBg (n : ℕ) : ‖coeff n g‖ * q ^ n ≤ B := hB ⟨n, rfl⟩
  have hA0 : 0 ≤ A := (by positivity : 0 ≤ ‖coeff 0 f‖ * q ^ 0).trans (hAf 0)
  have hB0 : 0 ≤ B := (by positivity : 0 ≤ ‖coeff 0 g‖ * q ^ 0).trans (hBg 0)
  have hscale : |c| = q * ρ := by rw [mul_div_cancel₀ _ hq.ne']
  have hupper : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ) * ρ ^ n * (A * B)) atTop (𝓝 0) := by
    simpa using (TauCeti.tendsto_add_pow_mul_pow_of_lt_one 1 hρ0 hρ1).mul_const (A * B)
  refine squeeze_zero (fun n ↦ by positivity) (fun n ↦ ?_) hupper
  rw [coeff_mul]
  calc
    ‖∑ p ∈ Finset.antidiagonal n, coeff p.1 f * coeff p.2 g‖ * |c| ^ n
        ≤ (∑ p ∈ Finset.antidiagonal n, ‖coeff p.1 f * coeff p.2 g‖) * |c| ^ n :=
      mul_le_mul_of_nonneg_right (norm_sum_le _ _) (by positivity)
    _ = ∑ p ∈ Finset.antidiagonal n, ‖coeff p.1 f * coeff p.2 g‖ * |c| ^ n := by
      rw [Finset.sum_mul]
    _ ≤ ∑ _p ∈ Finset.antidiagonal n, A * B * ρ ^ n := by
      refine Finset.sum_le_sum fun p hp ↦ ?_
      have hp' := Finset.mem_antidiagonal.mp hp
      have hfp : ‖coeff p.1 f‖ * |c| ^ p.1 ≤ A * ρ ^ p.1 := by
        rw [hscale, mul_pow, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hAf p.1) (by positivity)
      have hgp : ‖coeff p.2 g‖ * |c| ^ p.2 ≤ B * ρ ^ p.2 := by
        rw [hscale, mul_pow, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hBg p.2) (by positivity)
      calc
        ‖coeff p.1 f * coeff p.2 g‖ * |c| ^ n
            ≤ (‖coeff p.1 f‖ * ‖coeff p.2 g‖) * |c| ^ n := by gcongr; exact norm_mul_le _ _
        _ = (‖coeff p.1 f‖ * |c| ^ p.1) * (‖coeff p.2 g‖ * |c| ^ p.2) := by
          rw [← hp', pow_add]
          ring
        _ ≤ (A * ρ ^ p.1) * (B * ρ ^ p.2) := by gcongr
        _ = A * B * ρ ^ n := by rw [← hp', pow_add]; ring
    _ = (n + 1 : ℝ) * ρ ^ n * (A * B) := by
      rw [Finset.sum_const, Finset.Nat.card_antidiagonal]
      ring

end PowerSeries
