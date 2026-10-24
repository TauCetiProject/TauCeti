/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Restricted
public import Mathlib.RingTheory.PowerSeries.Trunc
public import TauCeti.Analysis.Asymptotics.Lemmas

/-!
# Restricted power series and their coefficient algebra

Mathlib's `PowerSeries.IsRestricted` asks the weighted coefficient norms of a power series to
tend to zero. A series whose coefficients vanish in every degree past some bound — a polynomial —
satisfies that condition at every radius, and a series restricted at one radius is restricted at
every smaller one. Without any ultrametric hypothesis, products of series restricted at one
radius are restricted at every strictly smaller radius. Over an ultrametric
normed commutative ring, constant series give the restricted subring its coefficient algebra
structure. The polynomial inclusion is an algebra homomorphism;
it induces the polynomial-to-series comparisons used in Weierstrass division and its quotients.

## Main results

* `TauCeti.PowerSeries.isRestricted_of_forall_coeff_eq_zero`: a series with a vanishing tail is
  restricted at every radius.
* `TauCeti.PowerSeries.isRestricted_of_abs_le`: restrictedness passes to smaller radii, and
  `TauCeti.PowerSeries.isRestrictedSubring_le_of_abs_le` is the resulting containment of subrings.
* `TauCeti.PowerSeries.isRestricted_polynomial`: every polynomial is restricted.
* `PowerSeries.IsRestricted.mul_of_abs_lt`: over any normed ring, a product of series restricted
  at `c'` is restricted at every `c` with `|c| < |c'|`.
* `TauCeti.PowerSeries.not_isRestricted_mk_pow`: for `a ≠ 0` and a multiplicative norm, `∑ aⁿ Xⁿ`
  is not restricted at the radius `‖a‖⁻¹`, and `TauCeti.PowerSeries.not_isRestricted_mk_one`:
  over a nontrivial normed ring, `∑ Xⁿ` is not restricted at the radius `1`.
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

/-- An inverse pair `x * y = 1` in the ring of series restricted at `c` is an inverse pair of
power series. -/
theorem coe_mul_coe_eq_one [IsUltrametricDist R]
    {x y : PowerSeries.IsRestricted.subring (R := R) c} (h : x * y = 1) :
    (x : PowerSeries R) * (y : PowerSeries R) = 1 := by
  rw [← Subring.coe_mul, h, Subring.coe_one]

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

/-- Over a nontrivial normed ring, the series `∑ Xⁿ` is not restricted at the radius `1`: all its
weighted coefficient norms there equal `‖1‖ ≠ 0`. -/
theorem not_isRestricted_mk_one [Nontrivial R] :
    ¬(PowerSeries.mk 1 : PowerSeries R).IsRestricted 1 := by
  intro hf
  have h := (PowerSeries.isRestricted_iff' _ _).mp hf
  simp only [PowerSeries.coeff_mk, Pi.one_apply, one_pow, mul_one] at h
  exact norm_ne_zero_iff.mpr one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h)

/-- A series restricted at `c` has weighted coefficient norms at `|c|` bounded by some `A ≥ 0`. -/
theorem _root_.PowerSeries.IsRestricted.exists_nonneg_norm_coeff_mul_pow_le
    (hf : f.IsRestricted c) :
    ∃ A, 0 ≤ A ∧ ∀ n, ‖f.coeff n‖ * |c| ^ n ≤ A := by
  rw [← PowerSeries.isRestricted_abs_iff, PowerSeries.isRestricted_iff'] at hf
  obtain ⟨A, hA⟩ := hf.bddAbove_range
  exact ⟨A, (by positivity : 0 ≤ ‖f.coeff 0‖ * |c| ^ 0).trans (hA ⟨0, rfl⟩), fun n ↦ hA ⟨n, rfl⟩⟩

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

/-- **Products of restricted series at a smaller radius.** Over any normed ring, if `f` and `g`
are restricted at the radius `c'`, then `f * g` is restricted at every radius `c` with
`|c| < |c'|`: the weighted coefficient norms of `f * g` at `c'` grow at most linearly, and the
geometric factor `(|c| / |c'|)ⁿ` absorbs this growth. Over an ultrametric ring no radius is lost
(`MvPowerSeries.IsRestricted.mul`). -/
theorem IsRestricted.mul_of_abs_lt (hf : f.IsRestricted c') (hg : g.IsRestricted c')
    (h : |c| < |c'|) : (f * g).IsRestricted c := by
  obtain ⟨A, hA0, hA⟩ := hf.exists_nonneg_norm_coeff_mul_pow_le
  obtain ⟨B, hB0, hB⟩ := hg.exists_nonneg_norm_coeff_mul_pow_le
  have hq : 0 < |c'| := (abs_nonneg c).trans_lt h
  set ρ := |c| / |c'|
  have hupper : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ) * ρ ^ n * (A * B)) atTop (𝓝 0) := by
    simpa using (TauCeti.tendsto_add_pow_mul_pow_of_lt_one 1 (by positivity)
      ((div_lt_one hq).mpr h)).mul_const (A * B)
  rw [← isRestricted_abs_iff, isRestricted_iff']
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
      calc
        ‖coeff p.1 f * coeff p.2 g‖ * |c| ^ n
            ≤ (‖coeff p.1 f‖ * ‖coeff p.2 g‖) * |c| ^ n := by gcongr; exact norm_mul_le _ _
        _ = (‖coeff p.1 f‖ * |c| ^ p.1) * (‖coeff p.2 g‖ * |c| ^ p.2) := by
          rw [← hp', pow_add]
          ring
        _ ≤ (A * ρ ^ p.1) * (B * ρ ^ p.2) :=
          mul_le_mul (TauCeti.mul_abs_pow_le_of_forall_mul_pow_le hq hA p.1)
            (TauCeti.mul_abs_pow_le_of_forall_mul_pow_le hq hB p.2)
            (by positivity) (by positivity)
        _ = A * B * ρ ^ n := by rw [← hp', pow_add]; ring
    _ = (n + 1 : ℝ) * ρ ^ n * (A * B) := by
      rw [Finset.sum_const, Finset.Nat.card_antidiagonal]
      ring

end PowerSeries
