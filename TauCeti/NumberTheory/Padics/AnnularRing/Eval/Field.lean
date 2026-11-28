/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.NumberTheory.Padics.AnnularRing.Eval.Basic
public import TauCeti.NumberTheory.Padics.AnnularRing.Presentation
import Mathlib.Algebra.BigOperators.Finsupp.Fin
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Algebra
import TauCeti.Analysis.Normed.Field.Basic
import TauCeti.Analysis.Normed.Group.NullFamily

/-!
# Annulus evaluations over complete normed fields and joint injectivity

Over a complete normed field `K` over `ℚ_p`, the evaluation homomorphism
`TauCeti.AnnularRing.eval : AnnularRing p →+* K` at a point `t ∈ K` with `p⁻¹ < ‖t‖ < 1` computes
images of two-variable power series `f = ∑ a_(i,j) T ^ i U ^ j ∈ ℤ_p⟦T, U⟧` via the presentation
`H ≃ ℤ_p⟦T, U⟧ / (TU - p)` as the convergent sum `∑ a_(i,j) t ^ i (p / t) ^ j`.

Over an algebraically closed `K`, such as `ℂ_p`, these evaluations are jointly injective on both
`H` and `H[1/T]`, so a two-variable series is a multiple of `TU - p` exactly when it vanishes on
the open annulus.

## Main results

* `TauCeti.AnnularRing.hasSum_eval_ofMvPowerSeries`: the value of the image of
  `f = ∑ a_(i,j) T ^ i U ^ j` is the convergent sum `∑ a_(i,j) t ^ i (p / t) ^ j`.
* `TauCeti.AnnularRing.eq_zero_of_forall_eval_eq_zero`,
  `TauCeti.AnnularRing.eq_of_forall_eval_eq`: over an algebraically closed `K`, evaluations on the
  open annulus are jointly injective on `H`.
* `TauCeti.AnnularRing.eq_zero_of_forall_localizedEval_eq_zero`,
  `TauCeti.AnnularRing.eq_of_forall_localizedEval_eq`: joint injectivity on `H[1/T]`.
* `TauCeti.AnnularRing.mem_span_iff_forall_eval_annulus`: a series `f ∈ ℤ_p⟦T, U⟧` is a multiple
  of `TU - p` exactly when `∑ a_(i,j) t ^ i (p / t) ^ j = 0` at every point of the annulus.

## Implementation notes

For nonzero `x`, injectivity is witnessed at a point `t` with `‖t‖ ^ N = p ^ (-k)` and
`N = 2k + 1`, where `k` is large compared with the valuation and index of one nonzero
coefficient. Then `‖d_m t ^ m‖ ^ N = p ^ (-(v_p(d_m) N + k m))`, only finitely many indices `m`
can reach the largest of these norms, and two of them reach it together only if `N` divides their
difference, as `k` and `N` are coprime. The value at `t` therefore has the norm of a single dominant
term (`HasSum.norm_eq_of_forall_norm_lt`).

## References

* R. Liu, D. Wan and L. Xiao, *The eigencurve over the boundary of weight space*, Duke Math. J.
  166 (2017), §§2–3.
-/

public noncomputable section

namespace TauCeti.AnnularRing

variable {p : ℕ} [Fact p.Prime] {K : Type*} [NormedField K]

/-! ### Bounds on the annulus -/

section Bounds

variable {t : K}

private theorem norm_pos_of_lt_norm (h₀ : (p : ℝ)⁻¹ < ‖t‖) : 0 < ‖t‖ :=
  (inv_pos.2 (Nat.cast_pos.mpr (Fact.out : p.Prime).pos)).trans h₀

private theorem one_lt_mul_norm (h₀ : (p : ℝ)⁻¹ < ‖t‖) : 1 < (p : ℝ) * ‖t‖ := by
  rwa [inv_lt_iff_one_lt_mul₀' (Nat.cast_pos.mpr (Fact.out : p.Prime).pos)] at h₀

/-- The bound `‖t‖ ^ i (p ‖t‖)⁻¹ ^ j` on the monomial values `‖a_(i,j) t ^ i (p / t) ^ j‖` is
summable over the exponents `(i, j)`. -/
private theorem summable_pow_mul_pow (h₀ : (p : ℝ)⁻¹ < ‖t‖) (h₁ : ‖t‖ < 1) :
    Summable fun n : Fin 2 →₀ ℕ ↦ ‖t‖ ^ n 0 * ((p : ℝ) * ‖t‖)⁻¹ ^ n 1 := by
  have h₂ : ((p : ℝ) * ‖t‖)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_mul_norm h₀)
  have hs := (summable_geometric_of_lt_one (norm_nonneg t) h₁).mul_of_nonneg
    (summable_geometric_of_lt_one (by positivity) h₂) (fun _ ↦ by positivity)
    (fun _ ↦ by positivity)
  refine (finTwoArrowEquiv' ℕ).symm.summable_iff.1 (hs.congr fun ij ↦ ?_)
  simp

/-- A point with `‖t‖ ^ N = p ^ (-k)` and `k < N` lies outside the circle `‖t‖ = p⁻¹`. -/
private theorem lt_norm_of_norm_pow_eq {k N : ℕ} (hkN : k < N) (h : ‖t‖ ^ N = (p : ℝ)⁻¹ ^ k) :
    (p : ℝ)⁻¹ < ‖t‖ := by
  have hp : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)
  have hp₀ : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.2 (Nat.cast_pos.mpr (Fact.out : p.Prime).pos)
  refine (pow_lt_pow_iff_left₀ hp₀.le (norm_nonneg t) (by omega : N ≠ 0)).1 ?_
  rw [h]
  exact pow_lt_pow_right_of_lt_one₀ hp₀ hp hkN

/-- A point with `‖t‖ ^ N = p ^ (-k)` and `0 < k` lies inside the unit circle. -/
private theorem norm_lt_one_of_norm_pow_eq {k N : ℕ} (hk : 0 < k)
    (h : ‖t‖ ^ N = (p : ℝ)⁻¹ ^ k) : ‖t‖ < 1 := by
  have hp : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)
  have hlt : (p : ℝ)⁻¹ ^ k < 1 := pow_lt_one₀ (by positivity) hp hk.ne'
  have hN : N ≠ 0 := by
    rintro rfl
    exact hlt.ne (by rw [← h, pow_zero])
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg t) hN).1 (h ▸ hlt)

end Bounds

/-! ### The dominant exponent -/

/-- The coefficient `d_m ≠ 0` has valuation at least `-min 0 m`. -/
private theorem neg_valuation_le (x : AnnularRing p) {m : ℤ} (hm : x.coeff m ≠ 0) :
    -((x.coeff m).valuation : ℤ) ≤ min 0 m := by
  have h := x.norm_coeff_le m
  rwa [PadicInt.norm_eq_zpow_neg_valuation hm,
    zpow_le_zpow_iff_right₀ (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)] at h

/-- The exponent `E(m) = v_p(d_m) N + k m`, for which `‖d_m t ^ m‖ ^ N = p ^ (-E(m))` when
`‖t‖ ^ N = p ^ (-k)`. -/
private def exponent (x : AnnularRing p) (k N : ℕ) (m : ℤ) : ℤ :=
  (x.coeff m).valuation * N + k * m

/-- The exponent of a nonzero coefficient is at most `(v_p(d_m) + |m|) (2k + 1)`. -/
private theorem exponent_le (x : AnnularRing p) (k : ℕ) (m : ℤ) :
    exponent x k (2 * k + 1) m ≤ ((x.coeff m).valuation + m.natAbs) * (2 * k + 1) := by
  have h : (k : ℤ) * m ≤ (2 * k + 1) * m.natAbs :=
    (mul_le_mul_of_nonneg_left Int.le_natAbs (by positivity)).trans
      (mul_le_mul_of_nonneg_right (by omega) (by positivity))
  simp only [exponent]
  push_cast at h ⊢
  linarith

/-- With `k = 3C + 1`, a nonzero coefficient of index `|m| > 3C` has exponent above
`C (2k + 1)`: for `m > 0` the term `k m` is large, and for `m < 0` the valuation `v_p(d_m) ≥ -m`
outweighs `k m`. -/
private theorem lt_exponent_of_lt_abs (x : AnnularRing p) {C k : ℕ} (hk : k = 3 * C + 1) {m : ℤ}
    (hm : x.coeff m ≠ 0) (hlt : 3 * (C : ℤ) < |m|) :
    C * (2 * k + 1) < exponent x k (2 * k + 1) m := by
  have hv := neg_valuation_le x hm
  simp only [exponent]
  rcases le_or_gt 0 m with h0 | h0
  · rw [abs_of_nonneg h0] at hlt
    have : (k : ℤ) * k ≤ k * m := mul_le_mul_of_nonneg_left (by omega) (by positivity)
    push_cast [hk] at this ⊢
    nlinarith
  · rw [abs_of_neg h0] at hlt
    rw [min_eq_right h0.le] at hv
    have : (-m) * (k + 1 : ℤ) ≤ (x.coeff m).valuation * (2 * k + 1) + k * m := by nlinarith
    have h2 : (k : ℤ) * (k + 1) ≤ (-m) * (k + 1) :=
      mul_le_mul_of_nonneg_right (by omega) (by positivity)
    push_cast [hk] at this h2 ⊢
    nlinarith

/-- Two indices with equal exponents differ by a multiple of `2k + 1`, since `k` and `2k + 1`
are coprime; so they coincide when `|m₀ - m| < 2k + 1`. -/
private theorem eq_of_exponent_eq (x : AnnularRing p) {k : ℕ} {m m₀ : ℤ}
    (h : exponent x k (2 * k + 1) m = exponent x k (2 * k + 1) m₀)
    (hlt : |m₀ - m| < 2 * k + 1) : m = m₀ := by
  have hdvd : (2 * k + 1 : ℤ) ∣ k * (m₀ - m) :=
    ⟨(x.coeff m).valuation - (x.coeff m₀).valuation, by
      simp only [exponent] at h; push_cast at h; linarith⟩
  have hcop : IsCoprime (2 * k + 1 : ℤ) k := ⟨1, -2, by ring⟩
  have := Int.eq_zero_of_abs_lt_dvd (hcop.dvd_of_dvd_mul_left hdvd) hlt
  omega

/-- **The dominant term.** For a nonzero element there are `k ≥ 1` and an index `m₀` at which the
exponent `E(m) = v_p(d_m) (2k + 1) + k m` is strictly smallest among the nonzero coefficients. -/
private theorem exists_exponent_lt (x : AnnularRing p) (hx : x ≠ 0) :
    ∃ k : ℕ, 0 < k ∧ ∃ m₀, x.coeff m₀ ≠ 0 ∧
      ∀ m ≠ m₀, x.coeff m ≠ 0 → exponent x k (2 * k + 1) m₀ < exponent x k (2 * k + 1) m := by
  obtain ⟨m', hm'⟩ : ∃ m, x.coeff m ≠ 0 := by
    by_contra! h
    exact hx (AnnularRing.ext (funext h))
  -- Indices with `|m| > 3C` cannot compete with `m'`, where `C = v_p(d_m') + |m'|`; among the
  -- others, a minimiser of the exponent is strict by `eq_of_exponent_eq`.
  set C : ℕ := (x.coeff m').valuation + m'.natAbs
  set k : ℕ := 3 * C + 1 with hk
  classical
  let s := (Finset.Icc (-(3 * C : ℤ)) (3 * C)).filter fun m ↦ x.coeff m ≠ 0
  have hm's : m' ∈ s := Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by omega, by omega⟩, hm'⟩
  obtain ⟨m₀, hm₀s, hmin⟩ := s.exists_min_image (exponent x k (2 * k + 1)) ⟨m', hm's⟩
  obtain ⟨hm₀I, hm₀⟩ := Finset.mem_filter.1 hm₀s
  rw [Finset.mem_Icc] at hm₀I
  refine ⟨k, by omega, m₀, hm₀, fun m hne hm ↦ ?_⟩
  by_cases hmI : m ∈ Finset.Icc (-(3 * C : ℤ)) (3 * C)
  · rw [Finset.mem_Icc] at hmI
    exact (hmin m (Finset.mem_filter.2 ⟨Finset.mem_Icc.2 hmI, hm⟩)).lt_of_ne fun heq ↦
      hne (eq_of_exponent_eq x heq.symm (abs_lt.2 ⟨by omega, by omega⟩))
  · rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hmI
    have habs : 3 * (C : ℤ) < |m| := by
      rcases hmI with h | h
      · exact lt_abs.2 (Or.inr (by omega))
      · exact lt_abs.2 (Or.inl h)
    exact (hmin m' hm's).trans_lt ((exponent_le x k m').trans_lt
      (lt_exponent_of_lt_abs x hk hm habs))

variable [NormedAlgebra ℚ_[p] K]

/-! ### Values of two-variable series -/

section MvPowerSeries

variable {t : K}

private theorem norm_term_pow {k N : ℕ} (h : ‖t‖ ^ N = (p : ℝ)⁻¹ ^ k) (x : AnnularRing p)
    {m : ℤ} (hm : x.coeff m ≠ 0) :
    ‖algebraMap ℚ_[p] K (x.coeff m) * t ^ m‖ ^ N = (p : ℝ) ^ (-exponent x k N m) := by
  have hp : (p : ℝ) ≠ 0 := (Nat.cast_pos.mpr (Fact.out : p.Prime).pos).ne'
  have hN : (‖t‖ ^ m) ^ N = ((p : ℝ) ^ (-(k : ℤ))) ^ m := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h]
    simp [zpow_neg]
  rw [norm_mul, ← padicIntAlgebraMap_apply, norm_padicIntAlgebraMap, norm_zpow, mul_pow, hN,
    PadicInt.norm_eq_zpow_neg_valuation hm, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hp,
    exponent]
  congr 1
  ring

/-- The monomial value `a t ^ i (p / t) ^ j` has norm at most `‖t‖ ^ i (p ‖t‖)⁻¹ ^ j`. -/
private theorem norm_mul_pow_mul_div_pow_le (a : ℤ_[p]) (n : Fin 2 →₀ ℕ) :
    ‖padicIntAlgebraMap p K a * t ^ n 0 * ((p : K) / t) ^ n 1‖ ≤
      ‖t‖ ^ n 0 * ((p : ℝ) * ‖t‖)⁻¹ ^ n 1 := by
  rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_div, norm_natCast_p,
    norm_padicIntAlgebraMap, mul_inv, div_eq_mul_inv, mul_assoc]
  exact mul_le_of_le_one_left (by positivity) (PadicInt.norm_le_one a)

/-- The term `a_n (T ^ n₀ U ^ n₁)_m t ^ m` of the double series computing the value of the image of
a two-variable series; it vanishes off the diagonal `m = n₀ - n₁`. -/
private def doubleTerm (t : K) (F : MvPowerSeries (Fin 2) ℤ_[p]) (x : (Fin 2 →₀ ℕ) × ℤ) : K :=
  padicIntAlgebraMap p K
    (MvPowerSeries.coeff x.1 F * ((T : AnnularRing p) ^ x.1 0 * U ^ x.1 1).coeff x.2) * t ^ x.2

private theorem doubleTerm_eq (h₀ : (p : ℝ)⁻¹ < ‖t‖) (F : MvPowerSeries (Fin 2) ℤ_[p])
    (x : (Fin 2 →₀ ℕ) × ℤ) :
    doubleTerm t F x = if x.2 = x.1 0 - x.1 1 then padicIntAlgebraMap p K
      (MvPowerSeries.coeff x.1 F) * t ^ x.1 0 * ((p : K) / t) ^ x.1 1 else 0 := by
  have ht : t ≠ 0 := norm_pos_iff.1 (norm_pos_of_lt_norm h₀)
  rw [doubleTerm, coeff_T_pow_mul_U_pow]
  split_ifs with h
  · rw [h, zpow_sub₀ ht, zpow_natCast, zpow_natCast, map_mul, map_pow, map_natCast, div_pow]
    field_simp
  · simp

variable [CompleteSpace K]

/-- **Values of two-variable series.** The value at `t` of the image of
`f = ∑ a_(i,j) T ^ i U ^ j` is the convergent sum `∑ a_(i,j) t ^ i (p / t) ^ j`. -/
theorem hasSum_eval_ofMvPowerSeries (h₀ : (p : ℝ)⁻¹ < ‖t‖) (h₁ : ‖t‖ < 1)
    (F : MvPowerSeries (Fin 2) ℤ_[p]) :
    HasSum (fun n : Fin 2 →₀ ℕ ↦ algebraMap ℚ_[p] K (MvPowerSeries.coeff n F : ℤ_[p]) *
        t ^ n 0 * ((p : K) / t) ^ n 1)
      (eval t h₀ h₁ (ofMvPowerSeries F)) := by
  have hs : Summable fun n : Fin 2 →₀ ℕ ↦
      (padicIntAlgebraMap p K (MvPowerSeries.coeff n F) : K) * t ^ n 0 * ((p : K) / t) ^ n 1 :=
    (summable_pow_mul_pow h₀ h₁).of_norm_bounded fun n ↦ norm_mul_pow_mul_div_pow_le _ n
  -- The double series is supported on the graph of `n ↦ n₀ - n₁`, where it is the given series.
  have hinj : Function.Injective fun n : Fin 2 →₀ ℕ ↦ (n, (n 0 : ℤ) - n 1) :=
    fun _ _ h ↦ congr_arg Prod.fst h
  have hG : HasSum (doubleTerm t F) (∑' n, padicIntAlgebraMap p K (MvPowerSeries.coeff n F) *
      t ^ n 0 * ((p : K) / t) ^ n 1) := by
    refine (hinj.hasSum_iff fun x hx ↦ ?_).1 ?_
    · rw [doubleTerm_eq h₀, ite_eq_right fun h ↦ hx ⟨x.1, Prod.ext rfl h.symm⟩]
    · refine hs.hasSum.congr_fun fun n ↦ ?_
      simp [doubleTerm_eq h₀]
  -- Summing first over the exponents `n` gives the normal-form coefficients of the image.
  have hhas : HasSum (fun m : ℤ ↦ padicIntAlgebraMap p K ((ofMvPowerSeries F).coeff m) * t ^ m)
      (eval t h₀ h₁ (ofMvPowerSeries F)) := by
    simpa only [padicIntAlgebraMap_apply] using hasSum_eval h₀ h₁ (ofMvPowerSeries F)
  have heq : eval t h₀ h₁ (ofMvPowerSeries F) = ∑' n, padicIntAlgebraMap p K
      (MvPowerSeries.coeff n F) * t ^ n 0 * ((p : K) / t) ^ n 1 :=
    hhas.unique (((Equiv.prodComm _ _).hasSum_iff.2 hG).prod_fiberwise fun m ↦
      ((hasSum_coeff_ofMvPowerSeries F m).map (padicIntAlgebraMap p K)
        (continuous_padicIntAlgebraMap (continuous_algebraMap ℚ_[p] K))).mul_right (t ^ m))
  rw [heq]
  simpa only [padicIntAlgebraMap_apply] using hs.hasSum

end MvPowerSeries

/-! ### Joint injectivity -/

section Injectivity

variable [CompleteSpace K] [IsAlgClosed K]

/-- **Joint injectivity of the evaluations.** Over an algebraically closed complete normed field
`K` over `ℚ_p`, such as `ℂ_p`, an element of the annular coefficient ring vanishing at every point
of the annulus `p⁻¹ < ‖t‖ < 1` is zero. -/
theorem eq_zero_of_forall_eval_eq_zero {x : AnnularRing p}
    (h : ∀ (t : K) (h₀ : (p : ℝ)⁻¹ < ‖t‖) (h₁ : ‖t‖ < 1), eval t h₀ h₁ x = 0) : x = 0 := by
  by_contra hx
  have : IsUltrametricDist K := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  obtain ⟨k, hk, m₀, hm₀, hdom⟩ := exists_exponent_lt x hx
  obtain ⟨t, ht⟩ := NormedField.exists_norm_pow_eq_of_isAlgClosed ((p : K) ^ k)
    (N := 2 * k + 1) (by omega)
  rw [norm_pow, norm_natCast_p] at ht
  have h₀ := lt_norm_of_norm_pow_eq (by omega) ht
  have h₁ := norm_lt_one_of_norm_pow_eq hk ht
  -- At `t`, the term of index `m₀` strictly dominates, so the value has its nonzero norm.
  have hpos : 0 < ‖algebraMap ℚ_[p] K (x.coeff m₀) * t ^ m₀‖ := by
    rw [norm_mul, ← padicIntAlgebraMap_apply, norm_padicIntAlgebraMap, norm_zpow]
    exact mul_pos (norm_pos_iff.2 hm₀) (zpow_pos (norm_pos_of_lt_norm h₀) _)
  have hS := hasSum_eval h₀ h₁ x
  have hnorm : ‖eval t h₀ h₁ x‖ = ‖algebraMap ℚ_[p] K (x.coeff m₀) * t ^ m₀‖ := by
    refine hS.norm_eq_of_forall_norm_lt m₀ fun m hm ↦ ?_
    by_cases hxm : x.coeff m = 0
    · simpa [hxm] using hpos
    · refine (pow_lt_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by omega : 2 * k + 1 ≠ 0)).1 ?_
      rw [norm_term_pow ht x hxm, norm_term_pow ht x hm₀]
      exact zpow_lt_zpow_right₀ (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)
        (neg_lt_neg (hdom m hm hxm))
  rw [h t h₀ h₁, norm_zero] at hnorm
  exact hpos.ne hnorm

/-- Two elements of `AnnularRing p` that agree at every point of the open annulus
`p⁻¹ < ‖t‖ < 1` in an algebraically closed complete normed field `K` over `ℚ_p` are equal. -/
theorem eq_of_forall_eval_eq {x y : AnnularRing p}
    (hxy : ∀ (t : K) (h₀ : (p : ℝ)⁻¹ < ‖t‖) (h₁ : ‖t‖ < 1), eval t h₀ h₁ x = eval t h₀ h₁ y) :
    x = y :=
  sub_eq_zero.mp <| eq_zero_of_forall_eval_eq_zero (K := K) fun t h₀ h₁ ↦ by
    rw [map_sub, hxy t h₀ h₁, sub_self]

/-- **Joint injectivity on `H[1/T]`**: an element of `H[1/T]` that vanishes at every point of the
open annulus `p⁻¹ < ‖t‖ < 1` in an algebraically closed complete normed field `K` over `ℚ_p` is
zero. -/
theorem eq_zero_of_forall_localizedEval_eq_zero {A : Type*} [CommRing A]
    [Algebra (AnnularRing p) A] [IsLocalization.Away (T : AnnularRing p) A] {x : A}
    (hx : ∀ (t : K) (h₀ : (p : ℝ)⁻¹ < ‖t‖) (h₁ : ‖t‖ < 1), localizedEval t h₀ h₁ x = 0) :
    x = 0 := by
  obtain ⟨k, a, ha⟩ := IsLocalization.Away.surj (T : AnnularRing p) x
  have ha0 : a = 0 := eq_zero_of_forall_eval_eq_zero (K := K) fun t h₀ h₁ ↦ by
    rw [← localizedEval_algebraMap (A := A), ← ha, map_mul, hx t h₀ h₁, zero_mul]
  rw [ha0, map_zero] at ha
  exact ((IsLocalization.Away.algebraMap_isUnit (T : AnnularRing p)).pow k).mul_left_eq_zero.mp ha

/-- Two elements of `H[1/T]` that agree at every point of the open annulus `p⁻¹ < ‖t‖ < 1` in an
algebraically closed complete normed field `K` over `ℚ_p` are equal. -/
theorem eq_of_forall_localizedEval_eq {A : Type*} [CommRing A]
    [Algebra (AnnularRing p) A] [IsLocalization.Away (T : AnnularRing p) A] {x y : A}
    (hxy : ∀ (t : K) (h₀ : (p : ℝ)⁻¹ < ‖t‖) (h₁ : ‖t‖ < 1),
      localizedEval t h₀ h₁ x = localizedEval t h₀ h₁ y) : x = y :=
  sub_eq_zero.mp <| eq_zero_of_forall_localizedEval_eq_zero (K := K) fun t h₀ h₁ ↦ by
    rw [map_sub, hxy t h₀ h₁, sub_self]

/-- **The annular evaluations detect the relation `TU = p`.** Over an algebraically closed complete
normed field `K` over `ℚ_p`, such as `ℂ_p`, a series `f = ∑ a_(i,j) T ^ i U ^ j ∈ ℤ_p⟦T, U⟧` is a
multiple of `TU - p` exactly when `∑ a_(i,j) t ^ i (p / t) ^ j = 0` at every `t` with
`p⁻¹ < ‖t‖ < 1`. -/
theorem mem_span_iff_forall_eval_annulus (f : MvPowerSeries (Fin 2) ℤ_[p]) :
    f ∈ Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C (p : ℤ_[p])} ↔
      ∀ t : K, (p : ℝ)⁻¹ < ‖t‖ → ‖t‖ < 1 →
        ∑' n : Fin 2 →₀ ℕ, algebraMap ℚ_[p] K (MvPowerSeries.coeff n f : ℤ_[p]) *
          t ^ n 0 * ((p : K) / t) ^ n 1 = 0 := by
  rw [← ker_ofMvPowerSeries, RingHom.mem_ker]
  refine ⟨fun hf t h₀ h₁ ↦ ?_, fun hf ↦ eq_zero_of_forall_eval_eq_zero (K := K) fun t h₀ h₁ ↦ ?_⟩
  · rw [(hasSum_eval_ofMvPowerSeries h₀ h₁ f).tsum_eq, hf, map_zero]
  · rw [← (hasSum_eval_ofMvPowerSeries h₀ h₁ f).tsum_eq]
    exact hf t h₀ h₁

end Injectivity

end TauCeti.AnnularRing
