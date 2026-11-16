/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Lipschitz
public import TauCeti.NumberTheory.Padics.AnnularRing.Gauge
public import TauCeti.NumberTheory.Padics.Basic
public import TauCeti.NumberTheory.Padics.Complex.Valuation
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Specialisation of `ℤ_p⟦T, p/T⟧` on the open annulus `p⁻¹ < |t| < 1`

For any complete normed field extension `K` of `ℚ_p` and `t ∈ K` with `p⁻¹ < ‖t‖ < 1`, evaluating
`∑_{m ∈ ℤ} d_m T ^ m` at `t` defines `TauCeti.AnnularRing.eval ht : AnnularRing p →+* K` (`T ↦ t`,
`U ↦ p / t`), bounded by `1` when `K` is ultrametric. Extending across `Localization.Away T` gives
`TauCeti.AnnularLaurent.eval hα ht : AnnularLaurent p hα →+* K`, continuous for every `α ∈ (0, 1)`
when `K` is ultrametric (`[IsUltrametricDist K]`), yet not Lipschitz when `α < ‖t‖`. While `ℚ_p`
has no points in `(p⁻¹, 1)`, `ℂ_p`-annulus evaluations are jointly injective
(`TauCeti.AnnularRing.eq_of_forall_eval_eq`), making `AnnularRing p` and `AnnularLaurent p hα`
integral domains.

## References

* R. Liu, D. Wan and L. Xiao, *The eigencurve over the boundary of weight space*, Duke Math. J.
  166 (2017), §§2–3.
-/

public noncomputable section

open Filter Topology
open scoped NNReal

namespace TauCeti

namespace AnnularRing

variable {p : ℕ} [Fact p.Prime]

private theorem one_lt_p : (1 : ℝ) < p := mod_cast (Fact.out : p.Prime).one_lt
private theorem p_pos : (0 : ℝ) < p := zero_lt_one.trans one_lt_p

/-- The `p`-adic field `ℚ_p` contains no element of norm strictly between `p⁻¹` and `1`, so
annular evaluations require a ramified extension such as `ℂ_p`. -/
theorem not_exists_padic_norm_mem_Ioo : ¬ ∃ t : ℚ_[p], ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1 := by
  rintro ⟨t, hlow, hhigh⟩
  have ht0 : t ≠ 0 := norm_pos_iff.1 ((inv_pos.2 p_pos).trans hlow)
  rw [Padic.norm_eq_zpow_neg_valuation ht0] at hlow hhigh
  have h1 := (zpow_lt_zpow_iff_right₀ (one_lt_p (p := p))).1 (zpow_neg_one (p : ℝ) ▸ hlow)
  have h2 := (zpow_lt_zpow_iff_right₀ (one_lt_p (p := p))).1 (zpow_zero (p : ℝ) ▸ hhigh)
  omega

section Eval

variable {K : Type*} [NormedField K] {t : K}

/-- Any element `t` whose norm lies in `(p⁻¹, 1)` is nonzero. -/
theorem ne_zero_of_norm_mem_Ioo (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) : t ≠ 0 :=
  norm_pos_iff.1 ((inv_pos.2 (p_pos (p := p))).trans ht.1)

private theorem inv_p_mul_norm_lt_one (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) :
    ((p : ℝ) * ‖t‖)⁻¹ < 1 :=
  inv_lt_one_of_one_lt₀ <| (mul_inv_cancel₀ (p_pos (p := p)).ne').symm.trans_lt
    (mul_lt_mul_of_pos_left ht.1 (p_pos (p := p)))

omit [Fact p.Prime] in
private theorem zpow_min_neg_mul_zpow (t : K) (n : ℕ) :
    (p : ℝ) ^ min (0 : ℤ) (-n) * ‖t‖ ^ (-(n : ℤ)) = (((p : ℝ) * ‖t‖)⁻¹) ^ n := by
  rw [min_eq_right (by omega), zpow_neg, zpow_natCast, zpow_neg, zpow_natCast,
    ← mul_inv, ← mul_pow, inv_pow]

section NormedAlgebra

variable [NormedAlgebra ℚ_[p] K]

/-- Termwise norm bound on the Laurent expansion of `x ∈ AnnularRing p` at `t`:
`‖x.coeff m * t ^ m‖ ≤ p ^ min 0 m * ‖t‖ ^ m`. -/
theorem norm_padicIntAlgebraMap_coeff_mul_zpow_le (x : AnnularRing p) (t : K) (m : ℤ) :
    ‖padicIntAlgebraMap p K (x.coeff m) * t ^ m‖ ≤ (p : ℝ) ^ min 0 m * ‖t‖ ^ m := by
  rw [norm_mul, norm_padicIntAlgebraMap, norm_zpow]
  exact mul_le_mul_of_nonneg_right (x.norm_coeff_le m) (zpow_nonneg (norm_nonneg t) m)

/-- On the open annulus `p⁻¹ < ‖t‖ < 1`, every term `x.coeff m * t ^ m` of `x ∈ AnnularRing p`
has norm at most `1`. -/
theorem norm_padicIntAlgebraMap_coeff_mul_zpow_le_one (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1)
    (x : AnnularRing p) (m : ℤ) :
    ‖padicIntAlgebraMap p K (x.coeff m) * t ^ m‖ ≤ 1 := by
  refine (norm_padicIntAlgebraMap_coeff_mul_zpow_le x t m).trans ?_
  rcases le_or_gt 0 m with hm | hm
  · lift m to ℕ using hm
    simpa [min_eq_left (Nat.cast_nonneg m)] using pow_le_one₀ (norm_nonneg t) ht.2.le
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = -n := ⟨(-m).toNat, by omega⟩
    rw [zpow_min_neg_mul_zpow]
    exact pow_le_one₀ (by positivity) (inv_p_mul_norm_lt_one ht).le

/-- On the open annulus `p⁻¹ < ‖t‖ < 1`, the Laurent expansion `∑ x.coeff m * t ^ m` of
`x ∈ AnnularRing p` is absolutely summable, dominated by geometric series in `‖t‖` and
`(p * ‖t‖)⁻¹`. -/
theorem summable_norm_padicIntAlgebraMap_coeff_mul_zpow (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1)
    (x : AnnularRing p) :
    Summable fun m : ℤ ↦ ‖padicIntAlgebraMap p K (x.coeff m) * t ^ m‖ := by
  refine Summable.of_nat_of_neg
    (Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
      (summable_geometric_of_lt_one (norm_nonneg t) ht.2))
    (Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
      (summable_geometric_of_lt_one (by positivity) (inv_p_mul_norm_lt_one ht)))
  · simpa [min_eq_left (Nat.cast_nonneg n)] using norm_padicIntAlgebraMap_coeff_mul_zpow_le x t n
  · exact (norm_padicIntAlgebraMap_coeff_mul_zpow_le x t (-n)).trans_eq (zpow_min_neg_mul_zpow t n)

variable [CompleteSpace K]

/-- On the open annulus `p⁻¹ < ‖t‖ < 1`, the Laurent expansion `∑ x.coeff m * t ^ m` of
`x ∈ AnnularRing p` is summable in any complete normed field extension `K` of `ℚ_p`. -/
theorem summable_padicIntAlgebraMap_coeff_mul_zpow (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1)
    (x : AnnularRing p) :
    Summable fun m : ℤ ↦ padicIntAlgebraMap p K (x.coeff m) * t ^ m :=
  (summable_norm_padicIntAlgebraMap_coeff_mul_zpow ht x).of_norm

/-- Specialisation `AnnularRing p →+* K` at `t` (`p⁻¹ < ‖t‖ < 1`), sending `∑ d_m T ^ m` to
`∑ d_m t ^ m`. -/
def eval (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) : AnnularRing p →+* K where
  toFun x := ∑' m : ℤ, padicIntAlgebraMap p K (x.coeff m) * t ^ m
  map_zero' := by simp
  map_one' := by rw [tsum_eq_single 0 fun m hm ↦ by simp [coeff_one, hm]]; simp
  map_add' x y := by
    simp_rw [coeff_add, map_add, add_mul]
    exact (summable_padicIntAlgebraMap_coeff_mul_zpow ht x).tsum_add
      (summable_padicIntAlgebraMap_coeff_mul_zpow ht y)
  map_mul' x y := by
    have ht0 : t ≠ 0 := ne_zero_of_norm_mem_Ioo ht
    refine ((DiscreteConvolution.hasSum_tsum_mul_sub
      (summable_norm_padicIntAlgebraMap_coeff_mul_zpow ht x)
      (summable_norm_padicIntAlgebraMap_coeff_mul_zpow ht y)).congr_fun fun m ↦ ?_).tsum_eq
    have hterm : (fun i : ℤ ↦ (padicIntAlgebraMap p K (x.coeff i) * t ^ i) *
        (padicIntAlgebraMap p K (y.coeff (m - i)) * t ^ (m - i))) =
        fun i : ℤ ↦ padicIntAlgebraMap p K (x.coeff i * y.coeff (m - i)) * t ^ m := by
      ext i; rw [map_mul, mul_mul_mul_comm, ← zpow_add₀ ht0, add_sub_cancel]
    rw [hterm]
    exact (((hasSum_coeff_mul x y m).map (padicIntAlgebraMap p K)
      continuous_padicIntAlgebraMap).mul_right (t ^ m)).tsum_eq.symm

theorem eval_apply (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) (x : AnnularRing p) :
    eval ht x = ∑' m : ℤ, padicIntAlgebraMap p K (x.coeff m) * t ^ m := (rfl)

/-- The two-sided series `∑ x.coeff m * t ^ m` sums to `eval ht x`. -/
theorem hasSum_eval (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) (x : AnnularRing p) :
    HasSum (fun m : ℤ ↦ padicIntAlgebraMap p K (x.coeff m) * t ^ m) (eval ht x) :=
  (summable_padicIntAlgebraMap_coeff_mul_zpow ht x).hasSum

@[simp] theorem eval_algebraMap (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) (c : ℤ_[p]) :
    eval ht (algebraMap ℤ_[p] (AnnularRing p) c) = padicIntAlgebraMap p K c := by
  rw [eval_apply, tsum_eq_single 0 fun m hm ↦ by simp [coeff_algebraMap, hm]]; simp
@[simp] theorem eval_T (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) : eval ht T = t := by
  rw [eval_apply, tsum_eq_single 1 fun m hm ↦ by simp [coeff_T, hm]]; simp [coeff_T]
@[simp] theorem eval_U (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) : eval ht U = (p : K) / t := by
  rw [eval_apply, tsum_eq_single (-1) fun m hm ↦ by simp [coeff_U, hm]]
  simp [coeff_U, div_eq_mul_inv]

/-- When `K` is ultrametric, every annulus evaluation `eval ht` maps `AnnularRing p` into the
closed unit ball `‖eval ht x‖ ≤ 1`. -/
theorem norm_eval_le_one [IsUltrametricDist K] (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1)
    (x : AnnularRing p) : ‖eval ht x‖ ≤ 1 := by
  rw [eval_apply]
  exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg zero_le_one
    (norm_padicIntAlgebraMap_coeff_mul_zpow_le_one ht x)

/-- Evaluating `ofPowerSeriesT f` at `t` computes the convergent power series `∑ f_n t ^ n`. -/
theorem hasSum_eval_ofPowerSeriesT (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) (f : PowerSeries ℤ_[p]) :
    HasSum (fun n : ℕ ↦ padicIntAlgebraMap p K (PowerSeries.coeff n f) * t ^ n)
      (eval ht (ofPowerSeriesT f)) := by
  have h1 : HasSum
      ((fun m : ℤ ↦ padicIntAlgebraMap p K ((ofPowerSeriesT f).coeff m) * t ^ m) ∘ ((↑) : ℕ → ℤ))
      (eval ht (ofPowerSeriesT f)) := by
    refine (Nat.cast_injective.hasSum_iff fun m hm ↦ ?_).2 (hasSum_eval ht (ofPowerSeriesT f))
    have hneg : m < 0 := by by_contra! h0; lift m to ℕ using h0; exact hm ⟨m, rfl⟩
    simp [coeff_ofPowerSeriesT_of_neg f hneg]
  simpa [Function.comp_def] using h1

/-- Evaluating `ofPowerSeriesU g` at `t` computes the convergent power series
`∑ g_n (p / t) ^ n`. -/
theorem hasSum_eval_ofPowerSeriesU (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) (g : PowerSeries ℤ_[p]) :
    HasSum (fun n : ℕ ↦ padicIntAlgebraMap p K (PowerSeries.coeff n g) * ((p : K) / t) ^ n)
      (eval ht (ofPowerSeriesU g)) := by
  have hinj : Function.Injective (fun n : ℕ ↦ -(n : ℤ)) := neg_injective.comp Nat.cast_injective
  refine ((hinj.hasSum_iff fun m hm ↦ ?_).2 (hasSum_eval ht (ofPowerSeriesU g))).congr_fun
    fun n ↦ ?_
  · have hpos : 0 < m := by by_contra! h0; exact hm ⟨(-m).toNat, by dsimp; omega⟩
    simp [coeff_ofPowerSeriesU_of_pos g hpos]
  · simp only [Function.comp_apply]
    rw [coeff_ofPowerSeriesU_neg_natCast, map_mul, map_pow, map_natCast,
      zpow_neg, zpow_natCast, ← inv_pow, mul_right_comm, ← mul_pow, div_eq_mul_inv, mul_comm]

/-- Extension of `eval ht` to `Localization.Away (T : AnnularRing p)`. -/
def evalAway (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) : Localization.Away (T : AnnularRing p) →+* K :=
  IsLocalization.Away.lift (T : AnnularRing p) (g := eval ht)
    (by rw [eval_T]; exact (ne_zero_of_norm_mem_Ioo ht).isUnit)

@[simp] theorem evalAway_algebraMap (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) (x : AnnularRing p) :
    evalAway ht (algebraMap (AnnularRing p) (Localization.Away (T : AnnularRing p)) x) =
      eval ht x := IsLocalization.Away.lift_eq _ _ x

end NormedAlgebra

end Eval

/-! ### Joint injectivity on the `ℂ_p`-annulus and integral domain structure -/

section JointInjectivity

private theorem exists_padicComplex_norm_rpow {q : ℚ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ t : ℂ_[p], ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1 ∧ ‖t‖ = (p : ℝ) ^ (-(q : ℝ)) := by
  obtain ⟨t, htval⟩ := PadicComplex.addValuation_surjective (p := p) (q : WithTop ℚ)
  have hnorm : ‖t‖ = (p : ℝ) ^ (-(q : ℝ)) :=
    (PadicComplex.addValuation_eq_coe_iff (p := p)).1 htval
  have hq0' : (0 : ℝ) < q := mod_cast hq0
  have hq1' : (q : ℝ) < 1 := mod_cast hq1
  exact ⟨t, ⟨hnorm ▸ (Real.rpow_neg_one (p : ℝ)).symm.trans_lt
    (Real.rpow_lt_rpow_of_exponent_lt (one_lt_p (p := p)) (neg_lt_neg_iff.2 hq1')),
    hnorm ▸ (Real.rpow_lt_rpow_of_exponent_lt (one_lt_p (p := p))
      (neg_neg_of_pos hq0')).trans_eq (Real.rpow_zero (p : ℝ))⟩, hnorm⟩

private def valScore (x : AnnularRing p) (m : ℤ) : ℤ := -2 * ((x.coeff m).valuation : ℤ) - m

private theorem valScore_le_neg_abs {x : AnnularRing p} {m : ℤ} (hm : x.coeff m ≠ 0) :
    valScore x m ≤ -|m| := by
  have h := x.norm_coeff_le m
  rw [PadicInt.norm_eq_zpow_neg_valuation hm, zpow_le_zpow_iff_right₀ (one_lt_p (p := p))] at h
  rw [valScore]; rcases le_or_gt 0 m with h0 | h0 <;> [rw [abs_of_nonneg h0]; rw [abs_of_neg h0]]
    <;> omega

private theorem exists_dominant_index {x : AnnularRing p} (hx : x ≠ 0) :
    ∃ (R : ℕ) (m₀ : ℤ), x.coeff m₀ ≠ 0 ∧ ∀ ⦃B : ℕ⦄, R + 1 ≤ B → ∀ ⦃m : ℤ⦄, m ≠ m₀ →
      x.coeff m ≠ 0 → (2 * (B : ℤ) + 1) * valScore x m + m <
        (2 * (B : ℤ) + 1) * valScore x m₀ + m₀ := by
  classical
  have ⟨m₁, hm₁⟩ : ∃ m₁ : ℤ, x.coeff m₁ ≠ 0 := by
    by_contra! hall; exact hx (AnnularRing.ext (funext hall))
  set R : ℕ := m₁.natAbs + 2 * (x.coeff m₁).valuation
  let S : Finset ℤ := (Finset.Icc (-(R : ℤ)) R).filter fun m ↦ x.coeff m ≠ 0
  have hm₁S : m₁ ∈ S := Finset.mem_filter.2
    ⟨Finset.mem_Icc.2 (by have := Int.abs_eq_natAbs m₁; omega), hm₁⟩
  let Smax : Finset ℤ := S.filter fun m ↦ valScore x m = S.sup' ⟨m₁, hm₁S⟩ (valScore x)
  have hSmax : Smax.Nonempty := by
    obtain ⟨m, hmS, hmM⟩ := Finset.exists_mem_eq_sup' ⟨m₁, hm₁S⟩ (valScore x)
    exact ⟨m, Finset.mem_filter.2 ⟨hmS, hmM.symm⟩⟩
  let m₀ : ℤ := Smax.max' hSmax
  have hm₀_mem : m₀ ∈ Smax := Finset.max'_mem Smax hSmax
  obtain ⟨hm₀S, hm₀_score⟩ := Finset.mem_filter.1 hm₀_mem
  obtain ⟨hm₀Icc, hm₀_ne⟩ := Finset.mem_filter.1 hm₀S
  have hm₀_Icc := Finset.mem_Icc.1 hm₀Icc
  refine ⟨R, m₀, hm₀_ne, fun B hB m hm_ne hm0 ↦ ?_⟩
  have hRB : (R : ℤ) < B := by omega
  by_cases hmIcc : -(R : ℤ) ≤ m ∧ m ≤ R
  · have hmS : m ∈ S := Finset.mem_filter.2 ⟨Finset.mem_Icc.2 hmIcc, hm0⟩
    rcases ((Finset.le_sup' (valScore x) hmS).trans_eq hm₀_score.symm).eq_or_lt with heq | hlt
    · have hmlt : m < m₀ := lt_of_le_of_ne
        (Finset.le_max' Smax m (Finset.mem_filter.2 ⟨hmS, heq.trans hm₀_score⟩)) hm_ne
      rw [heq]; linarith
    · have hle : valScore x m ≤ valScore x m₀ - 1 := by omega
      nlinarith [hle, hRB, hmIcc.2, hm₀_Icc.1]
  · have habs : (R : ℤ) + 1 ≤ |m| := by
      rcases le_or_gt 0 m with h0 | h0 <;> [rw [abs_of_nonneg h0]; rw [abs_of_neg h0]] <;> omega
    have hm₁_ge : -(R : ℤ) ≤ valScore x m₁ := by dsimp [valScore, R]; omega
    have hm₀_ge : -(R : ℤ) ≤ valScore x m₀ :=
      hm₁_ge.trans (hm₀_score ▸ Finset.le_sup' (valScore x) hm₁S)
    nlinarith [valScore_le_neg_abs hm0, le_abs_self m, hRB, hm₀_Icc.1, hm₀_ge]

private theorem exists_forall_eval_ne_zero_of_ne_zero {x : AnnularRing p} (hx : x ≠ 0) :
    ∃ B₀ : ℕ, ∀ ⦃B : ℕ⦄, B₀ ≤ B → ∀ (t : ℂ_[p]) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1),
      ‖t‖ = (p : ℝ) ^ (-((B : ℝ) / (2 * B + 1))) → eval ht x ≠ 0 := by
  classical
  obtain ⟨R, m₀, hm₀_ne, hdom⟩ := exists_dominant_index hx
  refine ⟨R + 1, fun B hB t ht hnorm_t ↦ ?_⟩
  have h2B1_pos : (0 : ℝ) < 2 * (B : ℝ) + 1 := by positivity
  let f : ℤ → ℂ_[p] := fun m ↦ padicIntAlgebraMap p ℂ_[p] (x.coeff m) * t ^ m
  let E : ℤ → ℤ := fun m ↦ -(((x.coeff m).valuation : ℤ) * (2 * B + 1)) - B * m
  have hnorm_eq {m : ℤ} (hm : x.coeff m ≠ 0) : ‖f m‖ = (p : ℝ) ^ ((E m : ℝ) / (2 * B + 1)) := by
    have hf_norm : ‖f m‖ = ‖x.coeff m‖ * ‖t‖ ^ m := by simp [f, norm_mul, norm_zpow]
    rw [hf_norm, PadicInt.norm_eq_zpow_neg_valuation hm, hnorm_t, ← Real.rpow_intCast,
      ← Real.rpow_intCast (n := m), ← Real.rpow_mul p_pos.le, ← Real.rpow_add p_pos]
    congr 1; simp only [E]; push_cast; field_simp [h2B1_pos.ne']; ring
  have hE_le {m : ℤ} (hm_ne : m ≠ m₀) (hm0 : x.coeff m ≠ 0) : E m ≤ E m₀ - 1 := by
    have h2 := hdom hB hm_ne hm0
    have h2E (k : ℤ) : 2 * E k = (2 * (B : ℤ) + 1) * valScore x k + k := by
      simp only [E, valScore]; ring
    rw [← h2E m, ← h2E m₀] at h2; omega
  set r : ℝ := (p : ℝ) ^ (((E m₀ - 1 : ℤ) : ℝ) / (2 * B + 1))
  have hr_nonneg : 0 ≤ r := Real.rpow_nonneg p_pos.le _
  have hr_lt : r < ‖f m₀‖ := (hnorm_eq hm₀_ne).symm ▸ Real.rpow_lt_rpow_of_exponent_lt
    (one_lt_p (p := p)) (div_lt_div_of_pos_right (by exact_mod_cast sub_one_lt (E m₀)) h2B1_pos)
  have htail_norm : ‖∑' m : ℤ, if m = m₀ then (0 : ℂ_[p]) else f m‖ ≤ r :=
    IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hr_nonneg fun m ↦ by
      split_ifs with hm_eq
      · simpa using hr_nonneg
      · by_cases hm0 : x.coeff m = 0
        · simpa [f, hm0] using hr_nonneg
        · rw [hnorm_eq hm0]
          exact Real.rpow_le_rpow_of_exponent_le (one_lt_p (p := p)).le
            (div_le_div_of_nonneg_right (by exact_mod_cast hE_le hm_eq hm0) h2B1_pos.le)
  intro heval0
  have hsplit := (summable_padicIntAlgebraMap_coeff_mul_zpow ht x).tsum_eq_add_tsum_ite m₀
  rw [← eval_apply ht x, heval0] at hsplit
  have hfeq := congr_arg norm (eq_neg_of_add_eq_zero_left hsplit.symm)
  rw [norm_neg] at hfeq
  linarith

private theorem exists_padicComplex_ratio (B : ℕ) (hB : 1 ≤ B) :
    ∃ t : ℂ_[p], ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1 ∧ ‖t‖ = (p : ℝ) ^ (-((B : ℝ) / (2 * B + 1))) := by
  have hB0 : (0 : ℚ) < B := by positivity
  have h2B1 : (0 : ℚ) < 2 * B + 1 := by positivity
  obtain ⟨t, ht, hnorm⟩ := exists_padicComplex_norm_rpow (p := p) (div_pos hB0 h2B1)
    ((div_lt_one h2B1).2 (by linarith))
  exact ⟨t, ht, by simpa using hnorm⟩

/-- Two elements of `AnnularRing p` agreeing at every point of `p⁻¹ < ‖t‖ < 1` in `ℂ_p` are equal.
-/
theorem eq_of_forall_eval_eq {x y : AnnularRing p}
    (h : ∀ (t : ℂ_[p]) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1), eval ht x = eval ht y) : x = y := by
  by_contra hxy
  obtain ⟨B₀, hB₀⟩ := exists_forall_eval_ne_zero_of_ne_zero (sub_ne_zero.2 hxy)
  obtain ⟨t, ht, hnorm⟩ := exists_padicComplex_ratio (p := p) (max B₀ 1) (le_max_right _ _)
  exact hB₀ (le_max_left _ _) t ht hnorm (by rw [map_sub, h t ht, sub_self])

instance instNoZeroDivisors : NoZeroDivisors (AnnularRing p) where
  eq_zero_or_eq_zero_of_mul_eq_zero {x y} hxy := by
    by_contra! hne
    obtain ⟨Bx, hBx⟩ := exists_forall_eval_ne_zero_of_ne_zero hne.1
    obtain ⟨By, hBy⟩ := exists_forall_eval_ne_zero_of_ne_zero hne.2
    obtain ⟨t, ht, hnorm⟩ :=
      exists_padicComplex_ratio (p := p) (max (max Bx By) 1) (le_max_right _ _)
    exact mul_ne_zero (hBx ((le_max_left Bx By).trans (le_max_left _ _)) t ht hnorm)
      (hBy ((le_max_right Bx By).trans (le_max_left _ _)) t ht hnorm)
      (by rw [← map_mul, hxy, map_zero])

instance instIsDomain : IsDomain (AnnularRing p) := NoZeroDivisors.to_isDomain _
instance instIsDomainLocalizationAway : IsDomain (Localization.Away (T : AnnularRing p)) :=
  Localization.Away.isDomain (T_ne_zero (p := p))

end JointInjectivity

end AnnularRing

/-! ### Continuity and non-Lipschitz behaviour on `AnnularLaurent p hα` -/

namespace AnnularLaurent

open AnnularRing

variable {p : ℕ} [Fact p.Prime] {α : ℝ}

instance instIsDomain (hα : α ∈ Set.Ioo 0 1) : IsDomain (AnnularLaurent p hα) :=
  IsLocalization.Away.isDomain (AnnularLaurent p hα) (T_ne_zero (p := p))

section Eval
variable {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K] [CompleteSpace K] {t : K}

/-- Extension of `AnnularRing.eval ht` to `AnnularLaurent p hα`. -/
def eval (hα : α ∈ Set.Ioo 0 1) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) : AnnularLaurent p hα →+* K :=
  AnnularRing.evalAway ht

@[simp] theorem eval_algebraMap (hα : α ∈ Set.Ioo 0 1) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1)
    (x : AnnularRing p) :
    eval hα ht (algebraMap (AnnularRing p) (AnnularLaurent p hα) x) = AnnularRing.eval ht x :=
  evalAway_algebraMap ht x

@[simp] theorem eval_ofRadius {β : ℝ} (hα : α ∈ Set.Ioo 0 1) (hβ : β ∈ Set.Ioo 0 1)
    (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) (z : AnnularLaurent p hα) :
    eval hβ ht (ofRadius hα hβ z) = eval hα ht z := by
  have hext : (eval hβ ht).comp (ofRadius hα hβ).toRingHom = eval hα ht :=
    IsLocalization.ringHom_ext (Submonoid.powers (T : AnnularRing p)) <| by
      ext x; simp [RingHom.comp_apply]
  exact RingHom.congr_fun hext z

theorem eval_unitT (hα : α ∈ Set.Ioo 0 1) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) :
    eval hα ht (unitT p hα) = t := by rw [val_unitT, eval_algebraMap, eval_T]

@[simp] theorem eval_zpow_unitT (hα : α ∈ Set.Ioo 0 1) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) (r : ℤ) :
    eval hα ht (unitT p hα ^ r).val = t ^ r := by
  have hnat (n : ℕ) : eval hα ht (unitT p hα ^ (n : ℤ)).val = t ^ (n : ℤ) := by
    rw [zpow_natCast, Units.val_pow_eq_pow_val, map_pow, eval_unitT, zpow_natCast]
  rcases le_or_gt 0 r with hr | hr
  · lift r to ℕ using hr; exact hnat r
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, r = -n := ⟨(-r).toNat, by omega⟩
    have hmul : eval hα ht (unitT p hα ^ (-(n : ℤ))).val * t ^ (n : ℤ) = 1 := by
      rw [← hnat n, ← map_mul, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero,
        Units.val_one, map_one]
    exact (eq_inv_of_mul_eq_one_left hmul).trans (zpow_neg t n).symm

/-- For `z ∈ AnnularLaurent p hα`, the two-sided series `∑ coeff z m * t ^ m` sums to
`eval hα ht z`. -/
theorem hasSum_eval (hα : α ∈ Set.Ioo 0 1) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1)
    (z : AnnularLaurent p hα) :
    HasSum (fun m : ℤ ↦ padicIntAlgebraMap p K (coeff z m) * t ^ m) (eval hα ht z) := by
  have ht0 : t ≠ 0 := ne_zero_of_norm_mem_Ioo ht
  obtain ⟨k, x, hx⟩ := IsLocalization.Away.surj (T : AnnularRing p) z
  have hval : eval hα ht z * t ^ (k : ℤ) = AnnularRing.eval ht x := by
    simpa [map_mul, map_pow, eval_algebraMap, eval_T, zpow_natCast] using congr_arg (eval hα ht) hx
  have hz_val : eval hα ht z = AnnularRing.eval ht x * t ^ (-(k : ℤ)) := by
    rw [← hval, mul_assoc, ← zpow_add₀ ht0, add_neg_cancel, zpow_zero, mul_one]
  rw [hz_val]
  refine ((Equiv.addRight (k : ℤ)).hasSum_iff.2
    ((AnnularRing.hasSum_eval ht x).mul_right (t ^ (-(k : ℤ))))).congr_fun fun m ↦ ?_
  have hunit : (unitT p hα ^ (k : ℤ)).val * z =
      algebraMap (AnnularRing p) (AnnularLaurent p hα) x := by
    rw [zpow_natCast, Units.val_pow_eq_pow_val, val_unitT, mul_comm, hx]
  have hm := congr_arg (fun w ↦ coeff w (m + k)) hunit
  rw [coeff_zpow_unitT_mul, add_sub_cancel_right, coeff_algebraMap] at hm
  simp only [Function.comp_apply, Equiv.coe_addRight, hm, mul_assoc, ← zpow_add₀ ht0,
    add_neg_cancel_right]

/-- When `α < ‖t‖`, `eval hα ht` is not Lipschitz on `AnnularLaurent p hα`. -/
theorem not_lipschitzWith_eval_of_lt (hα : α ∈ Set.Ioo 0 1) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1)
    (hαt : α < ‖t‖) (c : ℝ≥0) : ¬ LipschitzWith c (eval hα ht) := fun hL ↦ by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (c : ℝ) ((one_lt_div hα.1).2 hαt)
  have hpow_norm : ‖algebraMap (AnnularRing p) (AnnularLaurent p hα) T ^ n‖ = α ^ n := by
    have h := Huber.tateGauge_zpow_mul (A₀ := ringOfDefinition p hα) (ϖ := unitT p hα)
      (inv_pos.2 hα.1) n 1
    simpa [norm_def, zpow_natCast, Units.val_pow_eq_pow_val, ← norm_def hα 1] using h
  have hdist := hL.dist_le_mul (algebraMap (AnnularRing p) (AnnularLaurent p hα) T ^ n) 0
  rw [map_zero, dist_zero_right, dist_zero_right, map_pow, eval_algebraMap, eval_T,
    norm_pow, hpow_norm] at hdist
  linarith [(div_pow ‖t‖ α n).trans_le ((div_le_iff₀ (pow_pos hα.1 n)).2 hdist)]

section Ultrametric
variable [IsUltrametricDist K]

/-- In an ultrametric field `K`, the Tate gauge bound `‖z‖ ≤ α ^ r` implies the annulus
evaluation bound `‖eval hα ht z‖ ≤ ‖t‖ ^ r`. -/
theorem norm_eval_le_zpow_of_norm_le_zpow (hα : α ∈ Set.Ioo 0 1)
    (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) {z : AnnularLaurent p hα} {r : ℤ} (hz : ‖z‖ ≤ α ^ r) :
    ‖eval hα ht z‖ ≤ ‖t‖ ^ r := by
  obtain ⟨x, hx⟩ := (mem_ringOfDefinition_iff _).1 ((norm_le_zpow_iff hα z r).1 hz)
  have hz_eq : z = (unitT p hα ^ r).val * algebraMap (AnnularRing p) (AnnularLaurent p hα) x := by
    rw [hx, ← mul_assoc, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one,
      one_mul]
  rw [hz_eq, map_mul, eval_zpow_unitT, eval_algebraMap, norm_mul, norm_zpow]
  exact mul_le_of_le_one_right (zpow_nonneg (norm_nonneg t) r) (norm_eval_le_one ht x)

/-- Every annulus evaluation into a complete ultrametric field over `ℚ_p` is continuous. -/
theorem continuous_eval (hα : α ∈ Set.Ioo 0 1) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) :
    Continuous (eval hα ht) := by
  refine continuous_of_continuousAt_zero (eval hα ht).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero, Metric.tendsto_nhds]; intro ε hε
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hε ht.2
  refine Metric.eventually_nhds_iff.2 ⟨α ^ (r : ℤ), zpow_pos hα.1 _, fun z hz ↦ ?_⟩
  rw [dist_zero_right] at hz ⊢
  exact (norm_eval_le_zpow_of_norm_le_zpow hα ht hz.le).trans_lt (by simpa [zpow_natCast] using hr)

end Ultrametric
end Eval

/-- For every `α ∈ (0, 1)`, some `t ∈ ℂ_p` in `p⁻¹ < ‖t‖ < 1` gives a continuous non-Lipschitz
evaluation on `AnnularLaurent p hα`. -/
theorem exists_continuous_not_lipschitzWith_eval (hα : α ∈ Set.Ioo 0 1) :
    ∃ (t : ℂ_[p]) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1),
      Continuous (eval hα ht) ∧ ∀ c : ℝ≥0, ¬ LipschitzWith c (eval hα ht) := by
  have hp_pos : (0 : ℝ) < p := p_pos (p := p)
  let β : ℝ := max (p : ℝ)⁻¹ α
  have hβ_pos : 0 < β := lt_max_of_lt_right hα.1
  have hβ_inv : 1 < β⁻¹ := (one_lt_inv₀ hβ_pos).2
    (max_lt (inv_lt_one_of_one_lt₀ (one_lt_p (p := p))) hα.2)
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (p : ℝ) hβ_inv
  let N : ℕ := m + 2
  have hN_pos : (0 : ℝ) < N := by positivity
  have hmN : (p : ℝ) < (β⁻¹) ^ N := hm.trans_le (pow_le_pow_right₀ hβ_inv.le (by omega))
  obtain ⟨t, ht, hnorm⟩ := exists_padicComplex_norm_rpow (p := p) (q := 1 / N) (by positivity)
    ((div_lt_one (by positivity : (0 : ℚ) < N)).2 (by exact_mod_cast (by omega : 1 < N)))
  have hnorm' : ‖t‖ = (p : ℝ) ^ (-((1 : ℝ) / N)) := by simpa using hnorm
  have hβ_lt_t : β < ‖t‖ := by
    have hrpow := Real.rpow_lt_rpow hp_pos.le hmN (div_pos zero_lt_one hN_pos)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (inv_nonneg.2 hβ_pos.le),
      mul_one_div_cancel hN_pos.ne', Real.rpow_one] at hrpow
    have hinv := inv_strictAnti₀ (Real.rpow_pos_of_pos hp_pos _) hrpow
    rwa [inv_inv, ← Real.rpow_neg hp_pos.le, ← hnorm'] at hinv
  exact ⟨t, ht, continuous_eval hα ht,
    not_lipschitzWith_eval_of_lt hα ht ((le_max_right _ _).trans_lt hβ_lt_t)⟩

end AnnularLaurent
end TauCeti
