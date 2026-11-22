/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Lipschitz
public import TauCeti.NumberTheory.Padics.AnnularRing.Gauge
public import TauCeti.NumberTheory.Padics.AnnularRing.Presentation
public import TauCeti.NumberTheory.Padics.Basic
public import TauCeti.NumberTheory.Padics.Complex.Valuation
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# Specialisation of `ℤ_p⟦T, p/T⟧` on the open annulus `p⁻¹ < |t| < 1`

For a complete normed field extension `K` of `ℚ_p` (ultrametric via
`IsUltrametricDist.of_normedAlgebra`) and `t ∈ K` with `p⁻¹ < ‖t‖ < 1`, `∑ d_m t ^ m` defines
`TauCeti.AnnularRing.eval ht : AnnularRing p →+* K` (`T ↦ t`, `U ↦ p / t`), bounded by `1`.
Extending across `Localization.Away T` gives `TauCeti.AnnularLaurent.eval hα ht`, continuous for
`α ∈ (0, 1)`, yet not Lipschitz when `α < ‖t‖`. While `ℚ_p` has no points in `(p⁻¹, 1)`
`ℂ_p`-evaluations are jointly injective (`TauCeti.AnnularRing.eq_of_forall_eval_eq`,
`mem_span_iff_forall_eval_annulus`), making `AnnularRing p` and `AnnularLaurent p hα` domains.

## References

* R. Liu, D. Wan and L. Xiao, *The eigencurve over the boundary of weight space*, Duke Math. J.
  166 (2017), §§2–3.
-/

public noncomputable section

open Filter Topology
open scoped NNReal

namespace TauCeti
namespace AnnularRing

/-- Any element `t` whose norm lies in `(p⁻¹, 1)` is nonzero. -/
theorem ne_zero_of_norm_mem_Ioo {p : ℕ} {K : Type*} [NormedAddGroup K] {t : K}
    (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) : t ≠ 0 :=
  norm_pos_iff.1 ((inv_nonneg.2 (Nat.cast_nonneg p)).trans_lt ht.1)

variable {p : ℕ} [Fact p.Prime]
private theorem one_lt_p : (1 : ℝ) < p := mod_cast (Fact.out : p.Prime).one_lt
private theorem p_pos : (0 : ℝ) < p := zero_lt_one.trans one_lt_p

section Eval
variable {K : Type*} [NormedField K] {t : K}

private theorem inv_p_mul_norm_lt_one (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) :
    ((p : ℝ) * ‖t‖)⁻¹ < 1 :=
  inv_lt_one_of_one_lt₀ <| (mul_inv_cancel₀ (p_pos (p := p)).ne').symm.trans_lt
    (mul_lt_mul_of_pos_left ht.1 (p_pos (p := p)))
omit [Fact p.Prime] in
private theorem zpow_min_neg_mul_zpow (t : K) (n : ℕ) :
    (p : ℝ) ^ min (0 : ℤ) (-n) * ‖t‖ ^ (-(n : ℤ)) = (((p : ℝ) * ‖t‖)⁻¹) ^ n := by
  rw [min_eq_right (by omega)]; simp [mul_pow]; ring

section NormedAlgebra
variable [NormedAlgebra ℚ_[p] K]

/-- Norm of a scalar-monomial product `c * t ^ m` for `c : ℤ_p`: `‖c‖ * ‖t‖ ^ m`. -/
theorem norm_padicIntAlgebraMap_mul_zpow (c : ℤ_[p]) (t : K) (m : ℤ) :
    ‖padicIntAlgebraMap p K c * t ^ m‖ = ‖c‖ * ‖t‖ ^ m := by
  rw [norm_mul, norm_padicIntAlgebraMap, norm_zpow]
/-- Termwise norm bound: `‖x.coeff m * t ^ m‖ ≤ p ^ min 0 m * ‖t‖ ^ m`. -/
theorem norm_padicIntAlgebraMap_coeff_mul_zpow_le (x : AnnularRing p) (t : K) (m : ℤ) :
    ‖padicIntAlgebraMap p K (x.coeff m) * t ^ m‖ ≤ (p : ℝ) ^ min 0 m * ‖t‖ ^ m := by
  rw [norm_padicIntAlgebraMap_mul_zpow]
  exact mul_le_mul_of_nonneg_right (x.norm_coeff_le m) (zpow_nonneg (norm_nonneg t) m)
/-- On `p⁻¹ < ‖t‖ < 1`, every term `x.coeff m * t ^ m` has norm `≤ 1`. -/
theorem norm_padicIntAlgebraMap_coeff_mul_zpow_le_one (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1)
    (x : AnnularRing p) (m : ℤ) : ‖padicIntAlgebraMap p K (x.coeff m) * t ^ m‖ ≤ 1 := by
  refine (norm_padicIntAlgebraMap_coeff_mul_zpow_le x t m).trans ?_
  rcases le_or_gt 0 m with hm | hm
  · lift m to ℕ using hm
    simpa [min_eq_left (Nat.cast_nonneg m)] using pow_le_one₀ (norm_nonneg t) ht.2.le
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = -n := ⟨(-m).toNat, by omega⟩
    rw [zpow_min_neg_mul_zpow]; exact pow_le_one₀ (by positivity) (inv_p_mul_norm_lt_one ht).le

/-- On `p⁻¹ < ‖t‖ < 1`, `∑ ‖x.coeff m * t ^ m‖` is summable via geometric bounds. -/
theorem summable_norm_padicIntAlgebraMap_coeff_mul_zpow (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1)
    (x : AnnularRing p) : Summable fun m : ℤ ↦ ‖padicIntAlgebraMap p K (x.coeff m) * t ^ m‖ :=
  Summable.of_nat_of_neg (Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (fun n ↦ by simpa [min_eq_left (Nat.cast_nonneg n)] using
        norm_padicIntAlgebraMap_coeff_mul_zpow_le x t n)
      (summable_geometric_of_lt_one (norm_nonneg t) ht.2))
    (Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (fun n ↦ (norm_padicIntAlgebraMap_coeff_mul_zpow_le x t (-n)).trans_eq
        (zpow_min_neg_mul_zpow t n))
      (summable_geometric_of_lt_one (by positivity) (inv_p_mul_norm_lt_one ht)))

private theorem norm_evalTUTerm_eval_le (F : MvPowerSeries (Fin 2) ℤ_[p]) (d : Fin 2 →₀ ℕ) :
    ‖padicIntAlgebraMap p K (MvPowerSeries.coeff d F) * t ^ d 0 * ((p : K) / t) ^ d 1‖ ≤
      ‖t‖ ^ d 0 * (((p : ℝ) * ‖t‖)⁻¹) ^ d 1 := by
  have hpK : ‖(p : K)‖ = (p : ℝ)⁻¹ := by
    simpa [map_natCast] using norm_padicIntAlgebraMap (K := K) (p : ℤ_[p])
  rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_div, hpK, div_eq_mul_inv, mul_inv_rev,
    mul_comm (‖t‖⁻¹), norm_padicIntAlgebraMap]
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_left (pow_nonneg (norm_nonneg t) _) (PadicInt.norm_le_one _)) (by positivity)

variable [CompleteSpace K]

private theorem summable_evalTUTerm_eval (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1)
    (F : MvPowerSeries (Fin 2) ℤ_[p]) : Summable fun d : Fin 2 →₀ ℕ ↦
    padicIntAlgebraMap p K (MvPowerSeries.coeff d F) * t ^ d 0 * ((p : K) / t) ^ d 1 := by
  let e : (ℕ × ℕ) ≃ (Fin 2 →₀ ℕ) := (Finsupp.equivFunOnFinite.trans (finTwoArrowEquiv ℕ)).symm
  refine .of_norm_bounded (e.summable_iff.1 ?_) (norm_evalTUTerm_eval_le F)
  simpa [Function.comp_def, e] using
    (summable_geometric_of_lt_one (norm_nonneg t) ht.2).mul_of_nonneg
      (summable_geometric_of_lt_one (by positivity) (inv_p_mul_norm_lt_one ht))
      (fun _ ↦ pow_nonneg (norm_nonneg t) _) (fun _ ↦ pow_nonneg (by positivity) _)

/-- On `p⁻¹ < ‖t‖ < 1`, `∑ x.coeff m * t ^ m` is summable in a complete extension `K / ℚ_p`. -/
theorem summable_padicIntAlgebraMap_coeff_mul_zpow (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1)
    (x : AnnularRing p) : Summable fun m : ℤ ↦ padicIntAlgebraMap p K (x.coeff m) * t ^ m :=
  (summable_norm_padicIntAlgebraMap_coeff_mul_zpow ht x).of_norm

/-- Specialisation `AnnularRing p →+* K` at `t` (`p⁻¹ < ‖t‖ < 1`), `∑ d_m T ^ m ↦ ∑ d_m t ^ m`. -/
def eval (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) : AnnularRing p →+* K where
  toFun x := ∑' m : ℤ, padicIntAlgebraMap p K (x.coeff m) * t ^ m
  map_zero' := by simp
  map_one' := by rw [tsum_eq_single 0 fun m hm ↦ by simp [coeff_one, hm]]; simp
  map_add' x y := by
    simp_rw [coeff_add, map_add, add_mul]; exact (summable_padicIntAlgebraMap_coeff_mul_zpow
      ht x).tsum_add (summable_padicIntAlgebraMap_coeff_mul_zpow ht y)
  map_mul' x y := by
    refine ((DiscreteConvolution.hasSum_tsum_mul_sub
      (summable_norm_padicIntAlgebraMap_coeff_mul_zpow ht x)
      (summable_norm_padicIntAlgebraMap_coeff_mul_zpow ht y)).congr_fun fun m ↦ ?_).tsum_eq
    refine Eq.symm ((tsum_congr fun i ↦ ?_).trans (((hasSum_coeff_mul x y m).map
      (padicIntAlgebraMap p K)
      (continuous_padicIntAlgebraMap (continuous_algebraMap ℚ_[p] K))).mul_right (t ^ m)).tsum_eq)
    rw [mul_mul_mul_comm, ← zpow_add₀ (ne_zero_of_norm_mem_Ioo ht), add_sub_cancel, ← map_mul]; rfl

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

/-- Every annulus evaluation satisfies `‖eval ht x‖ ≤ 1`, via ultrametricity of `K`. -/
theorem norm_eval_le_one (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) (x : AnnularRing p) :
    ‖eval ht x‖ ≤ 1 := by
  have : IsUltrametricDist K := .of_normedAlgebra ℚ_[p]
  rw [eval_apply]; exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg zero_le_one
    (norm_padicIntAlgebraMap_coeff_mul_zpow_le_one ht x)

/-- Evaluating `ofPowerSeriesT f` at `t` computes `∑ f_n t ^ n`. -/
theorem hasSum_eval_ofPowerSeriesT (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) (f : PowerSeries ℤ_[p]) :
    HasSum (fun n : ℕ ↦ padicIntAlgebraMap p K (PowerSeries.coeff n f) * t ^ n)
      (eval ht (ofPowerSeriesT f)) := by
  refine ((Nat.cast_injective.hasSum_iff fun m hm ↦ ?_).2
    (hasSum_eval ht (ofPowerSeriesT f))).congr_fun fun n ↦ by simp
  have hneg : m < 0 := by by_contra! h0; lift m to ℕ using h0; exact hm ⟨m, rfl⟩
  simp [coeff_ofPowerSeriesT_of_neg f hneg]
/-- Evaluating `ofPowerSeriesU g` at `t` computes `∑ g_n (p / t) ^ n`. -/
theorem hasSum_eval_ofPowerSeriesU (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) (g : PowerSeries ℤ_[p]) :
    HasSum (fun n : ℕ ↦ padicIntAlgebraMap p K (PowerSeries.coeff n g) * ((p : K) / t) ^ n)
      (eval ht (ofPowerSeriesU g)) := by
  refine (((neg_injective.comp Nat.cast_injective).hasSum_iff fun m hm ↦ ?_).2
    (hasSum_eval ht (ofPowerSeriesU g))).congr_fun fun n ↦ ?_
  · have hpos : 0 < m := by by_contra! h0; exact hm ⟨(-m).toNat, by dsimp; omega⟩
    simp [coeff_ofPowerSeriesU_of_pos g hpos]
  · simp [coeff_ofPowerSeriesU_neg_natCast, div_eq_mul_inv, mul_pow]; ring

omit [CompleteSpace K] in
private theorem padicIntAlgebraMap_coeff_diag_mul_zpow (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1)
    (F : MvPowerSeries (Fin 2) ℤ_[p]) (m : ℤ) (k : ℕ) :
    padicIntAlgebraMap p K (MvPowerSeries.coeff (Finsupp.finTwoSubMinEquiv.symm (m, k)) F) *
        t ^ (Finsupp.finTwoSubMinEquiv.symm (m, k)) 0 *
        ((p : K) / t) ^ (Finsupp.finTwoSubMinEquiv.symm (m, k)) 1 =
      padicIntAlgebraMap p K ((p : ℤ_[p]) ^ ((-m).toNat + k) *
        MvPowerSeries.coeff (Finsupp.finTwoSubMinEquiv.symm (m, k)) F) * t ^ m := by
  have ht0 : t ≠ 0 := ne_zero_of_norm_mem_Ioo ht
  have hexp : ((m.toNat + k : ℕ) : ℤ) - (((-m).toNat + k : ℕ) : ℤ) = m := by omega
  have hpow : t ^ (m.toNat + k) / t ^ ((-m).toNat + k) = t ^ m := by
    rw [← zpow_natCast t, ← zpow_natCast t, ← zpow_sub₀ ht0, hexp]
  rw [Finsupp.finTwoSubMinEquiv_symm_apply_zero, Finsupp.finTwoSubMinEquiv_symm_apply_one,
    div_pow, ← map_natCast (padicIntAlgebraMap p K), map_mul, map_pow, mul_assoc _ (t ^ _),
    div_eq_mul_inv, mul_left_comm (t ^ _), ← div_eq_mul_inv, hpow]
  ring

/-- Evaluating `F ∈ ℤ_p⟦X_0, X_1⟧` termwise at `(t, p / t)` converges to
`eval ht (ofMvPowerSeries F)`. -/
theorem hasSum_eval_ofMvPowerSeries (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1)
    (F : MvPowerSeries (Fin 2) ℤ_[p]) :
    HasSum (fun d : Fin 2 →₀ ℕ ↦
      padicIntAlgebraMap p K (MvPowerSeries.coeff d F) * t ^ d 0 * ((p : K) / t) ^ d 1)
      (eval ht (ofMvPowerSeries F)) := by
  have hs := summable_evalTUTerm_eval ht F
  have hcomp := hs.comp_injective Finsupp.finTwoSubMinEquiv.symm.injective
  dsimp only [Function.comp_def] at hcomp
  convert hs.hasSum using 1
  rw [← Equiv.tsum_eq Finsupp.finTwoSubMinEquiv.symm, hcomp.tsum_prod' hcomp.prod_factor,
    eval_apply]
  refine tsum_congr fun m ↦ ?_
  simp_rw [padicIntAlgebraMap_coeff_diag_mul_zpow ht F m]
  rw [coeff_ofMvPowerSeries F m]
  have hsum : Summable fun k : ℕ ↦ (p : ℤ_[p]) ^ ((-m).toNat + k) *
      MvPowerSeries.coeff (Finsupp.finTwoSubMinEquiv.symm (m, k)) F := by
    simpa [pow_add, mul_assoc] using (PadicInt.summable_pow_mul
      (fun k ↦ MvPowerSeries.coeff (Finsupp.finTwoSubMinEquiv.symm (m, k)) F)).mul_left
      ((p : ℤ_[p]) ^ (-m).toNat)
  exact ((hsum.hasSum.map (padicIntAlgebraMap p K)
    (continuous_padicIntAlgebraMap (continuous_algebraMap ℚ_[p] K))).mul_right (t ^ m)).tsum_eq.symm
end NormedAlgebra
end Eval

/-! ### Joint injectivity on the `ℂ_p`-annulus and integral domain structure -/

section JointInjectivity

private def valScore (x : AnnularRing p) (m : ℤ) : ℤ := -2 * ((x.coeff m).valuation : ℤ) - m
private theorem valScore_le_neg_abs {x : AnnularRing p} {m : ℤ} (hm : x.coeff m ≠ 0) :
    valScore x m ≤ -|m| := by
  have h := x.norm_coeff_le m
  rw [PadicInt.norm_eq_zpow_neg_valuation hm, zpow_le_zpow_iff_right₀ (one_lt_p (p := p))] at h
  rw [valScore]; cases abs_cases m <;> omega

private theorem exists_dominant_index {x : AnnularRing p} (hx : x ≠ 0) :
    ∃ (R : ℕ) (m₀ : ℤ), x.coeff m₀ ≠ 0 ∧ ∀ ⦃B : ℕ⦄, R + 1 ≤ B → ∀ ⦃m : ℤ⦄, m ≠ m₀ → x.coeff m ≠ 0 →
      (2 * (B : ℤ) + 1) * valScore x m + m < (2 * (B : ℤ) + 1) * valScore x m₀ + m₀ := by
  classical
  have ⟨m₁, hm₁⟩ : ∃ m₁ : ℤ, x.coeff m₁ ≠ 0 := Classical.byContradiction fun h ↦
    hx (AnnularRing.ext (funext <| by simpa using h))
  set R : ℕ := m₁.natAbs + 2 * (x.coeff m₁).valuation
  let S : Finset ℤ := (Finset.Icc (-(R : ℤ)) R).filter fun m ↦ x.coeff m ≠ 0
  have hm₁S : m₁ ∈ S :=
    Finset.mem_filter.2 ⟨Finset.mem_Icc.2 (by have := Int.abs_eq_natAbs m₁; omega), hm₁⟩
  let Smax : Finset ℤ := S.filter fun m ↦ valScore x m = S.sup' ⟨m₁, hm₁S⟩ (valScore x)
  have hSmax : Smax.Nonempty := let ⟨m, hm⟩ := Finset.exists_mem_eq_sup' ⟨m₁, hm₁S⟩ (valScore x)
    ⟨m, Finset.mem_filter.2 ⟨hm.1, hm.2.symm⟩⟩
  let m₀ : ℤ := Smax.max' hSmax
  obtain ⟨hm₀S, hm₀_score⟩ := Finset.mem_filter.1 (Finset.max'_mem Smax hSmax)
  obtain ⟨hm₀_Icc, hm₀_ne⟩ := Finset.mem_filter.1 hm₀S; rw [Finset.mem_Icc] at hm₀_Icc
  refine ⟨R, m₀, hm₀_ne, fun B hB m hm_ne hm0 ↦ ?_⟩; have hRB : (R : ℤ) < B := by omega
  by_cases hmIcc : -(R : ℤ) ≤ m ∧ m ≤ R
  · have hmS : m ∈ S := Finset.mem_filter.2 ⟨Finset.mem_Icc.2 hmIcc, hm0⟩
    rcases ((Finset.le_sup' (valScore x) hmS).trans_eq hm₀_score.symm).eq_or_lt with heq | hlt
    · rw [heq]; linarith [lt_of_le_of_ne (Finset.le_max' Smax m
        (Finset.mem_filter.2 ⟨hmS, heq.trans hm₀_score⟩)) hm_ne]
    · nlinarith [Int.le_sub_one_of_lt hlt, hRB, hmIcc.2, hm₀_Icc.1]
  · have habs : (R : ℤ) + 1 ≤ |m| := by cases abs_cases m <;> omega
    have hm₀_ge : -(R : ℤ) ≤ valScore x m₀ := (by dsimp [valScore, R]; omega :
      -(R : ℤ) ≤ valScore x m₁).trans (hm₀_score ▸ Finset.le_sup' (valScore x) hm₁S)
    nlinarith [valScore_le_neg_abs hm0, le_abs_self m, hRB, hm₀_Icc.1, hm₀_ge]

private theorem exists_forall_eval_ne_zero_of_ne_zero {x : AnnularRing p} (hx : x ≠ 0) :
    ∃ B₀ : ℕ, ∀ ⦃B : ℕ⦄, B₀ ≤ B → ∀ (t : ℂ_[p]) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1),
      ‖t‖ = (p : ℝ) ^ (-((B : ℝ) / (2 * B + 1))) → eval ht x ≠ 0 := by
  classical obtain ⟨R, m₀, hm₀_ne, hdom⟩ := exists_dominant_index hx
  refine ⟨R + 1, fun B hB t ht hnorm_t heval0 ↦ ?_⟩
  have h2B1_pos : (0 : ℝ) < 2 * (B : ℝ) + 1 := by positivity
  let f : ℤ → ℂ_[p] := fun m ↦ padicIntAlgebraMap p ℂ_[p] (x.coeff m) * t ^ m
  let E : ℤ → ℤ := fun m ↦ -(((x.coeff m).valuation : ℤ) * (2 * B + 1)) - B * m
  have hnorm_eq {m : ℤ} (hm : x.coeff m ≠ 0) : ‖f m‖ = (p : ℝ) ^ ((E m : ℝ) / (2 * B + 1)) := by
    dsimp only [f]; rw [norm_padicIntAlgebraMap_mul_zpow, PadicInt.norm_eq_zpow_neg_valuation hm,
      hnorm_t, ← Real.rpow_intCast, ← Real.rpow_intCast (n := m), ← Real.rpow_mul p_pos.le,
      ← Real.rpow_add p_pos]; congr 1; simp only [E]; push_cast; field_simp [h2B1_pos.ne']; ring
  have hE_le {m : ℤ} (hm_ne : m ≠ m₀) (hm0 : x.coeff m ≠ 0) : E m ≤ E m₀ - 1 := by
    have h2E (k : ℤ) : 2 * E k = (2 * (B : ℤ) + 1) * valScore x k + k := by
      simp [E, valScore]; ring
    have := hdom hB hm_ne hm0; rw [← h2E m, ← h2E m₀] at this; omega
  set r : ℝ := (p : ℝ) ^ (((E m₀ - 1 : ℤ) : ℝ) / (2 * B + 1))
  have hr0 : 0 ≤ r := Real.rpow_nonneg (p_pos (p := p)).le _
  have hr_lt : r < ‖f m₀‖ := (hnorm_eq hm₀_ne).symm ▸ Real.rpow_lt_rpow_of_exponent_lt
    (one_lt_p (p := p)) (div_lt_div_of_pos_right (by exact_mod_cast sub_one_lt (E m₀)) h2B1_pos)
  have htail_norm : ‖∑' m : ℤ, if m = m₀ then (0 : ℂ_[p]) else f m‖ ≤ r :=
    IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hr0 fun m ↦ by
      by_cases hm_eq : m = m₀; · simp [hm_eq, hr0]
      by_cases hm0 : x.coeff m = 0; · simp [hm_eq, f, hm0, hr0]
      rw [ite_eq_right hm_eq, hnorm_eq hm0]
      exact Real.rpow_le_rpow_of_exponent_le (one_lt_p (p := p)).le
        (div_le_div_of_nonneg_right (by exact_mod_cast hE_le hm_eq hm0) h2B1_pos.le)
  have hsplit := (summable_padicIntAlgebraMap_coeff_mul_zpow ht x).tsum_eq_add_tsum_ite m₀
  rw [← eval_apply ht x, heval0] at hsplit
  linarith [(congr_arg norm (eq_neg_of_add_eq_zero_left hsplit.symm)).trans (norm_neg _)]

private theorem exists_padicComplex_ratio (B : ℕ) (hB : 1 ≤ B) : ∃ t : ℂ_[p],
    ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1 ∧ ‖t‖ = (p : ℝ) ^ (-((B : ℝ) / (2 * B + 1))) := by
  obtain ⟨t, ht⟩ := PadicComplex.exists_norm_eq_rpow (p := p) (-((B : ℚ) / (2 * B + 1)))
  have hnorm : ‖t‖ = (p : ℝ) ^ (-((B : ℝ) / (2 * B + 1))) := by simpa using ht
  have hpos : (0 : ℝ) < 2 * B + 1 := by positivity
  refine ⟨t, ⟨?_, hnorm ▸ (Real.rpow_lt_rpow_of_exponent_lt (one_lt_p (p := p))
    (neg_lt_zero.2 (div_pos (by positivity) hpos))).trans_eq (Real.rpow_zero _)⟩, hnorm⟩
  rw [hnorm, ← Real.rpow_neg_one]; exact Real.rpow_lt_rpow_of_exponent_lt (one_lt_p (p := p)) <|
    neg_lt_neg_iff.2 ((div_lt_one hpos).2 (by exact_mod_cast (by omega : B < 2 * B + 1)))

/-- Elements of `AnnularRing p` agreeing on `p⁻¹ < ‖t‖ < 1` in `ℂ_p` are equal. -/
theorem eq_of_forall_eval_eq {x y : AnnularRing p}
    (h : ∀ (t : ℂ_[p]) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1), eval ht x = eval ht y) : x = y := by
  by_contra hxy; obtain ⟨B₀, hB₀⟩ := exists_forall_eval_ne_zero_of_ne_zero (sub_ne_zero.2 hxy)
  obtain ⟨t, ht, hnorm⟩ := exists_padicComplex_ratio (p := p) (max B₀ 1) (le_max_right _ _)
  exact hB₀ (le_max_left _ _) t ht hnorm (by rw [map_sub, h t ht, sub_self])

/-- `F ∈ ℤ_p⟦X_0, X_1⟧` lies in `(X_0 X_1 - p)` iff it vanishes on `p⁻¹ < ‖t‖ < 1` in `ℂ_p`. -/
theorem mem_span_iff_forall_eval_annulus (F : MvPowerSeries (Fin 2) ℤ_[p]) :
    F ∈ Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C (p : ℤ_[p])} ↔
      ∀ t : ℂ_[p], ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1 →
        ∑' d : Fin 2 →₀ ℕ, padicIntAlgebraMap p ℂ_[p] (MvPowerSeries.coeff d F) *
          t ^ d 0 * ((p : ℂ_[p]) / t) ^ d 1 = 0 := by
  rw [← ker_ofMvPowerSeries, RingHom.mem_ker]
  exact ⟨fun h t ht ↦ by rw [(hasSum_eval_ofMvPowerSeries ht F).tsum_eq, h, map_zero],
    fun h ↦ eq_of_forall_eval_eq fun t ht ↦ by
      rw [← (hasSum_eval_ofMvPowerSeries ht F).tsum_eq, h t ht, map_zero]⟩

instance instNoZeroDivisors : NoZeroDivisors (AnnularRing p) where
  eq_zero_or_eq_zero_of_mul_eq_zero {x y} hxy := by
    by_contra! hne; obtain ⟨Bx, hBx⟩ := exists_forall_eval_ne_zero_of_ne_zero hne.1
    obtain ⟨By, hBy⟩ := exists_forall_eval_ne_zero_of_ne_zero hne.2
    obtain ⟨t, ht, hnorm⟩ := exists_padicComplex_ratio (p := p) (max (max Bx By) 1)
      (le_max_right _ _)
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
  IsLocalization.Away.lift (T : AnnularRing p) (g := AnnularRing.eval ht)
    (by rw [AnnularRing.eval_T]; exact (ne_zero_of_norm_mem_Ioo ht).isUnit)
@[simp] theorem eval_algebraMap (hα : α ∈ Set.Ioo 0 1) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1)
    (x : AnnularRing p) : eval hα ht (algebraMap _ _ x) = AnnularRing.eval ht x :=
  IsLocalization.Away.lift_eq _ _ x
@[simp] theorem eval_algebraMap_padicInt (hα : α ∈ Set.Ioo 0 1) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1)
    (c : ℤ_[p]) :
    eval hα ht (algebraMap ℤ_[p] (AnnularLaurent p hα) c) = padicIntAlgebraMap p K c := by
  rw [IsScalarTower.algebraMap_apply ℤ_[p] (AnnularRing p), eval_algebraMap,
    AnnularRing.eval_algebraMap]
@[simp] theorem eval_ofRadius {β : ℝ} (hα : α ∈ Set.Ioo 0 1) (hβ : β ∈ Set.Ioo 0 1)
    (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) (z : AnnularLaurent p hα) :
    eval hβ ht (ofRadius hα hβ z) = eval hα ht z := by
  have hcomp : (eval hβ ht).comp (ofRadius hα hβ).toRingHom = eval hα ht :=
    IsLocalization.ringHom_ext (Submonoid.powers (T : AnnularRing p)) <| by ext x; simp
  exact RingHom.congr_fun hcomp z
theorem eval_unitT (hα : α ∈ Set.Ioo 0 1) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) :
    eval hα ht (unitT p hα) = t := by rw [val_unitT, eval_algebraMap, eval_T]
@[simp] theorem eval_zpow_unitT (hα : α ∈ Set.Ioo 0 1) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) (r : ℤ) :
    eval hα ht (unitT p hα ^ r).val = t ^ r := by
  simpa only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
    Units.val_zpow_eq_zpow_val, eval_unitT] using
    congr_arg Units.val (map_zpow (Units.map (eval hα ht).toMonoidHom) (unitT p hα) r)

/-- For `z ∈ AnnularLaurent p hα`, `∑ coeff z m * t ^ m` sums to `eval hα ht z`. -/
theorem hasSum_eval (hα : α ∈ Set.Ioo 0 1) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1)
    (z : AnnularLaurent p hα) :
    HasSum (fun m : ℤ ↦ padicIntAlgebraMap p K (coeff z m) * t ^ m) (eval hα ht z) := by
  have ht0 : t ≠ 0 := ne_zero_of_norm_mem_Ioo ht
  obtain ⟨k, x, hx⟩ := IsLocalization.Away.surj (T : AnnularRing p) z
  have hclear : (unitT p hα ^ (k : ℤ)).val * z = algebraMap (AnnularRing p) _ x := by
    rw [zpow_natCast, Units.val_pow_eq_pow_val, val_unitT, mul_comm, hx]
  have hval : eval hα ht z * t ^ (k : ℤ) = AnnularRing.eval ht x := by
    simpa [map_mul, map_pow, eval_algebraMap, eval_T, zpow_natCast] using congr_arg (eval hα ht) hx
  have heval : eval hα ht z = AnnularRing.eval ht x * t ^ (-(k : ℤ)) := by
    rw [← hval, mul_assoc, ← zpow_add₀ ht0, add_neg_cancel, zpow_zero, mul_one]
  rw [heval]
  refine ((Equiv.addRight (k : ℤ)).hasSum_iff.2
    ((AnnularRing.hasSum_eval ht x).mul_right (t ^ (-(k : ℤ))))).congr_fun fun m ↦ ?_
  have hm := congr_arg (fun w ↦ coeff w (m + k)) hclear
  rw [coeff_zpow_unitT_mul, add_sub_cancel_right, coeff_algebraMap] at hm
  rw [hm]; simp only [Function.comp_apply, Equiv.coe_addRight, mul_assoc, ← zpow_add₀ ht0,
    add_neg_cancel_right]

/-- When `α < ‖t‖`, `eval hα ht` is not Lipschitz on `AnnularLaurent p hα`. -/
theorem not_lipschitzWith_eval_of_lt (hα : α ∈ Set.Ioo 0 1)
    (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) (hαt : α < ‖t‖) (c : ℝ≥0) :
    ¬ LipschitzWith c (eval hα ht) := fun hL ↦ by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (c : ℝ) ((one_lt_div hα.1).2 hαt)
  have hpow_norm : ‖algebraMap (AnnularRing p) (AnnularLaurent p hα) T ^ n‖ = α ^ n := by
    simpa using (pseudoUniformizer p hα).norm_pow n
  have hdist := hL.dist_le_mul (algebraMap (AnnularRing p) (AnnularLaurent p hα) T ^ n) 0
  simp [hpow_norm] at hdist
  linarith [(div_pow ‖t‖ α n).trans_le ((div_le_iff₀ (pow_pos hα.1 n)).2 hdist)]

/-- The Tate gauge bound `‖z‖ ≤ α ^ r` implies `‖eval hα ht z‖ ≤ ‖t‖ ^ r`. -/
theorem norm_eval_le_zpow_of_norm_le_zpow (hα : α ∈ Set.Ioo 0 1)
    (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) {z : AnnularLaurent p hα} {r : ℤ}
    (hz : ‖z‖ ≤ α ^ r) : ‖eval hα ht z‖ ≤ ‖t‖ ^ r := by
  obtain ⟨x, hx⟩ := (mem_ringOfDefinition_iff _).1 ((norm_le_zpow_iff hα z r).1 hz)
  have hz_eq : z = (unitT p hα ^ r).val * algebraMap (AnnularRing p) _ x := by
    simp [hx, ← mul_assoc, ← Units.val_mul]
  rw [hz_eq, map_mul, eval_zpow_unitT, eval_algebraMap, norm_mul, norm_zpow]
  exact mul_le_of_le_one_right (zpow_nonneg (norm_nonneg t) r) (norm_eval_le_one ht x)

/-- Every annulus evaluation into a complete normed field extension of `ℚ_p` is continuous. -/
theorem continuous_eval (hα : α ∈ Set.Ioo 0 1) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) :
    Continuous (eval hα ht) := by
  refine continuous_of_continuousAt_zero (eval hα ht).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero, Metric.tendsto_nhds]; intro ε hε
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hε ht.2
  refine Metric.eventually_nhds_iff.2 ⟨α ^ (r : ℤ), zpow_pos hα.1 _, fun z hz ↦ ?_⟩
  rw [dist_zero_right] at hz ⊢
  exact (norm_eval_le_zpow_of_norm_le_zpow hα ht hz.le).trans_lt (by simpa [zpow_natCast] using hr)
end Eval

/-- For every `α ∈ (0, 1)`, some `t ∈ ℂ_p` in `p⁻¹ < ‖t‖ < 1` gives a continuous non-Lipschitz
evaluation on `AnnularLaurent p hα`. -/
theorem exists_continuous_not_lipschitzWith_eval (hα : α ∈ Set.Ioo 0 1) :
    ∃ (t : ℂ_[p]) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1),
      Continuous (eval hα ht) ∧ ∀ c : ℝ≥0, ¬ LipschitzWith c (eval hα ht) := by
  let β : ℝ := max (p : ℝ)⁻¹ α
  have hβ_pos : 0 < β := lt_max_of_lt_right hα.1
  have hβ_inv : 1 < β⁻¹ :=
    (one_lt_inv₀ hβ_pos).2 (max_lt (inv_lt_one_of_one_lt₀ (one_lt_p (p := p))) hα.2)
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (p : ℝ) hβ_inv
  let N : ℕ := m + 2; have hN_pos : (0 : ℝ) < N := by positivity
  obtain ⟨t, hnorm⟩ := PadicComplex.exists_norm_eq_rpow (p := p) (-(1 / N : ℚ))
  have hnorm' : ‖t‖ = (p : ℝ) ^ (-((1 : ℝ) / N)) := by simpa using hnorm
  have hβ_lt_t : β < ‖t‖ := by
    have hrpow := Real.rpow_lt_rpow (p_pos (p := p)).le (hm.trans_le
      (pow_le_pow_right₀ hβ_inv.le (by omega : m ≤ N))) (div_pos zero_lt_one hN_pos)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (inv_nonneg.2 hβ_pos.le),
      mul_one_div_cancel hN_pos.ne', Real.rpow_one] at hrpow
    exact hnorm' ▸ Real.rpow_neg (p_pos (p := p)).le _ ▸ inv_inv β ▸
      inv_strictAnti₀ (Real.rpow_pos_of_pos (p_pos (p := p)) _) hrpow
  have ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1 := ⟨(le_max_left _ _).trans_lt hβ_lt_t,
    hnorm' ▸ (Real.rpow_lt_rpow_of_exponent_lt (one_lt_p (p := p))
      (neg_lt_zero.2 (by positivity))).trans_eq (Real.rpow_zero _)⟩
  exact ⟨t, ht, continuous_eval hα ht,
    not_lipschitzWith_eval_of_lt hα ht ((le_max_right _ _).trans_lt hβ_lt_t)⟩

end AnnularLaurent
end TauCeti
