/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Lipschitz
public import TauCeti.NumberTheory.Padics.AnnularRing.Evaluation
public import TauCeti.NumberTheory.Padics.AnnularRing.Gauge
public import TauCeti.NumberTheory.Padics.Basic
public import TauCeti.NumberTheory.Padics.Complex.Valuation
import Mathlib.RingTheory.PowerSeries.Trunc
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.RingTheory.Node.Completed

/-!
# Integral domain structure and `AnnularLaurent` evaluations on `p⁻¹ < |t| < 1`

Building on `TauCeti.NumberTheory.Padics.AnnularRing.Evaluation`, this file proves that
`AnnularRing p` and `AnnularLaurent p hα` are integral domains (`TauCeti.AnnularRing.instIsDomain`,
`TauCeti.AnnularLaurent.instIsDomain`) from `TauCeti.CompletedNodeAlgebra.isDomain` via
`TauCeti.AnnularRing.quotientEquiv`. It extends `AnnularRing.eval` across `Localization.Away T` to
`TauCeti.AnnularLaurent.eval hα ht`, proves continuity in the Tate gauge topology
(`continuous_eval`), uniqueness of continuous evaluations (`eq_eval_of_continuous`), and failure of
the Lipschitz property whenever `α < ‖t‖` (`not_lipschitzWith_eval_of_lt`,
`exists_continuous_not_lipschitzWith_eval`).

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

section Eval
variable {K : Type*} [NormedField K] {t : K}

private theorem inv_p_mul_norm_lt_one (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) :
    ((p : ℝ) * ‖t‖)⁻¹ < 1 :=
  inv_lt_one_of_one_lt₀ <| (mul_inv_cancel₀ (p_pos (p := p)).ne').symm.trans_lt
    (mul_lt_mul_of_pos_left ht.1 (p_pos (p := p)))

section NormedAlgebra
variable [NormedAlgebra ℚ_[p] K] [CompleteSpace K]

/-- Evaluating `ofPowerSeriesT f` at `t` computes `∑ f_n t ^ n`. -/
theorem hasSum_eval_ofPowerSeriesT (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) (f : PowerSeries ℤ_[p]) :
    HasSum (fun n : ℕ ↦ padicIntAlgebraMap p K (PowerSeries.coeff n f) * t ^ n)
      (eval t ht.1 ht.2 (ofPowerSeriesT f)) := by
  simp_rw [padicIntAlgebraMap_apply]
  refine ((Nat.cast_injective.hasSum_iff fun m hm ↦ ?_).2
    (hasSum_eval ht.1 ht.2 (ofPowerSeriesT f))).congr_fun fun n ↦ by simp
  have hneg : m < 0 := by by_contra! h0; lift m to ℕ using h0; exact hm ⟨m, rfl⟩
  simp [coeff_ofPowerSeriesT_of_neg f hneg]

/-- Evaluating `ofPowerSeriesU g` at `t` computes `∑ g_n (p / t) ^ n`. -/
theorem hasSum_eval_ofPowerSeriesU (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) (g : PowerSeries ℤ_[p]) :
    HasSum (fun n : ℕ ↦ padicIntAlgebraMap p K (PowerSeries.coeff n g) * ((p : K) / t) ^ n)
      (eval t ht.1 ht.2 (ofPowerSeriesU g)) := by
  simp_rw [padicIntAlgebraMap_apply]
  refine (((neg_injective.comp Nat.cast_injective).hasSum_iff fun m hm ↦ ?_).2
    (hasSum_eval ht.1 ht.2 (ofPowerSeriesU g))).congr_fun fun n ↦ ?_
  · have hpos : 0 < m := by by_contra! h0; exact hm ⟨(-m).toNat, by dsimp; omega⟩
    simp [coeff_ofPowerSeriesU_of_pos g hpos]
  · simp [coeff_ofPowerSeriesU_neg_natCast, div_eq_mul_inv, mul_pow]; ring

end NormedAlgebra
end Eval

/-! ### Joint injectivity on the `ℂ_p`-annulus and integral domain structure -/

section JointInjectivity

/-- Elements of `AnnularRing p` agreeing on `p⁻¹ < ‖t‖ < 1` in `ℂ_p` are equal. -/
theorem eq_of_forall_eval_eq {x y : AnnularRing p}
    (h : ∀ (t : ℂ_[p]) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1),
      eval t ht.1 ht.2 x = eval t ht.1 ht.2 y) : x = y :=
  sub_eq_zero.1 <| eq_zero_of_forall_eval_eq_zero (K := ℂ_[p]) fun t h₀ h₁ ↦ by
    rw [map_sub, h t ⟨h₀, h₁⟩, sub_self]

instance instIsDomain : IsDomain (AnnularRing p) :=
  letI : IsDomain (CompletedNodeAlgebra ℤ_[p] (p : ℤ_[p])) :=
    CompletedNodeAlgebra.isDomain (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
      PadicInt.p_nonunit
  quotientEquiv.symm.toMulEquiv.isDomain

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

/-- Extension of `AnnularRing.eval t ht.1 ht.2` to `AnnularLaurent p hα`. -/
def eval (hα : α ∈ Set.Ioo 0 1) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) : AnnularLaurent p hα →+* K :=
  IsLocalization.Away.lift (T : AnnularRing p) (g := AnnularRing.eval t ht.1 ht.2)
    (by rw [AnnularRing.eval_T]; exact (ne_zero_of_norm_mem_Ioo ht).isUnit)
@[simp] theorem eval_algebraMap (hα : α ∈ Set.Ioo 0 1) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1)
    (x : AnnularRing p) : eval hα ht (algebraMap _ _ x) = AnnularRing.eval t ht.1 ht.2 x :=
  IsLocalization.Away.lift_eq _ _ x
@[simp] theorem eval_algebraMap_padicInt (hα : α ∈ Set.Ioo 0 1) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1)
    (c : ℤ_[p]) :
    eval hα ht (algebraMap ℤ_[p] (AnnularLaurent p hα) c) = padicIntAlgebraMap p K c := by
  rw [IsScalarTower.algebraMap_apply ℤ_[p] (AnnularRing p), eval_algebraMap,
    AnnularRing.eval_algebraMap, padicIntAlgebraMap_apply]
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
  have heval : eval hα ht z = AnnularRing.eval t ht.1 ht.2 x * t ^ (-(k : ℤ)) := by
    have hval : eval hα ht z * t ^ (k : ℤ) = AnnularRing.eval t ht.1 ht.2 x := by
      simpa [map_mul, map_pow, eval_algebraMap, eval_T, zpow_natCast] using
        congr_arg (eval hα ht) hx
    rw [← hval, mul_assoc, ← zpow_add₀ ht0, add_neg_cancel, zpow_zero, mul_one]
  rw [heval]
  simp_rw [padicIntAlgebraMap_apply]
  refine ((Equiv.addRight (k : ℤ)).hasSum_iff.2
    ((AnnularRing.hasSum_eval ht.1 ht.2 x).mul_right (t ^ (-(k : ℤ))))).congr_fun fun m ↦ ?_
  have hm := congr_arg (fun w ↦ coeff w (m + k)) hclear
  rw [coeff_zpow_unitT_mul, add_sub_cancel_right, coeff_algebraMap] at hm
  rw [hm]; simp only [Function.comp_apply, Equiv.coe_addRight, mul_assoc, ← zpow_add₀ ht0,
    add_neg_cancel_right]

/-- When `α < ‖t‖`, `eval hα ht` is not Lipschitz on `AnnularLaurent p hα`. -/
theorem not_lipschitzWith_eval_of_lt (hα : α ∈ Set.Ioo 0 1)
    (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) (hαt : α < ‖t‖) (c : ℝ≥0) :
    ¬ LipschitzWith c (eval hα ht) := fun hL ↦ by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (c : ℝ) ((one_lt_div hα.1).2 hαt)
  have hdist := hL.dist_le_mul (algebraMap (AnnularRing p) (AnnularLaurent p hα) T ^ n) 0
  have hnorm_Tn : ‖algebraMap (AnnularRing p) (AnnularLaurent p hα) T ^ n‖ = α ^ n := by
    simpa using (pseudoUniformizer p hα).norm_pow n
  simp [hnorm_Tn] at hdist
  linarith [(div_pow ‖t‖ α n).trans_le ((div_le_iff₀ (pow_pos hα.1 n)).2 hdist)]

/-- The Tate gauge bound `‖z‖ ≤ α ^ r` implies `‖eval hα ht z‖ ≤ ‖t‖ ^ r`. -/
theorem norm_eval_le_zpow_of_norm_le_zpow (hα : α ∈ Set.Ioo 0 1)
    (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) {z : AnnularLaurent p hα} {r : ℤ}
    (hz : ‖z‖ ≤ α ^ r) : ‖eval hα ht z‖ ≤ ‖t‖ ^ r := by
  obtain ⟨x, hx⟩ := (mem_ringOfDefinition_iff _).1 ((norm_le_zpow_iff hα z r).1 hz)
  have hz_eq : z = (unitT p hα ^ r).val * algebraMap (AnnularRing p) _ x := by
    simp [hx, ← mul_assoc, ← Units.val_mul]
  rw [hz_eq, map_mul, eval_zpow_unitT, eval_algebraMap, norm_mul, norm_zpow]
  exact mul_le_of_le_one_right (zpow_nonneg (norm_nonneg t) r) (norm_eval_le_one ht.1 ht.2 x)

/-- Every annulus evaluation into a complete normed field extension of `ℚ_p` is continuous. -/
theorem continuous_eval (hα : α ∈ Set.Ioo 0 1) (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1) :
    Continuous (eval hα ht) := by
  refine continuous_of_continuousAt_zero (eval hα ht).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero, Metric.tendsto_nhds]; intro ε hε
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hε ht.2
  refine Metric.eventually_nhds_iff.2 ⟨α ^ (r : ℤ), zpow_pos hα.1 _, fun z hz ↦ ?_⟩
  rw [dist_zero_right] at hz ⊢
  exact (norm_eval_le_zpow_of_norm_le_zpow hα ht hz.le).trans_lt (by simpa [zpow_natCast] using hr)

/-- Any bounded ring homomorphism `AnnularRing p →+* K` agreeing with `AnnularRing.eval t ht.1 ht.2`
on `ℤ_p`, `T`, and `U` equals `AnnularRing.eval t ht.1 ht.2`, by truncating normal forms. -/
private theorem ringHom_eq_eval_of_bounded (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1)
    (g : AnnularRing p →+* K) {C : ℝ} (hC : ∀ y : AnnularRing p, ‖g y‖ ≤ C)
    (hg_alg : ∀ c : ℤ_[p], g (algebraMap ℤ_[p] (AnnularRing p) c) = padicIntAlgebraMap p K c)
    (hgT : g T = t) (hgU : g U = (p : K) / t) : g = AnnularRing.eval t ht.1 ht.2 := by
  ext x; obtain ⟨⟨f₀, g₀⟩, hx⟩ := normalForm.surjective x; rw [normalForm_apply] at hx
  have hsplit (φ : PowerSeries ℤ_[p] →ₐ[ℤ_[p]] AnnularRing p) (s : PowerSeries ℤ_[p]) (N : ℕ) :
      φ s = (∑ i ∈ Finset.range N, algebraMap ℤ_[p] _ (PowerSeries.coeff i s) * φ .X ^ i) +
        φ .X ^ N * φ (PowerSeries.mk fun i ↦ PowerSeries.coeff (i + N) s) := by
    conv_lhs => rw [PowerSeries.eq_X_pow_mul_shift_add_trunc N s, ← Polynomial.eval₂_C_X_eq_coe]
    rw [map_add, map_mul, map_pow, ← AlgHom.coe_toRingHom, Polynomial.hom_eval₂,
      PowerSeries.eval₂_trunc_eq_sum_range, add_comm]
    exact congrArg (· + _) <| Finset.sum_congr rfl fun i _ ↦ by
      rw [RingHom.comp_apply, AlgHom.coe_toRingHom, PowerSeries.C_eq_algebraMap, AlgHom.commutes]
  let sT (N : ℕ) : K :=
    ∑ i ∈ Finset.range N, padicIntAlgebraMap p K (PowerSeries.coeff i f₀) * t ^ i
  let sU (N : ℕ) : K :=
    ∑ i ∈ Finset.range N, padicIntAlgebraMap p K (PowerSeries.coeff i g₀) * ((p : K) / t) ^ i
  have hnorm_p_div_t : ‖(p : K) / t‖ = ((p : ℝ) * ‖t‖)⁻¹ := by
    rw [norm_div, TauCeti.norm_natCast_p, div_eq_mul_inv, mul_inv_rev, mul_comm]
  have hdiff (N : ℕ) :
      ‖g x - (sT N + ((p : K) / t) * sU N)‖ ≤ ‖t‖ ^ N * C + ‖(p : K) / t‖ ^ (N + 1) * C := by
    have hgx : g x - (sT N + ((p : K) / t) * sU N) =
        t ^ N * g (ofPowerSeriesT (PowerSeries.mk fun i ↦ PowerSeries.coeff (i + N) f₀)) +
        ((p : K) / t) ^ (N + 1) *
          g (ofPowerSeriesU (PowerSeries.mk fun i ↦ PowerSeries.coeff (i + N) g₀)) := by
      conv_lhs => rw [← hx, hsplit ofPowerSeriesT f₀ N, hsplit ofPowerSeriesU g₀ N]
      simp only [ofPowerSeriesT_X, ofPowerSeriesU_X, map_add, map_sum, map_mul, map_pow,
        hg_alg, hgT, hgU, sT, sU]; ring
    rw [hgx]; refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;>
      · rw [norm_mul, norm_pow]; exact mul_le_mul_of_nonneg_left (hC _) (by positivity)
  have htend_bound :
      Tendsto (fun N : ℕ ↦ ‖t‖ ^ N * C + ‖(p : K) / t‖ ^ (N + 1) * C) atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_mul, add_zero] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg t) ht.2).mul_const C).add
      (((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _)
        (hnorm_p_div_t ▸ inv_p_mul_norm_lt_one ht)).comp (tendsto_add_atTop_nat 1)).mul_const C)
  have htend_g : Tendsto (fun N ↦ sT N + ((p : K) / t) * sU N) atTop (𝓝 (g x)) :=
    tendsto_iff_norm_sub_tendsto_zero.2 <| squeeze_zero (fun _ ↦ norm_nonneg _)
      (fun N ↦ (norm_sub_rev _ _).trans_le (hdiff N)) htend_bound
  have htend_eval :
      Tendsto (fun N ↦ sT N + ((p : K) / t) * sU N) atTop (𝓝 (AnnularRing.eval t ht.1 ht.2 x)) := by
    rw [← hx, map_add, map_mul, eval_U]
    exact (hasSum_eval_ofPowerSeriesT ht f₀).tendsto_sum_nat.add
      (tendsto_const_nhds.mul (hasSum_eval_ofPowerSeriesU ht g₀).tendsto_sum_nat)
  exact tendsto_nhds_unique htend_g htend_eval

/-- Any continuous ring homomorphism `AnnularLaurent p hα →+* K` agreeing with
`padicIntAlgebraMap p K` on `ℤ_p` and sending `unitT p hα` to `t` equals `eval hα ht`. -/
theorem eq_eval_of_continuous {hα : α ∈ Set.Ioo 0 1} (ht : ‖t‖ ∈ Set.Ioo (p : ℝ)⁻¹ 1)
    (f : AnnularLaurent p hα →+* K) (hf : Continuous f)
    (hc : ∀ c, f (algebraMap ℤ_[p] _ c) = padicIntAlgebraMap p K c)
    (hT : f (unitT p hα) = t) : f = eval hα ht := by
  have ht0 : t ≠ 0 := ne_zero_of_norm_mem_Ioo ht
  let g : AnnularRing p →+* K := f.comp (algebraMap (AnnularRing p) (AnnularLaurent p hα))
  have hg_alg (c : ℤ_[p]) : g (algebraMap ℤ_[p] (AnnularRing p) c) = padicIntAlgebraMap p K c := by
    rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]; exact hc c
  have hgT : g T = t := by rw [RingHom.comp_apply, ← val_unitT hα]; exact hT
  have hgU : g U = (p : K) / t := by
    rw [eq_div_iff ht0, mul_comm, ← hgT, ← map_mul, T_mul_U, map_natCast]
  -- Continuity at `0` bounds `g` on `AnnularRing p`, since `T ^ r * y` shrinks into the ball.
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.1 (hf.continuousAt (x := 0)) 1 zero_lt_one
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hδ hα.2
  have hg_bound (y : AnnularRing p) : ‖g y‖ ≤ (‖t‖ ^ r)⁻¹ := by
    have hnorm_Ty : ‖algebraMap (AnnularRing p) (AnnularLaurent p hα) (T ^ r * y)‖ < δ := by
      rw [map_mul, map_pow]; refine (norm_mul_le _ _).trans_lt <| (mul_le_mul (norm_pow_le _ r)
        (norm_algebraMap_le_one hα y) (norm_nonneg _) (by positivity)).trans_lt ?_
      simpa [norm_algebraMap_T] using hr
    have h1 : ‖g (T ^ r * y)‖ < 1 := by
      rw [RingHom.comp_apply, ← dist_zero_right, ← f.map_zero]
      exact hball (by rwa [dist_zero_right])
    rw [map_mul, map_pow, norm_mul, norm_pow, hgT] at h1
    rw [← one_div, le_div_iff₀' (pow_pos (norm_pos_iff.2 ht0) r)]; exact h1.le
  exact IsLocalization.ringHom_ext (Submonoid.powers (T : AnnularRing p)) <| RingHom.ext fun x ↦
    (RingHom.congr_fun (ringHom_eq_eval_of_bounded ht g hg_bound hg_alg hgT hgU) x).trans
      (eval_algebraMap hα ht x).symm
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
  obtain ⟨t, ht, hnorm⟩ := PadicComplex.exists_norm_mem_Ioo_eq_rpow_neg (p := p) (q := (1 : ℚ) / N)
    (by positivity) ((div_lt_one (by positivity)).2 (by exact_mod_cast (by omega : 1 < N)))
  have hβ_lt_t : β < ‖t‖ := by
    have hrpow : (p : ℝ) ^ ((1 : ℝ) / N) < β⁻¹ := by
      calc (p : ℝ) ^ ((1 : ℝ) / N)
          < ((β⁻¹) ^ N : ℝ) ^ ((1 : ℝ) / N) := Real.rpow_lt_rpow (p_pos (p := p)).le
            (hm.trans_le (pow_le_pow_right₀ hβ_inv.le (Nat.le_add_right m 2))) (by positivity)
        _ = β⁻¹ := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (inv_nonneg.2 hβ_pos.le),
              mul_one_div_cancel hN_pos.ne', Real.rpow_one]
    calc β = (β⁻¹)⁻¹ := (inv_inv β).symm
      _ < ((p : ℝ) ^ ((1 : ℝ) / N))⁻¹ :=
          inv_strictAnti₀ (Real.rpow_pos_of_pos (p_pos (p := p)) _) hrpow
      _ = ‖t‖ := by rw [hnorm, Real.rpow_neg (p_pos (p := p)).le]; simp
  exact ⟨t, ht, continuous_eval hα ht,
    not_lipschitzWith_eval_of_lt hα ht ((le_max_right _ _).trans_lt hβ_lt_t)⟩

end AnnularLaurent
end TauCeti
