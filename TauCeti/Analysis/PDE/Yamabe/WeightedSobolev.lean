/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import TauCeti.Analysis.PDE.Yamabe.Bubble.Basic
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import TauCeti.Analysis.SpecialFunctions.Beta.Basic
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Comp
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# One-dimensional mass transport and the sharp radial Sobolev inequality

For `n > 2`, let `wₙ(s) = s ^ (n - 1) (2 / (1 + s²)) ^ n` (`TauCeti.Yamabe.bubbleRadialWeight n s`),
`aₙ = 4 (n - 1) / (n - 2)` (`TauCeti.Yamabe.conformalCoefficient`), and `pₙ = 2 n / (n - 2)`
(`TauCeti.Yamabe.criticalExponent`). Following Cordero-Erausquin–Nazaret–Villani, this file uses the
monotone mass-transport map matching `r ^ (n - 1) f(r) ^ pₙ dr` with `wₙ(s) ds` to prove
`n (n - 1) ∫_{s > 0} wₙ(s) ds ≤ aₙ ∫_{r > 0} r ^ (n - 1) f'(r)² dr` for every normalized,
compactly supported, nonnegative Lipschitz profile `f : ℝ → ℝ` that is antitone on `[0, ∞)`
(`TauCeti.Yamabe.mul_integral_bubbleRadialWeight_le_conformalCoefficient_mul_integral`).

## References

* D. Cordero-Erausquin, B. Nazaret, C. Villani, *A mass-transportation approach to sharp Sobolev and
  Gagliardo–Nirenberg inequalities*, Adv. Math. 182 (2004), 307–332.
* G. Talenti, *Best constant in Sobolev inequality*, Ann. Mat. Pura Appl. 110 (1976), 353–372.
-/

public section

noncomputable section

open Filter Function MeasureTheory Metric Set
open scoped NNReal Topology

namespace TauCeti.Yamabe

/-- Radial critical-mass density `s ^ (n - 1) * (2 / (1 + s²)) ^ n` of the unit bubble `U_{1,0}`. -/
def bubbleRadialWeight (n : ℕ) (s : ℝ) : ℝ := s ^ (n - 1) * (2 / (1 + s ^ 2)) ^ n

/-- Unfolding lemma for `TauCeti.Yamabe.bubbleRadialWeight`. -/
theorem bubbleRadialWeight_def (n : ℕ) (s : ℝ) :
    bubbleRadialWeight n s = s ^ (n - 1) * (2 / (1 + s ^ 2)) ^ n := (rfl)

private theorem continuous_bubbleRadialWeight (n : ℕ) : Continuous (bubbleRadialWeight n) :=
  (continuous_pow (n - 1)).mul ((continuous_const.div
    (continuous_const.add (continuous_pow 2)) fun _ ↦ by dsimp; positivity).pow n)

private theorem bubbleRadialWeight_pos {n : ℕ} {s : ℝ} (hs : 0 < s) :
    0 < bubbleRadialWeight n s := by
  rw [bubbleRadialWeight_def]; positivity

private theorem integrableOn_pow_mul_div_one_add_sq_pow {n k : ℕ} (hn : 0 < n)
    (hk : k ≤ 2 * (n - 1)) :
    IntegrableOn (fun s : ℝ ↦ s ^ k * (2 / (1 + s ^ 2)) ^ n) (Ioi 0) := by
  have hdom : IntegrableOn (fun s : ℝ ↦ (2 : ℝ) ^ n * (1 + s ^ 2) ^ (-1 : ℝ)) (Ioi 0) :=
    ((integrable_one_add_sq_rpow (by norm_num : (1 / 2 : ℝ) < 1)).const_mul _).integrableOn
  have hcont : Continuous fun s : ℝ ↦ s ^ k * (2 / (1 + s ^ 2)) ^ n :=
    (continuous_pow k).mul ((continuous_const.div
      (continuous_const.add (continuous_pow 2)) fun _ ↦ by dsimp; positivity).pow n)
  refine hdom.mono' hcont.aestronglyMeasurable.restrict
    (ae_restrict_of_forall_mem measurableSet_Ioi fun s (hs : 0 < s) ↦ ?_)
  have h1s : 0 < 1 + s ^ 2 := by positivity
  have hpow : s ^ k ≤ (1 + s ^ 2) ^ (n - 1) := by
    rcases le_or_gt s 1 with hs1 | hs1
    · exact (pow_le_one₀ hs.le hs1).trans (one_le_pow₀ (by linarith [sq_nonneg s]))
    · exact (pow_le_pow_right₀ hs1.le hk).trans
        (pow_mul s 2 (n - 1) ▸ pow_le_pow_left₀ (sq_nonneg s) (by linarith) _)
  rw [Real.norm_of_nonneg (by positivity), div_pow, Real.rpow_neg_one]
  refine (mul_le_mul_of_nonneg_right hpow (by positivity)).trans_eq ?_
  rw [show (1 + s ^ 2) ^ n = (1 + s ^ 2) ^ (n - 1) * (1 + s ^ 2) by
    rw [← pow_succ, Nat.sub_add_cancel hn]]; field_simp [h1s.ne']

private theorem integrableOn_bubbleRadialWeight {n : ℕ} (hn : 0 < n) :
    IntegrableOn (bubbleRadialWeight n) (Ioi 0) :=
  integrableOn_pow_mul_div_one_add_sq_pow hn (by omega)

private theorem integrableOn_sq_mul_bubbleRadialWeight {n : ℕ} (hn : 2 < n) :
    IntegrableOn (fun s ↦ s ^ 2 * bubbleRadialWeight n s) (Ioi 0) :=
  (integrableOn_pow_mul_div_one_add_sq_pow (n := n) (k := n + 1) (by omega) (by omega)).congr_fun
    (fun s _ ↦ by
      simp only [bubbleRadialWeight_def, show n + 1 = (n - 1) + 2 by omega, pow_add]; ring)
    measurableSet_Ioi

private theorem integral_bubbleRadialWeight_pos {n : ℕ} (hn : 0 < n) :
    0 < ∫ s in Ioi (0 : ℝ), bubbleRadialWeight n s := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (ae_restrict_of_forall_mem measurableSet_Ioi fun _ hs ↦ (bubbleRadialWeight_pos hs).le)
    (integrableOn_bubbleRadialWeight hn)]
  exact (isOpen_Ioi.measure_pos volume ⟨1, one_pos⟩).trans_le
    (measure_mono fun _ hs ↦ ⟨(bubbleRadialWeight_pos hs).ne', hs⟩)

private theorem sub_two_mul_integral_sq_mul_bubbleRadialWeight {n : ℕ} (hn : 2 < n) :
    ((n : ℝ) - 2) * ∫ s in Ioi (0 : ℝ), s ^ 2 * bubbleRadialWeight n s =
      (n : ℝ) * ∫ s in Ioi (0 : ℝ), bubbleRadialWeight n s := by
  have h₁ : IntegrableOn (fun s : ℝ ↦ s ^ (n - 1) * (2 * 1 / (1 ^ 2 + s ^ 2)) ^ n) (Ioi 0) :=
    (integrableOn_bubbleRadialWeight (n := n) (by omega)).congr_fun
      (fun s _ ↦ by simp [bubbleRadialWeight_def]) measurableSet_Ioi
  have h₂ : IntegrableOn (fun s : ℝ ↦ s ^ (n - 1) * (s ^ 2 * (2 * 1 / (1 ^ 2 + s ^ 2)) ^ n))
      (Ioi 0) :=
    (integrableOn_sq_mul_bubbleRadialWeight hn).congr_fun
      (fun s _ ↦ by simp only [bubbleRadialWeight_def, mul_one, one_pow]; ring) measurableSet_Ioi
  simpa only [bubbleRadialWeight_def, mul_one, one_pow, mul_left_comm _ (_ ^ 2)] using
    sub_two_mul_integral_radial hn h₁ h₂

private theorem exists_inverse_bubbleRadialWeight {n : ℕ} (hn : 0 < n) :
    ∃ Ginv : ℝ → ℝ,
      let I₀ := ∫ s in Ioi (0 : ℝ), bubbleRadialWeight n s;
      (∀ y ∈ Ioo 0 I₀, 0 < Ginv y ∧ (∫ σ in (0 : ℝ)..Ginv y, bubbleRadialWeight n σ) = y) ∧
      (∀ y ∈ Ioo 0 I₀, HasDerivAt Ginv (bubbleRadialWeight n (Ginv y))⁻¹ y) ∧
      (∀ y ∈ Ioo 0 I₀, Ginv y ^ n * (I₀ - y) ≤ 2 ^ n) ∧
      Tendsto Ginv (𝓝[>] 0) (𝓝 0) ∧
      Tendsto Ginv (𝓝[<] I₀) atTop := by
  set I₀ := ∫ s in Ioi (0 : ℝ), bubbleRadialWeight n s
  have hw := integrableOn_bubbleRadialWeight (n := n) hn
  have hI₀ : 0 < I₀ := integral_bubbleRadialWeight_pos hn
  let G : ℝ → ℝ := fun s ↦ ∫ σ in (0 : ℝ)..s, bubbleRadialWeight n σ
  have hG_deriv (s : ℝ) : HasDerivAt G (bubbleRadialWeight n s) s :=
    ((continuous_bubbleRadialWeight n).integral_hasStrictDerivAt 0 s).hasDerivAt
  have hG_cont : Continuous G := continuous_iff_continuousAt.2 fun s ↦ (hG_deriv s).continuousAt
  have hG_mono : StrictMonoOn G (Ici 0) :=
    strictMonoOn_of_deriv_pos (convex_Ici 0) hG_cont.continuousOn fun s hs ↦ by
      rw [interior_Ici] at hs; rw [(hG_deriv s).deriv]; exact bubbleRadialWeight_pos hs
  have hG0 : G 0 = 0 := intervalIntegral.integral_same
  have hG_top : Tendsto G atTop (𝓝 I₀) := intervalIntegral_tendsto_integral_Ioi 0 hw tendsto_id
  have hex (y : ℝ) (hy : y ∈ Ioo 0 I₀) : ∃ s > 0, G s = y := by
    obtain ⟨M, hM⟩ := (hG_top.eventually (lt_mem_nhds hy.2)).exists_forall_of_atTop
    obtain ⟨s, hs, hGs⟩ := intermediate_value_Icc (by positivity : 0 ≤ max M 1)
      hG_cont.continuousOn ⟨hG0.symm ▸ hy.1.le, (hM (max M 1) (le_max_left M 1)).le⟩
    exact ⟨s, lt_of_le_of_ne hs.1 fun h0 ↦ hy.1.ne (hG0.symm.trans (h0 ▸ hGs)), hGs⟩
  let Ginv : ℝ → ℝ := fun y ↦ if h : y ∈ Ioo 0 I₀ then Classical.choose (hex y h) else 0
  have hGinv (y : ℝ) (hy : y ∈ Ioo 0 I₀) : 0 < Ginv y ∧ G (Ginv y) = y := by
    simpa only [Ginv, hy, ↓reduceDIte] using Classical.choose_spec (hex y hy)
  refine ⟨Ginv, hGinv, fun y hy ↦ ?_, fun y hy ↦ ?_,
    Metric.tendsto_nhds.2 fun ε hε ↦ ?_, Filter.tendsto_atTop.2 fun M ↦ ?_⟩
  · obtain ⟨hs₀, hGs₀⟩ := hGinv y hy
    have hcont : ContinuousAt Ginv y := Metric.tendsto_nhds.2 fun ε hε ↦ by
      set δ := min (Ginv y / 2) (ε / 2)
      have hδ : 0 < δ := lt_min (half_pos hs₀) (half_pos hε)
      have hsub0 : 0 ≤ Ginv y - δ := sub_nonneg.2 ((min_le_left _ _).trans (by linarith))
      have hlo : G (Ginv y - δ) < y :=
        (hG_mono (mem_Ici.2 hsub0) (mem_Ici.2 hs₀.le) (by linarith)).trans_eq hGs₀
      have hhi : y < G (Ginv y + δ) :=
        hGs₀.symm.trans_lt (hG_mono (mem_Ici.2 hs₀.le) (mem_Ici.2 (by linarith)) (by linarith))
      filter_upwards [Ioo_mem_nhds (max_lt hy.1 hlo) (lt_min hy.2 hhi)] with z hz
      obtain ⟨hsz, hGsz⟩ := hGinv z
        ⟨(le_max_left _ _).trans_lt hz.1, hz.2.trans_le (min_le_left _ _)⟩
      have h1 : Ginv y - δ < Ginv z := not_le.1 fun hle ↦ ((le_max_right _ _).trans_lt hz.1).not_ge
        (hGsz ▸ hG_mono.monotoneOn (mem_Ici.2 hsz.le) (mem_Ici.2 hsub0) hle)
      have h2 : Ginv z < Ginv y + δ := not_le.1 fun hle ↦ (hz.2.trans_le (min_le_right _ _)).not_ge
        (hGsz ▸ hG_mono.monotoneOn (mem_Ici.2 (by linarith)) (mem_Ici.2 hsz.le) hle)
      have hδe : δ ≤ ε / 2 := min_le_right _ _
      rw [Real.dist_eq, abs_lt]; exact ⟨by linarith, by linarith⟩
    exact HasDerivAt.of_local_left_inverse hcont (hG_deriv (Ginv y))
      (bubbleRadialWeight_pos hs₀).ne'
      (eventually_of_mem (Ioo_mem_nhds hy.1 hy.2) fun z hz ↦ (hGinv z hz).2)
  · obtain ⟨hs, hGs⟩ := hGinv y hy
    set s := Ginv y
    have hsplit : I₀ - y = ∫ σ in Ioi s, bubbleRadialWeight n σ := by
      have hunion : Ioc 0 s ∪ Ioi s = Ioi (0 : ℝ) := Ioc_union_Ioi_eq_Ioi hs.le
      rw [← hGs, show G s = ∫ σ in (0 : ℝ)..s, bubbleRadialWeight n σ from rfl,
        intervalIntegral.integral_of_le hs.le,
        show I₀ = ∫ σ in Ioi (0 : ℝ), bubbleRadialWeight n σ from rfl, ← hunion,
        setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
          (hw.mono_set (hunion ▸ subset_union_left)) (hw.mono_set (hunion ▸ subset_union_right))]
      ring
    let g : ℝ → ℝ := fun σ ↦ -(2 ^ n / (n : ℝ)) * (σ ^ n)⁻¹
    let g' : ℝ → ℝ := fun σ ↦ σ ^ (n - 1) * (2 / σ ^ 2) ^ n
    have hg_d : ∀ σ ∈ Ici s, HasDerivAt g (g' σ) σ := fun σ hσ ↦ by
      have hσ0 : 0 < σ := hs.trans_le hσ
      refine (((hasDerivAt_pow n σ).inv (pow_ne_zero n hσ0.ne')).const_mul
        (-(2 ^ n / (n : ℝ)))).congr_deriv ?_
      have hsq : (σ ^ n) ^ 2 = (σ ^ 2) ^ n := by rw [← pow_mul, mul_comm, pow_mul]
      simp only [g', div_pow]; rw [hsq]; field_simp [hσ0.ne']
    have hg'_nn : ∀ σ ∈ Ioi s, 0 ≤ g' σ := fun σ hσ ↦ by have := hs.trans hσ; positivity
    have hg_top : Tendsto g atTop (𝓝 0) := by
      simpa [g] using ((tendsto_pow_atTop hn.ne').inv_tendsto_atTop).const_mul (-(2 ^ n / (n : ℝ)))
    have hle : ∫ σ in Ioi s, bubbleRadialWeight n σ ≤ 2 ^ n / (n : ℝ) * (s ^ n)⁻¹ := by
      rw [show 2 ^ n / (n : ℝ) * (s ^ n)⁻¹ = ∫ σ in Ioi s, g' σ by
        rw [integral_Ioi_of_hasDerivAt_of_nonneg' hg_d hg'_nn hg_top]; simp [g]]
      exact setIntegral_mono_on (hw.mono_set (Ioi_subset_Ioi hs.le))
        (integrableOn_Ioi_deriv_of_nonneg' hg_d hg'_nn hg_top) measurableSet_Ioi fun σ hσ ↦
        have hσ0 : 0 < σ := hs.trans hσ
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
          (div_le_div_of_nonneg_left zero_le_two (sq_pos_of_pos hσ0) (by linarith)) n)
          (pow_nonneg hσ0.le _)
    rw [hsplit]
    calc s ^ n * ∫ σ in Ioi s, bubbleRadialWeight n σ
        ≤ s ^ n * (2 ^ n / (n : ℝ) * (s ^ n)⁻¹) := mul_le_mul_of_nonneg_left hle (by positivity)
      _ = 2 ^ n / (n : ℝ) := by field_simp [hs.ne']
      _ ≤ 2 ^ n := div_le_self (by positivity) (by exact_mod_cast hn)
  · have hGε : 0 < G ε := hG0 ▸ hG_mono (mem_Ici.2 le_rfl) hε.le hε
    filter_upwards [Ioo_mem_nhdsGT (lt_min hGε hI₀)] with y hy
    obtain ⟨hs, hGs⟩ := hGinv y ⟨hy.1, hy.2.trans_le (min_le_right _ _)⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos hs]
    exact not_le.1 fun hle ↦
      (hy.2.trans_le (min_le_left _ _)).not_ge (hGs ▸ hG_mono.monotoneOn hε.le hs.le hle)
  · set M' := max M 0
    have hM'0 : 0 ≤ M' := le_max_right M 0
    have hM'lt : G M' < I₀ :=
      (hG_mono (mem_Ici.2 hM'0) (mem_Ici.2 (by linarith)) (lt_add_one M')).trans_le <|
        ge_of_tendsto hG_top <| eventually_of_mem (Ici_mem_atTop (M' + 1)) fun s (hs : M' + 1 ≤ s) ↦
          hG_mono.monotoneOn (mem_Ici.2 (by linarith)) (mem_Ici.2 (by linarith)) hs
    filter_upwards [Ioo_mem_nhdsLT (max_lt hI₀ hM'lt)] with y hy
    obtain ⟨hs, hGs⟩ := hGinv y ⟨(le_max_left 0 (G M')).trans_lt hy.1, hy.2⟩
    exact (le_max_left M 0).trans <| not_lt.1 fun hlt ↦
      ((le_max_right 0 (G M')).trans_lt hy.1).not_ge (hGs ▸ hG_mono.monotoneOn hs.le hM'0 hlt.le)

private theorem mul_one_add_sq_le_rpow_mul_deriv {n : ℕ} (hn : 2 < n) {r s s' y : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hy : 0 < y)
    (hode : s' * bubbleRadialWeight n s = r ^ (n - 1) * y ^ criticalExponent n) :
    (n : ℝ) / 2 * (r ^ (n - 1) * y ^ criticalExponent n * (1 + s ^ 2)) ≤
      y ^ (2 * ((n : ℝ) - 1) / ((n : ℝ) - 2)) *
        (((n - 1 : ℕ) : ℝ) * r ^ (n - 2) * s + r ^ (n - 1) * s') := by
  set q := 2 * ((n : ℝ) - 1) / ((n : ℝ) - 2)
  have hn0 : (0 : ℝ) < n := by positivity
  have hn1 : 0 ≤ (n : ℝ) - 1 := sub_nonneg.2 (by exact_mod_cast (show 1 ≤ n by omega))
  have hs'_pos : 0 < s' := not_le.1 fun hle ↦ by
    linarith [mul_nonpos_of_nonpos_of_nonneg hle (bubbleRadialWeight_pos (n := n) hs).le,
      show 0 < r ^ (n - 1) * y ^ criticalExponent n by positivity]
  have hprod : s' * (s / r) ^ (n - 1) = (y ^ (2 / ((n : ℝ) - 2)) * ((1 + s ^ 2) / 2)) ^ n := by
    have hpow : (y ^ (2 / ((n : ℝ) - 2))) ^ n = y ^ criticalExponent n := by
      rw [← Real.rpow_natCast _ n, ← Real.rpow_mul hy.le, criticalExponent_def]; congr 1; field_simp
    rw [mul_pow, hpow, div_pow, div_pow]; rw [bubbleRadialWeight_def, div_pow] at hode
    field_simp [hr.ne'] at hode ⊢; linarith
  have hgeom : y ^ (2 / ((n : ℝ) - 2)) * ((1 + s ^ 2) / 2) =
      s' ^ (1 / (n : ℝ)) * ((s / r) ^ (((n : ℝ) - 1) / n)) := by
    have hbase : 0 ≤ y ^ (2 / ((n : ℝ) - 2)) * ((1 + s ^ 2) / 2) := by positivity
    rw [show y ^ (2 / ((n : ℝ) - 2)) * ((1 + s ^ 2) / 2) =
        ((y ^ (2 / ((n : ℝ) - 2)) * ((1 + s ^ 2) / 2)) ^ n) ^ (1 / (n : ℝ)) by
      rw [← Real.rpow_natCast _ n, ← Real.rpow_mul hbase, mul_one_div_cancel hn0.ne',
        Real.rpow_one], ← hprod, Real.mul_rpow hs'_pos.le (by positivity),
      ← Real.rpow_natCast _ (n - 1), ← Real.rpow_mul (by positivity), Nat.cast_sub (by omega),
      Nat.cast_one, mul_one_div]
  have hamgm := Real.geom_mean_le_arith_mean2_weighted (w₁ := 1 / (n : ℝ))
    (w₂ := ((n : ℝ) - 1) / n) (p₁ := s') (p₂ := s / r) (by positivity) (div_nonneg hn1 hn0.le)
    hs'_pos.le (by positivity) (by field_simp; ring)
  rw [← hgeom] at hamgm
  have hmul := mul_le_mul_of_nonneg_left hamgm (by positivity : 0 ≤ (n : ℝ) * r ^ (n - 1) * y ^ q)
  have hyq : y ^ q * y ^ (2 / ((n : ℝ) - 2)) = y ^ criticalExponent n := by
    rw [← Real.rpow_add hy, criticalExponent_def]; congr 1; dsimp only [q]; field_simp; ring
  have lhs_eq : (n : ℝ) * r ^ (n - 1) * y ^ q * (y ^ (2 / ((n : ℝ) - 2)) * ((1 + s ^ 2) / 2)) =
      (n : ℝ) / 2 * (r ^ (n - 1) * y ^ criticalExponent n * (1 + s ^ 2)) := by
    rw [show (n : ℝ) * r ^ (n - 1) * y ^ q * (y ^ (2 / ((n : ℝ) - 2)) * ((1 + s ^ 2) / 2)) =
      (n : ℝ) * r ^ (n - 1) * (y ^ q * y ^ (2 / ((n : ℝ) - 2))) * ((1 + s ^ 2) / 2) by ring, hyq]
    ring
  have rhs_eq : (n : ℝ) * r ^ (n - 1) * y ^ q *
      (1 / (n : ℝ) * s' + ((n : ℝ) - 1) / n * (s / r)) =
      y ^ q * (((n - 1 : ℕ) : ℝ) * r ^ (n - 2) * s + r ^ (n - 1) * s') := by
    rw [Nat.cast_sub (by omega), Nat.cast_one,
      show r ^ (n - 1) = r ^ (n - 2) * r by rw [← pow_succ, show n - 2 + 1 = n - 1 by omega]]
    field_simp [hn0.ne', hr.ne']; ring
  rwa [lhs_eq, rhs_eq] at hmul

private theorem subinterval_young_pointwise {n : ℕ} (hn : 2 < n) {r y s d : ℝ}
    (hr : 0 ≤ r) (hy : 0 ≤ y) :
    let q := 2 * ((n : ℝ) - 1) / ((n : ℝ) - 2);
    -(q * y ^ (q - 1) * d * (r ^ (n - 1) * s)) ≤
      ((n : ℝ) - 1) / 2 * (r ^ (n - 1) * y ^ criticalExponent n * s ^ 2) +
        2 * ((n : ℝ) - 1) / ((n : ℝ) - 2) ^ 2 * (r ^ (n - 1) * d ^ 2) := by
  intro q
  have hn1 : 0 < (n : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast (show 1 < n by omega))
  have hn2 : 0 < (n : ℝ) - 2 := sub_pos.mpr (by exact_mod_cast hn)
  set A := y ^ (q - 1) * s; set B := 2 / ((n : ℝ) - 2) * (-d)
  have hmul := mul_le_mul_of_nonneg_left (show 2 * A * B ≤ A ^ 2 + B ^ 2 by
    nlinarith [sq_nonneg (A - B)]) (by positivity : 0 ≤ ((n : ℝ) - 1) / 2 * r ^ (n - 1))
  have hA2 : (y ^ (q - 1)) ^ 2 = y ^ criticalExponent n := by
    rw [← Real.rpow_two, ← Real.rpow_mul hy, show (q - 1) * 2 = criticalExponent n by
      dsimp only [q]; rw [criticalExponent_def]; field_simp [hn2.ne']; ring]
  have h1 : ((n : ℝ) - 1) / 2 * r ^ (n - 1) * (2 * A * B) =
      -(q * y ^ (q - 1) * d * (r ^ (n - 1) * s)) := by dsimp only [A, B, q]; field_simp [hn2.ne']
  have h2 : ((n : ℝ) - 1) / 2 * r ^ (n - 1) * (A ^ 2 + B ^ 2) =
      ((n : ℝ) - 1) / 2 * (r ^ (n - 1) * y ^ criticalExponent n * s ^ 2) +
        2 * ((n : ℝ) - 1) / ((n : ℝ) - 2) ^ 2 * (r ^ (n - 1) * d ^ 2) := by
    dsimp only [A, B]; rw [mul_pow, hA2]; field_simp [hn2.ne']
  rwa [h1, h2] at hmul

private theorem subinterval_transport_estimate {n : ℕ} (hn : 2 < n) {R₀ : ℝ} {K : ℝ≥0}
    {f : ℝ → ℝ} (hf_lip : LipschitzWith K f) (hf_pos : ∀ r ∈ Ioo 0 R₀, 0 < f r)
    (hderiv_int : IntegrableOn (fun r ↦ r ^ (n - 1) * (deriv f r) ^ 2) (Ioi 0))
    {I₀ : ℝ} {Ginv : ℝ → ℝ} (hGinv_pos : ∀ y ∈ Ioo 0 I₀, 0 < Ginv y)
    (hGinv_deriv : ∀ y ∈ Ioo 0 I₀, HasDerivAt Ginv (bubbleRadialWeight n (Ginv y))⁻¹ y)
    {F : ℝ → ℝ} (hF_deriv : ∀ r, HasDerivAt F (r ^ (n - 1) * f r ^ criticalExponent n) r)
    (hF_mem : ∀ r ∈ Ioo 0 R₀, F r ∈ Ioo 0 I₀)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < R₀) :
    (n : ℝ) / 2 * (F b - F a) +
        1 / 2 * (∫ s in (Ginv (F a))..(Ginv (F b)), s ^ 2 * bubbleRadialWeight n s) ≤
      b ^ (n - 1) * f b ^ (2 * ((n : ℝ) - 1) / ((n : ℝ) - 2)) * Ginv (F b) +
        2 * ((n : ℝ) - 1) / ((n : ℝ) - 2) ^ 2 *
          ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * (deriv f r) ^ 2 := by
  set q := 2 * ((n : ℝ) - 1) / ((n : ℝ) - 2); set pₙ := criticalExponent n
  have hn1 : 0 < (n : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast (show 1 < n by omega))
  let T := fun r ↦ Ginv (F r)
  let T' := fun r ↦ r ^ (n - 1) * f r ^ pₙ / bubbleRadialWeight n (T r)
  have hIoo {r : ℝ} (hr : r ∈ Icc a b) : r ∈ Ioo 0 R₀ := ⟨ha.trans_le hr.1, hr.2.trans_lt hb⟩
  have hT_pos {r : ℝ} (hr : r ∈ Icc a b) : 0 < T r := hGinv_pos (F r) (hF_mem r (hIoo hr))
  have hT_deriv : ∀ r ∈ Icc a b, HasDerivAt T (T' r) r := fun r hr ↦ by
    simpa only [T, T', Function.comp_def, div_eq_inv_mul] using
      (hGinv_deriv (F r) (hF_mem r (hIoo hr))).comp r (hF_deriv r)
  have hT_cont : ContinuousOn T (Icc a b) := fun r hr ↦
    (hT_deriv r hr).continuousAt.continuousWithinAt
  have hT'_cont : ContinuousOn T' (Icc a b) :=
    ContinuousOn.div ((continuous_pow (n - 1)).continuousOn.mul
      (hf_lip.continuous.continuousOn.rpow_const fun _ _ ↦ .inr (criticalExponent_pos hn).le))
      ((continuous_bubbleRadialWeight n).comp_continuousOn hT_cont) fun r hr ↦
        (bubbleRadialWeight_pos (hT_pos hr)).ne'
  let g := fun r ↦ r ^ (n - 1) * T r
  let g' := fun r ↦ ((n - 1 : ℕ) : ℝ) * r ^ (n - 2) * T r + r ^ (n - 1) * T' r
  have hg_deriv : ∀ r ∈ Icc a b, HasDerivAt g (g' r) r := fun r hr ↦ by
    simpa only [Pi.mul_def, g, g', show n - 1 - 1 = n - 2 by omega, mul_assoc] using
      (hasDerivAt_pow (n - 1) r).mul (hT_deriv r hr)
  have hg_ae : ∀ᵐ r, r ∈ uIoc a b → HasDerivAt g (g' r) r := .of_forall fun r hr ↦
    hg_deriv r (uIcc_of_le hab ▸ uIoc_subset_uIcc hr)
  have hg_AC : AbsolutelyContinuousOnInterval g a b :=
    (uIcc_of_le hab ▸ ((continuous_pow (n - 1)).continuousOn.mul hT_cont)
      ).absolutelyContinuousOnInterval_of_hasDerivAt_off_countable countable_empty
      (fun r hr ↦ hg_deriv r ⟨(min_eq_left hab ▸ hr.1.1).le, (max_eq_right hab ▸ hr.1.2).le⟩)
      ((((continuousOn_const.mul (continuous_pow (n - 2)).continuousOn).mul hT_cont).add
        ((continuous_pow (n - 1)).continuousOn.mul hT'_cont)).intervalIntegrable_of_Icc hab)
  have hf_AC : AbsolutelyContinuousOnInterval f a b :=
    hf_lip.lipschitzOnWith.absolutelyContinuousOnInterval
  have hfq_AC : AbsolutelyContinuousOnInterval (fun r ↦ f r ^ q) a b :=
    hf_AC.comp_of_contDiffAt (φ := fun y : ℝ ↦ y ^ q) fun _ ⟨r, hr, hfr⟩ ↦ by
      rw [uIcc_of_le hab] at hr
      exact hfr ▸ Real.contDiffAt_rpow_const_of_ne (hf_pos r (hIoo hr)).ne'
  let h' := fun r ↦ q * f r ^ (q - 1) * deriv f r
  have hfq_deriv : ∀ᵐ r, r ∈ uIoc a b → HasDerivAt (fun x ↦ f x ^ q) (h' r) r := by
    filter_upwards [hf_AC.boundedVariationOn.ae_differentiableAt_of_mem_uIcc] with r hrd hr
    have hr' : r ∈ Icc a b := uIcc_of_le hab ▸ uIoc_subset_uIcc hr
    exact ((hrd (uIoc_subset_uIcc hr)).hasDerivAt.rpow_const
      (.inl (hf_pos r (hIoo hr')).ne')).congr_deriv (by dsimp only [h']; ring)
  have hcont1 : IntervalIntegrable (fun r ↦ r ^ (n - 1) * f r ^ pₙ) volume a b :=
    ((continuous_pow (n - 1)).continuousOn.mul
      (hf_lip.continuous.continuousOn.rpow_const fun _ _ ↦ .inr (criticalExponent_pos hn).le)
      ).intervalIntegrable_of_Icc hab
  have hcont2 : IntervalIntegrable (fun r ↦ r ^ (n - 1) * f r ^ pₙ * T r ^ 2) volume a b :=
    hcont1.mul_continuousOn (uIcc_of_le hab ▸ hT_cont.pow 2)
  have hchg : ∫ r in a..b, r ^ (n - 1) * f r ^ pₙ * T r ^ 2 =
      ∫ s in (T a)..(T b), s ^ 2 * bubbleRadialWeight n s := by
    have heq : ∀ r ∈ Icc a b, r ^ (n - 1) * f r ^ pₙ * T r ^ 2 =
        (T r ^ 2 * bubbleRadialWeight n (T r)) * T' r := fun r hr ↦ by
      dsimp only [T']; field_simp [(bubbleRadialWeight_pos (hT_pos hr)).ne']
    rw [intervalIntegral.integral_congr (uIcc_of_le hab ▸ heq)]
    exact intervalIntegral.integral_comp_mul_deriv (uIcc_of_le hab ▸ hT_deriv)
      (uIcc_of_le hab ▸ hT'_cont) ((continuous_pow 2).mul (continuous_bubbleRadialWeight n))
  have h_amgm_int : (n : ℝ) / 2 * ((F b - F a) +
      ∫ s in (T a)..(T b), s ^ 2 * bubbleRadialWeight n s) ≤ ∫ r in a..b, f r ^ q * g' r := by
    have hcont12 : IntervalIntegrable (fun r ↦ r ^ (n - 1) * f r ^ pₙ * (1 + T r ^ 2))
        volume a b := (hcont1.add hcont2).congr fun r _ ↦ by ring
    rw [show (F b - F a) + ∫ s in (T a)..(T b), s ^ 2 * bubbleRadialWeight n s =
          ∫ r in a..b, r ^ (n - 1) * f r ^ pₙ * (1 + T r ^ 2) by
        rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ ↦ hF_deriv r) hcont1, ← hchg,
          ← intervalIntegral.integral_add hcont1 hcont2]
        exact intervalIntegral.integral_congr fun r _ ↦ by ring,
      ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hab (hcont12.const_mul _)
      ((hg_AC.intervalIntegrable_of_ae_hasDerivAt hg_ae).continuousOn_mul hfq_AC.continuousOn)
      fun r hr ↦ mul_one_add_sq_le_rpow_mul_deriv hn (hIoo hr).1 (hT_pos hr) (hf_pos r (hIoo hr))
        (div_mul_cancel₀ _ (bubbleRadialWeight_pos (hT_pos hr)).ne')
  have hibp := hfq_AC.integral_mul_deriv_eq_deriv_mul_of_ae_hasDerivAt hg_AC hfq_deriv hg_ae
  have hderiv_ab : IntervalIntegrable (fun r ↦ r ^ (n - 1) * (deriv f r) ^ 2) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
      (hderiv_int.mono_set fun r (hr : r ∈ Ioc a b) ↦ mem_Ioi.2 (ha.trans hr.1))
  have hyoung_int : -∫ r in a..b, h' r * g r ≤
      ((n : ℝ) - 1) / 2 * (∫ s in (T a)..(T b), s ^ 2 * bubbleRadialWeight n s) +
        2 * ((n : ℝ) - 1) / ((n : ℝ) - 2) ^ 2 *
          ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * (deriv f r) ^ 2 := by
    rw [← intervalIntegral.integral_neg]
    have hle := intervalIntegral.integral_mono_on hab
      (((hfq_AC.intervalIntegrable_of_ae_hasDerivAt hfq_deriv).mul_continuousOn
        hg_AC.continuousOn).neg) ((hcont2.const_mul _).add (hderiv_ab.const_mul _)) fun r hr ↦
        subinterval_young_pointwise hn (ha.le.trans hr.1) (hf_pos r (hIoo hr)).le
    rw [intervalIntegral.integral_add (hcont2.const_mul _) (hderiv_ab.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hchg] at hle
    refine hle.trans (add_le_add_right (mul_le_mul_of_nonneg_left ?_ (by positivity)) _)
    rw [intervalIntegral.integral_of_le hab]
    exact setIntegral_mono_set hderiv_int
      (ae_restrict_of_forall_mem measurableSet_Ioi fun r (hr : r ∈ Ioi (0 : ℝ)) ↦
        mul_nonneg (pow_nonneg (mem_Ioi.1 hr).le _) (sq_nonneg _))
      (Eventually.of_forall fun r (hr : r ∈ Ioc a b) ↦ mem_Ioi.2 (ha.trans hr.1))
  have ha_nonneg : 0 ≤ f a ^ q * g a := by
    have : 0 < f a := hf_pos a ⟨ha, hab.trans_lt hb⟩
    have : 0 < T a := hT_pos (left_mem_Icc.2 hab)
    positivity
  have hgb : f b ^ q * g b = b ^ (n - 1) * f b ^ q * T b := by simp [g]; ring
  dsimp only [T] at h_amgm_int hyoung_int hgb
  linarith

private theorem exists_boundary_term_lt {n : ℕ} (hn : 2 < n) {K : ℝ≥0} {f : ℝ → ℝ}
    (hf_lip : LipschitzWith K f) {R₀ : ℝ} (hR₀ : 0 < R₀) (hfR₀ : f R₀ = 0)
    (hf_pos : ∀ r ∈ Ioo 0 R₀, 0 < f r) {I₀ : ℝ} {Ginv : ℝ → ℝ}
    (hGinv_pos : ∀ y ∈ Ioo 0 I₀, 0 < Ginv y)
    (htail : ∀ y ∈ Ioo 0 I₀, Ginv y ^ n * (I₀ - y) ≤ 2 ^ n)
    {F : ℝ → ℝ} (hF_deriv : ∀ r, HasDerivAt F (r ^ (n - 1) * f r ^ criticalExponent n) r)
    (hF_mem : ∀ r ∈ Ioo 0 R₀, F r ∈ Ioo 0 I₀) (hFR₀ : F R₀ = I₀)
    {ε r₁ : ℝ} (hε : 0 < ε) (hr₁ : r₁ < R₀) :
    ∃ b ∈ Ioo (max r₁ 0) R₀,
      b ^ (n - 1) * f b ^ (2 * ((n : ℝ) - 1) / ((n : ℝ) - 2)) * Ginv (F b) < ε := by
  by_contra! hge
  set pₙ := criticalExponent n
  have hpₙ : 0 < pₙ := criticalExponent_pos hn
  set q := 2 * ((n : ℝ) - 1) / ((n : ℝ) - 2)
  set r₂ := max r₁ 0
  have hr₂0 : 0 ≤ r₂ := le_max_right r₁ 0
  have hn1 : 0 < (n : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast (show 1 < n by omega))
  have hn2 : 0 < (n : ℝ) - 2 := sub_pos.mpr (by exact_mod_cast hn)
  set α := ((n : ℝ) - 2) / ((n : ℝ) - 1) with hα_def
  have hα : 0 < α := div_pos hn2 hn1
  set c₀ := α * (ε ^ n / 2 ^ n) ^ (1 / ((n : ℝ) - 1)) / R₀ with hc₀_def
  have hc₀ : 0 < c₀ := by positivity
  let Φ := fun r ↦ I₀ - F r
  have hF_cont : Continuous F := continuous_iff_continuousAt.2 fun r ↦ (hF_deriv r).continuousAt
  have hψ_anti : AntitoneOn (fun r ↦ Φ r ^ α + c₀ * r) (Icc r₂ R₀) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc r₂ R₀)
      (((continuous_const.sub hF_cont).continuousOn.rpow_const fun _ _ ↦ .inr hα.le).add
        (continuousOn_const.mul continuousOn_id)) (fun r hr ↦ ?_) (fun r hr ↦ ?_)
    · rw [interior_Icc] at hr
      have hΦr : 0 < Φ r := sub_pos.mpr (hF_mem r ⟨hr₂0.trans_lt hr.1, hr.2⟩).2
      exact (((((hF_deriv r).const_sub I₀).rpow_const (.inl hΦr.ne')).differentiableAt).add
        (differentiableAt_id.const_mul c₀)).differentiableWithinAt
    · rw [interior_Icc] at hr
      have hr' : r ∈ Ioo 0 R₀ := ⟨hr₂0.trans_lt hr.1, hr.2⟩
      have hr0 : 0 < r := hr'.1; have hfr : 0 < f r := hf_pos r hr'
      have hΦr : 0 < Φ r := sub_pos.mpr (hF_mem r hr').2
      have hGr : 0 < Ginv (F r) := hGinv_pos (F r) (hF_mem r hr')
      have hpow_n : ε ^ n ≤ (r ^ (n - 1)) ^ n * (f r ^ pₙ) ^ (n - 1) * Ginv (F r) ^ n := by
        have hqn : (f r ^ q) ^ n = (f r ^ pₙ) ^ (n - 1) := by
          rw [← Real.rpow_natCast _ n, ← Real.rpow_mul hfr.le, ← Real.rpow_natCast _ (n - 1),
            ← Real.rpow_mul hfr.le, Nat.cast_sub (by omega), Nat.cast_one]
          congr 1; dsimp only [q, pₙ]; rw [criticalExponent_def]; field_simp [hn2.ne']
        simpa only [mul_pow, hqn] using pow_le_pow_left₀ hε.le (hge r hr) n
      have hrpow_split : (r ^ (n - 1)) ^ n * (f r ^ pₙ) ^ (n - 1) ≤
          (R₀ * (r ^ (n - 1) * f r ^ pₙ)) ^ (n - 1) := by
        rw [mul_pow, mul_pow, ← mul_assoc, ← pow_mul, show (n - 1) * n =
          (n - 1) + (n - 1) * (n - 1) by cases n with | zero => omega | succ m => simp; ring,
          pow_add, pow_mul]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr'.1.le hr.2.le _) (by positivity))
          (by positivity)
      have hΦ_bound : ε ^ n / 2 ^ n * Φ r ≤ (R₀ * (r ^ (n - 1) * f r ^ pₙ)) ^ (n - 1) := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        exact (mul_le_mul_of_nonneg_right hpow_n hΦr.le).trans ((mul_assoc _ _ _).le.trans
          (mul_le_mul hrpow_split (htail (F r) (hF_mem r hr')) (by positivity) (by positivity)))
      have hroot : (ε ^ n / 2 ^ n) ^ (1 / ((n : ℝ) - 1)) * Φ r ^ (1 / ((n : ℝ) - 1)) ≤
          R₀ * (r ^ (n - 1) * f r ^ pₙ) := by
        rw [← Real.mul_rpow (by positivity) hΦr.le]
        refine (Real.rpow_le_rpow (by positivity) hΦ_bound (by positivity)).trans_eq ?_
        rw [← Real.rpow_natCast _ (n - 1), ← Real.rpow_mul (by positivity),
          Nat.cast_sub (by omega), Nat.cast_one, mul_one_div_cancel hn1.ne', Real.rpow_one]
      have hdψ : HasDerivAt (fun x ↦ Φ x ^ α + c₀ * x)
          (-(r ^ (n - 1) * f r ^ pₙ) * α * Φ r ^ (α - 1) + c₀ * 1) r := by
        simpa only [Pi.add_def, id_eq] using
          (((hF_deriv r).const_sub I₀).rpow_const (.inl hΦr.ne')).add
            ((hasDerivAt_id r).const_mul c₀)
      rw [hdψ.deriv, show α - 1 = -(1 / ((n : ℝ) - 1)) by rw [hα_def]; field_simp [hn1.ne']; ring,
        Real.rpow_neg hΦr.le]
      have hpos_pow : 0 < Φ r ^ (1 / ((n : ℝ) - 1)) := Real.rpow_pos_of_pos hΦr _
      have hdiv : c₀ ≤ α * (Φ r ^ (1 / ((n : ℝ) - 1)))⁻¹ * (r ^ (n - 1) * f r ^ pₙ) := by
        rw [hc₀_def, div_le_iff₀ hR₀]
        refine (show α * (ε ^ n / 2 ^ n) ^ (1 / ((n : ℝ) - 1)) =
            α * (Φ r ^ (1 / ((n : ℝ) - 1)))⁻¹ *
              ((ε ^ n / 2 ^ n) ^ (1 / ((n : ℝ) - 1)) * Φ r ^ (1 / ((n : ℝ) - 1))) by
          field_simp [hpos_pow.ne']).trans_le
          ((mul_le_mul_of_nonneg_left hroot (by positivity)).trans_eq (by ring))
      linarith
  set C₁ := R₀ ^ (n - 1) * ((K : ℝ) + 1) ^ pₙ
  have hC₁ : 0 ≤ C₁ := by dsimp only [C₁]; positivity
  set β := (pₙ + 1) * α - 1
  have hβ : 0 < β := by
    rw [show β = (2 * (n : ℝ) - 1) / ((n : ℝ) - 1) by
      dsimp only [β, α, pₙ]; rw [criticalExponent_def]; field_simp [hn2.ne', hn1.ne']; ring]
    exact div_pos (by linarith) hn1
  have htend : Tendsto (fun r ↦ C₁ ^ α * (R₀ - r) ^ β) (𝓝[<] R₀) (𝓝 0) := by
    have hsub : Tendsto (fun r ↦ R₀ - r) (𝓝[<] R₀) (𝓝 0) :=
      sub_self R₀ ▸ (tendsto_const_nhds.sub tendsto_id).mono_left nhdsWithin_le_nhds
    simpa only [Real.zero_rpow hβ.ne', mul_zero] using
      (hsub.rpow_const (.inr hβ.le)).const_mul (C₁ ^ α)
  obtain ⟨r, hlt_c₀, hr⟩ :=
    ((htend.eventually (gt_mem_nhds hc₀)).and (Ioo_mem_nhdsLT (max_lt hr₁ hR₀))).exists
  have hr0 : r ∈ Ioo 0 R₀ := ⟨hr₂0.trans_lt hr.1, hr.2⟩
  have hmass_tail : I₀ - F r ≤ C₁ * (R₀ - r) ^ (pₙ + 1) := by
    have hf_int : IntervalIntegrable (fun ρ ↦ ρ ^ (n - 1) * f ρ ^ pₙ) volume r R₀ :=
      ((continuous_pow (n - 1)).mul
        (hf_lip.continuous.rpow_const fun _ ↦ .inr hpₙ.le)).intervalIntegrable r R₀
    rw [← hFR₀, ← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun ρ _ ↦ hF_deriv ρ) hf_int]
    have hint := intervalIntegral.integral_mono_on hr.2.le hf_int
      (intervalIntegrable_const (c := C₁ * (R₀ - r) ^ pₙ)) fun ρ hρ ↦ by
        have hdist : |f ρ - f R₀| ≤ K * |ρ - R₀| := by
          simpa only [Real.dist_eq] using hf_lip.dist_le_mul ρ R₀
        rw [hfR₀, sub_zero, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hρ.2)] at hdist
        have hfρ : f ρ ≤ ((K : ℝ) + 1) * (R₀ - r) :=
          (le_abs_self _).trans (hdist.trans (by nlinarith [K.coe_nonneg, hρ.1, hρ.2]))
        have hfρ0 : 0 ≤ f ρ := (eq_or_lt_of_le hρ.2).elim
          (fun h ↦ by simp [h, hfR₀]) (fun h ↦ (hf_pos ρ ⟨hr0.1.trans_le hρ.1, h⟩).le)
        refine (mul_le_mul (pow_le_pow_left₀ (hr0.1.le.trans hρ.1) hρ.2 _)
          (Real.rpow_le_rpow hfρ0 hfρ hpₙ.le) (Real.rpow_nonneg hfρ0 _) (by positivity)).trans_eq ?_
        dsimp only [C₁]; rw [Real.mul_rpow (by positivity) (sub_nonneg.2 hr.2.le)]; ring
    rw [intervalIntegral.integral_const, smul_eq_mul] at hint
    exact hint.trans_eq (by rw [Real.rpow_add (sub_pos.2 hr.2), Real.rpow_one]; ring)
  have hanti_r : Φ R₀ ^ α + c₀ * R₀ ≤ Φ r ^ α + c₀ * r :=
    hψ_anti (Ioo_subset_Icc_self hr) (right_mem_Icc.2 (max_lt hr₁ hR₀).le) hr.2.le
  simp only [Φ, hFR₀, sub_self, Real.zero_rpow hα.ne', zero_add] at hanti_r
  have hc₀_le : c₀ * (R₀ - r) ≤ (R₀ - r) * (C₁ ^ α * (R₀ - r) ^ β) := by
    calc c₀ * (R₀ - r) ≤ (I₀ - F r) ^ α := by linarith
      _ ≤ (C₁ * (R₀ - r) ^ (pₙ + 1)) ^ α :=
          Real.rpow_le_rpow (sub_nonneg.2 (hF_mem r hr0).2.le) hmass_tail hα.le
      _ = (R₀ - r) * (C₁ ^ α * (R₀ - r) ^ β) := by
          rw [Real.mul_rpow hC₁ (Real.rpow_nonneg (sub_nonneg.2 hr.2.le) _),
            ← Real.rpow_mul (sub_nonneg.2 hr.2.le),
            show (pₙ + 1) * α = 1 + β by dsimp only [β]; ring,
            Real.rpow_add (sub_pos.2 hr.2), Real.rpow_one]; ring
  linarith [le_of_mul_le_mul_left (by simpa only [mul_comm c₀] using hc₀_le) (sub_pos.2 hr.2)]

private theorem exists_support_endpoint_of_antitoneOn {n : ℕ} (hn : 2 < n) {f : ℝ → ℝ}
    (hf_cont : Continuous f) (hf_nonneg : ∀ r, 0 ≤ f r) (hf_anti : AntitoneOn f (Ici 0))
    {R I₀ : ℝ} (hR : 0 < R) (hfR : ∀ r ≥ R, f r = 0) (hI₀ : 0 < I₀)
    (hnorm : ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * f r ^ criticalExponent n = I₀) :
    ∃ R₀ > 0, ∃ F : ℝ → ℝ, f R₀ = 0 ∧ (∀ r ∈ Ioo 0 R₀, 0 < f r) ∧
      F 0 = 0 ∧ F R₀ = I₀ ∧
      (∀ r, HasDerivAt F (r ^ (n - 1) * f r ^ criticalExponent n) r) ∧
      ∀ r ∈ Ioo 0 R₀, F r ∈ Ioo 0 I₀ := by
  set pₙ := criticalExponent n
  have hpₙ : 0 < pₙ := criticalExponent_pos hn
  let Z := {r : ℝ | 0 ≤ r ∧ f r = 0}
  have hZ_bdd : BddBelow Z := ⟨0, fun r hr ↦ hr.1⟩
  set R₀ := sInf Z
  obtain ⟨hR₀_nonneg, hfR₀⟩ : R₀ ∈ Z :=
    (isClosed_Ici.inter (isClosed_eq hf_cont continuous_const)).csInf_mem
      ⟨R, hR.le, hfR R le_rfl⟩ hZ_bdd
  have hf_zero_ge : ∀ r ≥ R₀, f r = 0 := fun r hr ↦
    le_antisymm ((hf_anti hR₀_nonneg (hR₀_nonneg.trans hr) hr).trans_eq hfR₀) (hf_nonneg r)
  have hR₀_pos : 0 < R₀ := lt_of_le_of_ne hR₀_nonneg fun h0 ↦ by
    have hzero : ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * f r ^ pₙ = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero fun r (hr : 0 < r) ↦ by
        rw [hf_zero_ge r (h0 ▸ hr.le), Real.zero_rpow hpₙ.ne', mul_zero]
    linarith [hnorm ▸ hzero]
  have hf_pos : ∀ r ∈ Ioo 0 R₀, 0 < f r := fun r hr ↦
    lt_of_le_of_ne (hf_nonneg r) fun h0 ↦ hr.2.not_ge (csInf_le hZ_bdd ⟨hr.1.le, h0.symm⟩)
  let F : ℝ → ℝ := fun r ↦ ∫ ρ in (0 : ℝ)..r, ρ ^ (n - 1) * f ρ ^ pₙ
  have hF0 : F 0 = 0 := intervalIntegral.integral_same
  have hF_deriv (r : ℝ) : HasDerivAt F (r ^ (n - 1) * f r ^ pₙ) r :=
    (((continuous_pow (n - 1)).mul
      (hf_cont.rpow_const fun _ ↦ .inr hpₙ.le)).integral_hasStrictDerivAt 0 r).hasDerivAt
  have hFR₀ : F R₀ = I₀ := by
    have hint_Ioc : IntegrableOn (fun ρ ↦ ρ ^ (n - 1) * f ρ ^ pₙ) (Ioc 0 R₀) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hR₀_pos.le).1
        (((continuous_pow (n - 1)).mul
          (hf_cont.rpow_const fun _ ↦ .inr hpₙ.le)).intervalIntegrable 0 R₀)
    have hint_Ioi : IntegrableOn (fun ρ ↦ ρ ^ (n - 1) * f ρ ^ pₙ) (Ioi R₀) :=
      integrableOn_zero.congr_fun
        (fun ρ hρ ↦ by rw [hf_zero_ge ρ (mem_Ioi.1 hρ).le, Real.zero_rpow hpₙ.ne', mul_zero])
        measurableSet_Ioi
    rw [← hnorm, ← Ioc_union_Ioi_eq_Ioi hR₀_pos.le,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hint_Ioc hint_Ioi,
      setIntegral_eq_zero_of_forall_eq_zero fun ρ (hρ : ρ ∈ Ioi R₀) ↦ by
        rw [hf_zero_ge ρ (mem_Ioi.1 hρ).le, Real.zero_rpow hpₙ.ne', mul_zero],
      add_zero, ← intervalIntegral.integral_of_le hR₀_pos.le]
  have hF_strict : StrictMonoOn F (Icc 0 R₀) :=
    strictMonoOn_of_deriv_pos (convex_Icc 0 R₀)
      (continuous_iff_continuousAt.2 fun r ↦ (hF_deriv r).continuousAt).continuousOn fun r hr ↦ by
        rw [interior_Icc] at hr; rw [(hF_deriv r).deriv]
        exact mul_pos (pow_pos hr.1 _) (Real.rpow_pos_of_pos (hf_pos r hr) _)
  exact ⟨R₀, hR₀_pos, F, hfR₀, hf_pos, hF0, hFR₀, hF_deriv, fun r hr ↦
    ⟨hF0 ▸ hF_strict (left_mem_Icc.2 hR₀_pos.le) (Ioo_subset_Icc_self hr) hr.1,
     hFR₀ ▸ hF_strict (Ioo_subset_Icc_self hr) (right_mem_Icc.2 hR₀_pos.le) hr.2⟩⟩

private theorem integrableOn_pow_mul_deriv_sq_of_lipschitzWith {n : ℕ} {K : ℝ≥0} {f : ℝ → ℝ}
    (hf_lip : LipschitzWith K f) {R : ℝ} (hR : 0 < R) (hfR : ∀ r ≥ R, f r = 0) :
    IntegrableOn (fun r ↦ r ^ (n - 1) * (deriv f r) ^ 2) (Ioi 0) := by
  refine (((integrableOn_const (s := Ioc 0 R) (C := R ^ (n - 1) * (K : ℝ) ^ 2)
      measure_Ioc_lt_top.ne).integrable_indicator measurableSet_Ioc).integrableOn).mono'
    (((continuous_pow (n - 1)).measurable.mul
      ((measurable_deriv f).pow_const 2)).aestronglyMeasurable.restrict)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun r (hr : 0 < r) ↦ ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg hr.le _) (sq_nonneg _))]
  by_cases hle : r ≤ R
  · rw [indicator_of_mem (mem_Ioc.2 ⟨hr, hle⟩)]
    exact mul_le_mul (pow_le_pow_left₀ hr.le hle _) (sq_le_sq.mpr (by
      simpa only [Real.norm_eq_abs, abs_of_nonneg K.coe_nonneg] using
        norm_deriv_le_of_lipschitz hf_lip)) (sq_nonneg _) (pow_nonneg hR.le _)
  · rw [indicator_of_notMem (fun h ↦ hle (mem_Ioc.1 h).2)]
    have h0 : f =ᶠ[𝓝 r] 0 :=
      eventually_of_mem (Ioi_mem_nhds (lt_of_not_ge hle)) fun x hx ↦ hfR x hx.le
    simp [h0.deriv_eq]

/-- **Sharp one-dimensional weighted Sobolev inequality** for normalized antitone Lipschitz
profiles on `(0, ∞)`. -/
theorem mul_integral_bubbleRadialWeight_le_conformalCoefficient_mul_integral {n : ℕ} (hn : 2 < n)
    {K : ℝ≥0} {f : ℝ → ℝ} (hf_lip : LipschitzWith K f) (hf_nonneg : ∀ r, 0 ≤ f r)
    (hf_anti : AntitoneOn f (Ici 0)) {R : ℝ} (hR : 0 < R) (hfR : ∀ r ≥ R, f r = 0)
    (hnorm : ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * f r ^ criticalExponent n =
      ∫ s in Ioi (0 : ℝ), bubbleRadialWeight n s) :
    (n : ℝ) * ((n : ℝ) - 1) * ∫ s in Ioi (0 : ℝ), bubbleRadialWeight n s ≤
      conformalCoefficient n * ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * (deriv f r) ^ 2 := by
  have hn2 : 0 < (n : ℝ) - 2 := sub_pos.mpr (by exact_mod_cast hn)
  set I₀ := ∫ s in Ioi (0 : ℝ), bubbleRadialWeight n s
  set J₀ := ∫ s in Ioi (0 : ℝ), s ^ 2 * bubbleRadialWeight n s
  obtain ⟨Ginv, hGinv, hGinv_deriv, htail, htend0, htendTop⟩ :=
    exists_inverse_bubbleRadialWeight (n := n) (by omega)
  obtain ⟨R₀, hR₀, F, hfR₀, hf_pos, hF0, hFR₀, hF_deriv, hF_mem⟩ :=
    exists_support_endpoint_of_antitoneOn hn hf_lip.continuous hf_nonneg hf_anti hR hfR
      (integral_bubbleRadialWeight_pos (by omega)) hnorm
  have hderiv_int := integrableOn_pow_mul_deriv_sq_of_lipschitzWith (n := n) hf_lip hR hfR
  set q := 2 * ((n : ℝ) - 1) / ((n : ℝ) - 2)
  set D := ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * (deriv f r) ^ 2
  have hF_cont : Continuous F := continuous_iff_continuousAt.2 fun r ↦ (hF_deriv r).continuousAt
  have hb_est (b : ℝ) (hb : b ∈ Ioo 0 R₀) :
      (n : ℝ) / 2 * F b + 1 / 2 * (∫ s in (0 : ℝ)..Ginv (F b), s ^ 2 * bubbleRadialWeight n s) ≤
        b ^ (n - 1) * f b ^ q * Ginv (F b) + 2 * ((n : ℝ) - 1) / ((n : ℝ) - 2) ^ 2 * D := by
    have hF_lim0 : Tendsto F (𝓝[>] 0) (𝓝 0) := by
      simpa only [hF0] using (hF_cont.tendsto 0).mono_left nhdsWithin_le_nhds
    have hFa_0 : Tendsto (fun a ↦ Ginv (F a)) (𝓝[>] 0) (𝓝 0) :=
      htend0.comp <| tendsto_nhdsWithin_iff.2 ⟨hF_lim0,
        eventually_of_mem (Ioo_mem_nhdsGT hb.1) fun a ha ↦ (hF_mem a ⟨ha.1, ha.2.trans hb.2⟩).1⟩
    let H : ℝ → ℝ := fun u ↦ ∫ s in (0 : ℝ)..u, s ^ 2 * bubbleRadialWeight n s
    have hw2 := (continuous_pow 2).mul (continuous_bubbleRadialWeight n)
    have hH_cont : Continuous H := continuous_iff_continuousAt.2 fun u ↦
      (hw2.integral_hasStrictDerivAt 0 u).hasDerivAt.continuousAt
    have hH_eq (a : ℝ) : (∫ s in (Ginv (F a))..(Ginv (F b)), s ^ 2 * bubbleRadialWeight n s) =
        H (Ginv (F b)) - H (Ginv (F a)) :=
      (intervalIntegral.integral_interval_sub_left (hw2.intervalIntegrable 0 _)
        (hw2.intervalIntegrable 0 _)).symm
    have hlim := (((tendsto_const_nhds (x := F b)).sub hF_lim0).const_mul ((n : ℝ) / 2)).add
      (((tendsto_const_nhds (x := H (Ginv (F b)))).sub
        ((hH_cont.tendsto 0).comp hFa_0)).const_mul (1 / 2))
    rw [sub_zero, show H 0 = 0 from intervalIntegral.integral_same, sub_zero] at hlim
    exact le_of_tendsto (by simpa only [Function.comp_def, ← hH_eq] using hlim)
      (eventually_of_mem (Ioo_mem_nhdsGT hb.1) fun a ha ↦ subinterval_transport_estimate hn hf_lip
        hf_pos hderiv_int (fun y hy ↦ (hGinv y hy).1) hGinv_deriv hF_deriv hF_mem ha.1 ha.2.le hb.2)
  have hmain_raw : (n : ℝ) / 2 * I₀ + 1 / 2 * J₀ ≤ 2 * ((n : ℝ) - 1) / ((n : ℝ) - 2) ^ 2 * D := by
    have hF_limR : Tendsto F (𝓝[<] R₀) (𝓝 I₀) := by
      simpa only [hFR₀] using (hF_cont.tendsto R₀).mono_left nhdsWithin_le_nhds
    have hFb_top : Tendsto (fun b ↦ Ginv (F b)) (𝓝[<] R₀) atTop := htendTop.comp <|
      tendsto_nhdsWithin_iff.2 ⟨hF_limR,
        eventually_of_mem (Ioo_mem_nhdsLT hR₀) fun b hb ↦ (hF_mem b hb).2⟩
    have hLHS_lim : Tendsto (fun b ↦ (n : ℝ) / 2 * F b +
        1 / 2 * (∫ s in (0 : ℝ)..Ginv (F b), s ^ 2 * bubbleRadialWeight n s))
        (𝓝[<] R₀) (𝓝 ((n : ℝ) / 2 * I₀ + 1 / 2 * J₀)) := (hF_limR.const_mul _).add
      ((intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_sq_mul_bubbleRadialWeight hn)
        hFb_top).const_mul _)
    by_contra! hlt
    set ε := ((n : ℝ) / 2 * I₀ + 1 / 2 * J₀ -
      2 * ((n : ℝ) - 1) / ((n : ℝ) - 2) ^ 2 * D) / 3 with hε_def
    have hε : 0 < ε := by positivity
    obtain ⟨r₁, hr₁R₀, hr₁⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp (hLHS_lim.eventually
      (lt_mem_nhds (by linarith : (n : ℝ) / 2 * I₀ + 1 / 2 * J₀ - ε <
        (n : ℝ) / 2 * I₀ + 1 / 2 * J₀)))
    obtain ⟨b, hb, hb_lt⟩ := exists_boundary_term_lt hn hf_lip hR₀ hfR₀ hf_pos
      (fun y hy ↦ (hGinv y hy).1) htail hF_deriv hF_mem hFR₀ hε hr₁R₀
    have h1 : (n : ℝ) / 2 * I₀ + 1 / 2 * J₀ - ε < (n : ℝ) / 2 * F b +
        1 / 2 * (∫ s in (0 : ℝ)..Ginv (F b), s ^ 2 * bubbleRadialWeight n s) :=
      hr₁ ⟨(le_max_left r₁ 0).trans_lt hb.1, hb.2⟩
    have h2 := hb_est b ⟨(le_max_right r₁ 0).trans_lt hb.1, hb.2⟩
    dsimp only [q] at h2; linarith [hε_def]
  have hmul := mul_le_mul_of_nonneg_left hmain_raw (by positivity : 0 ≤ 2 * ((n : ℝ) - 2))
  have hlhs : 2 * ((n : ℝ) - 2) * ((n : ℝ) / 2 * I₀ + 1 / 2 * J₀) =
      (n : ℝ) * ((n : ℝ) - 1) * I₀ := by
    rw [show 2 * ((n : ℝ) - 2) * ((n : ℝ) / 2 * I₀ + 1 / 2 * J₀) =
        (n : ℝ) * ((n : ℝ) - 2) * I₀ + ((n : ℝ) - 2) * J₀ by ring,
      sub_two_mul_integral_sq_mul_bubbleRadialWeight hn]; ring
  have hrhs : 2 * ((n : ℝ) - 2) * (2 * ((n : ℝ) - 1) / ((n : ℝ) - 2) ^ 2 * D) =
      conformalCoefficient n * D := by rw [conformalCoefficient_def]; field_simp [hn2.ne']; ring
  rwa [hlhs, hrhs] at hmul

end TauCeti.Yamabe
