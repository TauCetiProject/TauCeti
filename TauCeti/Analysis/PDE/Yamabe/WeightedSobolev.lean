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
import TauCeti.Analysis.Calculus.Deriv.Integrable
import TauCeti.Analysis.PDE.Yamabe.Bubble.Moments
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Comp
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# The sharp one-dimensional weighted radial Sobolev inequality

For `n > 2`, let `wₙ(s) = s ^ (n - 1) (2 / (1 + s²)) ^ n` (`TauCeti.Yamabe.bubbleRadialWeight n s`)
be the radial critical-mass density of the unit Aubin–Talenti bubble,
`aₙ = 4 (n - 1) / (n - 2)` (`TauCeti.Yamabe.conformalCoefficient`), and `pₙ = 2 n / (n - 2)`
(`TauCeti.Yamabe.criticalExponent`). This file establishes the sharp one-dimensional weighted
Sobolev inequality

`n (n - 1) ∫_{s > 0} wₙ(s) ds ≤ aₙ ∫_{r > 0} r ^ (n - 1) f'(r)² dr`

(`TauCeti.Yamabe.mul_integral_bubbleRadialWeight_le_conformalCoefficient_mul_integral`) for every
Lipschitz profile `f : ℝ → ℝ` that is nonnegative and antitone on `[0, ∞)`, vanishes on `[R, ∞)`
for some `R > 0`, and satisfies the normalization
`∫_{r > 0} r ^ (n - 1) f(r) ^ pₙ dr = ∫_{s > 0} wₙ(s) ds`. It supplies the one-dimensional radial
input for the sharp Euclidean Sobolev inequality in `TauCeti.Analysis.PDE.Yamabe.SharpSobolev`.

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

private theorem exists_inverse_bubbleRadialWeight {n : ℕ} (hn : 0 < n) :
    ∃ Ginv : ℝ → ℝ,
      let I₀ := ∫ s in Ioi (0 : ℝ), bubbleRadialWeight n s;
      (∀ y ∈ Ioo 0 I₀, 0 < Ginv y ∧ (∫ σ in (0 : ℝ)..Ginv y, bubbleRadialWeight n σ) = y) ∧
      (∀ y ∈ Ioo 0 I₀, HasDerivAt Ginv (bubbleRadialWeight n (Ginv y))⁻¹ y) ∧
      (∀ y ∈ Ioo 0 I₀, Ginv y ^ n * (I₀ - y) ≤ 2 ^ n) ∧
      Tendsto Ginv (𝓝[>] 0) (𝓝 0) ∧
      Tendsto Ginv (𝓝[<] I₀) atTop := by
  set I₀ := ∫ s in Ioi (0 : ℝ), bubbleRadialWeight n s with hI₀_def
  have hw := integrableOn_bubbleRadialWeight (n := n) hn
  have hI₀ : 0 < I₀ := integral_bubbleRadialWeight_pos hn
  let G : ℝ → ℝ := fun s ↦ ∫ σ in (0 : ℝ)..s, bubbleRadialWeight n σ
  -- Stage 1: Strict monotonicity, image `(0, I₀)`, and `OrderIso` inverse of `G` on `(0, ∞)`.
  have hG_deriv (s : ℝ) : HasDerivAt G (bubbleRadialWeight n s) s :=
    ((continuous_bubbleRadialWeight n).integral_hasStrictDerivAt 0 s).hasDerivAt
  have hG_cont : Continuous G := continuous_iff_continuousAt.2 fun s ↦ (hG_deriv s).continuousAt
  have hG_mono : StrictMonoOn G (Ici 0) :=
    strictMonoOn_of_deriv_pos (convex_Ici 0) hG_cont.continuousOn fun s hs ↦ by
      rw [interior_Ici] at hs; rw [(hG_deriv s).deriv]; exact bubbleRadialWeight_pos hs
  have hG0 : G 0 = 0 := intervalIntegral.integral_same
  have hG_top : Tendsto G atTop (𝓝 I₀) := intervalIntegral_tendsto_integral_Ioi 0 hw tendsto_id
  have hG_lt_top (s : ℝ) (hs : 0 ≤ s) : G s < I₀ :=
    (hG_mono (mem_Ici.2 hs) (mem_Ici.2 (by linarith)) (lt_add_one s)).trans_le <|
      ge_of_tendsto hG_top <| eventually_of_mem (Ici_mem_atTop (s + 1)) fun t (ht : s + 1 ≤ t) ↦
        hG_mono.monotoneOn (mem_Ici.2 (by linarith)) (mem_Ici.2 (by linarith)) ht
  have hG_image : G '' Ioi 0 = Ioo 0 I₀ := by
    refine Subset.antisymm ?_ fun y hy ↦ ?_
    · rintro _ ⟨s, hs : 0 < s, rfl⟩
      exact ⟨hG0 ▸ hG_mono (mem_Ici.2 le_rfl) (mem_Ici.2 hs.le) hs, hG_lt_top s hs.le⟩
    · obtain ⟨M, hM⟩ := (hG_top.eventually (lt_mem_nhds hy.2)).exists_forall_of_atTop
      obtain ⟨s, hs, hGs⟩ := intermediate_value_Icc (by positivity : 0 ≤ max M 1)
        hG_cont.continuousOn ⟨hG0.symm ▸ hy.1.le, (hM (max M 1) (le_max_left M 1)).le⟩
      exact ⟨s, lt_of_le_of_ne hs.1 fun h0 ↦ hy.1.ne (hG0.symm.trans (h0 ▸ hGs)), hGs⟩
  let e : Ioi (0 : ℝ) ≃o Ioo 0 I₀ :=
    ((hG_mono.mono Ioi_subset_Ici_self).orderIso).trans (Set.orderIsoOfEq _ _ hG_image)
  let Ginv : ℝ → ℝ := fun y ↦ if h : y ∈ Ioo 0 I₀ then (e.symm ⟨y, h⟩ : ℝ) else 0
  have hGinv (y : ℝ) (hy : y ∈ Ioo 0 I₀) :
      0 < Ginv y ∧ (∫ σ in (0 : ℝ)..Ginv y, bubbleRadialWeight n σ) = y := by
    simp only [Ginv, hy, ↓reduceDIte]
    exact ⟨(e.symm ⟨y, hy⟩).property, congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)⟩
  have hGinv_contOn : ContinuousOn Ginv (Ioo 0 I₀) :=
    continuousOn_iff_continuous_domRestrict.2 <|
      (continuous_subtypeVal.comp e.symm.continuous).congr fun y ↦ by
        rw [Function.comp_apply, Set.domRestrict_apply]
        dsimp only [Ginv]
        split_ifs with h
        · rfl
        · exact absurd y.property h
  refine ⟨Ginv, hGinv, fun y hy ↦ ?_, fun y hy ↦ ?_,
    Metric.tendsto_nhds.2 fun ε hε ↦ ?_, Filter.tendsto_atTop.2 fun M ↦ ?_⟩
  · -- Derivative of `Ginv` via `OrderIso.continuous` and `HasDerivAt.of_local_left_inverse`.
    exact HasDerivAt.of_local_left_inverse (hGinv_contOn.continuousAt (isOpen_Ioo.mem_nhds hy))
      (hG_deriv (Ginv y)) (bubbleRadialWeight_pos (hGinv y hy).1).ne'
      (eventually_of_mem (Ioo_mem_nhds hy.1 hy.2) fun z hz ↦ (hGinv z hz).2)
  · -- Stage 2: Tail decay `Ginv(y)^n * (I₀ - y) ≤ 2^n`.
    set s := Ginv y
    obtain ⟨hs, hGs⟩ := hGinv y hy
    have hsplit : I₀ - y = ∫ σ in Ioi s, bubbleRadialWeight n σ := by
      rw [hI₀_def, ← hGs, ← intervalIntegral.integral_Ioi_sub_Ioi hw hs.le]
      ring
    rw [hsplit]
    exact pow_mul_integral_Ioi_bubbleRadialWeight_le hn hs
  · -- Stage 3: Limit `Ginv(y) → 0` as `y → 0⁺`.
    have hGε : 0 < G ε := hG0 ▸ hG_mono (mem_Ici.2 le_rfl) hε.le hε
    filter_upwards [Ioo_mem_nhdsGT (lt_min hGε hI₀)] with y hy
    obtain ⟨hs, hGs⟩ := hGinv y ⟨hy.1, hy.2.trans_le (min_le_right _ _)⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos hs]
    exact not_le.1 fun hle ↦
      (hy.2.trans_le (min_le_left _ _)).not_ge (hGs ▸ hG_mono.monotoneOn hε.le hs.le hle)
  · -- Stage 4: Limit `Ginv(y) → +∞` as `y → I₀⁻`.
    set M' := max M 0
    have hM'0 : 0 ≤ M' := le_max_right M 0
    filter_upwards [Ioo_mem_nhdsLT (max_lt hI₀ (hG_lt_top M' hM'0))] with y hy
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
  have hn1 : 0 ≤ (n : ℝ) - 1 := sub_nonneg.2 (Nat.one_le_cast.2 (by omega))
  have hs'_pos : 0 < s' := not_le.1 fun hle ↦ by
    have hrhs_pos : 0 < r ^ (n - 1) * y ^ criticalExponent n := by positivity
    linarith [mul_nonpos_of_nonpos_of_nonneg hle (bubbleRadialWeight_pos (n := n) hs).le, hrhs_pos]
  have hprod : s' * (s / r) ^ (n - 1) = (y ^ (2 / ((n : ℝ) - 2)) * ((1 + s ^ 2) / 2)) ^ n := by
    have hpow : (y ^ (2 / ((n : ℝ) - 2))) ^ n = y ^ criticalExponent n := by
      rw [← Real.rpow_natCast _ n, ← Real.rpow_mul hy.le, criticalExponent_def]; congr 1; field_simp
    rw [mul_pow, hpow, div_pow, div_pow]; rw [bubbleRadialWeight_def, div_pow] at hode
    field_simp [hr.ne'] at hode ⊢; linarith
  have hgeom : y ^ (2 / ((n : ℝ) - 2)) * ((1 + s ^ 2) / 2) =
      s' ^ (1 / (n : ℝ)) * ((s / r) ^ (((n : ℝ) - 1) / n)) := by
    have hbase : 0 ≤ y ^ (2 / ((n : ℝ) - 2)) * ((1 + s ^ 2) / 2) := by positivity
    have hroot : y ^ (2 / ((n : ℝ) - 2)) * ((1 + s ^ 2) / 2) =
        ((y ^ (2 / ((n : ℝ) - 2)) * ((1 + s ^ 2) / 2)) ^ n) ^ (1 / (n : ℝ)) := by
      rw [← Real.rpow_natCast _ n, ← Real.rpow_mul hbase, mul_one_div_cancel hn0.ne', Real.rpow_one]
    rw [hroot, ← hprod, Real.mul_rpow hs'_pos.le (by positivity),
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
    have hreassoc : (n : ℝ) * r ^ (n - 1) * y ^ q *
        (y ^ (2 / ((n : ℝ) - 2)) * ((1 + s ^ 2) / 2)) =
        (n : ℝ) * r ^ (n - 1) * (y ^ q * y ^ (2 / ((n : ℝ) - 2))) * ((1 + s ^ 2) / 2) := by ring
    rw [hreassoc, hyq]; ring
  have rhs_eq : (n : ℝ) * r ^ (n - 1) * y ^ q *
      (1 / (n : ℝ) * s' + ((n : ℝ) - 1) / n * (s / r)) =
      y ^ q * (((n - 1 : ℕ) : ℝ) * r ^ (n - 2) * s + r ^ (n - 1) * s') := by
    have hrpow : r ^ (n - 1) = r ^ (n - 2) * r := by
      have hsub : n - 2 + 1 = n - 1 := by omega
      rw [← pow_succ, hsub]
    rw [Nat.cast_sub (by omega), Nat.cast_one, hrpow]
    field_simp [hn0.ne', hr.ne']; ring
  rwa [lhs_eq, rhs_eq] at hmul

private theorem subinterval_young_pointwise {n : ℕ} (hn : 2 < n) {r y s d : ℝ}
    (hr : 0 ≤ r) (hy : 0 ≤ y) :
    let q := 2 * ((n : ℝ) - 1) / ((n : ℝ) - 2);
    -(q * y ^ (q - 1) * d * (r ^ (n - 1) * s)) ≤
      ((n : ℝ) - 1) / 2 * (r ^ (n - 1) * y ^ criticalExponent n * s ^ 2) +
        2 * ((n : ℝ) - 1) / ((n : ℝ) - 2) ^ 2 * (r ^ (n - 1) * d ^ 2) := by
  intro q
  have hn1 : 0 < (n : ℝ) - 1 := sub_pos.mpr (Nat.one_lt_cast.2 (by omega))
  have hn2 : 0 < (n : ℝ) - 2 := sub_pos.mpr (by exact_mod_cast hn)
  set A := y ^ (q - 1) * s; set B := 2 / ((n : ℝ) - 2) * (-d)
  have hAB : 2 * A * B ≤ A ^ 2 + B ^ 2 := by simpa only [mul_assoc] using two_mul_le_add_sq A B
  have hmul := mul_le_mul_of_nonneg_left hAB (by positivity : 0 ≤ ((n : ℝ) - 1) / 2 * r ^ (n - 1))
  have hA2 : (y ^ (q - 1)) ^ 2 = y ^ criticalExponent n := by
    have hexp : (q - 1) * 2 = criticalExponent n := by
      dsimp only [q]; rw [criticalExponent_def]; field_simp [hn2.ne']; ring
    rw [← Real.rpow_two, ← Real.rpow_mul hy, hexp]
  have h1 : ((n : ℝ) - 1) / 2 * r ^ (n - 1) * (2 * A * B) =
      -(q * y ^ (q - 1) * d * (r ^ (n - 1) * s)) := by dsimp only [A, B, q]; field_simp [hn2.ne']
  have h2 : ((n : ℝ) - 1) / 2 * r ^ (n - 1) * (A ^ 2 + B ^ 2) =
      ((n : ℝ) - 1) / 2 * (r ^ (n - 1) * y ^ criticalExponent n * s ^ 2) +
        2 * ((n : ℝ) - 1) / ((n : ℝ) - 2) ^ 2 * (r ^ (n - 1) * d ^ 2) := by
    dsimp only [A, B]; rw [mul_pow, hA2]; field_simp [hn2.ne']
  rwa [h1, h2] at hmul

private theorem transport_profile_ac_and_integral_eq {n : ℕ} (hn : 2 < n) {R₀ : ℝ} {K : ℝ≥0}
    {f : ℝ → ℝ} (hf_lip : LipschitzWith K f)
    {I₀ : ℝ} {Ginv : ℝ → ℝ} (hGinv_pos : ∀ y ∈ Ioo 0 I₀, 0 < Ginv y)
    (hGinv_deriv : ∀ y ∈ Ioo 0 I₀, HasDerivAt Ginv (bubbleRadialWeight n (Ginv y))⁻¹ y)
    {F : ℝ → ℝ} (hF_deriv : ∀ r, HasDerivAt F (r ^ (n - 1) * f r ^ criticalExponent n) r)
    (hF_mem : ∀ r ∈ Ioo 0 R₀, F r ∈ Ioo 0 I₀)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < R₀) :
    let T := fun r ↦ Ginv (F r)
    let T' := fun r ↦ r ^ (n - 1) * f r ^ criticalExponent n / bubbleRadialWeight n (T r)
    let g := fun r ↦ r ^ (n - 1) * T r
    let g' := fun r ↦ ((n - 1 : ℕ) : ℝ) * r ^ (n - 2) * T r + r ^ (n - 1) * T' r
    ContinuousOn T (Icc a b) ∧
      (∀ r ∈ Icc a b, HasDerivAt g (g' r) r) ∧
      AbsolutelyContinuousOnInterval g a b ∧
      ∫ r in a..b, r ^ (n - 1) * f r ^ criticalExponent n * T r ^ 2 =
        ∫ s in (T a)..(T b), s ^ 2 * bubbleRadialWeight n s := by
  intro T T' g g'
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
  have hsub : n - 1 - 1 = n - 2 := by omega
  have hg_deriv : ∀ r ∈ Icc a b, HasDerivAt g (g' r) r := fun r hr ↦ by
    simpa only [Pi.mul_def, g, g', hsub, mul_assoc] using
      (hasDerivAt_pow (n - 1) r).mul (hT_deriv r hr)
  have hg_AC : AbsolutelyContinuousOnInterval g a b :=
    (uIcc_of_le hab ▸ ((continuous_pow (n - 1)).continuousOn.mul hT_cont)
      ).absolutelyContinuousOnInterval_of_hasDerivAt_off_countable countable_empty
      (fun r hr ↦ hg_deriv r ⟨(min_eq_left hab ▸ hr.1.1).le, (max_eq_right hab ▸ hr.1.2).le⟩)
      ((((continuousOn_const.mul (continuous_pow (n - 2)).continuousOn).mul hT_cont).add
        ((continuous_pow (n - 1)).continuousOn.mul hT'_cont)).intervalIntegrable_of_Icc hab)
  have hchg : ∫ r in a..b, r ^ (n - 1) * f r ^ criticalExponent n * T r ^ 2 =
      ∫ s in (T a)..(T b), s ^ 2 * bubbleRadialWeight n s := by
    have heq : ∀ r ∈ Icc a b, r ^ (n - 1) * f r ^ criticalExponent n * T r ^ 2 =
        (T r ^ 2 * bubbleRadialWeight n (T r)) * T' r := fun r hr ↦ by
      dsimp only [T']; field_simp [(bubbleRadialWeight_pos (hT_pos hr)).ne']
    rw [intervalIntegral.integral_congr (uIcc_of_le hab ▸ heq)]
    exact intervalIntegral.integral_comp_mul_deriv (uIcc_of_le hab ▸ hT_deriv)
      (uIcc_of_le hab ▸ hT'_cont) ((continuous_pow 2).mul (continuous_bubbleRadialWeight n))
  exact ⟨hT_cont, hg_deriv, hg_AC, hchg⟩

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
  have hn1 : 0 < (n : ℝ) - 1 := sub_pos.mpr (Nat.one_lt_cast.2 (by omega))
  let T := fun r ↦ Ginv (F r)
  let T' := fun r ↦ r ^ (n - 1) * f r ^ pₙ / bubbleRadialWeight n (T r)
  let g := fun r ↦ r ^ (n - 1) * T r
  let g' := fun r ↦ ((n - 1 : ℕ) : ℝ) * r ^ (n - 2) * T r + r ^ (n - 1) * T' r
  have hIoo {r : ℝ} (hr : r ∈ Icc a b) : r ∈ Ioo 0 R₀ := ⟨ha.trans_le hr.1, hr.2.trans_lt hb⟩
  have hT_pos {r : ℝ} (hr : r ∈ Icc a b) : 0 < T r := hGinv_pos (F r) (hF_mem r (hIoo hr))
  -- Stage 1: Transport regularity, change of variables, and absolute continuity of `f^q`.
  obtain ⟨hT_cont, hg_deriv, hg_AC, hchg⟩ :=
    transport_profile_ac_and_integral_eq hn hf_lip hGinv_pos hGinv_deriv hF_deriv hF_mem ha hab hb
  have hg_ae : ∀ᵐ r, r ∈ uIoc a b → HasDerivAt g (g' r) r := .of_forall fun r hr ↦
    hg_deriv r (uIcc_of_le hab ▸ uIoc_subset_uIcc hr)
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
  -- Stage 2: Integrate the pointwise AM–GM lower bound over `[a, b]`.
  have h_amgm_int : (n : ℝ) / 2 * ((F b - F a) +
      ∫ s in (T a)..(T b), s ^ 2 * bubbleRadialWeight n s) ≤ ∫ r in a..b, f r ^ q * g' r := by
    have hcont12 : IntervalIntegrable (fun r ↦ r ^ (n - 1) * f r ^ pₙ * (1 + T r ^ 2))
        volume a b := (hcont1.add hcont2).congr fun r _ ↦ by ring
    have hsum_int : (F b - F a) + ∫ s in (T a)..(T b), s ^ 2 * bubbleRadialWeight n s =
        ∫ r in a..b, r ^ (n - 1) * f r ^ pₙ * (1 + T r ^ 2) := by
      rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ ↦ hF_deriv r) hcont1, ← hchg,
        ← intervalIntegral.integral_add hcont1 hcont2]
      exact intervalIntegral.integral_congr fun r _ ↦ by ring
    rw [hsum_int, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hab (hcont12.const_mul _)
      ((hg_AC.intervalIntegrable_of_ae_hasDerivAt hg_ae).continuousOn_mul hfq_AC.continuousOn)
      fun r hr ↦ mul_one_add_sq_le_rpow_mul_deriv hn (hIoo hr).1 (hT_pos hr) (hf_pos r (hIoo hr))
        (div_mul_cancel₀ _ (bubbleRadialWeight_pos (hT_pos hr)).ne')
  -- Stage 3: Integrate by parts and bound `-∫ h' g` via Young's inequality.
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

private theorem antitoneOn_tail_rpow_add_linear {n : ℕ} (hn : 2 < n) {f : ℝ → ℝ}
    {R₀ : ℝ} (hR₀ : 0 < R₀) (hf_pos : ∀ r ∈ Ioo 0 R₀, 0 < f r)
    {I₀ : ℝ} {Ginv : ℝ → ℝ} (hGinv_pos : ∀ y ∈ Ioo 0 I₀, 0 < Ginv y)
    (htail : ∀ y ∈ Ioo 0 I₀, Ginv y ^ n * (I₀ - y) ≤ 2 ^ n)
    {F : ℝ → ℝ} (hF_deriv : ∀ r, HasDerivAt F (r ^ (n - 1) * f r ^ criticalExponent n) r)
    (hF_mem : ∀ r ∈ Ioo 0 R₀, F r ∈ Ioo 0 I₀)
    {ε r₂ : ℝ} (hε : 0 < ε) (hr₂0 : 0 ≤ r₂)
    (hge : ∀ r ∈ Ioo r₂ R₀,
      ε ≤ r ^ (n - 1) * f r ^ (2 * ((n : ℝ) - 1) / ((n : ℝ) - 2)) * Ginv (F r)) :
    let α := ((n : ℝ) - 2) / ((n : ℝ) - 1)
    let c₀ := α * (ε ^ n / 2 ^ n) ^ (1 / ((n : ℝ) - 1)) / R₀
    AntitoneOn (fun r ↦ (I₀ - F r) ^ α + c₀ * r) (Icc r₂ R₀) := by
  intro α c₀
  set pₙ := criticalExponent n
  set q := 2 * ((n : ℝ) - 1) / ((n : ℝ) - 2)
  have hn1 : 0 < (n : ℝ) - 1 := sub_pos.mpr (Nat.one_lt_cast.2 (by omega))
  have hn2 : 0 < (n : ℝ) - 2 := sub_pos.mpr (by exact_mod_cast hn)
  have hα : 0 < α := div_pos hn2 hn1
  have hF_cont : Continuous F := continuous_iff_continuousAt.2 fun r ↦ (hF_deriv r).continuousAt
  refine antitoneOn_of_deriv_nonpos (convex_Icc r₂ R₀)
    (((continuous_const.sub hF_cont).continuousOn.rpow_const fun _ _ ↦ .inr hα.le).add
      (continuousOn_const.mul continuousOn_id)) (fun r hr ↦ ?_) (fun r hr ↦ ?_)
  · -- Stage 1: Differentiability on `(r₂, R₀)`.
    rw [interior_Icc] at hr
    have hΦr : 0 < I₀ - F r := sub_pos.mpr (hF_mem r ⟨hr₂0.trans_lt hr.1, hr.2⟩).2
    exact (((((hF_deriv r).const_sub I₀).rpow_const (.inl hΦr.ne')).differentiableAt).add
      (differentiableAt_id.const_mul c₀)).differentiableWithinAt
  · -- Stage 2: Combine `hge` with the tail decay of `Ginv` to lower-bound `F'(r)`.
    rw [interior_Icc] at hr
    have hr' : r ∈ Ioo 0 R₀ := ⟨hr₂0.trans_lt hr.1, hr.2⟩
    have hr0 : 0 < r := hr'.1; have hfr : 0 < f r := hf_pos r hr'
    have hΦr : 0 < I₀ - F r := sub_pos.mpr (hF_mem r hr').2
    have hGr : 0 < Ginv (F r) := hGinv_pos (F r) (hF_mem r hr')
    have hpow_n : ε ^ n ≤ (r ^ (n - 1)) ^ n * (f r ^ pₙ) ^ (n - 1) * Ginv (F r) ^ n := by
      have hqn : (f r ^ q) ^ n = (f r ^ pₙ) ^ (n - 1) := by
        rw [← Real.rpow_natCast _ n, ← Real.rpow_mul hfr.le, ← Real.rpow_natCast _ (n - 1),
          ← Real.rpow_mul hfr.le, Nat.cast_sub (by omega), Nat.cast_one]
        congr 1; dsimp only [q, pₙ]; rw [criticalExponent_def]; field_simp [hn2.ne']
      simpa only [mul_pow, hqn] using pow_le_pow_left₀ hε.le (hge r hr) n
    have hrpow_split : (r ^ (n - 1)) ^ n * (f r ^ pₙ) ^ (n - 1) ≤
        (R₀ * (r ^ (n - 1) * f r ^ pₙ)) ^ (n - 1) := by
      have hmul_idx : (n - 1) * n = (n - 1) + (n - 1) * (n - 1) := by
        cases n with | zero => omega | succ m => simp; ring
      rw [mul_pow, mul_pow, ← mul_assoc, ← pow_mul, hmul_idx, pow_add, pow_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr'.1.le hr.2.le _) (by positivity))
        (by positivity)
    have hΦ_bound : ε ^ n / 2 ^ n * (I₀ - F r) ≤ (R₀ * (r ^ (n - 1) * f r ^ pₙ)) ^ (n - 1) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      exact (mul_le_mul_of_nonneg_right hpow_n hΦr.le).trans ((mul_assoc _ _ _).le.trans
        (mul_le_mul hrpow_split (htail (F r) (hF_mem r hr')) (by positivity) (by positivity)))
    have hroot : (ε ^ n / 2 ^ n) ^ (1 / ((n : ℝ) - 1)) * (I₀ - F r) ^ (1 / ((n : ℝ) - 1)) ≤
        R₀ * (r ^ (n - 1) * f r ^ pₙ) := by
      rw [← Real.mul_rpow (by positivity) hΦr.le]
      refine (Real.rpow_le_rpow (by positivity) hΦ_bound (by positivity)).trans_eq ?_
      rw [← Real.rpow_natCast _ (n - 1), ← Real.rpow_mul (by positivity),
        Nat.cast_sub (by omega), Nat.cast_one, mul_one_div_cancel hn1.ne', Real.rpow_one]
    -- Stage 3: Deduce that the derivative of `(I₀ - F r) ^ α + c₀ * r` is nonpositive.
    have hdψ : HasDerivAt (fun x ↦ (I₀ - F x) ^ α + c₀ * x)
        (-(r ^ (n - 1) * f r ^ pₙ) * α * (I₀ - F r) ^ (α - 1) + c₀ * 1) r := by
      simpa only [Pi.add_def, id_eq] using
        (((hF_deriv r).const_sub I₀).rpow_const (.inl hΦr.ne')).add
          ((hasDerivAt_id r).const_mul c₀)
    have hα_sub : α - 1 = -(1 / ((n : ℝ) - 1)) := by dsimp only [α]; field_simp [hn1.ne']; ring
    rw [hdψ.deriv, hα_sub, Real.rpow_neg hΦr.le]
    have hpos_pow : 0 < (I₀ - F r) ^ (1 / ((n : ℝ) - 1)) := Real.rpow_pos_of_pos hΦr _
    have hdiv : c₀ ≤ α * ((I₀ - F r) ^ (1 / ((n : ℝ) - 1)))⁻¹ * (r ^ (n - 1) * f r ^ pₙ) := by
      have hfactor : α * (ε ^ n / 2 ^ n) ^ (1 / ((n : ℝ) - 1)) =
          α * ((I₀ - F r) ^ (1 / ((n : ℝ) - 1)))⁻¹ *
            ((ε ^ n / 2 ^ n) ^ (1 / ((n : ℝ) - 1)) * (I₀ - F r) ^ (1 / ((n : ℝ) - 1))) := by
        field_simp [hpos_pow.ne']
      rw [div_le_iff₀ hR₀]
      exact hfactor.trans_le ((mul_le_mul_of_nonneg_left hroot (by positivity)).trans_eq (by ring))
    linarith

private theorem sub_integral_le_pow_mul_rpow_of_lipschitzWith {n : ℕ} (hn : 2 < n) {K : ℝ≥0}
    {f : ℝ → ℝ} (hf_lip : LipschitzWith K f) {R₀ : ℝ} (hfR₀ : f R₀ = 0)
    (hf_pos : ∀ r ∈ Ioo 0 R₀, 0 < f r) {F : ℝ → ℝ}
    (hF_deriv : ∀ r, HasDerivAt F (r ^ (n - 1) * f r ^ criticalExponent n) r)
    {r : ℝ} (hr : r ∈ Ioo 0 R₀) :
    F R₀ - F r ≤ R₀ ^ (n - 1) * ((K : ℝ) + 1) ^ criticalExponent n *
      (R₀ - r) ^ (criticalExponent n + 1) := by
  set pₙ := criticalExponent n
  have hpₙ : 0 < pₙ := criticalExponent_pos hn
  have hR₀ : 0 < R₀ := hr.1.trans hr.2
  set C₁ := R₀ ^ (n - 1) * ((K : ℝ) + 1) ^ pₙ
  have hf_int : IntervalIntegrable (fun ρ ↦ ρ ^ (n - 1) * f ρ ^ pₙ) volume r R₀ :=
    ((continuous_pow (n - 1)).mul
      (hf_lip.continuous.rpow_const fun _ ↦ .inr hpₙ.le)).intervalIntegrable r R₀
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun ρ _ ↦ hF_deriv ρ) hf_int]
  have hint := intervalIntegral.integral_mono_on hr.2.le hf_int
    (intervalIntegrable_const (c := C₁ * (R₀ - r) ^ pₙ)) fun ρ hρ ↦ by
      have hdist : |f ρ - f R₀| ≤ K * |ρ - R₀| := by
        simpa only [Real.dist_eq] using hf_lip.dist_le_mul ρ R₀
      rw [hfR₀, sub_zero, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hρ.2)] at hdist
      have hfρ : f ρ ≤ ((K : ℝ) + 1) * (R₀ - r) :=
        (le_abs_self _).trans (hdist.trans (by nlinarith [K.coe_nonneg, hρ.1, hρ.2]))
      have hfρ0 : 0 ≤ f ρ := (eq_or_lt_of_le hρ.2).elim
        (fun h ↦ by simp [h, hfR₀]) (fun h ↦ (hf_pos ρ ⟨hr.1.trans_le hρ.1, h⟩).le)
      refine (mul_le_mul (pow_le_pow_left₀ (hr.1.le.trans hρ.1) hρ.2 _)
        (Real.rpow_le_rpow hfρ0 hfρ hpₙ.le) (Real.rpow_nonneg hfρ0 _) (by positivity)).trans_eq ?_
      dsimp only [C₁]; rw [Real.mul_rpow (by positivity) (sub_nonneg.2 hr.2.le)]; ring
  rw [intervalIntegral.integral_const, smul_eq_mul] at hint
  exact hint.trans_eq (by rw [Real.rpow_add (sub_pos.2 hr.2), Real.rpow_one]; ring)

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
  set r₂ := max r₁ 0
  have hr₂0 : 0 ≤ r₂ := le_max_right r₁ 0
  have hn1 : 0 < (n : ℝ) - 1 := sub_pos.mpr (Nat.one_lt_cast.2 (by omega))
  have hn2 : 0 < (n : ℝ) - 2 := sub_pos.mpr (by exact_mod_cast hn)
  set α := ((n : ℝ) - 2) / ((n : ℝ) - 1)
  have hα : 0 < α := div_pos hn2 hn1
  set c₀ := α * (ε ^ n / 2 ^ n) ^ (1 / ((n : ℝ) - 1)) / R₀
  have hc₀ : 0 < c₀ := by positivity
  -- Stage 1: Obtain the linear lower bound `c₀ * (R₀ - r) ≤ (I₀ - F r) ^ α` from antitonicity.
  have hψ_anti := antitoneOn_tail_rpow_add_linear hn hR₀ hf_pos hGinv_pos htail hF_deriv hF_mem
    hε hr₂0 hge
  -- Stage 2: Contradict it near `R₀` via the superlinear Lipschitz upper bound on `(I₀ - F r) ^ α`.
  set C₁ := R₀ ^ (n - 1) * ((K : ℝ) + 1) ^ pₙ
  have hC₁ : 0 ≤ C₁ := by dsimp only [C₁]; positivity
  set β := (pₙ + 1) * α - 1
  have hβ_eq : β = (2 * (n : ℝ) - 1) / ((n : ℝ) - 1) := by
    dsimp only [β, α, pₙ]; rw [criticalExponent_def]; field_simp [hn2.ne', hn1.ne']; ring
  have hβ : 0 < β := hβ_eq ▸ div_pos (by linarith) hn1
  have htend : Tendsto (fun r ↦ C₁ ^ α * (R₀ - r) ^ β) (𝓝[<] R₀) (𝓝 0) := by
    have hsub : Tendsto (fun r ↦ R₀ - r) (𝓝[<] R₀) (𝓝 0) :=
      sub_self R₀ ▸ (tendsto_const_nhds.sub tendsto_id).mono_left nhdsWithin_le_nhds
    simpa only [Real.zero_rpow hβ.ne', mul_zero] using
      (hsub.rpow_const (.inr hβ.le)).const_mul (C₁ ^ α)
  obtain ⟨r, hlt_c₀, hr⟩ :=
    ((htend.eventually (gt_mem_nhds hc₀)).and (Ioo_mem_nhdsLT (max_lt hr₁ hR₀))).exists
  have hr0 : r ∈ Ioo 0 R₀ := ⟨hr₂0.trans_lt hr.1, hr.2⟩
  have hmass_tail : I₀ - F r ≤ C₁ * (R₀ - r) ^ (pₙ + 1) :=
    hFR₀ ▸ sub_integral_le_pow_mul_rpow_of_lipschitzWith hn hf_lip hfR₀ hf_pos hF_deriv hr0
  have hanti_r : (I₀ - F R₀) ^ α + c₀ * R₀ ≤ (I₀ - F r) ^ α + c₀ * r :=
    hψ_anti (Ioo_subset_Icc_self hr) (right_mem_Icc.2 (max_lt hr₁ hR₀).le) hr.2.le
  simp only [hFR₀, sub_self, Real.zero_rpow hα.ne', zero_add] at hanti_r
  have hβ_add : (pₙ + 1) * α = 1 + β := by dsimp only [β]; ring
  have hc₀_le : c₀ * (R₀ - r) ≤ (R₀ - r) * (C₁ ^ α * (R₀ - r) ^ β) := by
    calc c₀ * (R₀ - r) ≤ (I₀ - F r) ^ α := by linarith
      _ ≤ (C₁ * (R₀ - r) ^ (pₙ + 1)) ^ α :=
          Real.rpow_le_rpow (sub_nonneg.2 (hF_mem r hr0).2.le) hmass_tail hα.le
      _ = (R₀ - r) * (C₁ ^ α * (R₀ - r) ^ β) := by
          rw [Real.mul_rpow hC₁ (Real.rpow_nonneg (sub_nonneg.2 hr.2.le) _),
            ← Real.rpow_mul (sub_nonneg.2 hr.2.le), hβ_add,
            Real.rpow_add (sub_pos.2 hr.2), Real.rpow_one]; ring
  linarith [le_of_mul_le_mul_left (by simpa only [mul_comm c₀] using hc₀_le) (sub_pos.2 hr.2)]

private theorem exists_support_endpoint_of_antitoneOn {n : ℕ} (hn : 2 < n) {f : ℝ → ℝ}
    (hf_cont : Continuous f) (hf_nonneg : ∀ r ∈ Ici (0 : ℝ), 0 ≤ f r)
    (hf_anti : AntitoneOn f (Ici 0)) {R I₀ : ℝ} (hR : 0 < R) (hfR : ∀ r ≥ R, f r = 0)
    (hI₀ : 0 < I₀)
    (hnorm : ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * f r ^ criticalExponent n = I₀) :
    ∃ R₀ > 0, ∃ F : ℝ → ℝ, f R₀ = 0 ∧ (∀ r ∈ Ioo 0 R₀, 0 < f r) ∧
      F 0 = 0 ∧ F R₀ = I₀ ∧
      (∀ r, HasDerivAt F (r ^ (n - 1) * f r ^ criticalExponent n) r) ∧
      ∀ r ∈ Ioo 0 R₀, F r ∈ Ioo 0 I₀ := by
  set pₙ := criticalExponent n
  have hpₙ : 0 < pₙ := criticalExponent_pos hn
  -- Stage 1: Locate the first nonnegative zero `R₀` and verify positivity of `f` on `(0, R₀)`.
  let Z := {r : ℝ | 0 ≤ r ∧ f r = 0}
  have hZ_bdd : BddBelow Z := ⟨0, fun r hr ↦ hr.1⟩
  set R₀ := sInf Z
  obtain ⟨hR₀_nonneg, hfR₀⟩ : R₀ ∈ Z :=
    (isClosed_Ici.inter (isClosed_eq hf_cont continuous_const)).csInf_mem
      ⟨R, hR.le, hfR R le_rfl⟩ hZ_bdd
  have hf_zero_ge : ∀ r ≥ R₀, f r = 0 := fun r hr ↦
    le_antisymm ((hf_anti hR₀_nonneg (hR₀_nonneg.trans hr) hr).trans_eq hfR₀)
      (hf_nonneg r (hR₀_nonneg.trans hr))
  have hR₀_pos : 0 < R₀ := lt_of_le_of_ne hR₀_nonneg fun h0 ↦ by
    have hzero : ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * f r ^ pₙ = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero fun r (hr : 0 < r) ↦ by
        rw [hf_zero_ge r (h0 ▸ hr.le), Real.zero_rpow hpₙ.ne', mul_zero]
    linarith [hnorm ▸ hzero]
  have hf_pos : ∀ r ∈ Ioo 0 R₀, 0 < f r := fun r hr ↦
    lt_of_le_of_ne (hf_nonneg r hr.1.le) fun h0 ↦ hr.2.not_ge (csInf_le hZ_bdd ⟨hr.1.le, h0.symm⟩)
  -- Stage 2: Define the cumulative mass function `F` and show `F(R₀) = I₀`.
  let F : ℝ → ℝ := fun r ↦ ∫ ρ in (0 : ℝ)..r, ρ ^ (n - 1) * f ρ ^ pₙ
  have hF0 : F 0 = 0 := intervalIntegral.integral_same
  have hF_deriv (r : ℝ) : HasDerivAt F (r ^ (n - 1) * f r ^ pₙ) r :=
    (((continuous_pow (n - 1)).mul
      (hf_cont.rpow_const fun _ ↦ .inr hpₙ.le)).integral_hasStrictDerivAt 0 r).hasDerivAt
  have hFR₀ : F R₀ = I₀ := by
    have hint_Ioc : IntervalIntegrable (fun ρ ↦ ρ ^ (n - 1) * f ρ ^ pₙ) volume 0 R₀ :=
      ((continuous_pow (n - 1)).mul
        (hf_cont.rpow_const fun _ ↦ .inr hpₙ.le)).intervalIntegrable 0 R₀
    have hint_Ioi : IntegrableOn (fun ρ ↦ ρ ^ (n - 1) * f ρ ^ pₙ) (Ioi R₀) :=
      integrableOn_zero.congr_fun
        (fun ρ hρ ↦ by rw [hf_zero_ge ρ (mem_Ioi.1 hρ).le, Real.zero_rpow hpₙ.ne', mul_zero])
        measurableSet_Ioi
    have htail0 : ∫ ρ in Ioi R₀, ρ ^ (n - 1) * f ρ ^ pₙ = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero fun ρ (hρ : ρ ∈ Ioi R₀) ↦ by
        rw [hf_zero_ge ρ (mem_Ioi.1 hρ).le, Real.zero_rpow hpₙ.ne', mul_zero]
    rw [← hnorm, ← intervalIntegral.integral_interval_add_Ioi' hint_Ioc hint_Ioi, htail0, add_zero]
  -- Stage 3: Deduce strict monotonicity of `F` on `[0, R₀]`.
  have hF_strict : StrictMonoOn F (Icc 0 R₀) :=
    strictMonoOn_of_deriv_pos (convex_Icc 0 R₀)
      (continuous_iff_continuousAt.2 fun r ↦ (hF_deriv r).continuousAt).continuousOn fun r hr ↦ by
        rw [interior_Icc] at hr; rw [(hF_deriv r).deriv]
        exact mul_pos (pow_pos hr.1 _) (Real.rpow_pos_of_pos (hf_pos r hr) _)
  exact ⟨R₀, hR₀_pos, F, hfR₀, hf_pos, hF0, hFR₀, hF_deriv, fun r hr ↦
    ⟨hF0 ▸ hF_strict (left_mem_Icc.2 hR₀_pos.le) (Ioo_subset_Icc_self hr) hr.1,
     hFR₀ ▸ hF_strict (Ioo_subset_Icc_self hr) (right_mem_Icc.2 hR₀_pos.le) hr.2⟩⟩

/-- **Sharp one-dimensional weighted Sobolev inequality** for normalized Lipschitz profiles that are
nonnegative and antitone on `[0, ∞)`. -/
theorem mul_integral_bubbleRadialWeight_le_conformalCoefficient_mul_integral {n : ℕ} (hn : 2 < n)
    {K : ℝ≥0} {f : ℝ → ℝ} (hf_lip : LipschitzWith K f) (hf_nonneg : ∀ r ∈ Ici (0 : ℝ), 0 ≤ f r)
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
  have hderiv_int := integrableOn_pow_mul_deriv_sq_of_lipschitzWith (k := n - 1) hf_lip hR.le hfR
  set q := 2 * ((n : ℝ) - 1) / ((n : ℝ) - 2)
  set D := ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * (deriv f r) ^ 2
  have hF_cont : Continuous F := continuous_iff_continuousAt.2 fun r ↦ (hF_deriv r).continuousAt
  -- Stage 1: Pass `a → 0⁺` in `subinterval_transport_estimate`.
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
    have hH0 : H 0 = 0 := intervalIntegral.integral_same
    rw [sub_zero, hH0, sub_zero] at hlim
    exact le_of_tendsto (by simpa only [Function.comp_def, ← hH_eq] using hlim)
      (eventually_of_mem (Ioo_mem_nhdsGT hb.1) fun a ha ↦ subinterval_transport_estimate hn hf_lip
        hf_pos hderiv_int (fun y hy ↦ (hGinv y hy).1) hGinv_deriv hF_deriv hF_mem ha.1 ha.2.le hb.2)
  -- Stage 2: Pass `b → R₀⁻` along a sequence where the boundary term vanishes.
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
  -- Stage 3: Rescale by `2(n - 2)` and eliminate `J₀` via the bubble radial moment identity.
  have hmul := mul_le_mul_of_nonneg_left hmain_raw (by positivity : 0 ≤ 2 * ((n : ℝ) - 2))
  have hlhs : 2 * ((n : ℝ) - 2) * ((n : ℝ) / 2 * I₀ + 1 / 2 * J₀) =
      (n : ℝ) * ((n : ℝ) - 1) * I₀ := by
    have hexpand : 2 * ((n : ℝ) - 2) * ((n : ℝ) / 2 * I₀ + 1 / 2 * J₀) =
        (n : ℝ) * ((n : ℝ) - 2) * I₀ + ((n : ℝ) - 2) * J₀ := by ring
    rw [hexpand, sub_two_mul_integral_sq_mul_bubbleRadialWeight hn]; ring
  have hrhs : 2 * ((n : ℝ) - 2) * (2 * ((n : ℝ) - 1) / ((n : ℝ) - 2) ^ 2 * D) =
      conformalCoefficient n * D := by rw [conformalCoefficient_def]; field_simp [hn2.ne']; ring
  rwa [hlhs, hrhs] at hmul

end TauCeti.Yamabe
