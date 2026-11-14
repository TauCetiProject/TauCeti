/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.EMetricSpace.Lipschitz
public import TauCeti.Analysis.PDE.Yamabe.Bubble.Basic
public import TauCeti.Analysis.PDE.Yamabe.SphereConstant
public import TauCeti.Analysis.Sobolev.D1p0.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.IntervalIntegral.Inverse
import TauCeti.Analysis.PDE.Yamabe.Bubble.Cutoff
import TauCeti.Analysis.PDE.Yamabe.Bubble.Homogeneous
import TauCeti.Analysis.PDE.Yamabe.Bubble.SobolevQuotient
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Comp
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.SchwarzRearrangement.PolyaSzego
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# The sharp Euclidean Sobolev inequality

Let `E` be a finite-dimensional real inner product space of dimension `n > 2`, equipped with
Lebesgue measure, and put `aₙ = 4 (n - 1) / (n - 2)` (`TauCeti.Yamabe.conformalCoefficient`),
`pₙ = 2 n / (n - 2)` (`TauCeti.Yamabe.criticalExponent`), and
`Y(Sⁿ) = n (n - 1) |Sⁿ| ^ (2 / n)` (`TauCeti.Yamabe.sphereYamabeConstant`). This file proves the
sharp Euclidean Sobolev inequality

`Y(Sⁿ) (∫ |u| ^ pₙ) ^ (2 / pₙ) ≤ aₙ ∫ ‖du‖²`

for compactly supported Lipschitz functions, compactly supported `C¹` functions, and every element
of the homogeneous Sobolev space `D^{1,2}_0(E)` (`TauCeti.D1p0 volume ⊤ 2`), where `Y(Sⁿ)` is
attained by the Aubin–Talenti bubbles and is therefore the least value of the Euclidean Sobolev
quotient on nonzero elements of `D^{1,2}_0(E)` as well as the greatest lower bound on nonzero
smooth compactly supported functions.

## Proof outline

1. **Symmetric decreasing rearrangement.** For a compactly supported `K`-Lipschitz function `u`, the
   real-valued Schwarz rearrangement `v` of `‖u ·‖` is again `K`-Lipschitz, radially antitone, and
   compactly supported; it preserves `∫ |u| ^ pₙ` by equimeasurability and does not increase
   `∫ ‖du‖²` by the Lipschitz Pólya–Szegő inequality
   (`TauCeti.integral_norm_fderiv_toReal_schwarzRearrangement_norm_rpow_le`).
2. **One-dimensional mass transport.** After scaling a nonzero radial profile `f` to have the same
   weighted `L^{pₙ}` mass `I₀ = ∫_{s > 0} s ^ (n - 1) (2 / (1 + s²)) ^ n ds` as the unit bubble,
   let `T : (0, R₀) → (0, ∞)` be the monotone transport matching `r ^ (n - 1) f(r) ^ pₙ dr` with
   `w(s) ds := s ^ (n - 1) (2 / (1 + s²)) ^ n ds`, where `R₀ > 0` is the first zero of `f`. On every
   compact subinterval `[a, b] ⊂ (0, R₀)`, `T` is `C¹` by
   `TauCeti.exists_contDiff_inverse_intervalIntegral`, and the weighted arithmetic–geometric mean
   inequality applied to `(1 / n) T'(r) + ((n - 1) / n) (T(r) / r)` yields
   `(n / 2) r ^ (n - 1) f(r) ^ pₙ (1 + T(r)²) ≤ f(r) ^ q d/dr (r ^ (n - 1) T(r))`
   with `q = 2 (n - 1) / (n - 2)`. Integrating by parts on `[a, b]`, applying Young's inequality to
   `-q r ^ (n - 1) f(r) ^ (pₙ / 2) f'(r) T(r)`, changing variables `s = T(r)` in the quadratic
   bubble-moment term, and showing `liminf_{b → R₀⁻} b ^ (n - 1) f(b) ^ q T(b) = 0` from the tail
   estimate `T(b) ^ n (I₀ - F(b)) ≤ 2 ^ n` gives the sharp radial inequality
   `n (n - 1) I₀ ≤ aₙ ∫_{r > 0} r ^ (n - 1) f'(r)² dr`.
3. **Completion to `D^{1,2}_0(E)`.** Compactly supported `C¹` functions have bounded derivative, so
   they are globally Lipschitz; density of test functions in `D^{1,2}_0(E)` extends the inequality
   to the whole homogeneous Sobolev space, where `exists_sobolevEmbeddingL_ae_eq_bubble` supplies
   extremals.

## Main results

* `sphereYamabeConstant_mul_rpow_le_conformalCoefficient_mul_integral_of_lipschitzWith`:
  sharp Sobolev inequality for compactly supported Lipschitz functions.
* `sphereYamabeConstant_mul_rpow_le_conformalCoefficient_mul_integral`:
  sharp Sobolev inequality for compactly supported `C¹` functions.
* `sphereYamabeConstant_mul_norm_sobolevEmbeddingL_sq_le_conformalCoefficient_mul_norm_sq` and
  `sphereYamabeConstant_mul_rpow_sobolevEmbeddingL_le_conformalCoefficient_mul_integral`:
  sharp Sobolev inequality on `D1p0 volume ⊤ 2` in norm and integral forms.
* `isLeast_image_conformalCoefficient_mul_norm_sq_div` and
  `isGLB_image_conformalCoefficient_mul_integral_div`: `Y(Sⁿ)` is the minimum of the Sobolev
  quotient on nonzero `D^{1,2}_0(E)` functions and the infimum on nonzero smooth compactly
  supported test functions.

## References

* T. Aubin, *Problèmes isopérimétriques et espaces de Sobolev*, J. Differential Geom. 11 (1976),
  573–598.
* G. Talenti, *Best constant in Sobolev inequality*, Ann. Mat. Pura Appl. 110 (1976), 353–372.
* D. Cordero-Erausquin, B. Nazaret, C. Villani, *A mass-transportation approach to sharp Sobolev and
  Gagliardo–Nirenberg inequalities*, Adv. Math. 182 (2004), 307–332.
* E. H. Lieb, M. Loss, *Analysis*, 2nd edition, Chapter 8.
-/

public section

noncomputable section

open Filter Function MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions Gradient NNReal Topology

namespace TauCeti.Yamabe

/-! ### The radial bubble weight and one-dimensional mass transport -/

/-- Radial critical-mass density `s ^ (n - 1) * (2 / (1 + s²)) ^ n` of the unit bubble `U_{1,0}`. -/
private def bubbleRadialWeight (n : ℕ) (s : ℝ) : ℝ :=
  s ^ (n - 1) * (2 / (1 + s ^ 2)) ^ n

private theorem continuous_bubbleRadialWeight (n : ℕ) : Continuous (bubbleRadialWeight n) := by
  unfold bubbleRadialWeight
  refine (continuous_pow (n - 1)).mul ((continuous_const.div ?_ ?_).pow n)
  · exact continuous_const.add (continuous_pow 2)
  · intro s
    positivity

private theorem bubbleRadialWeight_pos {n : ℕ} {s : ℝ} (hs : 0 < s) :
    0 < bubbleRadialWeight n s := by
  unfold bubbleRadialWeight
  positivity

/-- Tail bound on the accumulated bubble mass: for `s > 0`,
`s ^ n * (∫_{σ > 0} w σ - ∫_0^s w σ) ≤ 2 ^ n`. -/
private theorem pow_mul_sub_integral_bubbleRadialWeight_le {n : ℕ} (hn : 0 < n)
    (hw : IntegrableOn (bubbleRadialWeight n) (Ioi 0)) {s : ℝ} (hs : 0 < s) :
    s ^ n * ((∫ σ in Ioi (0 : ℝ), bubbleRadialWeight n σ) -
        ∫ σ in (0 : ℝ)..s, bubbleRadialWeight n σ) ≤ 2 ^ n := by
  have hsplit : (∫ σ in Ioi (0 : ℝ), bubbleRadialWeight n σ) -
      (∫ σ in (0 : ℝ)..s, bubbleRadialWeight n σ) = ∫ σ in Ioi s, bubbleRadialWeight n σ := by
    have hunion : Ioc 0 s ∪ Ioi s = Ioi (0 : ℝ) := Ioc_union_Ioi_eq_Ioi hs.le
    rw [intervalIntegral.integral_of_le hs.le, ← hunion,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hw.mono_set (hunion ▸ subset_union_left)) (hw.mono_set (hunion ▸ subset_union_right))]
    ring
  rw [hsplit]
  let g : ℝ → ℝ := fun σ ↦ -(2 ^ n / (n : ℝ)) * (σ ^ n)⁻¹
  let g' : ℝ → ℝ := fun σ ↦ σ ^ (n - 1) * (2 / σ ^ 2) ^ n
  have hg_deriv : ∀ σ ∈ Ici s, HasDerivAt g (g' σ) σ := fun σ hσ ↦ by
    have hσ0 : 0 < σ := hs.trans_le hσ
    refine (((hasDerivAt_pow n σ).inv (pow_ne_zero n hσ0.ne')).const_mul
      (-(2 ^ n / (n : ℝ)))).congr_deriv ?_
    have hsq : (σ ^ n) ^ 2 = (σ ^ 2) ^ n := by rw [← pow_mul, mul_comm, pow_mul]
    simp only [g', div_pow]
    rw [hsq]
    field_simp [hσ0.ne']
  have hg'_nonneg : ∀ σ ∈ Ioi s, 0 ≤ g' σ := fun σ hσ ↦ by
    have : 0 < σ := hs.trans hσ
    positivity
  have hg_tendsto : Tendsto g atTop (𝓝 0) := by
    simpa [g] using ((tendsto_pow_atTop hn.ne').inv_tendsto_atTop).const_mul (-(2 ^ n / (n : ℝ)))
  have hg_int : ∫ σ in Ioi s, g' σ = 2 ^ n / (n : ℝ) * (s ^ n)⁻¹ := by
    rw [integral_Ioi_of_hasDerivAt_of_nonneg' hg_deriv hg'_nonneg hg_tendsto]
    simp [g]
  have hle : ∫ σ in Ioi s, bubbleRadialWeight n σ ≤ 2 ^ n / (n : ℝ) * (s ^ n)⁻¹ := by
    rw [← hg_int]
    refine setIntegral_mono_on (hw.mono_set (Ioi_subset_Ioi hs.le))
      (integrableOn_Ioi_deriv_of_nonneg' hg_deriv hg'_nonneg hg_tendsto) measurableSet_Ioi
      fun σ (hσ : s < σ) ↦ ?_
    have hσ0 : 0 < σ := hs.trans hσ
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
      (div_le_div_of_nonneg_left zero_le_two (sq_pos_of_pos hσ0) (by linarith)) n)
      (pow_nonneg hσ0.le _)
  calc s ^ n * ∫ σ in Ioi s, bubbleRadialWeight n σ
      ≤ s ^ n * (2 ^ n / (n : ℝ) * (s ^ n)⁻¹) := mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 2 ^ n / (n : ℝ) := by field_simp [hs.ne']
    _ ≤ 2 ^ n := div_le_self (by positivity) (by exact_mod_cast hn)

/-- Existence and properties of the inverse of `s ↦ ∫_0^s w` on `(0, I₀)`. -/
private theorem exists_inverse_bubbleRadialWeight {n : ℕ} (hn : 0 < n)
    (hw : IntegrableOn (bubbleRadialWeight n) (Ioi 0))
    (hI₀ : 0 < ∫ s in Ioi (0 : ℝ), bubbleRadialWeight n s) :
    ∃ Ginv : ℝ → ℝ,
      let I₀ := ∫ s in Ioi (0 : ℝ), bubbleRadialWeight n s;
      let G := fun s : ℝ ↦ ∫ σ in (0 : ℝ)..s, bubbleRadialWeight n σ;
      StrictMonoOn G (Ici 0) ∧
      (∀ y ∈ Ioo 0 I₀, 0 < Ginv y ∧ G (Ginv y) = y) ∧
      (∀ s ≥ 0, ∀ y ∈ Ioo 0 I₀, G s = y → s = Ginv y) ∧
      (∀ y ∈ Ioo 0 I₀, Ginv y ^ n * (I₀ - y) ≤ 2 ^ n) ∧
      Tendsto Ginv (𝓝[>] 0) (𝓝 0) ∧
      Tendsto Ginv (𝓝[<] I₀) atTop := by
  set I₀ := ∫ s in Ioi (0 : ℝ), bubbleRadialWeight n s
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
    have hyG : y ∈ Icc (G 0) (G (max M 1)) :=
      ⟨hG0.symm ▸ hy.1.le, (hM (max M 1) (le_max_left M 1)).le⟩
    obtain ⟨s, hs, hGs⟩ :=
      intermediate_value_Icc (by positivity : 0 ≤ max M 1) hG_cont.continuousOn hyG
    refine ⟨s, lt_of_le_of_ne hs.1 ?_, hGs⟩
    rintro rfl
    exact hy.1.ne (hG0.symm.trans hGs)
  let Ginv : ℝ → ℝ := fun y ↦ if h : y ∈ Ioo 0 I₀ then Classical.choose (hex y h) else 0
  have hGinv (y : ℝ) (hy : y ∈ Ioo 0 I₀) : 0 < Ginv y ∧ G (Ginv y) = y := by
    simpa only [Ginv, hy, ↓reduceDIte] using Classical.choose_spec (hex y hy)
  have hunique (s : ℝ) (hs : 0 ≤ s) (y : ℝ) (hy : y ∈ Ioo 0 I₀) (hGs : G s = y) : s = Ginv y :=
    hG_mono.injOn hs (hGinv y hy).1.le (hGs.trans (hGinv y hy).2.symm)
  have htail (y : ℝ) (hy : y ∈ Ioo 0 I₀) : Ginv y ^ n * (I₀ - y) ≤ 2 ^ n := by
    obtain ⟨hs, hGs⟩ := hGinv y hy
    nth_rw 2 [← hGs]
    exact pow_mul_sub_integral_bubbleRadialWeight_le hn hw hs
  have htend0 : Tendsto Ginv (𝓝[>] 0) (𝓝 0) := Metric.tendsto_nhds.2 fun ε hε ↦ by
    have hGε : 0 < G ε := hG0 ▸ hG_mono (mem_Ici.2 le_rfl) hε.le hε
    filter_upwards [Ioo_mem_nhdsGT (lt_min hGε hI₀)] with y hy
    obtain ⟨hs, hGs⟩ := hGinv y ⟨hy.1, hy.2.trans_le (min_le_right _ _)⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos hs]
    by_contra! hle
    exact (hy.2.trans_le (min_le_left _ _)).not_ge (hGs ▸ hG_mono.monotoneOn hε.le hs.le hle)
  have htendTop : Tendsto Ginv (𝓝[<] I₀) atTop := Filter.tendsto_atTop.2 fun M ↦ by
    set M' := max M 0
    have hM'0 : 0 ≤ M' := le_max_right M 0
    have hM'lt : G M' < I₀ := by
      refine (hG_mono (mem_Ici.2 hM'0) (mem_Ici.2 (by linarith))
        (lt_add_one M')).trans_le (ge_of_tendsto hG_top ?_)
      filter_upwards [Ici_mem_atTop (M' + 1)] with s (hs : M' + 1 ≤ s)
      exact hG_mono.monotoneOn (mem_Ici.2 (by linarith)) (mem_Ici.2 (by linarith)) hs
    filter_upwards [Ioo_mem_nhdsLT (max_lt hI₀ hM'lt)] with y hy
    obtain ⟨hs, hGs⟩ := hGinv y ⟨(le_max_left 0 (G M')).trans_lt hy.1, hy.2⟩
    refine (le_max_left M 0).trans (not_lt.1 fun hlt ↦ ?_)
    exact ((le_max_right 0 (G M')).trans_lt hy.1).not_ge
      (hGs ▸ hG_mono.monotoneOn hs.le hM'0 hlt.le)
  exact ⟨Ginv, hG_mono, hGinv, hunique, htail, htend0, htendTop⟩

/-- Pointwise weighted AM–GM differential inequality along the 1D mass transport map. -/
private theorem mul_one_add_sq_le_rpow_mul_deriv {n : ℕ} (hn : 2 < n) {r s s' y : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hy : 0 < y)
    (hode : s' * bubbleRadialWeight n s = r ^ (n - 1) * y ^ criticalExponent n) :
    (n : ℝ) / 2 * (r ^ (n - 1) * y ^ criticalExponent n * (1 + s ^ 2)) ≤
      y ^ (2 * ((n : ℝ) - 1) / ((n : ℝ) - 2)) *
        (((n - 1 : ℕ) : ℝ) * r ^ (n - 2) * s + r ^ (n - 1) * s') := by
  set q := 2 * ((n : ℝ) - 1) / ((n : ℝ) - 2)
  have hn0 : (0 : ℝ) < n := by positivity
  have hn1 : 0 ≤ (n : ℝ) - 1 := sub_nonneg.2 (by exact_mod_cast (show 1 ≤ n by omega))
  have hw_pos : 0 < bubbleRadialWeight n s := bubbleRadialWeight_pos hs
  have hs'_pos : 0 < s' := by
    by_contra! hle
    have hprod_le : s' * bubbleRadialWeight n s ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hle hw_pos.le
    have hrhs_pos : 0 < r ^ (n - 1) * y ^ criticalExponent n := by positivity
    linarith
  have hprod : s' * (s / r) ^ (n - 1) = (y ^ (2 / ((n : ℝ) - 2)) * ((1 + s ^ 2) / 2)) ^ n := by
    have hpow : (y ^ (2 / ((n : ℝ) - 2))) ^ n = y ^ criticalExponent n := by
      rw [← Real.rpow_natCast _ n, ← Real.rpow_mul hy.le, criticalExponent_def]
      congr 1; field_simp
    rw [mul_pow, hpow, div_pow, div_pow]
    unfold bubbleRadialWeight at hode
    rw [div_pow] at hode
    field_simp [hr.ne'] at hode ⊢
    linarith
  have hgeom : y ^ (2 / ((n : ℝ) - 2)) * ((1 + s ^ 2) / 2) =
      s' ^ (1 / (n : ℝ)) * ((s / r) ^ (((n : ℝ) - 1) / n)) := by
    have hbase : 0 ≤ y ^ (2 / ((n : ℝ) - 2)) * ((1 + s ^ 2) / 2) := by positivity
    calc y ^ (2 / ((n : ℝ) - 2)) * ((1 + s ^ 2) / 2)
        = ((y ^ (2 / ((n : ℝ) - 2)) * ((1 + s ^ 2) / 2)) ^ n) ^ (1 / (n : ℝ)) := by
          rw [← Real.rpow_natCast _ n, ← Real.rpow_mul hbase, mul_one_div_cancel hn0.ne',
            Real.rpow_one]
      _ = (s' * (s / r) ^ (n - 1)) ^ (1 / (n : ℝ)) := by rw [hprod]
      _ = s' ^ (1 / (n : ℝ)) * ((s / r) ^ (((n : ℝ) - 1) / n)) := by
          rw [Real.mul_rpow hs'_pos.le (by positivity), ← Real.rpow_natCast _ (n - 1),
            ← Real.rpow_mul (by positivity), Nat.cast_sub (by omega), Nat.cast_one, mul_one_div]
  have hamgm := Real.geom_mean_le_arith_mean2_weighted (w₁ := 1 / (n : ℝ))
    (w₂ := ((n : ℝ) - 1) / n) (p₁ := s') (p₂ := s / r) (by positivity) (div_nonneg hn1 hn0.le)
    hs'_pos.le (by positivity) (by field_simp; ring)
  rw [← hgeom] at hamgm
  have hmul := mul_le_mul_of_nonneg_left hamgm (by positivity : 0 ≤ (n : ℝ) * r ^ (n - 1) * y ^ q)
  have hyq : y ^ q * y ^ (2 / ((n : ℝ) - 2)) = y ^ criticalExponent n := by
    rw [← Real.rpow_add hy, criticalExponent_def]
    congr 1; dsimp only [q]; field_simp; ring
  have hrpow : r ^ (n - 1) = r ^ (n - 2) * r := by
    rw [← pow_succ, show n - 2 + 1 = n - 1 by omega]
  have lhs_eq : (n : ℝ) * r ^ (n - 1) * y ^ q * (y ^ (2 / ((n : ℝ) - 2)) * ((1 + s ^ 2) / 2)) =
      (n : ℝ) / 2 * (r ^ (n - 1) * y ^ criticalExponent n * (1 + s ^ 2)) := by
    calc (n : ℝ) * r ^ (n - 1) * y ^ q * (y ^ (2 / ((n : ℝ) - 2)) * ((1 + s ^ 2) / 2))
        = (n : ℝ) * r ^ (n - 1) * (y ^ q * y ^ (2 / ((n : ℝ) - 2))) * ((1 + s ^ 2) / 2) := by ring
      _ = (n : ℝ) / 2 * (r ^ (n - 1) * y ^ criticalExponent n * (1 + s ^ 2)) := by rw [hyq]; ring
  have rhs_eq : (n : ℝ) * r ^ (n - 1) * y ^ q *
      (1 / (n : ℝ) * s' + ((n : ℝ) - 1) / n * (s / r)) =
      y ^ q * (((n - 1 : ℕ) : ℝ) * r ^ (n - 2) * s + r ^ (n - 1) * s') := by
    rw [Nat.cast_sub (by omega), Nat.cast_one, hrpow]
    field_simp [hn0.ne', hr.ne']; ring
  rwa [lhs_eq, rhs_eq] at hmul

/-- Smooth local representation `τ` of the 1D transport map `T(r) = Ginv (F r)` on an enlarged
subinterval `[a₀, b₀] ⊂ (0, R₀)`. -/
private theorem exists_contDiff_local_transport {n : ℕ} (hn : 2 < n) {R₀ : ℝ} {f : ℝ → ℝ}
    (hf_cont : Continuous f) (hf_pos : ∀ r ∈ Ioo 0 R₀, 0 < f r) {I₀ : ℝ} {Ginv : ℝ → ℝ}
    (hG_mono : StrictMonoOn (fun s ↦ ∫ σ in (0 : ℝ)..s, bubbleRadialWeight n σ) (Ici 0))
    (hGinv : ∀ y ∈ Ioo 0 I₀,
      0 < Ginv y ∧ (∫ σ in (0 : ℝ)..Ginv y, bubbleRadialWeight n σ) = y)
    (hunique : ∀ s ≥ 0, ∀ y ∈ Ioo 0 I₀,
      (∫ σ in (0 : ℝ)..s, bubbleRadialWeight n σ) = y → s = Ginv y)
    {F : ℝ → ℝ} (hF_deriv : ∀ r, HasDerivAt F (r ^ (n - 1) * f r ^ criticalExponent n) r)
    (hF_mem : ∀ r ∈ Ioo 0 R₀, F r ∈ Ioo 0 I₀)
    {a₀ b₀ : ℝ} (ha₀ : a₀ ∈ Ioo 0 R₀) (hb₀ : b₀ ∈ Ioo 0 R₀) (ha₀b₀ : a₀ ≤ b₀) :
    ∃ τ : ℝ → ℝ, ContDiff ℝ 1 τ ∧ (∀ r ∈ Icc a₀ b₀, Ginv (F r) = τ r) ∧
      ∀ r ∈ Ioo a₀ b₀,
        HasDerivAt τ (r ^ (n - 1) * f r ^ criticalExponent n / bubbleRadialWeight n (τ r)) r := by
  have hF_mono : MonotoneOn F (Icc a₀ b₀) :=
    monotoneOn_of_deriv_nonneg (convex_Icc a₀ b₀)
      (continuous_iff_continuousAt.2 fun r ↦ (hF_deriv r).continuousAt).continuousOn
      (fun r _ ↦ (hF_deriv r).differentiableAt.differentiableWithinAt) fun r hr ↦ by
        rw [interior_Icc] at hr; rw [(hF_deriv r).deriv]
        exact mul_nonneg (pow_nonneg (ha₀.1.trans hr.1).le _)
          (Real.rpow_nonneg (hf_pos r ⟨ha₀.1.trans hr.1, hr.2.trans hb₀.2⟩).le _)
  obtain ⟨hδ0, hGδ⟩ := hGinv (F a₀) (hF_mem a₀ ha₀)
  obtain ⟨hS0, hGS⟩ := hGinv (F b₀) (hF_mem b₀ hb₀)
  have hδS : Ginv (F a₀) ≤ Ginv (F b₀) := not_lt.1 fun hlt ↦
    (hF_mono (left_mem_Icc.2 ha₀b₀) (right_mem_Icc.2 ha₀b₀) ha₀b₀).not_gt
      (hGδ ▸ hGS ▸ hG_mono hS0.le hδ0.le hlt)
  obtain ⟨ψ, _, hψC1, _, hψ⟩ := exists_contDiff_inverse_intervalIntegral hδS
    (continuous_bubbleRadialWeight n).continuousOn fun t ht ↦
      bubbleRadialWeight_pos (hδ0.trans_le ht.1)
  have hsub_int : ∫ σ in Ginv (F a₀)..Ginv (F b₀), bubbleRadialWeight n σ = F b₀ - F a₀ := by
    rw [← intervalIntegral.integral_interval_sub_left
      ((continuous_bubbleRadialWeight n).intervalIntegrable 0 _)
      ((continuous_bubbleRadialWeight n).intervalIntegrable 0 _), hGS, hGδ]
  have hF_C1 : ContDiff ℝ 1 F := contDiff_one_iff_deriv.2 ⟨fun r ↦ (hF_deriv r).differentiableAt, by
    rw [show deriv F = fun r ↦ r ^ (n - 1) * f r ^ criticalExponent n from
      funext fun r ↦ (hF_deriv r).deriv]
    exact (continuous_pow (n - 1)).mul
      (hf_cont.rpow_const fun _ ↦ .inr (criticalExponent_pos hn).le)⟩
  refine ⟨fun r ↦ ψ (F r - F a₀), hψC1.comp (hF_C1.sub contDiff_const), fun r hr ↦ ?_,
    fun r hr ↦ ?_⟩
  · have hy : F r - F a₀ ∈ Icc 0 (∫ σ in Ginv (F a₀)..Ginv (F b₀), bubbleRadialWeight n σ) := by
      rw [hsub_int]
      exact ⟨sub_nonneg.2 (hF_mono (left_mem_Icc.2 ha₀b₀) hr hr.1),
        sub_le_sub_right (hF_mono hr (right_mem_Icc.2 ha₀b₀) hr.2) _⟩
    obtain ⟨hmem, hint, _⟩ := hψ (F r - F a₀) hy
    have hGτ : (∫ σ in (0 : ℝ)..ψ (F r - F a₀), bubbleRadialWeight n σ) = F r := by
      rw [← intervalIntegral.integral_add_adjacent_intervals
        ((continuous_bubbleRadialWeight n).intervalIntegrable 0 _)
        ((continuous_bubbleRadialWeight n).intervalIntegrable _ _), hGδ, hint, add_sub_cancel]
    exact (hunique _ (hδ0.le.trans hmem.1) (F r)
      (hF_mem r ⟨ha₀.1.trans_le hr.1, hr.2.trans_lt hb₀.2⟩) hGτ).symm
  · have hr' := Ioo_subset_Icc_self hr
    have hy : F r - F a₀ ∈ Icc 0 (∫ σ in Ginv (F a₀)..Ginv (F b₀), bubbleRadialWeight n σ) := by
      rw [hsub_int]
      exact ⟨sub_nonneg.2 (hF_mono (left_mem_Icc.2 ha₀b₀) hr' hr.1.le),
        sub_le_sub_right (hF_mono hr' (right_mem_Icc.2 ha₀b₀) hr.2.le) _⟩
    simpa only [Function.comp_def, div_eq_inv_mul] using
      (hψ (F r - F a₀) hy).2.2.comp r ((hF_deriv r).sub_const (F a₀))

/-- Local differentiability and absolute continuity of the 1D transport map `T(r) = Ginv (F r)` on
compact subintervals `[a, b] ⊂ (0, R₀)`. -/
private theorem hasDerivAt_transport_on_Icc {n : ℕ} (hn : 2 < n) {R₀ : ℝ} {f : ℝ → ℝ}
    (hf_cont : Continuous f) (hf_pos : ∀ r ∈ Ioo 0 R₀, 0 < f r) {I₀ : ℝ} {Ginv : ℝ → ℝ}
    (hG_mono : StrictMonoOn (fun s ↦ ∫ σ in (0 : ℝ)..s, bubbleRadialWeight n σ) (Ici 0))
    (hGinv : ∀ y ∈ Ioo 0 I₀,
      0 < Ginv y ∧ (∫ σ in (0 : ℝ)..Ginv y, bubbleRadialWeight n σ) = y)
    (hunique : ∀ s ≥ 0, ∀ y ∈ Ioo 0 I₀,
      (∫ σ in (0 : ℝ)..s, bubbleRadialWeight n σ) = y → s = Ginv y)
    {F : ℝ → ℝ} (hF_deriv : ∀ r, HasDerivAt F (r ^ (n - 1) * f r ^ criticalExponent n) r)
    (hF_mem : ∀ r ∈ Ioo 0 R₀, F r ∈ Ioo 0 I₀)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < R₀) :
    let T := fun r ↦ Ginv (F r);
    let T' := fun r ↦ r ^ (n - 1) * f r ^ criticalExponent n / bubbleRadialWeight n (T r);
    (∀ r ∈ Icc a b, HasDerivAt T (T' r) r) ∧
      ContinuousOn T' (Icc a b) ∧
      AbsolutelyContinuousOnInterval (fun r ↦ r ^ (n - 1) * T r) a b := by
  intro T T'
  have ha₀ : a / 2 ∈ Ioo 0 R₀ := ⟨by linarith, by linarith⟩
  have hb₀ : (b + R₀) / 2 ∈ Ioo 0 R₀ := ⟨by linarith, by linarith⟩
  obtain ⟨τ, hτC1, hT_eq, hτ_deriv⟩ := exists_contDiff_local_transport hn hf_cont hf_pos hG_mono
    hGinv hunique hF_deriv hF_mem ha₀ hb₀ (by linarith)
  have hT_deriv : ∀ r ∈ Icc a b, HasDerivAt T (T' r) r := fun r hr ↦ by
    have hr₀ : r ∈ Ioo (a / 2) ((b + R₀) / 2) := ⟨by linarith [hr.1], by linarith [hr.2]⟩
    have hd := hτ_deriv r hr₀
    rw [← hT_eq r (Ioo_subset_Icc_self hr₀)] at hd
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hr₀.1 hr₀.2] with x hx
    exact hT_eq x (Ioo_subset_Icc_self hx)
  have hT_cont : ContinuousOn T (Icc a b) := fun r hr ↦
    (hT_deriv r hr).continuousAt.continuousWithinAt
  have hT'_cont : ContinuousOn T' (Icc a b) := by
    refine ContinuousOn.div ((continuous_pow (n - 1)).continuousOn.mul
      (hf_cont.continuousOn.rpow_const fun _ _ ↦ .inr (criticalExponent_pos hn).le))
      ((continuous_bubbleRadialWeight n).comp_continuousOn hT_cont) fun r hr ↦
        (bubbleRadialWeight_pos
          (hGinv (F r) (hF_mem r ⟨ha.trans_le hr.1, hr.2.trans_lt hb⟩)).1).ne'
  have hAC : AbsolutelyContinuousOnInterval (fun r ↦ r ^ (n - 1) * T r) a b := by
    refine ((contDiff_id.pow (n - 1)).mul hτC1).contDiffOn.absolutelyContinuousOnInterval.congr
      fun r hr ↦ ?_
    rw [uIcc_of_le hab] at hr
    simp only [id_eq, T, hT_eq r ⟨by linarith [hr.1], by linarith [hr.2]⟩]
  exact ⟨hT_deriv, hT'_cont, hAC⟩

/-- Pointwise Young inequality bounding the integration-by-parts remainder term. -/
private theorem subinterval_young_pointwise {n : ℕ} (hn : 2 < n) {r y s d : ℝ}
    (hr : 0 ≤ r) (hy : 0 ≤ y) :
    let q := 2 * ((n : ℝ) - 1) / ((n : ℝ) - 2);
    -(q * y ^ (q - 1) * d * (r ^ (n - 1) * s)) ≤
      ((n : ℝ) - 1) / 2 * (r ^ (n - 1) * y ^ criticalExponent n * s ^ 2) +
        2 * ((n : ℝ) - 1) / ((n : ℝ) - 2) ^ 2 * (r ^ (n - 1) * d ^ 2) := by
  intro q
  have hn1 : 0 < (n : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast (show 1 < n by omega))
  have hn2 : 0 < (n : ℝ) - 2 := sub_pos.mpr (by exact_mod_cast hn)
  set A := y ^ (q - 1) * s
  set B := 2 / ((n : ℝ) - 2) * (-d)
  have hmul := mul_le_mul_of_nonneg_left (show 2 * A * B ≤ A ^ 2 + B ^ 2 by
    nlinarith [sq_nonneg (A - B)]) (by positivity : 0 ≤ ((n : ℝ) - 1) / 2 * r ^ (n - 1))
  have hA2 : (y ^ (q - 1)) ^ 2 = y ^ criticalExponent n := by
    rw [← Real.rpow_two, ← Real.rpow_mul hy, show (q - 1) * 2 = criticalExponent n by
      dsimp only [q]; rw [criticalExponent_def]; field_simp [hn2.ne']; ring]
  have h1 : ((n : ℝ) - 1) / 2 * r ^ (n - 1) * (2 * A * B) =
      -(q * y ^ (q - 1) * d * (r ^ (n - 1) * s)) := by
    dsimp only [A, B, q]; field_simp [hn2.ne']
  have h2 : ((n : ℝ) - 1) / 2 * r ^ (n - 1) * (A ^ 2 + B ^ 2) =
      ((n : ℝ) - 1) / 2 * (r ^ (n - 1) * y ^ criticalExponent n * s ^ 2) +
        2 * ((n : ℝ) - 1) / ((n : ℝ) - 2) ^ 2 * (r ^ (n - 1) * d ^ 2) := by
    dsimp only [A, B]; rw [mul_pow, hA2]; field_simp [hn2.ne']
  rwa [h1, h2] at hmul

/-- Absolute continuity and almost-everywhere derivative of `f ^ q` on `[a, b]` when `f` is
Lipschitz and strictly positive on `[a, b]`. -/
private theorem ac_rpow_of_lipschitzWith_pos {K : ℝ≥0} {f : ℝ → ℝ} (hf_lip : LipschitzWith K f)
    {a b : ℝ} (hab : a ≤ b) (hf_pos : ∀ r ∈ Icc a b, 0 < f r) (q : ℝ) :
    AbsolutelyContinuousOnInterval (fun r ↦ f r ^ q) a b ∧
      ∀ᵐ r, r ∈ uIoc a b → HasDerivAt (fun x ↦ f x ^ q) (q * f r ^ (q - 1) * deriv f r) r := by
  have hf_AC : AbsolutelyContinuousOnInterval f a b :=
    hf_lip.lipschitzOnWith.absolutelyContinuousOnInterval
  refine ⟨hf_AC.comp_of_contDiffAt (φ := fun y : ℝ ↦ y ^ q) fun _ ⟨r, hr, hfr⟩ ↦ ?_, ?_⟩
  · rw [uIcc_of_le hab] at hr
    exact hfr ▸ Real.contDiffAt_rpow_const_of_ne (hf_pos r hr).ne'
  · filter_upwards [hf_AC.boundedVariationOn.ae_differentiableAt_of_mem_uIcc] with r hrd hr
    have hr' : r ∈ Icc a b := uIcc_of_le hab ▸ uIoc_subset_uIcc hr
    exact ((hrd (uIoc_subset_uIcc hr)).hasDerivAt.rpow_const
      (.inl (hf_pos r hr').ne')).congr_deriv (by ring)

/-- Change of variables `∫_a^b r ^ (n - 1) f(r) ^ pₙ T(r)² dr = ∫_{T(a)}^{T(b)} s² wₙ(s) ds` along
the 1D mass transport map `T = Ginv ∘ F`. -/
private theorem intervalIntegral_secondMoment_transport {n : ℕ} {f F Ginv : ℝ → ℝ}
    {a b : ℝ} (hab : a ≤ b) (hGinv_pos : ∀ r ∈ Icc a b, 0 < Ginv (F r))
    (hT_deriv : ∀ r ∈ Icc a b, HasDerivAt (fun r ↦ Ginv (F r))
      (r ^ (n - 1) * f r ^ criticalExponent n / bubbleRadialWeight n (Ginv (F r))) r)
    (hT'_cont : ContinuousOn
      (fun r ↦ r ^ (n - 1) * f r ^ criticalExponent n / bubbleRadialWeight n (Ginv (F r)))
      (Icc a b)) :
    (∫ r in a..b, r ^ (n - 1) * f r ^ criticalExponent n * Ginv (F r) ^ 2) =
      ∫ s in (Ginv (F a))..(Ginv (F b)), s ^ 2 * bubbleRadialWeight n s := by
  let T := fun r ↦ Ginv (F r)
  let T' := fun r ↦ r ^ (n - 1) * f r ^ criticalExponent n / bubbleRadialWeight n (T r)
  have heq : ∀ r ∈ Icc a b, r ^ (n - 1) * f r ^ criticalExponent n * T r ^ 2 =
      (T r ^ 2 * bubbleRadialWeight n (T r)) * T' r := fun r hr ↦ by
    have hw0 : bubbleRadialWeight n (T r) ≠ 0 := (bubbleRadialWeight_pos (hGinv_pos r hr)).ne'
    calc r ^ (n - 1) * f r ^ criticalExponent n * T r ^ 2
        = T r ^ 2 * (bubbleRadialWeight n (T r) *
            (r ^ (n - 1) * f r ^ criticalExponent n / bubbleRadialWeight n (T r))) := by
          rw [mul_div_cancel₀ _ hw0]; ring
      _ = (T r ^ 2 * bubbleRadialWeight n (T r)) * T' r := by dsimp only [T']; ring
  rw [intervalIntegral.integral_congr (uIcc_of_le hab ▸ heq)]
  exact intervalIntegral.integral_comp_mul_deriv (uIcc_of_le hab ▸ hT_deriv)
    (uIcc_of_le hab ▸ hT'_cont) ((continuous_pow 2).mul (continuous_bubbleRadialWeight n))

/-- Subinterval integral estimate on `[a, b] ⊂ (0, R₀)` from integration by parts and Young's
inequality. -/
private theorem subinterval_transport_estimate {n : ℕ} (hn : 2 < n) {R₀ : ℝ} {K : ℝ≥0}
    {f : ℝ → ℝ} (hf_lip : LipschitzWith K f) (hf_pos : ∀ r ∈ Ioo 0 R₀, 0 < f r)
    (hderiv_int : IntegrableOn (fun r ↦ r ^ (n - 1) * (deriv f r) ^ 2) (Ioi 0))
    {I₀ : ℝ} {Ginv : ℝ → ℝ}
    (hG_mono : StrictMonoOn (fun s ↦ ∫ σ in (0 : ℝ)..s, bubbleRadialWeight n σ) (Ici 0))
    (hGinv : ∀ y ∈ Ioo 0 I₀,
      0 < Ginv y ∧ (∫ σ in (0 : ℝ)..Ginv y, bubbleRadialWeight n σ) = y)
    (hunique : ∀ s ≥ 0, ∀ y ∈ Ioo 0 I₀,
      (∫ σ in (0 : ℝ)..s, bubbleRadialWeight n σ) = y → s = Ginv y)
    {F : ℝ → ℝ} (hF_deriv : ∀ r, HasDerivAt F (r ^ (n - 1) * f r ^ criticalExponent n) r)
    (hF_mem : ∀ r ∈ Ioo 0 R₀, F r ∈ Ioo 0 I₀)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < R₀) :
    (n : ℝ) / 2 * (F b - F a) +
        1 / 2 * (∫ s in (Ginv (F a))..(Ginv (F b)), s ^ 2 * bubbleRadialWeight n s) ≤
      b ^ (n - 1) * f b ^ (2 * ((n : ℝ) - 1) / ((n : ℝ) - 2)) * Ginv (F b) +
        2 * ((n : ℝ) - 1) / ((n : ℝ) - 2) ^ 2 *
          ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * (deriv f r) ^ 2 := by
  set q := 2 * ((n : ℝ) - 1) / ((n : ℝ) - 2)
  let T := fun r ↦ Ginv (F r)
  set pₙ := criticalExponent n
  have hn1 : 0 < (n : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast (show 1 < n by omega))
  obtain ⟨hT_deriv, hT'_cont, hg_AC⟩ := hasDerivAt_transport_on_Icc hn hf_lip.continuous hf_pos
    hG_mono hGinv hunique hF_deriv hF_mem ha hab hb
  let T' := fun r ↦ r ^ (n - 1) * f r ^ pₙ / bubbleRadialWeight n (T r)
  let g := fun r ↦ r ^ (n - 1) * T r
  let g' := fun r ↦ ((n - 1 : ℕ) : ℝ) * r ^ (n - 2) * T r + r ^ (n - 1) * T' r
  have hg_ae : ∀ᵐ r, r ∈ uIoc a b → HasDerivAt g (g' r) r := .of_forall fun r hr ↦ by
    have hd := (hasDerivAt_pow (n - 1) r).mul (hT_deriv r (uIcc_of_le hab ▸ uIoc_subset_uIcc hr))
    simpa only [Pi.mul_def, g, g', show n - 1 - 1 = n - 2 by omega, mul_assoc] using hd
  obtain ⟨hfq_AC, hfq_deriv⟩ := ac_rpow_of_lipschitzWith_pos hf_lip hab
    (fun r hr ↦ hf_pos r ⟨ha.trans_le hr.1, hr.2.trans_lt hb⟩) q
  let h' := fun r ↦ q * f r ^ (q - 1) * deriv f r
  have hT_cont : ContinuousOn T (Icc a b) := fun r hr ↦
    (hT_deriv r hr).continuousAt.continuousWithinAt
  have hcont1 : IntervalIntegrable (fun r ↦ r ^ (n - 1) * f r ^ pₙ) volume a b :=
    ((continuous_pow (n - 1)).continuousOn.mul
      (hf_lip.continuous.continuousOn.rpow_const fun _ _ ↦ .inr (criticalExponent_pos hn).le)
      ).intervalIntegrable_of_Icc hab
  have hcont2 : IntervalIntegrable (fun r ↦ r ^ (n - 1) * f r ^ pₙ * T r ^ 2) volume a b :=
    hcont1.mul_continuousOn (uIcc_of_le hab ▸ hT_cont.pow 2)
  have hchg : ∫ r in a..b, r ^ (n - 1) * f r ^ pₙ * T r ^ 2 =
      ∫ s in (T a)..(T b), s ^ 2 * bubbleRadialWeight n s :=
    intervalIntegral_secondMoment_transport hab
      (fun r hr ↦ (hGinv (F r) (hF_mem r ⟨ha.trans_le hr.1, hr.2.trans_lt hb⟩)).1) hT_deriv hT'_cont
  have h_amgm_int : (n : ℝ) / 2 * ((F b - F a) +
      ∫ s in (T a)..(T b), s ^ 2 * bubbleRadialWeight n s) ≤ ∫ r in a..b, f r ^ q * g' r := by
    have hcont12 : IntervalIntegrable (fun r ↦ r ^ (n - 1) * f r ^ pₙ * (1 + T r ^ 2))
        volume a b := (hcont1.add hcont2).congr fun r _ ↦ by ring
    have hlhs_eq : (F b - F a) + ∫ s in (T a)..(T b), s ^ 2 * bubbleRadialWeight n s =
        ∫ r in a..b, r ^ (n - 1) * f r ^ pₙ * (1 + T r ^ 2) := by
      rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ ↦ hF_deriv r) hcont1, ← hchg,
        ← intervalIntegral.integral_add hcont1 hcont2]
      exact intervalIntegral.integral_congr fun r _ ↦ by ring
    rw [hlhs_eq, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hab (hcont12.const_mul _)
      ((hg_AC.intervalIntegrable_of_ae_hasDerivAt hg_ae).continuousOn_mul hfq_AC.continuousOn)
      fun r hr ↦ ?_
    have hr' : r ∈ Ioo 0 R₀ := ⟨ha.trans_le hr.1, hr.2.trans_lt hb⟩
    exact mul_one_add_sq_le_rpow_mul_deriv hn hr'.1 (hGinv (F r) (hF_mem r hr')).1 (hf_pos r hr')
      (div_mul_cancel₀ _ (bubbleRadialWeight_pos (hGinv (F r) (hF_mem r hr')).1).ne')
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
        hg_AC.continuousOn).neg)
      ((hcont2.const_mul _).add (hderiv_ab.const_mul _)) fun r hr ↦
        subinterval_young_pointwise hn (ha.le.trans hr.1)
          (hf_pos r ⟨ha.trans_le hr.1, hr.2.trans_lt hb⟩).le
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
    have : 0 < T a := (hGinv (F a) (hF_mem a ⟨ha, hab.trans_lt hb⟩)).1
    positivity
  have hgb : f b ^ q * g b = b ^ (n - 1) * f b ^ q * T b := by simp [g]; ring
  dsimp only [T] at h_amgm_int hyoung_int hgb
  linarith

/-- Differential-inequality step for `exists_boundary_term_lt`: if `b ^ (n - 1) f(b) ^ q T(b) ≥ ε`
throughout `(r₂, R₀)`, then `(I₀ - F r) ^ ((n - 2) / (n - 1)) + c₀ * r` is antitone on
`[r₂, R₀]`. -/
private theorem antitoneOn_tail_aux {n : ℕ} (hn : 2 < n) {f : ℝ → ℝ} {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hf_pos : ∀ r ∈ Ioo 0 R₀, 0 < f r) {I₀ : ℝ} {Ginv : ℝ → ℝ}
    (hGinv_pos : ∀ y ∈ Ioo 0 I₀, 0 < Ginv y)
    (htail : ∀ y ∈ Ioo 0 I₀, Ginv y ^ n * (I₀ - y) ≤ 2 ^ n)
    {F : ℝ → ℝ} (hF_deriv : ∀ r, HasDerivAt F (r ^ (n - 1) * f r ^ criticalExponent n) r)
    (hF_mem : ∀ r ∈ Ioo 0 R₀, F r ∈ Ioo 0 I₀)
    {ε r₂ α c₀ : ℝ} (hε : 0 < ε) (hr₂0 : 0 ≤ r₂)
    (hα_def : α = ((n : ℝ) - 2) / ((n : ℝ) - 1))
    (hc₀_def : c₀ = α * (ε ^ n / 2 ^ n) ^ (1 / ((n : ℝ) - 1)) / R₀)
    (hge : ∀ b ∈ Ioo r₂ R₀,
      ε ≤ b ^ (n - 1) * f b ^ (2 * ((n : ℝ) - 1) / ((n : ℝ) - 2)) * Ginv (F b)) :
    AntitoneOn (fun r ↦ (I₀ - F r) ^ α + c₀ * r) (Icc r₂ R₀) := by
  set pₙ := criticalExponent n
  set q := 2 * ((n : ℝ) - 1) / ((n : ℝ) - 2)
  have hn1 : 0 < (n : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast (show 1 < n by omega))
  have hn2 : 0 < (n : ℝ) - 2 := sub_pos.mpr (by exact_mod_cast hn)
  have hα : 0 < α := hα_def ▸ div_pos hn2 hn1
  let Φ := fun r ↦ I₀ - F r
  have hF_cont : Continuous F := continuous_iff_continuousAt.2 fun r ↦ (hF_deriv r).continuousAt
  refine antitoneOn_of_deriv_nonpos (convex_Icc r₂ R₀)
    (((continuous_const.sub hF_cont).continuousOn.rpow_const fun _ _ ↦ .inr hα.le).add
      (continuousOn_const.mul continuousOn_id)) (fun r hr ↦ ?_) (fun r hr ↦ ?_)
  · rw [interior_Icc] at hr
    have hΦr : 0 < Φ r := sub_pos.mpr (hF_mem r ⟨hr₂0.trans_lt hr.1, hr.2⟩).2
    exact (((((hF_deriv r).const_sub I₀).rpow_const (.inl hΦr.ne')).differentiableAt).add
      ((differentiableAt_id.const_mul c₀))).differentiableWithinAt
  · rw [interior_Icc] at hr
    have hr' : r ∈ Ioo 0 R₀ := ⟨hr₂0.trans_lt hr.1, hr.2⟩
    have hr0 : 0 < r := hr'.1
    have hfr : 0 < f r := hf_pos r hr'
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
      have hnat : (n - 1) * n = (n - 1) + (n - 1) * (n - 1) := by
        cases n with
        | zero => omega
        | succ m => simp; ring
      rw [mul_pow, mul_pow, ← mul_assoc, ← pow_mul, hnat, pow_add, pow_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr0.le hr.2.le _) (by positivity))
        (by positivity)
    have hΦ_bound : ε ^ n / 2 ^ n * Φ r ≤ (R₀ * (r ^ (n - 1) * f r ^ pₙ)) ^ (n - 1) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      exact (mul_le_mul_of_nonneg_right hpow_n hΦr.le).trans
        ((mul_assoc _ _ _).le.trans
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
      calc α * (ε ^ n / 2 ^ n) ^ (1 / ((n : ℝ) - 1))
          = α * (Φ r ^ (1 / ((n : ℝ) - 1)))⁻¹ *
              ((ε ^ n / 2 ^ n) ^ (1 / ((n : ℝ) - 1)) * Φ r ^ (1 / ((n : ℝ) - 1))) := by
            field_simp [hpos_pow.ne']
        _ ≤ α * (Φ r ^ (1 / ((n : ℝ) - 1)))⁻¹ * (R₀ * (r ^ (n - 1) * f r ^ pₙ)) :=
            mul_le_mul_of_nonneg_left hroot (by positivity)
        _ = α * (Φ r ^ (1 / ((n : ℝ) - 1)))⁻¹ * (r ^ (n - 1) * f r ^ pₙ) * R₀ := by ring
    linarith

/-- Superlinear vanishing `I₀ - F r ≤ C₁ * (R₀ - r) ^ (pₙ + 1)` near `R₀` for a Lipschitz profile
vanishing at `R₀`. -/
private theorem sub_accumulatedMass_le {n : ℕ} (hn : 2 < n) {K : ℝ≥0} {f : ℝ → ℝ}
    (hf_lip : LipschitzWith K f) {R₀ : ℝ} (hfR₀ : f R₀ = 0)
    (hf_pos : ∀ r ∈ Ioo 0 R₀, 0 < f r) {I₀ : ℝ} {F : ℝ → ℝ}
    (hF_deriv : ∀ r, HasDerivAt F (r ^ (n - 1) * f r ^ criticalExponent n) r) (hFR₀ : F R₀ = I₀)
    {r : ℝ} (hr : r ∈ Ioo 0 R₀) :
    I₀ - F r ≤ R₀ ^ (n - 1) * ((K : ℝ) + 1) ^ criticalExponent n *
      (R₀ - r) ^ (criticalExponent n + 1) := by
  set pₙ := criticalExponent n
  have hpₙ : 0 < pₙ := criticalExponent_pos hn
  have hr0 : 0 < r := hr.1
  have hR₀ : 0 < R₀ := hr.1.trans hr.2
  have hEq : I₀ - F r = ∫ ρ in r..R₀, ρ ^ (n - 1) * f ρ ^ pₙ := by
    rw [← hFR₀, ← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun ρ _ ↦ hF_deriv ρ)]
    exact ((continuous_pow (n - 1)).mul
      (hf_lip.continuous.rpow_const fun _ ↦ .inr hpₙ.le)).intervalIntegrable r R₀
  rw [hEq]
  have hbound : ∀ ρ ∈ Icc r R₀, ρ ^ (n - 1) * f ρ ^ pₙ ≤
      R₀ ^ (n - 1) * ((K : ℝ) + 1) ^ pₙ * (R₀ - r) ^ pₙ := fun ρ hρ ↦ by
    have hdist : |f ρ - f R₀| ≤ K * |ρ - R₀| := by
      simpa only [Real.dist_eq] using hf_lip.dist_le_mul ρ R₀
    rw [hfR₀, sub_zero, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hρ.2)] at hdist
    have hfρ : f ρ ≤ ((K : ℝ) + 1) * (R₀ - r) :=
      (le_abs_self _).trans (hdist.trans (by nlinarith [K.coe_nonneg, hρ.1, hρ.2]))
    have hfρ0 : 0 ≤ f ρ := by
      rcases eq_or_lt_of_le hρ.2 with rfl | hlt
      · simp [hfR₀]
      · exact (hf_pos ρ ⟨hr0.trans_le hρ.1, hlt⟩).le
    calc ρ ^ (n - 1) * f ρ ^ pₙ
        ≤ R₀ ^ (n - 1) * (((K : ℝ) + 1) * (R₀ - r)) ^ pₙ :=
          mul_le_mul (pow_le_pow_left₀ (hr0.le.trans hρ.1) hρ.2 _)
            (Real.rpow_le_rpow hfρ0 hfρ hpₙ.le) (Real.rpow_nonneg hfρ0 _) (by positivity)
      _ = R₀ ^ (n - 1) * ((K : ℝ) + 1) ^ pₙ * (R₀ - r) ^ pₙ := by
          rw [Real.mul_rpow (by positivity) (sub_nonneg.2 hr.2.le)]; ring
  have hint := intervalIntegral.integral_mono_on (μ := volume) hr.2.le
    (((continuous_pow (n - 1)).mul
      (hf_lip.continuous.rpow_const fun _ ↦ .inr hpₙ.le)).intervalIntegrable r R₀)
    intervalIntegrable_const hbound
  rw [intervalIntegral.integral_const, smul_eq_mul] at hint
  exact hint.trans_eq (by rw [Real.rpow_add (sub_pos.2 hr.2), Real.rpow_one]; ring)

/-- Vanishing along a sequence at the support endpoint `R₀`:
`liminf_{b → R₀⁻} b ^ (n - 1) f(b) ^ q T(b) = 0`. -/
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
  have hn1 : 0 < (n : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast (show 1 < n by omega))
  have hn2 : 0 < (n : ℝ) - 2 := sub_pos.mpr (by exact_mod_cast hn)
  set α := ((n : ℝ) - 2) / ((n : ℝ) - 1) with hα_def
  have hα : 0 < α := div_pos hn2 hn1
  set c₀ := α * (ε ^ n / 2 ^ n) ^ (1 / ((n : ℝ) - 1)) / R₀ with hc₀_def
  have hc₀ : 0 < c₀ := by positivity
  have hψ_anti := antitoneOn_tail_aux hn hR₀ hf_pos hGinv_pos htail hF_deriv hF_mem hε
    (le_max_right r₁ 0) hα_def hc₀_def hge
  set C₁ := R₀ ^ (n - 1) * ((K : ℝ) + 1) ^ pₙ
  have hC₁ : 0 ≤ C₁ := by dsimp only [C₁]; positivity
  set β := (pₙ + 1) * α - 1
  have hβ : 0 < β := by
    have hval : β = (2 * (n : ℝ) - 1) / ((n : ℝ) - 1) := by
      dsimp only [β, α, pₙ]; rw [criticalExponent_def]; field_simp [hn2.ne', hn1.ne']; ring
    rw [hval]; exact div_pos (by linarith) hn1
  have htend : Tendsto (fun r ↦ C₁ ^ α * (R₀ - r) ^ β) (𝓝[<] R₀) (𝓝 0) := by
    have hsub : Tendsto (fun r ↦ R₀ - r) (𝓝[<] R₀) (𝓝 0) := by
      rw [← sub_self R₀]
      exact (tendsto_const_nhds.sub tendsto_id).mono_left nhdsWithin_le_nhds
    simpa only [Real.zero_rpow hβ.ne', mul_zero] using
      (hsub.rpow_const (.inr hβ.le)).const_mul (C₁ ^ α)
  obtain ⟨r, hlt_c₀, hr⟩ :=
    ((htend.eventually (gt_mem_nhds hc₀)).and (Ioo_mem_nhdsLT (max_lt hr₁ hR₀))).exists
  have hr0 : r ∈ Ioo 0 R₀ := ⟨(le_max_right r₁ 0).trans_lt hr.1, hr.2⟩
  have hanti_r : (I₀ - F R₀) ^ α + c₀ * R₀ ≤ (I₀ - F r) ^ α + c₀ * r :=
    hψ_anti (Ioo_subset_Icc_self hr) (right_mem_Icc.2 (max_lt hr₁ hR₀).le) hr.2.le
  rw [hFR₀, sub_self, Real.zero_rpow hα.ne', zero_add] at hanti_r
  have hc₀_le : c₀ * (R₀ - r) ≤ (R₀ - r) * (C₁ ^ α * (R₀ - r) ^ β) := by
    calc c₀ * (R₀ - r) ≤ (I₀ - F r) ^ α := by linarith
      _ ≤ (C₁ * (R₀ - r) ^ (pₙ + 1)) ^ α := Real.rpow_le_rpow
          (sub_nonneg.2 (hF_mem r hr0).2.le)
          (sub_accumulatedMass_le hn hf_lip hfR₀ hf_pos hF_deriv hFR₀ hr0) hα.le
      _ = C₁ ^ α * (R₀ - r) ^ ((pₙ + 1) * α) := by
          rw [Real.mul_rpow hC₁ (Real.rpow_nonneg (sub_nonneg.2 hr.2.le) _),
            ← Real.rpow_mul (sub_nonneg.2 hr.2.le)]
      _ = (R₀ - r) * (C₁ ^ α * (R₀ - r) ^ β) := by
          rw [show (pₙ + 1) * α = 1 + β by dsimp only [β]; ring,
            Real.rpow_add (sub_pos.2 hr.2), Real.rpow_one]; ring
  have hc₀_le' : c₀ ≤ C₁ ^ α * (R₀ - r) ^ β :=
    le_of_mul_le_mul_left (by simpa only [mul_comm c₀] using hc₀_le) (sub_pos.2 hr.2)
  linarith

/-- Support endpoint `R₀ = inf {r ≥ 0 | f r = 0}` and accumulated mass `F` for a nonnegative
compactly supported antitone profile of positive integral. -/
private theorem exists_support_endpoint_of_antitoneOn {n : ℕ} (hn : 2 < n) {f : ℝ → ℝ}
    (hf_cont : Continuous f) (hf_nonneg : ∀ r, 0 ≤ f r) (hf_anti : AntitoneOn f (Ici 0))
    {R I₀ : ℝ} (hR : 0 < R) (hfR : ∀ r ≥ R, f r = 0) (hI₀ : 0 < I₀)
    (hnorm : ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * f r ^ criticalExponent n = I₀) :
    ∃ R₀ ∈ Ioc 0 R, ∃ F : ℝ → ℝ, f R₀ = 0 ∧ (∀ r ∈ Ioo 0 R₀, 0 < f r) ∧
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
  have hR₀_le : R₀ ≤ R := csInf_le hZ_bdd ⟨hR.le, hfR R le_rfl⟩
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
    have hint_Ioi : IntegrableOn (fun ρ ↦ ρ ^ (n - 1) * f ρ ^ pₙ) (Ioi R₀) := by
      refine integrableOn_zero.congr_fun (fun ρ hρ ↦ ?_) measurableSet_Ioi
      rw [hf_zero_ge ρ (mem_Ioi.1 hρ).le, Real.zero_rpow hpₙ.ne', mul_zero]
    have htail0 : ∫ ρ in Ioi R₀, ρ ^ (n - 1) * f ρ ^ pₙ = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero fun ρ (hρ : ρ ∈ Ioi R₀) ↦ by
        rw [hf_zero_ge ρ (mem_Ioi.1 hρ).le, Real.zero_rpow hpₙ.ne', mul_zero]
    rw [← hnorm, ← Ioc_union_Ioi_eq_Ioi hR₀_pos.le,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hint_Ioc hint_Ioi,
      htail0, add_zero, ← intervalIntegral.integral_of_le hR₀_pos.le]
  have hF_strict : StrictMonoOn F (Icc 0 R₀) :=
    strictMonoOn_of_deriv_pos (convex_Icc 0 R₀)
      (continuous_iff_continuousAt.2 fun r ↦ (hF_deriv r).continuousAt).continuousOn fun r hr ↦ by
        rw [interior_Icc] at hr; rw [(hF_deriv r).deriv]
        exact mul_pos (pow_pos hr.1 _) (Real.rpow_pos_of_pos (hf_pos r hr) _)
  refine ⟨R₀, ⟨hR₀_pos, hR₀_le⟩, F, hfR₀, hf_pos, hF0, hFR₀, hF_deriv, fun r hr ↦ ⟨?_, ?_⟩⟩
  · simpa only [hF0] using hF_strict (left_mem_Icc.2 hR₀_pos.le) (Ioo_subset_Icc_self hr) hr.1
  · simpa only [hFR₀] using hF_strict (Ioo_subset_Icc_self hr) (right_mem_Icc.2 hR₀_pos.le) hr.2

/-- Weighted `L²` derivative integrability for a compactly supported Lipschitz profile on
`(0, ∞)`. -/
private theorem integrableOn_pow_mul_deriv_sq_of_lipschitzWith {n : ℕ} {K : ℝ≥0} {f : ℝ → ℝ}
    (hf_lip : LipschitzWith K f) {R : ℝ} (hR : 0 < R) (hfR : ∀ r ≥ R, f r = 0) :
    IntegrableOn (fun r ↦ r ^ (n - 1) * (deriv f r) ^ 2) (Ioi 0) := by
  have hdom : IntegrableOn (Set.indicator (Ioc 0 R) fun _ : ℝ ↦ R ^ (n - 1) * (K : ℝ) ^ 2)
      (Ioi 0) :=
    ((integrableOn_const measure_Ioc_lt_top.ne).integrable_indicator
      measurableSet_Ioc).integrableOn
  refine hdom.mono' (((continuous_pow (n - 1)).measurable.mul
    ((measurable_deriv f).pow_const 2)).aestronglyMeasurable.restrict) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun r (hr : r ∈ Ioi (0 : ℝ)) ↦ ?_
  have hr0 : 0 < r := mem_Ioi.1 hr
  rw [Real.norm_eq_abs]
  by_cases hle : r ≤ R
  · rw [indicator_of_mem (mem_Ioc.2 ⟨hr0, hle⟩),
      abs_of_nonneg (mul_nonneg (pow_nonneg hr0.le _) (sq_nonneg _))]
    refine mul_le_mul (pow_le_pow_left₀ hr0.le hle _) ?_ (sq_nonneg _) (pow_nonneg hR.le _)
    exact sq_le_sq.mpr (by
      simpa only [Real.norm_eq_abs, abs_of_nonneg K.coe_nonneg] using
        norm_deriv_le_of_lipschitz hf_lip)
  · rw [indicator_of_notMem (fun h ↦ hle (mem_Ioc.1 h).2)]
    have hev : f =ᶠ[𝓝 r] 0 := by
      filter_upwards [Ioi_mem_nhds (lt_of_not_ge hle)] with x hx
      exact hfR x hx.le
    simp [hev.deriv_eq]

/-- **Sharp one-dimensional weighted Sobolev inequality** for a normalized compactly supported
Lipschitz antitone profile. -/
private theorem one_dim_sharp_sobolev_normalized {n : ℕ} (hn : 2 < n)
    (hw₁ : IntegrableOn (bubbleRadialWeight n) (Ioi 0))
    (hw₂ : IntegrableOn (fun s ↦ s ^ 2 * bubbleRadialWeight n s) (Ioi 0))
    (hI₀ : 0 < ∫ s in Ioi (0 : ℝ), bubbleRadialWeight n s)
    (hmom : ((n : ℝ) - 2) * ∫ s in Ioi (0 : ℝ), s ^ 2 * bubbleRadialWeight n s =
      (n : ℝ) * ∫ s in Ioi (0 : ℝ), bubbleRadialWeight n s)
    {K : ℝ≥0} {f : ℝ → ℝ} (hf_lip : LipschitzWith K f) (hf_nonneg : ∀ r, 0 ≤ f r)
    (hf_anti : AntitoneOn f (Ici 0)) {R : ℝ} (hR : 0 < R) (hfR : ∀ r ≥ R, f r = 0)
    (hnorm : ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * f r ^ criticalExponent n =
      ∫ s in Ioi (0 : ℝ), bubbleRadialWeight n s) :
    (n : ℝ) * ((n : ℝ) - 1) * ∫ s in Ioi (0 : ℝ), bubbleRadialWeight n s ≤
      conformalCoefficient n * ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * (deriv f r) ^ 2 := by
  have hn2 : 0 < (n : ℝ) - 2 := sub_pos.mpr (by exact_mod_cast hn)
  set I₀ := ∫ s in Ioi (0 : ℝ), bubbleRadialWeight n s
  set J₀ := ∫ s in Ioi (0 : ℝ), s ^ 2 * bubbleRadialWeight n s
  obtain ⟨Ginv, hG_mono, hGinv, hunique, htail, htend0, htendTop⟩ :=
    exists_inverse_bubbleRadialWeight (by omega) hw₁ hI₀
  obtain ⟨R₀, ⟨hR₀, _⟩, F, hfR₀, hf_pos, hF0, hFR₀, hF_deriv, hF_mem⟩ :=
    exists_support_endpoint_of_antitoneOn hn hf_lip.continuous hf_nonneg hf_anti hR hfR hI₀ hnorm
  have hderiv_int := integrableOn_pow_mul_deriv_sq_of_lipschitzWith (n := n) hf_lip hR hfR
  set q := 2 * ((n : ℝ) - 1) / ((n : ℝ) - 2)
  set D := ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * (deriv f r) ^ 2
  have hF_cont : Continuous F := continuous_iff_continuousAt.2 fun r ↦ (hF_deriv r).continuousAt
  have hb_est (b : ℝ) (hb : b ∈ Ioo 0 R₀) :
      (n : ℝ) / 2 * F b + 1 / 2 * (∫ s in (0 : ℝ)..Ginv (F b), s ^ 2 * bubbleRadialWeight n s) ≤
        b ^ (n - 1) * f b ^ q * Ginv (F b) + 2 * ((n : ℝ) - 1) / ((n : ℝ) - 2) ^ 2 * D := by
    have hF_lim0 : Tendsto F (𝓝[>] 0) (𝓝 0) := by
      simpa only [hF0] using (hF_cont.tendsto 0).mono_left nhdsWithin_le_nhds
    have hFa_0 : Tendsto (fun a ↦ Ginv (F a)) (𝓝[>] 0) (𝓝 0) := by
      refine htend0.comp (tendsto_nhdsWithin_iff.2 ⟨hF_lim0, ?_⟩)
      filter_upwards [Ioo_mem_nhdsGT hb.1] with a ha
      exact (hF_mem a ⟨ha.1, ha.2.trans hb.2⟩).1
    let H : ℝ → ℝ := fun u ↦ ∫ s in (0 : ℝ)..u, s ^ 2 * bubbleRadialWeight n s
    have hH_cont : Continuous H := continuous_iff_continuousAt.2 fun u ↦
      (((continuous_pow 2).mul (continuous_bubbleRadialWeight n)).integral_hasStrictDerivAt
        0 u).hasDerivAt.continuousAt
    have hH0 : H 0 = 0 := intervalIntegral.integral_same
    have hH_eq (a : ℝ) : (∫ s in (Ginv (F a))..(Ginv (F b)), s ^ 2 * bubbleRadialWeight n s) =
        H (Ginv (F b)) - H (Ginv (F a)) :=
      (intervalIntegral.integral_interval_sub_left (f := fun s ↦ s ^ 2 * bubbleRadialWeight n s)
        (((continuous_pow 2).mul (continuous_bubbleRadialWeight n)).intervalIntegrable 0 _)
        (((continuous_pow 2).mul (continuous_bubbleRadialWeight n)).intervalIntegrable 0 _)).symm
    have hlim := (((tendsto_const_nhds (x := F b)).sub hF_lim0).const_mul ((n : ℝ) / 2)).add
      (((tendsto_const_nhds (x := H (Ginv (F b)))).sub
        ((hH_cont.tendsto 0).comp hFa_0)).const_mul (1 / 2))
    rw [sub_zero, hH0, sub_zero] at hlim
    refine le_of_tendsto (by simpa only [Function.comp_def, ← hH_eq] using hlim) ?_
    filter_upwards [Ioo_mem_nhdsGT hb.1] with a ha
    exact subinterval_transport_estimate hn hf_lip hf_pos hderiv_int hG_mono hGinv hunique
      hF_deriv hF_mem ha.1 ha.2.le hb.2
  have hmain_raw : (n : ℝ) / 2 * I₀ + 1 / 2 * J₀ ≤ 2 * ((n : ℝ) - 1) / ((n : ℝ) - 2) ^ 2 * D := by
    have hF_limR : Tendsto F (𝓝[<] R₀) (𝓝 I₀) := by
      simpa only [hFR₀] using (hF_cont.tendsto R₀).mono_left nhdsWithin_le_nhds
    have hFb_top : Tendsto (fun b ↦ Ginv (F b)) (𝓝[<] R₀) atTop := by
      refine htendTop.comp (tendsto_nhdsWithin_iff.2 ⟨hF_limR, ?_⟩)
      filter_upwards [Ioo_mem_nhdsLT hR₀] with b hb
      exact (hF_mem b hb).2
    have hLHS_lim : Tendsto (fun b ↦ (n : ℝ) / 2 * F b +
        1 / 2 * (∫ s in (0 : ℝ)..Ginv (F b), s ^ 2 * bubbleRadialWeight n s))
        (𝓝[<] R₀) (𝓝 ((n : ℝ) / 2 * I₀ + 1 / 2 * J₀)) :=
      (hF_limR.const_mul _).add ((intervalIntegral_tendsto_integral_Ioi 0 hw₂ hFb_top).const_mul _)
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
    dsimp only [q] at h2
    linarith [hε_def]
  have hmul := mul_le_mul_of_nonneg_left hmain_raw (by positivity : 0 ≤ 2 * ((n : ℝ) - 2))
  have hlhs : 2 * ((n : ℝ) - 2) * ((n : ℝ) / 2 * I₀ + 1 / 2 * J₀) =
      (n : ℝ) * ((n : ℝ) - 1) * I₀ := by
    calc 2 * ((n : ℝ) - 2) * ((n : ℝ) / 2 * I₀ + 1 / 2 * J₀)
        = (n : ℝ) * ((n : ℝ) - 2) * I₀ + ((n : ℝ) - 2) * J₀ := by ring
      _ = (n : ℝ) * ((n : ℝ) - 2) * I₀ + (n : ℝ) * I₀ := by rw [hmom]
      _ = (n : ℝ) * ((n : ℝ) - 1) * I₀ := by ring
  have hrhs : 2 * ((n : ℝ) - 2) * (2 * ((n : ℝ) - 1) / ((n : ℝ) - 2) ^ 2 * D) =
      conformalCoefficient n * D := by
    rw [conformalCoefficient_def]; field_simp [hn2.ne']; ring
  rwa [hlhs, hrhs] at hmul

/-! ### Radial functions, rearrangement, and the sharp Euclidean Sobolev inequality -/

section EuclideanSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Every open ball of positive radius has strictly positive finite Lebesgue volume. -/
private theorem volume_real_ball_pos {r : ℝ} (hr : 0 < r) :
    0 < volume.real (ball (0 : E) r) := by
  rw [measureReal_def]
  exact ENNReal.toReal_pos (isOpen_ball.measure_pos volume (nonempty_ball.2 hr)).ne'
    measure_ball_lt_top.ne

/-- Polar-coordinate integrability, value, and second-moment identity for `bubbleRadialWeight`. -/
private theorem bubbleRadialWeight_integrals (hn : 2 < finrank ℝ E) :
    IntegrableOn (bubbleRadialWeight (finrank ℝ E)) (Ioi 0) ∧
      IntegrableOn (fun s ↦ s ^ 2 * bubbleRadialWeight (finrank ℝ E) s) (Ioi 0) ∧
      (finrank ℝ E : ℝ) * (volume.real (ball (0 : E) 1) *
          ∫ s in Ioi (0 : ℝ), bubbleRadialWeight (finrank ℝ E) s) =
        roundSphereVolume (finrank ℝ E) ∧
      0 < ∫ s in Ioi (0 : ℝ), bubbleRadialWeight (finrank ℝ E) s ∧
      ((finrank ℝ E : ℝ) - 2) * ∫ s in Ioi (0 : ℝ), s ^ 2 * bubbleRadialWeight (finrank ℝ E) s =
        (finrank ℝ E : ℝ) * ∫ s in Ioi (0 : ℝ), bubbleRadialWeight (finrank ℝ E) s := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  set n := finrank ℝ E with hn_def
  set ψ₁ : ℝ → ℝ := fun s ↦ (2 * (1 : ℝ) / ((1 : ℝ) ^ 2 + s ^ 2)) ^ n
  have h₁' : IntegrableOn (fun s ↦ s ^ (n - 1) * ψ₁ s) (Ioi 0) := by
    have h := integrable_bubble_rpow_criticalExponent (E := E) volume (by omega) hn.ne' one_pos 0
    simp_rw [bubble_rpow_criticalExponent hn.ne' one_pos, sub_zero] at h
    exact ((integrable_fun_norm_addHaar volume (f := ψ₁)).mp h).congr_fun
      (fun s _ ↦ by simp [ψ₁, smul_eq_mul, ← hn_def]) measurableSet_Ioi
  have h₁ : IntegrableOn (bubbleRadialWeight n) (Ioi 0) :=
    h₁'.congr_fun (fun s _ ↦ by simp [bubbleRadialWeight, ψ₁]) measurableSet_Ioi
  set C : ℝ := (((n : ℝ) - 2) / (2 * 1)) ^ 2
  have hC0 : C ≠ 0 := by
    have : (n : ℝ) - 2 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hn.ne')
    positivity
  have h₂'' : IntegrableOn (fun s : ℝ ↦ C * (s ^ (n - 1) * (s ^ 2 * ψ₁ s))) (Ioi 0) := by
    have h := integrable_norm_fderiv_bubble_sq (E := E) volume hn one_pos 0
    simp_rw [norm_fderiv_bubble_sq one_pos, sub_zero, mul_assoc] at h
    refine ((integrable_fun_norm_addHaar volume (f := fun s ↦ C * (s ^ 2 * ψ₁ s))).mp h).congr_fun
      (fun s _ ↦ ?_) measurableSet_Ioi
    simp only [smul_eq_mul, ← hn_def]; ring
  have h₂' : IntegrableOn (fun s : ℝ ↦ s ^ (n - 1) * (s ^ 2 * ψ₁ s)) (Ioi 0) := by
    have h : IntegrableOn (fun s : ℝ ↦ C⁻¹ * (C * (s ^ (n - 1) * (s ^ 2 * ψ₁ s)))) (Ioi 0) :=
      h₂''.const_mul C⁻¹
    exact h.congr_fun (fun s _ ↦ inv_mul_cancel_left₀ hC0 _) measurableSet_Ioi
  have h₂ : IntegrableOn (fun s ↦ s ^ 2 * bubbleRadialWeight n s) (Ioi 0) :=
    h₂'.congr_fun (fun s _ ↦ by simp only [bubbleRadialWeight, ψ₁, mul_one, one_pow]; ring)
      measurableSet_Ioi
  have hval : (n : ℝ) * (volume.real (ball (0 : E) 1) *
      ∫ s in Ioi (0 : ℝ), bubbleRadialWeight n s) = roundSphereVolume n := by
    have h := integral_bubble_rpow_criticalExponent_eq_roundSphereVolume
      (E := E) (by omega) hn.ne' one_pos 0
    simp_rw [bubble_rpow_criticalExponent hn.ne' one_pos, sub_zero] at h
    rw [integral_fun_norm_addHaar volume ψ₁] at h
    have hint₁ : (∫ s in Ioi (0 : ℝ), s ^ (finrank ℝ E - 1) • ψ₁ s) =
        ∫ s in Ioi (0 : ℝ), bubbleRadialWeight n s :=
      setIntegral_congr_fun measurableSet_Ioi fun s _ ↦ by
        simp [bubbleRadialWeight, ψ₁, smul_eq_mul, ← hn_def]
    rw [hint₁] at h
    simpa only [nsmul_eq_mul, smul_eq_mul, mul_assoc, ← hn_def] using h
  have hball := volume_real_ball_pos (E := E) one_pos
  have hpos : 0 < ∫ s in Ioi (0 : ℝ), bubbleRadialWeight n s := by
    by_contra! hle
    have hle0 : (n : ℝ) * (volume.real (ball (0 : E) 1) *
        ∫ s in Ioi (0 : ℝ), bubbleRadialWeight n s) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity)
        (mul_nonpos_of_nonneg_of_nonpos hball.le hle)
    linarith [hval ▸ roundSphereVolume_pos n]
  have hmom := sub_two_mul_integral_radial (t := 1) hn h₁' h₂'
  have hint_lhs : (∫ s in Ioi (0 : ℝ), s ^ (n - 1) * (s ^ 2 * ψ₁ s)) =
      ∫ s in Ioi (0 : ℝ), s ^ 2 * bubbleRadialWeight n s :=
    setIntegral_congr_fun measurableSet_Ioi fun s _ ↦ by
      simp only [bubbleRadialWeight, ψ₁, mul_one, one_pow]; ring
  have hint_rhs : (∫ s in Ioi (0 : ℝ), s ^ (n - 1) * ψ₁ s) =
      ∫ s in Ioi (0 : ℝ), bubbleRadialWeight n s :=
    setIntegral_congr_fun measurableSet_Ioi fun s _ ↦ by simp [bubbleRadialWeight, ψ₁]
  rw [hint_lhs, hint_rhs, one_pow, mul_one] at hmom
  exact ⟨h₁, h₂, hval, hpos, hmom⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- For a radial function `v : E → ℝ` and a unit vector `e₀`, the radial derivative along `e₀` is
bounded at every positive radius by `‖fderiv ℝ v (r • e₀)‖`. -/
private theorem deriv_radial_sq_le {v : E → ℝ} (hv_rad : ∀ x y, ‖x‖ = ‖y‖ → v x = v y)
    {e₀ : E} (he₀ : ‖e₀‖ = 1) {r : ℝ} (hr : 0 < r) :
    (deriv (fun s : ℝ ↦ v (s • e₀)) r) ^ 2 ≤ ‖fderiv ℝ v (r • e₀)‖ ^ 2 := by
  let g : ℝ → ℝ := fun s ↦ v (s • e₀)
  by_cases hg : DifferentiableAt ℝ g r
  · have hre₀_ne : r • e₀ ≠ 0 := fun h0 ↦ by
      have := congrArg norm h0
      simp [norm_smul, abs_of_pos hr, he₀, hr.ne'] at this
    have hv_eq : v = g ∘ norm := funext fun x ↦ hv_rad x (‖x‖ • e₀) (by simp [norm_smul, he₀])
    have hnorm_r : ‖r • e₀‖ = r := by simp [norm_smul, abs_of_pos hr, he₀]
    have hv_diff : DifferentiableAt ℝ v (r • e₀) := by
      rw [hv_eq]
      exact (hnorm_r ▸ hg).comp (r • e₀) (differentiableAt_id.norm ℝ hre₀_ne)
    have hray : HasDerivAt (fun s : ℝ ↦ s • e₀) e₀ r := by
      simpa only [id_eq, one_smul] using (hasDerivAt_id r).smul_const e₀
    have hg_deriv : HasDerivAt g (fderiv ℝ v (r • e₀) e₀) r :=
      hv_diff.hasFDerivAt.comp_hasDerivAt r hray
    rw [hg_deriv.deriv]
    refine sq_le_sq.mpr ?_
    rw [abs_of_nonneg (norm_nonneg _), ← Real.norm_eq_abs]
    simpa only [he₀, mul_one] using (fderiv ℝ v (r • e₀)).le_opNorm e₀
  · rw [deriv_zero_of_not_differentiableAt hg]
    simp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Orthogonal reflection equates `‖fderiv ℝ v‖` across points of equal norm. -/
private theorem norm_fderiv_eq_of_norm_eq {v : E → ℝ} (hv_rad : ∀ x y, ‖x‖ = ‖y‖ → v x = v y)
    {x y : E} (hxy : ‖x‖ = ‖y‖) : ‖fderiv ℝ v x‖ = ‖fderiv ℝ v y‖ := by
  let R := (ℝ ∙ (x - y))ᗮ.reflection
  have hcomp : v ∘ R = v := funext fun z ↦ hv_rad (R z) z (R.norm_map z)
  have h := R.norm_iteratedFDeriv_comp_right v x 1
  rwa [hcomp, Submodule.reflection_sub hxy, norm_iteratedFDeriv_one, norm_iteratedFDeriv_one] at h

/-- Squared gradient integrability for a compactly supported Lipschitz function. -/
private theorem integrable_norm_fderiv_sq_of_lipschitzWith {K : ℝ≥0} {u : E → ℝ}
    (hu : LipschitzWith K u) (hsupp : HasCompactSupport u) :
    Integrable (fun x ↦ ‖fderiv ℝ u x‖ ^ 2) volume := by
  have hdom : Integrable ((tsupport u).indicator fun _ : E ↦ (K : ℝ) ^ 2) volume :=
    (integrableOn_const hsupp.measure_lt_top.ne).integrable_indicator
      hsupp.isCompact.isClosed.measurableSet
  refine hdom.mono' (((measurable_fderiv ℝ u).norm.pow_const 2).aestronglyMeasurable)
    (Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  by_cases hx : x ∈ tsupport u
  · rw [indicator_of_mem hx]
    refine sq_le_sq.mpr ?_
    simpa only [abs_of_nonneg (norm_nonneg _), abs_of_nonneg K.coe_nonneg] using
      norm_fderiv_le_of_lipschitz ℝ hu
  · simp [indicator_of_notMem hx, (notMem_tsupport_iff_eventuallyEq.mp hx).fderiv_eq]

/-- Polar-coordinate upper bound comparing the 1D radial derivative integral of `f(r) = c v(r • e₀)`
with `∫ ‖fderiv ℝ v x‖ ^ 2`. -/
private theorem integral_radial_deriv_sq_le [Nontrivial E] {K : ℝ≥0} {v : E → ℝ}
    (hv_lip : LipschitzWith K v) (hv_supp : HasCompactSupport v)
    (hv_rad : ∀ x y, ‖x‖ = ‖y‖ → v x = v y) {e₀ : E} (he₀ : ‖e₀‖ = 1) {c : ℝ} (hc : 0 ≤ c) :
    (finrank ℝ E : ℝ) * (volume.real (ball (0 : E) 1) *
        ∫ r in Ioi (0 : ℝ), r ^ (finrank ℝ E - 1) *
          (deriv (fun r ↦ c * v (max r 0 • e₀)) r) ^ 2) ≤
      c ^ 2 * ∫ x, ‖fderiv ℝ v x‖ ^ 2 := by
  set n := finrank ℝ E with hn_def
  let f : ℝ → ℝ := fun r ↦ c * v (max r 0 • e₀)
  let φ : ℝ → ℝ := fun r ↦ ‖fderiv ℝ v (max r 0 • e₀)‖ ^ 2
  have hv_grad_int := integrable_norm_fderiv_sq_of_lipschitzWith hv_lip hv_supp
  have hv_grad_eq : (fun x : E ↦ ‖fderiv ℝ v x‖ ^ 2) = fun x ↦ φ ‖x‖ := funext fun x ↦ by
    simp only [φ, max_eq_left (norm_nonneg x)]
    have hnorm : ‖x‖ = ‖‖x‖ • e₀‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_norm, he₀, mul_one]
    rw [norm_fderiv_eq_of_norm_eq hv_rad hnorm]
  have hφ_int : IntegrableOn (fun r ↦ r ^ (n - 1) * ‖fderiv ℝ v (r • e₀)‖ ^ 2) (Ioi 0) := by
    rw [hv_grad_eq] at hv_grad_int
    exact ((integrable_fun_norm_addHaar volume (f := φ)).mp hv_grad_int).congr_fun
      (fun r (hr : 0 < r) ↦ by simp [φ, max_eq_left hr.le, smul_eq_mul, ← hn_def])
      measurableSet_Ioi
  have hpt : ∀ r ∈ Ioi (0 : ℝ), r ^ (n - 1) * (deriv f r) ^ 2 ≤
      c ^ 2 * (r ^ (n - 1) * ‖fderiv ℝ v (r • e₀)‖ ^ 2) := fun r (hr : 0 < r) ↦ by
    have hev : f =ᶠ[𝓝 r] fun s ↦ c * v (s • e₀) := by
      filter_upwards [Ioi_mem_nhds hr] with s hs
      simp [f, max_eq_left hs.le]
    rw [hev.deriv_eq, deriv_const_mul_field, mul_pow]
    calc r ^ (n - 1) * (c ^ 2 * deriv (fun s ↦ v (s • e₀)) r ^ 2)
        = c ^ 2 * (r ^ (n - 1) * deriv (fun s ↦ v (s • e₀)) r ^ 2) := by ring
      _ ≤ c ^ 2 * (r ^ (n - 1) * ‖fderiv ℝ v (r • e₀)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (deriv_radial_sq_le hv_rad he₀ hr) (pow_nonneg hr.le _))
            (sq_nonneg c)
  have hderiv_f_int : IntegrableOn (fun r ↦ r ^ (n - 1) * (deriv f r) ^ 2) (Ioi 0) := by
    refine (hφ_int.const_mul (c ^ 2)).mono'
      (((continuous_pow (n - 1)).measurable.mul
        ((measurable_deriv f).pow_const 2)).aestronglyMeasurable.restrict) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun r (hr : r ∈ Ioi (0 : ℝ)) ↦ ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (mem_Ioi.1 hr).le _) (sq_nonneg _))]
    exact hpt r hr
  have hrad_le : ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * (deriv f r) ^ 2 ≤
      c ^ 2 * ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * ‖fderiv ℝ v (r • e₀)‖ ^ 2 := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on hderiv_f_int (hφ_int.const_mul (c ^ 2)) measurableSet_Ioi hpt
  have hgrad_polar : (n : ℝ) * (volume.real (ball (0 : E) 1) *
      ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * ‖fderiv ℝ v (r • e₀)‖ ^ 2) =
      ∫ x, ‖fderiv ℝ v x‖ ^ 2 := by
    rw [hv_grad_eq, integral_fun_norm_addHaar volume φ]
    simp only [nsmul_eq_mul, smul_eq_mul, ← hn_def]
    congr 2
    exact setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) ↦ by
      simp [φ, max_eq_left hr.le]
  have := hc
  calc (n : ℝ) * (volume.real (ball (0 : E) 1) * ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * (deriv f r) ^ 2)
      ≤ (n : ℝ) * (volume.real (ball (0 : E) 1) *
          (c ^ 2 * ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * ‖fderiv ℝ v (r • e₀)‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrad_le measureReal_nonneg)
          (Nat.cast_nonneg n)
    _ = c ^ 2 * ((n : ℝ) * (volume.real (ball (0 : E) 1) *
          ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * ‖fderiv ℝ v (r • e₀)‖ ^ 2)) := by ring
    _ = c ^ 2 * ∫ x, ‖fderiv ℝ v x‖ ^ 2 := by rw [hgrad_polar]

/-- Sharp Sobolev inequality for a nonnegative radially antitone compactly supported Lipschitz
function on `E`. -/
private theorem radial_sharp_sobolev (hn : 2 < finrank ℝ E) {K : ℝ≥0} {v : E → ℝ}
    (hv_lip : LipschitzWith K v) (hv_nonneg : ∀ x, 0 ≤ v x)
    (hv_anti : ∀ x y, ‖x‖ ≤ ‖y‖ → v y ≤ v x) {R : ℝ} (hR : 0 < R)
    (hvR : ∀ x, R ≤ ‖x‖ → v x = 0) :
    sphereYamabeConstant (finrank ℝ E) *
        (∫ x, v x ^ criticalExponent (finrank ℝ E)) ^ (2 / criticalExponent (finrank ℝ E)) ≤
      conformalCoefficient (finrank ℝ E) * ∫ x, ‖fderiv ℝ v x‖ ^ 2 := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  set n := finrank ℝ E with hn_def
  set pₙ := criticalExponent n
  have hpₙ : 0 < pₙ := criticalExponent_pos hn
  have hv_supp : HasCompactSupport v :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E) R) fun x hx ↦
      mem_closedBall_zero_iff.2 (not_lt.1 fun hlt ↦ hx (hvR x hlt.le))
  set M := ∫ x, v x ^ pₙ
  have hM_nonneg : 0 ≤ M := integral_nonneg fun x ↦ Real.rpow_nonneg (hv_nonneg x) _
  rcases eq_or_lt_of_le hM_nonneg with hM0 | hM_pos
  · rw [← hM0, Real.zero_rpow (div_pos zero_lt_two hpₙ).ne', mul_zero]
    exact mul_nonneg (conformalCoefficient_pos hn).le (integral_nonneg fun _ ↦ sq_nonneg _)
  obtain ⟨e₀, he₀⟩ := exists_norm_eq (E := E) zero_le_one
  have hv_rad : ∀ x y, ‖x‖ = ‖y‖ → v x = v y := fun x y h ↦
    le_antisymm (hv_anti y x h.ge) (hv_anti x y h.le)
  obtain ⟨hw₁, hw₂, hI₀_val, hI₀_pos, hmom⟩ := bubbleRadialWeight_integrals (E := E) hn
  set I₀ := ∫ s in Ioi (0 : ℝ), bubbleRadialWeight n s
  have hball := volume_real_ball_pos (E := E) one_pos
  set c := (roundSphereVolume n / M) ^ (1 / pₙ)
  have hc0 : 0 ≤ roundSphereVolume n / M := div_nonneg (roundSphereVolume_pos n).le hM_pos.le
  have hc : 0 < c := Real.rpow_pos_of_pos (div_pos (roundSphereVolume_pos n) hM_pos) _
  let f : ℝ → ℝ := fun r ↦ c * v (max r 0 • e₀)
  have hf_lip : LipschitzWith (c.toNNReal * K) f := LipschitzWith.of_dist_le_mul fun r₁ r₂ ↦ by
    simp only [f, Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hc, NNReal.coe_mul,
      Real.coe_toNNReal c hc.le, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hc.le
    have hmax := (LipschitzWith.id.max (LipschitzWith.const 0)).dist_le_mul r₁ r₂
    simp only [id_eq, max_eq_left zero_le_one, NNReal.coe_one, one_mul, Real.dist_eq] at hmax
    exact ((Real.dist_eq _ _).symm.trans_le (hv_lip.dist_le_mul _ _)).trans
      (by rw [dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs, he₀, mul_one]; gcongr)
  have hf_anti : AntitoneOn f (Ici 0) := fun r₁ hr₁ r₂ hr₂ hle ↦
    mul_le_mul_of_nonneg_left (hv_anti _ _ (by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, he₀, mul_one, mul_one,
        max_eq_left hr₁, max_eq_left hr₂, abs_of_nonneg hr₁, abs_of_nonneg hr₂]
      exact hle)) hc.le
  have hfR : ∀ r ≥ R, f r = 0 := fun r hr ↦ by
    have hge : R ≤ ‖max r 0 • e₀‖ := by
      rw [norm_smul, Real.norm_eq_abs, he₀, mul_one, max_eq_left (hR.le.trans hr),
        abs_of_nonneg (hR.le.trans hr)]; exact hr
    simp [f, hvR _ hge]
  have hv_polar : M = (n : ℝ) * (volume.real (ball (0 : E) 1) *
      ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * v (r • e₀) ^ pₙ) := by
    have hv_eq : (fun x : E ↦ v x ^ pₙ) = fun x ↦ (fun r ↦ v (max r 0 • e₀) ^ pₙ) ‖x‖ :=
      funext fun x ↦ by
        dsimp only
        rw [max_eq_left (norm_nonneg x), hv_rad x (‖x‖ • e₀) (by simp [norm_smul, he₀])]
    dsimp only [M]
    rw [hv_eq, integral_fun_norm_addHaar volume (fun r ↦ v (max r 0 • e₀) ^ pₙ)]
    simp only [nsmul_eq_mul, smul_eq_mul, ← hn_def]
    congr 2
    exact setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) ↦ by rw [max_eq_left hr.le]
  have hnorm : ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * f r ^ pₙ = I₀ := by
    have hcp : c ^ pₙ = roundSphereVolume n / M := by
      rw [← Real.rpow_mul hc0, one_div_mul_cancel hpₙ.ne', Real.rpow_one]
    have hfun : ∀ r ∈ Ioi (0 : ℝ), r ^ (n - 1) * f r ^ pₙ =
        c ^ pₙ * (r ^ (n - 1) * v (r • e₀) ^ pₙ) := fun r (hr : 0 < r) ↦ by
      simp only [f, max_eq_left hr.le, Real.mul_rpow hc.le (hv_nonneg _)]; ring
    rw [setIntegral_congr_fun measurableSet_Ioi hfun, integral_const_mul, hcp]
    apply mul_left_cancel₀ (by positivity : (n : ℝ) * volume.real (ball (0 : E) 1) ≠ 0)
    calc (n : ℝ) * volume.real (ball (0 : E) 1) *
          (roundSphereVolume n / M * ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * v (r • e₀) ^ pₙ)
        = roundSphereVolume n / M * ((n : ℝ) * (volume.real (ball (0 : E) 1) *
            ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * v (r • e₀) ^ pₙ)) := by ring
      _ = roundSphereVolume n := by rw [← hv_polar, div_mul_cancel₀ _ hM_pos.ne']
      _ = (n : ℝ) * volume.real (ball (0 : E) 1) * I₀ := by rw [← hI₀_val, mul_assoc]
  have h1d := one_dim_sharp_sobolev_normalized hn hw₁ hw₂ hI₀_pos hmom hf_lip
    (fun r ↦ mul_nonneg hc.le (hv_nonneg _)) hf_anti hR hfR hnorm
  have hrad := integral_radial_deriv_sq_le hv_lip hv_supp hv_rad he₀ hc.le
  have hS_pos : 0 < roundSphereVolume n ^ (2 / pₙ) :=
    Real.rpow_pos_of_pos (roundSphereVolume_pos n) _
  have hM_rpow : 0 < M ^ (2 / pₙ) := Real.rpow_pos_of_pos hM_pos _
  have hc2 : c ^ 2 = roundSphereVolume n ^ (2 / pₙ) / M ^ (2 / pₙ) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hc0, one_div_mul_eq_div,
      Real.div_rpow (roundSphereVolume_pos n).le hM_pos.le]
  have hcomb : sphereYamabeConstant n * roundSphereVolume n ^ (2 / pₙ) ≤
      conformalCoefficient n * (roundSphereVolume n ^ (2 / pₙ) / M ^ (2 / pₙ)) *
        ∫ x, ‖fderiv ℝ v x‖ ^ 2 := by
    calc sphereYamabeConstant n * roundSphereVolume n ^ (2 / pₙ)
        = (n : ℝ) * ((n : ℝ) - 1) * roundSphereVolume n := by
          rw [two_div_criticalExponent, sphereYamabeConstant_mul_roundSphereVolume_rpow]
      _ = (n : ℝ) * volume.real (ball (0 : E) 1) * ((n : ℝ) * ((n : ℝ) - 1) * I₀) := by
          rw [← hI₀_val]; ring
      _ ≤ (n : ℝ) * volume.real (ball (0 : E) 1) *
            (conformalCoefficient n * ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * (deriv f r) ^ 2) :=
          mul_le_mul_of_nonneg_left h1d (by positivity)
      _ = conformalCoefficient n *
            ((n : ℝ) * (volume.real (ball (0 : E) 1) *
              ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * (deriv f r) ^ 2)) := by ring
      _ ≤ conformalCoefficient n * (c ^ 2 * ∫ x, ‖fderiv ℝ v x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hrad (conformalCoefficient_pos hn).le
      _ = conformalCoefficient n * (roundSphereVolume n ^ (2 / pₙ) / M ^ (2 / pₙ)) *
            ∫ x, ‖fderiv ℝ v x‖ ^ 2 := by rw [hc2]; ring
  have hmul2 := mul_le_mul_of_nonneg_left hcomb (div_pos hM_rpow hS_pos).le
  have h1 : M ^ (2 / pₙ) / roundSphereVolume n ^ (2 / pₙ) *
      (sphereYamabeConstant n * roundSphereVolume n ^ (2 / pₙ)) =
      sphereYamabeConstant n * M ^ (2 / pₙ) := by field_simp [hS_pos.ne']
  have h2 : M ^ (2 / pₙ) / roundSphereVolume n ^ (2 / pₙ) *
      (conformalCoefficient n * (roundSphereVolume n ^ (2 / pₙ) / M ^ (2 / pₙ)) *
        ∫ x, ‖fderiv ℝ v x‖ ^ 2) =
      conformalCoefficient n * ∫ x, ‖fderiv ℝ v x‖ ^ 2 := by
    field_simp [hS_pos.ne', hM_rpow.ne']
  rwa [h1, h2] at hmul2

/-- The Schwarz rearrangement of a function whose positive superlevel set has finite volume
vanishes outside a centered ball. -/
private theorem exists_radius_schwarzRearrangement_eq_zero [Nontrivial E] {u : E → ENNReal}
    (hfin0 : volume {y | 0 < u y} ≠ ⊤) :
    ∃ R > 0, ∀ x : E, R ≤ ‖x‖ → schwarzRearrangement volume u x = 0 := by
  have hball1 := volume_real_ball_pos (E := E) one_pos
  set R := max 1 ((volume {y | 0 < u y}).toReal / volume.real (ball (0 : E) 1) + 1)
  refine ⟨R, lt_of_lt_of_le one_pos (le_max_left _ _), fun x hx ↦ ?_⟩
  have hx1 : 1 ≤ ‖x‖ := (le_max_left _ _).trans hx
  have hx2 : (volume {y | 0 < u y}).toReal / volume.real (ball (0 : E) 1) + 1 ≤ ‖x‖ :=
    (le_max_right _ _).trans hx
  have hvol_lt : volume {y | 0 < u y} < volume (ball (0 : E) ‖x‖) := by
    have hpos_r : 0 < ‖x‖ ^ finrank ℝ E := pow_pos (one_pos.trans_le hx1) _
    rw [volume.addHaar_ball_of_pos 0 (one_pos.trans_le hx1),
      ← ENNReal.ofReal_toReal measure_ball_lt_top.ne, ← measureReal_def,
      ← ENNReal.ofReal_mul hpos_r.le, ← ENNReal.ofReal_toReal hfin0,
      ENNReal.ofReal_lt_ofReal_iff (mul_pos hpos_r hball1)]
    have hfinrank : 0 < finrank ℝ E := Module.finrank_pos
    have hpow : ‖x‖ ≤ ‖x‖ ^ finrank ℝ E := le_self_pow₀ hx1 hfinrank.ne'
    have hdiv : (volume {y | 0 < u y}).toReal < ‖x‖ * volume.real (ball (0 : E) 1) := by
      have := mul_le_mul_of_nonneg_right hx2 hball1.le
      rw [add_mul, div_mul_cancel₀ _ hball1.ne', one_mul] at this
      linarith
    exact hdiv.trans_le (mul_le_mul_of_nonneg_right hpow hball1.le)
  by_contra hne
  exact hvol_lt.not_gt ((lt_schwarzRearrangement_iff volume).mp (pos_iff_ne_zero.mpr hne))

/-- **The sharp Euclidean Sobolev inequality for compactly supported Lipschitz functions.**
In dimension `n > 2`, for Lebesgue measure,
`Y(Sⁿ) (∫ |u| ^ pₙ) ^ (2 / pₙ) ≤ aₙ ∫ ‖du‖²`. -/
theorem sphereYamabeConstant_mul_rpow_le_conformalCoefficient_mul_integral_of_lipschitzWith
    (hn : 2 < finrank ℝ E) {K : ℝ≥0} {u : E → ℝ} (hu : LipschitzWith K u)
    (hsupp : HasCompactSupport u) :
    sphereYamabeConstant (finrank ℝ E) *
        (∫ x, |u x| ^ criticalExponent (finrank ℝ E)) ^ (2 / criticalExponent (finrank ℝ E)) ≤
      conformalCoefficient (finrank ℝ E) * ∫ x, ‖fderiv ℝ u x‖ ^ 2 := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  set pₙ := criticalExponent (finrank ℝ E)
  have hpₙ : 0 < pₙ := criticalExponent_pos hn
  let u_enn : E → ENNReal := fun y ↦ ENNReal.ofReal ‖u y‖
  let v_enn : E → ENNReal := schwarzRearrangement volume u_enn
  let v : E → ℝ := fun z ↦ (v_enn z).toReal
  have hu_norm : LipschitzWith K (fun y ↦ ‖u y‖) := by
    simpa only [one_mul, Function.comp_def] using
      (lipschitzWith_one_norm : LipschitzWith 1 (norm : ℝ → ℝ)).comp hu
  have hv_lip : LipschitzWith K v := lipschitzWith_toReal_schwarzRearrangement volume hu_norm
  have hsub_supp : {y | 0 < u_enn y} ⊆ tsupport u := fun y hy ↦
    subset_tsupport u (mem_support.2 fun h0 ↦ by simp [u_enn, h0] at hy)
  have hfin0 : volume {y | 0 < u_enn y} ≠ ⊤ :=
    ((measure_mono hsub_supp).trans_lt hsupp.measure_lt_top).ne
  have hfin : ∀ t, 0 < t → volume {y | t < ‖u y‖} ≠ ⊤ := fun t ht ↦ by
    have hsub_t : {y | t < ‖u y‖} ⊆ tsupport u := fun y hy ↦
      hsub_supp (ENNReal.ofReal_pos.mpr (ht.trans hy))
    exact ((measure_mono hsub_t).trans_lt hsupp.measure_lt_top).ne
  have hv_ne_top : ∀ x, v_enn x ≠ ⊤ := by
    refine schwarzRearrangement_ne_top volume (K := K) (fun x y ↦ ?_) ENNReal.zero_ne_top hfin0
    calc ENNReal.ofReal ‖u x‖ ≤ ENNReal.ofReal (‖u y‖ + K * dist x y) :=
          ENNReal.ofReal_le_ofReal (hu_norm.le_add_mul x y)
      _ ≤ ENNReal.ofReal ‖u y‖ + K * edist x y := by
          rw [edist_dist, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul K.coe_nonneg]
          exact ENNReal.ofReal_add_le
  have hv_anti : ∀ x y, ‖x‖ ≤ ‖y‖ → v y ≤ v x := fun x y hxy ↦
    ENNReal.toReal_mono (hv_ne_top x) (schwarzRearrangement_le_of_norm_le volume u_enn hxy)
  obtain ⟨R, hR, hvR_enn⟩ := exists_radius_schwarzRearrangement_eq_zero hfin0
  have hvR : ∀ x, R ≤ ‖x‖ → v x = 0 := fun x hx ↦ by simp [v, v_enn, hvR_enn x hx]
  have hv_supp : HasCompactSupport v :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E) R) fun x hx ↦
      mem_closedBall_zero_iff.2 (not_lt.1 fun hlt ↦ hx (hvR x hlt.le))
  have hmass_eq : (∫ x, v x ^ pₙ) = ∫ x, |u x| ^ pₙ := by
    rw [← ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ Real.rpow_nonneg ENNReal.toReal_nonneg _),
      ← ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _)]
    congr 1
    rw [ofReal_integral_eq_lintegral_ofReal ((hv_lip.continuous.rpow_const fun _ ↦ .inr hpₙ.le
        ).integrable_of_hasCompactSupport (hv_supp.rpow_const hpₙ.ne'))
        (.of_forall fun _ ↦ Real.rpow_nonneg ENNReal.toReal_nonneg _),
      ofReal_integral_eq_lintegral_ofReal ((hu.continuous.abs.rpow_const fun _ ↦ .inr hpₙ.le
        ).integrable_of_hasCompactSupport (hsupp.abs.rpow_const hpₙ.ne'))
        (.of_forall fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _)]
    have h1 : (∫⁻ x, ENNReal.ofReal (v x ^ pₙ)) = ∫⁻ x, v_enn x ^ pₙ :=
      lintegral_congr fun x ↦ by
        rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hpₙ.le,
          ENNReal.ofReal_toReal (hv_ne_top x)]
    have h2 : (∫⁻ x, ENNReal.ofReal (|u x| ^ pₙ)) = ∫⁻ x, u_enn x ^ pₙ :=
      lintegral_congr fun x ↦ by
        dsimp only [u_enn]
        rw [← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hpₙ.le, ← Real.norm_eq_abs]
    rw [h1, h2]
    exact lintegral_rpow_schwarzRearrangement volume
      hu_norm.continuous.aemeasurable.ennreal_ofReal hpₙ
  have hps : ∫ x, ‖fderiv ℝ v x‖ ^ 2 ≤ ∫ x, ‖fderiv ℝ u x‖ ^ 2 := by
    simpa only [Real.rpow_two] using
      integral_norm_fderiv_toReal_schwarzRearrangement_norm_rpow_le hu hfin one_le_two
        (by simpa only [Real.rpow_two] using integrable_norm_fderiv_sq_of_lipschitzWith hu hsupp)
  rw [← hmass_eq]
  exact (radial_sharp_sobolev hn hv_lip (fun _ ↦ ENNReal.toReal_nonneg) hv_anti hR hvR).trans
    (mul_le_mul_of_nonneg_left hps (conformalCoefficient_pos hn).le)

/-- **The sharp Euclidean Sobolev inequality for compactly supported `C¹` functions.**
In dimension `n > 2`, for Lebesgue measure,
`Y(Sⁿ) (∫ |u| ^ pₙ) ^ (2 / pₙ) ≤ aₙ ∫ ‖du‖²`. -/
theorem sphereYamabeConstant_mul_rpow_le_conformalCoefficient_mul_integral
    (hn : 2 < finrank ℝ E) {u : E → ℝ} (hu : ContDiff ℝ 1 u) (hsupp : HasCompactSupport u) :
    sphereYamabeConstant (finrank ℝ E) *
        (∫ x, |u x| ^ criticalExponent (finrank ℝ E)) ^ (2 / criticalExponent (finrank ℝ E)) ≤
      conformalCoefficient (finrank ℝ E) * ∫ x, ‖fderiv ℝ u x‖ ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := hsupp.exists_bound_iteratedFDeriv_of_contDiff (n := 1) hu
  have hlip : LipschitzWith C.toNNReal u :=
    lipschitzWith_of_nnNorm_fderiv_le (hu.differentiable one_ne_zero) fun x ↦ by
      rw [← NNReal.coe_le_coe, coe_nnNorm, Real.coe_toNNReal C hC0, ← norm_iteratedFDeriv_one]
      exact hC 1 le_rfl x
  exact sphereYamabeConstant_mul_rpow_le_conformalCoefficient_mul_integral_of_lipschitzWith
    hn hlip hsupp

/-- Integration over `(⊤ : Opens E)` coincides with integration over `E`. -/
private theorem setIntegral_top_opens (F : E → ℝ) :
    (∫ x in (⊤ : Opens E), F x) = ∫ x, F x := by
  rw [Opens.coe_top, Measure.restrict_univ]

/-- **The sharp Euclidean Sobolev inequality on `D^{1,2}_0(E)`**, in norm form:
`Y(Sⁿ) ‖u‖_{pₙ}² ≤ aₙ ‖du‖₂²` for every `u ∈ D1p0 volume ⊤ 2` in dimension `n > 2`. -/
theorem sphereYamabeConstant_mul_norm_sobolevEmbeddingL_sq_le_conformalCoefficient_mul_norm_sq
    (hn : 2 < finrank ℝ E) (u : D1p0 volume (⊤ : Opens E) 2) :
    sphereYamabeConstant (finrank ℝ E) *
        ‖D1p0.sobolevEmbeddingL (inv_ofReal_criticalExponent_add_inv_eq_inv hn) u‖ ^ 2 ≤
      conformalCoefficient (finrank ℝ E) * ‖u‖ ^ 2 := by
  set hexp := inv_ofReal_criticalExponent_add_inv_eq_inv hn
  set pₙ := criticalExponent (finrank ℝ E)
  set pstar := ENNReal.ofReal pₙ
  have : Fact (1 ≤ pstar) := ⟨one_le_of_inv_add_eq_inv hexp⟩
  have hpₙ : 0 < pₙ := criticalExponent_pos hn
  have hpstar0 : pstar ≠ 0 := (ENNReal.ofReal_pos.mpr hpₙ).ne'
  have hpstar : pstar ≠ ⊤ := ENNReal.ofReal_ne_top
  refine (D1p0.denseRange_ofTestFunctionₗ (mu := volume) (Omega := (⊤ : Opens E))
    (p := 2)).induction_on u (isClosed_le
      (continuous_const.mul ((D1p0.sobolevEmbeddingL hexp).continuous.norm.pow 2))
      (continuous_const.mul (continuous_norm.pow 2))) fun φ ↦ ?_
  rw [D1p0.sobolevEmbeddingL_ofTestFunctionₗ hpstar hexp φ, D1p0.norm_ofTestFunctionₗ]
  have hnorm_u : ‖testFunctionLp (mu := volume) pstar φ‖ ^ 2 =
      (∫ x, |(φ : E → ℝ) x| ^ pₙ) ^ (2 / pₙ) := by
    have hLp := Lp.integral_norm_rpow_eq_norm_rpow hpstar0 hpstar
      (testFunctionLp (mu := volume) pstar φ)
    rw [ENNReal.toReal_ofReal hpₙ.le] at hLp
    have hint_eq : (∫ x in (⊤ : Opens E), ‖testFunctionLp (mu := volume) pstar φ x‖ ^ pₙ) =
        ∫ x, |(φ : E → ℝ) x| ^ pₙ := by
      have hae := testFunctionLp_apply_ae (mu := volume) pstar φ
      calc (∫ x in (⊤ : Opens E), ‖testFunctionLp (mu := volume) pstar φ x‖ ^ pₙ)
          = ∫ x in (⊤ : Opens E), |(φ : E → ℝ) x| ^ pₙ :=
            integral_congr_ae (hae.mono fun x hx ↦ by dsimp only; rw [hx, Real.norm_eq_abs])
        _ = ∫ x, |(φ : E → ℝ) x| ^ pₙ := setIntegral_top_opens _
    rw [hint_eq] at hLp
    calc ‖testFunctionLp (mu := volume) pstar φ‖ ^ 2
        = (‖testFunctionLp (mu := volume) pstar φ‖ ^ pₙ) ^ (2 / pₙ) := by
          rw [← Real.rpow_mul (norm_nonneg _), mul_div_cancel₀ _ hpₙ.ne', Real.rpow_two]
      _ = (∫ x, |(φ : E → ℝ) x| ^ pₙ) ^ (2 / pₙ) := by rw [← hLp]
  have hnorm_du : (eLpNorm (fderiv ℝ (φ : E → ℝ)) 2 volume).toReal ^ 2 =
      ∫ x, ‖fderiv ℝ (φ : E → ℝ) x‖ ^ 2 := by
    have hmem : MemLp (fderiv ℝ (φ : E → ℝ)) 2 volume :=
      (φ.contDiff.continuous_fderiv (by simp)).memLp_of_hasCompactSupport
        (φ.hasCompactSupport.fderiv ℝ)
    rw [hmem.eLpNorm_two_eq_ofReal_sqrt_integral,
      ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
      Real.sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _)]
  rw [hnorm_u, hnorm_du]
  exact sphereYamabeConstant_mul_rpow_le_conformalCoefficient_mul_integral hn
    (φ.contDiff.of_le (by simp)) φ.hasCompactSupport

/-- **The sharp Euclidean Sobolev inequality on `D^{1,2}_0(E)`**, in integral form. -/
theorem sphereYamabeConstant_mul_rpow_sobolevEmbeddingL_le_conformalCoefficient_mul_integral
    (hn : 2 < finrank ℝ E) (u : D1p0 volume (⊤ : Opens E) 2) :
    sphereYamabeConstant (finrank ℝ E) *
        (∫ x, |D1p0.sobolevEmbeddingL (inv_ofReal_criticalExponent_add_inv_eq_inv hn) u x| ^
            criticalExponent (finrank ℝ E)) ^ (2 / criticalExponent (finrank ℝ E)) ≤
      conformalCoefficient (finrank ℝ E) * ∫ x, ‖u.1 x‖ ^ 2 := by
  set hexp := inv_ofReal_criticalExponent_add_inv_eq_inv hn
  set pₙ := criticalExponent (finrank ℝ E)
  set pstar := ENNReal.ofReal pₙ
  have : Fact (1 ≤ pstar) := ⟨one_le_of_inv_add_eq_inv hexp⟩
  have hpₙ : 0 < pₙ := criticalExponent_pos hn
  have hLp := Lp.integral_norm_rpow_eq_norm_rpow (ENNReal.ofReal_pos.mpr hpₙ).ne'
    ENNReal.ofReal_ne_top (D1p0.sobolevEmbeddingL hexp u)
  rw [ENNReal.toReal_ofReal hpₙ.le, setIntegral_top_opens] at hLp
  simp_rw [Real.norm_eq_abs] at hLp
  have h1 : (∫ x, |D1p0.sobolevEmbeddingL hexp u x| ^ pₙ) ^ (2 / pₙ) =
      ‖D1p0.sobolevEmbeddingL hexp u‖ ^ 2 := by
    rw [hLp, ← Real.rpow_mul (norm_nonneg _), mul_div_cancel₀ _ hpₙ.ne', Real.rpow_two]
  have hsq := Lp.integral_norm_sq_eq_norm_sq u.1
  rw [setIntegral_top_opens, Submodule.norm_coe] at hsq
  rw [h1, hsq]
  exact sphereYamabeConstant_mul_norm_sobolevEmbeddingL_sq_le_conformalCoefficient_mul_norm_sq hn u

/-- **Sharpness on `D^{1,2}_0(E)`**: `Y(Sⁿ)` is the least value of the Euclidean Sobolev quotient
`aₙ ‖du‖₂² / ‖u‖_{pₙ}²` on nonzero elements of `D1p0 volume ⊤ 2`, attained by the Aubin–Talenti
bubbles. -/
theorem isLeast_image_conformalCoefficient_mul_norm_sq_div (hn : 2 < finrank ℝ E) :
    IsLeast
      ((fun u : D1p0 volume (⊤ : Opens E) 2 ↦
          conformalCoefficient (finrank ℝ E) * ‖u‖ ^ 2 /
            ‖D1p0.sobolevEmbeddingL (inv_ofReal_criticalExponent_add_inv_eq_inv hn) u‖ ^ 2) ''
        {u | u ≠ 0})
      (sphereYamabeConstant (finrank ℝ E)) := by
  set hexp := inv_ofReal_criticalExponent_add_inv_eq_inv hn
  set pₙ := criticalExponent (finrank ℝ E)
  have : Fact (1 ≤ ENNReal.ofReal pₙ) := ⟨one_le_of_inv_add_eq_inv hexp⟩
  have hpₙ : 0 < pₙ := criticalExponent_pos hn
  constructor
  · obtain ⟨u, hu_fun, hu_grad⟩ := exists_sobolevEmbeddingL_ae_eq_bubble volume hn one_pos (0 : E)
    have hu_norm_pow : ‖D1p0.sobolevEmbeddingL hexp u‖ ^ 2 =
        (∫ x, bubble 1 (0 : E) x ^ pₙ) ^ (2 / pₙ) := by
      have hLp := Lp.integral_norm_rpow_eq_norm_rpow (ENNReal.ofReal_pos.mpr hpₙ).ne'
        ENNReal.ofReal_ne_top (D1p0.sobolevEmbeddingL hexp u)
      rw [ENNReal.toReal_ofReal hpₙ.le, setIntegral_top_opens] at hLp
      have hint : (∫ x, ‖D1p0.sobolevEmbeddingL hexp u x‖ ^ pₙ) =
          ∫ x, bubble 1 (0 : E) x ^ pₙ :=
        integral_congr_ae (hu_fun.mono fun x hx ↦ by
          dsimp only; rw [hx, Real.norm_of_nonneg (bubble_pos one_pos 0 x).le])
      rw [hint] at hLp
      calc ‖D1p0.sobolevEmbeddingL hexp u‖ ^ 2
          = (‖D1p0.sobolevEmbeddingL hexp u‖ ^ pₙ) ^ (2 / pₙ) := by
            rw [← Real.rpow_mul (norm_nonneg _), mul_div_cancel₀ _ hpₙ.ne', Real.rpow_two]
        _ = (∫ x, bubble 1 (0 : E) x ^ pₙ) ^ (2 / pₙ) := by rw [← hLp]
    have hmass_pos : 0 < (∫ x, bubble 1 (0 : E) x ^ pₙ) ^ (2 / pₙ) := by
      rw [integral_bubble_rpow_criticalExponent_eq_roundSphereVolume (by omega) hn.ne' one_pos 0]
      exact Real.rpow_pos_of_pos (roundSphereVolume_pos _) _
    have hu_ne : u ≠ 0 := by
      rintro rfl
      simp [map_zero] at hu_norm_pow
      linarith
    have hu_grad_sq : ‖u‖ ^ 2 = ∫ x, ‖fderiv ℝ (bubble 1 (0 : E)) x‖ ^ 2 := by
      have hsq := Lp.integral_norm_sq_eq_norm_sq u.1
      rw [setIntegral_top_opens, Submodule.norm_coe] at hsq
      rw [← hsq]
      exact integral_congr_ae (hu_grad.mono fun x hx ↦ by
        dsimp only; rw [hx, norm_gradient_eq_norm_fderiv])
    refine ⟨u, hu_ne, ?_⟩
    dsimp only
    rw [hu_grad_sq, hu_norm_pow,
      conformalCoefficient_mul_integral_norm_fderiv_bubble_sq_eq_sphereYamabeConstant
        hn one_pos (0 : E), mul_div_cancel_right₀ _ hmass_pos.ne']
  · rintro _ ⟨u, hu_ne : u ≠ 0, rfl⟩
    have hemb_ne : D1p0.sobolevEmbeddingL hexp u ≠ 0 := fun h0 ↦
      hu_ne (D1p0.sobolevEmbeddingL_injective ENNReal.ofReal_ne_top hexp
        (h0.trans (map_zero _).symm))
    have hpos : 0 < ‖D1p0.sobolevEmbeddingL hexp u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hemb_ne)
    rw [le_div_iff₀ hpos]
    exact sphereYamabeConstant_mul_norm_sobolevEmbeddingL_sq_le_conformalCoefficient_mul_norm_sq
      hn u

/-- **Sharpness on `C_c^∞(E)`**: `Y(Sⁿ)` is the greatest lower bound of the Euclidean Sobolev
quotient on smooth compactly supported functions with positive critical mass. -/
theorem isGLB_image_conformalCoefficient_mul_integral_div (hn : 2 < finrank ℝ E) :
    IsGLB
      ((fun u : E → ℝ ↦
          conformalCoefficient (finrank ℝ E) * (∫ x, ‖fderiv ℝ u x‖ ^ 2) /
            (∫ x, |u x| ^ criticalExponent (finrank ℝ E)) ^
              (2 / criticalExponent (finrank ℝ E))) ''
        {u | ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
          0 < ∫ x, |u x| ^ criticalExponent (finrank ℝ E)})
      (sphereYamabeConstant (finrank ℝ E)) := by
  constructor
  · rintro _ ⟨u, ⟨hu_smooth, hu_supp, hu_pos⟩, rfl⟩
    have hrpow_pos : 0 < (∫ x, |u x| ^ criticalExponent (finrank ℝ E)) ^
        (2 / criticalExponent (finrank ℝ E)) := Real.rpow_pos_of_pos hu_pos _
    exact (le_div_iff₀ hrpow_pos).2
      (sphereYamabeConstant_mul_rpow_le_conformalCoefficient_mul_integral hn
        (hu_smooth.of_le (by simp)) hu_supp)
  · intro c hc
    by_contra! hlt
    obtain ⟨u, hu_smooth, hu_supp, _, _, hu_pos, hu_lt⟩ :=
      exists_contDiff_hasCompactSupport_sobolev_quotient_lt (E := E) hn isOpen_univ
        ⟨0, mem_univ 0⟩ (sub_pos.mpr hlt)
    linarith [hc ⟨u, ⟨hu_smooth, hu_supp, hu_pos⟩, rfl⟩]

end EuclideanSobolev

end TauCeti.Yamabe
