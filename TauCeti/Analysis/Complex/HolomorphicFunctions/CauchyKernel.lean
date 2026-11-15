/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.HolomorphicFunctions.Basic
public import TauCeti.Analysis.Contour.Cycle.Residue
import TauCeti.Analysis.Calculus.ContDiff.PiecewiseC1On.AbsolutelyContinuous
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Cauchy kernels and Riemann-sum approximation of holomorphic functions

For an open set `V : Opens ℂ` and a pole `w ∉ V`, `HolomorphicFunctions.cauchyKernel V w hw` is the
holomorphic function `z ↦ (w - z)⁻¹` on `V`, i.e. the inverse of `w - id` in
`holomorphicFunctions V`.

Given `f : holomorphicFunctions U` and a null-homologous cycle `Γ` in `U` avoiding `V` that winds
once around every point of `V`, partitioning the parameter intervals of the curves in the support of
`Γ` produces Riemann–Stieltjes sums `HolomorphicFunctions.cauchyIntegralRiemannSum f Γ V hdisj n`,
each an explicit `ℂ`-linear combination of Cauchy kernels with poles on `Cycle.trace Γ`, that
converge to `restrict hVU f` in the compact-open topology on `holomorphicFunctions V`. Any two
continuous algebra homomorphisms out of `holomorphicFunctions V` that agree on `id` therefore agree
on `restrict hVU f`, yielding uniqueness of the holomorphic functional calculus.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.4.
* W. Rudin, *Functional Analysis*, second edition, Theorem 10.27.
-/

public noncomputable section

open Complex Filter MeasureTheory Set Topology TopologicalSpace
open scoped Real Interval

namespace TauCeti.HolomorphicFunctions

variable {U V : Opens ℂ}

/-- The Cauchy kernel `z ↦ (w - z)⁻¹` on an open set `V` not containing `w`. -/
def cauchyKernel (V : Opens ℂ) (w : ℂ) (hw : w ∉ (V : Set ℂ)) : holomorphicFunctions V :=
  of V (fun z => (w - z)⁻¹)
    (((differentiableOn_const w).sub differentiableOn_id).inv fun z hz =>
      sub_ne_zero.mpr fun h : w = z => hw (h ▸ hz))

/-- Pointwise evaluation of `cauchyKernel V w hw` on `V`. -/
@[simp]
theorem cauchyKernel_apply (V : Opens ℂ) (w : ℂ) (hw : w ∉ (V : Set ℂ)) (z : V) :
    (cauchyKernel V w hw).val z = (w - z)⁻¹ := by
  rw [cauchyKernel, of_apply]

/-- Restricting a Cauchy kernel to a smaller open domain gives the Cauchy kernel there. -/
@[simp]
theorem restrict_cauchyKernel (hVU : V ≤ U) (w : ℂ) (hw : w ∉ (U : Set ℂ)) :
    restrict hVU (cauchyKernel U w hw) = cauchyKernel V w (fun h => hw (hVU h)) := by
  apply Subtype.ext
  ext z
  simp

/-- `(w - id) * (w - ·)⁻¹ = 1` in `holomorphicFunctions V` when `w ∉ V`. -/
theorem sub_id_mul_cauchyKernel (V : Opens ℂ) (w : ℂ) (hw : w ∉ (V : Set ℂ)) :
    (algebraMap ℂ (holomorphicFunctions V) w - of V id differentiableOn_id) *
      cauchyKernel V w hw = 1 := by
  apply Subtype.ext
  ext z
  have hne : w - (z : ℂ) ≠ 0 := sub_ne_zero.mpr fun h => hw (h ▸ z.property)
  simp [hne]

/-- `(w - ·)⁻¹ * (w - id) = 1` in `holomorphicFunctions V` when `w ∉ V`. -/
theorem cauchyKernel_mul_sub_id (V : Opens ℂ) (w : ℂ) (hw : w ∉ (V : Set ℂ)) :
    cauchyKernel V w hw *
      (algebraMap ℂ (holomorphicFunctions V) w - of V id differentiableOn_id) = 1 := by
  rw [mul_comm, sub_id_mul_cauchyKernel]

/-- For `w ∉ V`, `w - id` is a unit in `holomorphicFunctions V` with inverse
`cauchyKernel V w hw`. -/
theorem isUnit_sub_id_of_notMem (V : Opens ℂ) {w : ℂ} (hw : w ∉ (V : Set ℂ)) :
    IsUnit (algebraMap ℂ (holomorphicFunctions V) w - of V id differentiableOn_id) :=
  ⟨⟨_, cauchyKernel V w hw, sub_id_mul_cauchyKernel V w hw, cauchyKernel_mul_sub_id V w hw⟩, rfl⟩

private def curveNode (γ : Contour.PiecewiseC1ClosedCurve) (n j : ℕ) : ℝ :=
  γ.a + (j : ℝ) / (n + 1 : ℝ) * (γ.b - γ.a)

private theorem curveNode_zero (γ : Contour.PiecewiseC1ClosedCurve) (n : ℕ) :
    curveNode γ n 0 = γ.a := by
  simp [curveNode]

private theorem curveNode_last (γ : Contour.PiecewiseC1ClosedCurve) (n : ℕ) :
    curveNode γ n (n + 1) = γ.b := by
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  simp only [curveNode, Nat.cast_add, Nat.cast_one, div_self hn, one_mul, add_sub_cancel]

private theorem curveNode_mem_uIcc (γ : Contour.PiecewiseC1ClosedCurve) (n : ℕ) {j : ℕ}
    (hj : j ≤ n + 1) : curveNode γ n j ∈ uIcc γ.a γ.b := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have h0 : 0 ≤ (j : ℝ) / (n + 1 : ℝ) := by positivity
  have h1 : (j : ℝ) / (n + 1 : ℝ) ≤ 1 := (div_le_one hn).mpr (by exact_mod_cast hj)
  rcases le_total γ.a γ.b with hab | hba
  · rw [uIcc_of_le hab]
    exact ⟨by dsimp [curveNode]; nlinarith, by dsimp [curveNode]; nlinarith⟩
  · rw [uIcc_of_ge hba]
    exact ⟨by dsimp [curveNode]; nlinarith, by dsimp [curveNode]; nlinarith⟩

private theorem abs_curveNode_succ_sub (γ : Contour.PiecewiseC1ClosedCurve) (n j : ℕ) :
    |curveNode γ n (j + 1) - curveNode γ n j| = |γ.b - γ.a| / (n + 1 : ℝ) := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hsub : curveNode γ n (j + 1) - curveNode γ n j = (γ.b - γ.a) / (n + 1 : ℝ) := by
    dsimp [curveNode]
    push_cast
    ring
  rw [hsub, abs_div, abs_of_pos hn]

private def curveRiemannSum (g : ℂ → ℂ) (V : Opens ℂ) (γ : Contour.PiecewiseC1ClosedCurve)
    (hγV : ∀ t ∈ uIcc γ.a γ.b, γ t ∉ (V : Set ℂ)) (n : ℕ) : holomorphicFunctions V :=
  ∑ j : Fin (n + 1),
    ((γ (curveNode γ n (j.val + 1)) - γ (curveNode γ n j.val)) * g (γ (curveNode γ n j.val))) •
      cauchyKernel V (γ (curveNode γ n j.val))
        (hγV _ (curveNode_mem_uIcc γ n j.isLt.le))

private theorem curveRiemannSum_apply (g : ℂ → ℂ) (V : Opens ℂ)
    (γ : Contour.PiecewiseC1ClosedCurve) (hγV : ∀ t ∈ uIcc γ.a γ.b, γ t ∉ (V : Set ℂ))
    (n : ℕ) (z : V) :
    (curveRiemannSum g V γ hγV n).val z =
      ∑ j ∈ Finset.range (n + 1),
        (γ (curveNode γ n (j + 1)) - γ (curveNode γ n j)) *
          (g (γ (curveNode γ n j)) / (γ (curveNode γ n j) - z)) := by
  rw [← (holomorphicFunctions V).val_apply, curveRiemannSum, map_sum,
    ContinuousMap.sum_apply, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [div_eq_mul_inv, mul_assoc]

private theorem curveRiemannSum_sub_integral_eq (g : ℂ → ℂ)
    {γ : Contour.PiecewiseC1ClosedCurve} (hg : ContinuousOn g (γ '' uIcc γ.a γ.b))
    {z : ℂ} (hz : ∀ t ∈ uIcc γ.a γ.b, γ t ≠ z) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1),
      (γ (curveNode γ n (j + 1)) - γ (curveNode γ n j)) *
        (g (γ (curveNode γ n j)) / (γ (curveNode γ n j) - z))) -
      (∫ s in γ.a..γ.b, deriv γ s • (g (γ s) / (γ s - z))) =
      ∑ j ∈ Finset.range (n + 1),
        ∫ s in curveNode γ n j..curveNode γ n (j + 1),
          deriv γ s * (g (γ (curveNode γ n j)) / (γ (curveNode γ n j) - z) -
            g (γ s) / (γ s - z)) := by
  let φ : ℝ → ℂ := fun s => g (γ s) / (γ s - z)
  have hφ : ContinuousOn φ (uIcc γ.a γ.b) :=
    (hg.comp γ.continuousOn (mapsTo_image γ _)).div
      (γ.continuousOn.sub continuousOn_const) fun s hs => sub_ne_zero.mpr (hz s hs)
  have hint_sub {j : ℕ} (hj : j < n + 1) :
      uIcc (curveNode γ n j) (curveNode γ n (j + 1)) ⊆ uIcc γ.a γ.b :=
    uIcc_subset_uIcc (curveNode_mem_uIcc γ n hj.le) (curveNode_mem_uIcc γ n hj)
  have hint : ∀ j < n + 1,
      IntervalIntegrable (fun s => deriv γ s * φ s) volume
        (curveNode γ n j) (curveNode γ n (j + 1)) := fun j hj =>
    (γ.intervalIntegrable_deriv.mono_set (hint_sub hj)).mul_continuousOn (hφ.mono (hint_sub hj))
  have htot : (∫ s in γ.a..γ.b, deriv γ s • φ s) =
      ∑ j ∈ Finset.range (n + 1),
        ∫ s in curveNode γ n j..curveNode γ n (j + 1), deriv γ s * φ s := by
    simp only [smul_eq_mul]
    rw [intervalIntegral.sum_integral_adjacent_intervals hint, curveNode_zero, curveNode_last]
  rw [htot, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  have hsub := hint_sub hj'
  have hftc : ∫ s in curveNode γ n j..curveNode γ n (j + 1), deriv γ s =
      γ (curveNode γ n (j + 1)) - γ (curveNode γ n j) :=
    ((γ.isPiecewiseC1On.mono hsub).absolutelyContinuousOnInterval
      ).integral_deriv_eq_sub_of_finiteDimensional
  have hconst : (γ (curveNode γ n (j + 1)) - γ (curveNode γ n j)) * φ (curveNode γ n j) =
      ∫ s in curveNode γ n j..curveNode γ n (j + 1), deriv γ s * φ (curveNode γ n j) := by
    rw [intervalIntegral.integral_mul_const, hftc]
  rw [hconst, ← intervalIntegral.integral_sub
    ((γ.intervalIntegrable_deriv.mono_set hsub).mul_const _) (hint j hj')]
  exact intervalIntegral.integral_congr fun s _ => (mul_sub _ _ _).symm

private theorem curveNode_dist_le (γ : Contour.PiecewiseC1ClosedCurve) {n j : ℕ} {s δ : ℝ}
    (hs : s ∈ uIcc (curveNode γ n j) (curveNode γ n (j + 1)))
    (hstep : |γ.b - γ.a| / (n + 1 : ℝ) ≤ δ) :
    dist (curveNode γ n j) s ≤ δ :=
  (Real.dist_le_of_mem_uIcc left_mem_uIcc hs).trans
    ((Real.dist_eq _ _).trans_le
      ((abs_sub_comm _ _).le.trans ((abs_curveNode_succ_sub γ n j).le.trans hstep)))

private theorem tendstoUniformlyOn_curveRiemannSum {g : ℂ → ℂ} {γ : Contour.PiecewiseC1ClosedCurve}
    (hg : ContinuousOn g (γ '' uIcc γ.a γ.b)) (hγV : ∀ t ∈ uIcc γ.a γ.b, γ t ∉ (V : Set ℂ))
    {K : Set ℂ} (hKV : K ⊆ V) (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun n => extend (curveRiemannSum g V γ hγV n))
      (fun z => ∫ s in γ.a..γ.b, deriv γ s • (g (γ s) / (γ s - z))) atTop K := by
  -- Joint uniform continuity of `(t, z) ↦ g (γ t) / (γ t - z)` on `uIcc γ.a γ.b ×ˢ K`
  -- controls the oscillation across all `n + 1` subintervals uniformly in `z ∈ K`.
  let Φ : ℝ × ℂ → ℂ := fun p => g (γ p.1) / (γ p.1 - p.2)
  have hΦ : ContinuousOn Φ (uIcc γ.a γ.b ×ˢ K) :=
    (hg.comp (γ.continuousOn.comp continuousOn_fst fun _ hp => (mem_prod.mp hp).1)
      fun _ hp => mem_image_of_mem γ (mem_prod.mp hp).1).div
      ((γ.continuousOn.comp continuousOn_fst fun _ hp => (mem_prod.mp hp).1).sub continuousOn_snd)
      fun p hp => sub_ne_zero.mpr fun h =>
        hγV p.1 (mem_prod.mp hp).1 (h ▸ hKV (mem_prod.mp hp).2)
  have hunif := (isCompact_uIcc.prod hK).uniformContinuousOn_of_continuous hΦ
  obtain ⟨M, hMpos, hM⟩ := γ.isPiecewiseC1On.isBounded_image_deriv.exists_pos_norm_le
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let η : ℝ := ε / (M * (|γ.b - γ.a| + 1))
  obtain ⟨δ, hδpos, hδ⟩ :=
    Metric.uniformContinuousOn_iff_le.mp hunif η (div_pos hε (mul_pos hMpos (by positivity)))
  obtain ⟨N, hN⟩ := exists_nat_gt (|γ.b - γ.a| / δ)
  filter_upwards [eventually_ge_atTop N] with n hn z hzK
  have hzV : z ∈ V := hKV hzK
  have hstep : |γ.b - γ.a| / (n + 1 : ℝ) ≤ δ :=
    (div_le_iff₀ (by positivity : (0 : ℝ) < n + 1)).mpr
      (((div_lt_iff₀ hδpos).mp
        (hN.trans_le (by exact_mod_cast hn.trans n.le_succ : (N : ℝ) ≤ n + 1))).le.trans
        (by rw [mul_comm]))
  rw [extend_apply _ ⟨z, hzV⟩, curveRiemannSum_apply, dist_comm, dist_eq_norm,
    curveRiemannSum_sub_integral_eq g hg (fun t ht h => hγV t ht (h ▸ hzV)) n]
  calc ‖∑ j ∈ Finset.range (n + 1),
        ∫ s in curveNode γ n j..curveNode γ n (j + 1),
          deriv γ s * (Φ (curveNode γ n j, z) - Φ (s, z))‖
      ≤ ∑ _ ∈ Finset.range (n + 1), (M * η) * (|γ.b - γ.a| / (n + 1 : ℝ)) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
        have hj' := Finset.mem_range.mp hj
        rw [← abs_curveNode_succ_sub γ n j]
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => ?_
        have hs_mem : s ∈ uIcc (curveNode γ n j) (curveNode γ n (j + 1)) := uIoc_subset_uIcc hs
        have hsub : uIcc (curveNode γ n j) (curveNode γ n (j + 1)) ⊆ uIcc γ.a γ.b :=
          uIcc_subset_uIcc (curveNode_mem_uIcc γ n hj'.le) (curveNode_mem_uIcc γ n hj')
        have hdist : dist (curveNode γ n j, z) (s, z) ≤ δ := by
          rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
          exact curveNode_dist_le γ hs_mem hstep
        rw [norm_mul, ← dist_eq_norm]
        exact mul_le_mul (hM _ ⟨s, hsub hs_mem, rfl⟩)
          (hδ _ ⟨curveNode_mem_uIcc γ n hj'.le, hzK⟩ _ ⟨hsub hs_mem, hzK⟩ hdist)
          dist_nonneg hMpos.le
    _ = M * η * |γ.b - γ.a| := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
        push_cast
        field_simp
    _ < M * η * (|γ.b - γ.a| + 1) := by gcongr; linarith
    _ = ε := by dsimp [η]; field_simp

private theorem tendstoLocallyUniformlyOn_curveRiemannSum {g : ℂ → ℂ}
    {γ : Contour.PiecewiseC1ClosedCurve} (hg : ContinuousOn g (γ '' uIcc γ.a γ.b))
    (hγV : ∀ t ∈ uIcc γ.a γ.b, γ t ∉ (V : Set ℂ)) :
    TendstoLocallyUniformlyOn
      (fun n => extend (curveRiemannSum g V γ hγV n))
      (fun z => ∫ s in γ.a..γ.b, deriv γ s • (g (γ s) / (γ s - z))) atTop V :=
  (tendstoLocallyUniformlyOn_iff_forall_isCompact V.isOpen).mpr fun _ hKV hK =>
    tendstoUniformlyOn_curveRiemannSum hg hγV hKV hK

private def curveCauchyIntegral (g : ℂ → ℂ) (V : Opens ℂ) (γ : Contour.PiecewiseC1ClosedCurve)
    (hg : ContinuousOn g (γ '' uIcc γ.a γ.b))
    (hγV : ∀ t ∈ uIcc γ.a γ.b, γ t ∉ (V : Set ℂ)) : holomorphicFunctions V :=
  of V (fun z => ∫ s in γ.a..γ.b, deriv γ s • (g (γ s) / (γ s - z)))
    ((tendstoLocallyUniformlyOn_curveRiemannSum hg hγV).differentiableOn
      (Eventually.of_forall fun _ => differentiableOn_extend _) V.isOpen)

private theorem tendsto_curveRiemannSum {g : ℂ → ℂ} {γ : Contour.PiecewiseC1ClosedCurve}
    (hg : ContinuousOn g (γ '' uIcc γ.a γ.b))
    (hγV : ∀ t ∈ uIcc γ.a γ.b, γ t ∉ (V : Set ℂ)) :
    Tendsto (curveRiemannSum g V γ hγV) atTop (𝓝 (curveCauchyIntegral g V γ hg hγV)) := by
  rw [tendsto_iff_tendstoLocallyUniformlyOn]
  exact (tendstoLocallyUniformlyOn_curveRiemannSum hg hγV).congr_right fun z hz => by
    rw [extend_apply _ ⟨z, hz⟩, curveCauchyIntegral, of_apply]

/-- The `n`-th Riemann–Stieltjes sum of `(2πi)⁻¹ ∫_Γ extend f w / (w - ·) dw` in
`holomorphicFunctions V`, formed by partitioning each generator curve of `Γ` into `n + 1` equal
subintervals. Every term is a scalar multiple of a Cauchy kernel with pole on `Cycle.trace Γ`. -/
def cauchyIntegralRiemannSum (f : holomorphicFunctions U) (Γ : Contour.Cycle) (V : Opens ℂ)
    (hdisj : Disjoint (V : Set ℂ) (Contour.Cycle.trace Γ)) (n : ℕ) : holomorphicFunctions V :=
  (2 * π * I)⁻¹ • ∑ γ ∈ (FreeAbelianGroup.support Γ).attach,
    (FreeAbelianGroup.coeff γ.val Γ : ℂ) •
      curveRiemannSum (extend f) V γ.val
        (fun t ht hzV => disjoint_left.mp hdisj hzV
          (Contour.Cycle.mem_trace_iff.mpr ⟨γ.val, γ.property, t, ht, rfl⟩)) n

/-- Two `ℂ`-algebra homomorphisms out of `holomorphicFunctions V` that agree on every Cauchy kernel
with pole on `Cycle.trace Γ` agree on every `cauchyIntegralRiemannSum` along `Γ`. -/
theorem algHom_cauchyIntegralRiemannSum_eq {A : Type*} [Semiring A] [Algebra ℂ A]
    (Φ₁ Φ₂ : holomorphicFunctions V →ₐ[ℂ] A) (f : holomorphicFunctions U)
    (Γ : Contour.Cycle) (hdisj : Disjoint (V : Set ℂ) (Contour.Cycle.trace Γ))
    (hker : ∀ (w : ℂ) (hw : w ∈ Contour.Cycle.trace Γ),
      Φ₁ (cauchyKernel V w (disjoint_right.mp hdisj hw)) =
        Φ₂ (cauchyKernel V w (disjoint_right.mp hdisj hw)))
    (n : ℕ) :
    Φ₁ (cauchyIntegralRiemannSum f Γ V hdisj n) =
      Φ₂ (cauchyIntegralRiemannSum f Γ V hdisj n) := by
  rw [cauchyIntegralRiemannSum, map_smul, map_smul, map_sum, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [map_smul, map_smul]
  congr 1
  rw [curveRiemannSum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, map_smul]
  congr 1
  exact hker _ (Contour.Cycle.mem_trace_iff.mpr
    ⟨γ.val, γ.property, _, curveNode_mem_uIcc γ.val n j.isLt.le, rfl⟩)

/-- If `Γ` is a null-homologous cycle in `U` avoiding an open subset `V ≤ U` and winding once
around every point of `V`, the Riemann–Stieltjes sums `cauchyIntegralRiemannSum f Γ V hdisj n`
converge in `holomorphicFunctions V` to `restrict hVU f`. -/
theorem tendsto_cauchyIntegralRiemannSum (f : holomorphicFunctions U) {Γ : Contour.Cycle}
    (hVU : V ≤ U) (hΓ : Γ.IsIn U) (hn : Γ.IsNullHomologous U)
    (hdisj : Disjoint (V : Set ℂ) (Contour.Cycle.trace Γ))
    (hw : ∀ z ∈ (V : Set ℂ), Contour.Cycle.windingNumber z Γ = 1) :
    Tendsto (cauchyIntegralRiemannSum f Γ V hdisj) atTop (𝓝 (restrict hVU f)) := by
  let : LocallyCompactSpace V := V.isOpen.locallyCompactSpace
  have hcont_f (γ : FreeAbelianGroup.support Γ) :
      ContinuousOn (extend f) (γ.val '' uIcc γ.val.a γ.val.b) :=
    (differentiableOn_extend f).continuousOn.mono fun _ hz =>
      Contour.Cycle.isIn_iff.mp hΓ (Contour.Cycle.mem_trace_iff.mpr ⟨γ.val, γ.property, hz⟩)
  have hγV (γ : FreeAbelianGroup.support Γ) (t : ℝ) (ht : t ∈ uIcc γ.val.a γ.val.b) :
      γ.val t ∉ (V : Set ℂ) :=
    fun hzV => disjoint_left.mp hdisj hzV
      (Contour.Cycle.mem_trace_iff.mpr ⟨γ.val, γ.property, t, ht, rfl⟩)
  have hval_eq (n : ℕ) : (cauchyIntegralRiemannSum f Γ V hdisj n).val =
      (2 * π * I)⁻¹ • ∑ γ ∈ (FreeAbelianGroup.support Γ).attach,
        (FreeAbelianGroup.coeff γ.val Γ : ℂ) •
          (curveRiemannSum (extend f) V γ.val (hγV γ) n).val := by
    rw [← (holomorphicFunctions V).val_apply, cauchyIntegralRiemannSum, map_smul, map_sum]
    refine congrArg ((2 * π * I)⁻¹ • ·) (Finset.sum_congr rfl fun γ _ => ?_)
    rw [map_smul, (holomorphicFunctions V).val_apply]
  rw [tendsto_subtype_rng]
  simp only [hval_eq]
  have hsum : Tendsto
      (fun n => (2 * π * I)⁻¹ • ∑ γ ∈ (FreeAbelianGroup.support Γ).attach,
        (FreeAbelianGroup.coeff γ.val Γ : ℂ) •
          (curveRiemannSum (extend f) V γ.val (hγV γ) n).val)
      atTop
      (𝓝 ((2 * π * I)⁻¹ • ∑ γ ∈ (FreeAbelianGroup.support Γ).attach,
        (FreeAbelianGroup.coeff γ.val Γ : ℂ) •
          (curveCauchyIntegral (extend f) V γ.val (hcont_f γ) (hγV γ)).val)) :=
    (tendsto_finsetSum _ fun γ _ =>
      (tendsto_subtype_rng.mp (tendsto_curveRiemannSum (hcont_f γ) (hγV γ))).const_smul _
      ).const_smul _
  convert hsum using 2
  ext z
  have hz_notMem : (z : ℂ) ∉ Contour.Cycle.trace Γ := disjoint_left.mp hdisj z.property
  have hcauchy := Contour.Cycle.cauchyIntegralFormula_nullHomologous U.isOpen
    (differentiableOn_extend f) hΓ hn hz_notMem
  rw [Contour.Cycle.integral_eq_sum_support, ← Finset.sum_attach, hw z z.property, mul_one]
    at hcauchy
  simp only [ContinuousMap.smul_apply, ContinuousMap.sum_apply, smul_eq_mul]
  have hval : ∑ x ∈ (FreeAbelianGroup.support Γ).attach,
      (FreeAbelianGroup.coeff x.val Γ : ℂ) *
        (curveCauchyIntegral (extend f) V x.val (hcont_f x) (hγV x)).val z =
      2 * π * I * extend f z := by
    rw [← hcauchy]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [curveCauchyIntegral, of_apply, zsmul_eq_mul]
  rw [hval, inv_mul_cancel_left₀ two_pi_I_ne_zero, restrict_apply,
    extend_apply f ⟨(z : ℂ), hVU z.property⟩]

end TauCeti.HolomorphicFunctions
