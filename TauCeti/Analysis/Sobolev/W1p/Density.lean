/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Mollification
public import TauCeti.Analysis.Sobolev.W1p.Multiplication
public import TauCeti.MeasureTheory.Function.Lp.MollificationBridge

/-!
# Test functions are dense in `W^{1,p}(ℝⁿ)`

For `1 ≤ p < ∞`, every function in the whole-space Sobolev space `W^{1,p}(ℝⁿ)` is a
`W^{1,p}`-limit of test functions:

`W^{1,p}_0(ℝⁿ) = W^{1,p}(ℝⁿ)`.

The ambient space is any finite-dimensional real inner product space `E` with an additive Haar
measure; `ℝⁿ` stands for the whole-space case `Ω = ⊤` below.  For a nonempty bounded domain in a
space of positive dimension the two spaces differ, since the Poincaré inequality excludes the
nonzero constants from `W^{1,p}_0(Ω)`; so the statement is genuinely about the whole space.

## Density of test functions

The mollification operator `TauCeti.W1p.normedBumpL` on `W^{1,p}(ℝⁿ)` converges to the identity
(`TauCeti.W1p.tendsto_normedBumpL`).  If the jet of `u` vanishes outside a compact set, its
mollification has a smooth compactly supported representative by
`TauCeti.normedBumpLp_ae_eq_convolution`, so it is a test function.  A general `u` is first
truncated by the rescaled bumps `ψ(x / R)`: the Leibniz rule of `TauCeti.W1p.contDiffSMul`
computes the truncated jet, which agrees with the jet of `u` on the ball of radius `R` and is
dominated by a fixed multiple of it, so the truncations converge to `u` by dominated convergence.
Closedness of `W^{1,p}_0(ℝⁿ)` then gives the theorem.

## Main declarations

* `TauCeti.W1p.mem_w1p0Submodule_top`: every `u ∈ W^{1,p}(ℝⁿ)` lies in `W^{1,p}_0(ℝⁿ)`.
* `TauCeti.w1p0Submodule_top_eq_top`: `W^{1,p}_0(ℝⁿ) = W^{1,p}(ℝⁿ)` for `p < ∞`.
* `TauCeti.W1p.denseRange_ofTestFunctionₗ_top`: test functions are dense in `W^{1,p}(ℝⁿ)`.

## References

L. C. Evans, *Partial Differential Equations*, §5.3.1; H. Brezis, *Functional Analysis, Sobolev
Spaces and Partial Differential Equations*, Theorem 9.2.
-/

public section

noncomputable section

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped Convolution Distributions ENNReal Gradient InnerProductSpace Topology

namespace TauCeti

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {p : ENNReal} [Fact (1 ≤ p)]

/-- The whole-space restriction of an additive Haar measure is the measure itself. -/
local instance : (mu.restrict ((⊤ : Opens E) : Set E)).IsAddHaarMeasure := by
  rw [Opens.coe_top, Measure.restrict_univ]
  infer_instance

/-! ### Compactly supported Sobolev functions -/

omit [MeasurableSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The Euclidean jet norm is at most the sum of the norms of its two components. -/
private theorem norm_sobolev1Jet_le (y : Sobolev1Jet E) : ‖y‖ ≤ ‖y.fst‖ + ‖y.snd‖ := by
  refine (sq_le_sq₀ (norm_nonneg y) (by positivity)).1 ?_
  rw [WithLp.prod_norm_sq_eq_of_L2]
  nlinarith [norm_nonneg y.fst, norm_nonneg y.snd]

/-- The mollification of a Sobolev function whose jet vanishes outside a compact set is a test
function. -/
private theorem normedBumpL_mem_range_of_ae_eq_zero (hp : p ≠ ∞) (phi : ContDiffBump (0 : E))
    {u : W1p mu ⊤ p} {K : Set E} (hK : IsCompact K)
    (hu : ∀ᵐ x ∂(mu.restrict ((⊤ : Opens E) : Set E)), x ∉ K →
      (u : Sobolev1JetLp mu ⊤ p) x = 0) :
    W1p.normedBumpL hp phi u ∈ LinearMap.range (W1p.ofTestFunctionₗ mu ⊤ p) := by
  set nu := mu.restrict ((⊤ : Opens E) : Set E)
  set J : Sobolev1JetLp mu ⊤ p := u.1 with hJdef
  let Jt : E → Sobolev1Jet E := K.indicator J
  have hJt_mem : MemLp Jt p nu := (Lp.memLp J).indicator hK.measurableSet
  have hJt_cpt : HasCompactSupport Jt :=
    HasCompactSupport.intro hK fun x hx => indicator_of_notMem hx _
  have hJ_eq : hJt_mem.toLp Jt = J := by
    apply Lp.ext
    filter_upwards [hJt_mem.coeFn_toLp, hu] with x hx hux
    rw [hx]
    by_cases hxK : x ∈ K
    · exact indicator_of_mem hxK _
    · simp only [Jt, indicator_of_notMem hxK, hux hxK]
  let conv : E → Sobolev1Jet E := phi.normed nu ⋆[ContinuousLinearMap.lsmul ℝ ℝ, nu] Jt
  have hbridge : ((W1p.normedBumpL hp phi u : W1p mu ⊤ p) : Sobolev1JetLp mu ⊤ p) =ᵐ[nu] conv := by
    rw [W1p.coe_normedBumpL, ← hJdef, ← hJ_eq]
    exact normedBumpLp_ae_eq_convolution hp phi hJt_mem hJt_cpt
  have hconv_smooth : ContDiff ℝ (⊤ : ℕ∞) conv :=
    phi.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      phi.contDiff_normed (hJt_mem.locallyIntegrable Fact.out)
  have hconv_cpt : HasCompactSupport conv :=
    phi.hasCompactSupport_normed.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hJt_cpt
  let Phi : 𝓓((⊤ : Opens E), ℝ) :=
    ⟨fun x => WithLp.fstL 2 ℝ ℝ E (conv x), (WithLp.fstL 2 ℝ ℝ E).contDiff.comp hconv_smooth,
      hconv_cpt.comp_left (map_zero _), subset_univ _⟩
  refine ⟨Phi, W1p.ext_value (Lp.ext ?_)⟩
  rw [W1p.value_ofTestFunctionₗ]
  filter_upwards [testFunctionLp_apply_ae (mu := mu) p Phi,
    W1p.value_apply_ae (W1p.normedBumpL hp phi u), hbridge] with x hPhi hvalue hconv
  rw [hPhi, hvalue, hconv]
  rfl

/-! ### Truncation -/

/-- The smooth bump equal to one on the unit ball and supported in the ball of radius two. -/
private def unitBump : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩

omit [MeasurableSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
private theorem unitBump_rIn : (unitBump (E := E)).rIn = 1 :=
  rfl

omit [MeasurableSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
private theorem unitBump_rOut : (unitBump (E := E)).rOut = 2 :=
  rfl

omit [MeasurableSpace E] [BorelSpace E] in
private theorem exists_norm_fderiv_unitBump_le :
    ∃ C, 0 ≤ C ∧ ∀ x, ‖fderiv ℝ (unitBump (E := E)) x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (((unitBump (E := E)).contDiff (n := 1)).continuous_fderiv
    one_ne_zero).norm.bddAbove_range_of_hasCompactSupport
      ((unitBump (E := E)).hasCompactSupport.fderiv ℝ).norm
  exact ⟨C, (norm_nonneg _).trans (hC ⟨0, rfl⟩), fun x => hC ⟨x, rfl⟩⟩

/-- The truncating cutoff `x ↦ ψ (x / (n + 1))`, equal to one on the ball of radius `n + 1`. -/
private def truncCutoff (n : ℕ) : E → ℝ :=
  fun x => unitBump (E := E) (((n : ℝ) + 1)⁻¹ • x)

omit [MeasurableSpace E] [BorelSpace E] in
private theorem contDiff_truncCutoff (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (truncCutoff (E := E) n) :=
  (unitBump (E := E)).contDiff.comp (contDiff_const_smul _)

omit [MeasurableSpace E] [BorelSpace E] in
private theorem truncCutoff_nonneg (n : ℕ) (x : E) : 0 ≤ truncCutoff n x :=
  (unitBump (E := E)).nonneg

omit [MeasurableSpace E] [BorelSpace E] in
private theorem truncCutoff_le_one (n : ℕ) (x : E) : truncCutoff n x ≤ 1 :=
  (unitBump (E := E)).le_one

omit [MeasurableSpace E] [BorelSpace E] in
private theorem norm_gradient_truncCutoff_le {C : ℝ}
    (hbound : ∀ x, ‖fderiv ℝ (unitBump (E := E)) x‖ ≤ C) (n : ℕ) (x : E) :
    ‖∇ (truncCutoff n) x‖ ≤ C := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [gradient, LinearIsometryEquiv.norm_map]
  unfold truncCutoff
  rw [fderiv_comp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hn)]
  calc ((n : ℝ) + 1)⁻¹ * ‖fderiv ℝ (unitBump (E := E)) (((n : ℝ) + 1)⁻¹ • x)‖
      ≤ 1 * C := mul_le_mul (inv_le_one_of_one_le₀ (by linarith)) (hbound _)
        (norm_nonneg _) zero_le_one
    _ = C := one_mul C

omit [MeasurableSpace E] [BorelSpace E] in
/-- Near a point of norm less than `n + 1`, the cutoff is identically one. -/
private theorem truncCutoff_eventuallyEq_one {n : ℕ} {x : E} (hx : ‖x‖ < (n : ℝ) + 1) :
    truncCutoff n =ᶠ[𝓝 x] fun _ => 1 := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hx)] with y hy
  apply (unitBump (E := E)).one_of_mem_closedBall
  rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hn),
    unitBump_rIn, inv_mul_le_iff₀ hn, mul_one]
  exact (mem_ball_zero_iff.1 hy).le

omit [MeasurableSpace E] [BorelSpace E] in
/-- Near a point of norm greater than `2 (n + 1)`, the cutoff is identically zero. -/
private theorem truncCutoff_eventuallyEq_zero {n : ℕ} {x : E}
    (hx : 2 * ((n : ℝ) + 1) < ‖x‖) :
    truncCutoff n =ᶠ[𝓝 x] fun _ => 0 := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  filter_upwards [isOpen_lt continuous_const continuous_norm |>.mem_nhds hx] with y hy
  apply (unitBump (E := E)).zero_of_le_dist
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hn), unitBump_rOut,
    le_inv_mul_iff₀ hn]
  linarith

/-- The truncation `ψ(x / (n + 1)) u` of a Sobolev function, with `C` bounding the gradients of
all the cutoffs. -/
private def truncate {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ n (x : E), ‖∇ (truncCutoff n) x‖ ≤ C)
    (n : ℕ) (u : W1p mu ⊤ p) : W1p mu ⊤ p :=
  W1p.contDiffSMul (truncCutoff n) (contDiff_truncCutoff n) (M := 1 + C) (by linarith)
    (fun x _ => by
      rw [abs_of_nonneg (truncCutoff_nonneg n x)]
      linarith [truncCutoff_le_one n x])
    (fun x _ => by linarith [hbound n x]) u

/-- The truncation `ψ(x / (n + 1)) u` vanishes outside the ball of radius `2 (n + 1)`. -/
private theorem truncate_ae_eq_zero {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n (x : E), ‖∇ (truncCutoff n) x‖ ≤ C) (n : ℕ) (u : W1p mu ⊤ p) :
    ∀ᵐ x ∂(mu.restrict ((⊤ : Opens E) : Set E)), x ∉ closedBall (0 : E) (2 * ((n : ℝ) + 1)) →
      (truncate hC hbound n u : Sobolev1JetLp mu ⊤ p) x = 0 := by
  filter_upwards [W1p.value_apply_ae (truncate hC hbound n u),
    W1p.gradient_apply_ae (truncate hC hbound n u),
    W1p.value_contDiffSMul_ae (p := p) _ _ _ _ u,
    W1p.gradient_contDiffSMul_ae (p := p) _ _ _ _ u] with x hv hg hvT hgT hx
  have hx' : 2 * ((n : ℝ) + 1) < ‖x‖ := by
    simpa only [mem_closedBall_zero_iff, not_le] using hx
  have hpsi := truncCutoff_eventuallyEq_zero hx'
  have hfst : ((truncate hC hbound n u : Sobolev1JetLp mu ⊤ p) x).fst = 0 := by
    rw [← hv, truncate, hvT, hpsi.eq_of_nhds, zero_smul]
  have hsnd : ((truncate hC hbound n u : Sobolev1JetLp mu ⊤ p) x).snd = 0 := by
    rw [← hg, truncate, hgT, hpsi.eq_of_nhds, hpsi.gradient_eq.trans (gradient_fun_const _ _),
      zero_smul, smul_zero, add_zero]
  exact (WithLp.ext_iff _).2 (Prod.ext hfst hsnd)

omit [MeasurableSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Dominated convergence in `Lᵖ`, in the form used for truncation: if `f n` agrees with `g`
eventually at almost every point and `‖f n - g‖` is dominated by a fixed multiple of `‖g‖`, then
`f n → g` in `Lᵖ`. -/
private theorem tendsto_eLpNorm_sub_of_eventually_eq {α F : Type*} [MeasurableSpace α]
    {m : Measure α} [NormedAddCommGroup F] {q : ℝ≥0∞} (hq0 : q ≠ 0) (hq : q ≠ ∞)
    {f : ℕ → α → F} {g : α → F} (hf : ∀ n, AEStronglyMeasurable (f n) m) (hg : MemLp g q m)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ n, ∀ᵐ x ∂m, ‖f n x - g x‖ ≤ C * ‖g x‖)
    (hlim : ∀ᵐ x ∂m, ∀ᶠ n in atTop, f n x = g x) :
    Tendsto (fun n => eLpNorm (f n - g) q m) atTop (𝓝 0) := by
  have hr : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hq]
  have hlint : Tendsto (fun n => ∫⁻ x, ‖(f n - g) x‖ₑ ^ q.toReal ∂m) atTop (𝓝 0) := by
    have hdom := tendsto_lintegral_filter_of_dominated_convergence' (μ := m)
      (F := fun n x => ‖(f n - g) x‖ₑ ^ q.toReal) (f := fun _ => 0)
      (fun x => (ENNReal.ofReal C * ‖g x‖ₑ) ^ q.toReal)
      (Eventually.of_forall fun n => ((hf n).sub hg.1).enorm.pow_const _)
      (Eventually.of_forall fun n => (hbound n).mono fun x hx => by
        refine ENNReal.rpow_le_rpow ?_ hr.le
        rw [Pi.sub_apply, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hC]
        exact ENNReal.ofReal_le_ofReal hx)
      (by
        simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hr.le]
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hr.le ENNReal.ofReal_ne_top)]
        exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hr.le ENNReal.ofReal_ne_top)
          (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hq0 hq hg.2).ne)
      (hlim.mono fun x hx => tendsto_const_nhds.congr' (hx.mono fun n hn => by
        simp [hn, ENNReal.zero_rpow_of_pos hr]))
    simpa only [lintegral_zero] using hdom
  have h0 : (0 : ℝ≥0∞) ^ (1 / q.toReal) = 0 := ENNReal.zero_rpow_of_pos (one_div_pos.2 hr)
  simpa only [h0] using hlint.ennrpow_const (1 / q.toReal)

/-- **The truncations converge.**  The truncated jet agrees with the jet of `u` on the ball of
radius `n + 1`, and differs from it by at most `(2 + C)` times its norm. -/
private theorem tendsto_truncate (hp : p ≠ ∞) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n (x : E), ‖∇ (truncCutoff n) x‖ ≤ C) (u : W1p mu ⊤ p) :
    Tendsto (fun n => truncate hC hbound n u) atTop (𝓝 u) := by
  rw [tendsto_subtype_rng, Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  have hv (n : ℕ) := W1p.value_contDiffSMul_ae (p := p) (mu := mu) (Omega := ⊤)
    (contDiff_truncCutoff n) (M := 1 + C) (by linarith)
    (fun x _ => by
      rw [abs_of_nonneg (truncCutoff_nonneg n x)]
      linarith [truncCutoff_le_one n x])
    (fun x _ => by linarith [hbound n x]) u
  have hg (n : ℕ) := W1p.gradient_contDiffSMul_ae (p := p) (mu := mu) (Omega := ⊤)
    (contDiff_truncCutoff n) (M := 1 + C) (by linarith)
    (fun x _ => by
      rw [abs_of_nonneg (truncCutoff_nonneg n x)]
      linarith [truncCutoff_le_one n x])
    (fun x _ => by linarith [hbound n x]) u
  refine tendsto_eLpNorm_sub_of_eventually_eq (zero_lt_one.trans_le Fact.out).ne' hp
    (fun n => Lp.aestronglyMeasurable _) (Lp.memLp _) (by linarith : (0 : ℝ) ≤ 2 + C)
    (fun n => ?_) ?_
  · filter_upwards [W1p.value_apply_ae (truncate hC hbound n u),
      W1p.gradient_apply_ae (truncate hC hbound n u), W1p.value_apply_ae u,
      W1p.gradient_apply_ae u, hv n, hg n] with x hvT hgT hvu hgu hvn hgn
    set a := W1p.value u x
    set G := W1p.gradient u x
    set s := truncCutoff n x
    have hs0 : 0 ≤ s := truncCutoff_nonneg n x
    have hs1 : s ≤ 1 := truncCutoff_le_one n x
    have hs : |s - 1| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
    have ha : ‖a‖ ≤ ‖(u : Sobolev1JetLp mu ⊤ p) x‖ :=
      hvu ▸ WithLp.norm_fst_le (x := (u : Sobolev1JetLp mu ⊤ p) x)
    have hG : ‖G‖ ≤ ‖(u : Sobolev1JetLp mu ⊤ p) x‖ :=
      hgu ▸ WithLp.norm_snd_le (x := (u : Sobolev1JetLp mu ⊤ p) x)
    have hfst : ((truncate hC hbound n u : Sobolev1JetLp mu ⊤ p) x -
        (u : Sobolev1JetLp mu ⊤ p) x).fst = (s - 1) • a := by
      rw [WithLp.sub_fst, ← hvT, ← hvu, truncate, hvn, sub_smul, one_smul]
    have hsnd : ((truncate hC hbound n u : Sobolev1JetLp mu ⊤ p) x -
        (u : Sobolev1JetLp mu ⊤ p) x).snd = (s - 1) • G + a • ∇ (truncCutoff n) x := by
      rw [WithLp.sub_snd, ← hgT, ← hgu, truncate, hgn, sub_smul, one_smul]
      abel
    refine (norm_sobolev1Jet_le _).trans ?_
    rw [hfst, hsnd]
    have h1 : ‖(s - 1) • a‖ ≤ ‖a‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) hs
    have h2 : ‖(s - 1) • G + a • ∇ (truncCutoff n) x‖ ≤ ‖G‖ + ‖a‖ * C := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) hs
      · rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hbound n x) (norm_nonneg _)
    nlinarith [norm_nonneg a, norm_nonneg G]
  · filter_upwards [ae_all_iff.2 fun n => W1p.value_apply_ae (truncate hC hbound n u),
      ae_all_iff.2 fun n => W1p.gradient_apply_ae (truncate hC hbound n u),
      W1p.value_apply_ae u, W1p.gradient_apply_ae u, ae_all_iff.2 hv, ae_all_iff.2 hg]
      with x hvT hgT hvu hgu hvn hgn
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_gt_atTop ‖x‖] with n hn
    have hpsi := truncCutoff_eventuallyEq_one (E := E) (n := n) (x := x) (by linarith)
    have hfst : ((truncate hC hbound n u : Sobolev1JetLp mu ⊤ p) x -
        (u : Sobolev1JetLp mu ⊤ p) x).fst = 0 := by
      rw [WithLp.sub_fst, ← hvT n, ← hvu, truncate, hvn n, hpsi.eq_of_nhds, one_smul, sub_self]
    have hsnd : ((truncate hC hbound n u : Sobolev1JetLp mu ⊤ p) x -
        (u : Sobolev1JetLp mu ⊤ p) x).snd = 0 := by
      rw [WithLp.sub_snd, ← hgT n, ← hgu, truncate, hgn n, hpsi.eq_of_nhds,
        hpsi.gradient_eq.trans (gradient_fun_const _ _), one_smul, smul_zero, add_zero, sub_self]
    exact sub_eq_zero.1 ((WithLp.ext_iff _).2 (Prod.ext hfst hsnd))

/-! ### Density -/

/-- **Every function in `W^{1,p}(ℝⁿ)` is a limit of test functions**, for `1 ≤ p < ∞`.  Truncate
by rescaled cutoffs, then mollify the compactly supported truncations. -/
theorem W1p.mem_w1p0Submodule_top (hp : p ≠ ∞) (u : W1p mu ⊤ p) :
    u ∈ w1p0Submodule mu ⊤ p := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_fderiv_unitBump_le (E := E)
  have hgrad := norm_gradient_truncCutoff_le hbound
  let phi : ℕ → ContDiffBump (0 : E) := fun k =>
    ⟨1 / ((k : ℝ) + 1) / 2, 1 / ((k : ℝ) + 1), by positivity, half_lt_self (by positivity)⟩
  have hphi : Tendsto (fun k => (phi k).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hclosed := (w1p0Submodule mu ⊤ p).isClosed
  have htrunc (n : ℕ) : truncate hC hgrad n u ∈ w1p0Submodule mu ⊤ p :=
    hclosed.mem_of_tendsto (W1p.tendsto_normedBumpL hp hphi _) (Eventually.of_forall fun k => by
      obtain ⟨Phi, hPhi⟩ := normedBumpL_mem_range_of_ae_eq_zero hp (phi k)
        (isCompact_closedBall (0 : E) (2 * ((n : ℝ) + 1))) (truncate_ae_eq_zero hC hgrad n u)
      rw [← hPhi]
      exact W1p.ofTestFunctionₗ_mem_w1p0Submodule Phi)
  exact hclosed.mem_of_tendsto (tendsto_truncate hp hC hgrad u) (Eventually.of_forall htrunc)

/-- **`W^{1,p}_0(ℝⁿ) = W^{1,p}(ℝⁿ)`** for `1 ≤ p < ∞`: on the whole space the zero-boundary
condition is no condition at all.  When `E` has positive dimension, the analogous equality fails
for a nonempty bounded domain, and it fails for `p = ∞`, where the constant `1` is not a limit
of test functions. -/
theorem w1p0Submodule_top_eq_top (hp : p ≠ ∞) : w1p0Submodule mu ⊤ p = ⊤ :=
  eq_top_iff.2 fun u _ => W1p.mem_w1p0Submodule_top hp u

/-- **Test functions are dense in `W^{1,p}(ℝⁿ)`** for `1 ≤ p < ∞`. -/
theorem W1p.denseRange_ofTestFunctionₗ_top (hp : p ≠ ∞) :
    DenseRange (W1p.ofTestFunctionₗ mu ⊤ p) := fun u => by
  rw [← coe_w1p0Submodule]
  exact W1p.mem_w1p0Submodule_top hp u

end TauCeti
