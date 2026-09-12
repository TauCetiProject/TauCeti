/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Mollification
public import TauCeti.Analysis.Sobolev.W1p.Multiplication
import TauCeti.Analysis.Normed.Lp.ProdLp
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence

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
mollification is a test function (`TauCeti.W1p.normedBumpL_mem_range_of_ae_eq_zero`).  A general
`u` is first truncated by the rescaled bumps `ψ(x / R)`: the Leibniz rule of
`TauCeti.W1p.contDiffSMul` computes the truncated jet, which agrees with the jet of `u` on the
ball of radius `R` and is dominated by a fixed multiple of it, so the truncations converge to `u`
by dominated convergence.  Closedness of `W^{1,p}_0(ℝⁿ)` then gives the theorem.

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

open Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Gradient Topology

namespace TauCeti

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {p : ENNReal} [Fact (1 ≤ p)]

/-- The whole-space restriction of an additive Haar measure is the measure itself. -/
local instance : (mu.restrict ((⊤ : Opens E) : Set E)).IsAddHaarMeasure := by
  rw [Opens.coe_top, Measure.restrict_univ]
  infer_instance

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

/-- The value of the truncation is `ψ(x / (n + 1)) u`. -/
private theorem value_truncate_ae {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n (x : E), ‖∇ (truncCutoff n) x‖ ≤ C) (n : ℕ) (u : W1p mu ⊤ p) :
    ∀ᵐ x ∂(mu.restrict ((⊤ : Opens E) : Set E)),
      W1p.value (truncate hC hbound n u) x = truncCutoff n x • W1p.value u x := by
  rw [truncate]
  exact W1p.value_contDiffSMul_ae _ _ _ _ u

/-- The weak gradient of the truncation is `ψ(x / (n + 1)) ∇u + u ∇ψ(x / (n + 1))`. -/
private theorem gradient_truncate_ae {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n (x : E), ‖∇ (truncCutoff n) x‖ ≤ C) (n : ℕ) (u : W1p mu ⊤ p) :
    ∀ᵐ x ∂(mu.restrict ((⊤ : Opens E) : Set E)),
      W1p.gradient (truncate hC hbound n u) x
        = truncCutoff n x • W1p.gradient u x + W1p.value u x • ∇ (truncCutoff n) x := by
  rw [truncate]
  exact W1p.gradient_contDiffSMul_ae _ _ _ _ u

/-- The truncation `ψ(x / (n + 1)) u` vanishes outside the ball of radius `2 (n + 1)`. -/
private theorem truncate_ae_eq_zero {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n (x : E), ‖∇ (truncCutoff n) x‖ ≤ C) (n : ℕ) (u : W1p mu ⊤ p) :
    ∀ᵐ x ∂(mu.restrict ((⊤ : Opens E) : Set E)), x ∉ closedBall (0 : E) (2 * ((n : ℝ) + 1)) →
      (truncate hC hbound n u : Sobolev1JetLp mu ⊤ p) x = 0 := by
  filter_upwards [W1p.value_apply_ae (truncate hC hbound n u),
    W1p.gradient_apply_ae (truncate hC hbound n u), value_truncate_ae hC hbound n u,
    gradient_truncate_ae hC hbound n u] with x hv hg hvT hgT hx
  have hx' : 2 * ((n : ℝ) + 1) < ‖x‖ := by
    simpa only [mem_closedBall_zero_iff, not_le] using hx
  have hpsi := truncCutoff_eventuallyEq_zero hx'
  have hfst : ((truncate hC hbound n u : Sobolev1JetLp mu ⊤ p) x).fst = 0 := by
    rw [← hv, hvT, hpsi.eq_of_nhds, zero_smul]
  have hsnd : ((truncate hC hbound n u : Sobolev1JetLp mu ⊤ p) x).snd = 0 := by
    rw [← hg, hgT, hpsi.eq_of_nhds, hpsi.gradient_eq.trans (gradient_fun_const _ _),
      zero_smul, smul_zero, add_zero]
  exact (WithLp.ext_iff _).2 (Prod.ext hfst hsnd)

/-- The value of the truncation error `ψ(x / (n + 1)) u - u` is `(ψ(x / (n + 1)) - 1) u`. -/
private theorem fst_coe_truncate_sub_ae {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n (x : E), ‖∇ (truncCutoff n) x‖ ≤ C) (n : ℕ) (u : W1p mu ⊤ p) :
    ∀ᵐ x ∂(mu.restrict ((⊤ : Opens E) : Set E)),
      ((truncate hC hbound n u : Sobolev1JetLp mu ⊤ p) x - (u : Sobolev1JetLp mu ⊤ p) x).fst
        = (truncCutoff n x - 1) • W1p.value u x := by
  filter_upwards [W1p.value_apply_ae (truncate hC hbound n u), W1p.value_apply_ae u,
    value_truncate_ae hC hbound n u] with x hvT hvu hvn
  rw [WithLp.sub_fst, ← hvT, ← hvu, hvn, sub_smul, one_smul]

/-- The weak gradient of the truncation error `ψ(x / (n + 1)) u - u` is
`(ψ(x / (n + 1)) - 1) ∇u + u ∇ψ(x / (n + 1))`. -/
private theorem snd_coe_truncate_sub_ae {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n (x : E), ‖∇ (truncCutoff n) x‖ ≤ C) (n : ℕ) (u : W1p mu ⊤ p) :
    ∀ᵐ x ∂(mu.restrict ((⊤ : Opens E) : Set E)),
      ((truncate hC hbound n u : Sobolev1JetLp mu ⊤ p) x - (u : Sobolev1JetLp mu ⊤ p) x).snd
        = (truncCutoff n x - 1) • W1p.gradient u x + W1p.value u x • ∇ (truncCutoff n) x := by
  filter_upwards [W1p.gradient_apply_ae (truncate hC hbound n u), W1p.gradient_apply_ae u,
    gradient_truncate_ae hC hbound n u] with x hgT hgu hgn
  rw [WithLp.sub_snd, ← hgT, ← hgu, hgn, sub_smul, one_smul]
  abel

/-- The truncation error is at most `(2 + C)` times the jet of `u`, uniformly in `n`. -/
private theorem norm_coe_truncate_sub_le {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n (x : E), ‖∇ (truncCutoff n) x‖ ≤ C) (n : ℕ) (u : W1p mu ⊤ p) :
    ∀ᵐ x ∂(mu.restrict ((⊤ : Opens E) : Set E)),
      ‖(truncate hC hbound n u : Sobolev1JetLp mu ⊤ p) x - (u : Sobolev1JetLp mu ⊤ p) x‖
        ≤ (2 + C) * ‖(u : Sobolev1JetLp mu ⊤ p) x‖ := by
  filter_upwards [fst_coe_truncate_sub_ae hC hbound n u, snd_coe_truncate_sub_ae hC hbound n u,
    W1p.value_apply_ae u, W1p.gradient_apply_ae u] with x hfst hsnd hvu hgu
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
  refine (WithLp.prod_norm_le_norm_fst_add_norm_snd _).trans ?_
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

/-- At each point the truncations are eventually equal to `u`: the cutoff is one on the ball of
radius `n + 1`. -/
private theorem eventually_coe_truncate_eq {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n (x : E), ‖∇ (truncCutoff n) x‖ ≤ C) (u : W1p mu ⊤ p) :
    ∀ᵐ x ∂(mu.restrict ((⊤ : Opens E) : Set E)), ∀ᶠ n in atTop,
      (truncate hC hbound n u : Sobolev1JetLp mu ⊤ p) x = (u : Sobolev1JetLp mu ⊤ p) x := by
  filter_upwards [ae_all_iff.2 fun n => fst_coe_truncate_sub_ae hC hbound n u,
    ae_all_iff.2 fun n => snd_coe_truncate_sub_ae hC hbound n u] with x hfst hsnd
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_gt_atTop ‖x‖] with n hn
  have hpsi := truncCutoff_eventuallyEq_one (E := E) (n := n) (x := x) (by linarith)
  have hfst0 : ((truncate hC hbound n u : Sobolev1JetLp mu ⊤ p) x
      - (u : Sobolev1JetLp mu ⊤ p) x).fst = 0 := by
    rw [hfst n, hpsi.eq_of_nhds, sub_self, zero_smul]
  have hsnd0 : ((truncate hC hbound n u : Sobolev1JetLp mu ⊤ p) x
      - (u : Sobolev1JetLp mu ⊤ p) x).snd = 0 := by
    rw [hsnd n, hpsi.eq_of_nhds, hpsi.gradient_eq.trans (gradient_fun_const _ _), sub_self,
      zero_smul, smul_zero, add_zero]
  exact sub_eq_zero.1 ((WithLp.ext_iff _).2 (Prod.ext hfst0 hsnd0))

/-- **The truncations converge.**  The truncated jet agrees with the jet of `u` on the ball of
radius `n + 1`, and differs from it by at most `(2 + C)` times its norm. -/
private theorem tendsto_truncate (hp : p ≠ ∞) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n (x : E), ‖∇ (truncCutoff n) x‖ ≤ C) (u : W1p mu ⊤ p) :
    Tendsto (fun n => truncate hC hbound n u) atTop (𝓝 u) := by
  rw [tendsto_subtype_rng, Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  exact tendsto_eLpNorm_sub_of_eventually_eq (zero_lt_one.trans_le Fact.out).ne' hp
    (Eventually.of_forall fun n => Lp.aestronglyMeasurable _) (Lp.memLp _)
    (by linarith : (0 : ℝ) ≤ 2 + C)
    (Eventually.of_forall fun n => norm_coe_truncate_sub_le hC hbound n u)
    (eventually_coe_truncate_eq hC hbound u)

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
      obtain ⟨Phi, hPhi⟩ := W1p.normedBumpL_mem_range_of_ae_eq_zero hp (phi k)
        (isCompact_closedBall (0 : E) (2 * ((n : ℝ) + 1))) (truncate_ae_eq_zero hC hgrad n u)
      rw [← hPhi]
      exact W1p.ofTestFunctionₗ_mem_w1p0Submodule Phi)
  exact hclosed.mem_of_tendsto (tendsto_truncate hp hC hgrad u) (Eventually.of_forall htrunc)

/-- **`W^{1,p}_0(ℝⁿ) = W^{1,p}(ℝⁿ)`** for `1 ≤ p < ∞`: on the whole space the zero-boundary
condition is no condition at all.  Both restrictions are needed when `E` has positive dimension:
there the analogous equality fails for a nonempty bounded domain, and it fails for `p = ∞`, where
the constant `1` is not a limit of test functions. -/
theorem w1p0Submodule_top_eq_top (hp : p ≠ ∞) : w1p0Submodule mu ⊤ p = ⊤ :=
  eq_top_iff.2 fun u _ => W1p.mem_w1p0Submodule_top hp u

/-- **Test functions are dense in `W^{1,p}(ℝⁿ)`** for `1 ≤ p < ∞`. -/
theorem W1p.denseRange_ofTestFunctionₗ_top (hp : p ≠ ∞) :
    DenseRange (W1p.ofTestFunctionₗ mu ⊤ p) := fun u => by
  rw [← coe_w1p0Submodule]
  exact W1p.mem_w1p0Submodule_top hp u

end TauCeti
