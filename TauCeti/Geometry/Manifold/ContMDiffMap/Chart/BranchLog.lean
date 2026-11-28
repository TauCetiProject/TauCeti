/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Contractible
public import TauCeti.Geometry.Manifold.ContMDiffMap.BranchLog
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Comp
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Prod
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.WithSeminorms
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import TauCeti.Analysis.SpecialFunctions.Exp.Periodic
import TauCeti.Geometry.Manifold.ContMDiffMap.Basic

/-!
# Continuity of the branch of the logarithm, and contractibility

Let `M` be a compact, simply connected, locally path connected `C^n` manifold over `ℝ`, with
`n ≤ ∞`. The branch `ContMDiffMap.branchLog f x₀` of the logarithm of a nowhere-vanishing `C^n`
function `f : M → ℂ` depends continuously on `f` in the weak Whitney topology, as long as `f x₀`
stays off the branch cut of `log` (`ContMDiffMap.continuousOn_branchLog`): near `f₀`, the branch
of `f` is the branch of `f₀` plus the principal logarithm of `f / f₀`, which is a postcomposition
with a fixed smooth map.

The main application is a computation of homotopy type. For a connected nonempty set `s ⊆ M`,
the nowhere-vanishing `C^n` functions `M → ℂ` equal to `1` near `s`
(`ContMDiffMap.nonvanishingEqOneNear`) form a contractible space: their branches normalized at
a point of `s` vanish near `s`, so `exp ((1 - t) • branchLog f x₀)` contracts the space onto the
constant `1`, fixing `1` throughout. On Smale's route to the contractibility of the
diffeomorphisms of the square equal to the identity near the boundary, a diffeomorphism `φ` is
compared with the vector field `φ_* (1, 0)`, and the contractibility of this space of fields, a
space of maps to the circle with the homotopy type of `Ω² S¹`, is the homotopy-theoretic input
(S. Smale, *Diffeomorphisms of the 2-sphere*, Proc. Amer. Math. Soc. 10 (1959), 621–626); the
case of a rectangle is in `TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Rectangle`.

## Main definitions

* `ContMDiffMap.nonvanishingEqOneNearContraction`: the contraction
  `(t, f) ↦ exp ((1 - t) • branchLog f x₀)`, relative to the constant `1`.

## Main results

* `ContMDiffMap.continuousOn_branchLog`: the branch is continuous in the function.
* `ContMDiffMap.contractibleSpace_nonvanishingEqOneNear`: for connected nonempty `s`, the
  nowhere-vanishing functions equal to `1` near `s` form a contractible space.
-/

public section

noncomputable section

open Set Filter Topology Complex
open scoped Manifold TauCeti.ManifoldWeakWhitney ContDiff Real

namespace ContMDiffMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞}
  {f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯}

variable [SimplyConnectedSpace M] [LocallyPathConnectedSpace M]

/-- The exponential map of `ℂ`, as a `C^n` map. -/
private def expMap : C^n⟮𝓘(ℝ, ℂ), ℂ; 𝓘(ℝ, ℂ), ℂ⟯ := ⟨exp, Complex.contDiff_exp.contMDiff⟩

@[simp]
private theorem expMap_apply (z : ℂ) : (expMap : C^n⟮𝓘(ℝ, ℂ), ℂ; 𝓘(ℝ, ℂ), ℂ⟯) z = exp z := rfl

private theorem expMap_comp_smul_branchLog_mem {s : Set M} (hs : IsPreconnected s) {x₀ : M}
    (hx₀ : x₀ ∈ s) (t : ℝ) (f : nonvanishingEqOneNear I n s) :
    expMap.comp (t • branchLog (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) x₀) ∈ nonvanishingEqOneNear I n s := by
  obtain ⟨hf, h1⟩ := mem_nonvanishingEqOneNear.1 f.property
  refine mem_nonvanishingEqOneNear.2 ⟨fun x ↦ by simp [Complex.exp_ne_zero], ?_⟩
  filter_upwards [eventually_branchLog_eq_zero hf hs hx₀ h1] with x hx
  simp [hx]

/-! ### Continuity in the function -/

/-- A bump function on `ℂ`, equal to `1` on the closed disc of radius `1 / 4` about `1` and
supported in the disc of radius `1 / 2`. -/
private def bumpOne : ContDiffBump (1 : ℂ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

/-- A smooth function on `ℂ` which is the principal logarithm near `1`. -/
private def logNearOne (z : ℂ) : ℂ := log (1 + (bumpOne z : ℂ) * (z - 1))

private theorem one_add_bumpOne_mem_slitPlane (z : ℂ) :
    1 + (bumpOne z : ℂ) * (z - 1) ∈ slitPlane := by
  have hlt : ‖(bumpOne z : ℂ) * (z - 1)‖ < 1 := by
    by_cases hz : dist z 1 < 1 / 2
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg bumpOne.nonneg, ← dist_eq_norm]
      calc bumpOne z * dist z 1 ≤ 1 * dist z 1 :=
            mul_le_mul_of_nonneg_right bumpOne.le_one dist_nonneg
        _ < 1 := by linarith
    · rw [bumpOne.zero_of_le_dist (not_lt.1 hz)]
      simp
  refine mem_slitPlane_iff.2 (Or.inl ?_)
  have := neg_abs_le ((bumpOne z : ℂ) * (z - 1)).re
  rw [add_re, one_re]
  linarith [abs_re_le_norm ((bumpOne z : ℂ) * (z - 1))]

private theorem contDiff_logNearOne [ENat.LEInfty n] : ContDiff ℝ n logNearOne := by
  have hb : ContDiff ℝ n fun z : ℂ ↦ (bumpOne z : ℂ) :=
    ofRealCLM.contDiff.comp ((bumpOne.contDiff (n := ⊤)).of_le ENat.LEInfty.out)
  refine contDiff_iff_contDiffAt.2 fun z ↦ ?_
  exact (ContDiffAt.restrict_scalars ℝ (contDiffAt_log (one_add_bumpOne_mem_slitPlane z))).comp z
    (contDiff_const.add (hb.mul (contDiff_id.sub contDiff_const))).contDiffAt

private theorem logNearOne_eq {z : ℂ} (hz : ‖z - 1‖ ≤ 1 / 4) : logNearOne z = log z := by
  rw [logNearOne, bumpOne.one_of_mem_closedBall (by rwa [Metric.mem_closedBall, dist_eq_norm])]
  simp

/-- Near a logarithm `w₀` of `z₀`, the function `z ↦ w₀ + logNearOne (z * exp (-w₀))` is a
logarithm of `z`, for `z` within `‖z₀‖ / 4` of `z₀`. -/
private theorem exp_add_logNearOne {z z₀ w₀ : ℂ} (hw₀ : exp w₀ = z₀) (hz : z ≠ 0)
    (h : dist z z₀ < ‖z₀‖ / 4) : exp (w₀ + logNearOne (z * exp (-w₀))) = z := by
  have hz₀ : z₀ ≠ 0 := hw₀ ▸ Complex.exp_ne_zero w₀
  have hinv : exp (-w₀) = z₀⁻¹ := by rw [Complex.exp_neg, hw₀]
  have hn : ‖z * exp (-w₀) - 1‖ ≤ 1 / 4 := by
    rw [dist_eq_norm] at h
    rw [hinv, show z * z₀⁻¹ - 1 = (z - z₀) / z₀ by field_simp, norm_div,
      div_le_iff₀ (norm_pos_iff.2 hz₀)]
    linarith
  rw [Complex.exp_add, logNearOne_eq hn, exp_log (mul_ne_zero hz (Complex.exp_ne_zero _)), hw₀,
    hinv]
  field_simp

variable [IsManifold I n M] [LocallyCompactSpace E] [CompactSpace M] [ENat.LEInfty n]

/-- On compact `M` and for `n ≤ ∞`, **the branch of the logarithm depends continuously on the
function** in the weak Whitney topology, on the nowhere-vanishing functions whose value at the
base point lies off the branch cut of `log`. -/
theorem continuousOn_branchLog (x₀ : M) :
    ContinuousOn (fun f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ ↦ branchLog f x₀)
      {f | (∀ x, f x ≠ 0) ∧ f x₀ ∈ slitPlane} := by
  rintro f₀ ⟨hf₀, hx₀⟩
  set w₀ := branchLog f₀ x₀
  have hinv (x : M) : exp (-w₀ x) = (f₀ x)⁻¹ := by
    rw [Complex.exp_neg, exp_branchLog_apply hf₀]
  -- Near `f₀`, the branch of `f` is `w₀ + log (f / f₀)`, a postcomposition with a fixed map.
  let G : C^n⟮𝓘(ℝ, ℂ).prod I, ℂ × M; 𝓘(ℝ, ℂ), ℂ⟯ :=
    ⟨fun p ↦ w₀ p.2 + logNearOne (p.1 * exp (-w₀ p.2)),
      (contDiff_snd.add (contDiff_logNearOne.comp
        (contDiff_fst.mul (Complex.contDiff_exp.comp contDiff_snd.neg)))).comp_contMDiff
        (contMDiff_fst.prodMk_space (w₀.contMDiff.comp contMDiff_snd))⟩
  let Φ (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ := G.comp (f.prodMk ContMDiffMap.id)
  have hΦ : Continuous Φ := (continuous_postcomp_manifoldWeakWhitney G).comp
    (continuous_prodMk_manifoldWeakWhitney.comp (continuous_id.prodMk continuous_const))
  have hΦ_apply (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) (x : M) :
      Φ f x = w₀ x + logNearOne (f x * exp (-w₀ x)) := rfl
  have hΦ₀ : Φ f₀ x₀ = log (f₀ x₀) := by
    rw [hΦ_apply, hinv, mul_inv_cancel₀ (hf₀ x₀), logNearOne_eq (by simp), log_one, add_zero,
      branchLog_apply_self hf₀]
  -- Nearby functions are uniformly close to `f₀` relative to `‖f₀‖`, and the value of the
  -- candidate at `x₀` stays close to the principal logarithm.
  have h1 : ∀ᶠ f in 𝓝 f₀, ∀ x ∈ univ, dist (f x) (f₀ x) < ‖f₀ x‖ / 4 :=
    eventually_forall_dist_lt f₀ isCompact_univ (f₀.contMDiff.continuous.norm.div_const 4)
      fun x _ ↦ by have := norm_pos_iff.2 (hf₀ x); positivity
  have h2 : ∀ᶠ f in 𝓝 f₀, ‖Φ f x₀ - log (f x₀)‖ < 2 * π := by
    have ht : Tendsto (fun f ↦ Φ f x₀ - log (f x₀)) (𝓝 f₀) (𝓝 (Φ f₀ x₀ - log (f₀ x₀))) :=
      ((continuous_eval_const_manifoldWeakWhitney x₀).comp hΦ).continuousAt.sub
        (ContinuousAt.comp (f := fun f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ ↦ f x₀) (continuousAt_clog hx₀)
          (continuous_eval_const_manifoldWeakWhitney x₀).continuousAt)
    rw [hΦ₀, sub_self] at ht
    exact ht.norm.eventually (gt_mem_nhds (by simpa using Real.two_pi_pos))
  have hEq : ∀ᶠ f in 𝓝 f₀, f ∈ {f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ | (∀ x, f x ≠ 0) ∧ f x₀ ∈ slitPlane} →
      branchLog f x₀ = Φ f := by
    filter_upwards [h1, h2] with f hf1 hf2 hfS
    have hexp (x : M) : exp (Φ f x) = f x := by
      rw [hΦ_apply]
      exact exp_add_logNearOne (exp_branchLog_apply hf₀ x₀ x) (hfS.1 x) (hf1 x (mem_univ x))
    exact ContMDiffMap.ext fun x ↦ congrFun (coe_branchLog_eq hfS.1
      (Φ f).contMDiff.continuous hexp
      (eq_of_exp_eq_of_norm_sub_lt (by rw [hexp, exp_log (hfS.1 x₀)]) hf2)) x
  exact hΦ.continuousAt.continuousWithinAt.congr_of_eventuallyEq
    (eventually_nhdsWithin_iff.2 hEq) (hEq.self_of_nhds ⟨hf₀, hx₀⟩)

/-- **The contraction of the nowhere-vanishing functions equal to `1` near `s`**, for `s`
preconnected and containing `x₀`: `(t, f) ↦ exp ((1 - t) • branchLog f x₀)`, from the identity
to the constant `1`, fixing `1` throughout. -/
def nonvanishingEqOneNearContraction {s : Set M} (hs : IsPreconnected s) {x₀ : M}
    (hx₀ : x₀ ∈ s) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (nonvanishingEqOneNear I n s))
      (ContinuousMap.const _ ⟨1, one_mem_nonvanishingEqOneNear s⟩)
      {⟨1, one_mem_nonvanishingEqOneNear s⟩} where
  toFun p := ⟨expMap.comp (((1 : ℝ) - p.1) • branchLog (p.2 : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) x₀),
    expMap_comp_smul_branchLog_mem hs hx₀ _ p.2⟩
  continuous_toFun := by
    have hb : Continuous fun f : nonvanishingEqOneNear I n s ↦
        branchLog (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) x₀ :=
      (continuousOn_branchLog x₀).comp_continuous continuous_subtypeVal fun f ↦
        have hf := mem_nonvanishingEqOneNear.1 f.property
        ⟨hf.1, by rw [hf.2.self_of_nhdsSet x₀ hx₀]; exact one_mem_slitPlane⟩
    exact ((continuous_postcomp_manifoldWeakWhitney expMap).comp
      ((continuous_const.sub (continuous_subtypeVal.comp continuous_fst)).smul
        (hb.comp continuous_snd))).subtype_mk _
  map_zero_left f := Subtype.ext <| ContMDiffMap.ext fun x ↦ by
    simp [exp_branchLog_apply (mem_nonvanishingEqOneNear.1 f.property).1]
  map_one_left f := Subtype.ext <| ContMDiffMap.ext fun x ↦ by simp
  prop' t f hf := by
    rw [mem_singleton_iff.1 hf]
    exact Subtype.ext <| ContMDiffMap.ext fun x ↦ by simp

/-- The contraction at time `t` is `exp ((1 - t) • branchLog f x₀)`. -/
@[simp]
theorem nonvanishingEqOneNearContraction_apply {s : Set M} (hs : IsPreconnected s) {x₀ : M}
    (hx₀ : x₀ ∈ s) (t : unitInterval) (f : nonvanishingEqOneNear I n s) (x : M) :
    (nonvanishingEqOneNearContraction hs hx₀ (t, f) : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) x =
      exp ((1 - t : ℝ) • branchLog (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) x₀ x) :=
  (rfl)

/-- **The nowhere-vanishing functions equal to `1` near a connected set form a contractible
space**, on a compact, simply connected, locally path connected manifold, in the weak Whitney
topology. -/
theorem contractibleSpace_nonvanishingEqOneNear {s : Set M} (hs : IsConnected s) :
    ContractibleSpace (nonvanishingEqOneNear I n s) := by
  obtain ⟨x₀, hx₀⟩ := hs.nonempty
  exact (contractible_iff_id_nullhomotopic _).2
    ⟨_, ⟨(nonvanishingEqOneNearContraction hs.isPreconnected hx₀).toHomotopy⟩⟩

end ContMDiffMap
