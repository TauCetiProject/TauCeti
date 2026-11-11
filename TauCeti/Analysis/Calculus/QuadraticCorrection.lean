/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.QuadraticCorrection
public import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Smooth dependence of the quadratic correction on parameters

Let `e p + D p x + N p x = 0` be a family of equations parametrized by `p` in a Banach space `P`,
with right inverses `Q p` of `D p` satisfying `‖Q p y‖ ≤ C ‖y‖` and remainders `N p` satisfying the
quadratic estimate `‖N p x - N p y‖ ≤ (L / 2) (‖x‖ + ‖y‖) ‖x - y‖` on the ball of radius `δ`, with
`C` and `L` independent of `p`. By `TauCeti.exists_mem_range_norm_le_add_add_eq_zero` each
equation has a small solution `x p` in the range of `Q p`, unique among the solutions in that range
of norm at most `r` whenever `r ≤ δ` and `C L r < 1` (`TauCeti.eq_of_add_add_eq_zero`). In gluing
constructions `p` is a finite-dimensional gluing or obstruction parameter and `x p` the correction
of an approximate solution; the finite-dimensional reduction needs `x` to be as smooth in `p` as the
data.

This file proves that it is: if the fixed-point map `(p, z) ↦ Q p (e p + N p z)` is `C^n` at
`(p₀, x p₀)`, with `n ≠ 0`, then `x` is `C^n` at `p₀`
(`TauCeti.contDiffAt_of_forall_add_add_eq_zero`), and globally `C^n` if the fixed-point map is
(`TauCeti.contDiff_of_forall_add_add_eq_zero`). No smoothness of `p ↦ D p` is needed, and the
range of `Q p` may move with `p`.

The solutions in the range of `Q p` are the zeros of `f (p, z) = z + Q p (e p + N p z)`
(`TauCeti.mem_range_and_add_add_eq_zero_iff`). The quadratic estimate makes
`z ↦ Q p₀ (e p₀ + N p₀ z)` Lipschitz with constant `C L r'` on the ball of radius `r'`, for every
`r'` between `‖x p₀‖` and `δ`, so its derivative `A` at `x p₀` has norm at most `C L r < 1`, and
the partial derivative `1 + A` of `f` in `z` is invertible by the Neumann series. Mathlib's
implicit function theorem `ContDiffAt.implicitFunction` then gives a `C^n` local solution, and it
agrees with `x` near `p₀` because `x` is continuous
(`TauCeti.continuousAt_of_forall_add_add_eq_zero`).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications 52 (2012), Appendix A.3.
-/

public section

open Filter Metric Set
open scoped NNReal Topology ContDiff

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜] {P E F G : Type*}
  [NormedAddCommGroup P] [NormedSpace 𝕜 P] [CompleteSpace P]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [SeminormedAddCommGroup F] [FunLike G F E] [AddMonoidHomClass G F E]
  {Q : P → G} {D N : P → E → F} {e : P → F} {C L : ℝ≥0} {δ : ℝ}
  (hDQ : ∀ p y, D p (Q p y) = y) (hQ : ∀ p y, ‖Q p y‖ ≤ C * ‖y‖)
  (hN : ∀ p, ∀ x ∈ closedBall (0 : E) δ, ∀ y ∈ closedBall (0 : E) δ,
    ‖N p x - N p y‖ ≤ L / 2 * (‖x‖ + ‖y‖) * ‖x - y‖)
include hDQ hQ hN

/-- **Smooth dependence on a parameter.** Let `e p + D p x + N p x = 0` be a family of equations
over a Banach space `P`, with right inverses `Q p` of `D p` and remainders `N p` satisfying the
bounds with constants `C` and `L` uniform in `p`. Let `x p` be solutions in the range of `Q p`, all
of norm at most `r`, where `r < δ` and `C L r < 1`. If the fixed-point map
`(p, z) ↦ Q p (e p + N p z)` is `C^n` at `(p₀, x p₀)`, with `n ≠ 0`, then `x` is `C^n` at `p₀`. -/
theorem contDiffAt_of_forall_add_add_eq_zero {n : ℕ∞ω} (hn : n ≠ 0) {x : P → E} {r : ℝ}
    (hrδ : r < δ) (hr : C * L * r < 1) (hx : ∀ p, ‖x p‖ ≤ r) (hxQ : ∀ p, x p ∈ range (Q p))
    (hxe : ∀ p, e p + D p (x p) + N p (x p) = 0) {p₀ : P}
    (hT : ContDiffAt 𝕜 n (fun v : P × E ↦ Q v.1 (e v.1 + N v.1 v.2)) (p₀, x p₀)) :
    ContDiffAt 𝕜 n x p₀ := by
  -- The solutions in the range of `Q p` are the zeros of `f (p, z) = z + Q p (e p + N p z)`.
  have hzero (p : P) (z : E) :
      z + Q p (e p + N p z) = 0 ↔ z ∈ range (Q p) ∧ e p + D p z + N p z = 0 := by
    rw [mem_range_and_add_add_eq_zero_iff (hDQ p)]
    exact eq_neg_iff_add_eq_zero.symm
  have hf : ContDiffAt 𝕜 n (fun v : P × E ↦ v.2 + Q v.1 (e v.1 + N v.1 v.2)) (p₀, x p₀) :=
    contDiffAt_snd.add hT
  have hfu : x p₀ + Q p₀ (e p₀ + N p₀ (x p₀)) = 0 := (hzero p₀ (x p₀)).2 ⟨hxQ p₀, hxe p₀⟩
  -- The derivative `A` of the fixed-point map in `z` has norm less than one.
  have hTd := (hT.differentiableAt hn).hasFDerivAt
  set A : E →L[𝕜] E := fderiv 𝕜 (fun v : P × E ↦ Q v.1 (e v.1 + N v.1 v.2)) (p₀, x p₀) ∘L
    ContinuousLinearMap.inr 𝕜 P E with hAdef
  have hA : HasFDerivAt (fun z ↦ Q p₀ (e p₀ + N p₀ z)) A (x p₀) :=
    hTd.comp (x p₀) (hasFDerivAt_prodMk_right p₀ (x p₀))
  have hAle (r' : ℝ) (hr' : r' ∈ Ioo r δ) : ‖A‖ ≤ C * L * r' := by
    have hr'0 : 0 ≤ r' := (norm_nonneg _).trans ((hx p₀).trans hr'.1.le)
    have hlip : LipschitzOnWith (Real.toNNReal (C * L * r')) (fun z ↦ Q p₀ (e p₀ + N p₀ z))
        (ball 0 r') := by
      refine LipschitzOnWith.of_dist_le_mul fun z hz w hw ↦ ?_
      have hz' := mem_ball_zero_iff.1 hz
      have hw' := mem_ball_zero_iff.1 hw
      rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm, dist_eq_norm]
      calc ‖Q p₀ (e p₀ + N p₀ z) - Q p₀ (e p₀ + N p₀ w)‖ = ‖Q p₀ (N p₀ z - N p₀ w)‖ := by
            rw [← map_sub, add_sub_add_left_eq_sub]
        _ ≤ C * (L / 2 * (‖z‖ + ‖w‖) * ‖z - w‖) :=
            (hQ _ _).trans (by
              gcongr
              exact hN p₀ z (mem_closedBall_zero_iff.2 (hz'.le.trans hr'.2.le)) w
                (mem_closedBall_zero_iff.2 (hw'.le.trans hr'.2.le)))
        _ ≤ C * (L / 2 * (r' + r') * ‖z - w‖) := by gcongr
        _ = C * L * r' * ‖z - w‖ := by ring
    have h := hA.le_of_lipschitzOn
      (isOpen_ball.mem_nhds (mem_ball_zero_iff.2 ((hx p₀).trans_lt hr'.1))) hlip
    rwa [Real.coe_toNNReal _ (by positivity)] at h
  have hAlt : ‖A‖ < 1 := by
    have h : ‖A‖ ≤ C * L * r :=
      ge_of_tendsto (((continuous_const.mul continuous_id).tendsto r).mono_left
        nhdsWithin_le_nhds) (by filter_upwards [Ioo_mem_nhdsGT hrδ] with r' hr' using hAle r' hr')
    exact h.trans_lt hr
  -- Hence the partial derivative `1 + A` of `f` in `z` is invertible.
  have hinv : (fderiv 𝕜 (fun v : P × E ↦ v.2 + Q v.1 (e v.1 + N v.1 v.2)) (p₀, x p₀) ∘L
      ContinuousLinearMap.inr 𝕜 P E).IsInvertible := by
    have hfd : HasFDerivAt (fun v : P × E ↦ v.2 + Q v.1 (e v.1 + N v.1 v.2))
        (ContinuousLinearMap.snd 𝕜 P E +
          fderiv 𝕜 (fun v : P × E ↦ Q v.1 (e v.1 + N v.1 v.2)) (p₀, x p₀)) (p₀, x p₀) :=
      hasFDerivAt_snd.add hTd
    rw [hfd.fderiv, ContinuousLinearMap.add_comp,
      ContinuousLinearMap.snd_comp_inr, ← hAdef]
    obtain ⟨w, hw⟩ := isUnit_one_sub_of_norm_lt_one (x := -A) (by rwa [norm_neg])
    refine ⟨ContinuousLinearEquiv.unitsEquiv 𝕜 E w, ?_⟩
    ext z
    simp [hw]
  -- The implicit function agrees with the continuous family `x` near `p₀`.
  have hcont : ContinuousAt x p₀ :=
    continuousAt_of_forall_add_add_eq_zero hDQ hQ hN hrδ.le hr hx hxQ hxe
      (hT.continuousAt.comp (f := fun p : P ↦ (p, x p₀))
        (continuousAt_id.prodMk continuousAt_const))
  have hev : x =ᶠ[𝓝 p₀] hf.implicitFunction hn hinv := by
    filter_upwards [(continuousAt_id.prodMk hcont).tendsto.eventually
      (hf.eventually_apply_eq_iff_implicitFunction hn hinv)] with p hp
    exact (hp.1 (by rw [hfu]; exact (hzero p (x p)).2 ⟨hxQ p, hxe p⟩)).symm
  exact (hf.contDiffAt_implicitFunction hn hinv).congr_of_eventuallyEq hev

/-- **Smooth dependence on a parameter**, global form: a family of solutions `x p` in the range of
`Q p`, of norm at most `r < δ` with `C L r < 1`, is `C^n` when the fixed-point map
`(p, z) ↦ Q p (e p + N p z)` is, for `n ≠ 0`. -/
theorem contDiff_of_forall_add_add_eq_zero {n : ℕ∞ω} (hn : n ≠ 0) {x : P → E} {r : ℝ}
    (hrδ : r < δ) (hr : C * L * r < 1) (hx : ∀ p, ‖x p‖ ≤ r) (hxQ : ∀ p, x p ∈ range (Q p))
    (hxe : ∀ p, e p + D p (x p) + N p (x p) = 0)
    (hT : ContDiff 𝕜 n fun v : P × E ↦ Q v.1 (e v.1 + N v.1 v.2)) : ContDiff 𝕜 n x :=
  contDiff_iff_contDiffAt.2 fun _ ↦
    contDiffAt_of_forall_add_add_eq_zero hDQ hQ hN hn hrδ hr hx hxQ hxe hT.contDiffAt

end TauCeti
