/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Analysis.Calculus.ContDiff.Prod
import TauCeti.Analysis.Calculus.Deriv.Parity
import TauCeti.Analysis.Calculus.Deriv.Slope
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Convex.Deriv
import TauCeti.Analysis.Convex.Function.Basic
import TauCeti.Analysis.Convex.StrictTangent

/-!
# Fold and pitchfork bifurcations of one-parameter families of real functions

Let `F : ℝ × ℝ → ℝ` be a one-parameter family `x ↦ F (x, t)` of real functions with `F (0, 0) = 0`.
This file describes, for all `t` near `0`, the zeros of `x ↦ F (x, t)` near `0` together with the
signs of the derivative `∂ₓ F` at them, in the two ways in which such a zero degenerates in a
generic one-parameter family: the fold, and, for a family that is odd in `x`, the pitchfork of its
trivial zero.

**The fold.** Suppose `∂ₓ F (0, 0) = 0`, `∂ₓ² F (0, 0) > 0` and `b = ∂ₜ F (0, 0) ≠ 0`. Then for
every small `δ > 0` and every `t` near `0` (`TauCeti.eventually_fold`):

* if `b t > 0`, then `F (x, t) > 0` on `(-δ, δ)`: there is no zero;
* if `t = 0`, the only zero in `(-δ, δ)` is `0`;
* if `b t < 0`, there are exactly two zeros `x₁ ∈ (-δ, 0)` and `x₂ ∈ (0, δ)`, and
  `∂ₓ F (x₁, t) < 0 < ∂ₓ F (x₂, t)`.

So two nondegenerate zeros of opposite signs are born or die together, and the signed count
`∑ sign ∂ₓ F` of the zeros near `0` vanishes on both sides of `t = 0`.

**The equivariant pitchfork.** Suppose instead that `F` is odd in `x` near `(0, 0)`,
`F (-x, t) = -F (x, t)`, so that `x = 0` is a zero for every `t`, and that `∂ₓ F (0, 0) = 0`,
`∂ₓ³ F (0, 0) > 0` and `b = ∂ₜ ∂ₓ F (0, 0) ≠ 0`. Then for every small `δ > 0` and every `t` near
`0` (`TauCeti.eventually_pitchfork`):

* if `b t ≥ 0`, the only zero in `(-δ, δ)` is `0`, and `∂ₓ F (0, t) > 0` when `b t > 0`;
* if `b t < 0`, then `∂ₓ F (0, t) < 0`, and the zeros in `(-δ, δ)` are exactly `-x₀, 0, x₀` for
  some `x₀ ∈ (0, δ)`, with `∂ₓ F (-x₀, t) = ∂ₓ F (x₀, t) > 0`.

The sign of `∂ₓ F` at the trivial zero `0` changes as `t` crosses `0`, and on the side where it is
negative a single orbit `{-x₀, x₀}` of the symmetry `x ↦ -x` appears, whose two points carry the
sign of `∂ₓ³ F (0, 0)`. The signed count of all zeros near `0` is `1` on both sides, but the signed
count of the orbits, in which `{-x₀, x₀}` counts once, changes from `1` to `0`.

For `∂ₓ² F (0, 0) < 0`, respectively `∂ₓ³ F (0, 0) < 0`, the statements apply to `-F`, which has
the same zeros and the opposite derivatives.

These models motivate the file. In Taubes's analysis of a generic path of almost complex
structures, a one-dimensional Lyapunov–Schmidt reduction of the normal deformation problem of a
pseudoholomorphic curve, to a kernel and cokernel of dimension one
(`ContinuousLinearMap.FredholmPackage.obstructionMap`), is expected to produce a fold at a birth or
death of a pair of curves of opposite determinant signs, and an odd family, odd under the deck
transformation of a double cover, at the period doubling of a torus. In the latter case the
trivial zero corresponds to the double cover of the torus and the orbit `{-x₀, x₀}` to a single
embedded torus in twice its class; the resulting change in the signed count of orbits is why
Taubes weights multiply covered tori by a series rather than by their determinant signs alone.
Nothing in this file proves these reductions.

The proofs are elementary. Near `(0, 0)` the relevant derivative `∂ₓ² F` (for the fold) or
`∂ₓ³ F` (for the pitchfork) is positive, so each slice `x ↦ F (x, t)` is strictly convex on
`[-δ, δ]` (respectively on `[0, δ]`, using `∂ₓ² F (0, t) = 0` for an odd slice). A strictly convex
function has at most two zeros on an interval (`StrictConvexOn.eq_or_eq_of_apply_eq`), and its
derivative is negative at the first and positive at the second. The zeros are produced by the
intermediate value theorem, and the dependence on `t` enters only through the sign of `F (0, t)`
(respectively `∂ₓ F (0, t)`), which is that of `b t`.

## Main results

* `TauCeti.eventually_fold`: the zeros near a fold point and their signs.
* `TauCeti.eventually_setOf_eq_of_deriv_eq_zero`: the solutions of `g σ = s` near a nondegenerate
  critical point of `g`, and the signs of `g'` at them; `TauCeti.eq_and_eq_of_setOf_eq_pair`
  identifies the two solutions found on nested intervals.
* `TauCeti.eventually_pitchfork`: the zeros near a pitchfork point of an odd family and their
  signs.

## References

* M. Golubitsky and D. G. Schaeffer, *Singularities and Groups in Bifurcation Theory, Vol. I*,
  Applied Mathematical Sciences 51, Springer, 1985, Chapters II–III and VI.
* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential Geom.
  44 (1996), 818–893.
-/

public section

open Filter Set
open scoped Topology

namespace TauCeti

/-! ### Partial derivatives of a function of two variables -/

variable {F : ℝ × ℝ → ℝ}

/-- The `k`-th partial derivative of `F` in its first variable, as a function of the point. The
proofs below use that `partialFst F k (x, t)` is definitionally `deriv^[k] (fun y => F (y, t)) x`
to pass between the two forms. -/
private noncomputable def partialFst (F : ℝ × ℝ → ℝ) (k : ℕ) (p : ℝ × ℝ) : ℝ :=
  deriv^[k] (fun y => F (y, p.2)) p.1

/-- Near a point where `F` is `Cⁿ`, the function `partialFst F k` is `C^(n-k)`. -/
private theorem eventually_contDiffAt_partialFst {n : ℕ} {p₀ : ℝ × ℝ} (hF : ContDiffAt ℝ n F p₀)
    (k : ℕ) (hk : k ≤ n) : ∀ᶠ p in 𝓝 p₀, ContDiffAt ℝ (n - k : ℕ) (partialFst F k) p :=
  (hF.eventually (by simp)).mono fun _ hp =>
    hp.contDiffAt_iterate_deriv_fst (by exact_mod_cast (show n - k + k ≤ n by omega))

/-! ### Zeros of the slices -/

/-- The zeros of a strictly convex function on `[-δ, δ]` that is negative at `0` and positive at
`±δ`: one in `(-δ, 0)`, where the derivative is negative, and one in `(0, δ)`, where it is
positive. -/
private theorem fold_slice {g : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hconv : StrictConvexOn ℝ (Icc (-δ) δ) g) (hd : ∀ x ∈ Icc (-δ) δ, DifferentiableAt ℝ g x)
    (h0 : g 0 < 0) (hl : 0 < g (-δ)) (hr : 0 < g δ) :
    ∃ x₁ ∈ Ioo (-δ) 0, ∃ x₂ ∈ Ioo 0 δ, {x ∈ Ioo (-δ) δ | g x = 0} = {x₁, x₂} ∧
      deriv g x₁ < 0 ∧ 0 < deriv g x₂ := by
  have hc : ContinuousOn g (Icc (-δ) δ) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  obtain ⟨x₁, hx₁, hgx₁⟩ := intermediate_value_Ioo' (show -δ ≤ 0 by linarith)
    (hc.mono (Icc_subset_Icc le_rfl hδ.le)) ⟨h0, hl⟩
  obtain ⟨x₂, hx₂, hgx₂⟩ := intermediate_value_Ioo hδ.le
    (hc.mono (Icc_subset_Icc (by linarith) le_rfl)) ⟨h0, hr⟩
  have hm₁ : x₁ ∈ Icc (-δ) δ := ⟨hx₁.1.le, by linarith [hx₁.2]⟩
  have hm₂ : x₂ ∈ Icc (-δ) δ := ⟨by linarith [hx₂.1], hx₂.2.le⟩
  have h₁₂ : x₁ < x₂ := hx₁.2.trans hx₂.1
  refine ⟨x₁, hx₁, x₂, hx₂, ?_, ?_, ?_⟩
  · ext x
    simp only [mem_sep_iff, mem_insert_iff, mem_singleton_iff]
    refine ⟨fun ⟨hx, hgx⟩ =>
      hconv.eq_or_eq_of_apply_eq hm₁ hm₂ (Ioo_subset_Icc_self hx) h₁₂ hgx₁ hgx₂ hgx, ?_⟩
    rintro (rfl | rfl)
    · exact ⟨⟨hx₁.1, hx₁.2.trans hδ⟩, hgx₁⟩
    · exact ⟨⟨by linarith [hx₂.1], hx₂.2⟩, hgx₂⟩
  · have h := hconv.lt_slope_of_hasDerivAt hm₁ hm₂ h₁₂ (hd x₁ hm₁).hasDerivAt
    rwa [slope_def_field, hgx₁, hgx₂, sub_self, zero_div] at h
  · have h := hconv.slope_lt_of_hasDerivAt hm₁ hm₂ h₁₂ (hd x₂ hm₂).hasDerivAt
    rwa [slope_def_field, hgx₁, hgx₂, sub_self, zero_div] at h

/-- A strictly convex function on `[0, δ]` that is odd on `(-δ, δ)`, with nonnegative derivative at
`0`, has no zero in `(-δ, δ)` other than `0`. -/
private theorem pitchfork_slice_of_nonneg {g : ℝ → ℝ} {d δ : ℝ} (hδ : 0 < δ)
    (hconv : StrictConvexOn ℝ (Icc 0 δ) g) (hodd : ∀ x ∈ Ioo (-δ) δ, g (-x) = -g x)
    (hd : HasDerivAt g d 0) (hd0 : 0 ≤ d) : {x ∈ Ioo (-δ) δ | g x = 0} = {0} := by
  have h0 : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
  have hg0 : g 0 = 0 := by
    have := hodd 0 h0
    rw [neg_zero] at this
    linarith
  have hpos : ∀ y ∈ Ioc 0 δ, 0 < g y := fun y hy => by
    have h := hconv.mul_sub_lt_sub_of_hasDerivWithinAt ⟨le_rfl, hδ.le⟩ ⟨hy.1.le, hy.2⟩ hy.1.ne
      hd.hasDerivWithinAt
    rw [hg0, sub_zero, sub_zero] at h
    exact (mul_nonneg hd0 hy.1.le).trans_lt h
  ext y
  simp only [mem_sep_iff, mem_singleton_iff]
  refine ⟨fun ⟨hy, hgy⟩ => ?_, ?_⟩
  · rcases lt_trichotomy y 0 with h | h | h
    · have h' := hpos (-y) ⟨neg_pos.2 h, by linarith [hy.1]⟩
      rw [hodd y hy, hgy, neg_zero] at h'
      exact absurd h' (lt_irrefl 0)
    · exact h
    · exact absurd hgy (hpos y ⟨h, hy.2.le⟩).ne'
  · rintro rfl
    exact ⟨h0, hg0⟩

/-- A strictly convex function on `[0, δ]` that is odd on `(-δ, δ)`, with negative derivative at
`0` and positive at `δ`, has exactly the zeros `-x₀, 0, x₀` in `(-δ, δ)`, for some `x₀ ∈ (0, δ)`,
and its derivative at `±x₀` is positive. -/
private theorem pitchfork_slice_of_neg {g : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hconv : StrictConvexOn ℝ (Icc 0 δ) g) (hodd : ∀ x ∈ Ioo (-δ) δ, ∀ᶠ y in 𝓝 x, g (-y) = -g y)
    (hd : ∀ x ∈ Icc 0 δ, DifferentiableAt ℝ g x) (hneg : deriv g 0 < 0) (hgδ : 0 < g δ) :
    ∃ x₀ ∈ Ioo 0 δ, {x ∈ Ioo (-δ) δ | g x = 0} = {-x₀, 0, x₀} ∧ 0 < deriv g x₀ ∧
      deriv g (-x₀) = deriv g x₀ := by
  have h0 : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
  have hm₀ : (0 : ℝ) ∈ Icc 0 δ := ⟨le_rfl, hδ.le⟩
  have hg0 : g 0 = 0 := by
    have := (hodd 0 h0).self_of_nhds
    rw [neg_zero] at this
    linarith
  -- A point `ε ∈ (0, δ)` with `g ε < 0`, then a zero `x₀ ∈ (ε, δ)`.
  obtain ⟨ε, hεneg, hε⟩ := (((hd 0 hm₀).hasDerivAt.tendsto_slope_zero_right.eventually
    (gt_mem_nhds hneg)).and (Ioo_mem_nhdsGT hδ)).exists
  rw [zero_add, hg0, sub_zero, smul_eq_mul] at hεneg
  have hgε : g ε < 0 := by
    by_contra! h
    linarith [mul_nonneg (inv_nonneg.2 hε.1.le) h]
  obtain ⟨x₀, hx₀, hgx₀⟩ := intermediate_value_Ioo hε.2.le (fun y hy =>
    (hd y ⟨hε.1.le.trans hy.1, hy.2⟩).continuousAt.continuousWithinAt) ⟨hgε, hgδ⟩
  have hx₀pos : 0 < x₀ := hε.1.trans hx₀.1
  have hmx₀ : x₀ ∈ Icc 0 δ := ⟨hx₀pos.le, hx₀.2.le⟩
  have hx₀I : x₀ ∈ Ioo (-δ) δ := ⟨by linarith, hx₀.2⟩
  refine ⟨x₀, ⟨hx₀pos, hx₀.2⟩, ?_, ?_, deriv_neg_eq_of_eventually_odd (hodd x₀ hx₀I)⟩
  · ext y
    simp only [mem_sep_iff, mem_insert_iff, mem_singleton_iff]
    refine ⟨fun ⟨hy, hgy⟩ => ?_, ?_⟩
    · rcases lt_trichotomy y 0 with h | h | h
      · have hgy' : g (-y) = 0 := by rw [(hodd y hy).self_of_nhds, hgy, neg_zero]
        rcases hconv.eq_or_eq_of_apply_eq hm₀ hmx₀ ⟨by linarith, by linarith [hy.1]⟩ hx₀pos
          hg0 hgx₀ hgy' with h' | h'
        · linarith
        · exact Or.inl (by linarith)
      · exact Or.inr (Or.inl h)
      · rcases hconv.eq_or_eq_of_apply_eq hm₀ hmx₀ ⟨h.le, hy.2.le⟩ hx₀pos hg0 hgx₀ hgy
          with h' | h'
        · linarith
        · exact Or.inr (Or.inr h')
    · rintro (rfl | rfl | rfl)
      · exact ⟨⟨by linarith [hx₀.2], by linarith⟩,
          by rw [(hodd x₀ hx₀I).self_of_nhds, hgx₀, neg_zero]⟩
      · exact ⟨h0, hg0⟩
      · exact ⟨hx₀I, hgx₀⟩
  · have h := hconv.slope_lt_of_hasDerivAt hm₀ hmx₀ hx₀pos (hd x₀ hmx₀).hasDerivAt
    rwa [slope_def_field, hg0, hgx₀, sub_self, zero_div] at h

/-- The point `(x, t)` lies in the ball of radius `δ₀` about the origin when `|x|, |t| < δ₀`. -/
private theorem mem_ball_of_abs_lt {δ₀ x t : ℝ} (hx : |x| < δ₀) (ht : |t| < δ₀) :
    ((x, t) : ℝ × ℝ) ∈ Metric.ball ((0 : ℝ), (0 : ℝ)) δ₀ := by
  rw [Metric.mem_ball, Prod.dist_eq]
  exact max_lt (by simpa [Real.dist_eq] using hx) (by simpa [Real.dist_eq] using ht)

/-! ### The fold -/

/-- The facts about `F` at a point `(x, t)` of the box around a fold point. -/
private structure FoldBox (F : ℝ × ℝ → ℝ) (x t : ℝ) : Prop where
  hasDerivAt_fst : HasDerivAt (fun y => F (y, t)) (fderiv ℝ F (x, t) (1, 0)) x
  hasDerivAt_snd : HasDerivAt (fun s => F (x, s)) (fderiv ℝ F (x, t) (0, 1)) t
  deriv2_pos : 0 < deriv^[2] (fun y => F (y, t)) x
  mul_deriv_snd_pos : 0 < deriv (fun s => F (0, s)) 0 * fderiv ℝ F (x, t) (0, 1)

/-- Near a fold point there is a box `|x|, |t| < δ₀` on which `F` is differentiable,
`∂ₓ² F > 0` and `b ∂ₜ F > 0`, where `b = ∂ₜ F (0, 0)`. -/
private theorem exists_fold_box (hF : ContDiffAt ℝ 2 F 0)
    (h₂ : 0 < iteratedDeriv 2 (fun x => F (x, 0)) 0) (hb : deriv (fun s => F (0, s)) 0 ≠ 0) :
    ∃ δ₀ > 0, ∀ {x t : ℝ}, |x| < δ₀ → |t| < δ₀ → FoldBox F x t := by
  set b := deriv (fun s => F (0, s)) 0
  have hF0 : ContDiffAt ℝ (2 : ℕ) F (0, 0) := by
    rw [Prod.mk_zero_zero]
    exact_mod_cast hF
  have hbF : fderiv ℝ F (0, 0) (0, 1) = b :=
    (hasDerivAt_slice_right (hF0.differentiableAt two_ne_zero)).deriv.symm
  have hval : 0 < partialFst F 2 (0, 0) := by
    rw [partialFst, ← iteratedDeriv_eq_iterate]
    exact h₂
  have hcontt : ContinuousAt (fun p => b * fderiv ℝ F p (0, 1)) (0, 0) :=
    continuousAt_const.mul ((hF0.continuousAt_fderiv two_ne_zero).clm_apply continuousAt_const)
  have hev : ∀ᶠ p in 𝓝 ((0 : ℝ), (0 : ℝ)), ContDiffAt ℝ (2 : ℕ) F p ∧ 0 < partialFst F 2 p ∧
      0 < b * fderiv ℝ F p (0, 1) := by
    filter_upwards [hF0.eventually (by simp),
      ((eventually_contDiffAt_partialFst hF0 2 le_rfl).self_of_nhds.continuousAt).eventually
        (lt_mem_nhds hval),
      hcontt.eventually (lt_mem_nhds (show (0 : ℝ) < b * fderiv ℝ F (0, 0) (0, 1) by
        rw [hbF]; exact mul_self_pos.2 hb))] with p h₁ h₂ h₃
    exact ⟨h₁, h₂, h₃⟩
  obtain ⟨δ₀, hδ₀, hbox⟩ := Metric.eventually_nhds_iff_ball.1 hev
  refine ⟨δ₀, hδ₀, fun hx ht => ?_⟩
  obtain ⟨hcd, h2pos, hbpos⟩ := hbox _ (mem_ball_of_abs_lt hx ht)
  have hdF := hcd.differentiableAt two_ne_zero
  exact ⟨hasDerivAt_slice_left hdF, hasDerivAt_slice_right hdF, h2pos, hbpos⟩

/-- On the box around a fold point, the slices are strictly convex on `[-δ, δ]`. -/
private theorem strictConvexOn_of_foldBox {δ₀ δ t : ℝ}
    (hbox : ∀ {x t : ℝ}, |x| < δ₀ → |t| < δ₀ → FoldBox F x t) (hδ : δ < δ₀) (ht : |t| < δ₀) :
    StrictConvexOn ℝ (Icc (-δ) δ) (fun x => F (x, t)) :=
  strictConvexOn_of_deriv2_pos (convex_Icc _ _) (fun x hx =>
    (hbox ((abs_le.2 hx).trans_lt hδ) ht).hasDerivAt_fst.continuousAt.continuousWithinAt)
    fun x hx => (hbox ((abs_le.2 (Ioo_subset_Icc_self (by rwa [interior_Icc] at hx))).trans_lt
      hδ) ht).deriv2_pos

/-- **The fold.** Let `F : ℝ × ℝ → ℝ` be `C²` near the origin, with `F (0, 0) = 0`,
`∂ₓ F (0, 0) = 0`, `∂ₓ² F (0, 0) > 0` and `b = ∂ₜ F (0, 0) ≠ 0`. Then for all small `δ > 0` and all
`t` near `0`, the zeros of `x ↦ F (x, t)` in `(-δ, δ)` are: none if `b t > 0`; only `0` if `t = 0`;
and exactly two, `x₁ ∈ (-δ, 0)` and `x₂ ∈ (0, δ)`, with `∂ₓ F (x₁, t) < 0 < ∂ₓ F (x₂, t)`, if
`b t < 0`. -/
theorem eventually_fold (hF : ContDiffAt ℝ 2 F 0) (h₀ : F 0 = 0)
    (h₁ : deriv (fun x => F (x, 0)) 0 = 0) (h₂ : 0 < iteratedDeriv 2 (fun x => F (x, 0)) 0)
    (hb : deriv (fun s => F (0, s)) 0 ≠ 0) :
    ∀ᶠ δ in 𝓝[>] 0, ∀ᶠ t in 𝓝 0,
      (0 < deriv (fun s => F (0, s)) 0 * t → ∀ x ∈ Ioo (-δ) δ, 0 < F (x, t)) ∧
      (t = 0 → {x ∈ Ioo (-δ) δ | F (x, t) = 0} = {0}) ∧
      (deriv (fun s => F (0, s)) 0 * t < 0 → ∃ x₁ ∈ Ioo (-δ) 0, ∃ x₂ ∈ Ioo 0 δ,
        {x ∈ Ioo (-δ) δ | F (x, t) = 0} = {x₁, x₂} ∧
        deriv (fun x => F (x, t)) x₁ < 0 ∧ 0 < deriv (fun x => F (x, t)) x₂) := by
  obtain ⟨δ₀, hδ₀, hbox⟩ := exists_fold_box hF h₂ hb
  have h₀' : F (0, 0) = 0 := by
    rw [Prod.mk_zero_zero]
    exact h₀
  have h0δ₀ : |(0 : ℝ)| < δ₀ := by simpa using hδ₀
  -- The slice at `t = 0` is positive away from `0`, since it lies above its tangent at `0`.
  have hpos0 : ∀ {x : ℝ}, |x| < δ₀ → x ≠ 0 → 0 < F (x, 0) := by
    intro x hx hx0
    have hd0 : HasDerivAt (fun y => F (y, 0)) 0 0 := by
      have h := (hbox h0δ₀ h0δ₀).hasDerivAt_fst
      rwa [← h.deriv, h₁] at h
    have h := (strictConvexOn_of_foldBox hbox hx h0δ₀).mul_sub_lt_sub_of_hasDerivWithinAt
      ⟨by simp, abs_nonneg x⟩ ⟨neg_abs_le x, le_abs_self x⟩ hx0.symm hd0.hasDerivWithinAt
    rwa [zero_mul, h₀', sub_zero] at h
  -- Along vertical lines, `F (x, t) - F (x, 0)` has the sign of `b t`.
  have hsign : ∀ {x t : ℝ}, |x| < δ₀ → |t| < δ₀ → (0 < deriv (fun s => F (0, s)) 0 * t →
      F (x, 0) < F (x, t)) ∧ (deriv (fun s => F (0, s)) 0 * t < 0 → F (x, t) < F (x, 0)) :=
    fun hx ht => by
      simpa only [sub_zero] using lt_and_lt_of_hasDerivAt_of_mul_pos (a := 0) ordConnected_Ioo
        (fun s hs => (hbox hx (abs_lt.2 hs)).hasDerivAt_snd.continuousAt.continuousWithinAt)
        (fun s hs => (hbox hx (abs_lt.2 (interior_subset hs))).hasDerivAt_snd)
        (fun s hs => (hbox hx (abs_lt.2 (interior_subset hs))).mul_deriv_snd_pos)
        ⟨by linarith, hδ₀⟩ (abs_lt.1 ht)
  filter_upwards [Ioo_mem_nhdsGT hδ₀] with δ ⟨hδpos, hδδ₀⟩
  have hδabs : |δ| < δ₀ := by rwa [abs_of_pos hδpos]
  have hδabs' : |-δ| < δ₀ := by rwa [abs_neg]
  filter_upwards [Ioo_mem_nhds (neg_neg_of_pos hδ₀) hδ₀,
    (hbox hδabs h0δ₀).hasDerivAt_snd.continuousAt.eventually
      (lt_mem_nhds (hpos0 hδabs hδpos.ne')),
    (hbox hδabs' h0δ₀).hasDerivAt_snd.continuousAt.eventually
      (lt_mem_nhds (hpos0 hδabs' (neg_ne_zero.2 hδpos.ne')))] with t ht hFp hFn
  replace ht := abs_lt.2 ht
  have habs : ∀ {x}, x ∈ Ioo (-δ) δ → |x| < δ₀ := fun hx => (abs_lt.2 hx).trans hδδ₀
  refine ⟨fun hbt x hx => ?_, fun ht0 => ?_, fun hbt => ?_⟩
  · have hlt := (hsign (habs hx) ht).1 hbt
    rcases eq_or_ne x 0 with rfl | hx0
    · rwa [h₀'] at hlt
    · exact (hpos0 (habs hx) hx0).trans hlt
  · subst ht0
    ext x
    simp only [mem_sep_iff, mem_singleton_iff]
    refine ⟨fun ⟨hx, hFx⟩ => by_contra fun hx0 => (hpos0 (habs hx) hx0).ne' hFx, ?_⟩
    rintro rfl
    exact ⟨⟨by linarith, hδpos⟩, h₀'⟩
  · have hF0t : F (0, t) < 0 := by
      have := (hsign h0δ₀ ht).2 hbt
      rwa [h₀'] at this
    exact fold_slice hδpos (strictConvexOn_of_foldBox hbox hδδ₀ ht) (fun x hx =>
      (hbox ((abs_le.2 hx).trans_lt hδδ₀) ht).hasDerivAt_fst.differentiableAt) hF0t hFn hFp

/-- **A nondegenerate critical point folds the nearby values.** Let `g : ℝ → ℝ` be `C²` near `0`,
with `g' (0) = 0` and `g'' (0) ≠ 0`. Then for all small `δ > 0` and all `s` near `g 0`, the
solutions of `g σ = s` in `(-δ, δ)` are: none if `g'' (0) (s - g 0) < 0`; only `0` if `s = g 0`;
and exactly two, `σ₁ ∈ (-δ, 0)` and `σ₂ ∈ (0, δ)`, at which `g'` has opposite signs, if
`0 < g'' (0) (s - g 0)`. This is `eventually_fold` for `F (σ, u) = g'' (0) (g σ - g 0 - u)`. -/
theorem eventually_setOf_eq_of_deriv_eq_zero {g : ℝ → ℝ} (hg : ContDiffAt ℝ 2 g 0)
    (h₁ : deriv g 0 = 0) (h₂ : iteratedDeriv 2 g 0 ≠ 0) :
    ∀ᶠ δ in 𝓝[>] 0, ∀ᶠ s in 𝓝 (g 0),
      (iteratedDeriv 2 g 0 * (s - g 0) < 0 → ∀ σ ∈ Ioo (-δ) δ, g σ ≠ s) ∧
      (s = g 0 → {σ ∈ Ioo (-δ) δ | g σ = s} = {0}) ∧
      (0 < iteratedDeriv 2 g 0 * (s - g 0) → ∃ σ₁ ∈ Ioo (-δ) 0, ∃ σ₂ ∈ Ioo 0 δ,
        {σ ∈ Ioo (-δ) δ | g σ = s} = {σ₁, σ₂} ∧ deriv g σ₁ * deriv g σ₂ < 0) := by
  set a := iteratedDeriv 2 g 0
  set F : ℝ × ℝ → ℝ := fun p ↦ a * (g p.1 - g 0 - p.2)
  have hF : ContDiffAt ℝ 2 F 0 :=
    contDiffAt_const.mul (((hg.comp (0 : ℝ × ℝ) contDiffAt_fst).sub contDiffAt_const).sub
      contDiffAt_snd)
  have hdF (u : ℝ) : deriv (fun σ ↦ F (σ, u)) = fun σ ↦ a * deriv g σ := by
    simp only [F, deriv_const_mul_field', sub_sub, deriv_sub_const]
  have hb : deriv (fun u ↦ F (0, u)) 0 = -a := by
    rw [show (fun u ↦ F (0, u)) = fun u ↦ -a * u from funext fun u ↦ by simp only [F]; ring]
    simp
  have h2F : iteratedDeriv 2 (fun σ ↦ F (σ, 0)) 0 = a * a := by
    rw [iteratedDeriv_succ', iteratedDeriv_one, hdF, deriv_const_mul_field']
    simp only [a, iteratedDeriv_succ', iteratedDeriv_zero]
  have hfold := eventually_fold hF (by simp [F]) (by simp [hdF, h₁])
    (by rw [h2F]; exact mul_self_pos.2 h₂) (by rw [hb]; exact neg_ne_zero.2 h₂)
  have hst : Tendsto (fun s ↦ s - g 0) (𝓝 (g 0)) (𝓝 0) := by
    simpa using (continuous_sub_right (g 0)).tendsto (g 0)
  filter_upwards [hfold] with δ hδ
  filter_upwards [hst.eventually hδ] with s ⟨hlt, heq, hgt⟩
  rw [hb] at hlt hgt
  have hFs (σ : ℝ) : F (σ, s - g 0) = 0 ↔ g σ = s := by
    simp only [F, mul_eq_zero, h₂, false_or]
    constructor <;> intro h <;> linarith
  have hset : {σ ∈ Ioo (-δ) δ | F (σ, s - g 0) = 0} = {σ ∈ Ioo (-δ) δ | g σ = s} := by
    ext σ
    simp [hFs]
  refine ⟨fun h σ hσ hgσ ↦ ?_, fun h ↦ hset ▸ heq (by rw [h, sub_self]), fun h ↦ ?_⟩
  · have := hlt (by nlinarith) σ hσ
    rw [(hFs σ).2 hgσ] at this
    exact lt_irrefl 0 this
  · obtain ⟨σ₁, hσ₁, σ₂, hσ₂, hs, h₁, h₂'⟩ := hgt (by nlinarith)
    refine ⟨σ₁, hσ₁, σ₂, hσ₂, hset ▸ hs, ?_⟩
    rw [hdF] at h₁ h₂'
    nlinarith [mul_neg_of_neg_of_pos h₁ h₂']

/-- **The two solutions on nested intervals agree.** If `g` takes the value `s` on `(-δ₀, δ₀)`
exactly at `x₁ < 0 < x₂`, and on the smaller interval `(-δ₁, δ₁)` exactly at `σ₁ < 0 < σ₂`, then
`σ₁ = x₁` and `σ₂ = x₂`. -/
theorem eq_and_eq_of_setOf_eq_pair {g : ℝ → ℝ} {s δ₀ δ₁ x₁ x₂ σ₁ σ₂ : ℝ} (hδ : δ₁ ≤ δ₀)
    (hx₁ : x₁ < 0) (hx₂ : 0 < x₂) (h₀ : {σ ∈ Ioo (-δ₀) δ₀ | g σ = s} = {x₁, x₂})
    (hσ₁ : σ₁ < 0) (hσ₂ : 0 < σ₂) (h₁ : {σ ∈ Ioo (-δ₁) δ₁ | g σ = s} = {σ₁, σ₂}) :
    σ₁ = x₁ ∧ σ₂ = x₂ := by
  have hsub : ∀ σ ∈ ({σ₁, σ₂} : Set ℝ), σ ∈ ({x₁, x₂} : Set ℝ) := fun σ hσ ↦ by
    rw [← h₁] at hσ
    rw [← h₀]
    exact ⟨⟨by linarith [hσ.1.1], by linarith [hσ.1.2]⟩, hσ.2⟩
  refine ⟨(hsub σ₁ (by simp)).resolve_right fun h ↦ ?_,
    mem_singleton_iff.1 <| (hsub σ₂ (by simp)).resolve_left fun h ↦ ?_⟩
  · linarith [mem_singleton_iff.1 h]
  · linarith

/-! ### The equivariant pitchfork -/

/-- The facts about `F` at a point `(x, t)` of the box around a pitchfork point. -/
private structure PitchforkBox (F : ℝ × ℝ → ℝ) (x t : ℝ) : Prop where
  hasDerivAt_fst : HasDerivAt (fun y => F (y, t)) (partialFst F 1 (x, t)) x
  continuousAt_snd : ContinuousAt (fun s => F (x, s)) t
  hasDerivAt_partialFst_snd :
    HasDerivAt (fun s => partialFst F 1 (x, s)) (fderiv ℝ (partialFst F 1) (x, t) (0, 1)) t
  continuousAt_partialFst_two : ContinuousAt (fun y => partialFst F 2 (y, t)) x
  deriv3_pos : 0 < deriv^[3] (fun y => F (y, t)) x
  mul_deriv_snd_pos :
    0 < deriv (fun s => deriv (fun y => F (y, s)) 0) 0 * fderiv ℝ (partialFst F 1) (x, t) (0, 1)
  odd : F (-x, t) = -F (x, t)

/-- Near a pitchfork point there is a box `|x|, |t| < δ₀` on which `F` is odd, its first three
`x`-derivatives behave well, `∂ₓ³ F > 0` and `b ∂ₜ ∂ₓ F > 0`, where `b = ∂ₜ ∂ₓ F (0, 0)`. -/
private theorem exists_pitchfork_box (hF : ContDiffAt ℝ 3 F 0)
    (hodd : ∀ᶠ p in 𝓝 (0 : ℝ × ℝ), F (-p.1, p.2) = -F p)
    (h₃ : 0 < iteratedDeriv 3 (fun x => F (x, 0)) 0)
    (hb : deriv (fun s => deriv (fun x => F (x, s)) 0) 0 ≠ 0) :
    ∃ δ₀ > 0, ∀ {x t : ℝ}, |x| < δ₀ → |t| < δ₀ → PitchforkBox F x t := by
  set b := deriv (fun s => deriv (fun x => F (x, s)) 0) 0 with hb_def
  have hF0 : ContDiffAt ℝ (3 : ℕ) F (0, 0) := by
    rw [Prod.mk_zero_zero]
    exact_mod_cast hF
  rw [← Prod.mk_zero_zero] at hodd
  have hE₁ := eventually_contDiffAt_partialFst hF0 1 (by norm_num)
  have hcd₁ : ContDiffAt ℝ (2 : ℕ) (partialFst F 1) (0, 0) := hE₁.self_of_nhds
  -- `b` is the derivative in `t` of `partialFst F 1` at the origin.
  have hbF : fderiv ℝ (partialFst F 1) (0, 0) (0, 1) = b :=
    (hasDerivAt_slice_right (hcd₁.differentiableAt two_ne_zero)).deriv.symm
  have hval : 0 < partialFst F 3 (0, 0) := by
    rw [partialFst, ← iteratedDeriv_eq_iterate]
    exact h₃
  have hcontt : ContinuousAt (fun p => b * fderiv ℝ (partialFst F 1) p (0, 1)) (0, 0) :=
    continuousAt_const.mul ((hcd₁.continuousAt_fderiv two_ne_zero).clm_apply continuousAt_const)
  have hev : ∀ᶠ p in 𝓝 ((0 : ℝ), (0 : ℝ)), ContDiffAt ℝ (3 : ℕ) F p ∧
      ContDiffAt ℝ (2 : ℕ) (partialFst F 1) p ∧ ContDiffAt ℝ (1 : ℕ) (partialFst F 2) p ∧
      0 < partialFst F 3 p ∧ 0 < b * fderiv ℝ (partialFst F 1) p (0, 1) ∧
      F (-p.1, p.2) = -F p := by
    filter_upwards [hF0.eventually (by simp), hE₁,
      eventually_contDiffAt_partialFst hF0 2 (by norm_num),
      ((eventually_contDiffAt_partialFst hF0 3 le_rfl).self_of_nhds.continuousAt).eventually
        (lt_mem_nhds hval),
      hcontt.eventually (lt_mem_nhds (show (0 : ℝ) < b * fderiv ℝ (partialFst F 1) (0, 0) (0, 1)
        by rw [hbF]; exact mul_self_pos.2 hb)), hodd] with p h₁ h₂ h₃ h₄ h₅ h₆
    exact ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩
  obtain ⟨δ₀, hδ₀, hbox⟩ := Metric.eventually_nhds_iff_ball.1 hev
  refine ⟨δ₀, hδ₀, fun hx ht => ?_⟩
  obtain ⟨hcd, hcd₁, hcd₂, h3pos, hbpos, hoddp⟩ := hbox _ (mem_ball_of_abs_lt hx ht)
  dsimp only at hoddp
  exact ⟨(hasDerivAt_slice_left (hcd.differentiableAt (by simp))).differentiableAt.hasDerivAt,
    (hasDerivAt_slice_right (hcd.differentiableAt (by simp))).continuousAt,
    hasDerivAt_slice_right (hcd₁.differentiableAt two_ne_zero),
    (hasDerivAt_slice_left (hcd₂.differentiableAt one_ne_zero)).continuousAt, h3pos, hbpos,
    hoddp⟩

/-- On the box around a pitchfork point, the slices are strictly convex on `[0, δ]`. -/
private theorem strictConvexOn_of_pitchforkBox {δ₀ δ t : ℝ}
    (hbox : ∀ {x t : ℝ}, |x| < δ₀ → |t| < δ₀ → PitchforkBox F x t) (hδ : 0 < δ) (hδδ₀ : δ < δ₀)
    (ht : |t| < δ₀) : StrictConvexOn ℝ (Icc 0 δ) (fun x => F (x, t)) := by
  have hIcc {x : ℝ} (hx : x ∈ Icc 0 δ) : |x| < δ₀ :=
    abs_lt.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hc2 : ContinuousOn (fun y => partialFst F 2 (y, t)) (Icc 0 δ) := fun x hx =>
    (hbox (hIcc hx) ht).continuousAt_partialFst_two.continuousWithinAt
  refine strictConvexOn_Icc_of_deriv3_pos (fun x hx =>
    (hbox (hIcc hx) ht).hasDerivAt_fst.continuousAt.continuousWithinAt) ?_ hc2
    fun x hx => (hbox (hIcc (Ioo_subset_Icc_self hx)) ht).deriv3_pos
  -- The slice is odd near `0`, so its second derivative vanishes there.
  rw [← iteratedDeriv_eq_iterate, iteratedDeriv_two_eq_zero_of_eventually_odd]
  filter_upwards [Ioo_mem_nhds (neg_neg_of_pos (hδ.trans hδδ₀)) (hδ.trans hδδ₀)] with y hy
  exact (hbox (abs_lt.2 hy) ht).odd

/-- **The equivariant pitchfork.** Let `F : ℝ × ℝ → ℝ` be `C³` near the origin and odd in its
first variable, `F (-x, t) = -F (x, t)`, with `∂ₓ F (0, 0) = 0`, `∂ₓ³ F (0, 0) > 0` and
`b = ∂ₜ ∂ₓ F (0, 0) ≠ 0`. Then for all small `δ > 0` and all `t` near `0`: if `b t ≥ 0`, the only
zero of `x ↦ F (x, t)` in `(-δ, δ)` is `0`, and `∂ₓ F (0, t) > 0` when `b t > 0`; if `b t < 0`,
then `∂ₓ F (0, t) < 0` and the zeros in `(-δ, δ)` are exactly `-x₀, 0, x₀` for some
`x₀ ∈ (0, δ)`, with `∂ₓ F (-x₀, t) = ∂ₓ F (x₀, t) > 0`. -/
theorem eventually_pitchfork (hF : ContDiffAt ℝ 3 F 0)
    (hodd : ∀ᶠ p in 𝓝 (0 : ℝ × ℝ), F (-p.1, p.2) = -F p)
    (h₁ : deriv (fun x => F (x, 0)) 0 = 0) (h₃ : 0 < iteratedDeriv 3 (fun x => F (x, 0)) 0)
    (hb : deriv (fun s => deriv (fun x => F (x, s)) 0) 0 ≠ 0) :
    ∀ᶠ δ in 𝓝[>] 0, ∀ᶠ t in 𝓝 0,
      (0 ≤ deriv (fun s => deriv (fun x => F (x, s)) 0) 0 * t →
        {x ∈ Ioo (-δ) δ | F (x, t) = 0} = {0}) ∧
      (0 < deriv (fun s => deriv (fun x => F (x, s)) 0) 0 * t →
        0 < deriv (fun x => F (x, t)) 0) ∧
      (deriv (fun s => deriv (fun x => F (x, s)) 0) 0 * t < 0 →
        deriv (fun x => F (x, t)) 0 < 0 ∧ ∃ x₀ ∈ Ioo 0 δ,
          {x ∈ Ioo (-δ) δ | F (x, t) = 0} = {-x₀, 0, x₀} ∧
          0 < deriv (fun x => F (x, t)) x₀ ∧
          deriv (fun x => F (x, t)) (-x₀) = deriv (fun x => F (x, t)) x₀) := by
  obtain ⟨δ₀, hδ₀, hbox⟩ := exists_pitchfork_box hF hodd h₃ hb
  set b := deriv (fun s => deriv (fun x => F (x, s)) 0) 0
  have h0δ₀ : |(0 : ℝ)| < δ₀ := by simpa using hδ₀
  have h00 : partialFst F 1 (0, 0) = 0 := by
    rw [← (hbox h0δ₀ h0δ₀).hasDerivAt_fst.deriv]
    exact h₁
  -- `∂ₓ F (0, t)` has the sign of `b t`.
  have hsign : ∀ {t : ℝ}, |t| < δ₀ →
      (0 < b * t → 0 < partialFst F 1 (0, t)) ∧ (b * t < 0 → partialFst F 1 (0, t) < 0) :=
    fun ht => by
      simpa only [h00, sub_zero] using lt_and_lt_of_hasDerivAt_of_mul_pos (a := 0) ordConnected_Ioo
        (fun s hs => (hbox h0δ₀ (abs_lt.2 hs)).hasDerivAt_partialFst_snd.continuousAt
          |>.continuousWithinAt)
        (fun s hs => (hbox h0δ₀ (abs_lt.2 (interior_subset hs))).hasDerivAt_partialFst_snd)
        (fun s hs => (hbox h0δ₀ (abs_lt.2 (interior_subset hs))).mul_deriv_snd_pos)
        ⟨by linarith, hδ₀⟩ (abs_lt.1 ht)
  filter_upwards [Ioo_mem_nhdsGT hδ₀] with δ ⟨hδpos, hδδ₀⟩
  have hδabs : |δ| < δ₀ := by rwa [abs_of_pos hδpos]
  have hzero : F (0, 0) = 0 := by
    have := (hbox h0δ₀ h0δ₀).odd
    rw [neg_zero] at this
    linarith
  -- The slice at `t = 0` lies above its horizontal tangent at `0`.
  have hFδ0 : 0 < F (δ, 0) := by
    have hconv0 := strictConvexOn_of_pitchforkBox hbox hδpos hδδ₀ h0δ₀
    have h := hconv0.mul_sub_lt_sub_of_hasDerivWithinAt ⟨le_rfl, hδpos.le⟩ ⟨hδpos.le, le_rfl⟩
      hδpos.ne (hbox h0δ₀ h0δ₀).hasDerivAt_fst.hasDerivWithinAt
    rwa [h00, zero_mul, hzero, sub_zero] at h
  filter_upwards [Ioo_mem_nhds (neg_neg_of_pos hδ₀) hδ₀,
    (hbox hδabs h0δ₀).continuousAt_snd.eventually (lt_mem_nhds hFδ0)] with t ht hFδt
  replace ht := abs_lt.2 ht
  have hconv := strictConvexOn_of_pitchforkBox hbox hδpos hδδ₀ ht
  have hoddδ : ∀ x ∈ Ioo (-δ) δ, ∀ᶠ y in 𝓝 x, F (-y, t) = -F (y, t) := fun x hx => by
    filter_upwards [isOpen_Ioo.mem_nhds (Ioo_subset_Ioo (neg_le_neg hδδ₀.le) hδδ₀.le hx)] with y hy
    exact (hbox (abs_lt.2 hy) ht).odd
  have hderiv0 : deriv (fun x => F (x, t)) 0 = partialFst F 1 (0, t) :=
    (hbox h0δ₀ ht).hasDerivAt_fst.deriv
  refine ⟨fun hbt => pitchfork_slice_of_nonneg hδpos hconv
    (fun x hx => (hoddδ x hx).self_of_nhds) (hbox h0δ₀ ht).hasDerivAt_fst ?_,
    fun hbt => hderiv0 ▸ (hsign ht).1 hbt, fun hbt => ?_⟩
  · rcases hbt.lt_or_eq with hbt | hbt
    · exact ((hsign ht).1 hbt).le
    · rcases mul_eq_zero.1 hbt.symm with hb0 | rfl
      · exact absurd hb0 hb
      · exact h00.ge
  · have hneg : deriv (fun x => F (x, t)) 0 < 0 := hderiv0 ▸ (hsign ht).2 hbt
    exact ⟨hneg, pitchfork_slice_of_neg hδpos hconv hoddδ (fun x hx =>
      (hbox (by rw [abs_of_nonneg hx.1]; linarith [hx.2]) ht).hasDerivAt_fst.differentiableAt)
      hneg hFδt⟩

end TauCeti
