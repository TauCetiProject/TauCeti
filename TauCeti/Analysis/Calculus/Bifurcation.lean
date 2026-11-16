/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Slope
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Analysis.Calculus.FDeriv.Prod

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

These are the local models of the one-parameter bifurcations of pseudoholomorphic curves along a
generic path of almost complex structures, after the finite-dimensional reduction of their normal
deformation problem to a kernel and cokernel of dimension one
(`ContinuousLinearMap.FredholmPackage.obstructionMap`). An ordinary curve, or a torus, is born or
dies together with a partner of the opposite determinant sign through a fold. A torus `C` undergoes
period doubling through a pitchfork: the reduced equation on the double cover of `C` is odd under
the deck transformation, its trivial zero is the double cover of `C` itself, whose determinant sign
for the deck-twisted normal operator changes, and the orbit `{-x₀, x₀}` is a single embedded torus
in twice the class of `C`. The change in the
signed count of orbits is the reason Taubes weights multiply covered tori by the four-twist series
rather than by their determinant signs alone. The orientation of these reductions and the matching
of the signs with the labels of `TauCeti.torusWeightSeries` are separate.

The proofs are elementary. Near `(0, 0)` the relevant derivative `∂ₓ² F` (for the fold) or
`∂ₓ³ F` (for the pitchfork) is positive, so each slice `x ↦ F (x, t)` is strictly convex on
`[-δ, δ]` (respectively on `[0, δ]`, using `∂ₓ² F (0, t) = 0` for an odd slice). A strictly convex
function has at most two zeros on an interval (`StrictConvexOn.eq_or_eq_of_apply_eq`), and its
derivative is negative at the first and positive at the second. The zeros are produced by the
intermediate value theorem, and the dependence on `t` enters only through the sign of `F (0, t)`
(respectively `∂ₓ F (0, t)`), which is that of `b t`.

## Main results

* `TauCeti.eventually_fold`: the zeros near a fold point and their signs.
* `TauCeti.eventually_pitchfork`: the zeros near a pitchfork point of an odd family and their
  signs.
* `StrictConvexOn.eq_or_eq_of_apply_eq`: a strictly convex function takes each value at most twice.
* `TauCeti.deriv_neg_eq_of_eventually_odd`, `TauCeti.deriv_neg_eq_neg_of_eventually_even`,
  `TauCeti.iteratedDeriv_two_eq_zero_of_eventually_odd`: derivatives of functions that are odd or
  even near a point.

## References

* M. Golubitsky and D. G. Schaeffer, *Singularities and Groups in Bifurcation Theory, Vol. I*,
  Applied Mathematical Sciences 51, Springer, 1985, Chapters II–III and VI.
* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential Geom.
  44 (1996), 818–893.
-/

public section

open Filter Set
open scoped Topology

/-- A strictly convex function takes each value at most twice: if `f x = f y = c` with `x < y`,
then every `z` with `f z = c` is `x` or `y`. -/
theorem StrictConvexOn.eq_or_eq_of_apply_eq {S : Set ℝ} {f : ℝ → ℝ} {x y z c : ℝ}
    (hf : StrictConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S) (hxy : x < y)
    (hfx : f x = c) (hfy : f y = c) (hfz : f z = c) : z = x ∨ z = y := by
  by_contra! h
  rcases lt_trichotomy z x with hzx | hzx | hxz
  · have := hf.slope_strict_mono_adjacent hz hy hzx hxy
    rw [hfx, hfy, hfz, sub_self, zero_div, zero_div] at this
    exact lt_irrefl _ this
  · exact h.1 hzx
  rcases lt_trichotomy z y with hzy | hzy | hyz
  · have := hf.slope_strict_mono_adjacent hx hy hxz hzy
    rw [hfx, hfy, hfz, sub_self, zero_div, zero_div] at this
    exact lt_irrefl _ this
  · exact h.2 hzy
  · have := hf.slope_strict_mono_adjacent hx hz hxy hyz
    rw [hfx, hfy, hfz, sub_self, zero_div, zero_div] at this
    exact lt_irrefl _ this

namespace TauCeti

/-! ### Derivatives of functions that are odd or even near a point -/

/-- If `f` is odd near `x`, then `f'(-x) = f'(x)`. -/
theorem deriv_neg_eq_of_eventually_odd {f : ℝ → ℝ} {x : ℝ}
    (h : ∀ᶠ y in 𝓝 x, f (-y) = -f y) : deriv f (-x) = deriv f x := by
  have h' : f =ᶠ[𝓝 x] fun y => -f (-y) := h.mono fun y hy => by beta_reduce; rw [hy, neg_neg]
  rw [h'.deriv_eq, deriv.fun_neg, deriv_comp_neg, neg_neg]

/-- If `f` is even near `x`, then `f'(-x) = -f'(x)`. -/
theorem deriv_neg_eq_neg_of_eventually_even {f : ℝ → ℝ} {x : ℝ}
    (h : ∀ᶠ y in 𝓝 x, f (-y) = f y) : deriv f (-x) = -deriv f x := by
  have h' : f =ᶠ[𝓝 x] fun y => f (-y) := h.mono fun y hy => hy.symm
  rw [h'.deriv_eq, deriv_comp_neg, neg_neg]

/-- The second derivative at `0` of a function that is odd near `0` vanishes. -/
theorem iteratedDeriv_two_eq_zero_of_eventually_odd {f : ℝ → ℝ}
    (h : ∀ᶠ y in 𝓝 0, f (-y) = -f y) : iteratedDeriv 2 f 0 = 0 := by
  have h₁ : ∀ᶠ y in 𝓝 (0 : ℝ), deriv f (-y) = deriv f y :=
    h.eventually_nhds.mono fun y hy => deriv_neg_eq_of_eventually_odd hy
  have h₂ := deriv_neg_eq_neg_of_eventually_even h₁
  rw [neg_zero] at h₂
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  linarith

/-! ### Partial derivatives of a function of two variables -/

variable {F : ℝ × ℝ → ℝ}

/-- The iterated partial derivatives of `F` in its first variable, as Fréchet derivatives. -/
private noncomputable def partialFst (F : ℝ × ℝ → ℝ) : ℕ → ℝ × ℝ → ℝ
  | 0 => F
  | k + 1 => fun p => fderiv ℝ (partialFst F k) p (1, 0)

private theorem partialFst_zero : partialFst F 0 = F := rfl

private theorem partialFst_succ (k : ℕ) :
    partialFst F (k + 1) = fun p => fderiv ℝ (partialFst F k) p (1, 0) := rfl

/-- Near a point where `F` is `Cⁿ`, the `k`-th derivatives of the slices `y ↦ F (y, t)` are the
values of the `C^(n-k)` function `partialFst F k`. -/
private theorem eventually_partialFst {n : ℕ} {p₀ : ℝ × ℝ} (hF : ContDiffAt ℝ n F p₀) :
    ∀ k ≤ n, ∀ᶠ p in 𝓝 p₀, ContDiffAt ℝ (n - k : ℕ) (partialFst F k) p ∧
      deriv^[k] (fun y => F (y, p.2)) =ᶠ[𝓝 p.1] fun y => partialFst F k (y, p.2) := by
  intro k
  induction k with
  | zero =>
    intro _
    exact (hF.eventually (by simp)).mono fun p hp => ⟨by simpa [partialFst_zero] using hp, .rfl⟩
  | succ k ih =>
    intro hk
    filter_upwards [(ih (by omega)).eventually_nhds] with p hp
    have hcd : ContDiffAt ℝ ((n - (k + 1) : ℕ) + 1 : ℕ) (partialFst F k) p := by
      rw [show n - (k + 1) + 1 = n - k by omega]
      exact hp.self_of_nhds.1
    refine ⟨?_, ?_⟩
    · rw [partialFst_succ]
      exact (hcd.fderiv_right (by push_cast; rfl)).clm_apply contDiffAt_const
    · have ht : Tendsto (fun y : ℝ => (y, p.2)) (𝓝 p.1) (𝓝 p) := by
        simpa using ((continuous_id.prodMk continuous_const :
          Continuous fun y : ℝ => (y, p.2)).tendsto p.1)
      filter_upwards [ht.eventually hp] with y hy
      rw [Function.iterate_succ_apply', hy.2.deriv_eq, partialFst_succ]
      exact (hasDerivAt_slice_left
        ((hy.1.differentiableAt (by exact_mod_cast (show n - k ≠ 0 by omega))))).deriv

/-- Pointwise form of `eventually_partialFst`. -/
private theorem eventually_iterate_deriv_eq {n : ℕ} {p₀ : ℝ × ℝ} (hF : ContDiffAt ℝ n F p₀)
    {k : ℕ} (hk : k ≤ n) :
    ∀ᶠ p in 𝓝 p₀, deriv^[k] (fun y => F (y, p.2)) p.1 = partialFst F k p :=
  (eventually_partialFst hF k hk).mono fun _ hp => hp.2.self_of_nhds

/-! ### Zeros of the slices -/

/-- If `b f'` is positive on `(-δ₀, δ₀)`, where `f'` is the derivative of `f`, then `f t - f 0` has
the sign of `b t` for `|t| < δ₀`. -/
private theorem sign_sub_of_hasDerivAt {f f' : ℝ → ℝ} {b δ₀ t : ℝ}
    (hd : ∀ s ∈ Ioo (-δ₀) δ₀, HasDerivAt f (f' s) s) (hpos : ∀ s ∈ Ioo (-δ₀) δ₀, 0 < b * f' s)
    (ht : |t| < δ₀) : (0 < b * t → f 0 < f t) ∧ (b * t < 0 → f t < f 0) := by
  have ht' := abs_lt.1 ht
  have h0 : (0 : ℝ) ∈ Ioo (-δ₀) δ₀ := ⟨by linarith, by linarith⟩
  have hmono : StrictMonoOn (fun s => b * f s) (Ioo (-δ₀) δ₀) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioo _ _)
      (fun s hs => ((hd s hs).continuousAt.const_mul b).continuousWithinAt) fun s hs => ?_
    rw [interior_Ioo] at hs
    rw [((hd s hs).const_mul b).deriv]
    exact hpos s hs
  have key : t ≠ 0 → 0 < b * t * (f t - f 0) := by
    intro ht0
    have e : b * t * (f t - f 0) = t * (b * f t - b * f 0) := by ring
    rw [e]
    rcases ht0.lt_or_gt with h | h
    · exact mul_pos_of_neg_of_neg h (sub_neg.2 (hmono ht' h0 h))
    · exact mul_pos h (sub_pos.2 (hmono h0 ht' h))
  refine ⟨fun hbt => ?_, fun hbt => ?_⟩
  · exact sub_pos.1 ((pos_iff_pos_of_mul_pos (key (by rintro rfl; simp at hbt))).1 hbt)
  · exact sub_neg.1 ((neg_iff_neg_of_mul_pos (key (by rintro rfl; simp at hbt))).1 hbt)

/-- A strictly convex function vanishing at `0`, with nonnegative derivative there, is positive to
the right of `0`. -/
private theorem pos_of_strictConvexOn_of_pos {g : ℝ → ℝ} {S : Set ℝ} {d y : ℝ}
    (hg : StrictConvexOn ℝ S g) (h0 : (0 : ℝ) ∈ S) (hy : y ∈ S) (hg0 : g 0 = 0)
    (hd : HasDerivAt g d 0) (hd0 : 0 ≤ d) (hy0 : 0 < y) : 0 < g y := by
  have h := hg.lt_slope_of_hasDerivAt h0 hy hy0 hd
  rw [slope_def_field, hg0, sub_zero, sub_zero] at h
  exact (div_pos_iff_of_pos_right hy0).1 (hd0.trans_lt h)

/-- A strictly convex function vanishing at `0`, with nonpositive derivative there, is positive to
the left of `0`. -/
private theorem pos_of_strictConvexOn_of_neg {g : ℝ → ℝ} {S : Set ℝ} {d y : ℝ}
    (hg : StrictConvexOn ℝ S g) (h0 : (0 : ℝ) ∈ S) (hy : y ∈ S) (hg0 : g 0 = 0)
    (hd : HasDerivAt g d 0) (hd0 : d ≤ 0) (hy0 : y < 0) : 0 < g y := by
  have h := hg.slope_lt_of_hasDerivAt hy h0 hy0 hd
  rw [slope_def_field, hg0, zero_sub, zero_sub, neg_div_neg_eq] at h
  by_contra! hgy
  have : 0 ≤ g y / y := div_nonneg_of_nonpos hgy hy0.le
  linarith

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

/-- A function that is odd near `0`, whose second derivative is continuous and whose third
derivative is positive on `(-δ₀, δ₀)`, is strictly convex on `[0, δ]` for `0 < δ < δ₀`. -/
private theorem strictConvexOn_Icc_of_eventually_odd {g : ℝ → ℝ} {δ δ₀ : ℝ} (hδ : 0 < δ)
    (hδδ₀ : δ < δ₀) (hc : ContinuousOn g (Icc 0 δ)) (hodd : ∀ᶠ y in 𝓝 0, g (-y) = -g y)
    (hc2 : ContinuousOn (deriv^[2] g) (Ioo (-δ₀) δ₀))
    (h3 : ∀ x ∈ Ioo (-δ₀) δ₀, 0 < deriv^[3] g x) : StrictConvexOn ℝ (Icc 0 δ) g := by
  have h0 : (0 : ℝ) ∈ Ioo (-δ₀) δ₀ := ⟨by linarith, by linarith⟩
  have h2zero : deriv^[2] g 0 = 0 := by
    rw [← iteratedDeriv_eq_iterate]
    exact iteratedDeriv_two_eq_zero_of_eventually_odd hodd
  have hmono : StrictMonoOn (deriv^[2] g) (Ioo (-δ₀) δ₀) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioo _ _) hc2 fun y hy => ?_
    rw [interior_Ioo] at hy
    rw [← Function.iterate_succ_apply' deriv]
    exact h3 y hy
  refine strictConvexOn_of_deriv2_pos (convex_Icc _ _) hc fun y hy => ?_
  rw [interior_Icc] at hy
  rw [← h2zero]
  exact hmono h0 ⟨by linarith [hy.1], by linarith [hy.2]⟩ hy.1

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
  have hpos : ∀ y ∈ Ioc 0 δ, 0 < g y := fun y hy =>
    pos_of_strictConvexOn_of_pos hconv ⟨le_rfl, hδ.le⟩ ⟨hy.1.le, hy.2⟩ hg0 hd hd0 hy.1
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

/-- Near a fold point there is a box `|x|, |t| < δ₀` on which `F` is differentiable,
`∂ₓ² F > 0` and `b ∂ₜ F > 0`, where `b = ∂ₜ F (0, 0)`. -/
private theorem exists_fold_box (hF : ContDiffAt ℝ 2 F 0)
    (h₂ : 0 < iteratedDeriv 2 (fun x => F (x, 0)) 0) (hb : deriv (fun s => F (0, s)) 0 ≠ 0) :
    ∃ δ₀ > 0, ∀ {x t : ℝ}, |x| < δ₀ → |t| < δ₀ →
      HasDerivAt (fun y => F (y, t)) (fderiv ℝ F (x, t) (1, 0)) x ∧
      HasDerivAt (fun s => F (x, s)) (fderiv ℝ F (x, t) (0, 1)) t ∧
      0 < deriv^[2] (fun y => F (y, t)) x ∧
      0 < deriv (fun s => F (0, s)) 0 * fderiv ℝ F (x, t) (0, 1) := by
  set b := deriv (fun s => F (0, s)) 0
  have hF0 : ContDiffAt ℝ (2 : ℕ) F ((0 : ℝ), (0 : ℝ)) := hF
  have hbF : fderiv ℝ F (0, 0) (0, 1) = b :=
    (hasDerivAt_slice_right (hF0.differentiableAt two_ne_zero)).deriv.symm
  have hval : 0 < partialFst F 2 (0, 0) := by
    rw [← (eventually_iterate_deriv_eq hF0 le_rfl).self_of_nhds, ← iteratedDeriv_eq_iterate]
    exact h₂
  have hcontt : ContinuousAt (fun p => b * fderiv ℝ F p (0, 1)) (0, 0) :=
    continuousAt_const.mul ((hF0.continuousAt_fderiv two_ne_zero).clm_apply continuousAt_const)
  have hev : ∀ᶠ p in 𝓝 ((0 : ℝ), (0 : ℝ)), ContDiffAt ℝ (2 : ℕ) F p ∧
      deriv^[2] (fun y => F (y, p.2)) p.1 = partialFst F 2 p ∧ 0 < partialFst F 2 p ∧
      0 < b * fderiv ℝ F p (0, 1) := by
    filter_upwards [hF0.eventually (by simp), eventually_iterate_deriv_eq hF0 le_rfl,
      ((eventually_partialFst hF0 2 le_rfl).self_of_nhds.1.continuousAt).eventually
        (lt_mem_nhds hval),
      hcontt.eventually (lt_mem_nhds (show (0 : ℝ) < b * fderiv ℝ F (0, 0) (0, 1) by
        rw [hbF]; exact mul_self_pos.2 hb))] with p h₁ h₂ h₃ h₄
    exact ⟨h₁, h₂, h₃, h₄⟩
  obtain ⟨δ₀, hδ₀, hbox⟩ := Metric.eventually_nhds_iff_ball.1 hev
  refine ⟨δ₀, hδ₀, fun hx ht => ?_⟩
  obtain ⟨hcd, h2, h2pos, hbpos⟩ := hbox _ (mem_ball_of_abs_lt hx ht)
  have hdF := hcd.differentiableAt two_ne_zero
  dsimp only at h2
  exact ⟨hasDerivAt_slice_left hdF, hasDerivAt_slice_right hdF, h2 ▸ h2pos, hbpos⟩

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
  have h₀' : F (0, 0) = 0 := h₀
  have h0δ₀ : |(0 : ℝ)| < δ₀ := by simpa using hδ₀
  -- The slices are strictly convex on `[-δ, δ]` for `δ < δ₀`.
  have hconv : ∀ {δ t : ℝ}, δ < δ₀ → |t| < δ₀ →
      StrictConvexOn ℝ (Icc (-δ) δ) (fun x => F (x, t)) := fun hδ ht =>
    strictConvexOn_of_deriv2_pos (convex_Icc _ _) (fun x hx =>
      (hbox ((abs_le.2 hx).trans_lt hδ) ht).1.continuousAt.continuousWithinAt) fun x hx =>
      (hbox ((abs_le.2 (Ioo_subset_Icc_self (by rwa [interior_Icc] at hx))).trans_lt hδ)
        ht).2.2.1
  -- The slice at `t = 0` is positive away from `0`.
  have hpos0 : ∀ {x : ℝ}, |x| < δ₀ → x ≠ 0 → 0 < F (x, 0) := by
    intro x hx hx0
    have hd0 : HasDerivAt (fun y => F (y, 0)) 0 0 := by
      have h := (hbox h0δ₀ h0δ₀).1
      rwa [← h.deriv, h₁] at h
    have h0 : (0 : ℝ) ∈ Icc (-|x|) |x| := ⟨by simp, abs_nonneg x⟩
    have hxm : x ∈ Icc (-|x|) |x| := ⟨neg_abs_le x, le_abs_self x⟩
    rcases hx0.lt_or_gt with h | h
    · exact pos_of_strictConvexOn_of_neg (hconv hx h0δ₀) h0 hxm h₀' hd0 le_rfl h
    · exact pos_of_strictConvexOn_of_pos (hconv hx h0δ₀) h0 hxm h₀' hd0 le_rfl h
  -- Along vertical lines, `F (x, t) - F (x, 0)` has the sign of `b t`.
  have hsign : ∀ {x t : ℝ}, |x| < δ₀ → |t| < δ₀ → (0 < deriv (fun s => F (0, s)) 0 * t →
      F (x, 0) < F (x, t)) ∧ (deriv (fun s => F (0, s)) 0 * t < 0 → F (x, t) < F (x, 0)) :=
    fun hx ht => sign_sub_of_hasDerivAt (fun s hs => (hbox hx (abs_lt.2 hs)).2.1)
      (fun s hs => (hbox hx (abs_lt.2 hs)).2.2.2) ht
  filter_upwards [Ioo_mem_nhdsGT hδ₀] with δ ⟨hδpos, hδδ₀⟩
  have hδabs : |δ| < δ₀ := by rwa [abs_of_pos hδpos]
  have hδabs' : |-δ| < δ₀ := by rwa [abs_neg]
  filter_upwards [Ioo_mem_nhds (neg_neg_of_pos hδ₀) hδ₀,
    (hbox hδabs h0δ₀).2.1.continuousAt.eventually (lt_mem_nhds (hpos0 hδabs hδpos.ne')),
    (hbox hδabs' h0δ₀).2.1.continuousAt.eventually
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
    exact fold_slice hδpos (hconv hδδ₀ ht)
      (fun x hx => (hbox ((abs_le.2 hx).trans_lt hδδ₀) ht).1.differentiableAt) hF0t hFn hFp

/-! ### The equivariant pitchfork -/

/-- Near a pitchfork point there is a box `|x|, |t| < δ₀` on which `F` is odd, its first three
`x`-derivatives behave well, `∂ₓ³ F > 0` and `b ∂ₜ ∂ₓ F > 0`, where `b = ∂ₜ ∂ₓ F (0, 0)`. -/
private theorem exists_pitchfork_box (hF : ContDiffAt ℝ 3 F 0)
    (hodd : ∀ᶠ p in 𝓝 (0 : ℝ × ℝ), F (-p.1, p.2) = -F p)
    (h₃ : 0 < iteratedDeriv 3 (fun x => F (x, 0)) 0)
    (hb : deriv (fun s => deriv (fun x => F (x, s)) 0) 0 ≠ 0) :
    ∃ δ₀ > 0, ∀ {x t : ℝ}, |x| < δ₀ → |t| < δ₀ →
      HasDerivAt (fun y => F (y, t)) (partialFst F 1 (x, t)) x ∧
      ContinuousAt (fun s => F (x, s)) t ∧
      HasDerivAt (fun s => partialFst F 1 (x, s)) (fderiv ℝ (partialFst F 1) (x, t) (0, 1)) t ∧
      ContinuousAt (fun y => partialFst F 2 (y, t)) x ∧
      deriv^[2] (fun y => F (y, t)) x = partialFst F 2 (x, t) ∧
      0 < deriv^[3] (fun y => F (y, t)) x ∧
      0 < deriv (fun s => deriv (fun x => F (x, s)) 0) 0 *
        fderiv ℝ (partialFst F 1) (x, t) (0, 1) ∧
      F (-x, t) = -F (x, t) := by
  set b := deriv (fun s => deriv (fun x => F (x, s)) 0) 0
  have hF0 : ContDiffAt ℝ (3 : ℕ) F ((0 : ℝ), (0 : ℝ)) := hF
  have hE₁ := eventually_partialFst hF0 1 (by norm_num)
  have hcd₁ : ContDiffAt ℝ (2 : ℕ) (partialFst F 1) (0, 0) := hE₁.self_of_nhds.1
  -- `b` is the derivative in `t` of `partialFst F 1` at the origin.
  have hbF : fderiv ℝ (partialFst F 1) (0, 0) (0, 1) = b := by
    have heq : (fun s => deriv (fun x => F (x, s)) 0) =ᶠ[𝓝 0]
        fun s => partialFst F 1 (0, s) :=
      (((continuous_const.prodMk continuous_id).tendsto 0).eventually hE₁).mono fun s hs =>
        hs.2.self_of_nhds
    rw [show b = deriv (fun s => deriv (fun x => F (x, s)) 0) 0 from rfl, heq.deriv_eq]
    exact (hasDerivAt_slice_right (hcd₁.differentiableAt two_ne_zero)).deriv.symm
  have hval : 0 < partialFst F 3 (0, 0) := by
    rw [← (eventually_iterate_deriv_eq hF0 le_rfl).self_of_nhds, ← iteratedDeriv_eq_iterate]
    exact h₃
  have hcontt : ContinuousAt (fun p => b * fderiv ℝ (partialFst F 1) p (0, 1)) (0, 0) :=
    continuousAt_const.mul ((hcd₁.continuousAt_fderiv two_ne_zero).clm_apply continuousAt_const)
  have hev : ∀ᶠ p in 𝓝 ((0 : ℝ), (0 : ℝ)), ContDiffAt ℝ (3 : ℕ) F p ∧
      ContDiffAt ℝ (2 : ℕ) (partialFst F 1) p ∧ ContDiffAt ℝ (1 : ℕ) (partialFst F 2) p ∧
      deriv^[2] (fun y => F (y, p.2)) p.1 = partialFst F 2 p ∧
      deriv^[3] (fun y => F (y, p.2)) p.1 = partialFst F 3 p ∧ 0 < partialFst F 3 p ∧
      0 < b * fderiv ℝ (partialFst F 1) p (0, 1) ∧ F (-p.1, p.2) = -F p := by
    filter_upwards [hF0.eventually (by simp), hE₁, eventually_partialFst hF0 2 (by norm_num),
      eventually_iterate_deriv_eq hF0 le_rfl,
      ((eventually_partialFst hF0 3 le_rfl).self_of_nhds.1.continuousAt).eventually
        (lt_mem_nhds hval),
      hcontt.eventually (lt_mem_nhds (show (0 : ℝ) < b * fderiv ℝ (partialFst F 1) (0, 0) (0, 1)
        by rw [hbF]; exact mul_self_pos.2 hb)), hodd] with p h₁ h₂ h₃ h₄ h₅ h₆ h₇
    exact ⟨h₁, h₂.1, h₃.1, h₃.2.self_of_nhds, h₄, h₅, h₆, h₇⟩
  obtain ⟨δ₀, hδ₀, hbox⟩ := Metric.eventually_nhds_iff_ball.1 hev
  refine ⟨δ₀, hδ₀, fun hx ht => ?_⟩
  obtain ⟨hcd, hcd₁, hcd₂, h2, h3, h3pos, hbpos, hoddp⟩ := hbox _ (mem_ball_of_abs_lt hx ht)
  dsimp only at h2 h3 hoddp
  refine ⟨hasDerivAt_slice_left (hcd.differentiableAt (by simp)),
    (hasDerivAt_slice_right (hcd.differentiableAt (by simp))).continuousAt,
    hasDerivAt_slice_right (hcd₁.differentiableAt two_ne_zero),
    (hasDerivAt_slice_left (hcd₂.differentiableAt one_ne_zero)).continuousAt, h2, h3 ▸ h3pos,
    hbpos, hoddp⟩

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
    rw [← (hbox h0δ₀ h0δ₀).1.deriv]
    exact h₁
  have hoddt : ∀ {t : ℝ}, |t| < δ₀ → ∀ x ∈ Ioo (-δ₀) δ₀, ∀ᶠ y in 𝓝 x, F (-y, t) = -F (y, t) :=
    fun ht x hx => by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy using (hbox (abs_lt.2 hy) ht).2.2.2.2.2.2.2
  -- The slices are strictly convex on `[0, δ]` for `0 < δ < δ₀`.
  have hconv : ∀ {δ t : ℝ}, 0 < δ → δ < δ₀ → |t| < δ₀ →
      StrictConvexOn ℝ (Icc 0 δ) (fun x => F (x, t)) := fun {δ t} hδ hδδ₀ ht => by
    have hc2 : ContinuousOn (fun y => partialFst F 2 (y, t)) (Ioo (-δ₀) δ₀) := fun x hx =>
      (hbox (abs_lt.2 hx) ht).2.2.2.1.continuousWithinAt
    exact strictConvexOn_Icc_of_eventually_odd hδ hδδ₀ (fun x hx =>
      (hbox (abs_lt.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩) ht).1.continuousAt
        |>.continuousWithinAt)
      (hoddt ht 0 ⟨by linarith, hδ₀⟩)
      (hc2.congr fun x hx => (hbox (abs_lt.2 hx) ht).2.2.2.2.1)
      fun x hx => (hbox (abs_lt.2 hx) ht).2.2.2.2.2.1
  -- `∂ₓ F (0, t)` has the sign of `b t`.
  have hsign : ∀ {t : ℝ}, |t| < δ₀ →
      (0 < b * t → 0 < partialFst F 1 (0, t)) ∧ (b * t < 0 → partialFst F 1 (0, t) < 0) :=
    fun ht => by
      simpa only [h00] using sign_sub_of_hasDerivAt (f := fun s => partialFst F 1 (0, s))
        (fun s hs => (hbox h0δ₀ (abs_lt.2 hs)).2.2.1)
        (fun s hs => (hbox h0δ₀ (abs_lt.2 hs)).2.2.2.2.2.2.1) ht
  filter_upwards [Ioo_mem_nhdsGT hδ₀] with δ ⟨hδpos, hδδ₀⟩
  have hδabs : |δ| < δ₀ := by rwa [abs_of_pos hδpos]
  have hzero : F (0, 0) = 0 := by
    have := (hbox h0δ₀ h0δ₀).2.2.2.2.2.2.2
    rw [neg_zero] at this
    linarith
  have hFδ0 : 0 < F (δ, 0) := pos_of_strictConvexOn_of_pos (hconv hδpos hδδ₀ h0δ₀)
    ⟨le_rfl, hδpos.le⟩ ⟨hδpos.le, le_rfl⟩ hzero (hbox h0δ₀ h0δ₀).1 h00.ge hδpos
  filter_upwards [Ioo_mem_nhds (neg_neg_of_pos hδ₀) hδ₀,
    (hbox hδabs h0δ₀).2.1.eventually (lt_mem_nhds hFδ0)] with t ht hFδt
  replace ht := abs_lt.2 ht
  have hoddδ : ∀ x ∈ Ioo (-δ) δ, ∀ᶠ y in 𝓝 x, F (-y, t) = -F (y, t) := fun x hx =>
    hoddt ht x (Ioo_subset_Ioo (by linarith) hδδ₀.le hx)
  have hderiv0 : deriv (fun x => F (x, t)) 0 = partialFst F 1 (0, t) := (hbox h0δ₀ ht).1.deriv
  refine ⟨fun hbt => pitchfork_slice_of_nonneg hδpos (hconv hδpos hδδ₀ ht)
    (fun x hx => (hoddδ x hx).self_of_nhds) (hbox h0δ₀ ht).1 ?_,
    fun hbt => hderiv0 ▸ (hsign ht).1 hbt, fun hbt => ?_⟩
  · rcases hbt.lt_or_eq with hbt | hbt
    · exact ((hsign ht).1 hbt).le
    · rcases mul_eq_zero.1 hbt.symm with hb0 | rfl
      · exact absurd hb0 hb
      · exact h00.ge
  · have hneg : deriv (fun x => F (x, t)) 0 < 0 := hderiv0 ▸ (hsign ht).2 hbt
    exact ⟨hneg, pitchfork_slice_of_neg hδpos (hconv hδpos hδδ₀ ht) hoddδ
      (fun x hx => (hbox (by rw [abs_of_nonneg hx.1]; linarith [hx.2]) ht).1.differentiableAt)
      hneg hFδt⟩

end TauCeti
