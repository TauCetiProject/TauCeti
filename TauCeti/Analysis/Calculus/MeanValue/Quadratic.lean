/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Calculus.MeanValue
public import TauCeti.Analysis.Calculus.FDeriv.Remainder

/-!
# The quadratic mean value inequality

Let `f` be differentiable on a convex set `s`, and suppose that its derivative moves away from a
fixed linear map `φ` at most linearly in the distance to a point `z`:
`‖f' w - φ‖ ≤ L ‖w - z‖` for `w ∈ s`. Then for `x, y ∈ s`

`‖f y - f x - φ (y - x)‖ ≤ (L / 2) (‖x - z‖ + ‖y - z‖) ‖y - x‖`

(`Convex.norm_image_sub_sub_le_of_norm_hasFDerivWithin_sub_le`). Typically `z ∈ s` and
`φ = f' z`, and the hypothesis says that the derivative is `L`-Lipschitz at `z`; it holds when
`f'` is `L`-Lipschitz on `s` (`Convex.norm_image_sub_sub_le_of_lipschitzOnWith`). For `x = z`
this is the first-order Taylor bound `‖f y - f z - f' z (y - z)‖ ≤ (L / 2) ‖y - z‖²`. The
two-point form says that the nonlinear part `N w = f w - f z - f' z (w - z)` of `f` at `z`
satisfies

`‖N y - N x‖ ≤ (L / 2) (‖x - z‖ + ‖y - z‖) ‖y - x‖`,

which is the quadratic estimate used to solve `f = 0` near an approximate zero `z` by a
contraction (`TauCeti.Analysis.Normed.Operator.QuadraticCorrection.Basic`). The constant `L / 2`
is sharp: for `f t = t²` on `ℝ`, `z = 0`, `L = 2` and `0 ≤ x ≤ y`, both sides equal `y² - x²`.

Along the segment from `x` to `y`, the derivative of
`t ↦ f (x + t (y - x)) - t φ (y - x)` is bounded by the affine function
`L ((1 - t) ‖x - z‖ + t ‖y - z‖) ‖y - x‖` of `t`, and a derivative bounded by an affine function
on `[0, 1]` gives an increment bounded by its integral
(`TauCeti.norm_image_sub_le_of_norm_deriv_le_affine_segment_01`, by Mathlib's fencing theorem
`image_norm_le_of_norm_deriv_right_le_deriv_boundary`). The constant bound
`L max ‖x - z‖ ‖y - z‖` along the segment, with Mathlib's
`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'`, would lose a factor up to `2`.

For a `C²` map the quadratic estimate holds near every point: a map `f` that is `C²` at `z`
satisfies it with `φ = f' z` on some closed ball around `z`
(`ContDiffAt.exists_forall_norm_image_sub_sub_le`). For a family `f p` of maps, jointly `C²` at
`(p, z)` for every `p` in a compact set `K`, the radius and the constant can be chosen uniformly
for `p ∈ K` (`IsCompact.exists_forall_norm_image_sub_sub_le`, a restatement of
`IsCompact.exists_pos_forall_norm_sub_sub_fderiv_sub_le_mul`); this is how the constants of a
gluing construction are made uniform over a compact family of approximate solutions. These two
results are stated over `ℝ`, like the compactness results they rest on.

## Main results

* `TauCeti.norm_image_sub_le_of_norm_deriv_le_affine_segment_01`: the increment of a function on
  `[0, 1]` whose derivative is bounded by an affine function.
* `Convex.norm_image_sub_sub_le_of_norm_hasFDerivWithin_sub_le`: the quadratic mean value
  inequality.
* `Convex.norm_image_sub_sub_le_of_lipschitzOnWith`: its form for a Lipschitz derivative.
* `IsCompact.exists_forall_norm_image_sub_sub_le`: the quadratic estimate for a family of `C²`
  maps, uniformly over a compact set of parameters.
* `ContDiffAt.exists_forall_norm_image_sub_sub_le`: the quadratic estimate for a `C²` map near a
  point.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications 52 (2012), Appendix A.3.
-/

public section

open Metric Set Filter Function
open scoped NNReal Topology

/-- **Increment bound for a derivative bounded by an affine function.** If `h` has derivative
`h' t` within `[0, 1]` at every `t ∈ [0, 1]`, and `‖h' t‖ ≤ (1 - t) a + t b` for `t ∈ [0, 1)`,
then `‖h 1 - h 0‖ ≤ (a + b) / 2`, the integral of the bound over `[0, 1]`. -/
theorem TauCeti.norm_image_sub_le_of_norm_deriv_le_affine_segment_01 {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] {h h' : ℝ → G} {a b : ℝ}
    (hh : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt h (h' t) (Icc 0 1) t)
    (bound : ∀ t ∈ Ico (0 : ℝ) 1, ‖h' t‖ ≤ (1 - t) * a + t * b) :
    ‖h 1 - h 0‖ ≤ (a + b) / 2 := by
  -- The bound is the derivative of `B`, with `B 0 = 0` and `B 1 = (a + b) / 2`.
  set B : ℝ → ℝ := fun t ↦ t * a + t ^ 2 / 2 * (b - a)
  have hB (t : ℝ) : HasDerivAt B ((1 - t) * a + t * b) t := by
    have h := ((hasDerivAt_id t).mul_const a).add
      (((hasDerivAt_pow 2 t).div_const 2).mul_const (b - a))
    convert h using 1
    · ext s
      simp [B]
    · ring
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := fun t ↦ h t - h 0)
    (fun t ht ↦ ((hh t ht).sub_const _).continuousWithinAt)
    (fun t ht ↦ ((hh t (Ico_subset_Icc_self ht)).sub_const _).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)) (by simp [B]) hB bound (right_mem_Icc.2 zero_le_one)
  exact key.trans_eq (by simp only [B]; ring)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace Convex

variable {𝕜 G : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜] [NormedSpace 𝕜 E]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] {f : E → G} {f' : E → E →L[𝕜] G} {φ : E →L[𝕜] G}
  {s : Set E} {x y z : E}

/-- **The quadratic mean value inequality.** If `f` has derivative `f' w` within the convex set
`s` at every `w ∈ s`, and `‖f' w - φ‖ ≤ L ‖w - z‖` on `s`, then for `x, y ∈ s`,
`‖f y - f x - φ (y - x)‖ ≤ (L / 2) (‖x - z‖ + ‖y - z‖) ‖y - x‖`. -/
theorem norm_image_sub_sub_le_of_norm_hasFDerivWithin_sub_le {L : ℝ}
    (hf : ∀ w ∈ s, HasFDerivWithinAt f (f' w) s w) (bound : ∀ w ∈ s, ‖f' w - φ‖ ≤ L * ‖w - z‖)
    (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
    ‖f y - f x - φ (y - x)‖ ≤ L / 2 * (‖x - z‖ + ‖y - z‖) * ‖y - x‖ := by
  rcases lt_or_ge L 0 with hL | hL
  · -- A negative constant is only possible when `x = z = y`.
    have hz {w : E} (hw : w ∈ s) : w = z := by
      have h := (norm_nonneg _).trans (bound w hw)
      have : ‖w - z‖ ≤ 0 := by nlinarith [norm_nonneg (w - z)]
      exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
    simp [hz xs, hz ys]
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let : NormedSpace ℝ G := .restrictScalars ℝ 𝕜 G
  set a := ‖x - z‖
  set b := ‖y - z‖
  set d := ‖y - x‖
  set g := (AffineMap.lineMap x y : ℝ → E)
  have segm : MapsTo g (Icc 0 1) s := hs.mapsTo_lineMap xs ys
  -- Along the segment, the distance to `z` is at most the convex combination of `a` and `b`.
  have hgz {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ‖g t - z‖ ≤ (1 - t) * a + t * b := by
    have hgt : g t - z = (1 - t) • (x - z) + t • (y - z) := by
      simp only [g, AffineMap.lineMap_apply_module]
      module
    rw [hgt]
    refine (norm_add_le _ _).trans_eq ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (sub_nonneg.2 ht.2),
      Real.norm_of_nonneg ht.1]
  have hD (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt (fun t : ℝ ↦ f (g t) - f x - t • φ (y - x))
        (f' (g t) (y - x) - φ (y - x)) (Icc 0 1) t := by
    have hfg : HasDerivWithinAt (f ∘ g) (f' (g t) (y - x)) (Icc 0 1) t := by
      simpa using ((hf (g t) (segm ht)).restrictScalars ℝ).comp_hasDerivWithinAt _
        AffineMap.hasDerivWithinAt_lineMap segm
    exact ((hfg.sub_const (f x)).sub ((hasDerivWithinAt_id t _).smul_const (φ (y - x)))).congr_deriv
      (by rw [one_smul])
  have hbound (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) : ‖f' (g t) (y - x) - φ (y - x)‖ ≤
      (1 - t) * (L * a * d) + t * (L * b * d) := by
    rw [← ContinuousLinearMap.sub_apply']
    refine ((f' (g t) - φ).le_opNorm (y - x)).trans ?_
    have := (bound _ (segm (Ico_subset_Icc_self ht))).trans
      (mul_le_mul_of_nonneg_left (hgz (Ico_subset_Icc_self ht)) hL)
    nlinarith [norm_nonneg (y - x)]
  have key := TauCeti.norm_image_sub_le_of_norm_deriv_le_affine_segment_01 hD hbound
  simp only [g, AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero, one_smul, zero_smul,
    sub_self, sub_zero] at key
  exact key.trans_eq (by ring)

/-- **The quadratic mean value inequality**, version with `fderiv`: if `f` is differentiable at
every point of the convex set `s` and `‖fderiv 𝕜 f w - φ‖ ≤ L ‖w - z‖` on `s`, then for
`x, y ∈ s`, `‖f y - f x - φ (y - x)‖ ≤ (L / 2) (‖x - z‖ + ‖y - z‖) ‖y - x‖`. -/
theorem norm_image_sub_sub_le_of_norm_fderiv_sub_le {L : ℝ}
    (hf : ∀ w ∈ s, DifferentiableAt 𝕜 f w) (bound : ∀ w ∈ s, ‖fderiv 𝕜 f w - φ‖ ≤ L * ‖w - z‖)
    (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
    ‖f y - f x - φ (y - x)‖ ≤ L / 2 * (‖x - z‖ + ‖y - z‖) * ‖y - x‖ :=
  hs.norm_image_sub_sub_le_of_norm_hasFDerivWithin_sub_le
    (fun w hw ↦ (hf w hw).hasFDerivAt.hasFDerivWithinAt) bound xs ys

/-- **The quadratic mean value inequality for a Lipschitz derivative.** If `f` has derivative
`f' w` within the convex set `s` at every `w ∈ s` and `f'` is `K`-Lipschitz on `s`, then for
`x, y, z ∈ s`, `‖f y - f x - f' z (y - x)‖ ≤ (K / 2) (‖x - z‖ + ‖y - z‖) ‖y - x‖`. -/
theorem norm_image_sub_sub_le_of_lipschitzOnWith {K : ℝ≥0}
    (hf : ∀ w ∈ s, HasFDerivWithinAt f (f' w) s w) (hf' : LipschitzOnWith K f' s)
    (hs : Convex ℝ s) (zs : z ∈ s) (xs : x ∈ s) (ys : y ∈ s) :
    ‖f y - f x - f' z (y - x)‖ ≤ K / 2 * (‖x - z‖ + ‖y - z‖) * ‖y - x‖ :=
  hs.norm_image_sub_sub_le_of_norm_hasFDerivWithin_sub_le hf
    (fun _ hw ↦ lipschitzOnWith_iff_norm_sub_le.1 hf' hw zs) xs ys

end Convex

section ContDiff

variable {E G P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
  [NormedSpace ℝ G] [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- **The quadratic estimate, uniformly over a compact family.** Let `f p` be a family of maps
such that `(p, w) ↦ f p w` is `C²` at `(p, z)` for every `p` in a compact set `K`. Then there are
a radius `δ > 0` and a constant `L` such that for every `p ∈ K` and all `x, y` in the closed ball
of radius `δ` around `z`,
`‖f p y - f p x - fderiv ℝ (f p) z (y - x)‖ ≤ (L / 2) (‖x - z‖ + ‖y - z‖) ‖y - x‖`.
This is `IsCompact.exists_pos_forall_norm_sub_sub_fderiv_sub_le_mul` in the form of the quadratic
estimate, using `max ‖x - z‖ ‖y - z‖ ≤ ‖x - z‖ + ‖y - z‖`. -/
theorem IsCompact.exists_forall_norm_image_sub_sub_le {f : P → E → G} {K : Set P} {z : E}
    (hK : IsCompact K) (hf : ∀ p ∈ K, ContDiffAt ℝ 2 (uncurry f) (p, z)) :
    ∃ δ > 0, ∃ L : ℝ≥0, ∀ p ∈ K, ∀ x ∈ closedBall z δ, ∀ y ∈ closedBall z δ,
      ‖f p y - f p x - fderiv ℝ (f p) z (y - x)‖ ≤ L / 2 * (‖x - z‖ + ‖y - z‖) * ‖y - x‖ := by
  obtain ⟨δ, hδ, L, hL⟩ := hK.exists_pos_forall_norm_sub_sub_fderiv_sub_le_mul (F := f)
    (x := fun _ ↦ z) hf continuousOn_const
  refine ⟨δ, hδ, (2 * max L 0).toNNReal, fun p hp x hx y hy ↦ ?_⟩
  rw [mem_closedBall, dist_eq_norm] at hx hy
  have h := hL p hp (y - z) (x - z) hy hx
  simp only [add_sub_cancel, sub_sub_sub_cancel_right] at h
  refine h.trans ?_
  rw [Real.coe_toNNReal _ (by positivity), mul_div_cancel_left₀ _ two_ne_zero,
    max_comm ‖y - z‖]
  gcongr
  · exact le_max_left _ _
  · exact max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)

/-- **The quadratic estimate for a `C²` map.** If `f` is `C²` at `z`, there are a radius `δ > 0`
and a constant `L` such that for all `x, y` in the closed ball of radius `δ` around `z`,
`‖f y - f x - fderiv ℝ f z (y - x)‖ ≤ (L / 2) (‖x - z‖ + ‖y - z‖) ‖y - x‖`. -/
theorem ContDiffAt.exists_forall_norm_image_sub_sub_le {f : E → G} {z : E}
    (hf : ContDiffAt ℝ 2 f z) :
    ∃ δ > 0, ∃ L : ℝ≥0, ∀ x ∈ closedBall z δ, ∀ y ∈ closedBall z δ,
      ‖f y - f x - fderiv ℝ f z (y - x)‖ ≤ L / 2 * (‖x - z‖ + ‖y - z‖) * ‖y - x‖ := by
  obtain ⟨δ, hδ, L, h⟩ := isCompact_singleton.exists_forall_norm_image_sub_sub_le
    (f := fun (_ : ℝ) ↦ f) (K := {0}) fun _ _ ↦ hf.comp _ contDiffAt_snd
  exact ⟨δ, hδ, L, h 0 (mem_singleton 0)⟩

end ContDiff
