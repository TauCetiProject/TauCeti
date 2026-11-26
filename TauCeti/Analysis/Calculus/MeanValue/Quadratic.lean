/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Calculus.MeanValue

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

For a `C²` map the hypothesis holds near every point: a map `f` that is `C²` at `z` satisfies
the quadratic estimate with `φ = f' z` on some closed ball around `z`
(`ContDiffAt.exists_forall_norm_image_sub_sub_le`). For a family `f p` of maps, jointly `C²` at
`(p, z)` for every `p` in a compact set `K`, the radius and the constant can be chosen uniformly
for `p ∈ K` (`IsCompact.exists_forall_norm_image_sub_sub_le`); this is how the constants of a
gluing construction are made uniform over a compact family of approximate solutions.

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

variable {𝕜 E G P : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup P] [NormedSpace 𝕜 P]

/-- The quadratic estimate on the ball `closedBall z δ` with constant `L`, for every map `f p`
with `p ∈ T`. It only gets weaker as `δ` decreases and `L` increases. -/
private def QuadraticEstimateOn (f : P → E → G) (z : E) (δ : ℝ) (L : ℝ≥0) (T : Set P) : Prop :=
  ∀ p ∈ T, ∀ x ∈ closedBall z δ, ∀ y ∈ closedBall z δ,
    ‖f p y - f p x - fderiv 𝕜 (f p) z (y - x)‖ ≤ L / 2 * (‖x - z‖ + ‖y - z‖) * ‖y - x‖

omit [NormedAddCommGroup P] [NormedSpace 𝕜 P] in
private lemma QuadraticEstimateOn.mono {f : P → E → G} {z : E} {δ δ' : ℝ}
    {L L' : ℝ≥0} {T T' : Set P} (h : QuadraticEstimateOn (𝕜 := 𝕜) f z δ L T) (hδ : δ' ≤ δ)
    (hL : L ≤ L') (hT : T' ⊆ T) : QuadraticEstimateOn (𝕜 := 𝕜) f z δ' L' T' := by
  intro p hp x hx y hy
  refine (h p (hT hp) x (closedBall_subset_closedBall hδ hx) y
    (closedBall_subset_closedBall hδ hy)).trans ?_
  gcongr

/-- Near a parameter `p` at which `(q, w) ↦ f q w` is `C²` at `(p, z)`, the maps `f q` satisfy
the quadratic estimate at `z` on a common ball with a common constant. -/
private lemma exists_mem_nhds_quadraticEstimateOn {f : P → E → G} {p : P} {z : E}
    (hf : ContDiffAt 𝕜 2 (uncurry f) (p, z)) :
    ∃ U ∈ 𝓝 p, ∃ δ > 0, ∃ L : ℝ≥0, QuadraticEstimateOn (𝕜 := 𝕜) f z δ L U := by
  let : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
  -- The partial derivative `(q, w) ↦ fderiv 𝕜 (f q) w` is `C¹` at `(p, z)`, hence Lipschitz
  -- near `(p, z)`.
  have hF : ContDiffAt 𝕜 1 (fun q : P × E ↦ fderiv 𝕜 (f q.1) q.2) (p, z) :=
    ContDiffAt.fderiv (f := fun q : P × E ↦ f q.1) (g := Prod.snd) (m := 1) (n := 2)
      (hf.comp ((p, z), z) (f := fun r : (P × E) × E ↦ (r.1.1, r.2)) (by fun_prop))
      contDiffAt_snd (by norm_num)
  obtain ⟨L, t, ht, hLip⟩ := hF.exists_lipschitzOnWith
  have hev := hf.eventually (by simp)
  obtain ⟨u, hu, v, hv, huv⟩ := mem_prod_iff.1 (nhds_prod_eq (x := p) (y := z) ▸
    Filter.inter_mem ht hev)
  obtain ⟨δ, hδ, hδv⟩ := nhds_basis_closedBall.mem_iff.1 hv
  refine ⟨u, hu, δ, hδ, L, fun q hq x hx y hy ↦ ?_⟩
  have hmem {w : E} (hw : w ∈ closedBall z δ) : (q, w) ∈ t ∩ {r | ContDiffAt 𝕜 2 (uncurry f) r} :=
    huv ⟨hq, hδv hw⟩
  have hdiff {w : E} (hw : w ∈ closedBall z δ) : DifferentiableAt 𝕜 (f q) w :=
    ((hmem hw).2.comp w (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt two_ne_zero
  refine (convex_closedBall z δ).norm_image_sub_sub_le_of_norm_fderiv_sub_le
    (fun w hw ↦ hdiff hw) (fun w hw ↦ ?_) hx hy
  have h := hLip.dist_le_mul (q, w) (hmem hw).1 (q, z) (hmem (mem_closedBall_self hδ.le)).1
  rwa [dist_eq_norm, Prod.dist_eq, dist_self, dist_eq_norm, max_eq_right (norm_nonneg _)] at h

/-- **The quadratic estimate, uniformly over a compact family.** Let `f p` be a family of maps
such that `(p, w) ↦ f p w` is `C²` at `(p, z)` for every `p` in a compact set `K`. Then there are
a radius `δ > 0` and a constant `L` such that for every `p ∈ K` and all `x, y` in the closed ball
of radius `δ` around `z`,
`‖f p y - f p x - fderiv 𝕜 (f p) z (y - x)‖ ≤ (L / 2) (‖x - z‖ + ‖y - z‖) ‖y - x‖`. -/
theorem IsCompact.exists_forall_norm_image_sub_sub_le {f : P → E → G} {K : Set P} {z : E}
    (hK : IsCompact K) (hf : ∀ p ∈ K, ContDiffAt 𝕜 2 (uncurry f) (p, z)) :
    ∃ δ > 0, ∃ L : ℝ≥0, ∀ p ∈ K, ∀ x ∈ closedBall z δ, ∀ y ∈ closedBall z δ,
      ‖f p y - f p x - fderiv 𝕜 (f p) z (y - x)‖ ≤ L / 2 * (‖x - z‖ + ‖y - z‖) * ‖y - x‖ := by
  refine hK.induction_on (p := fun T ↦ ∃ δ > 0, ∃ L : ℝ≥0, QuadraticEstimateOn (𝕜 := 𝕜) f z δ L T)
    ⟨1, one_pos, 0, fun _ hp ↦ absurd hp (notMem_empty _)⟩ ?_ ?_ ?_
  · rintro T T' hTT' ⟨δ, hδ, L, h⟩
    exact ⟨δ, hδ, L, h.mono le_rfl le_rfl hTT'⟩
  · rintro T T' ⟨δ, hδ, L, h⟩ ⟨δ', hδ', L', h'⟩
    refine ⟨min δ δ', lt_min hδ hδ', max L L', fun p hp ↦ ?_⟩
    rcases hp with hp | hp
    · exact (h.mono (min_le_left _ _) (le_max_left _ _) subset_rfl) p hp
    · exact (h'.mono (min_le_right _ _) (le_max_right _ _) subset_rfl) p hp
  · intro p hp
    obtain ⟨U, hU, h⟩ := exists_mem_nhds_quadraticEstimateOn (hf p hp)
    exact ⟨U, mem_nhdsWithin_of_mem_nhds hU, h⟩

/-- **The quadratic estimate for a `C²` map.** If `f` is `C²` at `z`, there are a radius `δ > 0`
and a constant `L` such that for all `x, y` in the closed ball of radius `δ` around `z`,
`‖f y - f x - fderiv 𝕜 f z (y - x)‖ ≤ (L / 2) (‖x - z‖ + ‖y - z‖) ‖y - x‖`. -/
theorem ContDiffAt.exists_forall_norm_image_sub_sub_le {f : E → G} {z : E}
    (hf : ContDiffAt 𝕜 2 f z) :
    ∃ δ > 0, ∃ L : ℝ≥0, ∀ x ∈ closedBall z δ, ∀ y ∈ closedBall z δ,
      ‖f y - f x - fderiv 𝕜 f z (y - x)‖ ≤ L / 2 * (‖x - z‖ + ‖y - z‖) * ‖y - x‖ := by
  obtain ⟨δ, hδ, L, h⟩ := isCompact_singleton.exists_forall_norm_image_sub_sub_le
    (f := fun (_ : 𝕜) ↦ f) (K := {0}) fun _ _ ↦ hf.comp _ contDiffAt_snd
  exact ⟨δ, hδ, L, h 0 rfl⟩

end ContDiff
