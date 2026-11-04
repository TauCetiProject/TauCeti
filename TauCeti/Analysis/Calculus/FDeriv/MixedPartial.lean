/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FormalMultilinearSeries
public import Mathlib.Analysis.Convex.Basic

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-!
# Mixed space-time partial derivatives

Let `u : E → ℝ → F` be a function of a space variable `y` in a real normed space `E` and of a
time variable `t` in a convex set `s ⊆ ℝ`, such as a closed interval `[a, b]`. Time derivatives
are taken within `s`, so that at an endpoint of an interval they are one-sided. This file proves
the theorem of Schwarz and Peano on mixed partial derivatives in this setting: if one of the two
iterated partial derivatives `∂ₜ D_y u` and `D_y ∂ₜ u` exists and is jointly continuous, then the
other one exists and the two agree. Only the existence of the first partial derivatives and the
joint continuity of the given mixed derivative at the point are assumed; no joint
differentiability of `u` is needed.

* `TauCeti.hasFDerivAt_timeDeriv_of_continuousWithinAt`: if `∂ₜ D_y u` is jointly continuous at
  `(x, t)` and `u(y, ·)` has a time derivative `g y` at `t` for `y` near `x`, then `g` is
  differentiable at `x`, with derivative `∂ₜ D_y u (x, t)`.
* `TauCeti.hasDerivWithinAt_spatialDeriv_of_continuousWithinAt`: if `D_y ∂ₜ u` is jointly
  continuous at `(x, t)`, then the spatial derivative `D_y u (x, ·)` has time derivative
  `D_y ∂ₜ u (x, t)` within `s` at `t`.

Iterating these one-step statements shows that all orders of a family of mixed derivatives agree.
Index the candidate mixed derivatives by a family `Q r y t`, where `Q r y t n` stands for the
`n`-multilinear map `∂ₜ^r D_y^n u (y, t)`, and the admissible orders `(r, n)` by a lower set
`I ⊆ ℕ × ℕ`; for parabolic problems of order `k` this is `{(r, n) | 2 r + n ≤ k}`. Spatial
derivatives are related as in `HasFTaylorSeriesUpTo`, through `curryLeft`.

* `TauCeti.hasFDerivAt_of_isLowerSet`: if `Q 0` is related to itself by spatial derivatives, each
  `Q (r + 1)` is the time derivative of `Q r`, and the mixed derivatives are jointly continuous,
  then every `Q r` is related to itself by spatial derivatives.
* `TauCeti.hasDerivWithinAt_of_isLowerSet`: conversely, if every `Q r` is related to itself by
  spatial derivatives, `Q (r + 1) y t 0` is the time derivative of `Q r y t 0`, and the mixed
  derivatives are jointly continuous, then `Q (r + 1) y t n` is the time derivative of
  `Q r y t n` for every admissible `n`.

In either case the family `Q` satisfies both the spatial and the temporal derivative relations at
every admissible order, so every ordering of `r` time derivatives and `n` spatial derivatives
exists and equals `Q r y t n`, including the one-sided time derivatives at the endpoints of an
interval. This is the form in which spaces of functions with continuous mixed space-time
derivatives, such as parabolic Hölder spaces, are described independently of the order of
differentiation.

## References

* W. Rudin, *Principles of Mathematical Analysis*, 3rd ed., Theorem 9.41 (the two-variable form
  with the classical proof).
-/

public section

noncomputable section

namespace TauCeti

open Set Filter Metric
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] in
/-- A property that holds eventually near `x` in space and near `t` within `s` in time holds on a
box `‖y - x‖ < δ`, `τ ∈ s`, `|τ - t| < δ`. -/
private theorem exists_forall_of_eventually_prod {P : E × ℝ → Prop} {s : Set ℝ} {x : E}
    {t : ℝ} (h : ∀ᶠ p in 𝓝 x ×ˢ 𝓝[s] t, P p) :
    ∃ δ > 0, ∀ y, ‖y - x‖ < δ → ∀ τ ∈ s, |τ - t| < δ → P (y, τ) := by
  obtain ⟨ε₁, hε₁, pb, hpb, hP⟩ := Metric.eventually_nhds_prod_iff.1 h
  obtain ⟨ε₂, hε₂, h₂⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hpb)
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun y hy τ hτ hτt ↦ hP ?_ (h₂ ?_ hτ)⟩
  · rw [dist_eq_norm]
    exact hy.trans_le (min_le_left _ _)
  · rw [Real.dist_eq]
    exact hτt.trans_le (min_le_right _ _)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Joint continuity at `(x, t)` within `univ ×ˢ s`, as an eventual bound near `x` and near `t`
within `s`. -/
private theorem eventually_norm_sub_lt_of_continuousWithinAt {w : E → ℝ → F} {s : Set ℝ}
    {x : E} {t : ℝ} (hw : ContinuousWithinAt (fun p : E × ℝ ↦ w p.1 p.2) (univ ×ˢ s) (x, t))
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ p in 𝓝 x ×ˢ 𝓝[s] t, ‖w p.1 p.2 - w x t‖ < ε := by
  have h : Tendsto (fun p : E × ℝ ↦ w p.1 p.2) (𝓝 x ×ˢ 𝓝[s] t) (𝓝 (w x t)) := by
    simpa [ContinuousWithinAt, nhdsWithin_prod_eq] using hw
  simpa [dist_eq_norm] using Metric.tendsto_nhds.1 h ε hε

/-- If `v` has derivative `w τ` within a convex set `s` at every `τ ∈ s` with `|τ - t| < δ`, and
`w τ` is within `ε` of `W` there, then the increment of `v` from `t` to such a `σ` is
`(σ - t) • W` up to `ε |σ - t|`. -/
private theorem norm_sub_sub_smul_le_of_hasDerivWithinAt {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {v w : ℝ → G} {W : G} {s : Set ℝ} {t σ δ ε : ℝ} (hs : Convex ℝ s)
    (ht : t ∈ s) (hσ : σ ∈ s) (hσt : |σ - t| < δ)
    (hw : ∀ τ ∈ s, |τ - t| < δ → HasDerivWithinAt v (w τ) s τ)
    (hbound : ∀ τ ∈ s, |τ - t| < δ → ‖w τ - W‖ ≤ ε) :
    ‖v σ - v t - (σ - t) • W‖ ≤ ε * |σ - t| := by
  have hmem : ∀ τ ∈ s ∩ ball t δ, τ ∈ s ∧ |τ - t| < δ := fun τ hτ ↦
    ⟨hτ.1, by simpa [Real.dist_eq] using hτ.2⟩
  have key := (hs.inter (convex_ball t δ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun τ ↦ v τ - τ • W) (f' := fun τ ↦ w τ - W)
    (fun τ hτ ↦
      (((hw τ (hmem τ hτ).1 (hmem τ hτ).2).mono inter_subset_left).sub
        ((hasDerivWithinAt_id τ _).smul_const W)).congr_deriv (by rw [one_smul]))
    (fun τ hτ ↦ hbound τ (hmem τ hτ).1 (hmem τ hτ).2) (y := σ) (x := t)
    ⟨ht, mem_ball_self ((abs_nonneg _).trans_lt hσt)⟩ ⟨hσ, by simpa [Real.dist_eq] using hσt⟩
  rw [Real.norm_eq_abs] at key
  convert key using 2
  rw [sub_smul]
  abel

/-- **Peano's theorem on mixed partial derivatives**, differentiating a time derivative in space.
Let `u : E → ℝ → F`, let `s ⊆ ℝ` be convex, and let `t ∈ s` be a point at which derivatives within
`s` are unique. Suppose that near `x` in space and near `t` within `s`, the spatial derivative of
`u(·, τ)` at `y` is `v(y, τ)`, and that `v(y, ·)` has time derivative `w(y, τ)` within `s`, with
`w` jointly continuous at `(x, t)`. If `g y` is the time derivative of `u(y, ·)` within `s` at `t`
for every `y` near `x`, then `g` is differentiable at `x` with derivative `w(x, t)`: the spatial
derivative of `∂ₜu` exists and equals `∂ₜ D_y u`. -/
theorem hasFDerivAt_timeDeriv_of_continuousWithinAt {u : E → ℝ → F}
    {v w : E → ℝ → E →L[ℝ] F} {g : E → F} {s : Set ℝ} {x : E} {t : ℝ} (hs : Convex ℝ s)
    (ht : t ∈ s) (hst : UniqueDiffWithinAt ℝ s t)
    (hv : ∀ᶠ p in 𝓝 x ×ˢ 𝓝[s] t, HasFDerivAt (u · p.2) (v p.1 p.2) p.1)
    (hw : ∀ᶠ p in 𝓝 x ×ˢ 𝓝[s] t, HasDerivWithinAt (v p.1) (w p.1 p.2) s p.2)
    (hwc : ContinuousWithinAt (fun p : E × ℝ ↦ w p.1 p.2) (univ ×ˢ s) (x, t))
    (hg : ∀ᶠ y in 𝓝 x, HasDerivWithinAt (u y) (g y) s t) :
    HasFDerivAt g (w x t) x := by
  have : (𝓝[s \ {t}] t).NeBot := accPt_principal_iff_nhdsWithin.1 hst.accPt
  -- Differentiate the time difference quotients `slope (u y) t σ` in space and let `σ → t`.
  refine hasFDerivAt_of_tendstoUniformlyOnFilter (l := 𝓝[s \ {t}] t)
    (f := fun σ y ↦ slope (u y) t σ) (f' := fun σ y ↦ slope (v y) t σ)
    (g' := fun _ ↦ w x t) ?_ ?_ ?_
  · rw [Metric.tendstoUniformlyOnFilter_iff]
    intro ε hε
    obtain ⟨δ, hδ, hbox⟩ := exists_forall_of_eventually_prod
      (hw.and (eventually_norm_sub_lt_of_continuousWithinAt hwc (half_pos hε)))
    have hσ : ∀ᶠ σ in 𝓝[s \ {t}] t, σ ∈ s ∧ σ ≠ t ∧ |σ - t| < δ := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Metric.ball_mem_nhds t hδ)] with σ hσ hσδ
      exact ⟨hσ.1, hσ.2, by simpa [Real.dist_eq] using hσδ⟩
    filter_upwards [hσ.prod_mk (Metric.ball_mem_nhds x hδ)] with ⟨σ, y⟩ ⟨⟨hσs, hσt, hσδ⟩, hy⟩
    have hy : ‖y - x‖ < δ := by simpa [dist_eq_norm] using hy
    have key := norm_sub_sub_smul_le_of_hasDerivWithinAt (v := v y) (w := w y) hs ht hσs hσδ
      (fun τ hτ hτδ ↦ (hbox y hy τ hτ hτδ).1) (fun τ hτ hτδ ↦ (hbox y hy τ hτ hτδ).2.le)
    have hσt' : 0 < |σ - t| := abs_pos.2 (sub_ne_zero.2 hσt)
    rw [dist_eq_norm, slope_def_module, norm_sub_rev,
      ← inv_smul_smul₀ (sub_ne_zero.2 hσt) (w x t), ← smul_sub, norm_smul, norm_inv,
      Real.norm_eq_abs]
    calc |σ - t|⁻¹ * ‖v y σ - v y t - (σ - t) • w x t‖
        ≤ |σ - t|⁻¹ * (ε / 2 * |σ - t|) := by gcongr
      _ = ε / 2 := by field_simp
      _ < ε := half_lt_self hε
  · obtain ⟨δ, hδ, hbox⟩ := exists_forall_of_eventually_prod hv
    have hσ : ∀ᶠ σ in 𝓝[s \ {t}] t, σ ∈ s ∧ |σ - t| < δ := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Metric.ball_mem_nhds t hδ)] with σ hσ hσδ
      exact ⟨hσ.1, by simpa [Real.dist_eq] using hσδ⟩
    filter_upwards [hσ.prod_mk (Metric.ball_mem_nhds x hδ)] with ⟨σ, y⟩ ⟨⟨hσs, hσδ⟩, hy⟩
    have hy : ‖y - x‖ < δ := by simpa [dist_eq_norm] using hy
    simp only [slope_def_module]
    exact ((hbox y hy σ hσs hσδ).sub (hbox y hy t ht (by simpa using hδ))).const_smul _
  · filter_upwards [hg] with y hy
    exact hasDerivWithinAt_iff_tendsto_slope.1 hy

/-- **Peano's theorem on mixed partial derivatives**, differentiating a spatial derivative in
time. Let `u : E → ℝ → F`, let `s ⊆ ℝ` be convex, and let `t ∈ s`. Suppose that `v τ` is the
spatial derivative of `u(·, τ)` at `x` for `τ ∈ s` near `t`, and that near `x` in space and near
`t` within `s`, `u(y, ·)` has time derivative `g(y, τ)` within `s`, whose spatial derivative is
`w(y, τ)`, with `w` jointly continuous at `(x, t)`. Then `v` has time derivative `w(x, t)` within
`s` at `t`: the time derivative of `D_y u` exists and equals `D_y ∂ₜu`. -/
theorem hasDerivWithinAt_spatialDeriv_of_continuousWithinAt {u : E → ℝ → F}
    {v : ℝ → E →L[ℝ] F} {g : E → ℝ → F} {w : E → ℝ → E →L[ℝ] F} {s : Set ℝ} {x : E} {t : ℝ}
    (hs : Convex ℝ s) (ht : t ∈ s) (hv : ∀ᶠ τ in 𝓝[s] t, HasFDerivAt (u · τ) (v τ) x)
    (hg : ∀ᶠ p in 𝓝 x ×ˢ 𝓝[s] t, HasDerivWithinAt (u p.1) (g p.1 p.2) s p.2)
    (hw : ∀ᶠ p in 𝓝 x ×ˢ 𝓝[s] t, HasFDerivAt (g · p.2) (w p.1 p.2) p.1)
    (hwc : ContinuousWithinAt (fun p : E × ℝ ↦ w p.1 p.2) (univ ×ˢ s) (x, t)) :
    HasDerivWithinAt v (w x t) s t := by
  rw [hasDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hbox⟩ := exists_forall_of_eventually_prod
    ((hg.and hw).and (eventually_norm_sub_lt_of_continuousWithinAt hwc hc))
  have hvt : HasFDerivAt (u · t) (v t) x := hv.self_of_nhdsWithin ht
  filter_upwards [hv, self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds t hδ)]
    with σ hvσ hσs hσδ
  have hσδ : |σ - t| < δ := by simpa [Real.dist_eq] using hσδ
  set W := w x t
  -- The spatial increment of `u(·, σ) - u(·, t)` is `(σ - t) • W` up to `c |σ - t|` per unit
  -- length, by the mean value theorem in time and then in space.
  have hψ : HasFDerivAt (fun y ↦ u y σ - u y t - (σ - t) • W y) (v σ - v t - (σ - t) • W) x :=
    (hvσ.sub hvt).sub (W.hasFDerivAt.const_smul (σ - t))
  refine hψ.le_of_lip' (by positivity) ?_
  filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
  have hy : ‖y - x‖ < δ := by simpa [dist_eq_norm] using hy
  -- The time derivative of `τ ↦ u y τ - u x τ` is within `c ‖y - x‖` of `W (y - x)`.
  have hspace : ∀ τ ∈ s, |τ - t| < δ → ‖(g y τ - g x τ) - W (y - x)‖ ≤ c * ‖y - x‖ := by
    intro τ hτ hτδ
    have hmem : ∀ z ∈ ball x δ, ‖z - x‖ < δ := fun z hz ↦ by simpa [dist_eq_norm] using hz
    have key := (convex_ball x δ).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fun z ↦ g z τ - W z) (f' := fun z ↦ w z τ - W)
      (fun z hz ↦ ((hbox z (hmem z hz) τ hτ hτδ).1.2.sub W.hasFDerivAt).hasFDerivWithinAt)
      (fun z hz ↦ (hbox z (hmem z hz) τ hτ hτδ).2.le) (mem_ball_self hδ)
      (by simpa [dist_eq_norm] using hy)
    convert key using 2
    rw [map_sub]
    abel
  have htime := norm_sub_sub_smul_le_of_hasDerivWithinAt (v := fun τ ↦ u y τ - u x τ)
    (w := fun τ ↦ g y τ - g x τ) (W := W (y - x)) hs ht hσs hσδ
    (fun τ hτ hτδ ↦ (hbox y hy τ hτ hτδ).1.1.sub (hbox x (by simpa using hδ) τ hτ hτδ).1.1)
    hspace
  rw [Real.norm_eq_abs, mul_assoc, mul_comm |σ - t|, ← mul_assoc]
  convert htime using 2
  simp only [map_sub, smul_sub, sub_smul]
  abel

section Iterated

/-- Time derivatives commute with currying the first variable of a multilinear map. -/
private theorem hasDerivWithinAt_curryLeft_iff {n : ℕ}
    {f : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) ↦ E) F}
    {f' : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) ↦ E) F} {s : Set ℝ} {t : ℝ} :
    HasDerivWithinAt (fun σ ↦ (f σ).curryLeft) f'.curryLeft s t ↔ HasDerivWithinAt f f' s t := by
  let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) ↦ E) F
  -- `curryLeft` is the linear homeomorphism `L`, which commutes with difference quotients.
  have hL : ∀ g, g.curryLeft = L g := fun _ ↦ rfl
  have hslope : slope (fun σ ↦ (f σ).curryLeft) t = fun σ ↦ L (slope f t σ) := funext fun σ ↦ by
    simp only [slope_def_module, hL, L.map_sub, L.map_smul]
  refine (hasDerivWithinAt_iff_tendsto_slope (f := fun σ ↦ (f σ).curryLeft)).trans
    (Iff.trans ?_ hasDerivWithinAt_iff_tendsto_slope.symm)
  rw [hslope, hL]
  exact L.toHomeomorph.isInducing.tendsto_nhds_iff.symm

/-- Continuity is preserved by currying the first variable of a multilinear map. -/
private theorem continuousOn_curryLeft {X : Type*} [TopologicalSpace X] {n : ℕ}
    {f : X → ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) ↦ E) F} {S : Set X}
    (hf : ContinuousOn f S) : ContinuousOn (fun p ↦ (f p).curryLeft) S :=
  (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) ↦ E) F).continuous.comp_continuousOn
    hf

variable {Q : ℕ → E → ℝ → FormalMultilinearSeries ℝ E F} {s : Set ℝ} {I : Set (ℕ × ℕ)}

/-- **Mixed derivatives with time derivatives taken last.** Let `I ⊆ ℕ × ℕ` be a lower set of
orders, and let `s ⊆ ℝ` be a convex set on which derivatives within `s` are unique, such as a
nondegenerate closed interval. Suppose that

* `Q 0 y t (n + 1)` is the spatial derivative of `Q 0 · t n` whenever `(0, n + 1) ∈ I`;
* `Q (r + 1) y t n` is the time derivative within `s` of `Q r y · n` whenever `(r + 1, n) ∈ I`;
* the mixed derivatives `Q (r + 1) · · (n + 1)` are jointly continuous on `univ ×ˢ s`.

Then `Q r y t (n + 1)` is the spatial derivative of `Q r · t n` whenever `(r, n + 1) ∈ I`. Thus if
`Q r y t n` is `∂ₜ^r D_y^n u`, it is also `D_y^n ∂ₜ^r u`. -/
theorem hasFDerivAt_of_isLowerSet (hI : IsLowerSet I) (hs : Convex ℝ s)
    (hs' : UniqueDiffOn ℝ s)
    (hx : ∀ n, (0, n + 1) ∈ I → ∀ t ∈ s, ∀ y,
      HasFDerivAt (Q 0 · t n) (Q 0 y t (n + 1)).curryLeft y)
    (ht : ∀ r n, (r + 1, n) ∈ I → ∀ y, ∀ t ∈ s,
      HasDerivWithinAt (Q r y · n) (Q (r + 1) y t n) s t)
    (hc : ∀ r n, (r + 1, n + 1) ∈ I →
      ContinuousOn (fun p : E × ℝ ↦ Q (r + 1) p.1 p.2 (n + 1)) (univ ×ˢ s))
    {r n : ℕ} (hrn : (r, n + 1) ∈ I) {t : ℝ} (hts : t ∈ s) (y : E) :
    HasFDerivAt (Q r · t n) (Q r y t (n + 1)).curryLeft y := by
  induction r generalizing n t y with
  | zero => exact hx n hrn t hts y
  | succ r ih =>
    have hI₁ : (r, n + 1) ∈ I := hI (by simp) hrn
    have hI₂ : (r + 1, n) ∈ I := hI (by simp) hrn
    -- `Q (r + 1) · t n` is the time derivative of `Q r · · n`, whose spatial derivative is
    -- `Q r · · (n + 1)` by induction; the time derivative of the latter is the jointly continuous
    -- mixed derivative `Q (r + 1) · · (n + 1)`.
    refine hasFDerivAt_timeDeriv_of_continuousWithinAt (u := fun z τ ↦ Q r z τ n)
      (v := fun z τ ↦ (Q r z τ (n + 1)).curryLeft)
      (w := fun z τ ↦ (Q (r + 1) z τ (n + 1)).curryLeft) hs hts (hs' t hts) ?_ ?_
      (continuousOn_curryLeft (hc r n hrn) (y, t) ⟨mem_univ _, hts⟩)
      (Eventually.of_forall fun z ↦ ht r n hI₂ z t hts)
    · filter_upwards [prod_mem_prod univ_mem self_mem_nhdsWithin] with p hp
      exact ih hI₁ hp.2 p.1
    · filter_upwards [prod_mem_prod univ_mem self_mem_nhdsWithin] with p hp
      exact hasDerivWithinAt_curryLeft_iff.2 (ht r (n + 1) hrn p.1 p.2 hp.2)

/-- **Mixed derivatives with spatial derivatives taken last.** Let `I ⊆ ℕ × ℕ` be a lower set of
orders, and let `s ⊆ ℝ` be convex. Suppose that

* `Q r y t (n + 1)` is the spatial derivative of `Q r · t n` whenever `(r, n + 1) ∈ I`;
* `Q (r + 1) y t 0` is the time derivative within `s` of `Q r y · 0` whenever `(r + 1, 0) ∈ I`;
* the mixed derivatives `Q (r + 1) · · (n + 1)` are jointly continuous on `univ ×ˢ s`.

Then `Q (r + 1) y t n` is the time derivative within `s` of `Q r y · n` whenever `(r + 1, n) ∈ I`.
Thus if `Q r y t n` is `D_y^n ∂ₜ^r u`, it is also `∂ₜ^r D_y^n u`. -/
theorem hasDerivWithinAt_of_isLowerSet (hI : IsLowerSet I) (hs : Convex ℝ s)
    (hx : ∀ r n, (r, n + 1) ∈ I → ∀ t ∈ s, ∀ y,
      HasFDerivAt (Q r · t n) (Q r y t (n + 1)).curryLeft y)
    (ht : ∀ r, (r + 1, 0) ∈ I → ∀ y, ∀ t ∈ s,
      HasDerivWithinAt (Q r y · 0) (Q (r + 1) y t 0) s t)
    (hc : ∀ r n, (r + 1, n + 1) ∈ I →
      ContinuousOn (fun p : E × ℝ ↦ Q (r + 1) p.1 p.2 (n + 1)) (univ ×ˢ s))
    {r n : ℕ} (hrn : (r + 1, n) ∈ I) (y : E) {t : ℝ} (hts : t ∈ s) :
    HasDerivWithinAt (Q r y · n) (Q (r + 1) y t n) s t := by
  induction n generalizing r y t with
  | zero => exact ht r hrn y t hts
  | succ n ih =>
    have hI₁ : (r, n + 1) ∈ I := hI (by simp) hrn
    have hI₂ : (r + 1, n) ∈ I := hI (by simp) hrn
    -- `Q r y · (n + 1)` is the spatial derivative of `Q r · · n`, whose time derivative is
    -- `Q (r + 1) · · n` by induction; the spatial derivative of the latter is the jointly
    -- continuous mixed derivative `Q (r + 1) · · (n + 1)`.
    refine hasDerivWithinAt_curryLeft_iff.1 <|
      hasDerivWithinAt_spatialDeriv_of_continuousWithinAt (u := fun z τ ↦ Q r z τ n)
        (g := fun z τ ↦ Q (r + 1) z τ n) (w := fun z τ ↦ (Q (r + 1) z τ (n + 1)).curryLeft) hs hts
        ?_ ?_ ?_ (continuousOn_curryLeft (hc r n hrn) (y, t) ⟨mem_univ _, hts⟩)
    · filter_upwards [self_mem_nhdsWithin] with τ hτ
      exact hx r n hI₁ τ hτ y
    · filter_upwards [prod_mem_prod univ_mem self_mem_nhdsWithin] with p hp
      exact ih hI₂ p.1 hp.2
    · filter_upwards [prod_mem_prod univ_mem self_mem_nhdsWithin] with p hp
      exact hx (r + 1) n hrn p.2 hp.2 p.1

end Iterated

end TauCeti
