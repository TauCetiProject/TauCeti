/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothApprox
public import Mathlib.Topology.Homotopy.Basic
import TauCeti.Topology.MetricSpace.ContinuousRadius

/-!
# Relative smooth approximation into a normed space

Let `M` be a Hausdorff σ-compact manifold over a finite-dimensional real model with corners, `F`
a real normed space, `A ⊆ M` closed and `f : M → F` continuous. Mathlib's
`Continuous.exists_contMDiff_approx_and_eqOn` approximates `f` by a smooth map equal to `f` on
`A`, provided `f` is already smooth near `A`. Here `f` need not be smooth anywhere: it suffices
that it agrees on `A` with a map `e` which is smooth on a neighbourhood of `A`. The approximation
`g` is then equal to `e`, not merely to `f`, on a neighbourhood of `A`, with precision prescribed
by any continuous positive function (`Continuous.exists_contMDiff_approx_and_eventuallyEq`).

The typical use takes `A` to be the boundary `I.boundary M` and `e` an extension of boundary data
over a collar: a continuous filling of smooth boundary data is approximated by a smooth filling
with the same germ along the boundary. The smooth `e` cannot be dropped. On the closed disc, the
continuous filling `(x, y) ↦ (|y|, 0)` has the boundary trace `θ ↦ (|sin θ|, 0)`, which is the
restriction of no smooth map near the circle, so no smooth map agrees with it on the circle.

Two refinements follow. The straight-line homotopy from `f` to `g` is constant on `A` and stays
within the prescribed precision of `f`, and if `f` takes values in an open set `U ⊆ F`, then `g`
and the whole homotopy can be kept in `U`
(`Continuous.exists_contMDiff_eventuallyEq_and_homotopyRel`).
If `f` is only given on a subset `D ⊇ A` onto which `M` retracts continuously, the same
approximation holds on `D` (`ContinuousOn.exists_contMDiff_approx_and_eventuallyEq_of_retraction`).
This applies in particular to a closed ball `D` of a finite-dimensional normed space with `A` its
boundary sphere (`ContinuousOn.exists_contDiff_approx_and_eventuallyEq_sphere`): a continuous map
on the interval, the square (a ball for the sup norm on `ℝ × ℝ`) or the disc, agreeing on the
boundary with a map smooth near it, is uniformly approximated by a smooth map on the ambient space
with the same germ along the boundary.

## Implementation notes

Let `O'` be the open set of points of the interior of the neighbourhood `O` of `A` on which `e`
is within `ε / 2` of `f`; it contains `A`. A smooth Urysohn function `ρ : M → [0, 1]` equal to `1`
near `A` and to `0` near the complement of `O'` interpolates `h = f + ρ • (e - f)`, which is
continuous, within `ε / 2` of `f`, and equal to `e`, hence smooth, near `A`. Mathlib's relative
approximation theorem (A. Dedecker and P. Massot) applied to `h` with precision `ε / 2`, keeping
a closed neighbourhood of `A` fixed, gives the result.

## Main results

* `Continuous.exists_contMDiff_approx_and_eventuallyEq`: relative smooth approximation of a
  continuous map agreeing on a closed set with a map smooth near it.
* `Continuous.exists_contDiff_approx_and_eventuallyEq`: the same on a finite-dimensional normed
  space.
* `Continuous.exists_contMDiff_eventuallyEq_and_homotopyRel`: the approximation is homotopic to
  the original map relative to the closed set, by a homotopy that stays close to it and in a
  prescribed open set containing its image.
* `ContinuousOn.exists_contMDiff_approx_and_eventuallyEq_of_retraction`: approximation of a map
  given on a retract.
* `ContinuousOn.exists_contDiff_approx_and_eventuallyEq_sphere`: approximation on a closed ball,
  with the prescribed germ along its boundary sphere.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Springer, 2013, Theorem 6.21
  (Whitney approximation for functions into a Euclidean space, relative to a closed set).
-/

public section

open Set Function Metric Filter Topology
open scoped Manifold ContDiff

section Manifold

variable {E F H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

variable {f e : M → F} {ε : M → ℝ} {A O : Set M}

/-- **Relative smooth approximation.** Let `f : M → F` be continuous, `A ⊆ M` closed, and `e` a
map which is `C^n` on a neighbourhood `O` of `A` and agrees with `f` on `A`. Then for every
continuous positive precision `ε`, there is a `C^n` map `g` with `dist (g x) (f x) < ε x` for all
`x`, equal to `e` on a neighbourhood of `A`. -/
theorem Continuous.exists_contMDiff_approx_and_eventuallyEq (n : ℕ∞)
    (hf : Continuous f) (hε : Continuous ε) (hε_pos : ∀ x, 0 < ε x)
    (hA : IsClosed A) (hO : O ∈ 𝓝ˢ A) (he : CMDiff[O] n e) (hfe : EqOn f e A) :
    ∃ g : C^n⟮I, M; 𝓘(ℝ, F), F⟯, (∀ x, dist (g x) (f x) < ε x) ∧ (g : M → F) =ᶠ[𝓝ˢ A] e := by
  have := Manifold.locallyCompact_of_finiteDimensional I (M := M)
  have hAO : A ⊆ interior O := subset_interior_iff_mem_nhdsSet.mpr hO
  have he' : ContinuousOn e (interior O) := (he.mono interior_subset).continuousOn
  -- The open set `O'` where `e` is smooth and `ε / 2`-close to `f`.
  set O' := interior O ∩ {x | dist (e x) (f x) < ε x / 2}
  have hO'open : IsOpen O' := isOpen_iff_mem_nhds.mpr fun x hx ↦
    inter_mem (isOpen_interior.mem_nhds hx.1) <|
      ((he'.continuousAt (isOpen_interior.mem_nhds hx.1)).dist hf.continuousAt).eventually_lt
        (hε.continuousAt.div_const 2) hx.2
  have hAO' : A ⊆ O' := fun x hx ↦ ⟨hAO hx, by simpa [hfe hx] using half_pos (hε_pos x)⟩
  obtain ⟨ρ, hρ0, hρ1, hρI⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed I (n := 0)
    hO'open.isClosed_compl hA (disjoint_compl_left_iff_subset.mpr hAO')
  -- The continuous interpolation `h` between `f` and `e`.
  set h : M → F := fun x ↦ f x + ρ x • (e x - f x) with hh
  have hρO' {x : M} (hx : x ∉ O') : ∀ᶠ y in 𝓝 x, ρ y = 0 :=
    hρ0.filter_mono (nhds_le_nhdsSet hx)
  have h_cont : Continuous h := continuous_iff_continuousAt.mpr fun x ↦ by
    by_cases hx : x ∈ O'
    · exact hf.continuousAt.add <| ρ.contMDiff.continuous.continuousAt.smul <|
        (he'.continuousAt (isOpen_interior.mem_nhds hx.1)).sub hf.continuousAt
    · refine hf.continuousAt.congr ?_
      filter_upwards [hρO' hx] with y hy
      simp [hh, hy]
  have h_dist (x : M) : dist (h x) (f x) < ε x / 2 := by
    rw [hh, dist_self_add_left, norm_smul, ← dist_eq_norm, Real.norm_eq_abs,
      abs_of_nonneg (hρI x).1]
    by_cases hx : x ∈ O'
    · exact (mul_le_of_le_one_left dist_nonneg (hρI x).2).trans_lt hx.2
    · simpa [(hρO' hx).self_of_nhds] using half_pos (hε_pos x)
  -- A closed neighbourhood `S` of `A` on which `h = e`, inside an open set where `e` is smooth.
  set W := interior ({x | ρ x = 1} ∩ interior O)
  have hAW : A ⊆ W := subset_interior_iff_mem_nhdsSet.mpr <|
    inter_mem hρ1 (isOpen_interior.mem_nhdsSet.mpr hAO)
  have hhW (x : M) (hx : x ∈ W) : h x = e x := by
    have hρx : ρ x = 1 := (interior_subset hx).1
    simp [hh, hρx]
  obtain ⟨u, hu, hAu, huW⟩ := normal_exists_closure_subset hA isOpen_interior hAW
  have hh_smooth : CMDiff[W] n h :=
    (he.mono ((interior_subset.trans inter_subset_right).trans interior_subset)).congr hhW
  obtain ⟨g, hg, hgS, -⟩ := h_cont.exists_contMDiff_approx_and_eqOn I n (hε.div_const 2)
    (fun x ↦ half_pos (hε_pos x)) isClosed_closure (isOpen_interior.mem_nhdsSet.mpr huW)
    hh_smooth
  refine ⟨g, fun x ↦ ?_, ?_⟩
  · linarith [dist_triangle (g x) (h x) (f x), hg x, h_dist x]
  · exact eventually_of_mem (mem_of_superset (hu.mem_nhdsSet.mpr hAu) subset_closure)
      fun x hx ↦ (hgS hx).trans (hhW x (huW hx))

/-- **Relative smooth approximation, with a homotopy in a prescribed open set.** Under the
hypotheses of `Continuous.exists_contMDiff_approx_and_eventuallyEq`, if moreover `f` takes values
in an open set `U ⊆ F`, the `C^n` approximation `g`, equal to `e` near `A`, can be chosen
homotopic to `f` relative to `A`, by a homotopy which stays within `ε` of `f` and in `U`. -/
theorem Continuous.exists_contMDiff_eventuallyEq_and_homotopyRel (n : ℕ∞)
    (hf : Continuous f) (hε : Continuous ε) (hε_pos : ∀ x, 0 < ε x)
    (hA : IsClosed A) (hO : O ∈ 𝓝ˢ A) (he : CMDiff[O] n e) (hfe : EqOn f e A)
    {U : Set F} (hU : IsOpen U) (hfU : ∀ x, f x ∈ U) :
    ∃ g : C^n⟮I, M; 𝓘(ℝ, F), F⟯, (g : M → F) =ᶠ[𝓝ˢ A] e ∧
      ∃ G : ContinuousMap.HomotopyRel ⟨f, hf⟩ g A,
        ∀ t x, dist (G (t, x)) (f x) < ε x ∧ G (t, x) ∈ U := by
  -- A smaller precision `δ` such that the `δ`-ball around each `f x` lies in `U`.
  obtain ⟨η, hη, -, hη_pos, hηU⟩ := hU.exists_continuous_forall_dist_lt hf
  set δ : M → ℝ := fun x ↦ min (ε x) (η x)
  have hδ : Continuous δ := hε.min hη
  have hδ_pos (x : M) : 0 < δ x := lt_min (hε_pos x) (hη_pos x (hfU x))
  obtain ⟨g, hg, hge⟩ := hf.exists_contMDiff_approx_and_eventuallyEq I n hδ hδ_pos hA hO he hfe
  have hdist (t : unitInterval) (x : M) :
      dist (f x + (t : ℝ) • (g x - f x)) (f x) < δ x := by
    rw [dist_self_add_left, norm_smul, ← dist_eq_norm, Real.norm_eq_abs,
      abs_of_nonneg (unitInterval.nonneg t)]
    exact (mul_le_of_le_one_left dist_nonneg (unitInterval.le_one t)).trans_lt (hg x)
  refine ⟨g, hge,
    { toFun := fun p ↦ f p.2 + (p.1 : ℝ) • (g p.2 - f p.2)
      continuous_toFun := by fun_prop
      map_zero_left := fun x ↦ by simp
      map_one_left := fun x ↦ by simp
      prop' := fun t x hx ↦ by simp [(hge.self_of_nhdsSet hx).trans (hfe hx).symm] },
    fun t x ↦ ⟨(hdist t x).trans_le (min_le_left _ _),
      hηU x _ ((hdist t x).trans_le (min_le_right _ _))⟩⟩

/-- **Relative smooth approximation on a retract.** Let `D ⊆ M` be a set onto which `M` retracts
continuously, `f` continuous on `D`, `A ⊆ D` closed in `M`, and `e` a map which is `C^n` on a
neighbourhood of `A` and agrees with `f` on `A`. Then for every continuous positive precision `ε`
there is a `C^n` map `g : M → F` with `dist (g x) (f x) < ε x` for `x ∈ D`, equal to `e` on a
neighbourhood of `A`. -/
theorem ContinuousOn.exists_contMDiff_approx_and_eventuallyEq_of_retraction (n : ℕ∞) {D : Set M}
    {r : M → M} (hf : ContinuousOn f D) (hr : Continuous r) (hrD : ∀ x, r x ∈ D)
    (hrid : ∀ x ∈ D, r x = x) (hε : Continuous ε) (hε_pos : ∀ x, 0 < ε x)
    (hA : IsClosed A) (hAD : A ⊆ D) (hO : O ∈ 𝓝ˢ A) (he : CMDiff[O] n e) (hfe : EqOn f e A) :
    ∃ g : C^n⟮I, M; 𝓘(ℝ, F), F⟯, (∀ x ∈ D, dist (g x) (f x) < ε x) ∧
      (g : M → F) =ᶠ[𝓝ˢ A] e := by
  obtain ⟨g, hg, hge⟩ := (hf.comp_continuous hr hrD).exists_contMDiff_approx_and_eventuallyEq I n
    hε hε_pos hA hO he fun x hx ↦ by simp [hrid x (hAD hx), hfe hx]
  exact ⟨g, fun x hx ↦ by simpa [hrid x hx] using hg x, hge⟩

end Manifold

section NormedSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {f e : E → F} {ε : E → ℝ} {A O : Set E}

/-- **Relative smooth approximation on a normed space.** Let `f : E → F` be continuous, `A ⊆ E`
closed, and `e` a map which is `C^n` on a neighbourhood `O` of `A` and agrees with `f` on `A`.
Then for every continuous positive precision `ε`, there is a `C^n` map `g` with
`dist (g x) (f x) < ε x` for all `x`, equal to `e` on a neighbourhood of `A`. -/
theorem Continuous.exists_contDiff_approx_and_eventuallyEq (n : ℕ∞)
    (hf : Continuous f) (hε : Continuous ε) (hε_pos : ∀ x, 0 < ε x)
    (hA : IsClosed A) (hO : O ∈ 𝓝ˢ A) (he : ContDiffOn ℝ n e O) (hfe : EqOn f e A) :
    ∃ g : E → F, ContDiff ℝ n g ∧ (∀ x, dist (g x) (f x) < ε x) ∧ g =ᶠ[𝓝ˢ A] e := by
  obtain ⟨g, hg, hge⟩ := hf.exists_contMDiff_approx_and_eventuallyEq 𝓘(ℝ, E) n hε hε_pos hA hO
    he.contMDiffOn hfe
  exact ⟨g, g.contMDiff.contDiff, hg, hge⟩

/-- **Relative smooth approximation on a closed ball.** Let `f` be continuous on the closed ball
`closedBall c r` of a finite-dimensional normed space, and `e` a map which is `C^n` on a
neighbourhood of the sphere `sphere c r` and agrees with `f` there. Then for every continuous
positive precision `ε`, there is a `C^n` map `g : E → F` with `dist (g x) (f x) < ε x` on the
closed ball, equal to `e` on a neighbourhood of the sphere. For `0 < r` the sphere is the
frontier of the ball, so this applies to the interval, to the square (a ball for the sup norm on
`ℝ × ℝ`) and to the closed disc. -/
theorem ContinuousOn.exists_contDiff_approx_and_eventuallyEq_sphere (n : ℕ∞) {c : E} {r : ℝ}
    (hf : ContinuousOn f (closedBall c r)) (hε : Continuous ε) (hε_pos : ∀ x, 0 < ε x)
    (hO : O ∈ 𝓝ˢ (sphere c r)) (he : ContDiffOn ℝ n e O) (hfe : EqOn f e (sphere c r)) :
    ∃ g : E → F, ContDiff ℝ n g ∧ (∀ x ∈ closedBall c r, dist (g x) (f x) < ε x) ∧
      g =ᶠ[𝓝ˢ (sphere c r)] e := by
  rcases lt_or_ge r 0 with hr | hr
  · exact ⟨0, contDiff_const, by simp [closedBall_eq_empty.mpr hr],
      by simp [sphere_eq_empty_of_neg hr, EventuallyEq]⟩
  -- A continuous retraction `ρ` of `E` onto the closed ball.
  obtain ⟨ρ, hρ, hρD, hρid⟩ : ∃ ρ : E → E, Continuous ρ ∧ (∀ x, ρ x ∈ closedBall c r) ∧
      ∀ x ∈ closedBall c r, ρ x = x := by
    rcases hr.eq_or_lt with rfl | hr
    · exact ⟨fun _ ↦ c, continuous_const, fun _ ↦ by simp, fun x hx ↦ by simp_all⟩
    have hmax (x : E) : 0 < max 1 (‖x - c‖ / r) := one_pos.trans_le (le_max_left _ _)
    refine ⟨fun x ↦ c + (max 1 (‖x - c‖ / r))⁻¹ • (x - c), ?_, fun x ↦ ?_, fun x hx ↦ ?_⟩
    · exact continuous_const.add <| ((continuous_const.max (by fun_prop)).inv₀
        fun x ↦ (hmax x).ne').smul (by fun_prop)
    · beta_reduce
      rw [mem_closedBall, dist_self_add_left, norm_smul, norm_inv,
        Real.norm_of_nonneg (hmax x).le, inv_mul_le_iff₀ (hmax x)]
      exact (div_le_iff₀ hr).mp (le_max_right _ _)
    · rw [mem_closedBall, dist_eq_norm] at hx
      simp [max_eq_left ((div_le_one hr).mpr hx)]
  obtain ⟨g, hg, hge⟩ := hf.exists_contMDiff_approx_and_eventuallyEq_of_retraction 𝓘(ℝ, E) n hρ
    hρD hρid hε hε_pos isClosed_sphere sphere_subset_closedBall hO he.contMDiffOn hfe
  exact ⟨g, g.contMDiff.contDiff, hg, hge⟩

end NormedSpace
