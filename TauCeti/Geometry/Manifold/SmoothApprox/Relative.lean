/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothApprox
public import Mathlib.Topology.Homotopy.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Topology.Homotopy.Affine
import TauCeti.Analysis.Normed.Module.Ball.Retraction
import TauCeti.Topology.MetricSpace.ContinuousRadius

/-!
# Relative smooth approximation into a normed space

Let `M` be a Hausdorff σ-compact manifold over a finite-dimensional real model with corners, `F`
a real normed space, `A ⊆ M` closed and `f : M → F` continuous. Mathlib's
`Continuous.exists_contMDiff_approx_and_eqOn` approximates `f` by a smooth map equal to `f` on
`A`, provided `f` is already smooth near `A`. Here `f` need not be smooth anywhere: it suffices
that a map `e` smooth on a neighbourhood of `A` already fits the prescribed continuous positive
precision on `A`. The approximation `g` is then equal to `e` on a neighbourhood of `A`
(`Continuous.exists_contMDiff_approx_and_eventuallyEq`).

The typical use takes `A` to be the boundary `I.boundary M` and `e` an extension of boundary data
over a collar: a continuous filling of smooth boundary data is approximated by a smooth filling
with the same germ along the boundary. On the closed disc, the continuous filling
`(x, y) ↦ (|y|, 0)` has the boundary trace `θ ↦ (|sin θ|, 0)`, which is the restriction of no
smooth map near the circle, so no smooth map agrees with it on the circle.

Two refinements follow. If `e` agrees with `f` on `A` and `f` takes values in an open set `U ⊆ F`,
then `g` and a homotopy from `f` to `g` relative to `A` can be kept in `U` and within the
prescribed precision of `f` (`Continuous.exists_contMDiff_eventuallyEq_and_homotopyRel`).
If `f` is only given on a subset `D ⊇ A` onto which `M` retracts continuously, the same
approximation holds on `D` (`ContinuousOn.exists_contMDiff_approx_and_eventuallyEq_of_retraction`).
This applies in particular to a closed ball `D` of a finite-dimensional normed space with `A` its
boundary sphere (`ContinuousOn.exists_contDiff_approx_and_eventuallyEq_sphere`): a continuous map
on the interval, the square (a ball for the sup norm on `ℝ × ℝ`) or the disc can be approximated by
a smooth map on the ambient space with a prescribed germ along the boundary.

## Implementation notes

Choose a closed neighbourhood of `A` where `e` is smooth and fits the precision. Impose the
singleton constraint `{e x}` there and the open ball constraint elsewhere. The local smooth
choices are `e` near the closed neighbourhood and the constant `f x` near each point `x`
outside it. Mathlib's `exists_contMDiffMap_forall_mem_convex_of_local` glues the choices, as in
`Continuous.exists_contMDiff_approx_and_eqOn` (A. Dedecker and P. Massot).

## Main results

* `Continuous.exists_contMDiff_approx_and_eventuallyEq`: relative smooth approximation of a
  continuous map with a prescribed germ that already fits the precision on a closed set.
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
map which is `C^n` on a neighbourhood `O` of `A`. Given a continuous positive precision `ε`,
assume `dist (e x) (f x) < ε x` on `A`. Then there is a `C^n` map `g` within that precision of
`f` everywhere, equal to `e` on a neighbourhood of `A`. -/
theorem Continuous.exists_contMDiff_approx_and_eventuallyEq (n : ℕ∞)
    (hf : Continuous f) (hε : Continuous ε) (hε_pos : ∀ x, 0 < ε x)
    (hA : IsClosed A) (hO : O ∈ 𝓝ˢ A) (he : CMDiff[O] n e)
    (hef : ∀ x ∈ A, dist (e x) (f x) < ε x) :
    ∃ g : C^n⟮I, M; 𝓘(ℝ, F), F⟯, (∀ x, dist (g x) (f x) < ε x) ∧ (g : M → F) =ᶠ[𝓝ˢ A] e := by
  have := Manifold.locallyCompact_of_finiteDimensional I (M := M)
  let U := interior O ∩ {x | dist (e x) (f x) < ε x}
  have hdist : ContinuousOn (fun x ↦ dist (e x) (f x)) (interior O) :=
    continuous_dist.comp_continuousOn
      ((he.continuousOn.mono interior_subset).prodMk hf.continuousOn)
  have hU : IsOpen U :=
    (hdist.prodMk hε.continuousOn).isOpen_inter_preimage
      isOpen_interior isOpen_lt_prod
  have hAO : A ⊆ interior O := subset_interior_iff_mem_nhdsSet.mpr hO
  have hAU : A ⊆ U := fun x hx ↦ ⟨hAO hx, hef x hx⟩
  obtain ⟨W, hW, hAW, hWU⟩ := normal_exists_closure_subset hA hU hAU
  let S (x : M) := ball (f x) (ε x) ∩ {v : F | x ∈ closure W → v = e x}
  have hS (x : M) : Convex ℝ (S x) :=
    (convex_ball _ _).inter (convex_singleton (e x)).setOfPred_const_imp
  obtain ⟨g, hg⟩ := exists_contMDiffMap_forall_mem_convex_of_local I hS (n := n) (fun x ↦ by
    by_cases hx : x ∈ closure W
    · exact ⟨U, hU.mem_nhds (hWU hx), e, he.mono (inter_subset_left.trans interior_subset),
        fun y hy ↦ ⟨hy.2, fun _ ↦ rfl⟩⟩
    · have hnear := (continuous_const.dist hf).continuousAt.eventually_lt hε.continuousAt
          (by simpa using hε_pos x : dist (f x) (f x) < ε x)
      have hgood : ∀ᶠ y in 𝓝 x, f x ∈ S y := by
        filter_upwards [hnear, isClosed_closure.isOpen_compl.eventually_mem hx] with y hy hyW
        exact ⟨hy, fun hy' ↦ (hyW hy').elim⟩
      exact ⟨_, hgood, fun _ ↦ f x, contMDiffOn_const, fun _ hy ↦ hy⟩)
  refine ⟨g, fun x ↦ (hg x).1, ?_⟩
  filter_upwards [hW.mem_nhdsSet.mpr hAW] with x hx using (hg x).2 (subset_closure hx)

/-- **Relative smooth approximation, with a homotopy in a prescribed open set.** If `e` agrees
with `f` on `A` and `f` takes values in an open set `U ⊆ F`, the approximation from
`Continuous.exists_contMDiff_approx_and_eventuallyEq` can be chosen homotopic to `f` relative to
`A`, by a homotopy which stays within `ε` of `f` and in `U`. -/
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
  obtain ⟨g, hg, hge⟩ := hf.exists_contMDiff_approx_and_eventuallyEq I n hδ hδ_pos hA hO he
    (fun x hx ↦ by simpa [← hfe hx] using hδ_pos x)
  let G : ContinuousMap.HomotopyRel ⟨f, hf⟩ g A :=
    { toHomotopy := ContinuousMap.Homotopy.affine ⟨f, hf⟩ g
      prop' := fun t x hx ↦ by
        -- Pointwise, the affine homotopy is the line map between the endpoint values.
        change AffineMap.lineMap (f x) (g x) (t : ℝ) = f x
        simp [(hge.self_of_nhdsSet hx).trans (hfe hx).symm] }
  refine ⟨g, hge, G, fun t x ↦ ?_⟩
  have hdist : dist (G (t, x)) (f x) < δ x := by
    -- Evaluate the affine homotopy as a line map to use its distance formula.
    change dist (AffineMap.lineMap (f x) (g x) (t : ℝ)) (f x) < δ x
    rw [dist_lineMap_left, Real.norm_of_nonneg t.property.1, dist_comm (f x) (g x)]
    exact (mul_le_of_le_one_left dist_nonneg t.property.2).trans_lt (hg x)
  exact ⟨hdist.trans_le (min_le_left _ _), hηU x _ (hdist.trans_le (min_le_right _ _))⟩

/-- **Relative smooth approximation on a retract.** Let `D ⊆ M` be a set onto which `M` retracts
continuously, `f` continuous on `D`, `A ⊆ D` closed in `M`, and `e` a map which is `C^n` on a
neighbourhood of `A`. If `e` fits the precision `ε` on `A` and `ε` is positive and continuous on
`D`, there is a `C^n` map `g : M → F` with `dist (g x) (f x) < ε x` for `x ∈ D`, equal to `e`
on a neighbourhood of `A`. -/
theorem ContinuousOn.exists_contMDiff_approx_and_eventuallyEq_of_retraction (n : ℕ∞) {D : Set M}
    {r : M → M} (hf : ContinuousOn f D) (hr : Continuous r) (hrD : ∀ x, r x ∈ D)
    (hrid : ∀ x ∈ D, r x = x) (hε : ContinuousOn ε D) (hε_pos : ∀ x ∈ D, 0 < ε x)
    (hA : IsClosed A) (hAD : A ⊆ D) (hO : O ∈ 𝓝ˢ A) (he : CMDiff[O] n e)
    (hef : ∀ x ∈ A, dist (e x) (f x) < ε x) :
    ∃ g : C^n⟮I, M; 𝓘(ℝ, F), F⟯, (∀ x ∈ D, dist (g x) (f x) < ε x) ∧
      (g : M → F) =ᶠ[𝓝ˢ A] e := by
  obtain ⟨g, hg, hge⟩ := (hf.comp_continuous hr hrD).exists_contMDiff_approx_and_eventuallyEq I n
    (hε.comp_continuous hr hrD) (fun x ↦ hε_pos (r x) (hrD x)) hA hO he
    (fun x hx ↦ by simpa only [Function.comp_apply, hrid x (hAD hx)] using hef x hx)
  exact ⟨g, fun x hx ↦ by simpa only [Function.comp_apply, hrid x hx] using hg x, hge⟩

end Manifold

section NormedSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {f e : E → F} {ε : E → ℝ} {A O : Set E}

/-- **Relative smooth approximation on a normed space.** Let `f : E → F` be continuous, `A ⊆ E`
closed, and `e` a map which is `C^n` on a neighbourhood `O` of `A`. If `e` already fits the
continuous positive precision `ε` on `A`, there is a `C^n` map `g` with
`dist (g x) (f x) < ε x` for all `x`, equal to `e` on a neighbourhood of `A`. -/
theorem Continuous.exists_contDiff_approx_and_eventuallyEq (n : ℕ∞)
    (hf : Continuous f) (hε : Continuous ε) (hε_pos : ∀ x, 0 < ε x)
    (hA : IsClosed A) (hO : O ∈ 𝓝ˢ A) (he : ContDiffOn ℝ n e O)
    (hef : ∀ x ∈ A, dist (e x) (f x) < ε x) :
    ∃ g : E → F, ContDiff ℝ n g ∧ (∀ x, dist (g x) (f x) < ε x) ∧ g =ᶠ[𝓝ˢ A] e := by
  obtain ⟨g, hg, hge⟩ := hf.exists_contMDiff_approx_and_eventuallyEq 𝓘(ℝ, E) n hε hε_pos hA hO
    he.contMDiffOn hef
  exact ⟨g, g.contMDiff.contDiff, hg, hge⟩

/-- **Relative smooth approximation on a closed ball.** Let `f` be continuous on the closed ball
`closedBall c r` of a finite-dimensional normed space, and `e` a map which is `C^n` on a
neighbourhood of the sphere `sphere c r`. If `e` fits the precision `ε` on the sphere and `ε`
is continuous and positive on the closed ball, there is a `C^n` map `g : E → F` with
`dist (g x) (f x) < ε x` on the closed ball, equal to `e` on a neighbourhood of the sphere.
For `0 < r` the sphere is the frontier of the ball, so this applies to the interval, to the square
(a ball for the sup norm on `ℝ × ℝ`) and to the closed disc. -/
theorem ContinuousOn.exists_contDiff_approx_and_eventuallyEq_sphere (n : ℕ∞) {c : E} {r : ℝ}
    (hf : ContinuousOn f (closedBall c r)) (hε : ContinuousOn ε (closedBall c r))
    (hε_pos : ∀ x ∈ closedBall c r, 0 < ε x) (hO : O ∈ 𝓝ˢ (sphere c r))
    (he : ContDiffOn ℝ n e O) (hef : ∀ x ∈ sphere c r, dist (e x) (f x) < ε x) :
    ∃ g : E → F, ContDiff ℝ n g ∧ (∀ x ∈ closedBall c r, dist (g x) (f x) < ε x) ∧
      g =ᶠ[𝓝ˢ (sphere c r)] e := by
  rcases lt_or_ge r 0 with hr | hr
  · exact ⟨0, contDiff_const, by simp [closedBall_eq_empty.mpr hr],
      by simp [sphere_eq_empty_of_neg hr, EventuallyEq]⟩
  -- Retract `E` onto the closed ball radially.
  obtain ⟨g, hg, hge⟩ := hf.exists_contMDiff_approx_and_eventuallyEq_of_retraction 𝓘(ℝ, E) n
    (TauCeti.lipschitzWith_centeredRadialRetraction hr).continuous
    (TauCeti.centeredRadialRetraction_mem_closedBall hr)
    (fun _ ↦ TauCeti.centeredRadialRetraction_of_mem_closedBall) hε hε_pos isClosed_sphere
    sphere_subset_closedBall hO he.contMDiffOn hef
  exact ⟨g, g.contMDiff.contDiff, hg, hge⟩

end NormedSpace
