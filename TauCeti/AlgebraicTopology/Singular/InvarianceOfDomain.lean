/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.JordanBrouwer
public import Mathlib.Topology.Compactification.OnePoint.Sphere
import TauCeti.Topology.Connected.PathConnected

/-!
# Invariance of domain

Brouwer's **invariance of domain**: a continuous injective map from an open subset of `ℝⁿ` to
`ℝⁿ` has open image. More generally, let `M` and `N` be topological manifolds without boundary,
charted on finite-dimensional real normed spaces of the same dimension. Then a map `f : M → N`
which is continuous and injective on an open set `U` maps `U` to an open set
(`IsOpen.image_of_continuousOn_of_injOn`), and a continuous injection `M → N` is an open
embedding (`Continuous.isOpenEmbedding_of_injective`).

Consequently, interiors of subsets are intrinsic: if `A ⊆ M` and `B ⊆ N` are homeomorphic, a
point of `A` lies in the interior of `A` exactly when its image lies in the interior of `B`
(`Homeomorph.coe_apply_mem_interior_iff`), and likewise for frontiers
(`Homeomorph.coe_apply_mem_frontier_iff`). This identifies, for instance, the boundary surface of
a handlebody embedded in a `3`-manifold with the frontier of its image.

The proof is the one in Hatcher. Embed the target `F` in the sphere `Sⁿ`, its one-point
compactification (`onePointEquivSphereOfFinrankEq`). For a closed ball `D` in the domain on which
`f` is continuous and injective, with boundary sphere `S`, the complement of `f(S)` in `Sⁿ` is
not connected by the Jordan–Brouwer separation theorem
(`TauCeti.not_isPreconnected_compl_range_sphere`). It is the disjoint union of the
complement of `f(D)`, which is path connected because it is acyclic
(`TauCeti.isPathConnected_sphere_compl_range_closedBall`), and of the image of the
open ball, which is path connected as the image of a convex set. So these are its two path
components, and the image of the open ball is open, as a path component of an open subset of a
manifold.

## Main results

* `IsOpen.image_of_continuousOn_of_injOn`: **invariance of domain** for manifolds without
  boundary modelled on finite-dimensional real normed spaces of the same dimension.
* `Continuous.isOpenEmbedding_of_injective`: a continuous injection between such manifolds is an
  open embedding.
* `Homeomorph.coe_apply_mem_interior_iff` and `Homeomorph.coe_apply_mem_frontier_iff`: a
  homeomorphism between subsets of such manifolds matches their interiors and their frontiers.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.B, Theorem 2B.3.
* L. E. J. Brouwer, *Beweis der Invarianz des n-dimensionalen Gebiets*, Math. Ann. 71 (1912),
  305–313.
-/

public section

open Function Metric Module Set Topology

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **Invariance of domain, local form.** If `f` is continuous and injective on a closed ball of
positive radius in a finite-dimensional real normed space, with values in a normed space of the
same dimension, then the image of the open ball is open. -/
private theorem isOpen_image_ball (hEF : finrank ℝ E = finrank ℝ F) {f : E → F} {x : E} {r : ℝ}
    (hr : 0 < r) (hf : ContinuousOn f (closedBall x r)) (hinj : InjOn f (closedBall x r)) :
    IsOpen (f '' ball x r) := by
  set n := finrank ℝ F
  -- Embed `F` in the sphere `Sⁿ` as the complement of a point.
  let Φ : OnePoint F ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
    onePointEquivSphereOfFinrankEq (by simp [n])
  let j : F → sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := Φ ∘ (↑)
  have hj : IsOpenEmbedding j := Φ.isOpenEmbedding.comp OnePoint.isOpenEmbedding_coe
  -- Parametrize the closed ball of radius `r` about `x` by the closed unit ball.
  let a : E → E := fun y ↦ x + r • y
  have ha_norm (y : E) : dist (a y) x = r * ‖y‖ := by
    simp [a, dist_eq_norm, norm_smul, abs_of_pos hr]
  have ha_closedBall {y : E} (hy : y ∈ closedBall (0 : E) 1) : a y ∈ closedBall x r := by
    rw [mem_closedBall, ha_norm]
    simpa using mul_le_of_le_one_right hr.le (mem_closedBall_zero_iff.1 hy)
  have ha_inj : Injective a := fun y z h ↦ smul_right_injective E hr.ne' (add_left_cancel h)
  have hcont {s : Set E} (hs : s ⊆ closedBall (0 : E) 1) :
      Continuous fun y : s ↦ j (f (a y)) :=
    hj.continuous.comp (hf.comp_continuous (by fun_prop) fun y ↦ ha_closedBall (hs y.2))
  have hinj' {s : Set E} (hs : s ⊆ closedBall (0 : E) 1) : Injective fun y : s ↦ j (f (a y)) :=
    fun y z h ↦ Subtype.ext <| ha_inj <|
      hinj (ha_closedBall (hs y.2)) (ha_closedBall (hs z.2)) (hj.injective h)
  let hD : closedBall (0 : E) 1 → sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
    fun y ↦ j (f (a y))
  let hS : sphere (0 : E) 1 → sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
    fun y ↦ j (f (a y))
  -- `A` is the complement of the image of the sphere of radius `r`, `B` the image of the open
  -- ball and `C` the complement of the image of the closed ball.
  set A := (range hS)ᶜ
  set B := j '' (f '' ball x r) with hBdef
  set C := (range hD)ᶜ
  have hBA : B ⊆ A := by
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩ ⟨y, hy⟩
    have hzy : z = a y :=
      hinj (ball_subset_closedBall hz) (ha_closedBall (sphere_subset_closedBall y.2))
        (hj.injective hy).symm
    rw [hzy, mem_ball, ha_norm, mem_sphere_zero_iff_norm.1 y.2, mul_one] at hz
    exact hz.false
  have hABC : A ⊆ B ∪ C := by
    rintro p hpA
    by_contra hp
    obtain ⟨hpB, hpC⟩ := not_or.1 hp
    obtain ⟨y, rfl⟩ := not_not.1 hpC
    rcases (mem_closedBall_zero_iff.1 y.2).lt_or_eq with hy | hy
    · refine hpB ⟨f (a y), ⟨a y, ?_, rfl⟩, rfl⟩
      rw [mem_ball, ha_norm]
      simpa using mul_lt_of_lt_one_right hr hy
    · exact hpA ⟨⟨y, mem_sphere_zero_iff_norm.2 hy⟩, rfl⟩
  have hCA : C ⊆ A := compl_subset_compl.2 <| by
    rintro _ ⟨y, rfl⟩
    exact ⟨⟨y, sphere_subset_closedBall y.2⟩, rfl⟩
  have hfx : j (f x) ∈ B := ⟨f x, ⟨x, mem_ball_self hr, rfl⟩, rfl⟩
  -- `B` and `C` are path connected, and `C` is nonempty: it contains the point at infinity.
  have hB : IsPathConnected B := by
    rw [hBdef, ← image_comp]
    exact ((convex_ball x r).isPathConnected (nonempty_ball.2 hr)).image'
      (hj.continuous.comp_continuousOn (hf.mono ball_subset_closedBall))
  have hC : IsPathConnected C := by
    refine isPathConnected_sphere_compl_range_closedBall (hcont subset_rfl) (hinj' subset_rfl)
      ⟨Φ OnePoint.infty, ?_⟩
    rintro ⟨y, hy⟩
    exact OnePoint.coe_ne_infty _ (Φ.injective hy)
  -- By the Jordan–Brouwer separation theorem `A` is not path connected, so `B` is a path
  -- component of `A`.
  have hcomp : pathComponentIn A (j (f x)) = B :=
    hB.pathComponentIn_eq_of_not_isPathConnected hC hBA hCA hABC hfx fun hA ↦
      not_isPreconnected_compl_range_sphere (by simp [hEF]) (hcont sphere_subset_closedBall)
        (hinj' sphere_subset_closedBall) hA.isConnected.isPreconnected
  -- A path component of an open subset of a manifold is open.
  have : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) := ⟨by simp⟩
  have := ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin n))
    (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
  have hA : IsOpen A := (isCompact_range (hcont sphere_subset_closedBall)).isClosed.isOpen_compl
  have hBo : IsOpen B := hcomp ▸ hA.pathComponentIn _
  rw [← preimage_image_eq (f '' ball x r) hj.injective]
  exact hBo.preimage hj.continuous

end TauCeti

variable {E F M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace F N]

/-- **Invariance of domain.** Let `M` and `N` be topological manifolds without boundary, charted
on finite-dimensional real normed spaces of the same dimension. If `f : M → N` is continuous and
injective on an open set `U`, then `f '' U` is open. For `M` and `N` normed spaces, this is
Brouwer's theorem that a continuous injection from an open subset of `ℝⁿ` to `ℝⁿ` has open
image. -/
theorem IsOpen.image_of_continuousOn_of_injOn {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContinuousOn f U) (hinj : InjOn f U) (hEF : finrank ℝ E = finrank ℝ F) :
    IsOpen (f '' U) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x, hx, rfl⟩
  -- Read `f` in charts near `x` and `f x`, on an open set `W` around `x`.
  set φ := chartAt E x
  set ψ := chartAt F (f x)
  set W := φ.source ∩ (U ∩ f ⁻¹' ψ.source)
  have hW : IsOpen W := φ.open_source.inter (hf.isOpen_inter_preimage hU ψ.open_source)
  have hxW : x ∈ W := ⟨mem_chart_source E x, hx, mem_chart_source F (f x)⟩
  have hV : IsOpen (φ '' W) := φ.isOpen_image_of_subset_source hW inter_subset_left
  have hVW {y : E} (hy : y ∈ (φ : M → E) '' W) : φ.symm y ∈ W := by
    obtain ⟨w, hw, rfl⟩ := hy
    rwa [φ.left_inv hw.1]
  have hVt : φ '' W ⊆ φ.target := φ.image_source_eq_target ▸ image_mono inter_subset_left
  let g : E → F := ψ ∘ f ∘ φ.symm
  have hg : ContinuousOn g (φ '' W) :=
    ψ.continuousOn.comp ((hf.mono fun w (hw : w ∈ W) ↦ hw.2.1).comp (φ.continuousOn_symm.mono hVt)
      fun _ hy ↦ hVW hy) fun _ hy ↦ (hVW hy).2.2
  have hginj : InjOn g (φ '' W) := fun y hy z hz hyz ↦
    φ.symm.injOn (φ.symm_source ▸ hVt hy) (φ.symm_source ▸ hVt hz) <|
      hinj (hVW hy).2.1 (hVW hz).2.1 (ψ.injOn (hVW hy).2.2 (hVW hz).2.2 hyz)
  -- A closed ball around `φ x` in `φ '' W` has open image under `g`.
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.1 hV (φ x) ⟨x, hxW, rfl⟩
  have hball : closedBall (φ x) (ε / 2) ⊆ φ '' W :=
    (closedBall_subset_ball (half_lt_self hε)).trans hεV
  have hO := TauCeti.isOpen_image_ball hEF (half_pos hε) (hg.mono hball) (hginj.mono hball)
  have hOt : g '' ball (φ x) (ε / 2) ⊆ ψ.target := by
    rintro _ ⟨y, hy, rfl⟩
    exact ψ.map_source (hVW (hball (ball_subset_closedBall hy))).2.2
  refine Filter.mem_of_superset ((ψ.symm.isOpen_image_of_subset_source hO
    (ψ.symm_source ▸ hOt)).mem_nhds ⟨g (φ x), ⟨φ x, mem_ball_self (half_pos hε), rfl⟩, ?_⟩) ?_
  · simp [g, φ.left_inv (mem_chart_source E x), ψ.left_inv (mem_chart_source F (f x))]
  · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have hyW := hVW (hball (ball_subset_closedBall hy))
    exact ⟨φ.symm y, hyW.2.1, (ψ.left_inv hyW.2.2).symm⟩

/-- **Invariance of domain, global form.** A continuous injection between topological manifolds
without boundary, charted on finite-dimensional real normed spaces of the same dimension, is an
open embedding. -/
theorem Continuous.isOpenEmbedding_of_injective {f : M → N} (hf : Continuous f)
    (hinj : Injective f) (hEF : finrank ℝ E = finrank ℝ F) : IsOpenEmbedding f :=
  .of_continuous_injective_isOpenMap hf hinj fun _ hU ↦
    hU.image_of_continuousOn_of_injOn hf.continuousOn hinj.injOn hEF

namespace Homeomorph

variable {A : Set M} {B : Set N}

/-- A homeomorphism between subsets of manifolds of the same dimension maps interior points to
interior points. -/
private theorem coe_apply_mem_interior (e : A ≃ₜ B) (hEF : finrank ℝ E = finrank ℝ F) {x : A}
    (hx : (x : M) ∈ interior A) : (e x : N) ∈ interior B := by
  classical
  -- Extend `e` arbitrarily off `A`; on the interior of `A` it is continuous and injective.
  let g : M → N := fun y ↦ if hy : y ∈ A then e ⟨y, hy⟩ else e x
  have hgA (y : A) : g y = e y := by simp [g]
  have hg : ContinuousOn g (interior A) := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert (continuous_subtype_val.comp e.continuous).comp
      (continuous_inclusion (interior_subset (s := A))) using 1
    ext y
    exact hgA ⟨y, interior_subset y.2⟩
  have hginj : InjOn g (interior A) := fun y hy z hz hyz ↦ by
    have := hgA ⟨y, interior_subset hy⟩ ▸ hgA ⟨z, interior_subset hz⟩ ▸ hyz
    exact congrArg Subtype.val (e.injective (Subtype.ext this))
  refine interior_maximal ?_ (isOpen_interior.image_of_continuousOn_of_injOn hg hginj hEF)
    ⟨x, hx, hgA x⟩
  rintro _ ⟨y, hy, rfl⟩
  exact hgA ⟨y, interior_subset hy⟩ ▸ (e _).2

/-- **Invariance of interior points.** Let `A` and `B` be homeomorphic subsets of topological
manifolds without boundary, charted on finite-dimensional real normed spaces of the same
dimension. Then a point of `A` lies in the interior of `A` exactly when its image lies in the
interior of `B`. -/
theorem coe_apply_mem_interior_iff (e : A ≃ₜ B) (hEF : finrank ℝ E = finrank ℝ F) (x : A) :
    (e x : N) ∈ interior B ↔ (x : M) ∈ interior A :=
  ⟨fun h ↦ e.symm_apply_apply x ▸ e.symm.coe_apply_mem_interior hEF.symm h,
    e.coe_apply_mem_interior hEF⟩

/-- **Invariance of the frontier.** Let `A` and `B` be homeomorphic subsets of topological
manifolds without boundary, charted on finite-dimensional real normed spaces of the same
dimension. Then a point of `A` lies in the frontier of `A` exactly when its image lies in the
frontier of `B`. -/
theorem coe_apply_mem_frontier_iff (e : A ≃ₜ B) (hEF : finrank ℝ E = finrank ℝ F) (x : A) :
    (e x : N) ∈ frontier B ↔ (x : M) ∈ frontier A := by
  simp only [frontier, mem_sdiff, subset_closure (e x).2, subset_closure x.2, true_and,
    e.coe_apply_mem_interior_iff hEF]

end Homeomorph
