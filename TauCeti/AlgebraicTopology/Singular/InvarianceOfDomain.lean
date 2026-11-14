/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.JordanBrouwer
public import Mathlib.Topology.Compactification.OnePoint.Sphere
import TauCeti.Analysis.Normed.Module.Connected
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

For maps between finite-dimensional real normed spaces of the same dimension, the image of `U` is
still open when `f` is injective on `U` only away from a compact fibre `M = U ∩ f⁻¹{p}` of a single
point `p`, in M. Brown's language the only *inverse set* of `f` on `U`
(`IsOpen.image_of_continuousOn_of_injOn_sdiff`, the one-inverse-set case of Brown's Theorem 0).
Away from `p` this is invariance of domain, applied to `U \ M`. At a value `p` of `f` on `U`,
choose a compact `K ⊆ U` with `M` in its interior `V`. A small ball `ball p r` around `p` misses
the image of `K \ V`, so within it the image of `V \ M` is relatively closed in the punctured ball
and open. In dimension at least two the punctured ball is connected, and the image of `V \ M`
accumulates at `p`, so it fills the punctured ball. In dimension one the punctured ball has two
sides; if the image of `V \ M` filled only one, then the segments leaving `M` in the two
directions of `E` would cross the same values near `p`, contradicting injectivity.

## Main results

* `IsOpen.image_of_continuousOn_of_injOn`: **invariance of domain** for manifolds without
  boundary modelled on finite-dimensional real normed spaces of the same dimension.
* `Continuous.isOpenEmbedding_of_injective`: a continuous injection between such manifolds is an
  open embedding, and `IsOpen.isOpenEmbedding_domRestrict_of_continuousOn_of_injOn` is its form for
  a map continuous and injective on an open set.
* `Continuous.surjective_of_injective`: a continuous injection of a compact manifold into a
  connected manifold of the same dimension is surjective.
* `Homeomorph.coe_apply_mem_interior_iff` and `Homeomorph.coe_apply_mem_frontier_iff`: a
  homeomorphism between subsets of such manifolds matches their interiors and their frontiers.
* `Topology.IsOpenEmbedding.finrank_le_of_isEmbedding` and `Topology.IsOpenEmbedding.finrank_eq`:
  **invariance of dimension**, a nonempty open subset of `ℝᵐ` embeds into `ℝⁿ` only if `m ≤ n`.
* `IsOpen.image_of_continuousOn_of_injOn_sdiff`: the image of an open set of a normed space under a
  map injective on it away from one compact fibre is open (Brown's Theorem 0 for one inverse set).

## References

* A. Hatcher, *Algebraic Topology*, Section 2.B, Theorem 2B.3.
* L. E. J. Brouwer, *Beweis der Invarianz des n-dimensionalen Gebiets*, Math. Ann. 71 (1912),
  305–313.
* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76, Theorem 0.
-/

public section

open Function Metric Module Set Topology

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **Invariance of domain, local form on the unit ball.** If `f` is continuous and injective on
the closed unit ball of a finite-dimensional real normed space, with values in a normed space of
the same dimension, then the image of the open unit ball is open. -/
private theorem isOpen_image_ball_zero_one (hEF : finrank ℝ E = finrank ℝ F) {f : E → F}
    (hf : ContinuousOn f (closedBall 0 1)) (hinj : InjOn f (closedBall 0 1)) :
    IsOpen (f '' ball 0 1) := by
  set n := finrank ℝ F
  -- Embed `F` in the sphere `Sⁿ` as the complement of a point.
  let Φ : OnePoint F ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
    onePointEquivSphereOfFinrankEq (by simp [n])
  let j : F → sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := Φ ∘ (↑)
  have hj : IsOpenEmbedding j := Φ.isOpenEmbedding.comp OnePoint.isOpenEmbedding_coe
  have hcont {s : Set E} (hs : s ⊆ closedBall (0 : E) 1) : Continuous fun y : s ↦ j (f y) :=
    hj.continuous.comp (hf.comp_continuous continuous_subtype_val fun y ↦ hs y.2)
  have hinj' {s : Set E} (hs : s ⊆ closedBall (0 : E) 1) : Injective fun y : s ↦ j (f y) :=
    fun y z h ↦ Subtype.ext <| hinj (hs y.2) (hs z.2) (hj.injective h)
  have hjf : InjOn (j ∘ f) (closedBall 0 1) := hj.injective.injOn.comp hinj (mapsTo_univ _ _)
  have hAeq : ((j ∘ f) '' sphere 0 1)ᶜ = (range fun y : sphere (0 : E) 1 ↦ j (f y))ᶜ :=
    congrArg compl (image_eq_range _ _)
  have hCeq : ((j ∘ f) '' closedBall 0 1)ᶜ = (range fun y : closedBall (0 : E) 1 ↦ j (f y))ᶜ :=
    congrArg compl (image_eq_range _ _)
  -- `A` is the complement of the image of the unit sphere, `B` the image of the open ball and
  -- `C` the complement of the image of the closed ball.
  set A := ((j ∘ f) '' sphere 0 1)ᶜ
  set B := (j ∘ f) '' ball 0 1
  set C := ((j ∘ f) '' closedBall 0 1)ᶜ
  -- `B` and `C` are path connected, and `C` is nonempty: it contains the point at infinity.
  have hB : IsPathConnected B :=
    ((convex_ball (0 : E) 1).isPathConnected (nonempty_ball.2 one_pos)).image'
      (hj.continuous.comp_continuousOn (hf.mono ball_subset_closedBall))
  have hC : IsPathConnected C := by
    rw [hCeq]
    refine isPathConnected_sphere_compl_range_closedBall (hcont subset_rfl) (hinj' subset_rfl)
      ⟨Φ OnePoint.infty, ?_⟩
    rintro ⟨y, hy⟩
    exact OnePoint.coe_ne_infty _ (Φ.injective hy)
  -- By the Jordan–Brouwer separation theorem `A` is not path connected, so `B` is a path
  -- component of `A`.
  have hAB : A ⊆ B ∪ C := fun p hp ↦ by
    by_cases hpC : p ∈ (j ∘ f) '' closedBall 0 1
    · exact .inl <| (subset_image_sdiff _ _ _).trans
        (image_mono closedBall_sdiff_sphere.subset) ⟨hpC, hp⟩
    · exact .inr hpC
  have hcomp : pathComponentIn A (j (f 0)) = B :=
    hB.pathComponentIn_eq_of_not_isPathConnected hC
      (sphere_disjoint_ball.symm.image hjf ball_subset_closedBall
        sphere_subset_closedBall).subset_compl_right
      (compl_subset_compl.2 (image_mono sphere_subset_closedBall)) hAB
      ⟨0, mem_ball_self one_pos, rfl⟩ fun hA ↦
      not_isPreconnected_compl_range_sphere (by simp [hEF]) (hcont sphere_subset_closedBall)
        (hinj' sphere_subset_closedBall) (by rw [← hAeq]; exact hA.isConnected.isPreconnected)
  -- A path component of an open subset of a manifold is open.
  have : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) := ⟨by simp⟩
  have := ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin n))
    (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
  have hA : IsOpen A := by
    rw [hAeq]
    exact (isCompact_range (hcont sphere_subset_closedBall)).isClosed.isOpen_compl
  rw [← preimage_image_eq (f '' ball 0 1) hj.injective, ← image_comp]
  exact (hcomp ▸ hA.pathComponentIn _ : IsOpen B).preimage hj.continuous

/-- **Invariance of domain, local form.** If `f` is continuous and injective on a closed ball of
positive radius in a finite-dimensional real normed space, with values in a normed space of the
same dimension, then the image of the open ball is open. -/
private theorem isOpen_image_ball (hEF : finrank ℝ E = finrank ℝ F) {f : E → F} {x : E} {r : ℝ}
    (hr : 0 < r) (hf : ContinuousOn f (closedBall x r)) (hinj : InjOn f (closedBall x r)) :
    IsOpen (f '' ball x r) := by
  -- Reparametrize the closed ball of radius `r` about `x` by the closed unit ball.
  let a : E → E := fun y ↦ x + r • y
  have ha_comp : a = (x +ᵥ ·) ∘ (r • ·) := rfl
  have ha_ball : a '' ball 0 1 = ball x r := by
    rw [ha_comp, image_comp, Set.image_smul, Set.image_vadd]
    exact affinity_unitBall hr x
  have ha_closedBall : a '' closedBall 0 1 = closedBall x r := by
    rw [ha_comp, image_comp, Set.image_smul, Set.image_vadd]
    exact affinity_unitClosedBall hr.le x
  have ha_maps : MapsTo a (closedBall 0 1) (closedBall x r) := ha_closedBall ▸ mapsTo_image _ _
  have ha_inj : Injective a := fun y z h ↦ smul_right_injective E hr.ne' (add_left_cancel h)
  have := isOpen_image_ball_zero_one hEF (f := f ∘ a) (hf.comp (by fun_prop) ha_maps)
    (hinj.comp ha_inj.injOn ha_maps)
  rwa [image_comp, ha_ball] at this

/-- **Invariance of domain for normed spaces.** If `f` is continuous and injective on an open set
`V` of a finite-dimensional real normed space, with values in a normed space of the same
dimension, then `f '' V` is open. -/
private theorem isOpen_image_of_continuousOn_of_injOn (hEF : finrank ℝ E = finrank ℝ F)
    {f : E → F} {V : Set E} (hV : IsOpen V) (hf : ContinuousOn f V) (hinj : InjOn f V) :
    IsOpen (f '' V) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.1 hV x hx
  have hball : closedBall x (ε / 2) ⊆ V :=
    (closedBall_subset_ball (half_lt_self hε)).trans hεV
  exact Filter.mem_of_superset
    ((isOpen_image_ball hEF (half_pos hε) (hf.mono hball) (hinj.mono hball)).mem_nhds
      ⟨x, mem_ball_self (half_pos hε), rfl⟩)
    (image_mono (ball_subset_closedBall.trans hball))

end TauCeti

variable {E F M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace F N]

omit [FiniteDimensional ℝ E] in
/-- **Invariance of domain.** Let `M` and `N` be topological manifolds without boundary, charted
on real normed spaces `E` and `F` with `F` finite dimensional and `finrank ℝ E = finrank ℝ F`. If
`f : M → N` is continuous and injective on an open set `U`, then `f '' U` is open. For `M` and `N`
normed spaces, this is Brouwer's theorem that a continuous injection from an open subset of `ℝⁿ`
to `ℝⁿ` has open image. (If `E` is infinite dimensional then `F` is trivial, `N` is discrete and
`U` is empty.) -/
theorem IsOpen.image_of_continuousOn_of_injOn {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContinuousOn f U) (hinj : InjOn f U) (hEF : finrank ℝ E = finrank ℝ F) :
    IsOpen (f '' U) := by
  by_cases hE : FiniteDimensional ℝ E
  swap
  · -- `E` is infinite dimensional, so `finrank ℝ F = 0` and `N` is discrete: every subset of
    -- `N` is open.
    have hFs : Subsingleton F := Module.finrank_zero_iff.1 (hEF ▸ Module.finrank_of_not_finite hE)
    have := ChartedSpace.discreteTopology (H := F) (M := N)
    exact isOpen_discrete _
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
  have hO := TauCeti.isOpen_image_of_continuousOn_of_injOn hEF hV hg hginj
  have hOt : g '' (φ '' W) ⊆ ψ.target := by
    rintro _ ⟨y, hy, rfl⟩
    exact ψ.map_source (hVW hy).2.2
  refine Filter.mem_of_superset ((ψ.symm.isOpen_image_of_subset_source hO
    (ψ.symm_source ▸ hOt)).mem_nhds ⟨g (φ x), ⟨φ x, ⟨x, hxW, rfl⟩, rfl⟩, ?_⟩) ?_
  · simp [g, φ.left_inv (mem_chart_source E x), ψ.left_inv (mem_chart_source F (f x))]
  · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have hyW := hVW hy
    exact ⟨φ.symm y, hyW.2.1, (ψ.left_inv hyW.2.2).symm⟩

omit [FiniteDimensional ℝ E] in
/-- **Invariance of domain, global form.** A continuous injection between topological manifolds
without boundary, charted on real normed spaces of the same `finrank`, the second finite
dimensional, is an open embedding. -/
theorem Continuous.isOpenEmbedding_of_injective {f : M → N} (hf : Continuous f)
    (hinj : Injective f) (hEF : finrank ℝ E = finrank ℝ F) : IsOpenEmbedding f :=
  .of_continuous_injective_isOpenMap hf hinj fun _ hU ↦
    hU.image_of_continuousOn_of_injOn hf.continuousOn hinj.injOn hEF

omit [FiniteDimensional ℝ E] in
/-- **Invariance of domain, restricted to an open set.** Let `M` and `N` be topological manifolds
without boundary, charted on real normed spaces of the same `finrank`, the second finite
dimensional. If
`f : M → N` is continuous and injective on an open set `U`, then its restriction to `U` is an open
embedding. -/
theorem IsOpen.isOpenEmbedding_domRestrict_of_continuousOn_of_injOn {f : M → N} {U : Set M}
    (hU : IsOpen U) (hf : ContinuousOn f U) (hinj : InjOn f U)
    (hEF : finrank ℝ E = finrank ℝ F) : IsOpenEmbedding (U.domRestrict f) := by
  refine .of_continuous_injective_isOpenMap (continuousOn_iff_continuous_domRestrict.1 hf)
    hinj.injective fun s hs ↦ ?_
  have hsU : ((↑) '' s : Set M) ⊆ U := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  rw [domRestrict_eq, image_comp]
  exact (hU.isOpenMap_subtype_val s hs).image_of_continuousOn_of_injOn (hf.mono hsU)
    (hinj.mono hsU) hEF

omit [FiniteDimensional ℝ E] in
/-- **A continuous injection of a compact manifold into a connected one is onto.** Let `M` and `N`
be topological manifolds without boundary, charted on real normed spaces of the same `finrank`, the
second finite dimensional, with `M` compact and nonempty and `N` Hausdorff and connected. Then a
continuous injection `M → N` is surjective: its image is open by invariance of domain, and closed
as a compact subset of a Hausdorff space. -/
theorem Continuous.surjective_of_injective [CompactSpace M] [Nonempty M] [T2Space N]
    [PreconnectedSpace N] {f : M → N} (hf : Continuous f) (hinj : Injective f)
    (hEF : finrank ℝ E = finrank ℝ F) : Surjective f :=
  range_eq_univ.1 <| IsClopen.eq_univ
    ⟨(isCompact_range hf).isClosed, (hf.isOpenEmbedding_of_injective hinj hEF).isOpen_range⟩
    (range_nonempty f)

namespace Homeomorph

variable {A : Set M} {B : Set N}

omit [FiniteDimensional ℝ E] in
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

namespace Topology.IsOpenEmbedding

variable {X : Type*} [TopologicalSpace X]

omit [FiniteDimensional ℝ F] in
/-- **Invariance of dimension.** If a nonempty space has an open embedding into a real normed
space `F` and an embedding into a finite-dimensional real normed space `E`, then
`finrank ℝ F ≤ finrank ℝ E`. In particular a nonempty open subset of `ℝᵐ` is homeomorphic to no
subset of `ℝⁿ` for `n < m`. -/
theorem finrank_le_of_isEmbedding [Nonempty X] {g : X → F} (hg : IsOpenEmbedding g) {f : X → E}
    (hf : IsEmbedding f) : finrank ℝ F ≤ finrank ℝ E := by
  by_cases hF : FiniteDimensional ℝ F
  swap
  · rw [Module.finrank_of_not_finite hF]
    exact Nat.zero_le _
  by_contra! h
  -- Include `E` in `F` as a proper subspace `ι(E)`.
  obtain ⟨ι, hι⟩ := finrank_le_iff_exists_linearMap.1 h.le
  have hιf : IsEmbedding (ι ∘ f) :=
    (LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.2 hι)).isEmbedding.comp hf
  -- The open set `range g` is homeomorphic to `range (ι ∘ f) ⊆ ι(E)`, so by invariance of
  -- domain the proper subspace `ι(E)` has an interior point.
  let e : range g ≃ₜ range (ι ∘ f) := hg.isEmbedding.toHomeomorph.symm.trans hιf.toHomeomorph
  obtain ⟨x⟩ := ‹Nonempty X›
  have hx : ((⟨g x, mem_range_self x⟩ : range g) : F) ∈ interior (range g) := by
    rw [hg.isOpen_range.interior_eq]
    exact mem_range_self x
  have hint := (e.coe_apply_mem_interior_iff (E := F) (F := F) rfl _).2 hx
  have htop : LinearMap.range ι = ⊤ := Submodule.eq_top_of_nonempty_interior' _
    ⟨_, interior_mono (range_comp_subset_range f ι) hint⟩
  have hrank := LinearMap.finrank_range_of_inj hι
  rw [htop, finrank_top] at hrank
  exact h.ne hrank.symm

/-- **Invariance of dimension.** A nonempty space with open embeddings into finite-dimensional
real normed spaces `E` and `F` forces `finrank ℝ E = finrank ℝ F`. -/
theorem finrank_eq [Nonempty X] {f : X → E} (hf : IsOpenEmbedding f) {g : X → F}
    (hg : IsOpenEmbedding g) : finrank ℝ E = finrank ℝ F :=
  (hf.finrank_le_of_isEmbedding hg.isEmbedding).antisymm (hg.finrank_le_of_isEmbedding
    hf.isEmbedding)

end Topology.IsOpenEmbedding

section InverseSet

open Filter

variable {f : E → F} {p : F}

namespace TauCeti

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Let `m` be a point of an open set `U` on which `f` is continuous, with `f m = p`, and leave `m`
along a direction `w` on which `φ ∘ f` exceeds `φ p` at every positive time with `m + s • w ∈ U`
and `f (m + s • w)` near `p`. Then for some `t > 0` the segment from `m` to `m + t • w` stays in
`U`, and the values of `φ ∘ f` on it cover the interval `Ioc (φ p) (φ (f (m + t • w)))` at
positive times. -/
private theorem exists_segment_Ioc_subset {U : Set E} (hU : IsOpen U) (hf : ContinuousOn f U)
    {m : E} (hmU : m ∈ U) (hfm : f m = p) (w : E) (φ : F →L[ℝ] ℝ) {r : ℝ} (hr : 0 < r)
    (hlt : ∀ s : ℝ, 0 < s → m + s • w ∈ U → f (m + s • w) ∈ ball p r → φ p < φ (f (m + s • w))) :
    ∃ t : ℝ, 0 < t ∧ (∀ s ∈ Icc 0 t, m + s • w ∈ U) ∧ φ p < φ (f (m + t • w)) ∧
      ∀ v ∈ Ioc (φ p) (φ (f (m + t • w))), ∃ s ∈ Ioc 0 t, φ (f (m + s • w)) = v := by
  have hfc : ContinuousAt f m := hf.continuousAt (hU.mem_nhds hmU)
  have hN : U ∩ f ⁻¹' ball p r ∈ 𝓝 m :=
    inter_mem (hU.mem_nhds hmU) (hfc.preimage_mem_nhds (hfm ▸ ball_mem_nhds (f m) hr))
  have hγ : Tendsto (fun s : ℝ ↦ m + s • w) (𝓝 0) (𝓝 m) := by
    have : Continuous fun s : ℝ ↦ m + s • w := by fun_prop
    simpa using this.tendsto 0
  obtain ⟨δ, hδ, hδN⟩ := Metric.mem_nhds_iff.1 (hγ hN)
  have hmem (s : ℝ) (hs : s ∈ Icc 0 (δ / 2)) : m + s • w ∈ U ∧ f (m + s • w) ∈ ball p r :=
    hδN (by rw [mem_ball, Real.dist_0_eq_abs, abs_of_nonneg hs.1]; linarith [hs.2])
  have hcont : ContinuousOn (fun s : ℝ ↦ φ (f (m + s • w))) (Icc 0 (δ / 2)) :=
    φ.continuous.comp_continuousOn (hf.comp (by fun_prop) fun s hs ↦ (hmem s hs).1)
  refine ⟨δ / 2, half_pos hδ, fun s hs ↦ (hmem s hs).1,
    hlt _ (half_pos hδ) (hmem _ ⟨(half_pos hδ).le, le_rfl⟩).1 (hmem _ ⟨(half_pos hδ).le, le_rfl⟩).2,
    fun v hv ↦ ?_⟩
  exact intermediate_value_Ioc (half_pos hδ).le hcont (by simpa only [zero_smul, add_zero, hfm])

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- **The one-dimensional case of Brown's Theorem 0.** Let `f` be continuous on an open set `U`
and injective on `U` away from the nonempty compact fibre `M = U ∩ f ⁻¹' {p}`, and let `φ` be an
injective linear form on `F`. Then the points of `U \ M` sent near `p` cannot all have `φ`-value
above `φ p`: the segments leaving `M` from its two extreme points along a linear form `ψ` on `E`
would reach the same `φ`-value at two distinct points. -/
private theorem false_of_forall_lt {U : Set E} (hU : IsOpen U) (hf : ContinuousOn f U)
    (hinj : InjOn f (U \ f ⁻¹' {p})) (hM : IsCompact (U ∩ f ⁻¹' {p}))
    (hne : (U ∩ f ⁻¹' {p}).Nonempty) {ψ : E →L[ℝ] ℝ} {v₀ : E} (hv₀ : ψ v₀ = 1)
    {φ : F →L[ℝ] ℝ} (hφ : Injective φ) {r : ℝ} (hr : 0 < r)
    (hlt : ∀ y ∈ U \ f ⁻¹' {p}, f y ∈ ball p r → φ p < φ (f y)) : False := by
  -- The two extreme points of `M` for `ψ`, and the segments leaving `M` from them.
  obtain ⟨m₁, hm₁, hmin⟩ := hM.exists_isMinOn hne ψ.continuous.continuousOn
  obtain ⟨m₂, hm₂, hmax⟩ := hM.exists_isMaxOn hne ψ.continuous.continuousOn
  have hψ₁ (s : ℝ) : ψ (m₁ + s • -v₀) = ψ m₁ - s := by simp [hv₀, sub_eq_add_neg]
  have hψ₂ (s : ℝ) : ψ (m₂ + s • v₀) = ψ m₂ + s := by simp [hv₀]
  obtain ⟨t₁, -, hU₁, hlt₁, hivt₁⟩ := exists_segment_Ioc_subset hU hf hm₁.1 hm₁.2 (-v₀)
    φ hr fun s hs hsU hsr ↦ hlt _ ⟨hsU, fun hsp ↦ by
      have := isMinOn_iff.1 hmin _ ⟨hsU, hsp⟩
      rw [hψ₁] at this
      linarith⟩ hsr
  obtain ⟨t₂, -, hU₂, hlt₂, hivt₂⟩ := exists_segment_Ioc_subset hU hf hm₂.1 hm₂.2 v₀
    φ hr fun s hs hsU hsr ↦ hlt _ ⟨hsU, fun hsp ↦ by
      have := isMaxOn_iff.1 hmax _ ⟨hsU, hsp⟩
      rw [hψ₂] at this
      linarith⟩ hsr
  -- Both segments reach the common value `v` at points `y₁ ≠ y₂` outside `M`.
  set v := min (φ (f (m₁ + t₁ • -v₀))) (φ (f (m₂ + t₂ • v₀)))
  obtain ⟨s₁, hs₁, hv₁⟩ := hivt₁ v ⟨lt_min hlt₁ hlt₂, min_le_left _ _⟩
  obtain ⟨s₂, hs₂, hv₂⟩ := hivt₂ v ⟨lt_min hlt₁ hlt₂, min_le_right _ _⟩
  have hne₁₂ : m₁ + s₁ • -v₀ ≠ m₂ + s₂ • v₀ := by
    intro h
    have h' := congrArg ψ h
    rw [hψ₁, hψ₂] at h'
    have := isMinOn_iff.1 hmin _ hm₂
    linarith [hs₁.1, hs₂.1]
  have hout (y : E) (hyU : y ∈ U) (hy : φ (f y) = v) : y ∈ U \ f ⁻¹' {p} :=
    ⟨hyU, fun hyp ↦
      (lt_min hlt₁ hlt₂).ne ((congrArg φ (mem_singleton_iff.1 hyp)).symm.trans hy)⟩
  exact hne₁₂ (hinj (hout _ (hU₁ s₁ (Ioc_subset_Icc_self hs₁)) hv₁)
    (hout _ (hU₂ s₂ (Ioc_subset_Icc_self hs₂)) hv₂) (hφ (hv₁.trans hv₂.symm)))

/-- **Brown's Theorem 0 in dimension one, near `p`.** In the setting of
`IsOpen.image_of_continuousOn_of_injOn_sdiff` with `dim E = dim F = 1` and a nonempty fibre
`M = U ∩ f ⁻¹' {p}`, suppose that every preconnected subset of the punctured ball
`ball p r \ {p}` meeting `S = f '' (U \ M)` lies in `S`. Then `S` fills the punctured ball: both
of its sides `{φ < φ p}` and `{φ > φ p}`, for a linear isomorphism `φ : F ≃ ℝ`, meet `S` by
`TauCeti.false_of_forall_lt`. -/
private theorem ball_sdiff_singleton_subset_of_finrank_eq_one (hEF : finrank ℝ E = finrank ℝ F)
    (h1 : finrank ℝ F = 1) {U : Set E} (hU : IsOpen U) (hf : ContinuousOn f U)
    (hinj : InjOn f (U \ f ⁻¹' {p})) (hM : IsCompact (U ∩ f ⁻¹' {p}))
    (hne : (U ∩ f ⁻¹' {p}).Nonempty) {r : ℝ} (hr : 0 < r)
    (hconn : ∀ T ⊆ ball p r \ {p}, IsPreconnected T →
      (T ∩ f '' (U \ f ⁻¹' {p})).Nonempty → T ⊆ f '' (U \ f ⁻¹' {p})) :
    ball p r \ {p} ⊆ f '' (U \ f ⁻¹' {p}) := by
  set S := f '' (U \ f ⁻¹' {p})
  have hpS : p ∉ S := fun ⟨z, hz, hzp⟩ ↦ hz.2 hzp
  let φ : F ≃L[ℝ] ℝ := ContinuousLinearEquiv.ofFinrankEq (by rw [finrank_self, h1])
  let ψ : E ≃L[ℝ] ℝ := ContinuousLinearEquiv.ofFinrankEq (by rw [finrank_self, hEF, h1])
  have hψ : (ψ : E →L[ℝ] ℝ) (ψ.symm 1) = 1 := ψ.apply_symm_apply 1
  -- The two sides of `p` in `ball p r`.
  set L := ball p r ∩ {y | φ y < φ p}
  set R := ball p r ∩ {y | φ p < φ y}
  have hLR : ball p r \ {p} ⊆ L ∪ R := fun y ⟨hy, hyp⟩ ↦
    (lt_or_gt_of_ne (φ.injective.ne hyp)).imp (fun h ↦ ⟨hy, h⟩) fun h ↦ ⟨hy, h⟩
  have hLsub : L ⊆ ball p r \ {p} := fun y hy ↦ ⟨hy.1, fun h ↦ (lt_irrefl (φ p)) (h ▸ hy.2)⟩
  have hRsub : R ⊆ ball p r \ {p} := fun y hy ↦ ⟨hy.1, fun h ↦ (lt_irrefl (φ p)) (h ▸ hy.2)⟩
  have hLc : IsPreconnected L := ((convex_ball p r).inter
    (convex_halfSpace_lt φ.toLinearEquiv.toLinearMap.isLinear (φ p))).isPreconnected
  have hRc : IsPreconnected R := ((convex_ball p r).inter
    (convex_halfSpace_gt φ.toLinearEquiv.toLinearMap.isLinear (φ p))).isPreconnected
  -- If one side misses `S`, the points of `U \ M` sent near `p` all lie on the other side.
  have hside (φ' : F →L[ℝ] ℝ) (hφ' : Injective φ')
      (h : ∀ y ∈ S, y ∈ ball p r → φ' y ≠ φ' p → φ' p < φ' y) : False :=
    false_of_forall_lt hU hf hinj hM hne hψ hφ' hr fun y hy hyr ↦
      h _ ⟨y, hy, rfl⟩ hyr (hφ'.ne fun h ↦ hpS (h ▸ ⟨y, hy, rfl⟩))
  by_cases hL : (L ∩ S).Nonempty
  · by_cases hR : (R ∩ S).Nonempty
    · exact hLR.trans (union_subset (hconn L hLsub hLc hL) (hconn R hRsub hRc hR))
    refine (hside (-(φ : F →L[ℝ] ℝ)) (fun a b hab ↦ φ.injective (neg_injective hab))
      fun y hyS hyr hne ↦ ?_).elim
    rw [neg_apply, neg_apply, ne_eq, neg_inj] at hne
    rw [neg_apply, neg_apply, neg_lt_neg_iff]
    exact (lt_or_gt_of_ne hne).resolve_right fun h ↦ hR ⟨y, ⟨hyr, h⟩, hyS⟩
  refine (hside φ φ.injective fun y hyS hyr hne ↦ ?_).elim
  exact (lt_or_gt_of_ne hne).resolve_left fun h ↦ hL ⟨y, ⟨hyr, h⟩, hyS⟩

end TauCeti

open TauCeti in
/-- **Brown's Theorem 0, for one inverse set.** Let `E` and `F` be finite-dimensional real normed
spaces of the same dimension, and let `f : E → F` be continuous on an open set `U` and injective
on `U` away from the fibre `U ∩ f ⁻¹' {p}`. If this fibre is compact, then `f` maps `U` onto an
open set. For an empty fibre this is invariance of domain,
`IsOpen.image_of_continuousOn_of_injOn`. -/
theorem IsOpen.image_of_continuousOn_of_injOn_sdiff {U : Set E} (hU : IsOpen U)
    (hf : ContinuousOn f U) (hinj : InjOn f (U \ f ⁻¹' {p})) (hM : IsCompact (U ∩ f ⁻¹' {p}))
    (hEF : finrank ℝ E = finrank ℝ F) : IsOpen (f '' U) := by
  -- Away from `p`, this is invariance of domain on `V \ f ⁻¹' {p}` for open `V ⊆ U`.
  have hVo {V : Set E} (hV : IsOpen V) (hVU : V ⊆ U) : IsOpen (f '' (V \ f ⁻¹' {p})) := by
    have hV' : IsOpen (V \ f ⁻¹' {p}) :=
      (hf.mono hVU).isOpen_inter_preimage hV isOpen_compl_singleton
    exact hV'.image_of_continuousOn_of_injOn (hf.mono (sdiff_subset.trans hVU))
      (hinj.mono (sdiff_subset_sdiff_left hVU)) hEF
  refine isOpen_iff_mem_nhds.2 ?_
  rintro _ ⟨x, hxU, rfl⟩
  by_cases hxp : f x = p
  swap
  · exact mem_of_superset ((hVo hU subset_rfl).mem_nhds ⟨x, ⟨hxU, hxp⟩, rfl⟩)
      (image_mono sdiff_subset)
  rw [hxp]
  rcases Nat.lt_or_ge (finrank ℝ F) 1 with h0 | h1
  · -- In dimension zero every subset of `F` is open.
    have : Subsingleton F := finrank_zero_iff (R := ℝ).1 (by omega)
    exact univ_mem' fun y ↦ ⟨x, hxU, Subsingleton.elim _ _⟩
  have : Nontrivial E := finrank_pos_iff (R := ℝ).1 (by omega)
  set M := U ∩ f ⁻¹' {p}
  have hne : M.Nonempty := ⟨x, hxU, hxp⟩
  -- A compact neighbourhood `K ⊆ U` of `M`, with interior `V`.
  obtain ⟨K, hK, hMK, hKU⟩ := exists_compact_between hM hU inter_subset_left
  set V := interior K
  have hVU : V ⊆ U := interior_subset.trans hKU
  have hVM : V ∩ f ⁻¹' {p} = M :=
    Subset.antisymm (fun z hz ↦ ⟨hVU hz.1, hz.2⟩) (subset_inter hMK inter_subset_right)
  set S := f '' (V \ f ⁻¹' {p})
  have hS : IsOpen S := hVo isOpen_interior hVU
  have hpS : p ∉ S := fun ⟨z, hz, hzp⟩ ↦ hz.2 hzp
  -- A ball around `p` misses the image of `K \ V`.
  have hKV : IsCompact (f '' (K \ V)) :=
    (hK.diff isOpen_interior).image_of_continuousOn (hf.mono (sdiff_subset.trans hKU))
  obtain ⟨r, hr, hrK⟩ := Metric.isOpen_iff.1 hKV.isClosed.isOpen_compl p fun ⟨z, hz, hzp⟩ ↦
    hz.2 (hMK ⟨hKU hz.1, hzp⟩)
  -- Within that ball, `S` is relatively closed in the punctured ball.
  have hSball (y : F) (hy : y ∈ ball p r) (hyc : y ∈ closure S) (hyp : y ≠ p) : y ∈ S := by
    obtain ⟨z, hz, rfl⟩ := closure_minimal (image_mono (sdiff_subset.trans interior_subset))
      (hK.image_of_continuousOn (hf.mono hKU)).isClosed hyc
    have hzV : z ∈ V := by
      by_contra hzV
      exact hrK hy ⟨z, ⟨hz, hzV⟩, rfl⟩
    exact ⟨z, ⟨hzV, hyp⟩, rfl⟩
  have hconn (T : Set F) (hT : T ⊆ ball p r \ {p}) (hTc : IsPreconnected T)
      (hTS : (T ∩ S).Nonempty) : T ⊆ S :=
    hTc.subset_of_closure_inter_subset hS hTS fun y hy ↦
      hSball y (hT hy.2).1 hy.1 (hT hy.2).2
  -- `S` accumulates at `p`: the nonempty compact set `M` is not all of `E`, so it has a frontier
  -- point, which is a limit of points of `V \ M`.
  have hpcl : p ∈ closure S := by
    obtain ⟨m, hm⟩ := nonempty_frontier_iff.2 ⟨hne, fun h ↦ noncompact_univ E (h ▸ hM)⟩
    rw [frontier_eq_closure_inter_closure, hM.isClosed.closure_eq] at hm
    have hmV : m ∈ closure (V \ f ⁻¹' {p}) :=
      closure_mono (t := V \ f ⁻¹' {p})
        (fun z (hz : z ∈ V ∩ Mᶜ) ↦ ⟨hz.1, fun hzp ↦ hz.2 ⟨hVU hz.1, hzp⟩⟩)
        (isOpen_interior.inter_closure ⟨hMK hm.1, hm.2⟩)
    have := (hf.continuousAt (hU.mem_nhds hm.1.1)).continuousWithinAt.mem_closure_image hmV
    rwa [mem_singleton_iff.1 hm.1.2] at this
  suffices hsub : ball p r \ {p} ⊆ S by
    refine mem_of_superset (ball_mem_nhds p hr) fun y hy ↦ ?_
    rcases eq_or_ne y p with rfl | hyp
    · exact ⟨x, hxU, hxp⟩
    · obtain ⟨z, hz, rfl⟩ := hsub ⟨hy, hyp⟩
      exact ⟨z, hVU hz.1, rfl⟩
  rcases h1.eq_or_lt with h1 | h2
  · exact ball_sdiff_singleton_subset_of_finrank_eq_one hEF h1.symm isOpen_interior
      (hf.mono hVU) (hinj.mono (sdiff_subset_sdiff_left hVU)) (by rwa [hVM]) (by rwa [hVM]) hr
      hconn
  · -- In dimension at least two, the punctured ball is connected.
    refine hconn _ subset_rfl (isConnected_ball_sdiff_singleton ?_ p hr).isPreconnected ?_
    · rw [← finrank_eq_rank]
      exact_mod_cast h2
    obtain ⟨y, hyS, hy⟩ := Metric.mem_closure_iff.1 hpcl r hr
    exact ⟨y, ⟨by rwa [mem_ball, dist_comm], fun h ↦ hpS (h ▸ hyS)⟩, hyS⟩

end InverseSet
