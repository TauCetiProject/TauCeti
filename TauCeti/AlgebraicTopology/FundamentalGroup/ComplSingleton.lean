/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.LinearAlgebra.Dimension.Basic
public import TauCeti.AlgebraicTopology.FundamentalGroup.VanKampen.Basic
import TauCeti.AlgebraicTopology.FundamentalGroup.BasepointChange
import TauCeti.AlgebraicTopology.FundamentalGroup.PuncturedStarConvex
import TauCeti.Analysis.Convex.SimplyConnected
import TauCeti.Analysis.Normed.Module.Connected
import TauCeti.Geometry.Manifold.Connected

/-!
# Deleting a point from a manifold of dimension at least three

Let `X` be a connected topological manifold modelled on a real normed space `E` of dimension
greater than two, and let `p ∈ X`. The inclusion `X \ {p} → X` induces an isomorphism of
fundamental groups at every basepoint of `X \ {p}`. In particular `X \ {p}` is simply connected if
and only if `X` is. The direction needed to recognise a sphere, that `X` is simply connected when
`X \ {p}` is (for instance when `X \ {p}` is homeomorphic to `ℝⁿ`), holds already in dimension
`n ≥ 2`, since it only uses that a punctured ball is path connected.

The proof is the Seifert--van Kampen theorem for the cover of `X` by `X \ {p}` and a coordinate
ball `B` about `p`. The ball is simply connected, and so is the overlap `B \ {p}`, a punctured
ball, because the sphere `Sⁿ⁻¹` is simply connected for `n ≥ 3`. The free product
`π₁(X \ {p}) ∗ π₁(B)` therefore maps isomorphically onto `π₁(X)` with trivial second factor.
The abstract form of this argument only needs a neighbourhood `B` of a closed point `p` with
`B` and `B \ {p}` simply connected, and a path-connected complement of `p`
(`TauCeti.fundamentalGroup_map_subtypeVal_compl_singleton_bijective_of_mem_nhds`).

In dimension two the statement fails, because a punctured disc is not simply connected: the
torus minus a point has a free fundamental group of rank two, which maps onto `ℤ²` with nontrivial
kernel.

## Main declarations

* `TauCeti.fundamentalGroup_map_subtypeVal_compl_singleton_bijective_of_mem_nhds`: deleting a
  closed point `p` with a simply connected neighbourhood `B` such that `B \ {p}` is simply
  connected, from a space whose complement of `p` is path connected, induces a bijection of
  fundamental groups.
* `OpenPartialHomeomorph.isSimplyConnected_symm_image`: a chart carries simply connected subsets
  of its target to simply connected sets.
* `OpenPartialHomeomorph.exists_mem_nhds_isSimplyConnected_sdiff_singleton`: in dimension greater
  than two, every point in the source of a chart has such a neighbourhood, the preimage of a ball.
  In dimension greater than one the punctured neighbourhood is still path connected
  (`OpenPartialHomeomorph.exists_mem_nhds_isSimplyConnected_isPathConnected_sdiff_singleton`).
* `TauCeti.fundamentalGroup_map_subtypeVal_compl_singleton_bijective`: **deleting a point from a
  connected manifold of dimension at least three induces an isomorphism of fundamental groups.**
* `TauCeti.simplyConnectedSpace_of_isSimplyConnected_compl_singleton`: a manifold of dimension at
  least two whose complement of a point is simply connected is simply connected.
* `TauCeti.simplyConnectedSpace_compl_singleton_iff`: in dimension at least three, a manifold is
  simply connected if and only if the complement of any of its points is.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), §1.2: the van Kampen
  theorem 1.20 and Proposition 1.26 (attaching cells of dimension greater than two does not change
  the fundamental group).
-/

public section

open Metric Set Topology

namespace TauCeti

variable {X : Type*} [TopologicalSpace X]

/-- The complement of a closed point `p` and a neighbourhood of `p` have interiors covering the
space. -/
private theorem interior_compl_singleton_union_interior_eq_univ {p : X}
    (hp : IsClosed ({p} : Set X)) {B : Set X} (hB : B ∈ 𝓝 p) :
    interior {p}ᶜ ∪ interior B = univ := by
  refine eq_univ_of_forall fun y ↦ ?_
  rw [hp.isOpen_compl.interior_eq]
  by_cases hy : y = p
  · exact Or.inr (hy ▸ mem_interior_iff_mem_nhds.2 hB)
  · exact Or.inl hy

/-- **Deleting a point with a simply connected punctured neighbourhood.** Let `p` be a closed
point of `X` whose complement is path connected, and let `B` be a neighbourhood of `p` such that
both `B` and `B \ {p}` are simply connected. Then the inclusion `X \ {p} → X` induces a bijection
of fundamental groups at every point of `X \ {p}`. -/
theorem fundamentalGroup_map_subtypeVal_compl_singleton_bijective_of_mem_nhds {p : X}
    (hp : IsClosed ({p} : Set X)) (hX : IsPathConnected ({p}ᶜ : Set X)) {B : Set X}
    (hB : B ∈ 𝓝 p) (hBsc : IsSimplyConnected B) (hBp : IsSimplyConnected (B \ {p}))
    (x : ({p}ᶜ : Set X)) :
    Function.Bijective (FundamentalGroup.map (ContinuousMap.subtypeVal ({p}ᶜ : Set X)) x) := by
  obtain ⟨z, hzB, hzp⟩ := hBp.nonempty
  have hAB : IsSimplyConnected ({p}ᶜ ∩ B) := by rwa [inter_comm, ← sdiff_eq]
  have : SimplyConnectedSpace B := hBsc.simplyConnectedSpace
  -- The van Kampen map `π₁(X \ {p}, z) ∗ π₁(B, z) → π₁(X, z)` is bijective and its second factor
  -- is trivial, so its restriction to the first factor, the inclusion-induced map, is bijective.
  have hinl : Function.Bijective (Monoid.Coprod.inl : FundamentalGroup ({p}ᶜ : Set X) ⟨z, hzp⟩ →*
      Monoid.Coprod _ (FundamentalGroup B ⟨z, hzB⟩)) :=
    (MonoidHom.toMulEquiv Monoid.Coprod.fst Monoid.Coprod.inl
      (Monoid.Coprod.hom_ext rfl (MonoidHom.ext fun g ↦ by simp [Subsingleton.elim g 1]))
      Monoid.Coprod.fst_comp_inl).symm.bijective
  have hz : Function.Bijective
      (FundamentalGroup.map (ContinuousMap.subtypeVal ({p}ᶜ : Set X)) ⟨z, hzp⟩) := by
    have heq : ⇑(FundamentalGroup.map (ContinuousMap.subtypeVal ({p}ᶜ : Set X)) ⟨z, hzp⟩) =
        vanKampenLift {p}ᶜ B z hzp hzB ∘ Monoid.Coprod.inl :=
      funext fun g ↦ (vanKampenLift_apply_inl {p}ᶜ B z hzp hzB).symm
    rw [heq]
    exact (vanKampenLift_bijective (interior_compl_singleton_union_interior_eq_univ hp hB) hX
      hBsc.isPathConnected hAB hzp hzB).comp hinl
  have : PathConnectedSpace ({p}ᶜ : Set X) := isPathConnected_iff_pathConnectedSpace.1 hX
  exact FundamentalGroup.map_bijective_of_path _ (PathConnectedSpace.somePath _ x) hz

end TauCeti

section Chart

/-- The image under `φ.symm` of a simply connected subset of the target of `φ` is simply
connected. -/
theorem OpenPartialHomeomorph.isSimplyConnected_symm_image {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (φ : OpenPartialHomeomorph X Y) {S : Set Y} (hS : S ⊆ φ.target)
    (hSc : IsSimplyConnected S) : IsSimplyConnected (φ.symm '' S) :=
  have := hSc.simplyConnectedSpace
  (φ.symm.homeomorphOfImageSubsetSource hS rfl).symm.toHomotopyEquiv.simplyConnectedSpace

variable {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A point `p` in the source of `φ` has a simply connected neighbourhood `φ.symm '' ball (φ p) r`,
whose complement of `p` is the image of the punctured ball. -/
private theorem OpenPartialHomeomorph.exists_ball_subset_target (φ : OpenPartialHomeomorph X E)
    {p : X} (hp : p ∈ φ.source) :
    ∃ r > 0, ball (φ p) r ⊆ φ.target ∧ φ.symm '' ball (φ p) r ∈ 𝓝 p ∧
      IsSimplyConnected (φ.symm '' ball (φ p) r) ∧
      φ.symm '' ball (φ p) r \ {p} = φ.symm '' (ball (φ p) r \ {φ p}) := by
  obtain ⟨r, hr, hbt⟩ := Metric.isOpen_iff.1 φ.open_target (φ p) (φ.map_source hp)
  refine ⟨r, hr, hbt, ?_,
    φ.isSimplyConnected_symm_image hbt ((convex_ball _ r).isSimplyConnected ⟨_, mem_ball_self hr⟩),
    ?_⟩
  · simpa [φ.left_inv hp] using φ.symm.image_mem_nhds (φ.map_source hp) (ball_mem_nhds _ hr)
  · rw [(φ.symm.injOn.mono hbt).image_sdiff_subset (singleton_subset_iff.2 (mem_ball_self hr)),
      image_singleton, φ.left_inv hp]

/-- If `E` is a real normed space of dimension greater than one, every point `p` in the source of
a partial homeomorphism `φ : X → E` has a simply connected neighbourhood `B` with `B \ {p}` path
connected: the preimage of a small open ball about `φ p`. -/
theorem OpenPartialHomeomorph.exists_mem_nhds_isSimplyConnected_isPathConnected_sdiff_singleton
    (h : 1 < Module.rank ℝ E) (φ : OpenPartialHomeomorph X E) {p : X} (hp : p ∈ φ.source) :
    ∃ B ∈ 𝓝 p, IsSimplyConnected B ∧ IsPathConnected (B \ {p}) := by
  obtain ⟨r, hr, hbt, hB, hBsc, hsdiff⟩ := φ.exists_ball_subset_target hp
  refine ⟨_, hB, hBsc, ?_⟩
  rw [hsdiff]
  exact (TauCeti.isPathConnected_ball_sdiff_singleton h _ hr).image'
    (φ.continuousOn_symm.mono (sdiff_subset.trans hbt))

/-- If `E` is a real normed space of dimension greater than two, every point `p` in the source of
a partial homeomorphism `φ : X → E` has a neighbourhood `B` such that `B` and `B \ {p}` are simply
connected: the preimage of a small open ball about `φ p`. -/
theorem OpenPartialHomeomorph.exists_mem_nhds_isSimplyConnected_sdiff_singleton
    (h : 2 < Module.rank ℝ E) (φ : OpenPartialHomeomorph X E) {p : X} (hp : p ∈ φ.source) :
    ∃ B ∈ 𝓝 p, IsSimplyConnected B ∧ IsSimplyConnected (B \ {p}) := by
  obtain ⟨r, hr, hbt, hB, hBsc, hsdiff⟩ := φ.exists_ball_subset_target hp
  refine ⟨_, hB, hBsc, ?_⟩
  rw [hsdiff]
  exact φ.isSimplyConnected_symm_image (sdiff_subset.trans hbt)
    (TauCeti.isSimplyConnected_ball_sdiff_singleton h _ hr)

end Chart

namespace TauCeti

variable {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ChartedSpace E X]

/-- **Deleting a point from a manifold of dimension at least three does not change its
fundamental group.** If `X` is a connected manifold modelled on a real normed space of dimension
greater than two, the inclusion `X \ {p} → X` induces an isomorphism of fundamental groups at
every point of `X \ {p}`. -/
theorem fundamentalGroup_map_subtypeVal_compl_singleton_bijective [ConnectedSpace X]
    (h : 2 < Module.rank ℝ E) (p : X) (x : ({p}ᶜ : Set X)) :
    Function.Bijective (FundamentalGroup.map (ContinuousMap.subtypeVal ({p}ᶜ : Set X)) x) := by
  have := ChartedSpace.t1Space E X
  obtain ⟨B, hB, hBsc, hBp⟩ :=
    (chartAt E p).exists_mem_nhds_isSimplyConnected_sdiff_singleton h (mem_chart_source E p)
  exact fundamentalGroup_map_subtypeVal_compl_singleton_bijective_of_mem_nhds isClosed_singleton
    (isPathConnected_compl_of_finite_of_one_lt_rank (Cardinal.one_lt_two.trans h)
      (finite_singleton p)) hB hBsc hBp x

/-- **A manifold of dimension at least two is simply connected if the complement of a point is.**
If `X` is modelled on a real normed space of dimension greater than one and `X \ {p}` is simply
connected, then so is `X`. In particular this holds when `X \ {p}` is homeomorphic to `ℝⁿ`,
`n ≥ 2`. -/
theorem simplyConnectedSpace_of_isSimplyConnected_compl_singleton (h : 1 < Module.rank ℝ E)
    {p : X} (hp : IsSimplyConnected ({p}ᶜ : Set X)) : SimplyConnectedSpace X := by
  -- `X` is the union of the simply connected sets `X \ {p}` and `B`, which meet in `B \ {p}`.
  have := ChartedSpace.t1Space E X
  obtain ⟨B, hB, hBsc, hBp⟩ :=
    OpenPartialHomeomorph.exists_mem_nhds_isSimplyConnected_isPathConnected_sdiff_singleton h
      (chartAt E p) (mem_chart_source E p)
  have := hp.simplyConnectedSpace
  have := hBsc.simplyConnectedSpace
  refine simplyConnectedSpace_of_interior_union
    (interior_compl_singleton_union_interior_eq_univ isClosed_singleton hB) ?_
  rwa [inter_comm, ← sdiff_eq]

/-- **A manifold of dimension at least three is simply connected if and only if the complement of
a point is.** -/
theorem simplyConnectedSpace_compl_singleton_iff (h : 2 < Module.rank ℝ E) (p : X) :
    SimplyConnectedSpace ({p}ᶜ : Set X) ↔ SimplyConnectedSpace X := by
  refine ⟨fun hA ↦ simplyConnectedSpace_of_isSimplyConnected_compl_singleton
    (Cardinal.one_lt_two.trans h) hA, fun hX ↦ ?_⟩
  -- Every loop in `X \ {p}` is null-homotopic in `X`, hence in `X \ {p}` by injectivity.
  have : PathConnectedSpace ({p}ᶜ : Set X) := isPathConnected_iff_pathConnectedSpace.1 <|
    isPathConnected_compl_of_finite_of_one_lt_rank (Cardinal.one_lt_two.trans h)
      (finite_singleton p)
  refine simply_connected_iff_loops_nullhomotopic.2 ⟨this, fun x γ ↦ ?_⟩
  have hinj := (fundamentalGroup_map_subtypeVal_compl_singleton_bijective h p x).1
  exact Quotient.eq.mp (congrArg CategoryTheory.End.asHom (hinj (Subsingleton.elim
    (FundamentalGroup.map _ x (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)))
    (FundamentalGroup.map _ x
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (Path.refl x)))))))

end TauCeti
