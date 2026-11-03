/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Sphere
public import TauCeti.Analysis.Convex.Intrinsic
public import TauCeti.Analysis.InnerProductSpace.Sphere.Ray
import TauCeti.Topology.Homeomorph.FixedPoint

/-!
# The no-retraction theorem and Brouwer's fixed-point theorem

The boundary sphere `∂Dⁿ = TopCat.diskBoundary n` is not a retract of the disk
`Dⁿ = TopCat.disk n` (`TauCeti.noRetraction_diskBoundary`), and consequently every continuous
self-map of `Dⁿ` has a fixed point (`TauCeti.brouwerFixedPoint_topCatDisk`). The theorem then
passes to every nonempty compact convex subset of a finite-dimensional real normed space
(`TauCeti.brouwerFixedPoint_compactConvex`), with no assumption that the set has nonempty
interior.

For `n = 0` the boundary is empty while the disk is a point, so there is no map at all from the
disk to its boundary. For `n = m + 1`, apply reduced singular homology in degree `m` with integer
coefficients to maps `i : Sᵐ ⟶ Dᵐ⁺¹` and `r : Dᵐ⁺¹ ⟶ Sᵐ` with `i ≫ r = 𝟙`: the identity of
`H~ₘ(Sᵐ; ℤ) ≅ ℤ` (`TauCeti.reducedSingularHomologyTopCatSphereIso`) would factor as `i_*`
followed by `r_*` through `H~ₘ(Dᵐ⁺¹; ℤ)`, which vanishes as the disk is contractible
(`TauCeti.isZero_reducedSingularHomologyFunctor_of_contractibleSpace`).

A self-map `f` of the disk without fixed points gives a retraction of the boundary inclusion,
sending `x` to the point where the ray from `f x` through `x` meets the boundary sphere
(`ContinuousMap.closedBallRayRetraction`), so no such `f` exists.

A nonempty compact convex set `C` has a point `c` of its intrinsic interior, and is then
homeomorphic to the closed unit ball of the direction `V` of its affine span
(`TauCeti.convexClosedBallHomeomorph`). Since `V` is finite-dimensional, its closed unit ball is
homeomorphic to the disk of dimension `finrank ℝ V` (`TauCeti.closedBallHomeomorphOfFinrankEq`),
and the fixed-point property is invariant under homeomorphisms
(`Homeomorph.forall_exists_isFixedPt_iff`).

## Main results

* `TauCeti.noRetraction_diskBoundary`: `∂Dⁿ` is not a retract of `Dⁿ`; in particular the boundary
  inclusion `∂Dⁿ ⟶ Dⁿ` has no retraction.
* `TauCeti.brouwerFixedPoint_topCatDisk`: **Brouwer's fixed-point theorem** for `Dⁿ`.
* `TauCeti.brouwerFixedPoint_compactConvex`: Brouwer's fixed-point theorem for a nonempty compact
  convex subset of a finite-dimensional real normed space, and
  `TauCeti.brouwerFixedPoint_compactConvex_continuousOn` for a function of the ambient space that
  is continuous on the set and maps it into itself.
* `TauCeti.brouwerFixedPoint_compactConvex_finiteSpan`: the same for a compact convex set lying in
  a finite-dimensional subspace of an arbitrary real normed space.
* `TauCeti.brouwerFixedPoint_closedBall`: closed balls of nonnegative radius.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, Corollary 2.15.
-/

public section

open CategoryTheory Limits Metric Set Function

universe w

namespace TauCeti

/-- **The no-retraction theorem**: the boundary sphere `∂Dⁿ` of the disk is not a retract of
the disk `Dⁿ`. That is, there are no maps `i : ∂Dⁿ ⟶ Dⁿ` and `r : Dⁿ ⟶ ∂Dⁿ` with `i ≫ r = 𝟙`;
in particular the boundary inclusion `TopCat.diskBoundaryInclusion n` has no retraction. This
includes `n = 0`, where the boundary is empty. -/
theorem noRetraction_diskBoundary (n : ℕ) :
    IsEmpty (Retract (TopCat.diskBoundary.{w} n) (TopCat.disk.{w} n)) := by
  refine ⟨fun ρ ↦ ?_⟩
  cases n with
  | zero => exact isEmptyElim (ρ.r (diskCenter 0))
  | succ m =>
    let R := ModuleCat.of ℤ (ULift.{w} ℤ)
    let F := reducedSingularHomologyFunctor R m
    have hD : IsZero (F.obj (TopCat.disk.{w} (m + 1))) :=
      isZero_reducedSingularHomologyFunctor_of_contractibleSpace R _ m
    -- The identity of `H~ₘ(Sᵐ)` factors through `H~ₘ(Dᵐ⁺¹) = 0`.
    have hS : IsZero (F.obj (TopCat.diskBoundary.{w} (m + 1))) := by
      rw [IsZero.iff_id_eq_zero, ← F.map_id, ← ρ.retract, F.map_comp,
        hD.eq_of_src (F.map ρ.r) 0, comp_zero]
    have : Subsingleton (ULift.{w} ℤ) := ModuleCat.isZero_iff_subsingleton.mp
      (hS.of_iso (reducedSingularHomologyTopCatSphereIso R m).symm)
    exact zero_ne_one (Subsingleton.elim (0 : ULift.{w} ℤ) 1)

/-- **Brouwer's fixed-point theorem**: every continuous self-map of the disk `Dⁿ` has a fixed
point. -/
theorem brouwerFixedPoint_topCatDisk (n : ℕ) (f : TopCat.disk.{w} n ⟶ TopCat.disk.{w} n) :
    ∃ x, Function.IsFixedPt f x := by
  by_contra! hf
  -- Transport `f` to the closed unit ball of `EuclideanSpace ℝ (Fin n)`, the carrier of `Dⁿ`.
  let e : TopCat.disk.{w} n ≃ₜ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := Homeomorph.ulift
  let eS : TopCat.diskBoundary.{w} n ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    Homeomorph.ulift
  let g : C(closedBall (0 : EuclideanSpace ℝ (Fin n)) 1,
      closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    ContinuousMap.comp ⟨e, e.continuous⟩ (f.hom.comp ⟨e.symm, e.symm.continuous⟩)
  have hg (x) : g x ≠ x := fun h ↦ hf (e.symm x) (e.injective (by simpa [g] using h))
  let r : C(TopCat.disk.{w} n, TopCat.diskBoundary.{w} n) :=
    (eS.symm : C(sphere (0 : EuclideanSpace ℝ (Fin n)) 1, TopCat.diskBoundary.{w} n)).comp
      ((g.closedBallRayRetraction hg).comp e)
  refine (noRetraction_diskBoundary n).false
    ⟨TopCat.diskBoundaryInclusion n, TopCat.ofHom r, ?_⟩
  ext s
  -- `TopCat.ofHom r` is typed through the `ULift` carriers of `Dⁿ` and `∂Dⁿ`, so the composite
  -- cannot be rewritten by `CategoryTheory.comp_apply`; by definition it is `r` after the
  -- inclusion.
  change eS.symm (g.closedBallRayRetraction hg (e (TopCat.diskBoundaryInclusion n s))) = s
  rw [eS.symm_apply_eq]
  -- The boundary inclusion keeps the underlying point of the sphere.
  have hs : (e (TopCat.diskBoundaryInclusion n s) : EuclideanSpace ℝ (Fin n)) = eS s := (rfl)
  exact Subtype.ext ((g.closedBallRayRetraction_apply_of_mem_sphere hg (hs ▸ (eS s).2)).trans hs)

section CompactConvex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {C : Set E}

/-- **Brouwer's fixed-point theorem for compact convex sets**: every continuous self-map of a
nonempty compact convex subset of a finite-dimensional real normed space has a fixed point. The
set may have empty interior. -/
theorem brouwerFixedPoint_compactConvex (hC : IsCompact C) (hconv : Convex ℝ C)
    (hne : C.Nonempty) (f : C(C, C)) : ∃ x, IsFixedPt f x := by
  obtain ⟨c, hc⟩ := hne.intrinsicInterior hconv
  let V := (affineSpan ℝ C).direction
  -- `C` is a closed ball of `V` around `c`, and that ball is the disk of dimension `finrank ℝ V`.
  let e : TopCat.disk.{0} (Module.finrank ℝ V) ≃ₜ C :=
    (Homeomorph.ulift.trans (closedBallHomeomorphOfFinrankEq (F := V) (by simp))).trans
      (convexClosedBallHomeomorph hconv hC.isClosed hC.isBounded hc)
  -- The morphism `TopCat.ofHom g` of `TopCat` has underlying map `g` by definition.
  exact e.forall_exists_isFixedPt_iff.1
    (fun g ↦ brouwerFixedPoint_topCatDisk _ (TopCat.ofHom g)) f

/-- **Brouwer's fixed-point theorem for compact convex sets**, for a function on the ambient
space: a function continuous on a nonempty compact convex subset `C` of a finite-dimensional real
normed space and mapping `C` into itself has a fixed point in `C`. -/
theorem brouwerFixedPoint_compactConvex_continuousOn (hC : IsCompact C) (hconv : Convex ℝ C)
    (hne : C.Nonempty) {f : E → E} (hf : ContinuousOn f C) (hfC : MapsTo f C C) :
    ∃ x ∈ C, IsFixedPt f x := by
  obtain ⟨x, hx⟩ := brouwerFixedPoint_compactConvex hC hconv hne
    ⟨hfC.restrict f C C, hf.mapsToRestrict hfC⟩
  exact ⟨x, x.2, congrArg Subtype.val hx⟩

/-- **Brouwer's fixed-point theorem for closed balls**: every continuous self-map of a closed
ball of nonnegative radius in a finite-dimensional real normed space has a fixed point. -/
theorem brouwerFixedPoint_closedBall (x : E) {r : ℝ} (hr : 0 ≤ r)
    (f : C(closedBall x r, closedBall x r)) : ∃ y, IsFixedPt f y :=
  brouwerFixedPoint_compactConvex (isCompact_closedBall x r) (convex_closedBall x r)
    (nonempty_closedBall.2 hr) f

end CompactConvex

/-- **Brouwer's fixed-point theorem for compact convex sets in a finite-dimensional subspace**:
every continuous self-map of a nonempty compact convex set `C` lying in a finite-dimensional
subspace `V` of an arbitrary real normed space has a fixed point. -/
theorem brouwerFixedPoint_compactConvex_finiteSpan {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (V : Submodule ℝ E) [FiniteDimensional ℝ V] {C : Set E} (hCV : C ⊆ V)
    (hC : IsCompact C) (hconv : Convex ℝ C) (hne : C.Nonempty) (f : C(C, C)) :
    ∃ x, IsFixedPt f x := by
  -- Read `C` inside `V`, where the finite-dimensional theorem applies.
  have hCV' : C ⊆ range V.subtype := by simpa using hCV
  let e : (V.subtype ⁻¹' C : Set V) ≃ₜ C :=
    Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange hCV'
  obtain ⟨x, hx⟩ := hne
  exact e.forall_exists_isFixedPt_iff.1 (brouwerFixedPoint_compactConvex
    ((Topology.IsInducing.subtypeVal.isCompact_preimage_iff hCV').2 hC)
    (hconv.linear_preimage V.subtype) ⟨⟨x, hCV hx⟩, hx⟩) f

end TauCeti
