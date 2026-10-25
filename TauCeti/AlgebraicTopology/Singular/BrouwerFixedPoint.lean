/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Sphere
public import TauCeti.Analysis.InnerProductSpace.SphereRay
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# The no-retraction theorem and Brouwer's fixed-point theorem for the disk

The boundary sphere `∂Dⁿ = TopCat.diskBoundary n` is not a retract of the disk
`Dⁿ = TopCat.disk n` (`TauCeti.noRetraction_diskBoundary`), and consequently every continuous
self-map of `Dⁿ` has a fixed point (`TauCeti.brouwerFixedPoint_topCatDisk`).

For `n = 0` the boundary is empty while the disk is a point, so there is no map at all from the
disk to its boundary. For `n = m + 1`, apply reduced singular homology in degree `m` with integer
coefficients to maps `i : Sᵐ ⟶ Dᵐ⁺¹` and `r : Dᵐ⁺¹ ⟶ Sᵐ` with `i ≫ r = 𝟙`: the identity of
`H~ₘ(Sᵐ; ℤ) ≅ ℤ` (`TauCeti.reducedSingularHomologyTopCatSphereIso`) would factor as `i_*`
followed by `r_*` through `H~ₘ(Dᵐ⁺¹; ℤ)`, which vanishes as the disk is contractible
(`TauCeti.isZero_reducedSingularHomologyFunctor_of_contractibleSpace`).

A self-map `f` of the disk without fixed points gives a retraction of the boundary inclusion,
sending `x` to the point where the ray from `f x` through `x` meets the boundary sphere
(`ContinuousMap.closedBallRayRetraction`), so no such `f` exists.

## Main results

* `TauCeti.noRetraction_diskBoundary`: `∂Dⁿ` is not a retract of `Dⁿ`; in particular the boundary
  inclusion `∂Dⁿ ⟶ Dⁿ` has no retraction.
* `TauCeti.brouwerFixedPoint_topCatDisk`: **Brouwer's fixed-point theorem** for `Dⁿ`.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, Corollary 2.15.
-/

public section

open CategoryTheory Limits Metric

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

end TauCeti
