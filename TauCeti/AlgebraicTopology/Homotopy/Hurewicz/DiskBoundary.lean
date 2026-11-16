/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Sphere
public import TauCeti.AlgebraicTopology.Singular.Sphere
import TauCeti.Algebra.Group.ZMultiples

/-!
# Hurewicz classes as images of the sphere generator

A generalized loop `p : (Iⁿ⁺¹, ∂Iⁿ⁺¹) → (X, x)` is also a pointed map `Sⁿ⁺¹ → X`, the attaching
map `GenLoop.diskBoundaryMap p` of the cell that kills its class. With integer coefficients, the
image under this map of the standard generator `[Sⁿ⁺¹]` of the homology of the sphere
`TopCat.diskBoundary (n + 2)` (`TauCeti.reducedSingularHomologyTopCatSphereIso`) is the Hurewicz
class of `p`, up to a sign that depends neither on the space nor on the loop
(`TauCeti.exists_singularHomologyMap_diskBoundaryMap_eq_units_smul_hurewicz`).

Both classes are natural in based maps, and every generalized loop factors through the
tautological loop of the sphere (`GenLoop.hurewicz_eq_hurewicz_sphereGenLoop_comp`), so it
suffices to compare them on the sphere. There both generate the infinite cyclic group
`Hₙ₊₁(Sⁿ⁺¹; ℤ)` (`TauCeti.isIso_hurewicz_sphereGenLoop`), so they differ by a unit.

This identifies the homology classes killed by attaching cells along generalized loops, as
computed by `TauCeti.ker_singularHomologyMap_cellAttachmentIncl`, with Hurewicz classes.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.2, the Hurewicz map.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology TauCeti
open scoped Topology.Homotopy

namespace TauCeti

open _root_.GenLoop

/-- The sphere `TopCat.diskBoundary (n + 2)`, read as the unit sphere of
`EuclideanSpace ℝ (Fin (n + 2))`. -/
private abbrev diskBoundaryIso (n : ℕ) :
    TopCat.diskBoundary.{0} (n + 2) ≅
      TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :=
  TopCat.isoOfHomeo Homeomorph.ulift

/-- The generator `[Sⁿ⁺¹]` of the integral homology of the sphere `TopCat.diskBoundary (n + 2)`,
read on the unit sphere of `EuclideanSpace ℝ (Fin (n + 2))`. -/
private abbrev sphereClass (n : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)) :=
  (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).obj (ModuleCat.of ℤ ℤ)).map
    (diskBoundaryIso n).hom).hom
    ((reducedSingularHomologyι (ModuleCat.of ℤ ℤ) (n + 1)).app (TopCat.diskBoundary.{0} (n + 2))
      ((reducedSingularHomologyTopCatSphereIso (ModuleCat.of ℤ ℤ) (n + 1)).inv 1))

/-- On the sphere, the image of the generator `[Sⁿ⁺¹]` is a unit multiple of the Hurewicz class
of the tautological loop. -/
private lemma exists_sphereClass_eq_units_smul (n : ℕ) :
    ∃ ε : ℤˣ, sphereClass n =
      (ε : ℤ) • (hurewicz (ModuleCat.of ℤ ℤ) (sphereGenLoop (n + 1))).hom 1 := by
  let H := (singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).obj (ModuleCat.of ℤ ℤ)
  -- `k ↦ k • g` and `k ↦ k • sphereClass n` are both isomorphisms `ℤ ≅ Hₙ₊₁(Sⁿ⁺¹; ℤ)`.
  let eg := (asIso (hurewicz (ModuleCat.of ℤ ℤ) (sphereGenLoop (n + 1)))).toLinearEquiv
  have : IsIso ((reducedSingularHomologyι (ModuleCat.of ℤ ℤ) (n + 1)).app
      (TopCat.sphere.{0} (n + 1))) := by
    rw [← reducedSingularHomologySuccIso_hom]
    infer_instance
  let es := ((reducedSingularHomologyTopCatSphereIso (ModuleCat.of ℤ ℤ) (n + 1)).symm ≪≫
    asIso ((reducedSingularHomologyι (ModuleCat.of ℤ ℤ) (n + 1)).app (TopCat.sphere.{0} (n + 1))) ≪≫
      H.mapIso (diskBoundaryIso n)).toLinearEquiv
  have hes : es 1 = sphereClass n := by
    rw [Iso.toLinearEquiv_apply, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, asIso_hom]
    -- `TopCat.sphere (n + 1)` is `TopCat.diskBoundary (n + 2)` by the definition of
    -- `TopCat.sphere`, so the composite only typechecks up to this unfolding: `erw` splits it, and
    -- `rfl` matches the two sides, which differ only in how this object is written.
    erw [Functor.mapIso_hom, ModuleCat.comp_apply, ModuleCat.comp_apply]
    rfl
  have heg : ⇑eg = fun k : ℤ ↦ k • (hurewicz (ModuleCat.of ℤ ℤ) (sphereGenLoop (n + 1))).hom 1 := by
    funext k
    rw [← map_zsmul, smul_eq_mul, mul_one]
    rw [Iso.toLinearEquiv_apply, asIso_hom]
  obtain ⟨ε, hε⟩ := AddMonoidHom.exists_eq_units_smul_of_map_eq
    (es.symm.trans eg).toLinearMap.toAddMonoidHom (x := sphereClass n) (heg ▸ eg.bijective) <| by
      rw [LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe, LinearEquiv.trans_apply, ← hes,
        LinearEquiv.symm_apply_apply, heg]
      exact one_smul _ _
  refine ⟨ε⁻¹, ?_⟩
  rw [hε, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

/-- **The attaching sphere of a generalized loop carries its Hurewicz class, up to a universal
sign.** There is a unit `ε` of `ℤ` such that for every generalized loop
`p : (Iⁿ⁺¹, ∂Iⁿ⁺¹) → (X, x)`, the image of the generator `[Sⁿ⁺¹]` of the homology of the sphere
under the attaching map `GenLoop.diskBoundaryMap p` is `ε` times the Hurewicz class of `p`. -/
theorem exists_singularHomologyMap_diskBoundaryMap_eq_units_smul_hurewicz (n : ℕ) :
    ∃ ε : ℤˣ, ∀ (X : TopCat.{0}) (x : X) (p : Ω^ (Fin (n + 1)) X x),
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).obj (ModuleCat.of ℤ ℤ)).map
          (diskBoundaryMap p)).hom
        ((reducedSingularHomologyι (ModuleCat.of ℤ ℤ) (n + 1)).app (TopCat.diskBoundary.{0} (n + 2))
          ((reducedSingularHomologyTopCatSphereIso (ModuleCat.of ℤ ℤ) (n + 1)).inv 1)) =
        (ε : ℤ) • (hurewicz (ModuleCat.of ℤ ℤ) p).hom 1 := by
  obtain ⟨ε, hε⟩ := exists_sphereClass_eq_units_smul n
  refine ⟨ε, fun X x p ↦ ?_⟩
  -- The attaching map is the map out of the sphere read on `TopCat.diskBoundary`, and both
  -- classes are images of the corresponding classes of the sphere.
  have hd : diskBoundaryMap p = (diskBoundaryIso n).hom ≫ TopCat.ofHom (toSphere p) := by
    ext s
    exact diskBoundaryMap_apply p s
  rw [hurewicz_eq_hurewicz_sphereGenLoop_comp, ModuleCat.comp_apply, ← map_zsmul, ← hε, hd]
  -- `TopCat.ofHom (toSphere p)` has target `TopCat.of X`, which is `X` only up to unfolding.
  erw [Functor.map_comp]
  rfl

end TauCeti
