/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.PointedHomotopyCat.Basic
public import TauCeti.Topology.Homotopy.Extension.Basic
public import TauCeti.Topology.Homotopy.HomotopyEquiv
import TauCeti.Topology.Homotopy.Extension.HomotopyEquivRel

/-!
# Pointed homotopy equivalences and isomorphisms in `PointedHomotopyCat`

An isomorphism in `TauCeti.PointedHomotopyCat` is represented by a homotopy equivalence whose
forward and inverse maps both preserve the base points and whose homotopies to the identities are
relative to the base points (`TauCeti.PointedHomotopyCat.homotopyEquivOfIso`). Conversely, between
spaces whose base points have the homotopy extension property, every base-point-preserving homotopy
equivalence upgrades to an isomorphism in `TauCeti.PointedHomotopyCat`
(`TauCeti.PointedHomotopyCat.isoOfHomotopyEquiv`), by
`TauCeti.HasHomotopyExtensionProperty.exists_basedInverse_homotopicRel`.

## Main definitions

* `TauCeti.PointedHomotopyCat.isoOfHomotopyEquiv`: a based homotopy equivalence between spaces
  whose base points have the homotopy extension property, as an isomorphism in
  `PointedHomotopyCat`.
* `TauCeti.PointedHomotopyCat.homotopyEquivOfIso`: the underlying pointed homotopy equivalence of
  an isomorphism in `PointedHomotopyCat`.

## Main results

* `TauCeti.PointedHomotopyCat.isIso_quotient_map_of_homotopyEquiv`: a based map whose underlying
  continuous map is a homotopy equivalence becomes an isomorphism in `PointedHomotopyCat` when both
  base points have the homotopy extension property.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Chapter 0 (Proposition 0.19).
-/

public section

noncomputable section

universe u

open CategoryTheory

namespace TauCeti

namespace PointedHomotopyCat

/-- **A based homotopy equivalence between well-pointed spaces is an isomorphism in
`PointedHomotopyCat`.** If both base points have the homotopy extension property and
`h : X.carrier ≃ₕ Y.carrier` preserves the base points, then `h` admits a based homotopy inverse
with both homotopies relative to the base points
(`HasHomotopyExtensionProperty.exists_basedInverse_homotopicRel`). -/
def isoOfHomotopyEquiv {X Y : BasedTopologicalSpace.{u}}
    (hX : HasHomotopyExtensionProperty ({X.basepoint} : Set X.carrier))
    (hY : HasHomotopyExtensionProperty ({Y.basepoint} : Set Y.carrier))
    (h : ContinuousMap.HomotopyEquiv X.carrier Y.carrier)
    (hh : h.toFun X.basepoint = Y.basepoint) :
    quotient.obj X ≅ quotient.obj Y :=
  let hg := hX.exists_basedInverse_homotopicRel hY h hh
  { hom := quotient.map ⟨h.toFun, hh⟩
    inv := quotient.map ⟨hg.choose, hg.choose_spec.1⟩
    hom_inv_id := by
      rw [← quotient.map_comp, ← quotient.map_id, quotient_map_eq_iff]
      simp only [BasedTopologicalSpace.comp_eq_hom_comp,
        BasedTopologicalSpace.Hom.toContinuousMap_comp, BasedTopologicalSpace.id_eq_hom_id,
        BasedTopologicalSpace.Hom.toContinuousMap_id]
      exact hg.choose_spec.2.1
    inv_hom_id := by
      rw [← quotient.map_comp, ← quotient.map_id, quotient_map_eq_iff]
      simp only [BasedTopologicalSpace.comp_eq_hom_comp,
        BasedTopologicalSpace.Hom.toContinuousMap_comp, BasedTopologicalSpace.id_eq_hom_id,
        BasedTopologicalSpace.Hom.toContinuousMap_id]
      exact hg.choose_spec.2.2 }

/-- The forward morphism of `PointedHomotopyCat.isoOfHomotopyEquiv` is the pointed homotopy class
of the given based homotopy equivalence. -/
@[simp]
theorem isoOfHomotopyEquiv_hom {X Y : BasedTopologicalSpace.{u}}
    (hX : HasHomotopyExtensionProperty ({X.basepoint} : Set X.carrier))
    (hY : HasHomotopyExtensionProperty ({Y.basepoint} : Set Y.carrier))
    (h : ContinuousMap.HomotopyEquiv X.carrier Y.carrier)
    (hh : h.toFun X.basepoint = Y.basepoint) :
    (isoOfHomotopyEquiv hX hY h hh).hom = quotient.map ⟨h.toFun, hh⟩ :=
  (rfl)

/-- A based map between spaces whose base points have the homotopy extension property becomes an
isomorphism in `PointedHomotopyCat` as soon as its underlying continuous map is a homotopy
equivalence. -/
theorem isIso_quotient_map_of_homotopyEquiv {X Y : BasedTopologicalSpace.{u}}
    (hX : HasHomotopyExtensionProperty ({X.basepoint} : Set X.carrier))
    (hY : HasHomotopyExtensionProperty ({Y.basepoint} : Set Y.carrier))
    {f : X ⟶ Y} (h : ContinuousMap.HomotopyEquiv X.carrier Y.carrier)
    (hf : h.toFun = f.toContinuousMap) :
    IsIso (quotient.map f) := by
  have hh : h.toFun X.basepoint = Y.basepoint := by
    rw [hf]
    exact f.map_basepoint
  have hfeq : (⟨h.toFun, hh⟩ : X ⟶ Y) = f := BasedTopologicalSpace.Hom.ext hf
  rw [← hfeq, ← isoOfHomotopyEquiv_hom hX hY h hh]
  infer_instance

/-- **An isomorphism in `PointedHomotopyCat` gives a pointed homotopy equivalence.** Its forward
and inverse maps are chosen based representatives of `e.hom` and `e.inv`, so both preserve base
points and both composites are homotopic to the identities relative to the base points. -/
def homotopyEquivOfIso {X Y : BasedTopologicalSpace.{u}}
    (e : quotient.obj X ≅ quotient.obj Y) :
    ContinuousMap.HomotopyEquiv X.carrier Y.carrier :=
  let hf := quotient.map_surjective e.hom
  let hg := quotient.map_surjective e.inv
  { toFun := hf.choose.toContinuousMap
    invFun := hg.choose.toContinuousMap
    left_inv := by
      have h := (quotient_map_eq_iff (hf.choose ≫ hg.choose) (𝟙 X)).1 <| by
        rw [quotient.map_comp, hf.choose_spec, hg.choose_spec, e.hom_inv_id, quotient.map_id]
      simp only [BasedTopologicalSpace.comp_eq_hom_comp,
        BasedTopologicalSpace.Hom.toContinuousMap_comp, BasedTopologicalSpace.id_eq_hom_id,
        BasedTopologicalSpace.Hom.toContinuousMap_id] at h
      exact h.homotopic
    right_inv := by
      have h := (quotient_map_eq_iff (hg.choose ≫ hf.choose) (𝟙 Y)).1 <| by
        rw [quotient.map_comp, hg.choose_spec, hf.choose_spec, e.inv_hom_id, quotient.map_id]
      simp only [BasedTopologicalSpace.comp_eq_hom_comp,
        BasedTopologicalSpace.Hom.toContinuousMap_comp, BasedTopologicalSpace.id_eq_hom_id,
        BasedTopologicalSpace.Hom.toContinuousMap_id] at h
      exact h.homotopic }

/-- The forward map of `PointedHomotopyCat.homotopyEquivOfIso` preserves base points. -/
@[simp]
theorem homotopyEquivOfIso_toFun_basepoint {X Y : BasedTopologicalSpace.{u}}
    (e : quotient.obj X ≅ quotient.obj Y) :
    (homotopyEquivOfIso e).toFun X.basepoint = Y.basepoint :=
  (quotient.map_surjective e.hom).choose.map_basepoint

/-- The inverse map of `PointedHomotopyCat.homotopyEquivOfIso` preserves base points. -/
@[simp]
theorem homotopyEquivOfIso_invFun_basepoint {X Y : BasedTopologicalSpace.{u}}
    (e : quotient.obj X ≅ quotient.obj Y) :
    (homotopyEquivOfIso e).invFun Y.basepoint = X.basepoint :=
  (quotient.map_surjective e.inv).choose.map_basepoint

/-- The forward map of `PointedHomotopyCat.homotopyEquivOfIso` represents `e.hom`. -/
@[simp]
theorem quotient_map_homotopyEquivOfIso_toFun {X Y : BasedTopologicalSpace.{u}}
    (e : quotient.obj X ≅ quotient.obj Y) :
    quotient.map ⟨(homotopyEquivOfIso e).toFun, homotopyEquivOfIso_toFun_basepoint e⟩ = e.hom :=
  (quotient.map_surjective e.hom).choose_spec

/-- The inverse map of `PointedHomotopyCat.homotopyEquivOfIso` represents `e.inv`. -/
@[simp]
theorem quotient_map_homotopyEquivOfIso_invFun {X Y : BasedTopologicalSpace.{u}}
    (e : quotient.obj X ≅ quotient.obj Y) :
    quotient.map ⟨(homotopyEquivOfIso e).invFun, homotopyEquivOfIso_invFun_basepoint e⟩ = e.inv :=
  (quotient.map_surjective e.inv).choose_spec

/-- The left composite of `PointedHomotopyCat.homotopyEquivOfIso` is homotopic to the identity
relative to the base point. -/
theorem homotopyEquivOfIso_left_inv_homotopicRel {X Y : BasedTopologicalSpace.{u}}
    (e : quotient.obj X ≅ quotient.obj Y) :
    ((homotopyEquivOfIso e).invFun.comp (homotopyEquivOfIso e).toFun).HomotopicRel
      (ContinuousMap.id X.carrier) {X.basepoint} := by
  have h := (quotient_map_eq_iff
      (⟨(homotopyEquivOfIso e).toFun, homotopyEquivOfIso_toFun_basepoint e⟩ ≫
        ⟨(homotopyEquivOfIso e).invFun, homotopyEquivOfIso_invFun_basepoint e⟩) (𝟙 X)).1 <| by
    rw [quotient.map_comp, quotient_map_homotopyEquivOfIso_toFun,
      quotient_map_homotopyEquivOfIso_invFun, e.hom_inv_id, quotient.map_id]
  simpa only [BasedTopologicalSpace.comp_eq_hom_comp,
    BasedTopologicalSpace.Hom.toContinuousMap_comp, BasedTopologicalSpace.id_eq_hom_id,
    BasedTopologicalSpace.Hom.toContinuousMap_id] using h

/-- The right composite of `PointedHomotopyCat.homotopyEquivOfIso` is homotopic to the identity
relative to the base point. -/
theorem homotopyEquivOfIso_right_inv_homotopicRel {X Y : BasedTopologicalSpace.{u}}
    (e : quotient.obj X ≅ quotient.obj Y) :
    ((homotopyEquivOfIso e).toFun.comp (homotopyEquivOfIso e).invFun).HomotopicRel
      (ContinuousMap.id Y.carrier) {Y.basepoint} := by
  have h := (quotient_map_eq_iff
      (⟨(homotopyEquivOfIso e).invFun, homotopyEquivOfIso_invFun_basepoint e⟩ ≫
        ⟨(homotopyEquivOfIso e).toFun, homotopyEquivOfIso_toFun_basepoint e⟩) (𝟙 Y)).1 <| by
    rw [quotient.map_comp, quotient_map_homotopyEquivOfIso_invFun,
      quotient_map_homotopyEquivOfIso_toFun, e.inv_hom_id, quotient.map_id]
  simpa only [BasedTopologicalSpace.comp_eq_hom_comp,
    BasedTopologicalSpace.Hom.toContinuousMap_comp, BasedTopologicalSpace.id_eq_hom_id,
    BasedTopologicalSpace.Hom.toContinuousMap_id] using h

end PointedHomotopyCat

end TauCeti
