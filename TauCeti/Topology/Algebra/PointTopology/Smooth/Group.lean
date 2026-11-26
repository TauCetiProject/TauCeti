/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.RingHom.Smooth
public import TauCeti.Topology.Algebra.PointTopology.Group
import TauCeti.NumberTheory.LocalField.NormedField
import TauCeti.Topology.Algebra.PointTopology.Scheme.Smooth

/-!
# Smooth homomorphisms are open on field-valued points

For affine group schemes over a complete nontrivially normed field, a smooth homomorphism
to a finite-type group induces an open homomorphism of topological groups on field-valued
points. Its image is an open subgroup, and it carries compact open subgroups to compact open
subgroups by continuity and openness.
-/

public section

open WithConv TauCeti.PointTopology
open scoped TauCeti.PointTopology

namespace BialgHom

/-- A smooth map of coordinate algebras with finite-type domain induces an open map on
convolution points over a complete nontrivially normed field. -/
theorem isOpenMap_mapDomain_of_smooth {K A B : Type u} [NontriviallyNormedField K]
    [CompleteSpace K] [CommRing A] [CommRing B] [Bialgebra K A] [Bialgebra K B]
    [Algebra.FiniteType K A] (φ : A →ₐc[K] B) (hφ : φ.toAlgHom.toRingHom.Smooth) :
    IsOpenMap (mapDomain (A := K) φ) := by
  let eA := (isHomeomorph_ofConv (k := K) (A := A) (R := K)).homeomorph _
  let eB := (isHomeomorph_ofConv (k := K) (A := B) (R := K)).homeomorph _
  have h := eA.symm.isOpenMap.comp
    ((AlgHom.isOpenMap_comap_of_smooth φ.toAlgHom hφ).comp eB.isOpenMap)
  convert h using 1
  funext x
  apply eA.injective
  simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
  simp [eA, eB, mapDomain_apply]

/-- A smooth homomorphism of affine groups over a nonarchimedean local field is open on
rational points when the target is of finite type. -/
theorem isOpenMap_mapDomain_of_smooth_of_isNonarchimedeanLocalField
    {K A B : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CommRing A] [CommRing B] [Bialgebra K A] [Bialgebra K B]
    [Algebra.FiniteType K A] (φ : A →ₐc[K] B) (hφ : φ.toAlgHom.toRingHom.Smooth) :
    IsOpenMap (mapDomain (A := K) φ) := by
  have h : @IsOpenMap _ _
      (@instTopologicalSpaceWithConv K B K _ _ _ _ _ (TauCeti.normalizedNormedFieldTopology K))
      (@instTopologicalSpaceWithConv K A K _ _ _ _ _ (TauCeti.normalizedNormedFieldTopology K))
      (mapDomain (A := K) φ) := by
    let _ := TauCeti.normalizedNontriviallyNormedField K
    let _ := TauCeti.normalizedNormedField_completeSpace K
    exact φ.isOpenMap_mapDomain_of_smooth hφ
  rwa [TauCeti.normalizedNormedField_topology_eq K] at h

end BialgHom
