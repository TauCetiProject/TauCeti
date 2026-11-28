/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LocalField.Basic
public import TauCeti.Topology.Algebra.PointTopology.Smooth.Group.Basic
import TauCeti.NumberTheory.LocalField.NormedField

/-!
# Smooth maps on convolution points over a local field

Smooth maps of commutative bialgebras are open on convolution points valued in a nonarchimedean
local field algebra. For Hopf algebras, the range is an open subgroup and the image of a compact
open subgroup is compact and open, as required by ReductiveGroupsPartII, RG2.0.2.
-/

public section

open WithConv TauCeti.PointTopology
open scoped TauCeti.PointTopology

namespace BialgHom

/-- A smooth map of commutative bialgebras is open on convolution points valued in a
nonarchimedean local field algebra, with its valuative topology. -/
theorem isOpenMap_mapDomain_of_smooth_of_isNonarchimedeanLocalField
    {k K A B : Type u} [CommRing k] [Field K] [Algebra k K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CommRing A] [CommRing B] [Bialgebra k A] [Bialgebra k B]
    (φ : A →ₐc[k] B) (hφ : φ.toAlgHom.toRingHom.Smooth) :
    IsOpenMap (mapDomain (A := K) φ) := by
  have h : @IsOpenMap _ _
      (@instTopologicalSpaceWithConv k B K _ _ _ _ _ (TauCeti.normalizedNormedFieldTopology K))
      (@instTopologicalSpaceWithConv k A K _ _ _ _ _ (TauCeti.normalizedNormedFieldTopology K))
      (mapDomain (A := K) φ) := by
    let _ := TauCeti.normalizedNontriviallyNormedField K
    let _ := TauCeti.normalizedNormedField_completeSpace K
    exact φ.isOpenMap_mapDomain_of_smooth hφ
  rwa [TauCeti.normalizedNormedField_topology_eq K] at h

/-- In the Hopf-algebra case, a smooth map has an open range subgroup on local-field points. -/
theorem isOpen_range_mapDomain_of_smooth_of_isNonarchimedeanLocalField
    {k K A B : Type u} [CommRing k] [Field K] [Algebra k K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CommRing A] [CommRing B]
    [HopfAlgebra k A] [HopfAlgebra k B]
    (φ : A →ₐc[k] B) (hφ : φ.toAlgHom.toRingHom.Smooth) :
    IsOpen ((mapDomain (A := K) φ).range : Set (WithConv (A →ₐ[k] K))) := by
  simpa only [MonoidHom.coe_range] using
    (φ.isOpenMap_mapDomain_of_smooth_of_isNonarchimedeanLocalField hφ).isOpen_range

/-- In the Hopf-algebra case, a smooth map carries compact open subgroups of local-field
points to compact open subgroups. -/
theorem isCompact_isOpen_map_subgroup_of_smooth_of_isNonarchimedeanLocalField
    {k K A B : Type u} [CommRing k] [Field K] [Algebra k K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CommRing A] [CommRing B]
    [HopfAlgebra k A] [HopfAlgebra k B]
    (φ : A →ₐc[k] B) (hφ : φ.toAlgHom.toRingHom.Smooth)
    (U : Subgroup (WithConv (B →ₐ[k] K)))
    (hc : IsCompact (U : Set (WithConv (B →ₐ[k] K))))
    (ho : IsOpen (U : Set (WithConv (B →ₐ[k] K)))) :
    IsCompact (U.map (mapDomain (A := K) φ) : Set (WithConv (A →ₐ[k] K))) ∧
      IsOpen (U.map (mapDomain (A := K) φ) : Set (WithConv (A →ₐ[k] K))) := by
  exact ⟨hc.image (continuous_mapDomain φ),
    φ.isOpenMap_mapDomain_of_smooth_of_isNonarchimedeanLocalField hφ _ ho⟩

end BialgHom
