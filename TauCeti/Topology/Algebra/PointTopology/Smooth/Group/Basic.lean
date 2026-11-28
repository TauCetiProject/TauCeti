/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RingHom.Smooth
public import TauCeti.Topology.Algebra.PointTopology.Group
import TauCeti.Topology.Algebra.PointTopology.Scheme.Smooth

/-!
# Smooth homomorphisms are open on field-valued points

A smooth map of commutative bialgebras induces an open map on convolution points valued in a
complete nontrivially normed field algebra. In the Hopf-algebra case these are groups of points;
the range subgroup is open and compact open subgroups have compact open images. The corresponding
valuative-topology statements are in
`TauCeti.Topology.Algebra.PointTopology.Smooth.Group.LocalField`.
-/

public section

open WithConv TauCeti.PointTopology
open scoped TauCeti.PointTopology

namespace BialgHom

/-- A smooth map of commutative bialgebras induces an open map on convolution points valued
in a complete nontrivially normed field algebra over the base ring. -/
theorem isOpenMap_mapDomain_of_smooth {k K A B : Type u} [CommRing k]
    [NontriviallyNormedField K] [Algebra k K]
    [CompleteSpace K] [CommRing A] [CommRing B] [Bialgebra k A] [Bialgebra k B]
    (φ : A →ₐc[k] B) (hφ : φ.toAlgHom.toRingHom.Smooth) :
    IsOpenMap (mapDomain (A := K) φ) := by
  let eA := (isHomeomorph_ofConv (k := k) (A := A) (R := K)).homeomorph _
  let eB := (isHomeomorph_ofConv (k := k) (A := B) (R := K)).homeomorph _
  have h := eA.symm.isOpenMap.comp
    ((AlgHom.isOpenMap_comap_of_smooth φ.toAlgHom hφ).comp eB.isOpenMap)
  convert h using 1
  funext x
  apply eA.injective
  simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
  simp [eA, eB, mapDomain_apply]

end BialgHom
