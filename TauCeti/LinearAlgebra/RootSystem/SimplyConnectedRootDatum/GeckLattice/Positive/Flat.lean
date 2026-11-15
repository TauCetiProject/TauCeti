/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Subsystem.Flat
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Positive.BaseChange

/-!
# Flatness of the positive Geck carrier

The positive Geck carrier has torsion-free coordinate algebra over `ℤ`. Thus its structural
morphism is flat, as are its pullbacks. The coordinate algebra presented by the positive
base-change ideal is flat over every commutative base ring: the named comparison identifies it
with scalar extension of the integral coordinate algebra.
-/

public section

open AlgebraicGeometry
open TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType

universe v

attribute [local instance high] Algebra.toModule

variable (t : DynkinType) (ht : t.Valid)

/-- The positive Geck coordinate algebra has no scalar torsion over `ℤ`. -/
instance isTorsionFree_geckTorusPositiveCoordinateHopfAlgebra :
    Module.IsTorsionFree ℤ
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht))
        (t.geckTorusPositiveDefiningIdeal ht)) := by
  rw [geckTorusPositiveDefiningIdeal_def]
  infer_instance

/-- The structural morphism of the integral positive Geck carrier is flat. -/
instance flat_geckTorusPositiveGroupScheme :
    Flat (t.geckTorusPositiveGroupScheme ht).X.hom := by
  rw [geckTorusPositiveGroupScheme_def]
  infer_instance

/-- The transported positive coordinate algebra is flat over every commutative base ring. -/
instance flat_geckTorusPositiveBaseChangeCoordinateHopfAlgebra
    (A : Type v) [CommRing A] :
    Module.Flat A
      (CommHopfAlgCat.quotient
        (CommHopfAlgCat.baseChange (K := A)
          (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)))
        (t.geckTorusPositiveBaseChangeIdeal ht A)) := by
  rw [geckTorusPositiveBaseChangeIdeal_def, geckTorusPositiveDefiningIdeal_def,
    ← kostantTorusSubsystemBaseChangeIdeal_def]
  infer_instance

end TauCeti.DynkinType
