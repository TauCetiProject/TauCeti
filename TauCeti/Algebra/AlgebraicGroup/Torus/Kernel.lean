/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.CharacterLattice
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Kernel
public import TauCeti.Algebra.AlgebraicGroup.Torus.CharacterLattice.Characterization

/-!
# When a multiplicative-type kernel is a torus

The scheme-theoretic kernel of a homomorphism of multiplicative-type groups is a torus exactly
when the cokernel of the geometric character map is torsion-free. This uses the coordinate
algebra of the kernel, retaining infinitesimal structure in positive characteristic.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.9(b) and §12.d.
-/

public section

open CategoryTheory

namespace TauCeti.multiplicativeTypeCommHopfAlgProperty

universe u

variable {k : Type u} [Field k] {H K : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- A homomorphism of multiplicative-type groups has a torus as its scheme-theoretic kernel
exactly when its geometric character cokernel is torsion-free. No smoothness assumption on
either group is required. -/
theorem torus_kernelCoordinate_iff_isMulTorsionFree_quotient
    (hH : multiplicativeTypeCommHopfAlgProperty k H)
    (hK : multiplicativeTypeCommHopfAlgProperty k K) (f : H.obj ⟶ K.obj) :
    torusCommHopfAlgProperty k
        (FiniteTypeCommHopfAlgCat.quotient K (CommHopfAlgCat.kernelHopfIdeal f)) ↔
      IsMulTorsionFree (CommHopfAlgCat.geometricCharacterGroup K.obj ⧸
        (CommHopfAlgCat.geometricCharacterMap f).range) := by
  let _ := CommHopfAlgCat.geometricCharacterGroup_fg_of_multiplicativeType K hK
  let C := CommHopfAlgCat.geometricCharacterGroup K.obj ⧸
    (CommHopfAlgCat.geometricCharacterMap f).range
  exact torus_iff_isMulTorsionFree_of_baseChange_iso_coordinateRing (FGCommGrpCat.of C)
    (ObjectProperty.isoMk _ (geometricKernelCoordinateIso hH hK f).symm)

end TauCeti.multiplicativeTypeCommHopfAlgProperty
