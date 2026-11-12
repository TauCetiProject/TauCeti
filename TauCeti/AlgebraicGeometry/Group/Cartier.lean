/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Smooth.CharZero

/-!
# Cartier's theorem for affine group schemes

Every affine group scheme of finite type over a field of characteristic zero is smooth.
This transports `TauCeti.smoothCommHopfAlgProperty_of_charZero` from coordinate Hopf
algebras to native group objects in schemes. In particular it applies to closed subgroup
schemes without a prior reducedness or smoothness assumption.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 3, Cartier's theorem.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

/-- An affine group scheme of finite type over a field of characteristic zero is smooth. -/
theorem smooth_of_grpObj_of_charZero {k : Type u} [Field k] [CharZero k]
    (G : Over (Spec (.of k))) [GrpObj G] [IsAffine G.left]
    [LocallyOfFiniteType G.hom] : Smooth G.hom := by
  let A : FiniteTypeAffineGroupSchemeCat (.of k) :=
    ⟨⟨Grp.mk G, (affineGroupSchemeProperty_iff _).mpr inferInstance⟩,
      (finiteTypeAffineGroupSchemeProperty_iff _ _).mpr inferInstance⟩
  apply (smooth_iff_algebraSmooth_coordinate k A).mpr
  exact (smoothCommHopfAlgProperty_iff _).mp
    (smoothCommHopfAlgProperty_of_charZero k _)

end TauCeti.AlgebraicGeometry
