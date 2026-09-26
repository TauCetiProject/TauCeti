/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Etale
public import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# Smoothness of finite commutative group algebras

Over a field, the group algebra of a finite commutative group is smooth precisely when the
group order is invertible in the field. The forward direction uses reducedness of a smooth
algebra: in the defining characteristic, Cauchy's theorem supplies a nontrivial torsion
element, whose difference from the identity is nilpotent in the group algebra. The reverse
direction uses étaleness of group algebras of invertible order.

This criterion detects smoothness of finite diagonalizable groups, including the roots-of-unity
group schemes.

## References

* J. S. Milne, *Algebraic Groups* (2017), §12.
-/

public section

namespace TauCeti.MonoidAlgebra

variable (k G : Type*) [Field k] [CommGroup G] [Finite G]

/-- A finite commutative group algebra over a field is smooth if and only if the order of the
group is invertible in the field. -/
@[simp]
theorem smooth_iff_isUnit_card :
    Algebra.Smooth k (MonoidAlgebra k G) ↔ IsUnit (Nat.card G : k) := by
  refine ⟨fun hs => ?_, fun h => ?_⟩
  · by_contra h
    apply not_isReduced_monoidAlgebra_of_not_isUnit_card k G h
    let _ : Algebra.Smooth k (MonoidAlgebra k G) := hs
    exact isReduced_of_smooth k (MonoidAlgebra k G)
  · let _ : Algebra.Etale k (MonoidAlgebra k G) := etale_of_isUnit_card k G h
    infer_instance

end TauCeti.MonoidAlgebra
