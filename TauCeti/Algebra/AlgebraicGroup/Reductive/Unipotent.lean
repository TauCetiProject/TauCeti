/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Connected
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Reductive.Basic

/-!
# Normal unipotent subgroups of reductive groups in characteristic zero

Over a characteristic-zero field, a smooth normal unipotent closed subgroup of a reductive
affine group is trivial. Connectedness of the subgroup follows from unipotence, so it need
not be supplied separately. The subgroup can be defined over the original field; no
algebraically closed hypothesis is imposed.

This applies to normal unipotent kernels in commutative reductive groups, once those kernels
have been constructed as smooth closed subgroup schemes.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 14 and 19.
-/

public section

namespace TauCeti.reductiveCommHopfAlgProperty

universe u

variable {k : Type u} [Field k] [CharZero k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- Every smooth normal unipotent closed subgroup of a reductive group in characteristic
zero is the identity subgroup, without a separate connectedness assumption. -/
theorem eq_augmentation_of_isNormal_of_smoothUnipotent
    (hH : reductiveCommHopfAlgProperty k H) (I : HopfIdeal k H) (hI : I.IsNormal)
    (hu : smoothUnipotentCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient H I)) :
    I = HopfIdeal.augmentation k H := by
  apply le_antisymm (HopfIdeal.le_augmentation k H I)
  rw [← hH.unipotentRadicalDefiningIdeal_eq_augmentation]
  exact FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_le H I
    (HopfIdeal.IsUnipotentRadicalCandidate.mk hI hu.geometricallyConnected hu)

end TauCeti.reductiveCommHopfAlgProperty
