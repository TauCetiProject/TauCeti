/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Reductive
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.IdentityComponent
public import TauCeti.Algebra.AlgebraicGroup.Center.Basic
import TauCeti.Algebra.AlgebraicGroup.Smooth.CharZero

/-!
# The radical as the connected center of a reductive group

Over an algebraically closed field of characteristic zero, the solvable radical of a reductive
affine group is the identity component of its scheme-theoretic center. The characteristic-zero
hypothesis makes the center smooth, so no reduction of the center is needed.

One containment uses that the radical is central. For the other, the identity component of the
center is a connected smooth commutative normal subgroup and hence a solvable-radical candidate.
This description is the geometric form of the central-torus reduction from a reductive group to
its semisimple quotient.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 19 and 21.
* A. Borel, *Linear Algebraic Groups*, §§14.2 and 14.10.
-/

public section

namespace TauCeti.reductiveCommHopfAlgProperty

universe u

noncomputable section

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- Over an algebraically closed field of characteristic zero, the solvable radical of a
reductive affine group is the identity component of its scheme-theoretic center. -/
theorem solvableRadicalDefiningIdeal_eq_identityComponent_centerDefiningIdeal
    (hH : reductiveCommHopfAlgProperty k H) :
    FiniteTypeCommHopfAlgCat.solvableRadicalDefiningIdeal H =
      (TauCeti.CommHopfAlgCat.centerDefiningIdeal H.obj).identityComponent := by
  let C := TauCeti.CommHopfAlgCat.centerDefiningIdeal H.obj
  let J := C.identityComponent
  have hcentral : J.IsCentral :=
    (TauCeti.CommHopfAlgCat.centerDefiningIdeal_le_iff H.obj J).mp C.le_identityComponent
  let _ : Algebra.Smooth k (FiniteTypeCommHopfAlgCat.quotient H C) :=
    (smoothCommHopfAlgProperty_iff _).mp
      (smoothCommHopfAlgProperty_of_charZero k
        (FiniteTypeCommHopfAlgCat.quotient H C).obj)
  have hcandidate : HopfIdeal.IsSolvableRadicalCandidate H J := by
    let _ : Coalgebra.IsCocomm k (FiniteTypeCommHopfAlgCat.quotient H J) :=
      hcentral.isCocomm_quotient
    exact .mk hcentral.isNormal C.geometricallyConnected_identityComponent
      C.smooth_identityComponent
      (geometricallySolvablePointsCommHopfAlgProperty_of_isCocomm k _)
  apply le_antisymm
  · exact FiniteTypeCommHopfAlgCat.solvableRadicalDefiningIdeal_le H J hcandidate
  · apply C.identityComponent_le_of_le
      ((TauCeti.CommHopfAlgCat.centerDefiningIdeal_le_iff H.obj _).mpr
        hH.isCentral_solvableRadicalDefiningIdeal)
    exact HopfIdeal.IsSolvableRadicalCandidate.geometricallyConnected
      (FiniteTypeCommHopfAlgCat.isSolvableRadicalCandidate_solvableRadicalDefiningIdeal H)

end

end TauCeti.reductiveCommHopfAlgProperty
