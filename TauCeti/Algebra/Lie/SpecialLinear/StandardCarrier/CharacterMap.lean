/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.TwistedFrobenius
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.CharacterMap

/-!
# Character pullbacks on the standard type-A carrier

The weight-torus coordinates of `SlStd.points r A` are fundamental-weight coordinates. The
signed reverse-inverse-transpose graph automorphism reverses those coordinates, so its character
pullback is reversal as well. Composing it with the `p ^ k`-power Frobenius multiplies this
pullback by `p ^ k`. These computations identify the character actions of the represented
endomorphisms, independently of any comparison with another group scheme.

The Frobenius result holds over every commutative ring of exponential characteristic `p`;
the graph result requires no characteristic assumption, including in rank zero.

The argument uses the torus equations of `SlStd.graphAutomorphismPoints` and `SlStd.frobenius`
and the contravariant composition law `IsCharacterMap.comp`, as in
`DynkinType.isCharacterMap_geckTwistedFrobenius`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 10, Theorem 29.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
-/

public section

namespace TauCeti.SlStd

variable (r : ℕ) (A : Type) [CommRing A]

/-- The character pullback of the pinned graph automorphism is reversal in fundamental-weight
coordinates. -/
theorem isCharacterMap_graphAutomorphismPoints :
    IsCharacterMap (weightTorusPoints r A) (graphAutomorphismPoints r A).toMonoidHom
      (LinearEquiv.funCongrLeft ℤ ℤ (Fin.revPerm : Equiv.Perm (Fin r))).toLinearMap := by
  refine isCharacterMap_iff.mpr fun s => ?_
  rw [MulEquiv.coe_toMonoidHom, graphAutomorphismPoints_weightTorusPoints]
  congr 1
  funext i
  have hsingle : (LinearEquiv.funCongrLeft ℤ ℤ
      (Fin.revPerm : Equiv.Perm (Fin r))) (Pi.single i 1) = Pi.single i.rev 1 := by
    ext j
    simp [LinearEquiv.funCongrLeft_apply, Pi.single_apply, Fin.rev_eq_iff]
  simp [hsingle]

variable (p k : ℕ) [ExpChar A p]

/-- The character pullback of the `p ^ k`-power Frobenius is multiplication by `p ^ k`. -/
theorem isCharacterMap_frobenius :
    IsCharacterMap (weightTorusPoints r A) (frobenius r p k A) ((p ^ k : ℕ) • 1) :=
  isCharacterMap_iff.mpr fun s => by
    rw [frobenius_weightTorusPoints, torusPointMap_nsmul, torusPointMap_one,
      MonoidHom.pow_apply, MonoidHom.id_apply]

/-- The character pullback of graph-twisted Frobenius is `p ^ k` times reversal. -/
theorem isCharacterMap_twistedFrobenius :
    IsCharacterMap (weightTorusPoints r A) (twistedFrobenius r p k A)
      ((p ^ k : ℕ) •
        (LinearEquiv.funCongrLeft ℤ ℤ (Fin.revPerm : Equiv.Perm (Fin r))).toLinearMap) := by
  have h := (isCharacterMap_graphAutomorphismPoints r A).comp
    (isCharacterMap_frobenius r A p k)
  rw [smul_mul_assoc, one_mul] at h
  refine isCharacterMap_iff.mpr fun s => ?_
  rw [twistedFrobenius_apply]
  exact h.map_apply s

end TauCeti.SlStd
