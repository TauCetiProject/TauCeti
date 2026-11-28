/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.LinearAlgebra.RootSystem.Isomorphism.Pairing
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Reduced

/-!
# Cartan-matching pairing comparisons in type `B₂`

The Bourbaki-numbered simple roots of `B₂` have ordered pairings `-2` and `-1`.
The comparison with any Cartan-matching base over a characteristic-zero domain must retain
this order, rather than transposing the matrix. The target root pairing below need not span
its ambient modules and its scalar ring need not be the integers of the source datum.

The last check pairs with a nonsimple coroot, obtained by reflecting the short simple root
at the long one. Its pairing with the long simple root is `2`.
-/

namespace TauCeti.Examples

open DynkinType

attribute [local instance] DynkinType.isReduced_simplyConnectedRootDatum

variable {ι R M N : Type*} [CommRing R] [IsDomain R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)
  (e : ((B 2).simplyConnectedBase (by simp)).support ≃ b.support)
  (he : ∀ i j, b.cartanMatrix (e i) (e j) =
    ((B 2).simplyConnectedBase (by simp)).cartanMatrix i j)

/-- Long root against short coroot: the ordered entry is `-2`. -/
example :
    P.pairingIn ℤ
      (((B 2).simplyConnectedBase (by simp)).indexEquivOfCartanMatrixEq b e he
        ((B 2).simpleIndex (by simp) ⟨0, by simp⟩))
      (((B 2).simplyConnectedBase (by simp)).indexEquivOfCartanMatrixEq b e he
        ((B 2).simpleIndex (by simp) ⟨1, by simp⟩)) = -2 := by
  rw [RootPairing.Base.pairingIn_indexEquivOfCartanMatrixEq]
  rw [(B 2).pairingIn_simpleIndex (by simp)]
  rw [cartanMatrix_B]
  decide

/-- Short root against long coroot: the reversed entry is `-1`. -/
example :
    P.pairingIn ℤ
      (((B 2).simplyConnectedBase (by simp)).indexEquivOfCartanMatrixEq b e he
        ((B 2).simpleIndex (by simp) ⟨1, by simp⟩))
      (((B 2).simplyConnectedBase (by simp)).indexEquivOfCartanMatrixEq b e he
        ((B 2).simpleIndex (by simp) ⟨0, by simp⟩)) = -1 := by
  rw [RootPairing.Base.pairingIn_indexEquivOfCartanMatrixEq]
  rw [(B 2).pairingIn_simpleIndex (by simp)]
  rw [cartanMatrix_B]
  decide

/-- A reflected short coroot pairs with the long simple root with value `2`. -/
example :
    P.pairingIn ℤ
      (((B 2).simplyConnectedBase (by simp)).indexEquivOfCartanMatrixEq b e he
        ((B 2).simpleIndex (by simp) ⟨0, by simp⟩))
      (((B 2).simplyConnectedBase (by simp)).indexEquivOfCartanMatrixEq b e he
        (((B 2).simplyConnectedRootDatum (by simp)).reflectionPerm
          ((B 2).simpleIndex (by simp) ⟨0, by simp⟩)
          ((B 2).simpleIndex (by simp) ⟨1, by simp⟩))) = 2 := by
  rw [RootPairing.Base.pairingIn_indexEquivOfCartanMatrixEq,
    RootPairing.pairingIn_reflectionPerm, RootPairing.pairingIn_reflectionPerm_self_left]
  rw [(B 2).pairingIn_simpleIndex (by simp)]
  rw [cartanMatrix_B]
  decide

end TauCeti.Examples
