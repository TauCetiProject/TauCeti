/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.F4.SpecialMap
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Weyl.RootSubgroup

/-!
# Weyl transport and the special F₄ root permutation

The length-exchanging permutation of the forty-eight F₄ roots intertwines Weyl words
with the words obtained by reversing each Bourbaki node. A Weyl-transported simple root
retains its length. These two facts identify the root and exponent when the exceptional
isogeny is applied to a Weyl-transported root subgroup.

## References

* R. Steinberg, *Endomorphisms of Linear Algebraic Groups*, §11.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VIII.
-/

public section

namespace TauCeti.DynkinType

/-- Weyl transport preserves the length of the starting simple root. -/
@[simp] theorem f4Length_geckWeylRootIndex (l : List (Fin 4)) (i : Fin 4) :
    f4Length (F4.geckWeylRootIndex valid_F4 l i) = F4.rootLength i := by
  -- The generic word API uses `Fin F4.rank`, while this concrete table uses `Fin 4`.
  -- `erw` reduces that semireducible rank at the API boundary.
  induction l with
  | nil => erw [F4.geckWeylRootIndex_nil valid_F4 i, simpleIndex_F4, f4Length_castAdd]
  | cons j l ih =>
    erw [F4.geckWeylRootIndex_cons valid_F4 j l i, simplyConnectedRootDatum_F4,
      simpleIndex_F4, f4SimplyConnectedRootDatum_reflectionPerm,
      f4Length_reflectionIndex_simple, ih]

/-- The special root permutation reverses every node in a Weyl presentation. -/
theorem f4SpecialIsogenyIndex_geckWeylRootIndex (l : List (Fin 4)) (i : Fin 4) :
    f4SpecialIsogenyIndex (F4.geckWeylRootIndex valid_F4 l i) =
      F4.geckWeylRootIndex valid_F4 (l.map lengthPermF4) (lengthPermF4 i) := by
  -- As above, the concrete and generic word APIs use definitionally equal rank indices.
  induction l with
  | nil =>
    erw [List.map_nil, F4.geckWeylRootIndex_nil valid_F4 i,
      F4.geckWeylRootIndex_nil valid_F4 (lengthPermF4 i), simpleIndex_F4,
      simpleIndex_F4, f4SpecialIsogenyIndex_castAdd]
  | cons j l ih =>
    erw [List.map_cons, F4.geckWeylRootIndex_cons valid_F4 j l i,
      F4.geckWeylRootIndex_cons valid_F4 (lengthPermF4 j) (l.map lengthPermF4)
        (lengthPermF4 i), simplyConnectedRootDatum_F4, simpleIndex_F4,
      simpleIndex_F4, f4SimplyConnectedRootDatum_reflectionPerm,
      f4SimplyConnectedRootDatum_reflectionPerm, f4SpecialIsogenyIndex_reflectionIndex, ih]

end TauCeti.DynkinType
