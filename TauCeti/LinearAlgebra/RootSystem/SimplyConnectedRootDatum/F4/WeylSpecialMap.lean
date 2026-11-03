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

-- Specialize the generic rank-indexed word API once to the concrete F₄ root table.
-- Equality transport below avoids asking `rw` to match across the semireducible
-- `Fin F4.rank` / `Fin 4` boundary.
private theorem geckWeylRootIndex_F4_nil (i : Fin 4) :
    F4.geckWeylRootIndex valid_F4 [] i = Fin.castAdd 44 i := by
  exact (F4.geckWeylRootIndex_nil valid_F4 i).trans (simpleIndex_F4 valid_F4 i)

private theorem geckWeylRootIndex_F4_cons (j : Fin 4) (l : List (Fin 4)) (i : Fin 4) :
    F4.geckWeylRootIndex valid_F4 (j :: l) i =
      f4ReflectionIndex (Fin.castAdd 44 j) (F4.geckWeylRootIndex valid_F4 l i) := by
  calc
    _ = (F4.simplyConnectedRootDatum valid_F4).reflectionPerm (F4.simpleIndex valid_F4 j)
        (F4.geckWeylRootIndex valid_F4 l i) := F4.geckWeylRootIndex_cons valid_F4 j l i
    _ = _ := by
      rw [simplyConnectedRootDatum_F4, simpleIndex_F4 valid_F4 j]
      exact f4SimplyConnectedRootDatum_reflectionPerm _ _

/-- Weyl transport preserves the length of the starting simple root. -/
@[simp] theorem f4Length_geckWeylRootIndex (l : List (Fin 4)) (i : Fin 4) :
    f4Length (F4.geckWeylRootIndex valid_F4 l i) = F4.rootLength i := by
  induction l with
  | nil => exact (congrArg f4Length (geckWeylRootIndex_F4_nil i)).trans (f4Length_castAdd i)
  | cons j l ih =>
    exact (congrArg f4Length (geckWeylRootIndex_F4_cons j l i)).trans
      ((f4Length_f4ReflectionIndex _ _).trans ih)

/-- The special root permutation reverses every node in a Weyl presentation. -/
@[simp] theorem f4SpecialIsogenyIndex_geckWeylRootIndex (l : List (Fin 4)) (i : Fin 4) :
    f4SpecialIsogenyIndex (F4.geckWeylRootIndex valid_F4 l i) =
      F4.geckWeylRootIndex valid_F4 (l.map lengthPermF4) (lengthPermF4 i) := by
  induction l with
  | nil =>
    exact (congrArg f4SpecialIsogenyIndex (geckWeylRootIndex_F4_nil i)).trans
      ((f4SpecialIsogenyIndex_castAdd i).trans (geckWeylRootIndex_F4_nil (lengthPermF4 i)).symm)
  | cons j l ih =>
    have h := congrArg₂ f4ReflectionIndex (f4SpecialIsogenyIndex_castAdd j) ih
    exact (congrArg f4SpecialIsogenyIndex (geckWeylRootIndex_F4_cons j l i)).trans
      ((f4SpecialIsogenyIndex_f4ReflectionIndex _ _).trans
        (h.trans
          (geckWeylRootIndex_F4_cons (lengthPermF4 j) (l.map lengthPermF4) (lengthPermF4 i)).symm))

end TauCeti.DynkinType
