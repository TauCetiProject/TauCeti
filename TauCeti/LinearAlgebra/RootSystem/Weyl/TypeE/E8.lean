/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Rational
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E8.Automorphism
import TauCeti.LinearAlgebra.RootSystem.Weyl.Automorphism
import TauCeti.LinearAlgebra.RootSystem.Weyl.BaseChange
import TauCeti.LinearAlgebra.RootSystem.Weyl.CartanType

/-!
# The Weyl group of type `E₈` has order `696729600`

Every finite reduced crystallographic root system over `ℚ` with a base of Cartan type `E₈` has a
Weyl group of order `696729600 = 2¹⁴ · 3⁵ · 5² · 7`, and, the `E₈` diagram having no nontrivial
symmetry, so has its full automorphism group.

The order is known on the pinned integral root datum of type `E₈`
(`TauCeti.DynkinType.card_weylGroup_e8SimplyConnectedRootDatum`). The Weyl group is unchanged by
the entrywise base change of that datum to `ℚ` (`TauCeti.weylGroupBaseChangeEquiv`), which is the
pinned rational model `TauCeti.DynkinType.rationalRootSystem` of type `E₈`, and it is an invariant
of the Cartan type (`TauCeti.nonempty_weylGroup_mulEquiv_of_hasCartanType`), so the order passes
from the model to every rational root system of type `E₈`. These are the Weyl factors of the
`E₈` components of even unimodular lattices, such as `E₈ ⊕ E₈`.

## Main results

* `RootPairing.card_weylGroup_of_hasCartanType_E8`: **every finite reduced crystallographic root
  system over `ℚ` with a base of Cartan type `E₈` has Weyl group of order `696729600`.**
* `RootPairing.card_aut_of_hasCartanType_E8`: so does its automorphism group.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §4.10 and Plate VII.
* S. Fomin and N. Reading, *Root systems and generalized associahedra*, arXiv:math/0505518v3,
  Lecture 2, §2.5, Figure 2.8.
-/

public section

namespace TauCeti.DynkinType

/-- The Weyl group of the pinned rational root system of type `E₈` has order `696729600`: it is
the Weyl group of the pinned integral datum, read after base change to `ℚ`. -/
private theorem card_weylGroup_rationalRootSystem_E8 :
    Nat.card (E8.rationalRootSystem valid_E8).weylGroup = 696729600 := by
  rw [rationalRootSystem_def, ← Nat.card_congr (weylGroupBaseChangeEquiv ℚ _ _).toEquiv,
    simplyConnectedRootDatum_E8]
  -- The goal indexes the roots by `Fin E8.numRoots`, which reduces to the `Fin 240` of the
  -- integral `E₈` datum, so `exact` rather than a further rewrite closes it.
  exact card_weylGroup_e8SimplyConnectedRootDatum

end TauCeti.DynkinType

namespace RootPairing

open TauCeti TauCeti.DynkinType

variable {ι M N : Type*} [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
  {P : RootPairing ι ℚ M N} [Finite ι] [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base}

/-- **The Weyl group of type `E₈` has order `696729600 = 2¹⁴ · 3⁵ · 5² · 7`**: every finite
reduced crystallographic root system over `ℚ` with a base of Cartan type `E₈` has Weyl group of
this order. -/
theorem card_weylGroup_of_hasCartanType_E8 (h : HasCartanType P b .E8) :
    Nat.card P.weylGroup = 696729600 := by
  obtain ⟨e⟩ := nonempty_weylGroup_mulEquiv_of_hasCartanType b (E8.rationalBase valid_E8) .E8 h
    (E8.hasCartanType_rationalRootSystem valid_E8)
  rw [Nat.card_congr e.toEquiv, card_weylGroup_rationalRootSystem_E8]

/-- **The automorphism group of a root system of type `E₈` has order `696729600`**: it is the
Weyl group, the `E₈` diagram having no nontrivial symmetry. -/
theorem card_aut_of_hasCartanType_E8 (h : HasCartanType P b .E8) :
    Nat.card P.Aut = 696729600 := by
  rw [← Subgroup.card_top, ← weylGroup_eq_top_of_hasCartanType_E8 h,
    card_weylGroup_of_hasCartanType_E8 h]

end RootPairing
