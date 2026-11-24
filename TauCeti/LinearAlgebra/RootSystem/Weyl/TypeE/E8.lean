/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.DynkinType
import TauCeti.LinearAlgebra.RootSystem.BaseChange.CartanType
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E8.Automorphism
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Reduced
import TauCeti.LinearAlgebra.RootSystem.Weyl.Automorphism
import TauCeti.LinearAlgebra.RootSystem.Weyl.BaseChange
import TauCeti.LinearAlgebra.RootSystem.Weyl.CartanType

/-!
# The Weyl group of type `E₈` has order `696729600`

Every finite reduced crystallographic root system over a characteristic-zero domain, such as `ℚ`,
with a base of Cartan type `E₈` has a Weyl group of order `696729600 = 2¹⁴ · 3⁵ · 5² · 7`, and, the
`E₈` diagram having no nontrivial symmetry, so has its full automorphism group.

The order is known on the pinned integral root datum of type `E₈`
(`TauCeti.DynkinType.card_weylGroup_e8SimplyConnectedRootDatum`). The Weyl group is unchanged by
the entrywise base change of that datum to any such domain `R`
(`TauCeti.weylGroupBaseChangeEquiv`), the base change is again a root system of type `E₈` because
the `E₈` roots already span integrally and base change keeps the Cartan type
(`TauCeti.HasCartanType.rootPairingBaseChange`), and the Weyl group is an invariant of the Cartan
type (`TauCeti.nonempty_weylGroup_mulEquiv_of_hasCartanType`), so the order passes from that model
to every root system of type `E₈` over `R`. These are the Weyl factors of the `E₈` components of
even unimodular lattices, such as `E₈ ⊕ E₈`.

## Main results

* `RootPairing.card_weylGroup_of_hasCartanType_E8`: **every finite reduced crystallographic root
  system over a characteristic-zero domain with a base of Cartan type `E₈` has Weyl group of order
  `696729600`.**
* `RootPairing.card_aut_of_hasCartanType_E8`: so does its automorphism group.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §4.10 and Plate VII.
* S. Fomin and N. Reading, *Root systems and generalized associahedra*, arXiv:math/0505518v3,
  Lecture 2, §2.5, Figure 2.8.
-/

public section

namespace TauCeti.DynkinType

variable (R : Type*) [CommRing R] [IsDomain R] [CharZero R]

/-- The pinned integral root datum of type `E₈`, read entrywise in `Fin 8 → R`. -/
local notation "Q" =>
  rootPairingBaseChange R e8SimplyConnectedRootDatum e8SimplyConnectedRootDatum_toLinearMap_apply

-- The roots and coroots of the pinned `E₈` datum already span over `ℤ`, because the `E₈` Cartan
-- matrix is unimodular, so they span after any base change.
private instance : (Q).IsRootSystem where
  span_root_eq_top :=
    span_range_root_rootPairingBaseChange_eq_top R _ _ span_root_e8SimplyConnectedRootDatum_eq_top
  span_coroot_eq_top := span_range_coroot_rootPairingBaseChange_eq_top R _ _
    corootSpan_e8SimplyConnectedRootDatum_eq_top

private instance : (Q).IsReduced := isReduced_rootPairingBaseChange R _ _

end TauCeti.DynkinType

namespace RootPairing

open TauCeti TauCeti.DynkinType

variable {ι R M N : Type*} [CommRing R] [IsDomain R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base}

/-- **The Weyl group of type `E₈` has order `696729600 = 2¹⁴ · 3⁵ · 5² · 7`**: every finite
reduced crystallographic root system over a characteristic-zero domain, for instance `ℚ`, with a
base of Cartan type `E₈` has Weyl group of this order. -/
theorem card_weylGroup_of_hasCartanType_E8 (h : HasCartanType P b .E8) :
    Nat.card P.weylGroup = 696729600 := by
  obtain ⟨e⟩ := nonempty_weylGroup_mulEquiv_of_hasCartanType b _ .E8 h
    (hasCartanType_e8SimplyConnectedRootDatum.rootPairingBaseChange R _)
  rw [Nat.card_congr e.toEquiv, ← Nat.card_congr (weylGroupBaseChangeEquiv R _ _).toEquiv,
    card_weylGroup_e8SimplyConnectedRootDatum]

/-- **The automorphism group of a root system of type `E₈` has order `696729600`**: it is the
Weyl group, the `E₈` diagram having no nontrivial symmetry. -/
theorem card_aut_of_hasCartanType_E8 (h : HasCartanType P b .E8) :
    Nat.card P.Aut = 696729600 := by
  rw [← Subgroup.card_top, ← weylGroup_eq_top_of_hasCartanType_E8 h,
    card_weylGroup_of_hasCartanType_E8 h]

end RootPairing
