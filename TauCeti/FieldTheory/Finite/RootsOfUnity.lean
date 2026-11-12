/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import TauCeti.RingTheory.RootsOfUnity.Finite

/-!
# Roots of unity of order dividing `q - 1` in a finite field

The unit group of a finite field `F` with `q` elements consists of the `(q - 1)`-st roots of unity
(`TauCeti.rootsOfUnity_natCard_sub_one_eq_top`), and there are `q - 1` of them, so `F` has enough
roots of unity of order `q - 1`, and hence of every order `d ∣ q - 1`. In particular `F` contains a
primitive `d`-th root of unity for every such `d`.

Mathlib has the case `d = p - 1` of the prime field `ZMod p`, as the instance
`HasEnoughRootsOfUnity (ZMod p) (p - 1)` of `Mathlib.RingTheory.ZMod.Torsion`.

## Main results

* `TauCeti.hasEnoughRootsOfUnity_of_dvd_natCard_sub_one`: a finite field with `q` elements has
  enough roots of unity of every order dividing `q - 1`.
* `TauCeti.exists_isPrimitiveRoot_of_dvd_natCard_sub_one`: hence a primitive `d`-th root of unity
  for every such `d`.
-/

public section

namespace TauCeti

variable {F : Type*} [Field F] [Finite F] {d : ℕ}

/-- **A finite field with `q` elements has enough roots of unity of every order dividing
`q - 1`.** -/
theorem hasEnoughRootsOfUnity_of_dvd_natCard_sub_one (hd : d ∣ Nat.card F - 1) :
    HasEnoughRootsOfUnity F d := by
  have : NeZero (Nat.card F - 1) := ⟨Nat.card_units F ▸ Nat.card_pos.ne'⟩
  have : HasEnoughRootsOfUnity F (Nat.card F - 1) := .of_card_le <| by
    rw [Nat.card_congr (rootsOfUnityEquivUnits F).toEquiv, Nat.card_units]
  exact .of_dvd F hd

/-- **A finite field with `q` elements contains a primitive `d`-th root of unity for every `d`
dividing `q - 1`.** -/
theorem exists_isPrimitiveRoot_of_dvd_natCard_sub_one (hd : d ∣ Nat.card F - 1) :
    ∃ ζ : F, IsPrimitiveRoot ζ d :=
  have := hasEnoughRootsOfUnity_of_dvd_natCard_sub_one hd
  HasEnoughRootsOfUnity.exists_isPrimitiveRoot F d

end TauCeti
