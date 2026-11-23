/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic

/-!
# Signs act trivially on `ZMod 2`-modules

In a `ZMod 2`-module every element is its own negative (`ZModModule.neg_eq_self`), so every sign
`(-1)ʳ` acts as the identity. This is what makes the Koszul signs `(-1)ᵖ` in the differential of
a tensor product of complexes disappear with mod-two coefficients; the hom-groups of
`ModuleCat (ZMod 2)` are `ZMod 2`-modules, so it applies to morphisms there as well as to
elements.

## Main results

* `TauCeti.ZModModule.neg_one_pow_zsmul`: `(-1)ʳ • x = x` in a `ZMod 2`-module.
-/

public section

namespace TauCeti.ZModModule

/-- In a `ZMod 2`-module, every sign `(-1)ʳ` acts as the identity. -/
theorem neg_one_pow_zsmul {G : Type*} [AddCommGroup G] [Module (ZMod 2) G] (x : G) (r : ℕ) :
    ((-1 : ℤ) ^ r) • x = x := by
  simp [← Int.cast_smul_eq_zsmul (ZMod 2)]

end TauCeti.ZModModule
