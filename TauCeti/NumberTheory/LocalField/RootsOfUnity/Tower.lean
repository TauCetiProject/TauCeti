/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.RootsOfUnity.Basic
public import TauCeti.RingTheory.RootsOfUnity.Map

/-!
# Root-of-unity orders in field extensions

The `p`-power root group of a field embeds in that of every extension, so its finite order
divides the order in the extension. A field isomorphism preserves the order exactly. These
facts compare the invariant `localRootOfUnityOrder` through towers of local fields.
-/

public section

namespace TauCeti

variable (p : ℕ)
variable {K L : Type*} [CommMonoid K] [CommMonoid L]

/-- An injective monoid map preserves the order of each root, so the finite root-group
order of its source divides the order in its target. -/
theorem localRootOfUnityOrder_dvd_of_injective (f : K →* L)
    (hf : Function.Injective f)
    (hK : Finite (pPowerRootsOfUnity p K))
    (hL : Finite (pPowerRootsOfUnity p L)) :
    localRootOfUnityOrder p K hK ∣ localRootOfUnityOrder p L hL := by
  let _ := hK
  let _ := hL
  simpa only [localRootOfUnityOrder_def] using
    Subgroup.card_dvd_of_injective (pPowerRootsOfUnityMap p f)
      (pPowerRootsOfUnityMap_injective p f hf)

/-- The `p`-power root order of a field divides that of every extension field. -/
theorem localRootOfUnityOrder_dvd_of_fieldHom {F E : Type*} [Field F] [Field E]
    (f : F →+* E) (hF : Finite (pPowerRootsOfUnity p F))
    (hE : Finite (pPowerRootsOfUnity p E)) :
    localRootOfUnityOrder p F hF ∣ localRootOfUnityOrder p E hE :=
  localRootOfUnityOrder_dvd_of_injective p f.toMonoidHom f.injective hF hE

/-- A field isomorphism preserves the order of the finite `p`-power root group. -/
theorem localRootOfUnityOrder_eq_of_ringEquiv {F E : Type*} [Field F] [Field E]
    (f : F ≃+* E) (hF : Finite (pPowerRootsOfUnity p F))
    (hE : Finite (pPowerRootsOfUnity p E)) :
    localRootOfUnityOrder p F hF = localRootOfUnityOrder p E hE := by
  let _ := hF
  let _ := hE
  simpa only [localRootOfUnityOrder_def] using
    Nat.card_congr (pPowerRootsOfUnityEquiv p f.toMulEquiv).toEquiv

end TauCeti
