/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.Algebra.Group.Action.Basic

/-!
# Scalar towers through a localization of commutative monoids

Let `f : M.LocalizationMap N` exhibit the commutative monoid `N` as a localization of `C` at a
submonoid `M`. Suppose that `N` acts by monoid actions on types `S` and `E`, and that `S` acts on
`E`. This file shows that compatibility of these actions on the image of `C` extends to all of
`N`: if `(f c • s) • e = f c • (s • e)` for every `c : C`, then `IsScalarTower N S E`. For
localizations of commutative semirings, this gives
`IsLocalization.isScalarTower_of_isScalarTower` in `TauCeti.RingTheory.Localization.Defs`.

## Main results

* `Submonoid.LocalizationMap.isScalarTower`: if `(f c • s) • e = f c • (s • e)` for all `c : C`,
  `s : S` and `e : E`, then `IsScalarTower N S E`.
-/

public section

namespace Submonoid.LocalizationMap

/-- **Scalar towers through a localization.** Let `f : M.LocalizationMap N` exhibit `N` as a
localization of `C` at `M`, let `N` act on `S` and on `E` by monoid actions, and let `S` act on
`E`. If `(f c • s) • e = f c • (s • e)` for all `c : C`, `s : S` and `e : E`, then
`IsScalarTower N S E`. -/
theorem isScalarTower {C N S E : Type*} [CommMonoid C] [CommMonoid N] {M : Submonoid C}
    (f : M.LocalizationMap N) [MulAction N S] [MulAction N E] [SMul S E]
    (h : ∀ (c : C) (s : S) (e : E), (f c • s) • e = f c • s • e) :
    IsScalarTower N S E := by
  refine ⟨fun r s e ↦ ?_⟩
  -- Write `r = c / m`; since `f m` acts invertibly on `E`, compare both sides after acting by it.
  obtain ⟨⟨c, m⟩, hr⟩ := f.surj r
  have hmr : f m * r = f c := by rw [mul_comm, hr]
  rw [← (f.map_units m).smul_left_cancel, ← h m (r • s) e, smul_smul, smul_smul, hmr, h]

end Submonoid.LocalizationMap
