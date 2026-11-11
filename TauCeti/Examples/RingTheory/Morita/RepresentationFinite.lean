/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Spectrum.Prime.Basic
import TauCeti.RingTheory.Morita.RepresentationFinite

/-!
# Tests: counting indecomposable modules distinguishes `k` from `k × k`

The number of isomorphism classes of finitely generated indecomposable modules is a Morita
invariant (`IsMoritaEquivalent.card_skeleton_indecomposable_eq`), and over a commutative semisimple
ring it is the number of maximal ideals
(`TauCeti.card_skeleton_indecomposable_eq_card_maximalSpectrum`). This file computes it for a field
`k`, which has one class, and for `k × k`, which has two (the two factors). Hence `k` and `k × k`
are not Morita equivalent.
-/

open CategoryTheory

namespace TauCeti

universe u

variable (k : Type u) [Field k]

/-- *card_skeleton_indecomposable_field*: over a field, every finitely generated indecomposable
module is isomorphic to the field itself. -/
example : Nat.card (Skeleton (ObjectProperty.FullSubcategory
    fun M : ModuleCat.{u} k ↦ Module.Finite k M ∧ Indecomposable M)) = 1 := by
  rw [card_skeleton_indecomposable_eq_card_maximalSpectrum, Nat.card_unique]

/-- *card_skeleton_indecomposable_prod*: over `k × k` there are exactly two finitely generated
indecomposable modules up to isomorphism, one for each factor. -/
example : Nat.card (Skeleton (ObjectProperty.FullSubcategory
    fun M : ModuleCat.{u} (k × k) ↦ Module.Finite (k × k) M ∧ Indecomposable M)) = 2 := by
  rw [card_skeleton_indecomposable_eq_card_maximalSpectrum,
    ← Nat.card_congr (IsArtinianRing.primeSpectrumEquivMaximalSpectrum (R := k × k)),
    Nat.card_congr (PrimeSpectrum.primeSpectrumProd k k), Nat.card_sum, Nat.card_unique]

/-- *not_isMoritaEquivalent_field_prod*: `k` and `k × k` are not Morita equivalent, since they have
different numbers of finitely generated indecomposable modules. -/
example : ¬ IsMoritaEquivalent k k (k × k) := fun h ↦ by
  have := h.card_skeleton_indecomposable_eq.{u}
  rw [card_skeleton_indecomposable_eq_card_maximalSpectrum,
    card_skeleton_indecomposable_eq_card_maximalSpectrum, Nat.card_unique,
    ← Nat.card_congr (IsArtinianRing.primeSpectrumEquivMaximalSpectrum (R := k × k)),
    Nat.card_congr (PrimeSpectrum.primeSpectrumProd k k), Nat.card_sum, Nat.card_unique] at this
  omega

end TauCeti
