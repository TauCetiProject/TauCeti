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
invariant (`IsMoritaEquivalent.card_skeleton_finite_indecomposable_modules_eq`), and over a
commutative semisimple ring it is the number of maximal ideals
(`TauCeti.card_skeleton_finite_indecomposable_eq_card_maximalSpectrum`). This file computes it for
a field `k`, which has one class, and for `k × k`, which has two (the two factors). Hence `k` and
`k × k` are not Morita equivalent.
-/

open CategoryTheory

namespace TauCeti

universe u

variable (k : Type u) [Field k]

/-- *not_isMoritaEquivalent_field_prod*: over a field `k` every finitely generated indecomposable
module is isomorphic to `k`, while over `k × k` there are two of them up to isomorphism, one for
each factor. Hence `k` and `k × k` are not Morita equivalent. -/
example : Nat.card (Skeleton (ObjectProperty.FullSubcategory
      fun M : ModuleCat.{u} k ↦ Module.Finite k M ∧ Indecomposable M)) = 1 ∧
    Nat.card (Skeleton (ObjectProperty.FullSubcategory
      fun M : ModuleCat.{u} (k × k) ↦ Module.Finite (k × k) M ∧ Indecomposable M)) = 2 ∧
    ¬ IsMoritaEquivalent k k (k × k) := by
  have hk : Nat.card (Skeleton (ObjectProperty.FullSubcategory
      fun M : ModuleCat.{u} k ↦ Module.Finite k M ∧ Indecomposable M)) = 1 := by
    rw [card_skeleton_finite_indecomposable_eq_card_maximalSpectrum, Nat.card_unique]
  have hkk : Nat.card (Skeleton (ObjectProperty.FullSubcategory
      fun M : ModuleCat.{u} (k × k) ↦ Module.Finite (k × k) M ∧ Indecomposable M)) = 2 := by
    rw [card_skeleton_finite_indecomposable_eq_card_maximalSpectrum,
      ← Nat.card_congr (IsArtinianRing.primeSpectrumEquivMaximalSpectrum (R := k × k)),
      Nat.card_congr (PrimeSpectrum.primeSpectrumProd k k), Nat.card_sum, Nat.card_unique]
  refine ⟨hk, hkk, fun h ↦ ?_⟩
  have := h.card_skeleton_finite_indecomposable_modules_eq.{u, u}
  rw [hk, hkk] at this
  omega

end TauCeti
