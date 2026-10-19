/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.BackAndForth.ExtensionPair
public import TauCeti.ModelTheory.Scott.Rank

/-!
# Internal Scott rank of structures with the self-extension property

If every finitely generated partial automorphism of a relational structure `M` extends to any
given element, that is `Language.IsExtensionPair M M`, then two tuples of `M` with the same atomic
type are back-and-forth equivalent at every level. Hence `M` stabilizes internally at zero, every
tuple has orbit rank zero, and the internal Scott rank of `M` is one, the least possible value.

For countably generated structures the hypothesis is ultrahomogeneity (Mathlib's
`isUltrahomogeneous_iff_IsExtensionPair`); it also holds for dense linear orders without endpoints
of every cardinality. No countability is assumed.
-/

public section

universe u v w o

namespace FirstOrder.Language.IsExtensionPair

open TauCeti

variable {L : Language.{u, v}} [L.IsRelational] {M : Type w} [L.Structure M]

/-- A structure with the self-extension property stabilizes internally at zero. -/
theorem selfStabilizesCompletely_zero (h : L.IsExtensionPair M M) :
    SelfStabilizesCompletely (L := L) M (0 : Ordinal.{o}) :=
  (selfStabilizesCompletely_def M 0).mpr fun _ _ _ =>
    ⟨fun hab => (BFEquiv.zero.mp hab).bfEquiv_of_isExtensionPair h h _,
      fun hab => hab.mono le_self_add⟩

/-- The least internal stabilization ordinal of a structure with the self-extension property is
zero. -/
theorem selfStabilizationOrdinal_eq_zero (h : L.IsExtensionPair M M) :
    selfStabilizationOrdinal (L := L) M = 0 :=
  le_antisymm (selfStabilizationOrdinal_le M h.selfStabilizesCompletely_zero) bot_le

/-- Every finite tuple of a structure with the self-extension property has orbit rank zero. -/
theorem orbitRank_eq_zero (h : L.IsExtensionPair M M) {n : ℕ} (a : Fin n → M) :
    orbitRank (L := L) a = 0 :=
  le_antisymm (h.selfStabilizationOrdinal_eq_zero ▸ orbitRank_le_selfStabilizationOrdinal a)
    bot_le

/-- A structure with the self-extension property has internal Scott rank one. -/
theorem internalScottRank_eq_one (h : L.IsExtensionPair M M) :
    internalScottRank (L := L) M = 1 := by
  apply le_antisymm _ one_le_internalScottRank
  simp [h.orbitRank_eq_zero]

end FirstOrder.Language.IsExtensionPair
