/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Lex
import Mathlib.LinearAlgebra.Finsupp.Supported

/-!
# Injective relabeling as extension by zero

For an injective index map, pushing forward a finitely supported function is ordinary
function extension by zero, over any additive commutative monoid. For an arbitrary index map `f`,
the range of `Finsupp.mapDomain f` consists of the finitely supported functions vanishing outside
the range of `f` (`Finsupp.mem_range_mapDomain_iff'`).

Pushing forward along a strictly monotone map of linearly ordered indices preserves and reflects
the strict and non-strict lexicographic orders, since the relabeled functions vanish off the image
and the order relabels the positions where they first differ.
-/

public section

namespace Finsupp

/-- Pushing a finitely supported function along an injection extends its values by zero
outside the image. -/
theorem coe_mapDomain_eq_extend {α β M : Type*} [AddCommMonoid M]
    {e : α → β} (he : Function.Injective e) (x : α →₀ M) :
    (mapDomain e x : β → M) = Function.extend e x 0 := by
  classical
  funext j
  by_cases hj : j ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hj
    simp [he]
  · simp [mapDomain_of_notMem_range _ _ hj, Function.extend_apply' _ _ _ hj]

/-- **The range of `Finsupp.mapDomain f` for an arbitrary index map `f`** consists of the finitely
supported functions vanishing outside the range of `f`. Mathlib's `Finsupp.mem_range_mapDomain_iff`
is the case of an injective `f`; this one needs no injectivity. -/
theorem mem_range_mapDomain_iff' {α β M : Type*} [AddCommMonoid M] (f : α → β) (x : β →₀ M) :
    x ∈ Set.range (mapDomain f) ↔ ∀ b ∉ Set.range f, x b = 0 := by
  have h : LinearMap.range (lmapDomain M ℕ f) = supported M ℕ (Set.range f) := by
    simpa only [supported_univ, Submodule.map_top, Set.image_univ] using
      lmapDomain_supported M ℕ f Set.univ
  simpa only [LinearMap.mem_range, lmapDomain_apply, mem_supported', Set.mem_range] using
    SetLike.ext_iff.1 h x

/-- A finitely supported function supported on a set `s` is the push-forward along the inclusion
of its restriction to `s`. -/
theorem mapDomain_subtypeDomain_subtype {α M : Type*} [AddCommMonoid M] {s : Set α} {f : α →₀ M}
    (hf : ↑f.support ⊆ s) : (f.subtypeDomain (· ∈ s)).mapDomain Subtype.val = f := by
  classical
  have h := extendDomain_subtypeDomain f (P := (· ∈ s)) fun _ ha ↦ hf ha
  rwa [extendDomain_eq_embDomain_subtype, embDomain_eq_mapDomain] at h

/-- Pushing forward along a strictly monotone map of indices preserves and reflects the strict
lexicographic order: the first position at which two relabeled functions differ is the image of
the first position at which the original functions differ. -/
theorem toLex_mapDomain_lt_toLex_mapDomain_iff {α β M : Type*} [LinearOrder α] [Preorder β]
    [AddCommMonoid M] [Preorder M] {f : α → β} (hf : StrictMono f) {x y : α →₀ M} :
    toLex (mapDomain f x) < toLex (mapDomain f y) ↔ toLex x < toLex y := by
  simp only [Lex.lt_iff, ofLex_toLex]
  constructor
  · rintro ⟨k, hk, hlt⟩
    -- Off the image of `f` both relabeled functions vanish, so `k` is a value of `f`.
    obtain ⟨i, rfl⟩ : k ∈ Set.range f := by
      by_contra h
      simp [mapDomain_of_notMem_range _ _ h] at hlt
    refine ⟨i, fun j hj ↦ ?_, by simpa [hf.injective] using hlt⟩
    simpa [hf.injective] using hk (f j) (hf hj)
  · rintro ⟨i, hi, hlt⟩
    refine ⟨f i, fun l hl ↦ ?_, by simpa [hf.injective] using hlt⟩
    by_cases h : l ∈ Set.range f
    · obtain ⟨j, rfl⟩ := h
      simpa [hf.injective] using hi j (hf.lt_iff_lt.1 hl)
    · simp [mapDomain_of_notMem_range _ _ h]

/-- Pushing forward along a strictly monotone map of linearly ordered indices preserves and
reflects the lexicographic order. -/
theorem toLex_mapDomain_le_toLex_mapDomain_iff {α β M : Type*} [LinearOrder α] [LinearOrder β]
    [AddCommMonoid M] [PartialOrder M] {f : α → β} (hf : StrictMono f) {x y : α →₀ M} :
    toLex (mapDomain f x) ≤ toLex (mapDomain f y) ↔ toLex x ≤ toLex y := by
  simp only [le_iff_lt_or_eq, toLex_mapDomain_lt_toLex_mapDomain_iff hf, toLex_inj,
    (mapDomain_injective hf.injective).eq_iff]

end Finsupp
