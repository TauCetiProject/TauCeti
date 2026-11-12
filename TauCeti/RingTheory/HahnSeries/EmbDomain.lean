/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HahnSeries.Basic

/-!
# Support, range and composition of `HahnSeries.embDomain`

Extending the domain of a Hahn series along an order embedding `f : Γ ↪o Γ'` moves each
coefficient from `g` to `f g`. Mathlib records that the support of `embDomain f x` is contained in
the image of the support of `x`. This file records that it is equal to that image, that a Hahn
series on `Γ'` lies in the range of `embDomain f` exactly when its support lies in the range of
`f`, and that extending along two embeddings in turn is extending along their composite.

These are the facts used to identify the image of a Laurent series under a change of exponent
group, such as `X ↦ X ^ d` on `ℤ`, or `ℤ → ℚ, k ↦ k / n` into rational exponents. The range
characterization has the shape of the `HahnSeries.mem_range_embDomain_iff` proposed for Mathlib in
mathlib4 PR #42313.

## Main results

* `HahnSeries.support_embDomain`: `(embDomain f x).support = f '' x.support`.
* `HahnSeries.mem_range_embDomain_iff`: `x ∈ Set.range (embDomain f) ↔ x.support ⊆ Set.range f`.
* `HahnSeries.embDomain_embDomain`: `embDomain g (embDomain f x) = embDomain (f.trans g) x`.
-/

public section

namespace HahnSeries

variable {Γ Γ' Γ'' R : Type*} [PartialOrder Γ] [PartialOrder Γ'] [PartialOrder Γ''] [Zero R]

/-- The support of `embDomain f x` is the image of the support of `x`. -/
@[simp]
theorem support_embDomain (f : Γ ↪o Γ') (x : HahnSeries Γ R) :
    (embDomain f x).support = f '' x.support := by
  refine support_embDomain_subset.antisymm ?_
  rintro _ ⟨g, hg, rfl⟩
  simpa using hg

/-- A Hahn series lies in the range of `embDomain f` exactly when its support lies in the range
of `f`. -/
theorem mem_range_embDomain_iff {f : Γ ↪o Γ'} {x : HahnSeries Γ' R} :
    x ∈ Set.range (embDomain f) ↔ x.support ⊆ Set.range f := by
  refine ⟨?_, fun hx ↦ ?_⟩
  · rintro ⟨y, rfl⟩
    rw [support_embDomain]
    exact Set.image_subset_range _ _
  have hpwo : (f ⁻¹' x.support).IsPWO := by
    rw [Set.IsPWO, Set.partiallyWellOrderedOn_iff_exists_lt]
    intro s hs
    obtain ⟨m, n, hmn, hle⟩ := x.isPWO_support.exists_lt (f := f ∘ s) hs
    exact ⟨m, n, hmn, f.le_iff_le.mp hle⟩
  refine ⟨⟨fun g ↦ x.coeff (f g), hpwo⟩, ?_⟩
  ext b
  by_cases hb : b ∈ Set.range f
  · obtain ⟨g, rfl⟩ := hb
    exact embDomain_coeff
  · rw [embDomain_of_notMem_range hb]
    by_contra h
    exact hb (hx (Ne.symm h))

/-- Extending the domain along `f` and then along `g` is extending it along `f.trans g`. -/
theorem embDomain_embDomain (f : Γ ↪o Γ') (g : Γ' ↪o Γ'') (x : HahnSeries Γ R) :
    embDomain g (embDomain f x) = embDomain (f.trans g) x := by
  ext c
  by_cases hc : c ∈ Set.range (f.trans g)
  · obtain ⟨a, rfl⟩ := hc
    rw [RelEmbedding.trans_apply, embDomain_coeff, embDomain_coeff, ← RelEmbedding.trans_apply,
      embDomain_coeff]
  · rw [embDomain_of_notMem_range hc]
    by_cases hc' : c ∈ Set.range g
    · obtain ⟨b, rfl⟩ := hc'
      rw [embDomain_coeff, embDomain_of_notMem_range]
      rintro ⟨a, rfl⟩
      exact hc ⟨a, rfl⟩
    · exact embDomain_of_notMem_range hc'

end HahnSeries
