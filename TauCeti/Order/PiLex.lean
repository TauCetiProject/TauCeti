/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Order.PiLex

/-!
# Upper cuts in the lexicographic order on dependent functions

Since `Pi.toLex : (∀ i, β i) → Lex (∀ i, β i)` is monotone whenever `ι` is a well-founded linear
order and each `β i` is partially ordered (`Pi.toLex_monotone`), every lexicographic upper cut
`{x ∈ s | c ≤ toLex (f x)}` decomposes into the union of the pointwise upper cuts
`{x ∈ s | v ≤ f x}` over the attained values `v ∈ f '' s` lying in `{v | c ≤ toLex v}`
(`Pi.inter_preimage_Ici_toLex_eq_biUnion`, `Pi.preimage_Ici_toLex_eq_biUnion`). When `f '' s` is
finite, this expresses each lexicographic upper cut on `s` as a finite union of pointwise upper
cuts.

## Main results

* `Pi.inter_preimage_Ici_toLex_eq_biUnion`: decomposes `s ∩ (toLex ∘ f) ⁻¹' Set.Ici c` into the
  union of `s ∩ f ⁻¹' Set.Ici v` over `v ∈ f '' s ∩ toLex ⁻¹' Set.Ici c`.
* `Pi.preimage_Ici_toLex_eq_biUnion`: global (`s = Set.univ`) version over
  `Set.range f ∩ toLex ⁻¹' Set.Ici c`.
-/

public section

namespace Pi

variable {X ι : Type*} {β : ι → Type*} [LinearOrder ι] [WellFoundedLT ι]
  [∀ i, PartialOrder (β i)]

/-- On any set `s : Set X`, a lexicographic upper cut `s ∩ (toLex ∘ f) ⁻¹' Set.Ici c` equals
the union of the pointwise upper cuts `s ∩ f ⁻¹' Set.Ici v` over all attained values
`v ∈ f '' s` satisfying `c ≤ toLex v`. -/
theorem inter_preimage_Ici_toLex_eq_biUnion (f : X → ∀ i, β i) (s : Set X)
    (c : Lex (∀ i, β i)) :
    s ∩ (toLex ∘ f) ⁻¹' Set.Ici c =
      ⋃ v ∈ f '' s ∩ toLex ⁻¹' Set.Ici c, s ∩ f ⁻¹' Set.Ici v := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, Function.comp_apply, Set.mem_Ici,
    Set.mem_iUnion, Set.mem_image, exists_prop]
  refine ⟨fun ⟨hx, hcx⟩ ↦ ⟨f x, ⟨⟨x, hx, rfl⟩, hcx⟩, hx, le_rfl⟩, ?_⟩
  rintro ⟨v, ⟨_, hcv⟩, hx, hvx⟩
  exact ⟨hx, hcv.trans (toLex_monotone hvx)⟩

/-- A lexicographic upper cut `(toLex ∘ f) ⁻¹' Set.Ici c` equals the union of the pointwise upper
cuts `f ⁻¹' Set.Ici v` over all attained values `v ∈ Set.range f` satisfying `c ≤ toLex v`. -/
theorem preimage_Ici_toLex_eq_biUnion (f : X → ∀ i, β i) (c : Lex (∀ i, β i)) :
    (toLex ∘ f) ⁻¹' Set.Ici c =
      ⋃ v ∈ Set.range f ∩ toLex ⁻¹' Set.Ici c, f ⁻¹' Set.Ici v := by
  simpa using inter_preimage_Ici_toLex_eq_biUnion f Set.univ c

end Pi
