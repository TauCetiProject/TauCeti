/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import Mathlib.Algebra.Module.SpanRank
import Mathlib.Data.Fintype.EquivFin

/-!
# Generating families of a prescribed length

For a finitely generated submodule, its least number of generators is at most `n` exactly
when it has a generating family indexed by `Fin n`. A minimum generating finset can be
embedded in `Fin n`, with zero at the unused indices. This includes the zero submodule
and the empty family.
-/

public section

namespace Submodule

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- A finitely generated submodule has at most `n` generators exactly when it is spanned
by a family of length `n`. Zero entries may pad a shorter generating family. -/
theorem FG.spanFinrank_le_iff_exists_fin_generating_family {p : Submodule R M}
    (hp : p.FG) (n : ℕ) :
    p.spanFinrank ≤ n ↔ ∃ f : Fin n → M, span R (Set.range f) = p := by
  classical
  constructor
  · intro hn
    obtain ⟨s, hs, hspan⟩ := hp.exists_span_finset_card_eq_spanFinrank
    let e : s ↪ Fin n := s.equivFin.toEmbedding.trans
      ⟨Fin.castLE (hs.trans_le hn), Fin.castLE_injective _⟩
    let f : Fin n → M := Function.extend e Subtype.val (fun _ ↦ 0)
    refine ⟨f, le_antisymm ?_ ?_⟩
    · apply span_le.mpr
      rintro x ⟨i, rfl⟩
      dsimp [f]
      rw [Function.extend_def]
      split_ifs with hi
      · exact hspan ▸ subset_span (Classical.choose hi).property
      · exact p.zero_mem
    · rw [← hspan]
      apply span_mono
      intro x hx
      refine ⟨e ⟨x, hx⟩, ?_⟩
      exact e.injective.extend_apply Subtype.val (fun _ ↦ 0) ⟨x, hx⟩
  · rintro ⟨f, rfl⟩
    exact (spanFinrank_span_le_ncard_of_finite (Set.finite_range f)).trans
      (by simpa using (Set.ncard_image_le (f := f) (s := Set.univ)))

end Submodule
