/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.SetTheory.Cardinal.Finite
public import TauCeti.RingTheory.FittingIdeal.Generators

/-!
# Minors ideals and generating families

Let `F` be a module over a commutative ring `R`. This file relates the ideals of minors
`Submodule.minorsIdeal` to explicit generating families:

* If a submodule is contained in the span of fewer than `p` vectors, its `p × p` minors ideal
  vanishes (`Submodule.minorsIdeal_eq_bot_of_le_span_range`), since every minor formed from those
  generators repeats a row.
* Adjoining a single generator `x` to a submodule `N` shifts its minors ideals by at most one:
  `(N ⊔ R ∙ x).minorsIdeal (p + 1) ≤ N.minorsIdeal p`
  (`Submodule.minorsIdeal_sup_span_singleton_succ_le`). Inductively, adjoining a finite family of
  generators shifts the minors ideals by at most the size of the family
  (`Submodule.minorsIdeal_sup_span_range_add_le`).

## Main results

* `Submodule.minorsIdeal_span_range_eq_bot_of_lt`: the `p × p` minors ideal of the span of fewer
  than `p` vectors vanishes.
* `Submodule.minorsIdeal_eq_bot_of_le_span_range`: the `p × p` minors ideal of a submodule
  contained in the span of fewer than `p` vectors vanishes.
* `Submodule.minorsIdeal_sup_span_singleton_succ_le`: adjoining one generator shifts the minors
  ideals by at most one.
* `Submodule.minorsIdeal_sup_span_range_add_le`: adjoining a finite family of `m` generators shifts
  the minors ideals by at most `m`.

## References

* [Stacks Project, Tag 07Z6](https://stacks.math.columbia.edu/tag/07Z6)
-/

public section

open Module

namespace Submodule

variable {R F : Type*} [CommRing R] [AddCommGroup F] [Module R F]

/-- The `p × p` minors ideal of the span of fewer than `p` vectors vanishes: any `p` vectors chosen
from the generating family must repeat a generator, so the corresponding determinant has two equal
rows. -/
theorem minorsIdeal_span_range_eq_bot_of_lt {ι : Type*} [Finite ι] {p : ℕ}
    (h : Nat.card ι < p) (v : ι → F) :
    (Submodule.span R (Set.range v)).minorsIdeal p = ⊥ := by
  cases nonempty_fintype ι
  rw [Nat.card_eq_fintype_card] at h
  rw [minorsIdeal_span, TauCeti.minorsIdealOfSet_def, Ideal.span_eq_bot]
  rintro _ ⟨f, w, hw, rfl⟩
  choose g hg using hw
  obtain ⟨i, j, hij, hgij⟩ := Fintype.exists_ne_map_eq_of_card_lt g (by simpa using h)
  exact Matrix.det_zero_of_row_eq hij <| funext fun k ↦ by simp [← hg i, ← hg j, hgij]

/-- If a submodule `N` is contained in the span of fewer than `p` vectors, its `p × p` minors ideal
vanishes. -/
theorem minorsIdeal_eq_bot_of_le_span_range {ι : Type*} [Finite ι] {N : Submodule R F} {p : ℕ}
    {v : ι → F} (hN : N ≤ Submodule.span R (Set.range v)) (hp : Nat.card ι < p) :
    N.minorsIdeal p = ⊥ :=
  le_bot_iff.mp <| (minorsIdeal_mono hN p).trans_eq (minorsIdeal_span_range_eq_bot_of_lt hp v)

/-- Adjoining a single generator `x` to a submodule `N` shifts its minors ideals by at most one:
every `(p + 1) × (p + 1)` minor of `N ⊔ R ∙ x` lies in `N.minorsIdeal p`. -/
theorem minorsIdeal_sup_span_singleton_succ_le (N : Submodule R F) (x : F) (p : ℕ) :
    (N ⊔ R ∙ x).minorsIdeal (p + 1) ≤ N.minorsIdeal p := by
  have hspan : N ⊔ R ∙ x = Submodule.span R (insert x (N : Set F)) := by
    rw [span_insert, span_eq, sup_comm]
  rw [hspan, minorsIdeal_span, TauCeti.minorsIdealOfSet_def, Ideal.span_le]
  rintro _ ⟨f, w, hw, rfl⟩
  by_cases h : ∃ i₀, w i₀ = x
  · obtain ⟨i₀, hi₀⟩ := h
    by_cases h' : ∃ i, i ≠ i₀ ∧ w i = x
    · obtain ⟨i, hi, hwi⟩ := h'
      rw [Matrix.det_zero_of_row_eq hi (funext fun _ ↦ by simp [hwi, hi₀])]
      exact zero_mem _
    · push Not at h'
      rw [Matrix.det_succ_row _ i₀]
      refine sum_mem fun j _ ↦ Ideal.mul_mem_left _ _ <|
        det_mem_minorsIdeal (fun k ↦ f (j.succAbove k)) fun k ↦
          (hw (i₀.succAbove k)).resolve_left (h' _ (Fin.succAbove_ne i₀ k))
  · push Not at h
    exact N.minorsIdeal_succ_le p <| det_mem_minorsIdeal f fun i ↦ (hw i).resolve_left (h i)

private theorem minorsIdeal_sup_span_range_fin_add_le :
    ∀ {m : ℕ} (N : Submodule R F) (v : Fin m → F) (p : ℕ),
      (N ⊔ Submodule.span R (Set.range v)).minorsIdeal (p + m) ≤ N.minorsIdeal p
  | 0, N, v, p => by simp [Set.range_eq_empty]
  | m + 1, N, v, p => by
    have hrange : Set.range v = insert (v 0) (Set.range (v ∘ Fin.succ)) := by
      ext y; simp [Fin.exists_fin_succ, @eq_comm _ (v 0)]
    have hsup : N ⊔ Submodule.span R (Set.range v) =
        (N ⊔ R ∙ v 0) ⊔ Submodule.span R (Set.range (v ∘ Fin.succ)) := by
      rw [hrange, span_insert, sup_assoc, sup_comm (R ∙ v 0), ← sup_assoc]
    rw [hsup, show p + (m + 1) = (p + 1) + m by omega]
    exact (minorsIdeal_sup_span_range_fin_add_le (N ⊔ R ∙ v 0) (v ∘ Fin.succ) (p + 1)).trans
      (minorsIdeal_sup_span_singleton_succ_le N (v 0) p)

/-- Adjoining a finite family `v : ι → F` of generators to a submodule `N` shifts its minors ideals
by at most `Nat.card ι`. -/
theorem minorsIdeal_sup_span_range_add_le {ι : Type*} [Finite ι] (N : Submodule R F) (v : ι → F)
    (p : ℕ) :
    (N ⊔ Submodule.span R (Set.range v)).minorsIdeal (p + Nat.card ι) ≤ N.minorsIdeal p := by
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  rw [(Nat.card_congr e).trans (Nat.card_fin m), ← e.symm.surjective.range_comp v]
  exact minorsIdeal_sup_span_range_fin_add_le N (v ∘ e.symm) p

end Submodule
