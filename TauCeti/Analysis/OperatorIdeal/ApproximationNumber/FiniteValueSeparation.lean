/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Uniform separation for a finite positive family

A finite family of positive real numbers admits one positive radius that is
smaller than every value, smaller than a prescribed tolerance, and separates
all distinct values.  This is the elementary finite ingredient used to make
Gram spectral bands pairwise disjoint.

The tolerance is written `ε / 16` because the consumer needs room for four
halvings; no significance attaches to the constant beyond that.

## Provenance

* Original module: authored for the Davis--Kahan tan-2-theta development, then
  moved here once its dependencies were measured: the two statements are about
  finite families of reals and use nothing but Mathlib.
* Extraction class: **moved and renamespaced.**  Statements and proofs are
  unchanged; only the enclosing namespace and the import list moved.
* Original authors / copyright: Jon Crall, OpenAI GPT-5.6 Thinking;
  Copyright (c) 2026 Kitware, Inc.; Apache 2.0.
* Spectra influence: **none.**
-/

public section

namespace TauCeti
namespace ApproximationNumber

noncomputable section

/-- A finite family of strictly positive reals has a common positive strict
lower bound. -/
theorem exists_pos_lt_all_finset
    {α : Type*} (s : Finset α) (f : α → ℝ)
    (hf : ∀ i ∈ s, 0 < f i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ s, δ < f i := by
  classical
  by_cases hs : s.Nonempty
  · let t : Finset ℝ := s.image f
    have ht : t.Nonempty := Finset.image_nonempty.mpr hs
    let m : ℝ := t.min' ht
    have hm_mem : m ∈ t := by
      exact t.min'_mem ht
    obtain ⟨i, hi, hfi⟩ := Finset.mem_image.mp hm_mem
    have hm0 : 0 < m := by
      rw [← hfi]
      exact hf i hi
    refine ⟨m / 2, by linarith, ?_⟩
    intro i hi
    have hfi_mem : f i ∈ t := Finset.mem_image.mpr ⟨i, hi, rfl⟩
    have hm_le : m ≤ f i := by
      simpa [m] using t.min'_le (f i) hfi_mem
    linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro i hi
    exact False.elim (hs ⟨i, hi⟩)

/-- Uniform radius for finitely many positive values.  Distinct values have
pairwise disjoint closed radius-`η` intervals. -/
theorem exists_uniform_positive_separation
    {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ,
      0 < η ∧
      η < ε / 16 ∧
      (∀ i, η < a i) ∧
      ∀ i j, a i ≠ a j → 2 * η < |a i - a j| := by
  classical
  let pairs : Finset (Fin n × Fin n) :=
    (Finset.univ.product Finset.univ).filter fun ij => a ij.1 ≠ a ij.2
  have hpairs : ∀ ij ∈ pairs, 0 < |a ij.1 - a ij.2| / 2 := by
    intro ij hij
    have hne : a ij.1 ≠ a ij.2 := (Finset.mem_filter.mp hij).2
    have habs : 0 < |a ij.1 - a ij.2| := abs_pos.mpr (sub_ne_zero.mpr hne)
    positivity
  obtain ⟨δp, hδp0, hδp⟩ :=
    exists_pos_lt_all_finset pairs (fun ij => |a ij.1 - a ij.2| / 2) hpairs
  obtain ⟨δv, hδv0, hδv⟩ :=
    exists_pos_lt_all_finset Finset.univ a (by
      intro i _
      exact ha i)
  let η : ℝ := min (ε / 16) (min δv δp) / 2
  have hε16 : 0 < ε / 16 := by positivity
  have hη0 : 0 < η := by
    dsimp only [η]
    positivity
  refine ⟨η, hη0, ?_, ?_, ?_⟩
  · have hmin : min (ε / 16) (min δv δp) ≤ ε / 16 := min_le_left _ _
    dsimp only [η]
    nlinarith
  · intro i
    have hmin1 : min (ε / 16) (min δv δp) ≤ min δv δp := min_le_right _ _
    have hmin2 : min δv δp ≤ δv := min_le_left _ _
    have hlt : δv < a i := hδv i (Finset.mem_univ i)
    dsimp only [η]
    nlinarith
  · intro i j hij
    have hp : (i, j) ∈ pairs := by
      apply Finset.mem_filter.mpr
      refine ⟨?_, hij⟩
      exact Finset.mem_product.mpr ⟨Finset.mem_univ i, Finset.mem_univ j⟩
    have hgap : δp < |a i - a j| / 2 := hδp (i, j) hp
    have hmin1 : min (ε / 16) (min δv δp) ≤ min δv δp := min_le_right _ _
    have hmin2 : min δv δp ≤ δp := min_le_right _ _
    dsimp only [η]
    nlinarith

end

end ApproximationNumber
end TauCeti
