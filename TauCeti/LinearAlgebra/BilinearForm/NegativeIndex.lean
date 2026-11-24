/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Otis Chodosh
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.ENat.Lattice
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Signature
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# The negative index of a bilinear form

The negative index is the supremum, in `ℕ∞`, of the dimensions of finite-dimensional subspaces
on which the diagonal of a real bilinear form is strictly negative away from zero. This
definition also applies to infinite-dimensional spaces. Restricting the admissible vectors to
a submodule gives `LinearMap.BilinForm.negativeIndexOn`. In finite dimension the index agrees
with the negative index of inertia of the associated quadratic form.

The index is monotone in the admissible submodule and commutes with increasing unions. These
facts give the algebraic part of defining the Morse index by compactly supported variations and
computing it along an exhaustion.
-/

public noncomputable section

open Module

namespace LinearMap.BilinForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The negative index of a bilinear form on an admissible submodule, allowing infinity. -/
def negativeIndexOn (B : LinearMap.BilinForm ℝ V) (S : Submodule ℝ V) : ℕ∞ :=
  ⨆ (W : Submodule ℝ V) (_ : Module.Finite ℝ W) (_ : W ≤ S)
    (_ : ∀ w ∈ W, w ≠ 0 → B w w < 0), (finrank ℝ W : ℕ∞)

/-- The negative index of a real bilinear form, allowing infinity. -/
def negativeIndex (B : LinearMap.BilinForm ℝ V) : ℕ∞ :=
  B.negativeIndexOn ⊤

variable (B : LinearMap.BilinForm ℝ V) {S T : Submodule ℝ V}

/-- The negative index is the supremum of the dimensions of its finite negative subspaces. -/
theorem negativeIndexOn_def :
    B.negativeIndexOn S =
      ⨆ (W : Submodule ℝ V) (_ : Module.Finite ℝ W) (_ : W ≤ S)
        (_ : ∀ w ∈ W, w ≠ 0 → B w w < 0), (finrank ℝ W : ℕ∞) :=
  (rfl)

/-- The negative index allows every vector as an admissible variation. -/
theorem negativeIndex_def : B.negativeIndex = B.negativeIndexOn ⊤ :=
  (rfl)

/-- An upper bound for the index is exactly an upper bound for every finite negative subspace. -/
theorem negativeIndexOn_le_iff {n : ℕ∞} :
    B.negativeIndexOn S ≤ n ↔
      ∀ (W : Submodule ℝ V) [Module.Finite ℝ W], W ≤ S →
        (∀ w ∈ W, w ≠ 0 → B w w < 0) → (finrank ℝ W : ℕ∞) ≤ n := by
  simp only [negativeIndexOn, iSup_le_iff]

/-- Every finite-dimensional negative subspace supplies a lower bound for the index. -/
theorem finrank_le_negativeIndexOn (W : Submodule ℝ V) [Module.Finite ℝ W]
    (hWS : W ≤ S) (hW : ∀ w ∈ W, w ≠ 0 → B w w < 0) :
    (finrank ℝ W : ℕ∞) ≤ B.negativeIndexOn S :=
  le_iSup_of_le W <| le_iSup_of_le ‹Module.Finite ℝ W› <|
    le_iSup_of_le hWS <| le_iSup_of_le hW le_rfl

/-- Enlarging the admissible submodule cannot decrease the negative index. -/
theorem negativeIndexOn_mono (hST : S ≤ T) :
    B.negativeIndexOn S ≤ B.negativeIndexOn T := by
  rw [negativeIndexOn_le_iff]
  intro W _ hWS hW
  exact B.finrank_le_negativeIndexOn W (hWS.trans hST) hW

/-- The negative index vanishes precisely when the diagonal is nonnegative. -/
theorem negativeIndexOn_eq_zero_iff :
    B.negativeIndexOn S = 0 ↔ ∀ v ∈ S, 0 ≤ B v v := by
  constructor
  · intro h v hv
    by_contra hn
    have hneg : B v v < 0 := lt_of_not_ge hn
    have hv0 : v ≠ 0 := by
      rintro rfl
      simp at hneg
    have hspan : ∀ w ∈ (ℝ ∙ v), w ≠ 0 → B w w < 0 := by
      intro w hw hw0
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
      have ha : a ≠ 0 := by
        rintro rfl
        simp at hw0
      rw [smul_left, smul_right, ← mul_assoc]
      exact mul_neg_of_pos_of_neg (mul_self_pos.mpr ha) hneg
    have hle := B.finrank_le_negativeIndexOn (ℝ ∙ v)
      ((Submodule.span_singleton_le_iff_mem v S).mpr hv) hspan
    rw [finrank_span_singleton hv0, h] at hle
    simp at hle
  · intro h
    apply le_antisymm _ bot_le
    rw [negativeIndexOn_le_iff]
    intro W _ hWS hW
    have hbot : W = ⊥ := by
      apply (Submodule.eq_bot_iff W).mpr
      intro w hw
      by_contra hw0
      exact (not_lt_of_ge (h w (hWS hw))) (hW w hw hw0)
    simp [hbot]

/-- The negative index vanishes precisely when the form is nonnegative on every vector. -/
theorem negativeIndex_eq_zero_iff :
    B.negativeIndex = 0 ↔ ∀ v, 0 ≤ B v v := by
  simp [negativeIndex, negativeIndexOn_eq_zero_iff]

/-- The negative index commutes with increasing unions of admissible submodules. -/
theorem negativeIndexOn_iSup_of_monotone (S : ℕ → Submodule ℝ V) (hS : Monotone S) :
    B.negativeIndexOn (⨆ n, S n) = ⨆ n, B.negativeIndexOn (S n) := by
  apply le_antisymm
  · rw [negativeIndexOn_le_iff]
    intro W _ hW hneg
    have hcompact := (Submodule.fg_iff_compact W).mp
      (Module.Finite.iff_fg.mp ‹Module.Finite ℝ W›)
    obtain ⟨_, ⟨n, rfl⟩, hn⟩ := hcompact _ _ (Set.range_nonempty S) hS.directed_le.directedOn_range
      isLUB_iSup hW
    exact le_iSup_of_le n (B.finrank_le_negativeIndexOn W hn hneg)
  · exact iSup_le fun n ↦ B.negativeIndexOn_mono (le_iSup S n)

/-- In finite dimension the extended negative index is the usual negative index of inertia. -/
theorem negativeIndex_eq_sigNeg [Module.Finite ℝ V] :
    B.negativeIndex = (sigNeg B.toQuadraticMap : ℕ∞) := by
  apply le_antisymm
  · rw [negativeIndex, negativeIndexOn_le_iff]
    intro W _ _ hW
    apply ENat.natCast_le_natCast.mpr
    apply le_sigNeg_of_negDef
    intro w hw
    simpa only [QuadraticMap.restrict_apply, _root_.neg_apply,
      LinearMap.BilinMap.toQuadraticMap_apply] using
      neg_pos.mpr (hW w w.property (by simpa using hw))
  · obtain ⟨W, hW, hneg⟩ := exists_finrank_eq_sigNeg_and_negDef B.toQuadraticMap
    rw [← hW]
    apply B.finrank_le_negativeIndexOn W le_top
    intro v hv hv0
    have h := hneg ⟨v, hv⟩ (by simpa using hv0)
    simpa only [QuadraticMap.restrict_apply, _root_.neg_apply,
      LinearMap.BilinMap.toQuadraticMap_apply, neg_pos] using h

end LinearMap.BilinForm
