/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Otis Chodosh
-/
module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Signature
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# The negative index of a bilinear form

The negative index is the supremum, in `ℕ∞`, of the dimensions of finite-dimensional subspaces
on which the diagonal of a bilinear form over a linearly ordered field is strictly negative
away from zero. This definition also applies to infinite-dimensional spaces. Restricting the
admissible vectors to a submodule gives `LinearMap.BilinForm.negativeIndexOn`. In finite dimension
the index agrees with the negative index of inertia of the associated quadratic form.

The index is monotone in the admissible submodule and commutes with directed unions. These
facts give the algebraic part of defining the Morse index by compactly supported variations and
computing it along an exhaustion.
-/

public noncomputable section

open Module

namespace LinearMap.BilinForm

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [AddCommGroup V] [Module 𝕜 V]

/-- The negative index of a bilinear form on an admissible submodule, allowing infinity. -/
def negativeIndexOn (B : LinearMap.BilinForm 𝕜 V) (S : Submodule 𝕜 V) : ℕ∞ :=
  ⨆ (W : Submodule 𝕜 V) (_ : Module.Finite 𝕜 W) (_ : W ≤ S)
    (_ : ∀ w ∈ W, w ≠ 0 → B w w < 0), (finrank 𝕜 W : ℕ∞)

/-- The negative index of a bilinear form over a linearly ordered field, allowing infinity. -/
def negativeIndex (B : LinearMap.BilinForm 𝕜 V) : ℕ∞ :=
  B.negativeIndexOn ⊤

variable (B : LinearMap.BilinForm 𝕜 V) {S T : Submodule 𝕜 V}

/-- The negative index is the supremum of the dimensions of its finite negative subspaces. -/
theorem negativeIndexOn_def :
    B.negativeIndexOn S =
      ⨆ (W : Submodule 𝕜 V) (_ : Module.Finite 𝕜 W) (_ : W ≤ S)
        (_ : ∀ w ∈ W, w ≠ 0 → B w w < 0), (finrank 𝕜 W : ℕ∞) :=
  (rfl)

/-- The negative index allows every vector as an admissible variation. -/
theorem negativeIndex_def : B.negativeIndex = B.negativeIndexOn ⊤ :=
  (rfl)

/-- An upper bound for the index is exactly an upper bound for every finite negative subspace. -/
theorem negativeIndexOn_le_iff {n : ℕ∞} :
    B.negativeIndexOn S ≤ n ↔
      ∀ (W : Submodule 𝕜 V) [Module.Finite 𝕜 W], W ≤ S →
        (∀ w ∈ W, w ≠ 0 → B w w < 0) → (finrank 𝕜 W : ℕ∞) ≤ n := by
  simp only [negativeIndexOn, iSup_le_iff]

/-- Every finite-dimensional negative subspace supplies a lower bound for the index. -/
theorem finrank_le_negativeIndexOn (W : Submodule 𝕜 V) [Module.Finite 𝕜 W]
    (hWS : W ≤ S) (hW : ∀ w ∈ W, w ≠ 0 → B w w < 0) :
    (finrank 𝕜 W : ℕ∞) ≤ B.negativeIndexOn S :=
  le_iSup_of_le W <| le_iSup_of_le ‹Module.Finite 𝕜 W› <|
    le_iSup_of_le hWS <| le_iSup_of_le hW le_rfl

/-- A finite lower bound for the index is realized by a negative subspace of that dimension. -/
theorem le_negativeIndexOn_iff {n : ℕ} :
    (n : ℕ∞) ≤ B.negativeIndexOn S ↔
      ∃ W : Submodule 𝕜 V, Module.Finite 𝕜 W ∧ W ≤ S ∧
        (∀ w ∈ W, w ≠ 0 → B w w < 0) ∧ finrank 𝕜 W = n := by
  constructor
  · intro h
    cases n with
    | zero =>
      exact ⟨⊥, inferInstance, bot_le, by simp, by simp⟩
    | succ n =>
      have hlt : (n : ℕ∞) < B.negativeIndexOn S := by
        simpa only [Nat.cast_add, Nat.cast_one, ENat.natCast_add_one_le_iff] using h
      simp only [negativeIndexOn_def, lt_iSup_iff] at hlt
      obtain ⟨W, hfin, hWS, hneg, hdim⟩ := hlt
      let := hfin
      obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank
        (Nat.succ_le_of_lt (ENat.natCast_lt_natCast.mp hdim))
      have hmap := hv.map' W.subtype (LinearMap.ker_eq_bot.mpr W.subtype_injective)
      let U := Submodule.span 𝕜 (Set.range (W.subtype ∘ v))
      have hUW : U ≤ W := Submodule.span_le.mpr (by
        rintro _ ⟨i, rfl⟩
        exact (v i).property)
      exact ⟨U, Module.Finite.span_of_finite 𝕜 (Set.finite_range _), hUW.trans hWS,
        fun w hw ↦ hneg w (hUW hw),
        by simpa [U] using finrank_span_eq_card hmap⟩
  · rintro ⟨W, hfin, hWS, hneg, rfl⟩
    exact B.finrank_le_negativeIndexOn W hWS hneg

/-- The negative index is infinite precisely when negative subspaces have every finite dimension. -/
theorem negativeIndexOn_eq_top_iff :
    B.negativeIndexOn S = ⊤ ↔
      ∀ n : ℕ, ∃ W : Submodule 𝕜 V, Module.Finite 𝕜 W ∧ W ≤ S ∧
        (∀ w ∈ W, w ≠ 0 → B w w < 0) ∧ finrank 𝕜 W = n := by
  simp only [ENat.eq_top_iff_forall_ge, le_negativeIndexOn_iff]

/-- Enlarging the admissible submodule cannot decrease the negative index. -/
theorem negativeIndexOn_mono (hST : S ≤ T) :
    B.negativeIndexOn S ≤ B.negativeIndexOn T := by
  rw [negativeIndexOn_le_iff]
  intro W _ hWS hW
  exact B.finrank_le_negativeIndexOn W (hWS.trans hST) hW

variable [IsStrictOrderedRing 𝕜]

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
    have hspan : ∀ w ∈ (𝕜 ∙ v), w ≠ 0 → B w w < 0 := by
      intro w hw hw0
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
      have ha : a ≠ 0 := by
        rintro rfl
        simp at hw0
      rw [smul_left, smul_right, ← mul_assoc]
      exact mul_neg_of_pos_of_neg (mul_self_pos.mpr ha) hneg
    have hle := B.finrank_le_negativeIndexOn (𝕜 ∙ v)
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

/-- The negative index commutes with directed unions of admissible submodules. -/
theorem negativeIndexOn_iSup_of_directed {ι : Sort*} (S : ι → Submodule 𝕜 V)
    (hS : Directed (· ≤ ·) S) :
    B.negativeIndexOn (⨆ i, S i) = ⨆ i, B.negativeIndexOn (S i) := by
  cases isEmpty_or_nonempty ι
  · simp [negativeIndexOn_eq_zero_iff]
  apply le_antisymm
  · rw [negativeIndexOn_le_iff]
    intro W _ hW hneg
    have hcompact := (Submodule.fg_iff_compact W).mp
      (Module.Finite.iff_fg.mp ‹Module.Finite 𝕜 W›)
    obtain ⟨_, ⟨n, rfl⟩, hn⟩ := hcompact _ _ (Set.range_nonempty S) hS.directedOn_range
      isLUB_iSup hW
    exact le_iSup_of_le n (B.finrank_le_negativeIndexOn W hn hneg)
  · exact iSup_le fun n ↦ B.negativeIndexOn_mono (le_iSup S n)

/-- Negativity on a submodule is positive definiteness of the restricted negative quadratic form. -/
theorem posDef_restrict_neg_toQuadraticMap_iff (W : Submodule 𝕜 V) :
    ((-B.toQuadraticMap).restrict W).PosDef ↔ ∀ w ∈ W, w ≠ 0 → B w w < 0 := by
  simp only [QuadraticMap.PosDef, QuadraticMap.restrict_apply, _root_.neg_apply,
    LinearMap.BilinMap.toQuadraticMap_apply, neg_pos, Subtype.forall,
    ne_eq, Submodule.mk_eq_zero]

/-- In finite dimension the extended negative index is the usual negative index of inertia. -/
theorem negativeIndex_eq_sigNeg [Module.Finite 𝕜 V] :
    B.negativeIndex = (sigNeg B.toQuadraticMap : ℕ∞) := by
  apply le_antisymm
  · rw [negativeIndex, negativeIndexOn_le_iff]
    intro W _ _ hW
    exact ENat.natCast_le_natCast.mpr
      (le_sigNeg_of_negDef B.toQuadraticMap ((B.posDef_restrict_neg_toQuadraticMap_iff W).mpr hW))
  · obtain ⟨W, hW, hneg⟩ := exists_finrank_eq_sigNeg_and_negDef B.toQuadraticMap
    rw [← hW]
    exact B.finrank_le_negativeIndexOn W le_top
      ((B.posDef_restrict_neg_toQuadraticMap_iff W).mp hneg)

end LinearMap.BilinForm
