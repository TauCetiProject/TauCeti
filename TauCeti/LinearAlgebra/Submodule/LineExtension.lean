/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Extending a subspace by a line

For a subspace `W` of a real vector space `F`, a `Submodule.LineExtension W` is a subspace
`W' = W ⊕ ℝv` of one more dimension, together with a functional `φ` cutting out `W` inside `W'`
and normalised by `φ v = 1`. Every proper subspace of a finite-dimensional space admits one
(`Submodule.nonempty_lineExtension`); `Submodule.lineExtension` is a chosen one.

The complements of the two closed half-subspaces `{x ∈ W' | φ x ≤ 0}` and `{x ∈ W' | 0 ≤ φ x}`
cover the complement of `W` (`Submodule.LineExtension.compl_union_compl`) and intersect in the
complement of `W'` (`Submodule.LineExtension.compl_inter_compl`). Each of them is star-convex,
about `v` and `-v` respectively (`TauCeti.starConvex_compl_setOf_mem_and_nonpos`), which is what
lets a Mayer–Vietoris argument remove one dimension of `W'` at a time in relative homology
computations modulo the complement of a subspace.
-/

public section

open Module

namespace Submodule

variable {F : Type*} [AddCommGroup F] [Module ℝ F]

/-- An extension of a subspace `W` by a line: a subspace `W'` containing `W` with one more
dimension, together with a functional `φ` cutting out `W` in `W'` and a vector `v ∈ W'` with
`φ v = 1`. -/
structure LineExtension (W : Submodule ℝ F) where
  /-- The larger subspace. -/
  W' : Submodule ℝ F
  /-- The functional cutting out `W` inside `W'`. -/
  φ : F →ₗ[ℝ] ℝ
  /-- The vector of `W'` on which `φ` is one. -/
  v : F
  v_mem : v ∈ W'
  apply_v : φ v = 1
  le : W ≤ W'
  apply_eq_zero : ∀ x ∈ W, φ x = 0
  mem_of_apply_eq_zero : ∀ x ∈ W', φ x = 0 → x ∈ W
  finrank_eq : finrank ℝ W' = finrank ℝ W + 1

/-- Every proper subspace of a finite-dimensional space admits an extension by a line. -/
lemma nonempty_lineExtension [FiniteDimensional ℝ F] {W : Submodule ℝ F} (hW : W ≠ ⊤) :
    Nonempty (LineExtension W) := by
  obtain ⟨v, hv⟩ : ∃ v, v ∉ W := by
    by_contra! h
    exact hW (eq_top_iff.2 fun x _ ↦ h x)
  obtain ⟨f, hfv, hfW⟩ := W.exists_dual_map_eq_bot_of_notMem hv inferInstance
  replace hfW : ∀ x ∈ W, f x = 0 := fun x hx ↦
    (Submodule.mem_bot ℝ).1 (hfW ▸ Submodule.mem_map_of_mem hx)
  refine ⟨⟨W ⊔ ℝ ∙ v, (f v)⁻¹ • f, v,
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self v), ?_, le_sup_left,
    fun x hx ↦ ?_, fun x hx hφx ↦ ?_, ?_⟩⟩
  · simp [inv_mul_cancel₀ hfv]
  · simp [hfW x hx]
  · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
    have ha : a = 0 := by simpa [hfW y hy, hfv] using hφx
    simpa [ha] using hy
  · exact Submodule.finrank_sup_span_singleton hv

/-- A chosen extension of a proper subspace by a line. -/
noncomputable def lineExtension [FiniteDimensional ℝ F] (W : Submodule ℝ F) (hW : W ≠ ⊤) :
    LineExtension W :=
  (nonempty_lineExtension hW).some

namespace LineExtension

variable {W : Submodule ℝ F} (s : LineExtension W)

/-- The complements of the two closed half-subspaces `{x ∈ W' | ±φ x ≤ 0}` of an extension by a
line cover the complement of `W`. -/
lemma compl_union_compl :
    {x | x ∈ s.W' ∧ s.φ x ≤ 0}ᶜ ∪ {x | x ∈ s.W' ∧ (-s.φ) x ≤ 0}ᶜ = (W : Set F)ᶜ := by
  ext x
  simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq, LinearMap.neg_apply, neg_nonpos,
    SetLike.mem_coe]
  constructor
  · rintro (h | h) hx <;> exact h ⟨s.le hx, by simp [s.apply_eq_zero _ hx]⟩
  · intro hx
    by_contra! h
    exact hx (s.mem_of_apply_eq_zero _ h.1.1 (le_antisymm h.1.2 h.2.2))

/-- The complements of the two closed half-subspaces `{x ∈ W' | ±φ x ≤ 0}` of an extension by a
line intersect in the complement of `W'`. -/
lemma compl_inter_compl :
    {x | x ∈ s.W' ∧ s.φ x ≤ 0}ᶜ ∩ {x | x ∈ s.W' ∧ (-s.φ) x ≤ 0}ᶜ = (s.W' : Set F)ᶜ := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq, LinearMap.neg_apply,
    neg_nonpos, SetLike.mem_coe]
  constructor
  · rintro ⟨h₁, h₂⟩ hx
    rcases le_total (s.φ x) 0 with h | h
    exacts [h₁ ⟨hx, h⟩, h₂ ⟨hx, h⟩]
  · intro hx
    exact ⟨fun h ↦ hx h.1, fun h ↦ hx h.1⟩

end LineExtension

end Submodule
