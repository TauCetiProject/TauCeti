/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MoorePath.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Concatenation of Moore paths

Two Moore paths `γ`, `δ` with `γ.target = δ.source` **concatenate** to the path of duration
`γ.length + δ.length` which runs through `γ` and then through `δ`.  Because the durations add,
concatenation is strictly associative (`trans_assoc`) and the constant paths of duration `0` are
strict units (`const_trans`, `trans_const`): these are equalities of Moore paths, not homotopies.
This is the reason to use Moore paths rather than paths on the unit interval, whose concatenation
is associative and unital only up to homotopy.

Concatenation is continuous on the space of pairs of composable paths (`continuous_trans`), by
the exponential law `MoorePath.continuous_iff`.

## Main definitions

* `TauCeti.MoorePath.trans γ δ h`: the concatenation of `γ` and `δ`, for `h : γ.target = δ.source`.

## Main results

* `TauCeti.MoorePath.trans_assoc`: concatenation is strictly associative.
* `TauCeti.MoorePath.const_trans`, `TauCeti.MoorePath.trans_const`: the constant paths are strict
  units.
* `TauCeti.MoorePath.continuous_trans`: concatenation is continuous on composable pairs.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Section 7.1.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter III.
-/

public section

open NNReal Topology

namespace TauCeti

namespace MoorePath

variable {X : Type*} [TopologicalSpace X]

/-- The **concatenation** of two Moore paths with `γ.target = δ.source`: `γ` on `[0, γ.length]`,
then `δ`, shifted by `γ.length`. -/
noncomputable def trans (γ δ : MoorePath X) (h : γ.target = δ.source) : MoorePath X where
  toFun t := if t ≤ γ.length then γ t else δ (t - γ.length)
  continuous_toFun := by
    refine Continuous.if_le γ.continuous
      (δ.continuous.comp (continuous_id.sub _root_.continuous_const)) continuous_id
      _root_.continuous_const fun t ht ↦ ?_
    rw [ht, tsub_self, ← target_eq_apply, ← source_eq_apply]
    exact h
  length := γ.length + δ.length
  stopped' t ht := by
    split_ifs with h₁ h₂ h₂
    · rw [le_antisymm (h₁.trans le_self_add) ht]
    · exact (h₂ (ht.trans h₁)).elim
    · -- `δ` has duration `0`, so it is constant at `δ.source = γ.target`.
      have hδ : δ.length = 0 := by simpa using h₂
      rw [δ.apply_eq_target_of_length_le (hδ.trans_le zero_le), hδ, add_zero, ← target_eq_apply, h,
        target_eq_apply, hδ, source_eq_apply]
    · rw [add_tsub_cancel_left, δ.apply_of_length_le (le_tsub_of_add_le_left ht)]

variable {γ δ ε : MoorePath X}

theorem trans_apply (h : γ.target = δ.source) (t : ℝ≥0) :
    γ.trans δ h t = if t ≤ γ.length then γ t else δ (t - γ.length) :=
  (rfl)

@[simp]
theorem length_trans (h : γ.target = δ.source) : (γ.trans δ h).length = γ.length + δ.length :=
  (rfl)

theorem trans_apply_of_le (h : γ.target = δ.source) {t : ℝ≥0} (ht : t ≤ γ.length) :
    γ.trans δ h t = γ t :=
  ite_eq_left ht

theorem trans_apply_of_length_le (h : γ.target = δ.source) {t : ℝ≥0} (ht : γ.length ≤ t) :
    γ.trans δ h t = δ (t - γ.length) := by
  rcases ht.lt_or_eq with hlt | heq
  · exact ite_eq_right hlt.not_ge
  · rw [← heq, tsub_self, trans_apply, ite_eq_left le_rfl, ← source_eq_apply, ← h, target_eq_apply]

@[simp]
theorem source_trans (h : γ.target = δ.source) : (γ.trans δ h).source = γ.source := by
  rw [source_eq_apply, source_eq_apply]
  exact trans_apply_of_le h zero_le

@[simp]
theorem target_trans (h : γ.target = δ.source) : (γ.trans δ h).target = δ.target := by
  rw [target_eq_apply, length_trans, trans_apply_of_length_le h le_self_add, add_tsub_cancel_left,
    target_eq_apply]

/-- Concatenation is strictly associative. -/
theorem trans_assoc (h₁ : γ.target = δ.source) (h₂ : δ.target = ε.source)
    (h₁₂ : (γ.trans δ h₁).target = ε.source) (h₂₃ : γ.target = (δ.trans ε h₂).source) :
    (γ.trans δ h₁).trans ε h₁₂ = γ.trans (δ.trans ε h₂) h₂₃ := by
  refine ext (by simp [add_assoc]) fun t _ ↦ ?_
  rcases le_or_gt t γ.length with ht₁ | ht₁
  · rw [trans_apply_of_le h₁₂ (by simpa using ht₁.trans le_self_add), trans_apply_of_le h₁ ht₁,
      trans_apply_of_le h₂₃ ht₁]
  rcases le_or_gt t (γ.length + δ.length) with ht₂ | ht₂
  · rw [trans_apply_of_le h₁₂ (by simpa using ht₂), trans_apply_of_length_le h₁ ht₁.le,
      trans_apply_of_length_le h₂₃ ht₁.le, trans_apply_of_le h₂ (tsub_le_iff_left.2 ht₂)]
  · rw [trans_apply_of_length_le h₁₂ (by simpa using ht₂.le), trans_apply_of_length_le h₂₃ ht₁.le,
      trans_apply_of_length_le h₂ (le_tsub_of_add_le_left ht₂.le), length_trans, tsub_tsub]

/-- The constant path is a strict left unit. -/
@[simp]
theorem const_trans {x : X} (h : (const x).target = δ.source) : (const x).trans δ h = δ := by
  refine ext (by simp) fun t _ ↦ ?_
  rw [trans_apply_of_length_le h ((length_const x).trans_le zero_le), length_const, tsub_zero]

/-- The constant path is a strict right unit. -/
@[simp]
theorem trans_const {x : X} (h : γ.target = (const x).source) : γ.trans (const x) h = γ := by
  refine ext (by simp) fun t _ ↦ ?_
  rcases le_or_gt t γ.length with ht | ht
  · exact trans_apply_of_le h ht
  · rw [trans_apply_of_length_le h ht.le, const_apply, ← source_const x, ← h,
      γ.apply_eq_target_of_length_le ht.le]

/-- Concatenation is continuous on the space of composable pairs. -/
theorem continuous_trans :
    Continuous fun p : {p : MoorePath X × MoorePath X // p.1.target = p.2.source} ↦
      p.1.1.trans p.1.2 p.2 := by
  have hγ : Continuous fun p : {p : MoorePath X × MoorePath X // p.1.target = p.2.source} ↦ p.1.1 :=
    continuous_fst.comp continuous_subtype_val
  have hδ : Continuous fun p : {p : MoorePath X × MoorePath X // p.1.target = p.2.source} ↦ p.1.2 :=
    continuous_snd.comp continuous_subtype_val
  rw [continuous_iff]
  refine ⟨(continuous_length.comp hγ).add (continuous_length.comp hδ), ?_⟩
  simp only [trans_apply]
  refine Continuous.if_le (continuous_eval.comp ((hγ.comp continuous_fst).prodMk continuous_snd))
    (continuous_eval.comp ((hδ.comp continuous_fst).prodMk
      (continuous_snd.sub (continuous_length.comp (hγ.comp continuous_fst)))))
    continuous_snd (continuous_length.comp (hγ.comp continuous_fst)) fun q hq ↦ ?_
  rw [hq, tsub_self, ← target_eq_apply, ← source_eq_apply]
  exact q.1.2

end MoorePath

end TauCeti
