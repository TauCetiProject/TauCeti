/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PathSpace.Moore.Between.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Concatenating a finite sequence of Moore paths

Let `q 0, …, q n` be points of `X` and let `γ i` be a Moore path from `q i` to `q (i + 1)` for
each `i < n`. Their concatenation `MoorePathBetween.concat q γ` is the Moore path from `q 0` to
`q n` running through `γ 0, …, γ (n - 1)` in turn, with no reparametrization: its length is the
sum of the lengths of the pieces (`TauCeti.MoorePathBetween.length_concat`). For `n = 0` it is
the constant path of length zero at `q 0`.

Concatenation of Moore paths is strictly associative and unital, so this iterated concatenation
needs no bracketing convention, and a piece of length zero, necessarily a constant path, can be
dropped on the nose (`TauCeti.MoorePathBetween.concat_succ_of_length_eq_zero`). Concatenation is
continuous, so the iterated concatenation of continuously varying pieces varies continuously
(`TauCeti.MoorePathBetween.continuous_concat`); the vertices need not vary continuously, since
they are the endpoints of the pieces.

This is how a broken geodesic is assembled from its segments: the vertices are a tuple of points
and the pieces are the short geodesics joining consecutive vertices.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter III.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton, 1963, §16.
-/

public noncomputable section

open scoped NNReal

namespace TauCeti

namespace MoorePathBetween

variable {X : Type*} [TopologicalSpace X]

/-- The **concatenation** of Moore paths `γ i`, running from `q i.castSucc` to `q i.succ` for
`i < n`: the Moore path from `q 0` to `q (Fin.last n)` running through `γ 0, …, γ (n - 1)` in
turn. For `n = 0` it is the constant path of length zero at `q 0`. -/
def concat : {n : ℕ} → (q : Fin (n + 1) → X) → (γ : Fin n → MoorePath X) →
    (∀ i, (γ i).source = q i.castSucc ∧ (γ i).target = q i.succ) →
    MoorePathBetween X (q 0) (q (Fin.last n))
  | 0, q, _, _ => ⟨MoorePath.refl (q 0), by simp, by simp [Fin.last]⟩
  | _ + 1, q, γ, h =>
    ⟨(γ 0).trans (concat (Fin.tail q) (Fin.tail γ)
        fun i ↦ by simpa [Fin.tail] using h i.succ).toMoorePath
        (by rw [source]; exact (h 0).2),
      by simpa using (h 0).1, by rw [MoorePath.target_trans, target]; simp [Fin.tail]⟩

variable {n : ℕ} {q : Fin (n + 1) → X} {γ : Fin n → MoorePath X}

@[simp]
theorem toMoorePath_concat_zero {q : Fin 1 → X} {γ : Fin 0 → MoorePath X}
    (h : ∀ i, (γ i).source = q i.castSucc ∧ (γ i).target = q i.succ) :
    (concat q γ h).toMoorePath = MoorePath.refl (q 0) := by
  rw [concat, toMoorePath_mk]

theorem toMoorePath_concat_succ {q : Fin (n + 2) → X} {γ : Fin (n + 1) → MoorePath X}
    (h : ∀ i, (γ i).source = q i.castSucc ∧ (γ i).target = q i.succ) :
    (concat q γ h).toMoorePath =
      (γ 0).trans (concat (Fin.tail q) (Fin.tail γ)
        fun i ↦ by simpa [Fin.tail] using h i.succ).toMoorePath
        (by rw [source]; exact (h 0).2) := by
  rw [concat, toMoorePath_mk]

/-- The length of a concatenation is the sum of the lengths of its pieces. -/
@[simp]
theorem length_concat (h : ∀ i, (γ i).source = q i.castSucc ∧ (γ i).target = q i.succ) :
    (concat q γ h).toMoorePath.length = ∑ i, (γ i).length := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [toMoorePath_concat_succ, MoorePath.length_trans, ih, Fin.sum_univ_succ]
    rfl

/-- **A piece of length zero can be dropped**: if the first piece has length zero, the
concatenation is the concatenation of the remaining pieces, as a Moore path. -/
theorem toMoorePath_concat_succ_of_length_eq_zero {q : Fin (n + 2) → X}
    {γ : Fin (n + 1) → MoorePath X}
    (h : ∀ i, (γ i).source = q i.castSucc ∧ (γ i).target = q i.succ) (h0 : (γ 0).length = 0) :
    (concat q γ h).toMoorePath =
      (concat (Fin.tail q) (Fin.tail γ)
        fun i ↦ by simpa [Fin.tail] using h i.succ).toMoorePath := by
  obtain ⟨x, hx⟩ : ∃ x, γ 0 = MoorePath.refl x := ⟨_, MoorePath.eq_refl_of_length_eq_zero h0⟩
  rw [toMoorePath_concat_succ]
  simp only [hx, MoorePath.refl_trans]

/-- A concatenation of pieces of length zero is the constant path of length zero. -/
theorem toMoorePath_concat_of_length_eq_zero
    (h : ∀ i, (γ i).source = q i.castSucc ∧ (γ i).target = q i.succ)
    (h0 : ∀ i, (γ i).length = 0) :
    (concat q γ h).toMoorePath = MoorePath.refl (q 0) := by
  have hc := MoorePath.eq_refl_of_length_eq_zero
    ((length_concat h).trans (Finset.sum_eq_zero fun i _ ↦ h0 i))
  rwa [source] at hc

/-- **Concatenation of continuous families is continuous.** If the first vertex `q y 0` and each
piece `γ y i` depend continuously on the parameter `y`, so does their concatenation. The first
vertex matters only when there are no pieces. -/
theorem continuous_concat {Y : Type*} [TopologicalSpace Y] {q : Y → Fin (n + 1) → X}
    {γ : Y → Fin n → MoorePath X}
    (h : ∀ y i, (γ y i).source = q y i.castSucc ∧ (γ y i).target = q y i.succ)
    (hq : Continuous fun y ↦ q y 0) (hγ : ∀ i, Continuous fun y ↦ γ y i) :
    Continuous fun y ↦ (concat (q y) (γ y) (h y)).toMoorePath := by
  induction n with
  | zero =>
    simp only [toMoorePath_concat_zero]
    exact MoorePath.continuous_refl.comp hq
  | succ n ih =>
    simp only [toMoorePath_concat_succ]
    have hq' : Continuous fun y ↦ Fin.tail (q y) 0 := by
      convert MoorePath.continuous_target.comp (hγ 0) using 2 with y
      exact ((h y 0).2).symm
    exact (hγ 0).moorePath_trans
      (ih (q := fun y ↦ Fin.tail (q y)) (γ := fun y ↦ Fin.tail (γ y))
        (fun y i ↦ by simpa [Fin.tail] using h y i.succ) hq' fun i ↦ hγ i.succ) _

end MoorePathBetween

end TauCeti
