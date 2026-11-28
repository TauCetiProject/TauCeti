/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/

module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Gap bounds for the rows of a theta chain

At a fixed archimedean place the primed nodes form an arithmetic progression, and the step
weights are its midpoints. The base row is a descending block of letters ending at zero,
followed by the negatives of the primed nodes. We compute its gap criterion, and verify the
bounds needed for the rational row construction and multiplicity comparison.

The row and bounds follow L. Alpöge's `GlobalTheory.Mem.HostFrames.hostHyp_of_gaps` and
`GlobalTheory.Mem.HostFrames.hostHyp_frames_ev` in
`Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/StandardLatticesDiagonal.lean`.
-/

public section

namespace TauCeti.ThetaRow

/-- The `i`th primed node, with initial node `b` and spacing `2 * h`. Indices start at zero. -/
def primedNode (b h : ℤ) (i : ℕ) : ℤ := b + 2 * h * i

/-- The step weight between the `i`th and `(i+1)`st primed nodes. -/
def stepWeight (b h : ℤ) (i : ℕ) : ℤ := primedNode b h i + h

/-- The value of the primed node at an arbitrary index. -/
theorem primedNode_def (b h : ℤ) (i : ℕ) : primedNode b h i = b + 2 * h * i := (rfl)

/-- The step weight is the preceding primed node plus the half-spacing. -/
theorem stepWeight_def (b h : ℤ) (i : ℕ) : stepWeight b h i = primedNode b h i + h := (rfl)

/-- The first primed node is the base point. -/
@[simp] theorem primedNode_zero (b h : ℤ) : primedNode b h 0 = b := by simp [primedNode_def]

/-- The difference of two primed nodes is their signed index difference times the spacing. -/
theorem primedNode_sub (b h : ℤ) (i j : ℕ) :
    primedNode b h j - primedNode b h i = 2 * h * ((j : ℤ) - i) := by
  simp only [primedNode_def]
  ring

/-- The difference from a primed node to its following step weight is the signed half-spacing. -/
@[simp] theorem stepWeight_sub_primedNode (b h : ℤ) (i : ℕ) :
    stepWeight b h i - primedNode b h i = h := by simp [stepWeight_def]

/-- The signed half-spacing is also the gap from the step weight to the next primed node. -/
@[simp] theorem primedNode_succ_sub_stepWeight (b h : ℤ) (i : ℕ) :
    primedNode b h (i + 1) - stepWeight b h i = h := by
  rw [stepWeight_def, ← sub_sub, primedNode_sub, Nat.cast_add, Nat.cast_one]
  ring

/-- Every step weight is separated from every primed node by at least the absolute half-spacing.
The index factor in the difference is odd, hence cannot vanish. -/
theorem abs_le_abs_primedNode_sub_stepWeight (b h : ℤ) (i j : ℕ) :
    |h| ≤ |primedNode b h i - stepWeight b h j| := by
  have heq : primedNode b h i - stepWeight b h j = h * (2 * ((i : ℤ) - j) - 1) := by
    rw [stepWeight_def, ← sub_sub, primedNode_sub]
    ring
  have hodd : 1 ≤ |2 * ((i : ℤ) - j) - 1| := Int.one_le_abs (by omega)
  rw [heq, abs_mul]
  exact le_mul_of_one_le_right (abs_nonneg h) hodd

/-- The base row at one place, with letters indexed from `0` to `k` and `m` negated primed
nodes. The letters decrease by `4 * Δ` at each step, ending at zero. -/
def rowParameter (k m : ℕ) (Δ b h : ℤ) : Fin ((k + 1) + m) → ℤ :=
  Fin.append (fun i : Fin (k + 1) ↦ ((k : ℤ) - i.val) * (4 * Δ))
    (fun i : Fin m ↦ -primedNode b h i.val)

/-- Evaluate the base row on its letter block. -/
@[simp] theorem rowParameter_castAdd {k m : ℕ} (Δ b h : ℤ) (i : Fin (k + 1)) :
    rowParameter k m Δ b h (i.castAdd m) = ((k : ℤ) - i.val) * (4 * Δ) := by
  simp [rowParameter]

/-- Evaluate the base row on its negative primed-node block. -/
@[simp] theorem rowParameter_natAdd {k m : ℕ} (Δ b h : ℤ) (i : Fin m) :
    rowParameter k m Δ b h (i.natAdd (k + 1)) = -primedNode b h i.val := by
  simp [rowParameter]

/-- A nonnegative gap bounded by the letter step, the initial node, and the node spacing
separates every ordered pair of distinct entries of the base row. -/
theorem le_rowParameter_sub {k m g : ℕ} {Δ b h : ℤ}
    (hΔ : (g : ℤ) ≤ 4 * Δ) (hb : (g : ℤ) ≤ b) (hh : (g : ℤ) ≤ 2 * h)
    {i j : Fin ((k + 1) + m)} (hij : i < j) :
    (g : ℤ) ≤ rowParameter k m Δ b h i - rowParameter k m Δ b h j := by
  have hΔ₀ : 0 ≤ 4 * Δ := (Int.natCast_nonneg g).trans hΔ
  have hh₀ : 0 ≤ 2 * h := (Int.natCast_nonneg g).trans hh
  revert hij
  refine Fin.addCases (fun i ↦ Fin.addCases (fun j hij ↦ ?_) (fun j _ ↦ ?_) j)
    (fun i ↦ Fin.addCases (fun j hij ↦ ?_) (fun j hij ↦ ?_) j) i
  -- Compare two letters, a letter and a node, or two nodes. A node cannot precede a letter.
  · simp only [rowParameter_castAdd]
    have hlt : (i.val : ℤ) < j.val := by
      simp only [Fin.lt_def, Fin.val_castAdd] at hij
      exact_mod_cast hij
    have hd : 0 ≤ (j.val : ℤ) - i.val - 1 := by omega
    nlinarith [mul_nonneg hΔ₀ hd]
  · simp only [rowParameter_castAdd, rowParameter_natAdd, primedNode_def]
    have hik : (i.val : ℤ) ≤ k := by omega
    nlinarith [mul_nonneg (sub_nonneg.mpr hik) hΔ₀, mul_nonneg hh₀ (Int.natCast_nonneg j.val)]
  · exact (not_lt_of_ge (by
      simp only [Fin.le_def, Fin.val_castAdd, Fin.val_natAdd]
      omega) hij).elim
  · simp only [rowParameter_natAdd, neg_sub_neg, primedNode_sub]
    have hlt : (i.val : ℤ) < j.val := by
      simp only [Fin.lt_def, Fin.val_natAdd] at hij
      omega
    have hd : 0 ≤ (j.val : ℤ) - i.val - 1 := by omega
    nlinarith [mul_nonneg hh₀ hd]

/-- For a row with at least two letters and two nodes, the three gap tests are exact: each is
attained by an adjacent pair (the first two letters, the join, and the first two nodes). -/
theorem forall_le_rowParameter_sub_iff {k m g : ℕ} {Δ b h : ℤ} :
    (∀ i j : Fin ((k + 2) + (m + 2)), i < j →
      (g : ℤ) ≤ rowParameter (k + 1) (m + 2) Δ b h i -
        rowParameter (k + 1) (m + 2) Δ b h j) ↔
      (g : ℤ) ≤ 4 * Δ ∧ (g : ℤ) ≤ b ∧ (g : ℤ) ≤ 2 * h := by
  constructor
  · intro H
    have hletters := H ((0 : Fin (k + 2)).castAdd (m + 2))
      ((1 : Fin (k + 2)).castAdd (m + 2)) (by simp [Fin.lt_def])
    have hjoin := H ((Fin.last (k + 1)).castAdd (m + 2))
      ((0 : Fin (m + 2)).natAdd (k + 2)) (by simp [Fin.lt_def])
    have hnodes := H ((0 : Fin (m + 2)).natAdd (k + 2))
      ((1 : Fin (m + 2)).natAdd (k + 2)) (by simp [Fin.lt_def])
    refine ⟨?_, by simpa using hjoin, ?_⟩
    · simp at hletters
      linarith
    · simp [primedNode_def] at hnodes
      linarith
  · exact fun ⟨hΔ, hb, hh⟩ _ _ hij ↦ le_rowParameter_sub hΔ hb hh hij

/-- The quartic size bounds on the letter step and half-spacing imply the row conditions:
step weights interlace with both gaps at least `(t+3)/2`, the spacing between successive
primed nodes is at least `max (256*r^4) (4*N^3+2*t+6)`, and the base row has gaps at least
`100*r^4`. -/
theorem rowParameter_gaps_of_quartic_bounds {k m r t N : ℕ} {Δ b h : ℤ}
    (hN : 0 < N) (hr : r ≤ N) (ht : t ≤ N)
    (hΔ : (256 * N ^ 4 : ℕ) ≤ Δ) (hh : (256 * N ^ 4 : ℕ) ≤ h)
    (hb : (100 * r ^ 4 : ℕ) ≤ b) :
    (∀ i : ℕ, (t : ℤ) + 3 ≤ 2 * (stepWeight b h i - primedNode b h i) ∧
      (t : ℤ) + 3 ≤ 2 * (primedNode b h (i + 1) - stepWeight b h i)) ∧
    (∀ i : ℕ, max (256 * (r : ℤ) ^ 4) (4 * (N : ℤ) ^ 3 + 2 * t + 6) ≤
      primedNode b h (i + 1) - primedNode b h i) ∧
    ∀ i j : Fin ((k + 1) + m), i < j →
      (100 * r ^ 4 : ℕ) ≤ rowParameter k m Δ b h i - rowParameter k m Δ b h j := by
  push_cast at hΔ hh
  have hN₁ : (1 : ℤ) ≤ N := by exact_mod_cast hN
  have hrN : (r : ℤ) ^ 4 ≤ (N : ℤ) ^ 4 := by gcongr
  have htN : (t : ℤ) ≤ N := by exact_mod_cast ht
  have hn₃ : (N : ℤ) ^ 3 ≤ (N : ℤ) ^ 4 := pow_le_pow_right₀ hN₁ (by decide)
  have h14 : 1 ≤ (4 : ℕ) := by decide
  have hn₁ : (N : ℤ) ≤ (N : ℤ) ^ 4 := by
    simpa using pow_le_pow_right₀ hN₁ h14
  have hn₀ : (1 : ℤ) ≤ (N : ℤ) ^ 4 := hN₁.trans hn₁
  have hstep : (t : ℤ) + 3 ≤ 2 * h := by linarith
  have hnode : max (256 * (r : ℤ) ^ 4) (4 * (N : ℤ) ^ 3 + 2 * t + 6) ≤ 2 * h :=
    max_le (by linarith) (by linarith [htN, hn₀])
  refine ⟨fun i ↦ by simpa using hstep, fun i ↦ ?_, fun i j hij ↦ ?_⟩
  · simpa [primedNode_sub, Nat.cast_add] using hnode
  · refine le_rowParameter_sub (g := 100 * r ^ 4) ?_ hb ?_ hij <;> push_cast <;> linarith

end TauCeti.ThetaRow
