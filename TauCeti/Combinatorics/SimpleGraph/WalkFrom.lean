/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Fin.Tuple.Take

/-!
# Walks recorded as vertex sequences

A walk in a simple graph `G` with `m` steps starting at `v₀` can be recorded by its sequence of
`m + 1` vertices `s : Fin (m + 1) → V`: the sequence starts at `v₀` and consecutive vertices are
adjacent. This encoding is convenient when walks index the basis of a vector space, as in the path
models of the Temperley–Lieb algebras, since the walks with a fixed number of steps then form a
decidable subset of a finite function type.

## Main definitions

* `SimpleGraph.IsWalkFrom`: a vertex sequence is a walk in `G` from `v₀`.

## Main results

* `SimpleGraph.isWalkFrom_snoc`: a walk extended by one vertex is a walk exactly when the new
  vertex is adjacent to the old endpoint.
* `SimpleGraph.IsWalkFrom.take`: any prefix of a walk from `v₀` is a walk from `v₀`.
* `SimpleGraph.IsWalkFrom.update`: moving an interior vertex of a walk whose neighbouring positions
  carry the same vertex to another neighbour of that vertex gives a walk.
* `SimpleGraph.IsWalkFrom.le_add_of_adj_le_succ`: if each step increases a `ℕ`-valued function by
  at most `1`, then `i` steps increase it by at most `i`.
-/

public section

open Function

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V) (v₀ : V)

/-- `s` is a walk in `G` with `m` steps starting at `v₀`, recorded by its sequence of `m + 1`
vertices. -/
def IsWalkFrom {m : ℕ} (s : Fin (m + 1) → V) : Prop :=
  s 0 = v₀ ∧ ∀ i : Fin m, G.Adj (s i.castSucc) (s i.succ)

instance [DecidableEq V] [DecidableRel G.Adj] {m : ℕ} (s : Fin (m + 1) → V) :
    Decidable (IsWalkFrom G v₀ s) :=
  inferInstanceAs (Decidable (s 0 = v₀ ∧ ∀ i : Fin m, G.Adj (s i.castSucc) (s i.succ)))

variable {G v₀}

/-- A vertex sequence is a walk from `v₀` exactly when it starts at `v₀` and consecutive vertices
are adjacent. -/
theorem isWalkFrom_iff {m : ℕ} (s : Fin (m + 1) → V) :
    IsWalkFrom G v₀ s ↔ s 0 = v₀ ∧ ∀ i : Fin m, G.Adj (s i.castSucc) (s i.succ) :=
  (Iff.rfl)

/-- A walk with no steps is just its starting vertex. -/
@[simp]
theorem isWalkFrom_zero (s : Fin 1 → V) : IsWalkFrom G v₀ s ↔ s 0 = v₀ := by
  simp [isWalkFrom_iff]

/-- A walk from `v₀` starts at `v₀`. -/
theorem IsWalkFrom.apply_zero {m : ℕ} {s : Fin (m + 1) → V} (hs : IsWalkFrom G v₀ s) :
    s 0 = v₀ :=
  ((isWalkFrom_iff s).1 hs).1

/-- A walk extended by one vertex is a walk exactly when the new vertex is adjacent to the old
endpoint. -/
@[simp]
theorem isWalkFrom_snoc {m : ℕ} (s : Fin (m + 1) → V) (y : V) :
    IsWalkFrom G v₀ (Fin.snoc s y : Fin (m + 2) → V) ↔
      IsWalkFrom G v₀ s ∧ G.Adj (s (Fin.last m)) y := by
  rw [IsWalkFrom, IsWalkFrom, Fin.forall_fin_succ']
  simp [and_assoc, Fin.succ_castSucc, -Fin.castSucc_succ]

/-- A vertex sequence is a walk exactly when its initial segment is a walk whose endpoint is
adjacent to the last vertex. -/
theorem isWalkFrom_iff_init {m : ℕ} (s : Fin (m + 2) → V) :
    IsWalkFrom G v₀ s ↔
      IsWalkFrom G v₀ (Fin.init s) ∧ G.Adj (Fin.init s (Fin.last m)) (s (Fin.last (m + 1))) := by
  conv_lhs => rw [← Fin.snoc_init_self s]
  exact isWalkFrom_snoc _ _

/-- Dropping the last step of a walk from `v₀` leaves a walk from `v₀`. -/
theorem IsWalkFrom.init {m : ℕ} {s : Fin (m + 2) → V} (hs : IsWalkFrom G v₀ s) :
    IsWalkFrom G v₀ (Fin.init s) :=
  ((isWalkFrom_iff_init s).1 hs).1

/-- Consecutive vertices of a walk are adjacent. -/
theorem IsWalkFrom.adj {m : ℕ} {s : Fin (m + 1) → V} (hs : IsWalkFrom G v₀ s)
    {a b : Fin (m + 1)} (hab : a.val + 1 = b.val) : G.Adj (s a) (s b) := by
  have h := hs.2 ⟨a, by omega⟩
  rwa [show (⟨a, _⟩ : Fin m).castSucc = a from Fin.ext rfl,
    show (⟨a, _⟩ : Fin m).succ = b from Fin.ext (by simp [hab])] at h

/-- The prefix of length `k ≤ m` of an `m`-step walk from `v₀` is a `k`-step walk from `v₀`. -/
theorem IsWalkFrom.take {m k : ℕ} (hk : k ≤ m) {s : Fin (m + 1) → V} (hs : IsWalkFrom G v₀ s) :
    IsWalkFrom G v₀ (Fin.take (k + 1) (Nat.add_le_add_right hk 1) s) := by
  refine ⟨by simpa [Fin.take_apply] using hs.1, fun i ↦ ?_⟩
  simp only [Fin.take_apply]
  exact hs.adj rfl

/-- Moving the vertex at an interior position `b` of a walk, whose two neighbouring positions
carry the same vertex, to another neighbour of that vertex gives a walk. -/
theorem IsWalkFrom.update {m : ℕ} {s : Fin (m + 1) → V} (hs : IsWalkFrom G v₀ s)
    {a b c : Fin (m + 1)} (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val) (hac : s a = s c)
    {x : V} (hx : G.Adj (s a) x) : IsWalkFrom G v₀ (update s b x) := by
  refine ⟨by rw [update_of_ne (Fin.ne_of_val_ne (by rw [Fin.val_zero]; omega))]; exact hs.1,
    fun i ↦ ?_⟩
  by_cases h₁ : i.succ = b
  · have ha : i.castSucc = a := Fin.ext (by simp [← h₁] at hab ⊢; omega)
    rw [h₁, update_self, update_of_ne (by rw [ha]; exact Fin.ne_of_val_ne (by omega)), ha]
    exact hx
  by_cases h₂ : i.castSucc = b
  · have hc : i.succ = c := Fin.ext (by simp [← h₂] at hbc ⊢; omega)
    rw [h₂, update_self, update_of_ne (by rw [hc]; exact Fin.ne_of_val_ne (by omega)), hc,
      ← hac]
    exact hx.symm
  · rw [update_of_ne h₁, update_of_ne h₂]
    exact hs.2 i

/-- If every step in `G` increases a `ℕ`-valued function `f` by at most `1`, then after `i` steps
a walk from `v₀` reaches at most `f v₀ + i`. -/
theorem IsWalkFrom.le_add_of_adj_le_succ {m : ℕ} {s : Fin (m + 1) → V} (hs : IsWalkFrom G v₀ s)
    (f : V → ℕ) (hf : ∀ ⦃u v⦄, G.Adj u v → f v ≤ f u + 1) (i : Fin (m + 1)) :
    f (s i) ≤ f v₀ + i.val := by
  induction i using Fin.induction with
  | zero => simp [hs.1]
  | succ j ih =>
    have hstep := hf (hs.2 j)
    simp only [Fin.val_castSucc] at ih
    simp only [Fin.val_succ]
    omega

end SimpleGraph
