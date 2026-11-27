/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Pi
public import TauCeti.Analysis.Polynomial.Interlacing.Basic
import TauCeti.Algebra.Polynomial.Colex.Basic

/-!
# Interlacing families of polynomials

Let `S 0, …, S (m - 1)` be finite types and `f : (∀ k, S k) → ℝ[X]` a family of real polynomials
indexed by the assignments `σ` of a value in `S k` to every coordinate `k`. For a number `k` and
an assignment `τ`, the partial sum `TauCeti.partialSum f k τ` is the sum of the `f σ` over the
assignments `σ` that agree with `τ` at every coordinate below `k`. Fixing the coordinates below
`k` as in `τ` and letting the value at `k` vary splits this sum into the partial sums at level
`k + 1`; the family is an *interlacing family* (`TauCeti.IsInterlacingFamily`) when these are
commonly interlaced, for every `k` and every `τ`.

The main theorem is that of Marcus, Spielman and Srivastava: if the members of an interlacing
family have positive leading coefficients and every `S k` is nonempty, then some member has every
root at most some root of the sum of all the members. Starting from the full sum, the one-level
lemma `TauCeti.exists_isRoot_le_of_commonlyInterlaced` fixes one coordinate at a time; after `m`
steps the partial sum is a single member. Marcus, Spielman and Srivastava apply this to the
characteristic polynomials of the signed adjacency matrices of a graph, whose sum is a multiple
of its matching polynomial, to find a signing with every eigenvalue at most the largest root of
the matching polynomial.

## Main definitions

* `TauCeti.partialSum`: the sum over the assignments that agree with `τ` below `k`.
* `TauCeti.IsInterlacingFamily`: the children of every partial sum are commonly interlaced.

## Main results

* `TauCeti.sum_partialSum_update`: a partial sum is the sum of its children.
* `TauCeti.exists_isRoot_le_of_isInterlacingFamily`: some member of an interlacing family with
  positive leading coefficients has every root at most some root of the sum of all members.

## References

* A. W. Marcus, D. A. Spielman, N. Srivastava, *Interlacing families I: bipartite Ramanujan
  graphs of all degrees*, Ann. of Math. 182 (2015), 307–325; arXiv:1304.4132, Definition 4.3 and
  Theorem 4.4.
-/

public section

open Finset Polynomial

namespace TauCeti

variable {m : ℕ} {S : Fin m → Type*} [∀ k, Fintype (S k)] [∀ k, DecidableEq (S k)]

section PartialSum

variable {M : Type*} [AddCommMonoid M]

/-- The partial sum of a family `f` indexed by assignments `σ : ∀ k, S k`: the sum of `f σ` over
the assignments `σ` that agree with `τ` at every coordinate below `k`. -/
def partialSum (f : (∀ k, S k) → M) (k : ℕ) (τ : ∀ k, S k) : M :=
  ∑ σ with ∀ i : Fin m, (i : ℕ) < k → σ i = τ i, f σ

/-- The defining formula of a partial sum. -/
theorem partialSum_def (f : (∀ k, S k) → M) (k : ℕ) (τ : ∀ k, S k) :
    partialSum f k τ = ∑ σ with ∀ i : Fin m, (i : ℕ) < k → σ i = τ i, f σ :=
  (rfl)

/-- With no coordinate fixed, the partial sum is the sum of the whole family. -/
@[simp]
theorem partialSum_zero (f : (∀ k, S k) → M) (τ : ∀ k, S k) :
    partialSum f 0 τ = ∑ σ, f σ := by
  simp [partialSum]

/-- With every coordinate fixed, the partial sum is the single member `f τ`. -/
theorem partialSum_of_le (f : (∀ k, S k) → M) {k : ℕ} (hk : m ≤ k) (τ : ∀ k, S k) :
    partialSum f k τ = f τ := by
  rw [partialSum, Finset.sum_eq_single_of_mem τ (by simp)]
  intro σ hσ hne
  refine absurd (funext fun i ↦ ?_) hne
  exact (mem_filter.1 hσ).2 i (i.isLt.trans_le hk)

/-- A partial sum is the sum of its children: fixing the coordinates below `k` as in `τ` and
summing over every value of the coordinate `k`. -/
theorem sum_partialSum_update (f : (∀ k, S k) → M) (k : Fin m) (τ : ∀ k, S k) :
    ∑ t : S k, partialSum f ((k : ℕ) + 1) (Function.update τ k t) = partialSum f k τ := by
  rw [partialSum, ← sum_fiberwise _ (fun σ : ∀ k, S k ↦ σ k)]
  refine sum_congr rfl fun t _ ↦ ?_
  rw [partialSum, filter_filter]
  refine sum_congr (filter_congr fun σ _ ↦ ⟨fun h ↦ ⟨fun i hi ↦ ?_, ?_⟩, fun ⟨h, hk⟩ i hi ↦ ?_⟩)
    fun _ _ ↦ rfl
  · simpa [Function.update_of_ne (Fin.ne_of_lt hi)] using h i (by omega)
  · simpa using h k (by omega)
  · rcases (Nat.lt_succ_iff.1 hi).lt_or_eq with hi | hi
    · simpa [Function.update_of_ne (Fin.ne_of_lt hi)] using h i hi
    · obtain rfl := Fin.ext hi
      simpa using hk

end PartialSum

/-- An *interlacing family* of real polynomials: for every coordinate `k` and every assignment
`τ`, the partial sums obtained by fixing the coordinates below `k` as in `τ` and letting the value
at `k` vary are commonly interlaced. -/
def IsInterlacingFamily (f : (∀ k, S k) → ℝ[X]) : Prop :=
  ∀ (k : Fin m) (τ : ∀ k, S k),
    CommonlyInterlaced fun t : S k ↦ partialSum f ((k : ℕ) + 1) (Function.update τ k t)

/-- The defining property of an interlacing family. -/
theorem isInterlacingFamily_iff {f : (∀ k, S k) → ℝ[X]} :
    IsInterlacingFamily f ↔ ∀ (k : Fin m) (τ : ∀ k, S k),
      CommonlyInterlaced fun t : S k ↦ partialSum f ((k : ℕ) + 1) (Function.update τ k t) :=
  Iff.rfl

/-- Every partial sum of a family with positive leading coefficients has positive leading
coefficient. -/
theorem leadingCoeff_partialSum_pos {f : (∀ k, S k) → ℝ[X]}
    (hlc : ∀ σ, 0 < (f σ).leadingCoeff) (k : ℕ) (τ : ∀ k, S k) :
    0 < (partialSum f k τ).leadingCoeff :=
  leadingCoeff_sum_pos ⟨τ, by simp⟩ fun σ _ ↦ hlc σ

/-- **Interlacing families** (Marcus–Spielman–Srivastava, Theorem 4.4). If the members of an
interlacing family of real polynomials have positive leading coefficients, then some member has
every root at most some root of the sum of all the members. -/
theorem exists_isRoot_le_of_isInterlacingFamily [∀ k, Nonempty (S k)]
    (f : (∀ k, S k) → ℝ[X]) (hlc : ∀ σ, 0 < (f σ).leadingCoeff)
    (hf : IsInterlacingFamily f) :
    ∃ σ, ∀ x : ℝ, (f σ).IsRoot x → ∃ y : ℝ, (∑ σ', f σ').IsRoot y ∧ x ≤ y := by
  -- Going down from level `m`, where the partial sum is a single member, to level `0`.
  suffices h : ∀ n ≤ m, ∀ τ, ∃ σ, ∀ x : ℝ, (f σ).IsRoot x →
      ∃ y : ℝ, (partialSum f (m - n) τ).IsRoot y ∧ x ≤ y by
    simpa using h m le_rfl (Classical.arbitrary _)
  intro n
  induction n with
  | zero =>
    exact fun _ τ ↦ ⟨τ, fun x hx ↦ ⟨x, by rwa [Nat.sub_zero, partialSum_of_le f le_rfl], le_rfl⟩⟩
  | succ n ih =>
    intro hn τ
    let k : Fin m := ⟨m - (n + 1), by omega⟩
    have hk : (k : ℕ) + 1 = m - n := by simp only [k]; omega
    -- Choose the child at level `k + 1` given by the one-level lemma, and descend into it.
    obtain ⟨t, ht⟩ := exists_isRoot_le_of_commonlyInterlaced (hf k τ)
      fun t ↦ leadingCoeff_partialSum_pos hlc _ _
    obtain ⟨σ, hσ⟩ := ih (by omega) (Function.update τ k t)
    refine ⟨σ, fun x hx ↦ ?_⟩
    obtain ⟨y, hy, hxy⟩ := hσ x hx
    rw [← hk] at hy
    obtain ⟨z, hz, hyz⟩ := ht y hy
    rw [sum_partialSum_update] at hz
    exact ⟨z, hz, hxy.trans hyz⟩

end TauCeti
