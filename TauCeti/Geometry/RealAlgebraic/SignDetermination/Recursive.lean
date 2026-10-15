/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.SignDetermination.Adapted
import Mathlib.Data.Fin.Tuple.Basic

/-! # Recursive sign determination with adapted queries

A count table records the number of sample points with each sign word. To adjoin a
polynomial, retain the positive entries of the old table and extend each of their words
by the three possible signs. These candidate columns are distinct, so an adapted square
query matrix is invertible. Its inverse computes the new counts; words whose old tail
was absent have count zero.

`refineCounts` performs this step using a polynomial sign-sum oracle. `determineSigns`
iterates it by structural recursion on the number of polynomials, starting with the
oracle's value on `1`. Both are noncomputable: independent query rows are chosen by
classical choice. No assumption of realizability is used to choose rows or candidates.
When the oracle supplies exact sign sums, the resulting rational entries are the exact
natural counts, so positive entries characterize all realized sign conditions.

The root specialization uses Tarski queries and counts distinct roots with arbitrary
multiplicities. A zero root polynomial gives an empty sample, not its infinite zero set.

## References

C. Cordwell, Y. K. Tan, A. Platzer,
[*A Verified Decision Procedure for Univariate Real Arithmetic with the BKR Algorithm*]
(https://doi.org/10.4230/LIPIcs.ITP.2021.14), ITP 2021, for recursive query adaptation.
S. Basu, R. Pollack, M.-F. Roy,
[*Algorithms in Real Algebraic Geometry*, second edition]
(https://doi.org/10.1007/3-540-33099-2), Chapter 10.
-/

public section

open Polynomial
open scoped Matrix

namespace TauCeti.SignDetermination

variable {n : ℕ}

private theorem extension_columns_injective (c : (Fin n → SignType) → ℚ) :
    Function.Injective (fun a : {σ // 0 < c σ} × SignType =>
      Fin.cons (α := fun _ => SignType) a.2 a.1.val) := by
  intro a b h
  obtain ⟨hhead, htail⟩ := Fin.cons_inj.mp h
  exact Prod.ext (Subtype.ext htail) hhead

open scoped Classical in
/-- Choose one independent query row per candidate extension of a positive old count.
The choice depends only on the old count table, not on the new polynomial or oracle. -/
noncomputable def extensionRows (c : (Fin n → SignType) → ℚ) :
    ({σ // 0 < c σ} × SignType) ↪ (Fin (n + 1) → Fin 3) :=
  Classical.choose (exists_isUnit_fullMatrix_submatrix
    (fun a : {σ // 0 < c σ} × SignType => Fin.cons (α := fun _ => SignType) a.2 a.1.val)
    (extension_columns_injective c))

open scoped Classical in
/-- The selected extension queries form an invertible square matrix. This includes an
empty old support, in which case the square matrix has no rows or columns. -/
theorem isUnit_extensionRows (c : (Fin n → SignType) → ℚ) :
    IsUnit ((fullMatrix (Fin (n + 1))).submatrix (extensionRows c)
      (fun a : {σ // 0 < c σ} × SignType => Fin.cons (α := fun _ => SignType) a.2 a.1.val)) :=
  Classical.choose_spec (exists_isUnit_fullMatrix_submatrix
    (fun a : {σ // 0 < c σ} × SignType => Fin.cons (α := fun _ => SignType) a.2 a.1.val)
    (extension_columns_injective c))

section Construction

variable {R : Type*} [CommSemiring R]

open scoped Classical in
/-- Recover candidate extension counts from adapted polynomial queries, with zero for
words whose tail has no positive old count. Correctness requires an exact sign-sum oracle
and a correct old table, as stated in `refineCounts_eq_signCount`. -/
noncomputable def refineCounts (query : R[X] → ℚ) (Q : Fin n → R[X]) (q : R[X])
    (c : (Fin n → SignType) → ℚ) (σ : Fin (n + 1) → SignType) : ℚ :=
  if h : 0 < c (Fin.tail σ) then
    (((fullMatrix (Fin (n + 1))).submatrix (extensionRows c)
      (fun a : {τ // 0 < c τ} × SignType => Fin.cons (α := fun _ => SignType) a.2 a.1.val))⁻¹ *ᵥ
        (fun i => query (∏ j, (Fin.cons (α := fun _ => R[X]) q Q j) ^ (extensionRows c i j).val)))
      (⟨Fin.tail σ, h⟩, σ 0)
  else 0

open scoped Classical in
/-- The characteristic formula for the update on an old supported word. -/
@[simp]
theorem refineCounts_cons (query : R[X] → ℚ) (Q : Fin n → R[X]) (q : R[X])
    (c : (Fin n → SignType) → ℚ) (τ : Fin n → SignType) (hτ : 0 < c τ)
    (s : SignType) :
    refineCounts query Q q c (Fin.cons s τ) =
      (((fullMatrix (Fin (n + 1))).submatrix (extensionRows c)
        (fun a : {υ // 0 < c υ} × SignType => Fin.cons (α := fun _ => SignType) a.2 a.1.val))⁻¹ *ᵥ
          (fun i => query (∏ j, (Fin.cons (α := fun _ => R[X]) q Q j) ^ (extensionRows c i j).val)))
        (⟨τ, hτ⟩, s) := by
  simp [refineCounts, hτ]

/-- An extension of an unsupported word has count zero, without evaluating any query. -/
@[simp]
theorem refineCounts_eq_zero (query : R[X] → ℚ) (Q : Fin n → R[X]) (q : R[X])
    (c : (Fin n → SignType) → ℚ) (σ : Fin (n + 1) → SignType)
    (h : ¬ 0 < c (Fin.tail σ)) : refineCounts query Q q c σ = 0 := by
  simp [refineCounts, h]

/-- Determine sign counts by successively adjoining the first polynomial to the recursively
computed tail table. The recursion terminates after exactly the tuple length many updates. -/
noncomputable def determineSigns (query : R[X] → ℚ) :
    (n : ℕ) → (Fin n → R[X]) → (Fin n → SignType) → ℚ
  | 0, _, _ => query 1
  | n + 1, Q, σ => refineCounts query (Fin.tail Q) (Q 0)
      (determineSigns query n (Fin.tail Q)) σ

@[simp]
theorem determineSigns_zero (query : R[X] → ℚ) (Q : Fin 0 → R[X])
    (σ : Fin 0 → SignType) : determineSigns query 0 Q σ = query 1 := (rfl)

/-- The successor equation exposes the single adapted update used by the recursion. -/
@[simp]
theorem determineSigns_succ (query : R[X] → ℚ) (Q : Fin (n + 1) → R[X]) :
    determineSigns query (n + 1) Q = refineCounts query (Fin.tail Q) (Q 0)
      (determineSigns query n (Fin.tail Q)) := (rfl)

end Construction

section Correctness

variable {R : Type*} [CommRing R] [LinearOrder R]

/-- A correct count table covers all new sign words by extending only its positive entries. -/
private theorem extension_columns_cover (Z : Finset R) (Q : Fin n → R[X]) (q : R[X])
    (c : (Fin n → SignType) → ℚ) (hc : ∀ σ, c σ = (Z.signCount Q σ : ℚ)) :
    ∀ x ∈ Z, ∃ a : {σ // 0 < c σ} × SignType,
      Fin.cons (α := fun _ => SignType) a.2 a.1.val =
        fun j => SignType.sign ((Fin.cons (α := fun _ => R[X]) q Q j).eval x) := by
  intro x hx
  let τ := fun j => SignType.sign ((Q j).eval x)
  have hτ : 0 < c τ := by
    rw [hc, Nat.cast_pos]
    exact (Finset.signCount_pos Z Q τ).mpr ⟨x, hx, fun _ => rfl⟩
  refine ⟨(⟨τ, hτ⟩, SignType.sign (q.eval x)), ?_⟩
  ext j
  cases j using Fin.cases <;> simp [τ]

variable [IsStrictOrderedRing R]

/-- Adjoining one polynomial preserves exact counts: invert the adapted candidate matrix
and discard precisely the extensions of unrealized old words. -/
theorem refineCounts_eq_signCount (Z : Finset R) (Q : Fin n → R[X]) (q : R[X])
    (c : (Fin n → SignType) → ℚ) (hc : ∀ σ, c σ = (Z.signCount Q σ : ℚ))
    (σ : Fin (n + 1) → SignType) :
    refineCounts (fun p => (Z.signSum p : ℚ)) Q q c σ =
      (Z.signCount (Fin.cons q Q) σ : ℚ) := by
  classical
  by_cases h : 0 < c (Fin.tail σ)
  · have hm := Z.inv_fullMatrix_submatrix_mulVec_signSum (Fin.cons q Q)
      (fun a : {τ // 0 < c τ} × SignType => Fin.cons (α := fun _ => SignType) a.2 a.1.val)
      (extensionRows c)
      (extension_columns_injective c) (extension_columns_cover Z Q q c hc)
      (isUnit_extensionRows c)
    simpa only [refineCounts, dite_eq_left h, Fin.cons_self_tail] using
      congrFun hm (⟨Fin.tail σ, h⟩, σ 0)
  · rw [refineCounts_eq_zero _ _ _ _ _ h]
    suffices hz : Z.signCount (Fin.cons q Q) σ = 0 by simp [hz]
    apply Nat.eq_zero_of_not_pos
    intro hpos
    obtain ⟨x, hx, hs⟩ := (Finset.signCount_pos _ _ _).mp hpos
    apply h
    rw [hc, Nat.cast_pos]
    exact (Finset.signCount_pos Z Q _).mpr
      ⟨x, hx, fun j => by simpa only [Fin.cons_succ, Fin.tail_def] using hs j.succ⟩

/-- Splitting an old sign word by the new polynomial preserves its total count. -/
theorem sum_refineCounts_cons (Z : Finset R) (Q : Fin n → R[X]) (q : R[X])
    (c : (Fin n → SignType) → ℚ) (hc : ∀ σ, c σ = (Z.signCount Q σ : ℚ))
    (τ : Fin n → SignType) :
    ∑ s : SignType, refineCounts (fun p => (Z.signSum p : ℚ)) Q q c (Fin.cons s τ) =
      c τ := by
  classical
  simp only [refineCounts_eq_signCount Z Q q c hc, hc, ← Nat.cast_sum]
  congr 1
  simp only [Finset.signCount_eq_card_filter]
  have hcard := Finset.card_eq_sum_card_fiberwise
    (s := Z.filter fun x => ∀ j, SignType.sign ((Q j).eval x) = τ j)
    (t := Finset.univ) (f := fun x => SignType.sign (q.eval x))
    (fun _ _ => Finset.mem_univ _)
  convert hcard.symm using 1
  · simp [Finset.filter_filter, Fin.forall_fin_succ, and_comm]
  · congr 1
    ext x
    simp

/-- The recursive adapted-query procedure returns every exact sign count on a finite sample.
No nonzero, squarefree, or distinct-polynomial hypothesis is needed. -/
theorem determineSigns_eq_signCount (Z : Finset R) (n : ℕ) (Q : Fin n → R[X])
    (σ : Fin n → SignType) :
    determineSigns (fun p => (Z.signSum p : ℚ)) n Q σ = (Z.signCount Q σ : ℚ) := by
  induction n with
  | zero => simp [Finset.signCount_eq_card_filter]
  | succ n ih =>
    rw [determineSigns_succ, refineCounts_eq_signCount Z _ _ _ (ih _)]
    simp

/-- Positive recursive output entries characterize exactly the realized sign words. -/
@[simp]
theorem determineSigns_pos_iff (Z : Finset R) (Q : Fin n → R[X]) (σ : Fin n → SignType) :
    0 < determineSigns (fun p => (Z.signSum p : ℚ)) n Q σ ↔
      ∃ x ∈ Z, ∀ j, SignType.sign ((Q j).eval x) = σ j := by
  rw [determineSigns_eq_signCount, Nat.cast_pos, Finset.signCount_pos]

/-- Tarski queries as the oracle give the exact counts at distinct polynomial roots.
For a zero root polynomial the result is the zero table. -/
theorem determineSigns_tarskiQuery (p : R[X]) (Q : Fin n → R[X])
    (σ : Fin n → SignType) :
    determineSigns (fun q => (tarskiQuery p q : ℚ)) n Q σ =
      (p.roots.toFinset.signCount Q σ : ℚ) := by
  simpa only [tarskiQuery_eq_signSum] using determineSigns_eq_signCount p.roots.toFinset n Q σ

/-- For a nonzero root polynomial, positive output entries are exactly the sign conditions
realized by its zeros, including repeated roots and zero query values. -/
theorem determineSigns_tarskiQuery_pos_iff (p : R[X]) (hp : p ≠ 0) (Q : Fin n → R[X])
    (σ : Fin n → SignType) :
    0 < determineSigns (fun q => (tarskiQuery p q : ℚ)) n Q σ ↔
      ∃ x, p.eval x = 0 ∧ ∀ j, SignType.sign ((Q j).eval x) = σ j := by
  rw [determineSigns_tarskiQuery, Nat.cast_pos, signCount_roots_pos hp]

end Correctness

end TauCeti.SignDetermination
