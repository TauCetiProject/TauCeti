/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.TreeWalk.Leading
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Products along double-traversal tree walks

Each edge of a closed tree walk is traversed once in each direction. Grouping the factors
of a commutative product by these edges pairs each factor with its reverse. In particular,
a product of entries of a Hermitian matrix becomes a product of squared absolute values.
This is the deterministic factorization underlying the leading terms of Wigner moments.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.3, proof of Lemma 2.1.6.
-/

public section

open Finset

namespace TauCeti.TreeWalk.IsTreeWalk

variable {k : ℕ} {w : ℕ → ℕ} (hw : IsTreeWalk k w)
include hw

private theorem reverse_step_of_edge_eq {i j : ℕ} (hi : i < 2 * k) (hj : j < 2 * k)
    (hup : w (i + 1) = i + 1) (hne : j ≠ i)
    (he : s(w j, w (j + 1)) = s(w i, w (i + 1))) :
    w j = i + 1 ∧ w (j + 1) = w i := by
  rcases Sym2.eq_iff.mp he with h | h
  · by_cases hjup : w (j + 1) = j + 1
    · omega
    · have hd := hw.step_down hj hjup
      have hu := depth_succ_of_le (hw.le_self i hi.le)
      rw [h.1, h.2, hup] at hd
      omega
  · exact ⟨h.1.trans hup, h.2⟩

/-- An edge discovered at step `i` has precisely two occurrences: step `i` and a unique
return step, with the opposite orientation. -/
theorem edge_fiber_eq_pair {i : ℕ} (hi : i < 2 * k) (hup : w (i + 1) = i + 1) :
    ∃ j < 2 * k, w j = i + 1 ∧ w (j + 1) = w i ∧
      {t ∈ range (2 * k) | s(w t, w (t + 1)) = s(w i, w (i + 1))} = {i, j} := by
  let S := {t ∈ range (2 * k) | s(w t, w (t + 1)) = s(w i, w (i + 1))}
  have hiS : i ∈ S := by simp [S, hi]
  obtain ⟨a, b, hab, hS⟩ := card_eq_two.mp (hw.card_edge i hi)
  have hS' : S = {a, b} := hS
  have hj : ∃ j, j ≠ i ∧ S = {i, j} := by
    rw [hS'] at hiS
    simp only [mem_insert, mem_singleton] at hiS
    rcases hiS with rfl | rfl
    · exact ⟨b, hab.symm, hS'⟩
    · exact ⟨a, hab, hS'.trans (pair_comm _ _)⟩
  obtain ⟨j, hji, hpair⟩ := hj
  have hjS : j ∈ S := by rw [hpair]; simp
  obtain ⟨hj, he⟩ := mem_filter.mp hjS
  obtain ⟨h₁, h₂⟩ := hw.reverse_step_of_edge_eq hi (mem_range.mp hj) hup hji he
  exact ⟨j, mem_range.mp hj, h₁, h₂, hpair⟩

/-- A commutative product along a tree walk is the product over discovery steps of the
forward and backward factors for that edge. This includes the empty walk. -/
theorem prod_eq_prod_up_mul_reverse {M : Type*} [CommMonoid M] (a : ℕ → ℕ → M) :
    ∏ i ∈ range (2 * k), a (w i) (w (i + 1)) =
      ∏ i ∈ range (2 * k) with w (i + 1) = i + 1,
        a (w i) (i + 1) * a (i + 1) (w i) := by
  let e : ℕ → Sym2 ℕ := fun i ↦ s(w i, w (i + 1))
  let E := (range (2 * k)).image e
  have hgroup := prod_fiberwise_of_maps_to
    (s := range (2 * k)) (t := E) (g := e)
    (fun i hi ↦ mem_image_of_mem e hi) (fun i ↦ a (w i) (w (i + 1)))
  rw [← hgroup]
  symm
  refine prod_bij (fun i _ ↦ e i) ?_ ?_ ?_ ?_
  · intro i hi
    exact mem_image_of_mem e (mem_filter.mp hi).1
  · intro i hi j hj he
    have hi' := mem_filter.mp hi
    have hj' := mem_filter.mp hj
    have hli := hw.le_self i (mem_range.mp hi'.1).le
    have hlj := hw.le_self j (mem_range.mp hj'.1).le
    have h := Sym2.eq_iff.mp he
    simp only [hi'.2, hj'.2] at h
    omega
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hx
    obtain ⟨i, hi, hup, he⟩ := hw.exists_up_edge (mem_range.mp hj)
    exact ⟨i, mem_filter.mpr ⟨mem_range.mpr hi, hup⟩, by simpa [e, hup] using he.symm⟩
  · intro i hi
    obtain ⟨hi, hup⟩ := mem_filter.mp hi
    obtain ⟨j, hj, h₁, h₂, hpair⟩ := hw.edge_fiber_eq_pair (mem_range.mp hi) hup
    have hne : i ≠ j := by
      intro hij
      subst j
      have hle := hw.le_self i (mem_range.mp hi).le
      omega
    dsimp only [e]
    rw [hpair, prod_pair hne, hup, h₁, h₂]

end TauCeti.TreeWalk.IsTreeWalk

namespace TauCeti.TreeWalk

variable {α M : Type*} [DecidableEq α] [CommMonoid M] {m : ℕ}

/-- A product along a closed path with `m + 1` vertices and every edge traversed twice
factors into forward-backward pairs, indexed by first discoveries. Vertices may have arbitrary
labels. The path of length zero contributes the empty product. -/
theorem prod_path_eq_prod_up_mul_reverse (v : Fin (2 * m + 1) → α)
    (hclosed : v (Fin.last (2 * m)) = v 0) (hv : #(univ.image v) = m + 1)
    (he : ∀ i : Fin (2 * m),
      #{j : Fin (2 * m) | s(v j.castSucc, v j.succ) = s(v i.castSucc, v i.succ)} = 2)
    (a : α → α → M) :
    ∏ i : Fin (2 * m), a (v i.castSucc) (v i.succ) =
      ∏ i : Fin (2 * m) with canonicalWalk v i.succ = i.succ,
        a (v i.castSucc) (v i.succ) * a (v i.succ) (v i.castSucc) := by
  let f : ℕ → α := fun i ↦ v (Fin.ofNat (2 * m + 1) i)
  have hw := isTreeWalk_canonicalWalk v hclosed hv he
  have hfc (i : Fin (2 * m + 1)) : f (canonicalWalk v i) = v i := by
    have hc : canonicalWalk v i < 2 * m + 1 := (canonicalWalk_le v i).trans_lt i.isLt
    have h := (canonicalWalk_eq_iff v ⟨canonicalWalk v i, hc⟩ i).mp (canonicalWalk_idem v i)
    calc
      f (canonicalWalk v i) = v ⟨canonicalWalk v i, hc⟩ := by
        apply congrArg v
        apply Fin.ext
        simp only [Fin.val_ofNat, Nat.mod_eq_of_lt hc]
      _ = v i := h
  have h := hw.prod_eq_prod_up_mul_reverse (fun i j ↦ a (f i) (f j))
  have hleft : (∏ i : Fin (2 * m), a (v i.castSucc) (v i.succ)) =
      ∏ i ∈ range (2 * m), a (f (canonicalWalk v i)) (f (canonicalWalk v (i + 1))) := by
    rw [← Fin.prod_univ_eq_prod_range]
    exact prod_congr rfl fun i _ ↦ (congrArg₂ a (hfc i.castSucc) (hfc i.succ)).symm
  rw [hleft, h]
  rw [prod_filter, prod_filter, ← Fin.prod_univ_eq_prod_range]
  apply prod_congr rfl
  intro i _
  simp only [Fin.val_succ]
  split_ifs with hi
  · have hi' : f (i + 1) = v i.succ := by
      rw [← hi]
      exact hfc i.succ
    exact congrArg₂ (fun x y ↦ a x y * a y x) (hfc i.castSucc) hi'
  · rfl

end TauCeti.TreeWalk
