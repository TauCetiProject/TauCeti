/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.TreeWalk.Leading

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
  · exact fun i hi j hj he ↦ hw.injOn_edge_up hi hj he
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hx
    obtain ⟨i, hi, hup, he⟩ := hw.exists_up_edge (mem_range.mp hj)
    exact ⟨i, mem_filter.mpr ⟨mem_range.mpr hi, hup⟩, by simpa [e, hup] using he.symm⟩
  · intro i hi
    obtain ⟨hi, hup⟩ := mem_filter.mp hi
    obtain ⟨j, hj, h₁, h₂, hpair⟩ := hw.exists_edge_fiber_eq_pair (mem_range.mp hi) hup
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

/-- A product along a leading cyclic word factors into forward-backward pairs, indexed by
the discovery steps of its path extension. -/
theorem prod_cyclic_eq_prod_up_mul_reverse [NeZero m] (w : Fin (2 * m) → α)
    (h : ∀ i, ∃ j ≠ i, s(w j, w (finRotate (2 * m) j)) = s(w i, w (finRotate (2 * m) i)))
    (hv : #(univ.image w) = m + 1) (a : α → α → M) :
    ∏ i : Fin (2 * m), a (w i) (w (finRotate (2 * m) i)) =
      ∏ i : Fin (2 * m) with canonicalWalk (cyclicPath w) i.succ = i.succ,
        a (w i) (w (finRotate (2 * m) i)) * a (w (finRotate (2 * m) i)) (w i) := by
  simpa only [cyclicPath_castSucc, cyclicPath_succ] using
    prod_path_eq_prod_up_mul_reverse (cyclicPath w) (by simp) (by simpa using hv)
      (card_edge_fiber_cyclicPath w h hv) a

end TauCeti.TreeWalk
