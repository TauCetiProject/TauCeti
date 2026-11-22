/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Characteristic roots of diagonal matrices

Over an integral domain, the characteristic roots of a diagonal matrix are its diagonal entries,
counted with multiplicity. A diagonal with distinct entries is therefore determined by its
characteristic polynomial up to permutation, with one diagonal for each permutation. This gives
the multiplicity `n!` in the spectral change of variables of Anderson, Guionnet and Zeitouni,
*An Introduction to Random Matrices* (2010), §4.1.

## Main results

* `Matrix.roots_charpoly_diagonal` — the characteristic roots of a diagonal are its entries.
* `Matrix.diagonalCharpolyFiber` — the diagonals with the same characteristic polynomial as a
  given diagonal.
* `Matrix.permEquivDiagonalCharpolyFiber` — permutations parametrize that fiber when the given
  diagonal is simple.
* `Matrix.natCard_diagonalCharpolyFiber` — that fiber has `card ι !` elements.
-/

public section

open Polynomial

namespace Matrix

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The diagonals whose diagonal matrix has the same characteristic polynomial as that of `d`. -/
def diagonalCharpolyFiber (d : ι → R) : Set (ι → R) :=
  {e | (diagonal e).charpoly = (diagonal d).charpoly}

/-- Membership in the fiber is equality of characteristic polynomials of the diagonal matrices. -/
@[simp] theorem mem_diagonalCharpolyFiber {d e : ι → R} :
    e ∈ diagonalCharpolyFiber d ↔ (diagonal e).charpoly = (diagonal d).charpoly :=
  Iff.rfl

variable [IsDomain R]

/-- The characteristic roots of a diagonal matrix are its diagonal entries with multiplicity. -/
theorem roots_charpoly_diagonal (d : ι → R) :
    (diagonal d).charpoly.roots = Finset.univ.val.map d := by
  rw [charpoly_diagonal, roots_prod]
  · simp
  · exact Finset.prod_ne_zero_iff.mpr fun _ _ ↦ X_sub_C_ne_zero _

private theorem injective_of_roots_charpoly_diagonal_eq {d e : ι → R} (hd : Function.Injective d)
    (h : (diagonal e).charpoly.roots = (diagonal d).charpoly.roots) : Function.Injective e := by
  simp only [roots_charpoly_diagonal] at h
  have hn : (Finset.univ.val.map e).Nodup := h ▸ (Finset.univ.nodup.map hd)
  exact fun i j hij ↦ Multiset.inj_on_of_nodup_map hn i (by simp) j (by simp) hij

/-- All diagonals with the same characteristic polynomial as a simple diagonal
are its permutations, with a unique permutation for each diagonal. -/
noncomputable def permEquivDiagonalCharpolyFiber (d : ι → R) (hd : Function.Injective d) :
    Equiv.Perm ι ≃ diagonalCharpolyFiber d := by
  let f (σ : Equiv.Perm ι) : diagonalCharpolyFiber d :=
    ⟨d ∘ σ, by
      simp only [mem_diagonalCharpolyFiber, charpoly_diagonal, Function.comp_apply]
      exact Equiv.prod_comp σ (fun i ↦ X - C (d i))⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro σ τ h
    exact Equiv.ext fun i ↦ hd (congrFun (congrArg Subtype.val h) i)
  · intro ⟨e, he⟩
    have hr := congrArg roots (mem_diagonalCharpolyFiber.mp he)
    have hi := injective_of_roots_charpoly_diagonal_eq hd hr
    have hmem (i : ι) : e i ∈ Set.range d := by
      have h : e i ∈ (diagonal e).charpoly.roots := by simp [roots_charpoly_diagonal]
      rw [hr, roots_charpoly_diagonal] at h
      simpa using h
    choose σ hσ using hmem
    have hs : Function.Injective σ := fun i j hij ↦ hi (by rw [← hσ i, ← hσ j, hij])
    exact ⟨Equiv.ofBijective σ ⟨hs, Finite.surjective_of_injective hs⟩,
      Subtype.ext (funext hσ)⟩

/-- The permutation-to-diagonal map evaluates the original diagonal at permuted indices. -/
@[simp] theorem permEquivDiagonalCharpolyFiber_apply (d : ι → R) (hd : Function.Injective d)
    (σ : Equiv.Perm ι) (i : ι) :
    (permEquivDiagonalCharpolyFiber d hd σ : ι → R) i = d (σ i) := (rfl)

/-- A diagonal with distinct entries has exactly `card ι !` orderings of its spectrum. -/
theorem natCard_diagonalCharpolyFiber (d : ι → R) (hd : Function.Injective d) :
    Nat.card (diagonalCharpolyFiber d) = (Fintype.card ι).factorial := by
  rw [← Nat.card_congr (permEquivDiagonalCharpolyFiber d hd), Nat.card_eq_fintype_card,
    Fintype.card_perm]

end Matrix
