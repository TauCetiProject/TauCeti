/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Matrix.IsDiag
import TauCeti.LinearAlgebra.Matrix.Diagonal

/-!
# Ambiguities in spectral diagonalization

For a diagonal with distinct entries, two unitary frames give the same conjugate exactly
when their relative frame is diagonal. This is the sign ambiguity for orthogonal frames
and the phase ambiguity for complex unitary frames. The diagonal itself is determined by
the characteristic polynomial up to permutation, and the fiber of a simple diagonal
has cardinality `n!`.

These are the algebraic fibers of the spectral change of variables in
Anderson, Guionnet and Zeitouni, *An Introduction to Random Matrices* (2010), §4.1.
-/

public section

noncomputable section

open Polynomial

namespace Matrix

section Unitary

variable {ι R : Type*} [Fintype ι] [DecidableEq ι]
  [CommRing R] [IsLeftCancelMulZero R] [StarRing R]

/-- A diagonal with distinct entries has exactly the diagonal unitary frames in its stabilizer. -/
theorem conjStarAlgAut_diagonal_eq_iff {d : ι → R} (hd : Function.Injective d)
    (U : unitaryGroup ι R) :
    Unitary.conjStarAlgAut ℕ _ U (diagonal d) = diagonal d ↔ Matrix.IsDiag (U : Matrix ι ι R) := by
  rw [Unitary.conjStarAlgAut_apply]
  constructor
  · intro h
    apply TauCeti.isDiag_of_commute_diagonal hd
    calc
      diagonal d * (U : Matrix ι ι R) = (U * diagonal d * (star U : Matrix ι ι R)) * U := by rw [h]
      _ = U * diagonal d := by simp [Matrix.mul_assoc]
  · intro h
    have hcomm : Commute (U : Matrix ι ι R) (diagonal d) := by
      rw [← h.diagonal_diag]
      simp only [Commute, SemiconjBy, diagonal_mul_diagonal]
      congr 1
      funext i
      exact mul_comm _ _
    rw [hcomm.eq]
    simp [Matrix.mul_assoc]

/-- Two frames give the same conjugate of a simple diagonal exactly when they differ
by a right diagonal unitary. -/
theorem conjStarAlgAut_diagonal_eq_conjStarAlgAut_iff {d : ι → R} (hd : Function.Injective d)
    (U V : unitaryGroup ι R) :
    Unitary.conjStarAlgAut ℕ _ U (diagonal d) = Unitary.conjStarAlgAut ℕ _ V (diagonal d) ↔
      Matrix.IsDiag ((star V * U : unitaryGroup ι R) : Matrix ι ι R) := by
  rw [← conjStarAlgAut_diagonal_eq_iff hd, Unitary.conjStarAlgAut_mul_apply]
  have hV : Unitary.conjStarAlgAut ℕ (Matrix ι ι R) (star V)
      (Unitary.conjStarAlgAut ℕ _ V (diagonal d)) = diagonal d := by
    rw [← Unitary.conjStarAlgAut_mul_apply]
    simp
  conv_rhs => rhs; rw [← hV]
  exact (Unitary.conjStarAlgAut ℕ (Matrix ι ι R) (star V)).injective.eq_iff.symm

end Unitary

section Fiber

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [IsDomain R]

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
def permEquivDiagonalCharpolyFiber (d : ι → R) (hd : Function.Injective d) :
    Equiv.Perm ι ≃ {e : ι → R // (diagonal e).charpoly = (diagonal d).charpoly} := by
  let f (σ : Equiv.Perm ι) : {e : ι → R // (diagonal e).charpoly = (diagonal d).charpoly} :=
    ⟨d ∘ σ, by
      simp only [charpoly_diagonal, Function.comp_apply]
      exact Equiv.prod_comp σ (fun i ↦ X - C (d i))⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro σ τ h
    exact Equiv.ext fun i ↦ hd (congrFun (congrArg Subtype.val h) i)
  · intro ⟨e, he⟩
    have hr := congrArg roots he
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
    (permEquivDiagonalCharpolyFiber d hd σ).val i = d (σ i) := (rfl)

/-- A diagonal with distinct entries has exactly `card ι !` orderings of its spectrum. -/
theorem natCard_diagonalCharpolyFiber (d : ι → R) (hd : Function.Injective d) :
    Nat.card {e : ι → R // (diagonal e).charpoly = (diagonal d).charpoly} =
      (Fintype.card ι).factorial := by
  rw [← Nat.card_congr (permEquivDiagonalCharpolyFiber d hd), Nat.card_eq_fintype_card,
    Fintype.card_perm]

end Fiber

section Ordered

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

/-- The decreasing ordering of a real Hermitian diagonal is the ordered eigenvalue vector
of every unitary conjugate of that diagonal. -/
theorem eigenvalues₀_conjStarAlgAut_diagonal (U : unitaryGroup (Fin n) 𝕜) {d : Fin n → ℝ}
    (hd : Antitone d) (hA : (Unitary.conjStarAlgAut ℝ _ U
      (diagonal fun i ↦ (d i : 𝕜))).IsHermitian) :
    hA.eigenvalues₀ = d ∘ Fin.cast (Fintype.card_fin n) := by
  let D := diagonal fun i : Fin n ↦ (d i : 𝕜)
  have hC : (Unitary.conjStarAlgAut ℝ _ U D).charpoly = D.charpoly := by
    rw [Unitary.conjStarAlgAut_apply, ← inv_eq_left_inv (Unitary.coe_star_mul_self U)]
    exact charpoly_units_conj (Unitary.toUnits U) D
  rw [← List.ofFn_inj, ← hA.sort_roots_charpoly_eq_eigenvalues₀, hC,
    roots_charpoly_diagonal, Multiset.map_map]
  have hmap : (Finset.univ.val.map (RCLike.re ∘ fun i ↦ (d i : 𝕜))) =
      (List.ofFn d : Multiset ℝ) := by
    simp [Fin.univ_val_map]
  rw [hmap, List.ofFn_congr (Fintype.card_fin n).symm d, Multiset.coe_sort]
  exact List.mergeSort_of_pairwise (by
    simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
    have hm : Monotone (Fin.cast (Fintype.card_fin n)) := fun _ _ h ↦ h
    exact (hd.comp_monotone hm).sortedGE_ofFn)

end Ordered

end Matrix
