/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
import TauCeti.LinearAlgebra.Matrix.Charpoly.Roots

/-!
# Ordered eigenvalues of a unitary diagonalization

A decreasing real diagonal is recovered from the ordered eigenvalues of any of its unitary
conjugates. This is the ordered diagonal coordinate in the spectral change of variables of
Anderson, Guionnet and Zeitouni, *An Introduction to Random Matrices* (2010), §4.1.
-/

public section

open Polynomial

namespace Matrix

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

end Matrix
