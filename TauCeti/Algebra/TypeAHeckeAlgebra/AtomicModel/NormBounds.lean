/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Basic
import TauCeti.Analysis.Normed.Module.Finsupp

/-!
# Norm bounds for the signed checked representation

Over any normed commutative ring `R`, the matrix entries `signedChecked pos q x (single w 1) u`
of an element `x` of the type-A Hecke algebra are uniformly bounded over all words `w, u`
(`TauCeti.TypeAHeckeAlgebra.exists_norm_signedChecked_single_apply_le`).

## Main results

* `TauCeti.TypeAHeckeAlgebra.exists_norm_signedChecked_single_apply_le`: uniform matrix-entry
  bound for `signedChecked`.
-/

public section

open Finsupp

namespace TauCeti.TypeAHeckeAlgebra

variable {R : Type*} [NormedCommRing R] {ι : Type*} [LinearOrder ι] (pos : ι → Prop)
  [DecidablePred pos] (q : Rˣ) {n : ℕ}

/-- **Uniform matrix-entry bound for `signedChecked`** across all words `w, u : Fin n → ι`. -/
theorem exists_norm_signedChecked_single_apply_le (x : TypeAHeckeAlgebra R q n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w u : Fin n → ι, ‖signedChecked pos q x (single w 1) u‖ ≤ C := by
  suffices h : ∃ B : ℝ, 0 ≤ B ∧
      ∀ w : Fin n → ι, (signedChecked pos q x (single w 1)).sum (fun _ r ↦ ‖r‖) ≤ B by
    obtain ⟨B, hB0, hB⟩ := h
    exact ⟨B, hB0, fun w u ↦ (Finsupp.norm_apply_le_sum_norm _ u).trans (hB w)⟩
  have h1 (u : Fin n → ι) : (single u (1 : R)).sum (fun _ r ↦ ‖r‖) ≤ ‖(1 : R)‖ := by
    simp [Finsupp.sum_single_index]
  have hs (r : R) (u : Fin n → ι) : (r • single u (1 : R)).sum (fun _ c ↦ ‖c‖) ≤ ‖r‖ * ‖(1 : R)‖ :=
    (Finsupp.sum_norm_smul_le r _).trans (mul_le_mul_of_nonneg_left (h1 u) (norm_nonneg _))
  have hx : x ∈ Algebra.adjoin R (Set.range (T (n := n) q)) := by rw [adjoin_range_T]; trivial
  induction hx using Algebra.adjoin_induction with
  | mem _ hy =>
    obtain ⟨i, rfl⟩ := hy
    set B₀ := ‖(q : R) ^ 2‖ + 1 + ‖(q : R) ^ 2 - 1‖ + ‖(q : R)‖
    refine ⟨‖((q⁻¹ : Rˣ) : R)‖ * (B₀ * ‖(1 : R)‖), by positivity, fun w ↦ ?_⟩
    rw [signedChecked_T, LinearMap.smul_apply]
    refine (Finsupp.sum_norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    rw [signedCheckedR_single_one]
    have := norm_nonneg (1 : R); have := norm_nonneg ((q : R) ^ 2)
    have := norm_nonneg ((q : R) ^ 2 - 1); have := norm_nonneg (q : R)
    split_ifs
    · exact (hs _ w).trans (by nlinarith)
    · rw [neg_smul, one_smul, Finsupp.sum_norm_neg]; exact (h1 w).trans (by nlinarith)
    · rw [sub_eq_add_neg]
      refine (Finsupp.sum_norm_add_le _ _).trans ?_
      rw [Finsupp.sum_norm_neg]; exact (add_le_add (hs _ _) (hs _ _)).trans (by nlinarith)
    · rw [Finsupp.sum_norm_neg]; exact (hs _ _).trans (by nlinarith)
  | algebraMap r =>
    exact ⟨‖r‖ * ‖(1 : R)‖, by positivity, fun w ↦ by
      rw [AlgHom.commutes, Module.algebraMap_end_apply]; exact hs r w⟩
  | add _ _ _ _ hx hy =>
    obtain ⟨Bx, hBx0, hBx⟩ := hx; obtain ⟨By, hBy0, hBy⟩ := hy
    exact ⟨Bx + By, add_nonneg hBx0 hBy0, fun w ↦ by
      rw [map_add, LinearMap.add_apply]
      exact (Finsupp.sum_norm_add_le _ _).trans (add_le_add (hBx w) (hBy w))⟩
  | mul _ _ _ _ hx hy =>
    obtain ⟨Bx, hBx0, hBx⟩ := hx; obtain ⟨By, hBy0, hBy⟩ := hy
    exact ⟨Bx * By, mul_nonneg hBx0 hBy0, fun w ↦ by
      rw [map_mul, mul_apply_eq_comp]
      exact (LinearMap.sum_norm_apply_le _ hBx _).trans (mul_le_mul_of_nonneg_left (hBy w) hBx0)⟩

end TauCeti.TypeAHeckeAlgebra
