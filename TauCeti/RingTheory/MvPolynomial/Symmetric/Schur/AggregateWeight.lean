/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Basic
import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Symmetric

/-!
# Aggregate weights of bounded semistandard tableaux

Across all tableaux of a fixed shape, each letter occurs equally often. The same holds for
families of tableaux, allowing a different shape in each member of the family. This computes
the total degree in one row of variables across the standard bideterminant coordinates,
including when those coordinates are replicated over classes of algebraic modular forms.

The argument uses the Bender–Knuth involution via `TauCeti.BoundedSSYT.weight_benderKnuth`.
-/

public section

open Finset

namespace TauCeti.BoundedSSYT

/-- The total number of occurrences of a letter across all bounded tableaux of a shape is
independent of the letter. -/
theorem sum_weight_apply_eq {N : ℕ} {μ : YoungDiagram} (a b : Fin N) :
    ∑ T : BoundedSSYT N μ, T.weight a = ∑ T : BoundedSSYT N μ, T.weight b := by
  cases N with
  | zero => exact a.elim0
  | succ n =>
    let S (i : Fin (n + 1)) := ∑ T : BoundedSSYT (n + 1) μ, T.weight i
    have hstep (i : Fin n) : S i.castSucc = S i.succ := by
      have hi : (i.succ : ℕ) = (i.castSucc : ℕ) + 1 := rfl
      exact Fintype.sum_bijective (fun T ↦ T.benderKnuth hi)
        (benderKnuth_involutive _ _ hi).bijective _ _ (fun T ↦ by
          rw [weight_benderKnuth, Equiv.swap_apply_right])
    have hall (i : Fin (n + 1)) : S i = S 0 :=
      Fin.induction rfl (fun j hj ↦ (hstep j).symm.trans hj) i
    exact (hall a).trans (hall b).symm

/-- Multiplying the total occurrence count for one letter by the alphabet size counts all
cells across all tableaux of the shape. -/
theorem card_mul_sum_weight_apply {N : ℕ} {μ : YoungDiagram} (a : Fin N) :
    N * (∑ T : BoundedSSYT N μ, T.weight a) = Fintype.card (BoundedSSYT N μ) * μ.card := by
  calc
    _ = ∑ j : Fin N, ∑ T : BoundedSSYT N μ, T.weight j := by
      simp only [sum_weight_apply_eq _ a, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_id]
    _ = ∑ T : BoundedSSYT N μ, ∑ j : Fin N, T.weight j := sum_comm
    _ = _ := by simp only [sum_weight, sum_const, card_univ, nsmul_eq_mul, Nat.cast_id]

/-- For one coordinate indexed by a class `c` and a tableau at each place, its degree in
letter `a` is the sum of the local weights at `a`. Across all coordinates this total,
multiplied by the alphabet size, equals the number of coordinates times the total size of
the shapes. -/
theorem card_mul_sum_prod_sum_weight_apply {C σ : Type*} [Fintype C] [Fintype σ] [DecidableEq σ]
    {N : ℕ} (μ : σ → YoungDiagram) (a : Fin N) :
    N * (∑ v : C × (∀ w, BoundedSSYT N (μ w)), ∑ w, (v.2 w).weight a) =
      Fintype.card (C × (∀ w, BoundedSSYT N (μ w))) * ∑ w, (μ w).card := by
  let K := C × (∀ w, BoundedSSYT N (μ w))
  have h (w : σ) : N * (∑ v : K, (v.2 w).weight a) = Fintype.card K * (μ w).card := by
    let U := ∀ u : {u // u ≠ w}, BoundedSSYT N (μ u)
    let e : K ≃ C × (BoundedSSYT N (μ w) × U) :=
      (Equiv.refl C).prodCongr (Equiv.piSplitAt w (fun w ↦ BoundedSSYT N (μ w)))
    have hsplit : (∑ v : K, (v.2 w).weight a) =
        ∑ v : C × (BoundedSSYT N (μ w) × U), v.2.1.weight a :=
      Fintype.sum_equiv e _ _ fun _ ↦ rfl
    rw [hsplit, Fintype.card_congr e]
    simp only [Fintype.sum_prod_type, sum_const, card_univ, nsmul_eq_mul, Nat.cast_id,
      ← mul_sum, Fintype.card_prod]
    calc
      _ = Fintype.card C * Fintype.card U * (N * ∑ T : BoundedSSYT N (μ w), T.weight a) :=
        by ac_rfl
      _ = _ := by rw [card_mul_sum_weight_apply]; ac_rfl
  calc
    _ = ∑ w, N * ∑ v : K, (v.2 w).weight a := by rw [← mul_sum, sum_comm]
    _ = ∑ w, Fintype.card K * (μ w).card := sum_congr rfl fun w _ ↦ h w
    _ = _ := by rw [← mul_sum]

end TauCeti.BoundedSSYT
