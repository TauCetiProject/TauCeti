/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-!
# Diagonal quadratic forms

This file provides general infrastructure for diagonal quadratic forms expressed as weighted sums
of squares.

## Main results

* `TauCeti.equivalent_weightedSumSquares_comp`: reindexing the coefficients preserves equivalence.
* `TauCeti.equivalent_weightedSumSquares_of_pair`: a binary equivalence extends across fixed
  coordinates.
-/

public section

namespace TauCeti

universe u v

open QuadraticMap

section PairExtension

variable {R : Type u} [CommSemiring R] {n : ℕ}
variable {w w' : Fin n → R} {i j : Fin n}

private def replacePair (f : (Fin 2 → R) → (Fin 2 → R)) (i j : Fin n)
    (x : Fin n → R) (k : Fin n) : R :=
  if k = i then f ![x i, x j] 0 else if k = j then f ![x i, x j] 1 else x k

omit [CommSemiring R] in
private theorem replacePair_apply_left (f : (Fin 2 → R) → (Fin 2 → R))
    (i j : Fin n) (x : Fin n → R) : replacePair f i j x i = f ![x i, x j] 0 := by
  simp [replacePair]

omit [CommSemiring R] in
private theorem replacePair_apply_right (f : (Fin 2 → R) → (Fin 2 → R))
    (hij : i ≠ j) (x : Fin n → R) : replacePair f i j x j = f ![x i, x j] 1 := by
  simp [replacePair, hij.symm]

omit [CommSemiring R] in
private theorem finTwo_eta (v : Fin 2 → R) : ![v 0, v 1] = v := by
  ext k
  fin_cases k <;> rfl

omit [CommSemiring R] in
private theorem replacePair_comp (f g : (Fin 2 → R) → (Fin 2 → R))
    (hfg : Function.LeftInverse f g) (hij : i ≠ j) (x : Fin n → R) :
    replacePair f i j (replacePair g i j x) = x := by
  funext k
  by_cases hki : k = i
  · subst k
    simp only [replacePair_apply_left,
      replacePair_apply_right (f := g) (i := i) (j := j) hij]
    rw [finTwo_eta, hfg]
    rfl
  by_cases hkj : k = j
  · subst k
    simp only [replacePair_apply_right (f := f) (i := i) (j := j) hij,
      replacePair_apply_left, replacePair_apply_right (f := g) (i := i) (j := j) hij]
    rw [finTwo_eta, hfg]
    rfl
  · simp [replacePair, hki, hkj]

private def pairLinearEquiv (hij : i ≠ j)
    (e : (weightedSumSquares R ![w i, w j]).IsometryEquiv
      (weightedSumSquares R ![w' i, w' j])) :
    (Fin n → R) ≃ₗ[R] (Fin n → R) where
  toFun := replacePair e i j
  invFun := replacePair e.symm i j
  left_inv := replacePair_comp e.symm e e.symm_apply_apply hij
  right_inv := replacePair_comp e e.symm e.apply_symm_apply hij
  map_add' x y := by
    funext k
    by_cases hki : k = i
    · subst k
      simpa [replacePair, hij, hij.symm] using
        congrFun (map_add e ![x i, x j] ![y i, y j]) 0
    by_cases hkj : k = j
    · subst k
      simpa [replacePair, hij, hij.symm] using
        congrFun (map_add e ![x i, x j] ![y i, y j]) 1
    · simp [replacePair, hki, hkj]
  map_smul' a x := by
    funext k
    by_cases hki : k = i
    · subst k
      simpa [replacePair, hij, hij.symm] using
        congrFun (map_smul e a ![x i, x j]) 0
    by_cases hkj : k = j
    · subst k
      simpa [replacePair, hij, hij.symm] using
        congrFun (map_smul e a ![x i, x j]) 1
    · simp [replacePair, hki, hkj]

private theorem sum_pair_add_rest (f : Fin n → R) (hij : i ≠ j) :
    ∑ k, f k = f i + f j + ∑ k ∈ (Finset.univ.erase i).erase j, f k := by
  calc
    ∑ k, f k = f i + ∑ k ∈ Finset.univ.erase i, f k :=
      (Finset.add_sum_erase Finset.univ f (Finset.mem_univ i)).symm
    _ = f i + (f j + ∑ k ∈ (Finset.univ.erase i).erase j, f k) := by
      rw [Finset.add_sum_erase (Finset.univ.erase i) f
        (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)]
    _ = _ := by ac_rfl

private def pairIsometryEquiv (hij : i ≠ j)
    (e : (weightedSumSquares R ![w i, w j]).IsometryEquiv
      (weightedSumSquares R ![w' i, w' j]))
    (hrest : ∀ k, k ≠ i → k ≠ j → w k = w' k) :
    (weightedSumSquares R w).IsometryEquiv (weightedSumSquares R w') where
  toLinearEquiv := pairLinearEquiv hij e
  map_app' x := by
    simp only [weightedSumSquares_apply]
    rw [sum_pair_add_rest _ hij, sum_pair_add_rest _ hij]
    simp only [pairLinearEquiv]
    have hpair := e.map_app ![x i, x j]
    simp only [weightedSumSquares_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, smul_eq_mul] at hpair
    rw [replacePair_apply_left, replacePair_apply_right (f := e) (i := i) (j := j) hij x]
    simp only [smul_eq_mul]
    rw [hpair]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    simp [replacePair, hki, hkj, hrest k hki hkj]

/-- Replacing two distinct coefficients by an equivalent binary form, while fixing all other
coefficients, produces an equivalent diagonal form. -/
theorem equivalent_weightedSumSquares_of_pair (hij : i ≠ j)
    (hpair : (weightedSumSquares R ![w i, w j]).Equivalent
      (weightedSumSquares R ![w' i, w' j]))
    (hrest : ∀ k, k ≠ i → k ≠ j → w k = w' k) :
    (weightedSumSquares R w).Equivalent (weightedSumSquares R w') := by
  obtain ⟨e⟩ := hpair
  exact ⟨pairIsometryEquiv hij e hrest⟩

end PairExtension

variable {R : Type u} [CommSemiring R] {ι : Type v} [Fintype ι]

/-- Permuting the coefficients of a diagonal form does not change its equivalence class. -/
theorem equivalent_weightedSumSquares_comp (w : ι → R) (σ : Equiv.Perm ι) :
    (QuadraticMap.weightedSumSquares R w).Equivalent
      (QuadraticMap.weightedSumSquares R (w ∘ σ)) := by
  refine ⟨{
    toLinearEquiv := LinearEquiv.funCongrLeft R R σ
    map_app' := fun x => ?_ }⟩
  simp only [QuadraticMap.weightedSumSquares_apply, Function.comp_apply, smul_eq_mul]
  simpa using (Equiv.sum_comp σ.symm (fun i => w (σ i) * (x (σ i) * x (σ i)))).symm

end TauCeti
