/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.Normalized.Chains
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Even periodic Chern chains

For an idempotent `e` in a unital algebra over a characteristic-zero field, the even
periodic Chern chain has components

* `ch₀(e) = e`,
* `ch₂ₖ(e) = (-1)^k (2k)! / k! (e - 1/2) ⊗ e ⊗ ⋯ ⊗ e` for `k > 0`.

These are normalized Hochschild chains. The components satisfy
`b ch₂ₖ₊₂(e) + B ch₂ₖ(e) = 0`, including the exceptional degree-zero component.
Thus they form a cycle in the product totalization of chains; no finite-support claim
is made for this infinite family. Component evaluations against normalized cochains are
provided here; the totalization and descent to K-theory are not constructed in this file.
The subtraction of `1/2` and the factorial coefficient are both essential for closedness.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
* J.-L. Loday, *Cyclic Homology*, §8.3.
-/

public section

noncomputable section

namespace TauCeti
namespace normalizedHochschildChains

section Chern

variable (R A : Type*) [Field R] [NonAssocRing A] [Module R A]

/-- The coefficient `(-1)^k (2k)! / k!` in the even Chern chain. -/
def evenChernCoeff (k : ℕ) : R :=
  (-1 : R) ^ k * (Nat.factorial (2 * k) : R) / (Nat.factorial k : R)

/-- The initial Chern coefficient. -/
@[simp]
theorem evenChernCoeff_zero : evenChernCoeff R 0 = 1 := by
  simp [evenChernCoeff]

/-- The first positive-degree Chern coefficient. -/
@[simp]
theorem evenChernCoeff_one : evenChernCoeff R 1 = -2 := by
  norm_num [evenChernCoeff]

/-- The recursion ensuring cancellation between the two mixed boundaries. -/
theorem evenChernCoeff_succ [CharZero R] (k : ℕ) :
    evenChernCoeff R (k + 1) = -(2 * (2 * k + 1) : R) * evenChernCoeff R k := by
  have hk : (Nat.factorial k : R) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hk1 : (k + 1 : R) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hdegree : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
  rw [evenChernCoeff, evenChernCoeff, hdegree,
    Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  rw [pow_succ]
  field_simp
  ring

/-- The centered idempotent word of degree `n`. The initial entry is `e - 1/2`. -/
def centeredWord (e : A) (n : ℕ) : normalizedHochschildChains R A n :=
  tensor R A n (Fin.cons (e - (2 : R)⁻¹ • 1) (fun _ ↦ e))

/-- Expand the centered word using linearity of its initial entry. -/
theorem centeredWord_eq (e : A) (n : ℕ) :
    centeredWord R A e n = tensor R A n (fun _ ↦ e) -
      (2 : R)⁻¹ • tensor R A n (Fin.cons 1 (fun _ ↦ e)) := by
  have hc : (Fin.cons e (fun _ : Fin n ↦ e)) = fun _ ↦ e := by
    ext i
    exact Fin.cases rfl (fun _ ↦ rfl) i
  rw [centeredWord, ← MultilinearMap.curryLeft_apply, map_sub, map_smul]
  simp only [sub_apply, smul_apply, MultilinearMap.curryLeft_apply, hc]

/-- The Hochschild boundary of a centered even word is half the word with initial unit. -/
theorem b_centeredWord [IsScalarTower R A A] [SMulCommClass R A A] [CharZero R]
    {e : A} (he : IsIdempotentElem e) (k : ℕ) :
    b R A (2 * k + 1) (centeredWord R A e (2 * k + 2)) =
      (2 : R)⁻¹ • tensor R A (2 * k + 1) (Fin.cons 1 (fun _ ↦ e)) := by
  rw [centeredWord_eq, map_sub, map_smul, b_tensor_const R A he,
    ite_eq_right (Nat.not_even_two_mul_add_one k), b_tensor_cons_one R A he]
  simp only [smul_sub, ← Nat.cast_smul_eq_nsmul R, smul_smul, Nat.cast_ofNat,
    inv_mul_cancel₀ (by norm_num : (2 : R) ≠ 0), one_smul]
  abel

/-- Connes' boundary of a centered even word is its length times the word with initial unit. -/
theorem B_centeredWord (e : A) (k : ℕ) :
    B R A (2 * k) (centeredWord R A e (2 * k)) =
      (2 * k + 1) • tensor R A (2 * k + 1) (Fin.cons 1 (fun _ ↦ e)) := by
  rw [centeredWord_eq, map_sub, map_smul, B_tensor_const R A (even_two_mul k),
    B_tensor_eq_zero_of_eq_one R A _ 0 (Fin.cons_zero _ _), smul_zero, sub_zero]

/-- The degree-`2k` component of the even periodic Chern chain. Degree zero is not centered. -/
def evenChernChain (e : A) : (k : ℕ) → normalizedHochschildChains R A (2 * k)
  | 0 => tensor R A 0 (fun _ ↦ e)
  | k + 1 => evenChernCoeff R (k + 1) • centeredWord R A e (2 * (k + 1))

/-- The degree-zero Chern chain is the one-factor tensor `e`. -/
@[simp]
theorem evenChernChain_zero (e : A) :
    evenChernChain R A e 0 = tensor R A 0 (fun _ ↦ e) := (rfl)

/-- The positive-degree Chern chains have the centered factorial formula. -/
theorem evenChernChain_succ (e : A) (k : ℕ) :
    evenChernChain R A e (k + 1) =
      evenChernCoeff R (k + 1) • centeredWord R A e (2 * (k + 1)) := (rfl)

/-- **The even periodic Chern chain is closed under `b + B`.** The displayed identity is
in degree `2k + 1` and includes the exceptional degree-zero component. -/
theorem b_evenChernChain_add_B_evenChernChain
    [IsScalarTower R A A] [SMulCommClass R A A] [CharZero R] {e : A}
    (he : IsIdempotentElem e) (k : ℕ) :
    b R A (2 * k + 1) (evenChernChain R A e (k + 1)) +
      B R A (2 * k) (evenChernChain R A e k) = 0 := by
  -- Match the degree expression of the Chern component, rather than rewriting dependent indices.
  have hb : b R A (2 * k + 1) (centeredWord R A e (2 * (k + 1))) =
      (2 : R)⁻¹ • tensor R A (2 * k + 1) (Fin.cons 1 (fun _ ↦ e)) :=
    b_centeredWord R A he k
  rw [evenChernChain_succ, map_smul, hb]
  cases k with
  | zero =>
    rw [evenChernCoeff_one, evenChernChain_zero, B_tensor_const R A (by simp)]
    simp only [smul_smul]
    norm_num
  | succ k =>
    rw [evenChernChain_succ, map_smul, B_centeredWord, evenChernCoeff_succ R (k + 1),
      smul_smul, ← Nat.cast_smul_eq_nsmul R, smul_smul, ← add_smul]
    convert zero_smul R
      (tensor R A (2 * (k + 1) + 1) (Fin.cons 1 (fun _ ↦ e))) using 1
    congr 1
    push_cast
    field_simp
    ring

/-- The zero element has zero Chern chain in every degree. -/
@[simp]
theorem evenChernChain_zero_elem (k : ℕ) : evenChernChain R A (0 : A) k = 0 := by
  cases k with
  | zero =>
    rw [evenChernChain_zero]
    exact (tensor R A 0).map_coord_zero 0 rfl
  | succ k =>
    rw [evenChernChain_succ, centeredWord]
    have ht : tensor R A (2 * (k + 1))
        (Fin.cons (0 - (2 : R)⁻¹ • (1 : A)) (fun _ ↦ 0)) = 0 := by
      exact (tensor R A (2 * (k + 1))).map_coord_zero
        (⟨0, by omega⟩ : Fin (2 * (k + 1))).succ (Fin.cons_succ _ _ _)
    rw [ht, smul_zero]

/-- Normalization kills the positive-degree Chern components of the unit. Its degree-zero
component is still the unit. -/
@[simp]
theorem evenChernChain_one_succ (k : ℕ) : evenChernChain R A (1 : A) (k + 1) = 0 := by
  rw [evenChernChain_succ, centeredWord]
  rw [tensor_eq_zero R A _ (⟨0, by omega⟩ : Fin (2 * (k + 1))).succ
    (Fin.succ_ne_zero _) (Fin.cons_succ _ _ _), smul_zero]

variable {M : Type*} [AddCommGroup M] [Module R M]

/-- Evaluation of a positive Chern component, including the initial-unit correction. -/
theorem lift_evenChernChain_succ (e : A) (k : ℕ)
    (φ : normalizedHochschildCochains R A M (2 * (k + 1))) :
    lift φ (evenChernChain R A e (k + 1)) =
      evenChernCoeff R (k + 1) • (φ.val (fun _ ↦ e) -
        (2 : R)⁻¹ • φ.val (Fin.cons 1 (fun _ ↦ e))) := by
  simp [evenChernChain_succ, centeredWord_eq]

end Chern
end normalizedHochschildChains
end TauCeti
