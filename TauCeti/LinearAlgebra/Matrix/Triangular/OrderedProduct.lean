/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Ordered products of upper-triangular matrices

If `N₀, …, N_{n-1}` are upper-triangular `n × n` matrices and the `t`-th factor vanishes at the
`t`-th diagonal entry, then the ordered product `N₀ * ⋯ * N_{n-1}` is zero. With all factors equal
this is the nilpotence of a strictly upper-triangular matrix; in general it is the matrix form of
the fact that `N_t` maps the `t + 1`-st space of the standard flag into the `t`-th one.

For upper-triangular matrices `M₀, …, M_{n-1}` with diagonal entries `d_t = M_t t t`, taking
`N_t = M_t - d_t • 1` shows that `(M₀ - d₀) ⋯ (M_{n-1} - d_{n-1}) = 0`: these are the
ordered-product equations of a simultaneously triangularized representation. A ring
homomorphism carries such an ordered product `(M₀ - c₀ • 1) ⋯ (M_{m-1} - c_{m-1} • 1)` to the
ordered product of the images, as for the change of coefficients `RingHom.mapMatrix`, which sends
the scalar matrix `a • 1` to `f a • 1`.

## Main results

* `Matrix.list_prod_ofFn_apply_eq_zero_of_isUpperTriangular`: the rows of index at least `s` of the
  ordered product vanish when its `t`-th factor vanishes at the `s + t`-th diagonal entry and the
  factors reach the last index.
* `Matrix.list_prod_ofFn_eq_zero_of_isUpperTriangular`: the ordered product `N₀ * ⋯ * N_{n-1}`
  vanishes when `N_t` vanishes at the `t`-th diagonal entry.
* `TauCeti.map_list_prod_ofFn_sub_smul_one`: a ring homomorphism sending each `c i • 1` to
  `d i • 1` maps `∏ (M i - c i • 1)` to `∏ (φ (M i) - d i • 1)`, in order.
* `RingHom.mapMatrix_smul_one`: `f.mapMatrix` sends `a • 1` to `f a • 1`.
-/

public section

namespace Matrix

variable {S : Type*} [Semiring S] {n : ℕ}

/-- In an ordered product of `m` upper-triangular matrices whose `t`-th factor vanishes at the
`s + t`-th diagonal entry, the rows of index at least `s` vanish, provided `n ≤ s + m`. -/
theorem list_prod_ofFn_apply_eq_zero_of_isUpperTriangular {m : ℕ}
    {N : Fin m → Matrix (Fin n) (Fin n) S} (htri : ∀ t, (N t).IsUpperTriangular) (s : ℕ)
    (hdiag : ∀ (t : Fin m) (i : Fin n), i.val = s + t.val → N t i i = 0) (hsm : n ≤ s + m)
    (i j : Fin n) (hi : s ≤ i.val) : (List.ofFn N).prod i j = 0 := by
  induction m generalizing s i j with
  | zero => have := i.isLt; omega
  | succ m ih =>
      rw [List.ofFn_succ, List.prod_cons, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun l _ ↦ ?_
      by_cases hl : s + 1 ≤ l.val
      · rw [ih (fun t ↦ htri t.succ) (s + 1)
          (fun t i hi ↦ hdiag t.succ i (by simp only [Fin.val_succ]; omega)) (by omega) l j hl,
          mul_zero]
      · obtain hli | hli | hli := lt_trichotomy l i
        · rw [htri 0 hli, zero_mul]
        · subst hli
          rw [hdiag 0 l (by simp only [Fin.val_zero]; omega), zero_mul]
        · exact absurd (Fin.lt_def.mp hli) (by omega)

/-- **The ordered product of a flag of nilpotent steps vanishes.** If each `N t` is upper
triangular with `N t t t = 0`, then `N 0 * N 1 * ⋯ * N (n - 1) = 0`. -/
theorem list_prod_ofFn_eq_zero_of_isUpperTriangular {N : Fin n → Matrix (Fin n) (Fin n) S}
    (htri : ∀ t, (N t).IsUpperTriangular) (hdiag : ∀ t, N t t t = 0) :
    (List.ofFn N).prod = 0 := by
  ext i j
  exact list_prod_ofFn_apply_eq_zero_of_isUpperTriangular htri 0
    (fun t i hi ↦ by rw [show i = t from Fin.ext (by omega)]; exact hdiag t) (by omega) i j
    (Nat.zero_le _)

end Matrix

/-- A ring homomorphism `φ` sending each `c i • 1` to `d i • 1` sends the ordered product
`(M₀ - c₀ • 1) * ⋯ * (M_{m-1} - c_{m-1} • 1)` to
`(φ M₀ - d₀ • 1) * ⋯ * (φ M_{m-1} - d_{m-1} • 1)`. -/
theorem TauCeti.map_list_prod_ofFn_sub_smul_one {R S B C Φ : Type*} [Ring R] [Ring S] [SMul B R]
    [SMul C S] [FunLike Φ R S] [RingHomClass Φ R S] (φ : Φ) {m : ℕ} (M : Fin m → R)
    {c : Fin m → B} {d : Fin m → C} (hφ : ∀ i, φ (c i • 1) = d i • 1) :
    φ (List.ofFn fun i ↦ M i - c i • 1).prod = (List.ofFn fun i ↦ φ (M i) - d i • 1).prod := by
  simp only [map_list_prod, List.map_ofFn, Function.comp_def, map_sub, hφ]

/-- `f.mapMatrix` sends the scalar matrix `a • 1` to `f a • 1`. -/
theorem RingHom.mapMatrix_smul_one {m α β : Type*} [Fintype m] [DecidableEq m]
    [NonAssocSemiring α] [NonAssocSemiring β] (f : α →+* β) (a : α) :
    f.mapMatrix (a • (1 : Matrix m m α)) = f a • 1 := by
  rw [f.mapMatrix_apply, Matrix.map_smul' _ _ _ (map_mul f),
    Matrix.map_one _ (map_zero f) (map_one f)]
