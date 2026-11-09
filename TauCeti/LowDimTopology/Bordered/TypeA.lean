/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CharP.Two
public import TauCeti.Algebra.Homology.DG.Ungraded
public import TauCeti.LinearAlgebra.Graded.Insertion

/-!
# Type `A` modules

In bordered Heegaard Floer homology a three-manifold with parametrized boundary has a type `A`
module `CFA`, an `A∞` right module over the algebra of the boundary. This file defines type `A`
modules over an ungraded differential algebra over a ring of characteristic two, the setting of
the type `D` structures of `TauCeti.LowDimTopology.Bordered.TypeD`.

A type `A` module over the differential algebra `(A, d)` (`TauCeti.TypeAModule`) has operations
`m_{n+1} : M ⊗ A^{⊗ n} → M`, stored as `op n : M →ₗ[R] MultilinearMap R (Fin n → A) M`,
satisfying the `A∞` relations `TauCeti.TypeAModule.stasheffSum`. The operations read the first `n`
entries of a sequence `a : ℕ → A`, so that splitting the inputs of the `A∞` relations needs no
reindexing between propositionally equal arities; the multiplication terms collapse two entries
with `TauCeti.replaceBlock`. There is no grading: the bordered algebras carry gradings by
noncommutative groups, not by `ℤ`, so the `ℤ`-graded `TauCeti.AInfinityRightModule` does not
apply, and over a ring of characteristic two the relations need no signs. A differential right
module is a type `A` module with `m₁ = dM`, `m₂` the action and no higher operations
(`TauCeti.TypeAModule.ofDGRightModule`).

## Main definitions

* `TauCeti.TypeAModule`: a type `A` module, given by its operations and the `A∞` relations.
* `TauCeti.TypeAModule.ofDGRightModule`: the type `A` module of a differential right module.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687),
  Chapter 2: `A∞` modules.
-/

public section

open Finset MulOpposite

namespace TauCeti

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (d : A →ₗ[R] A)
  (M : Type*) [AddCommGroup M] [Module R M]

namespace TypeAModule

variable {M}

/-- The left side of the **`A∞` relation** of arity `n` for operations `op k`, where
`op k x a = m_{k+1}(x, a 0, …, a (k - 1))` reads the first `k` entries of a sequence `a : ℕ → A`:
```
∑_{j ≤ n} m(m(x, a₀, …, a_{j-1}), a_j, …, a_{n-1}) + ∑_{l < n} m(x, …, d a_l, …)
  + ∑_{l < n - 1} m(x, …, a_l a_{l+1}, …).
```
Over a ring of characteristic two these are all the terms of the `A∞` relation of a right module
over a differential algebra. -/
def stasheffSum (op : (n : ℕ) → M →ₗ[R] MultilinearMap R (fun _ : Fin n => A) M) (n : ℕ)
    (x : M) (a : ℕ → A) : M :=
  (∑ j ∈ range (n + 1), op (n - j) (op j x fun t => a t) fun t => a (j + t)) +
    (∑ l ∈ range n, op n x fun t => Function.update a l (d (a l)) t) +
    ∑ l ∈ range (n - 1), op (n - 1) x fun t => replaceBlock a l 2 (a l * a (l + 1)) t

theorem stasheffSum_def (op : (n : ℕ) → M →ₗ[R] MultilinearMap R (fun _ : Fin n => A) M)
    (n : ℕ) (x : M) (a : ℕ → A) :
    stasheffSum d op n x a =
      (∑ j ∈ range (n + 1), op (n - j) (op j x fun t => a t) fun t => a (j + t)) +
        (∑ l ∈ range n, op n x fun t => Function.update a l (d (a l)) t) +
        ∑ l ∈ range (n - 1), op (n - 1) x fun t => replaceBlock a l 2 (a l * a (l + 1)) t :=
  (rfl)

end TypeAModule

/-- A **type `A` module** over the differential algebra `(A, d)`: an ungraded right `A∞` module,
given by operations `op n x a = m_{n+1}(x, a 0, …, a (n - 1))`, linear in the module element and
multilinear in the `n` algebra elements, satisfying the `A∞` relations
`TauCeti.TypeAModule.stasheffSum`. -/
@[ext]
structure TypeAModule where
  /-- `op n x a = m_{n+1}(x, a 0, …, a (n - 1))`. -/
  op : (n : ℕ) → M →ₗ[R] MultilinearMap R (fun _ : Fin n => A) M
  /-- The `A∞` relations. -/
  stasheffSum_eq_zero (n : ℕ) (x : M) (a : ℕ → A) : TypeAModule.stasheffSum d op n x a = 0

/-! ### Differential modules -/

namespace TypeAModule

section DG

variable {d M} [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]

/-- The right action `a ↦ x * a` as an `R`-linear map. -/
private def rightMul (x : M) : A →ₗ[R] M where
  toFun a := MulOpposite.op a • x
  map_add' a b := by simp [add_smul]
  map_smul' c a := by simp [op_smul, smul_assoc]

/-- The operations of a differential right module: `m₁ = dM`, `m₂` the right action, and no
higher operations. -/
private noncomputable def dgOp (dM : M →ₗ[R] M) :
    (n : ℕ) → M →ₗ[R] MultilinearMap R (fun _ : Fin n => A) M
  | 0 =>
    { toFun x := MultilinearMap.constOfIsEmpty R _ (dM x)
      map_add' x y := by ext; simp
      map_smul' c x := by ext; simp }
  | 1 =>
    { toFun x := MultilinearMap.ofSubsingleton R A M (0 : Fin 1) (rightMul x)
      map_add' x y := by ext; simp [rightMul]
      map_smul' c x := by
        ext a
        simp only [rightMul, MultilinearMap.ofSubsingleton_apply_apply,
          LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, smul_apply]
        exact smul_comm _ _ _ }
  | _ + 2 => 0

private theorem dgOp_of_two_le (dM : M →ₗ[R] M) {n : ℕ} (hn : 2 ≤ n) : dgOp (A := A) dM n = 0 := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rfl

private theorem stasheffSum_dgOp [CharP R 2] {dM : M →ₗ[R] M}
    (hM : IsUngradedDGRightModule d dM) (n : ℕ) (x : M) (a : ℕ → A) :
    stasheffSum d (dgOp dM) n x a = 0 := by
  have h2 := add_self_eq_zero_of_charTwo R (M := M)
  match n with
  | 0 => simp [stasheffSum, dgOp, hM.map_map]
  | 1 =>
    simp only [stasheffSum, sum_range_succ, range_zero, sum_empty, zero_add, Nat.sub_self,
      add_zero]
    simp only [Nat.sub_zero, dgOp, Fin.isValue, rightMul, LinearMap.coe_mk, AddHom.coe_mk,
      MultilinearMap.constOfIsEmpty_apply, Function.const_apply, Fin.val_eq_zero,
      MultilinearMap.ofSubsingleton_apply_apply, Nat.add_one_sub_one, hM.map_smul,
      Function.update_self]
    rw [← add_assoc, h2, zero_add, h2]
  | 2 =>
    simp only [stasheffSum, sum_range_succ, range_zero, sum_empty, zero_add]
    simp [dgOp, rightMul, mul_smul, h2]
  | n + 3 =>
    simp only [stasheffSum]
    rw [Finset.sum_eq_zero fun j hj => ?_, Finset.sum_eq_zero fun l _ => ?_,
      Finset.sum_eq_zero fun l _ => ?_]
    · simp
    · rw [dgOp_of_two_le dM (by omega)]
      simp
    · rw [dgOp_of_two_le dM (by omega)]
      simp
    · rcases le_or_gt 2 j with hj2 | hj2
      · rw [dgOp_of_two_le dM hj2]
        simp
      · rw [dgOp_of_two_le dM (by simp only [mem_range] at hj; omega)]
        simp

/-- The type `A` module of a differential right module `(M, dM)` over `(A, d)`: `m₁ = dM`,
`m₂(x, a) = x * a`, and no higher operations. -/
noncomputable def ofDGRightModule [CharP R 2] {dM : M →ₗ[R] M}
    (hM : IsUngradedDGRightModule d dM) : TypeAModule d M where
  op := dgOp dM
  stasheffSum_eq_zero := stasheffSum_dgOp hM

variable [CharP R 2] {dM : M →ₗ[R] M}
  (hM : IsUngradedDGRightModule d dM)

@[simp]
theorem ofDGRightModule_op_zero_apply (x : M) (a : Fin 0 → A) :
    (ofDGRightModule hM).op 0 x a = dM x :=
  (rfl)

@[simp]
theorem ofDGRightModule_op_one_apply (x : M) (a : Fin 1 → A) :
    (ofDGRightModule hM).op 1 x a = MulOpposite.op (a 0) • x :=
  (rfl)

theorem ofDGRightModule_op_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    (ofDGRightModule hM).op n = 0 :=
  dgOp_of_two_le dM hn

end DG

end TypeAModule

end TauCeti
