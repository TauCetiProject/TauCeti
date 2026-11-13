/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Module.Right.Ungraded

/-!
# Differential modules as ungraded `A∞` right modules

Let `(A, d)` be an algebra with a linear map `d`, thought of as an ungraded differential algebra
(`TauCeti.IsUngradedDGAlgebra`). A differential right module over it
(`TauCeti.IsUngradedDGRightModule`), a right `A`-module `M` with a linear map `dM` satisfying the
Leibniz rule and `dM ∘ dM = 0`, is an ungraded `A∞` right module
(`TauCeti.UngradedAInfinityRightModule`) over a ring of characteristic two: its operations are
`m₁ = dM`, the right action `m₂(m, a) = m * a` and `m_{n+1} = 0` for `n ≥ 2`. The `A∞` relation of
length one is the Leibniz rule, that of length two is associativity of the action, and the others
hold trivially. Such a module is strictly unital for every family of elements of the algebra,
since its higher operations vanish.

## Main definitions

* `TauCeti.IsUngradedDGRightModule.toUngradedAInfinityRightModule`: a differential right module as
  an `A∞` module.

## Main results

* `TauCeti.IsUngradedDGRightModule.toUngradedAInfinityRightModule_act_zero`,
  `TauCeti.IsUngradedDGRightModule.toUngradedAInfinityRightModule_act_one` and
  `TauCeti.IsUngradedDGRightModule.toUngradedAInfinityRightModule_act_add_two`: the operations.
* `TauCeti.IsUngradedDGRightModule.isStrictlyUnital_toUngradedAInfinityRightModule`: differential
  modules are strictly unital.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687),
  Chapter 2 (differential modules as `A∞` modules over `𝔽₂`).
-/

public section

open Finset MulOpposite

namespace TauCeti

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]

namespace IsUngradedDGRightModule

variable [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]

/-- The operations of a differential right module: `m₁ = dM`, `m₂` is the right action and
`m_{n+1} = 0` for `n ≥ 2`. -/
private noncomputable def dgAct (dM : M →ₗ[R] M) :
    (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M)
  | 0 => MultilinearMap.constOfIsEmpty (RingHom.id R) _ dM
  | 1 => MultilinearMap.ofSubsingleton (RingHom.id R) A (M →ₗ[R] M) 0
    ((Algebra.lsmul R R M).toLinearMap ∘ₗ (opLinearEquiv R).toLinearMap)
  | _ + 2 => 0

private theorem dgAct_apply_of_eq_zero (dM : M →ₗ[R] M) {n : ℕ} (hn : n = 0) (a : Fin n → A)
    (m : M) : dgAct (R := R) dM n a m = dM m := by
  subst hn
  rfl

private theorem dgAct_apply_of_eq_one (dM : M →ₗ[R] M) {n : ℕ} (hn : n = 1) (a : Fin n → A)
    (m : M) : dgAct (R := R) dM n a m = op (a ⟨0, by omega⟩) • m := by
  subst hn
  rfl

private theorem dgAct_eq_zero_of_two_le (dM : M →ₗ[R] M) {n : ℕ} (hn : 2 ≤ n) :
    dgAct (R := R) (A := A) dM n = 0 := by
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rfl

private theorem dgAct_apply_of_two_le (dM : M →ₗ[R] M) {n : ℕ} (hn : 2 ≤ n) (a : Fin n → A)
    (m : M) : dgAct (R := R) dM n a m = 0 := by
  rw [dgAct_eq_zero_of_two_le dM hn]
  rfl

variable {d : A →ₗ[R] A} {dM : M →ₗ[R] M}

/-- **A differential right module is an `A∞` module**, over a ring of characteristic two: its
operations are `m₁ = dM`, the right action `m₂(m, a) = m * a` and `m_{n+1} = 0` for `n ≥ 2`.
The `A∞` relation of length one is the Leibniz rule, that of length two is associativity of the
action, and the others hold trivially. -/
noncomputable def toUngradedAInfinityRightModule [CharP R 2]
    (hM : IsUngradedDGRightModule d dM) : UngradedAInfinityRightModule d M where
  act := dgAct dM
  stasheff n a m := by
    have h2 (x : M) : x + x = 0 := add_self_eq_zero_of_charTwo R x
    match n with
    | 0 =>
      simp [ungradedStasheffComp_def, ungradedStasheffDiff_def, dgAct_apply_of_eq_zero, hM.map_map]
    | 1 =>
      simp only [ungradedStasheffComp_def, ungradedStasheffDiff_def, Fin.sum_univ_succ,
        Fin.sum_univ_zero, ungradedStasheffMul_succ, dgAct_apply_of_eq_zero,
        dgAct_apply_of_eq_one, Fin.val_zero, Fin.val_succ, Nat.sub_zero, Nat.sub_self, add_zero,
        Fin.zero_eta, Function.update_self, hM.map_smul, Fin.isValue]
      calc _ = (op (a 0) • dM m + op (a 0) • dM m) + (op (d (a 0)) • m + op (d (a 0)) • m) := by
            abel
        _ = 0 := by rw [h2, h2, add_zero]
    | 2 =>
      have hmul : Fin.contractNth 0 (· * ·) a 0 = a 0 * a 1 := by
        rw [Fin.contractNth_apply_of_eq _ _ _ _ rfl, Fin.castSucc_zero, Fin.succ_zero_eq_one]
      simp only [ungradedStasheffComp_def, ungradedStasheffDiff_def, Fin.sum_univ_succ,
        Fin.sum_univ_zero, ungradedStasheffMul_succ, dgAct_apply_of_eq_zero,
        dgAct_apply_of_eq_one, Fin.val_zero, Fin.val_succ, Nat.sub_zero, Fin.isValue,
        dgAct_apply_of_two_le dM (le_refl 2), map_zero, add_zero, zero_add, Fin.zero_eta, hmul,
        Fin.castSucc_zero, Fin.mk_one]
      rw [op_mul, mul_smul, h2]
    | n + 3 =>
      have hcomp : ungradedStasheffComp (dgAct dM) (n + 3) a m = 0 := by
        rw [ungradedStasheffComp_def]
        refine sum_eq_zero fun k _ => ?_
        rcases le_or_gt 2 (k : ℕ) with hk | hk
        · rw [dgAct_apply_of_two_le dM hk, map_zero]
        · exact dgAct_apply_of_two_le dM (by omega) _ _
      have hdiff : ungradedStasheffDiff (dgAct dM) d (n + 3) a m = 0 := by
        rw [ungradedStasheffDiff_def]
        exact sum_eq_zero fun l _ => dgAct_apply_of_two_le dM (by omega) _ _
      have hmul : ungradedStasheffMul (dgAct dM) (n + 3) a m = 0 := by
        rw [ungradedStasheffMul_succ]
        exact sum_eq_zero fun l _ => dgAct_apply_of_two_le dM (by omega) _ _
      rw [hcomp, hdiff, hmul, add_zero, add_zero]

/-- The operation `m₁` of a differential module viewed as an `A∞` module is its differential. -/
@[simp]
theorem toUngradedAInfinityRightModule_act_zero [CharP R 2] (hM : IsUngradedDGRightModule d dM)
    (a : Fin 0 → A) (m : M) : hM.toUngradedAInfinityRightModule.act 0 a m = dM m :=
  (rfl)

/-- The operation `m₂` of a differential module viewed as an `A∞` module is its right action. -/
@[simp]
theorem toUngradedAInfinityRightModule_act_one [CharP R 2] (hM : IsUngradedDGRightModule d dM)
    (a : Fin 1 → A) (m : M) : hM.toUngradedAInfinityRightModule.act 1 a m = op (a 0) • m :=
  (rfl)

/-- The operations `m_{n+1}`, `n ≥ 2`, of a differential module viewed as an `A∞` module vanish. -/
@[simp]
theorem toUngradedAInfinityRightModule_act_add_two [CharP R 2]
    (hM : IsUngradedDGRightModule d dM) (n : ℕ) :
    hM.toUngradedAInfinityRightModule.act (n + 2) = 0 :=
  (rfl)

/-- A differential module viewed as an `A∞` module is strictly unital for every family of
elements: its operations `m_{n+1}`, `n ≥ 2`, vanish. -/
theorem isStrictlyUnital_toUngradedAInfinityRightModule [CharP R 2]
    (hM : IsUngradedDGRightModule d dM) {S : Type*} (ι : S → A) :
    hM.toUngradedAInfinityRightModule.IsStrictlyUnital ι := by
  refine (UngradedAInfinityRightModule.isStrictlyUnital_iff _).2 fun n hn a _ _ _ => ?_
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [hM.toUngradedAInfinityRightModule_act_add_two n, zero_apply]

end IsUngradedDGRightModule

end TauCeti
