/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorPower.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Basic operations on tensor powers

Mathlib's `TensorPower.mulEquiv` identifies `⨂[R]^k M ⊗[R] ⨂[R]^m M` with `⨂[R]^(k + m) M`.  This
file records the inverse operation: `TensorPower.splitAt` cuts a tensor power of length `n` after
its first `k` factors, landing in `⨂[R]^k M ⊗[R] ⨂[R]^(n - k) M`, together with its value on pure
tensors and the fact that it is injective. It also identifies the first tensor power with the
underlying module.

## Main definitions

* `TensorPower.splitAt`: split a tensor power at a specified position.
* `TauCeti.TensorPower.oneEquiv`: identify the first tensor power with the underlying module.

-/

public section

open scoped TensorProduct

universe uR uM

variable (R : Type uR) (M : Type uM) [CommSemiring R] [AddCommMonoid M] [Module R M]

namespace TauCeti.TensorPower

/-- A tensor word of length one is a single letter. -/
noncomputable def oneEquiv : TensorPower R 1 M ≃ₗ[R] M :=
  PiTensorProduct.subsingletonEquiv (R := R) (s := fun _ : Fin 1 ↦ M) 0

/-- The length-one tensor-power equivalence evaluates a pure tensor at its unique index. -/
@[simp]
theorem oneEquiv_tprod (f : Fin 1 → M) :
    oneEquiv R M (PiTensorProduct.tprod R f) = f 0 :=
  PiTensorProduct.subsingletonEquiv_apply_tprod 0 f

/-- The inverse length-one tensor-power equivalence sends a letter to the corresponding pure
tensor. -/
@[simp]
theorem oneEquiv_symm_apply (a : M) :
    (oneEquiv R M).symm a = PiTensorProduct.tprod R (fun _ ↦ a) :=
  PiTensorProduct.subsingletonEquiv_symm_apply' 0 a

end TauCeti.TensorPower

namespace TensorPower

/-- Split a tensor power after its first `k` factors. -/
noncomputable def splitAt (n k : ℕ) (hk : k ≤ n) :
    TensorPower R n M →ₗ[R] TensorPower R k M ⊗[R] TensorPower R (n - k) M :=
  (TensorPower.mulEquiv (R := R) (M := M)).symm.toLinearMap ∘ₗ
    (TensorPower.cast R M (Nat.add_sub_of_le hk).symm).toLinearMap

@[simp]
theorem mulEquiv_splitAt (n k : ℕ) (hk : k ≤ n) (x : TensorPower R n M) :
    TensorPower.mulEquiv (splitAt R M n k hk x) =
      TensorPower.cast R M (Nat.add_sub_of_le hk).symm x := by
  simp [splitAt]

/-- Splitting a tensor power at a fixed position loses no information: it is the composite of two
linear equivalences. -/
theorem splitAt_injective (n k : ℕ) (hk : k ≤ n) :
    Function.Injective (splitAt R M n k hk) := by
  intro x y hxy
  have := congrArg (TensorPower.mulEquiv (R := R) (M := M)) hxy
  rw [mulEquiv_splitAt, mulEquiv_splitAt] at this
  exact (TensorPower.cast R M (Nat.add_sub_of_le hk).symm).injective this

/-- Splitting a pure tensor separates its first `k` entries from the remaining entries. -/
@[simp]
theorem splitAt_tprod (n k : ℕ) (hk : k ≤ n) (x : Fin n → M) :
    splitAt R M n k hk (PiTensorProduct.tprod R x) =
      PiTensorProduct.tprod R (fun i : Fin k ↦ x (Fin.castLE hk i)) ⊗ₜ[R]
        PiTensorProduct.tprod R (fun j : Fin (n - k) ↦ x ⟨k + j.1, by omega⟩) := by
  apply TensorPower.mulEquiv.injective
  rw [mulEquiv_splitAt, TensorPower.cast_tprod, ← TensorPower.gMul_def,
    TensorPower.tprod_mul_tprod]
  congr 1
  funext i
  simp only [Function.comp_apply]
  by_cases hi : i.1 < k
  · let j : Fin k := ⟨i.1, hi⟩
    have hij : Fin.castAdd (n - k) j = i := by ext; rfl
    rw [← hij, Fin.append_left]
    congr 1
  · let j : Fin (n - k) := ⟨i.1 - k, by omega⟩
    have hij : Fin.natAdd k j = i := by ext; simp [j]; omega
    rw [← hij, Fin.append_right]
    congr 1

/-- Identifying the empty left tensor block with scalars agrees with concatenation. -/
theorem lid_map_algebraMap₀_symm (n : ℕ) (z : TensorPower R 0 M ⊗[R] TensorPower R n M) :
    TensorProduct.lid R (TensorPower R n M)
      (TensorProduct.map (TensorPower.algebraMap₀ (R := R) (M := M)).symm.toLinearMap
        LinearMap.id z) =
      TensorPower.cast R M (Nat.zero_add n) (TensorPower.mulEquiv z) := by
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a b =>
    obtain ⟨a, rfl⟩ := (TensorPower.algebraMap₀ (R := R) (M := M)).surjective a
    simpa only [TensorProduct.map_tmul, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, LinearMap.id_apply, TensorProduct.lid_tmul,
      ← TensorPower.gMul_def] using (TensorPower.algebraMap₀_mul a b).symm

/-- Identifying the empty right tensor block with scalars agrees with concatenation. -/
theorem rid_map_algebraMap₀_symm (n : ℕ) (z : TensorPower R n M ⊗[R] TensorPower R 0 M) :
    TensorProduct.rid R (TensorPower R n M)
      (TensorProduct.map LinearMap.id
        (TensorPower.algebraMap₀ (R := R) (M := M)).symm.toLinearMap z) =
      TensorPower.cast R M (Nat.add_zero n) (TensorPower.mulEquiv z) := by
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a b =>
    obtain ⟨b, rfl⟩ := (TensorPower.algebraMap₀ (R := R) (M := M)).surjective b
    simpa only [TensorProduct.map_tmul, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, LinearMap.id_apply, TensorProduct.rid_tmul,
      ← TensorPower.gMul_def] using (TensorPower.mul_algebraMap₀ b a).symm

/-- Splitting a tensor power into three consecutive blocks is independent of the order of
the two cuts, after applying the tensor associator. -/
theorem mulEquiv_symm_assoc (p q r : ℕ) (x : TensorPower R (p + q + r) M) :
    (TensorProduct.assoc R _ _ _)
      (TensorProduct.map (TensorPower.mulEquiv (R := R) (M := M)).symm.toLinearMap
        LinearMap.id ((TensorPower.mulEquiv (R := R) (M := M)).symm x)) =
      TensorProduct.map LinearMap.id
        (TensorPower.mulEquiv (R := R) (M := M)).symm.toLinearMap
        ((TensorPower.mulEquiv (R := R) (M := M)).symm
          (TensorPower.cast R M (Nat.add_assoc p q r) x)) := by
  obtain ⟨x, rfl⟩ := (TensorPower.mulEquiv (R := R) (M := M)
    (n := p + q) (m := r)).surjective x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a c =>
    obtain ⟨a, rfl⟩ := (TensorPower.mulEquiv (R := R) (M := M)
      (n := p) (m := q)).surjective a
    induction a using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, TensorProduct.add_tmul, ha, hb]
    | tmul a b =>
      simp only [LinearEquiv.symm_apply_apply, TensorProduct.map_tmul,
        LinearEquiv.coe_coe, LinearMap.id_apply, TensorProduct.assoc_tmul]
      rw [← TensorPower.gMul_def, ← TensorPower.gMul_def, TensorPower.mul_assoc]
      simp only [TensorPower.gMul_def, LinearEquiv.symm_apply_apply,
        TensorProduct.map_tmul, LinearMap.id_apply, LinearEquiv.coe_coe]

end TensorPower
