/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Product
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
import TauCeti.LinearAlgebra.ExteriorPower.Basic
import TauCeti.RingTheory.GradedAlgebra.Basic

/-!
# Exterior powers of a product module

Mathlib's `ExteriorAlgebra.prodEquivTensor` identifies `⋀ (M × N)` with the graded tensor product
`⋀ M ᵍ⊗ ⋀ N`, its inverse sending `a ⊗ b` to `a ∧ b` (with `a` and `b` mapped along the inclusions
of the factors). This file records the degree-by-degree form of that identification:
`⋀ⁿ (M × N)` is the direct sum of the `⋀ⁱ M ⊗ ⋀ʲ N` with `i + j = n`.

## Main definitions

* `exteriorPower.mulInlInr h`: for `h : i + j = n`, the wedge map
  `⋀ⁱ M ⊗ ⋀ʲ N → ⋀ⁿ (M × N)`, `a ⊗ b ↦ a ∧ b`.
* `exteriorPower.prodComponent i j`: the `(i, j)`-component `⋀ⁿ (M × N) → ⋀ⁱ M ⊗ ⋀ʲ N` of
  `ExteriorAlgebra.prodEquivTensor`.

## Main results

* `exteriorPower.prodComponent_mulInlInr_tmul`, `exteriorPower.prodComponent_mulInlInr_of_ne`:
  for `a ∈ ⋀ⁱ M` and `b ∈ ⋀ʲ N`, the `(i, j)`-component of `a ∧ b` is `a ⊗ b`, and its
  `(i', j')`-components with `i' ≠ i` vanish.
* `exteriorPower.sum_mulInlInr_prodComponent`: every `x ∈ ⋀ⁿ (M × N)` is the sum of the wedges of
  its `(i, n - i)`-components.

Together these say that the wedge maps exhibit `⋀ⁿ (M × N)` as `⨁_{i + j = n} ⋀ⁱ M ⊗ ⋀ʲ N`. This is
the module-level input to the identification of the Koszul complex of `φ.coprod ψ` with the tensor
product of the Koszul complexes of `φ` and `ψ`.
-/

public section

noncomputable section

open TensorProduct

namespace exteriorPower

variable {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

variable (R M N) in
/-- The **wedge map** `⋀ⁱ M ⊗ ⋀ʲ N → ⋀ⁿ (M × N)` for `i + j = n`, sending `a ⊗ b` to `a ∧ b`,
where `a` and `b` are mapped into `⋀ (M × N)` along the inclusions of the two factors. -/
def mulInlInr {i j n : ℕ} (h : i + j = n) : ⋀[R]^i M ⊗[R] ⋀[R]^j N →ₗ[R] ⋀[R]^n (M × N) :=
  TensorProduct.lift <| LinearMap.mk₂ R
    (fun a b ↦ ⟨ExteriorAlgebra.map (LinearMap.inl R M N) a *
        ExteriorAlgebra.map (LinearMap.inr R M N) b, h ▸ SetLike.mul_mem_graded
          (TauCeti.ExteriorAlgebra.map_mem_exteriorPower (LinearMap.inl R M N) a.2)
          (TauCeti.ExteriorAlgebra.map_mem_exteriorPower (LinearMap.inr R M N) b.2)⟩)
    (fun _ _ _ ↦ Subtype.ext <| by simp [add_mul])
    (fun _ _ _ ↦ Subtype.ext <| by simp)
    (fun _ _ _ ↦ Subtype.ext <| by simp [mul_add])
    (fun _ _ _ ↦ Subtype.ext <| by simp)

/-- The wedge map sends `a ⊗ b` to `a ∧ b`. -/
@[simp]
theorem coe_mulInlInr_tmul {i j n : ℕ} (h : i + j = n) (a : ⋀[R]^i M) (b : ⋀[R]^j N) :
    (mulInlInr R M N h (a ⊗ₜ b) : ExteriorAlgebra R (M × N)) =
      ExteriorAlgebra.map (LinearMap.inl R M N) a * ExteriorAlgebra.map (LinearMap.inr R M N) b :=
  (rfl)

variable (R M N) in
/-- The `(i, j)`-component `⋀ⁿ (M × N) → ⋀ⁱ M ⊗ ⋀ʲ N` of `ExteriorAlgebra.prodEquivTensor`. -/
def prodComponent (i j : ℕ) {n : ℕ} : ⋀[R]^n (M × N) →ₗ[R] ⋀[R]^i M ⊗[R] ⋀[R]^j N :=
  TensorProduct.map
      (DirectSum.component R ℕ _ i ∘ₗ
        (DirectSum.decomposeLinearEquiv fun k : ℕ ↦ ⋀[R]^k M).toLinearMap)
      (DirectSum.component R ℕ _ j ∘ₗ
        (DirectSum.decomposeLinearEquiv fun k : ℕ ↦ ⋀[R]^k N).toLinearMap) ∘ₗ
    (GradedTensorProduct.of R (fun k : ℕ ↦ ⋀[R]^k M) fun k : ℕ ↦ ⋀[R]^k N).symm.toLinearMap ∘ₗ
      (ExteriorAlgebra.prodEquivTensor R M N).toLinearMap ∘ₗ (⋀[R]^n (M × N)).subtype

/-- The `(i, j)`-component of `a ∧ b`, for `a ∈ ⋀ⁱ M` and `b ∈ ⋀ʲ N`, is `a ⊗ b`. -/
@[simp]
theorem prodComponent_mulInlInr_tmul {i j n : ℕ} (h : i + j = n) (a : ⋀[R]^i M)
    (b : ⋀[R]^j N) :
    prodComponent R M N i j (mulInlInr R M N h (a ⊗ₜ b)) = a ⊗ₜ b := by
  simp [prodComponent, ← ExteriorAlgebra.prodEquivTensor_symm_tmul, GradedTensorProduct.tmul]

/-- The `(i', j')`-component of `a ∧ b`, for `a ∈ ⋀ⁱ M` and `b ∈ ⋀ʲ N`, vanishes when `i' ≠ i`. -/
theorem prodComponent_mulInlInr_of_ne {i j n : ℕ} (h : i + j = n) {i' : ℕ} (j' : ℕ)
    (hi : i' ≠ i) (x : ⋀[R]^i M ⊗[R] ⋀[R]^j N) :
    prodComponent R M N i' j' (mulInlInr R M N h x) = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    simp [prodComponent, ← ExteriorAlgebra.prodEquivTensor_symm_tmul, GradedTensorProduct.tmul,
      DirectSum.component.of, hi.symm]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

variable (R M N) in
/-- The inverse of `ExteriorAlgebra.prodEquivTensor`, on the underlying tensor product of the
exterior algebras: `a ⊗ b ↦ a ∧ b`. -/
private def prodMul :
    ExteriorAlgebra R M ⊗[R] ExteriorAlgebra R N →ₗ[R] ExteriorAlgebra R (M × N) :=
  (ExteriorAlgebra.prodEquivTensor R M N).symm.toLinearMap ∘ₗ
    (GradedTensorProduct.of R (fun k : ℕ ↦ ⋀[R]^k M) fun k : ℕ ↦ ⋀[R]^k N).toLinearMap

private theorem prodMul_tmul (a : ExteriorAlgebra R M) (b : ExteriorAlgebra R N) :
    prodMul R M N (a ⊗ₜ b) =
      ExteriorAlgebra.map (LinearMap.inl R M N) a * ExteriorAlgebra.map (LinearMap.inr R M N) b :=
  (rfl)

/-- Projecting to degree `n` after `prodMul` is the sum of the projections to the degrees
`(i, n - i)` before it. -/
private theorem sum_prodMul_map_proj (n : ℕ) (z : ExteriorAlgebra R M ⊗[R] ExteriorAlgebra R N) :
    ∑ i : Fin (n + 1), prodMul R M N (TensorProduct.map
        (GradedAlgebra.proj (fun k : ℕ ↦ ⋀[R]^k M) i)
        (GradedAlgebra.proj (fun k : ℕ ↦ ⋀[R]^k N) (n - i)) z) =
      GradedAlgebra.proj (fun k : ℕ ↦ ⋀[R]^k (M × N)) n (prodMul R M N z) := by
  -- Both sides are additive in `z`, so it suffices to treat products of homogeneous elements.
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp only [map_add, Finset.sum_add_distrib, hz, hz']
  | tmul a b =>
    induction a using DirectSum.Decomposition.inductionOn (fun k : ℕ ↦ ⋀[R]^k M) with
    | zero => simp
    | add a a' ha ha' =>
      simp only [TensorProduct.add_tmul, map_add, Finset.sum_add_distrib, ha, ha']
    | @homogeneous k a =>
    induction b using DirectSum.Decomposition.inductionOn (fun k : ℕ ↦ ⋀[R]^k N) with
    | zero => simp
    | add b b' hb hb' =>
      simp only [TensorProduct.tmul_add, map_add, Finset.sum_add_distrib, hb, hb']
    | @homogeneous l b =>
      have hmem : prodMul R M N (a ⊗ₜ b) ∈ ⋀[R]^(k + l) (M × N) :=
        (mulInlInr R M N rfl (a ⊗ₜ b)).2
      simp only [TensorProduct.map_tmul,
        TauCeti.GradedAlgebra.proj_of_mem (fun k : ℕ ↦ ⋀[R]^k M) a.2,
        TauCeti.GradedAlgebra.proj_of_mem (fun k : ℕ ↦ ⋀[R]^k N) b.2, ite_tmul, tmul_ite,
        apply_ite (prodMul R M N), map_zero]
      rw [GradedAlgebra.proj_apply]
      by_cases hkl : k + l = n
      · rw [Fintype.sum_eq_single ⟨k, by omega⟩ fun i hi ↦ by
          split_ifs with h₁ h₂ <;> first | rfl | exact absurd (Fin.ext h₂.symm) hi]
        subst hkl
        simp [DirectSum.decompose_of_mem_same (fun k : ℕ ↦ ⋀[R]^k (M × N)) hmem]
      · rw [DirectSum.decompose_of_mem_ne (fun k : ℕ ↦ ⋀[R]^k (M × N)) hmem hkl,
          Finset.sum_eq_zero fun i _ ↦ by split_ifs <;> first | rfl | omega]

/-- The wedge of the `(i, j)`-components of the inverse image of `z` under `prodEquivTensor` is
`prodMul` of the `(i, j)`-projection of `z`. -/
private theorem coe_mulInlInr_map_component {i j n : ℕ} (h : i + j = n)
    (z : ExteriorAlgebra R M ⊗[R] ExteriorAlgebra R N) :
    (mulInlInr R M N h (TensorProduct.map
        (DirectSum.component R ℕ _ i ∘ₗ
          (DirectSum.decomposeLinearEquiv fun k : ℕ ↦ ⋀[R]^k M).toLinearMap)
        (DirectSum.component R ℕ _ j ∘ₗ
          (DirectSum.decomposeLinearEquiv fun k : ℕ ↦ ⋀[R]^k N).toLinearMap) z) :
        ExteriorAlgebra R (M × N)) =
      prodMul R M N (TensorProduct.map (GradedAlgebra.proj (fun k : ℕ ↦ ⋀[R]^k M) i)
        (GradedAlgebra.proj (fun k : ℕ ↦ ⋀[R]^k N) j) z) := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp only [map_add, Submodule.coe_add, hz, hz']
  | tmul a b =>
    simp [prodMul_tmul, GradedAlgebra.proj_apply, ← DirectSum.apply_eq_component,
      DirectSum.decomposeLinearEquiv_apply]

/-- **`⋀ⁿ (M × N)` is the sum of the wedges of its components**: every `x ∈ ⋀ⁿ (M × N)` is the sum
over `i ≤ n` of the wedges of its `(i, n - i)`-components. -/
theorem sum_mulInlInr_prodComponent (n : ℕ) (x : ⋀[R]^n (M × N)) :
    ∑ i : Fin (n + 1), mulInlInr R M N (Nat.add_sub_of_le i.is_le)
      (prodComponent R M N i (n - i) x) = x := by
  apply Subtype.ext
  simp only [prodComponent, LinearMap.comp_apply, Submodule.coe_sum, coe_mulInlInr_map_component,
    sum_prodMul_map_proj]
  simp [prodMul]

end exteriorPower
