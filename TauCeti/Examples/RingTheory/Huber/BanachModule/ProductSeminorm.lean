/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.BanachModule.ProductSeminorm
import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# Checks for the nonarchimedean product seminorm and completed tensor norm

In `L ⊗[L] L` over any ultrametric seminormed commutative ring with `‖1‖ = 1`, the tensor
`2 ⊗ₜ 3 - 7 ⊗ₜ 1` equals `-1 ⊗ₜ 1` and therefore has product seminorm `1`, including over `ℚ_[2]`
and `ℚ_[3]` where `2` or `3` has strictly smaller `p`-adic norm. Tensoring with the rank-zero module
`Fin 0 → A` gives seminorm `0` everywhere and a zero completed tensor product. In `K ⊗[K] K`,
`1 ⊗ₜ c + d ⊗ₜ 1` has product seminorm `‖c + d‖`; at `d = -c` with `c ≠ 0` the seminorm vanishes
even though the displayed two-term presentation has positive maximum `‖c‖`. On `CompletedTensor`,
the completed product norm agrees with `productSeminorm` on algebraic tensors, makes `lid` an
isometry, and makes multiplication on `ℚ_[p]` lift with operator norm `1`.
-/

public section

open scoped NNReal TensorProduct
open TauCeti.Huber TauCeti.Huber.BanachModule

section Ring

variable {L : Type*} [SeminormedCommRing L] [IsUltrametricDist L] [NormOneClass L]

/-- In `L ⊗[L] L`, `2 ⊗ₜ 3 - 7 ⊗ₜ 1` collapses under `lid` to `2 * 3 - 7 * 1 = -1`, so its product
seminorm is `1` in every residue characteristic. -/
example : productSeminorm L L L ((2 : L) ⊗ₜ[L] 3 - 7 ⊗ₜ[L] 1) = 1 := by
  rw [productSeminorm_eq_norm_lid]
  have hlid : TensorProduct.lid L L ((2 : L) ⊗ₜ[L] 3 - 7 ⊗ₜ[L] 1) = -1 := by
    simp only [map_sub, TensorProduct.lid_tmul, smul_eq_mul]
    ring
  rw [hlid, norm_neg, norm_one]

/-- In `L ⊗[L] L`, `productSeminorm (1 ⊗ₜ c + d ⊗ₜ 1) = ‖c + d‖`. -/
example (c d : L) : productSeminorm L L L ((1 : L) ⊗ₜ[L] c + d ⊗ₜ[L] 1) = ‖c + d‖ := by
  rw [productSeminorm_eq_norm_lid]
  have hlid : TensorProduct.lid L L ((1 : L) ⊗ₜ[L] c + d ⊗ₜ[L] 1) = c + d := by
    simp only [map_add, TensorProduct.lid_tmul, smul_eq_mul]
    ring
  rw [hlid]

end Ring

section Degenerate

/-- Tensoring the zero space `Fin 0 → A` on the left gives product seminorm `0` everywhere. -/
example {A W : Type*} [SeminormedCommRing A]
    [SeminormedAddCommGroup W] [Module A W] (z : (Fin 0 → A) ⊗[A] W) :
    productSeminorm A (Fin 0 → A) W z = 0 := by
  rw [Subsingleton.elim z 0, map_zero]

/-- On `CompletedTensor A (Fin 0 → A) W`, every element is `0` and has norm `0`. -/
example {A W : Type*} [SeminormedCommRing A] [TauCeti.NormedRing.IsTate A]
    [SeminormedAddCommGroup W] [Module A W] [IsBoundedSMul A W]
    (x : CompletedTensor A (Fin 0 → A) W) : x = 0 ∧ ‖x‖ = 0 := by
  have hx : x = 0 := by
    refine (CompletedTensor.denseRange_toCompletion A (Fin 0 → A) W).induction_on x
      (isClosed_eq continuous_id continuous_const) fun z ↦ ?_
    rw [Subsingleton.elim z 0, map_zero]
  exact ⟨hx, by simp [hx]⟩

end Degenerate

section Cancellation

/-- For `c ≠ 0` in an ultrametric normed field `K`, `1 ⊗ₜ c + (-c) ⊗ₜ 1` has product seminorm `0`,
even though the displayed two-term presentation `![1, -c]`, `![c, 1]` has positive maximum `‖c‖`. -/
example {K : Type*} [NormedField K] [IsUltrametricDist K] {c : K} (hc : c ≠ 0) :
    let v : Fin 2 → K := ![1, -c]
    let w : Fin 2 → K := ![c, 1]
    (∑ i, v i ⊗ₜ[K] w i) = (1 : K) ⊗ₜ[K] c + (-c) ⊗ₜ[K] 1 ∧
      productSeminorm K K K (∑ i, v i ⊗ₜ[K] w i) = 0 ∧
      (↑(Finset.univ.sup fun i ↦ ‖v i‖₊ * ‖w i‖₊) : ℝ) = ‖c‖ ∧ 0 < ‖c‖ := by
  refine ⟨by simp [Fin.sum_univ_two], ?_, ?_, norm_pos_iff.mpr hc⟩
  · simp [Fin.sum_univ_two, productSeminorm_eq_norm_lid]
  · simp [Fin.univ_succ]

end Cancellation

section PadicChecks

/-- Over `ℚ_[2]` (residue characteristic `2`, where `‖2‖ = 1/2`), both `productSeminorm` and the
completed tensor norm of `2 ⊗ 3 - 7 ⊗ 1` equal `1`. -/
example :
    productSeminorm ℚ_[2] ℚ_[2] ℚ_[2] ((2 : ℚ_[2]) ⊗ₜ[ℚ_[2]] 3 - 7 ⊗ₜ[ℚ_[2]] 1) = 1 ∧
      ‖CompletedTensor.tmul ℚ_[2] ℚ_[2] ℚ_[2] 2 3 -
        CompletedTensor.tmul ℚ_[2] ℚ_[2] ℚ_[2] 7 1‖ = 1 := by
  have h : productSeminorm ℚ_[2] ℚ_[2] ℚ_[2] ((2 : ℚ_[2]) ⊗ₜ[ℚ_[2]] 3 - 7 ⊗ₜ[ℚ_[2]] 1) = 1 := by
    rw [productSeminorm_eq_norm_lid]
    have hlid : TensorProduct.lid ℚ_[2] ℚ_[2] ((2 : ℚ_[2]) ⊗ₜ[ℚ_[2]] 3 - 7 ⊗ₜ[ℚ_[2]] 1) = -1 := by
      simp only [map_sub, TensorProduct.lid_tmul, smul_eq_mul]
      ring
    rw [hlid, norm_neg, norm_one]
  refine ⟨h, ?_⟩
  rw [← CompletedTensor.toCompletion_tmul, ← CompletedTensor.toCompletion_tmul, ← map_sub,
    CompletedTensor.norm_toCompletion, h]

/-- Over `ℚ_[3]` (residue characteristic `3`, where `‖3‖ = 1/3`), both `productSeminorm` and the
completed tensor norm of `2 ⊗ 3 - 7 ⊗ 1` equal `1`. -/
example :
    productSeminorm ℚ_[3] ℚ_[3] ℚ_[3] ((2 : ℚ_[3]) ⊗ₜ[ℚ_[3]] 3 - 7 ⊗ₜ[ℚ_[3]] 1) = 1 ∧
      ‖CompletedTensor.tmul ℚ_[3] ℚ_[3] ℚ_[3] 2 3 -
        CompletedTensor.tmul ℚ_[3] ℚ_[3] ℚ_[3] 7 1‖ = 1 := by
  have h : productSeminorm ℚ_[3] ℚ_[3] ℚ_[3] ((2 : ℚ_[3]) ⊗ₜ[ℚ_[3]] 3 - 7 ⊗ₜ[ℚ_[3]] 1) = 1 := by
    rw [productSeminorm_eq_norm_lid]
    have hlid : TensorProduct.lid ℚ_[3] ℚ_[3] ((2 : ℚ_[3]) ⊗ₜ[ℚ_[3]] 3 - 7 ⊗ₜ[ℚ_[3]] 1) = -1 := by
      simp only [map_sub, TensorProduct.lid_tmul, smul_eq_mul]
      ring
    rw [hlid, norm_neg, norm_one]
  refine ⟨h, ?_⟩
  rw [← CompletedTensor.toCompletion_tmul, ← CompletedTensor.toCompletion_tmul, ← map_sub,
    CompletedTensor.norm_toCompletion, h]

/-- In `ℚ_[2] ⊗̂ ℚ_[2]`, `2⁻¹ ⊗ 4` has norm `1/2`, matching `‖(2 : ℚ_[2])‖` after scalar
balancing. -/
example : ‖CompletedTensor.tmul ℚ_[2] ℚ_[2] ℚ_[2] (2 : ℚ_[2])⁻¹ 4‖ = (2 : ℝ)⁻¹ := by
  rw [← CompletedTensor.norm_lid, CompletedTensor.lid_tmul, smul_eq_mul]
  have hmul : (2 : ℚ_[2])⁻¹ * 4 = 2 := by norm_num
  rw [hmul]
  simpa using Padic.norm_p (p := 2)

/-- Lifting multiplication `ℚ_[p] × ℚ_[p] → ℚ_[p]` via `CompletedTensor.liftIsometry` preserves the
operator norm (`1`). -/
example (p : ℕ) [Fact p.Prime] :
    ‖CompletedTensor.liftIsometry ℚ_[p] ℚ_[p] ℚ_[p] ℚ_[p]
      (ContinuousLinearMap.mul ℚ_[p] ℚ_[p])‖ = 1 := by
  rw [LinearIsometryEquiv.norm_map]
  exact ContinuousLinearMap.opNorm_mul ℚ_[p] ℚ_[p]

end PadicChecks

section Coherence

/-- `CompletedTensor.instNormedAddCommGroup` preserves the original `AddCommGroup`, `UniformSpace`,
and `TopologicalSpace` instances from `CompletedTensor` up to `rfl`. -/
example {A V W : Type*} [SeminormedCommRing A] [TauCeti.NormedRing.IsTate A]
    [SeminormedAddCommGroup V] [Module A V] [IsBoundedSMul A V]
    [SeminormedAddCommGroup W] [Module A W] [IsBoundedSMul A W] :
    (CompletedTensor.instNormedAddCommGroup (A := A) (V := V) (W := W)).toAddCommGroup =
        CompletedTensor.instAddCommGroup A V W ∧
      (CompletedTensor.instNormedAddCommGroup (A := A) (V := V) (W := W)).toUniformSpace =
        CompletedTensor.instUniformSpace A V W ∧
      (CompletedTensor.instNormedAddCommGroup (A := A) (V := V)
          (W := W)).toUniformSpace.toTopologicalSpace =
        (CompletedTensor.instUniformSpace A V W).toTopologicalSpace :=
  ⟨rfl, rfl, rfl⟩

/-- Over a nontrivially normed field `K`, `CompletedTensor.instNormedSpace` preserves the original
`CompletedTensor.instModule K V W` instance up to `rfl`. -/
example {K V W : Type*} [NontriviallyNormedField K]
    [SeminormedAddCommGroup V] [NormedSpace K V]
    [SeminormedAddCommGroup W] [NormedSpace K W] :
    (CompletedTensor.instNormedSpace (K := K) (V := V) (W := W)).toModule =
      CompletedTensor.instModule K V W :=
  rfl

end Coherence
