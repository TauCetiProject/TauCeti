/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import TauCeti.RingTheory.Huber.BanachModule.ProductSeminorm

/-!
# Checks for the nonarchimedean product seminorm and completed product norm

This file tests `TauCeti.Huber.BanachModule.productSeminorm`,
`TauCeti.Huber.hasBasis_banachTensorTopology`, and
`TauCeti.Huber.BanachModule.CompletedTensor.productNorm` on concrete and degenerate cases:

* in `L ⊗[L] L`, `2 ⊗ₜ 3 - 7 ⊗ₜ 1` has product seminorm `1`, including on `ℚ_[2]` and `ℚ_[3]`
  where `2` and `3` respectively have strictly smaller norm than `1`;
* tensoring the zero module `Fin 0 → K` produces zero `productSeminorm` and zero `productNorm`
  everywhere;
* in `K ⊗[K] K`, `1 ⊗ₜ c + d ⊗ₜ 1` has product seminorm `‖c + d‖`, vanishing for `d = -c` even
  when the displayed two-term presentation has positive maximum `‖c‖`;
* on `V ⊗̂_L W`, scalar first factors satisfy `|a ⊗ w| = ‖a‖ * ‖w‖`, and in `ℚ_[2] ⊗̂_{ℚ_[2]} ℚ_[2]`
  the sum `1 ⊗ 1 + 1 ⊗ 1` has norm `1 / 2 < 1`;
* on `ℚ_[2]` equipped with the rescaled norm `(3 / 4) * ‖x‖` (whose nonzero norms miss
  `[7 / 8, 1]`), `|1 ⊗ 1| = 3 / 4` directly in the original norm without renorming, and the
  open balls of `productSeminorm` and `productNorm` form neighbourhood bases of `0`.
-/

public section

open Filter Set TensorProduct Topology TauCeti.Huber BanachModule

namespace TauCeti.ProductSeminormExample

section Algebraic

/-- In `L ⊗[L] L` for an ultrametric seminormed commutative ring with `‖1‖ = 1`, the tensor
`2 ⊗ₜ 3 - 7 ⊗ₜ 1` corresponds under `TensorProduct.lid L L` to `2 * 3 - 7 = -1`, so its product
seminorm is `1`. -/
example {L : Type*} [SeminormedCommRing L] [NormOneClass L] [IsUltrametricDist L]
    [IsBoundedSMul L L] :
    productSeminorm L L L ((2 : L) ⊗ₜ[L] 3 - 7 ⊗ₜ[L] 1) = 1 := by
  have hlid : TensorProduct.lid L L ((2 : L) ⊗ₜ[L] 3 - 7 ⊗ₜ[L] 1) = -1 := by
    simp only [map_sub, TensorProduct.lid_tmul, smul_eq_mul]
    ring
  rw [productSeminorm_eq_norm_lid, hlid, norm_neg, norm_one]

/-- In residue characteristic `2` (`L = ℚ_[2]`, where `‖(2 : ℚ_[2])‖ = 1 / 2`), the product
seminorm of `2 ⊗ₜ 3 - 7 ⊗ₜ 1` is `1`. -/
example : productSeminorm ℚ_[2] ℚ_[2] ℚ_[2] (2 ⊗ₜ[ℚ_[2]] 3 - 7 ⊗ₜ[ℚ_[2]] 1) = 1 ∧
    ‖(2 : ℚ_[2])‖ = 1 / 2 := by
  refine ⟨?_, by simpa using (Padic.norm_p (p := 2))⟩
  have hlid : TensorProduct.lid ℚ_[2] ℚ_[2] (2 ⊗ₜ[ℚ_[2]] 3 - 7 ⊗ₜ[ℚ_[2]] 1) = -1 := by
    simp only [map_sub, TensorProduct.lid_tmul, smul_eq_mul]
    norm_num
  rw [productSeminorm_eq_norm_lid, hlid, norm_neg, norm_one]

/-- In residue characteristic `3` (`L = ℚ_[3]`, where `‖(3 : ℚ_[3])‖ = 1 / 3`), the product
seminorm of `2 ⊗ₜ 3 - 7 ⊗ₜ 1` is `1`. -/
example : productSeminorm ℚ_[3] ℚ_[3] ℚ_[3] (2 ⊗ₜ[ℚ_[3]] 3 - 7 ⊗ₜ[ℚ_[3]] 1) = 1 ∧
    ‖(3 : ℚ_[3])‖ = 1 / 3 := by
  refine ⟨?_, by simpa using (Padic.norm_p (p := 3))⟩
  have hlid : TensorProduct.lid ℚ_[3] ℚ_[3] (2 ⊗ₜ[ℚ_[3]] 3 - 7 ⊗ₜ[ℚ_[3]] 1) = -1 := by
    simp only [map_sub, TensorProduct.lid_tmul, smul_eq_mul]
    norm_num
  rw [productSeminorm_eq_norm_lid, hlid, norm_neg, norm_one]

/-- Tensoring the zero space `Fin 0 → K` gives `productSeminorm = 0` everywhere. -/
example {K W : Type*} [SeminormedCommRing K]
    [SeminormedAddCommGroup W] [Module K W] (u : (Fin 0 → K) ⊗[K] W) :
    productSeminorm K (Fin 0 → K) W u = 0 := by
  rw [Subsingleton.elim u 0, map_zero]

/-- In `K ⊗[K] K`, `productSeminorm K K K (1 ⊗ₜ c + d ⊗ₜ 1) = ‖c + d‖`. -/
example {K : Type*} [SeminormedCommRing K] [NormOneClass K] [IsUltrametricDist K]
    [IsBoundedSMul K K] (c d : K) :
    productSeminorm K K K (1 ⊗ₜ[K] c + d ⊗ₜ[K] 1) = ‖c + d‖ := by
  rw [productSeminorm_eq_norm_lid]
  simp [add_comm c d]

/-- For `d = -c` with `‖c‖ ≠ 0`, `1 ⊗ₜ c + (-c) ⊗ₜ 1` has product seminorm `0` even though the
displayed two-term presentation has positive maximum `max (‖1‖ * ‖c‖) (‖-c‖ * ‖1‖) = ‖c‖`. -/
example {K : Type*} [SeminormedCommRing K] [NormOneClass K] [IsUltrametricDist K]
    [IsBoundedSMul K K] {c : K} (hc : ‖c‖ ≠ 0) :
    productSeminorm K K K (1 ⊗ₜ[K] c + (-c) ⊗ₜ[K] 1) = 0 ∧
      0 < max (‖(1 : K)‖ * ‖c‖) (‖-c‖ * ‖(1 : K)‖) := by
  refine ⟨?_, ?_⟩
  · rw [productSeminorm_eq_norm_lid]
    simp
  · simp only [norm_one, one_mul, norm_neg, mul_one, max_self]
    exact lt_of_le_of_ne (norm_nonneg c) hc.symm

end Algebraic

section Completed

/-- Tensoring the zero-dimensional space `Fin 0 → K` on the left gives `productNorm = 0` for every
completed tensor. -/
example {K W : Type*} [SeminormedCommRing K] [IsBoundedSMul K K]
    [SeminormedAddCommGroup W] [Module K W] (z : CompletedTensor K (Fin 0 → K) W) :
    CompletedTensor.productNorm K (Fin 0 → K) W z = 0 :=
  (CompletedTensor.denseRange_toCompletion K (Fin 0 → K) W).induction_on z
    (isClosed_eq CompletedTensor.continuous_productNorm continuous_const) fun u ↦ by
      rw [Subsingleton.elim u 0, map_zero, CompletedTensor.productNorm_zero]

/-- For a scalar first factor over a complete nontrivially normed ultrametric field `L` and an
ultrametric normed `L`-space `W`, `|a ⊗ w| = ‖a‖ * ‖w‖` on the completion. -/
example {L W : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
    [NormedAddCommGroup W] [IsUltrametricDist W] [NormedSpace L W] (a : L) (w : W) :
    CompletedTensor.productNorm L L W (CompletedTensor.tmul L L W a w) = ‖a‖ * ‖w‖ :=
  CompletedTensor.productNorm_tmul a w

/-- In `L ⊗̂_L L`, the norm of `1 ⊗ a + b ⊗ 1` is `‖a + b‖`. -/
example {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
    (a b : L) :
    CompletedTensor.productNorm L L L
      (CompletedTensor.tmul L L L 1 a + CompletedTensor.tmul L L L b 1) = ‖a + b‖ := by
  rw [CompletedTensor.productNorm_eq_norm_lid, map_add, CompletedTensor.lid_tmul,
    CompletedTensor.lid_tmul]
  simp

/-- In `ℚ_[2] ⊗̂_{ℚ_[2]} ℚ_[2]`, `1 ⊗ 1 + 1 ⊗ 1` has norm `1 / 2`, strictly below
`max ‖(1 : ℚ_[2])‖ ‖(1 : ℚ_[2])‖ = 1`. -/
example :
    CompletedTensor.productNorm ℚ_[2] ℚ_[2] ℚ_[2]
      (CompletedTensor.tmul ℚ_[2] ℚ_[2] ℚ_[2] 1 1 +
        CompletedTensor.tmul ℚ_[2] ℚ_[2] ℚ_[2] 1 1) = 1 / 2 ∧
      (1 / 2 : ℝ) < max ‖(1 : ℚ_[2])‖ ‖(1 : ℚ_[2])‖ := by
  refine ⟨?_, by norm_num⟩
  rw [CompletedTensor.productNorm_eq_norm_lid, map_add, CompletedTensor.lid_tmul]
  simpa [one_add_one_eq_two] using (Padic.norm_p (p := 2))

end Completed

noncomputable section ScaledNorm

/-- A wrapper around `ℚ_[2]` equipped with the rescaled norm `(3 / 4) * ‖x.val‖`. -/
@[ext]
structure ScaledQ2 where
  /-- The underlying `2`-adic rational number. -/
  val : ℚ_[2]

instance : AddCommGroup ScaledQ2 where
  zero := ⟨0⟩
  neg x := ⟨-x.val⟩
  add x y := ⟨x.val + y.val⟩
  sub x y := ⟨x.val - y.val⟩
  nsmul n x := ⟨n • x.val⟩
  zsmul n x := ⟨n • x.val⟩
  add_assoc _ _ _ := ScaledQ2.ext (add_assoc _ _ _)
  zero_add _ := ScaledQ2.ext (zero_add _)
  add_zero _ := ScaledQ2.ext (add_zero _)
  neg_add_cancel _ := ScaledQ2.ext (neg_add_cancel _)
  add_comm _ _ := ScaledQ2.ext (add_comm _ _)
  sub_eq_add_neg _ _ := ScaledQ2.ext (sub_eq_add_neg _ _)
  nsmul_zero _ := ScaledQ2.ext (zero_smul _ _)
  nsmul_succ _ _ := ScaledQ2.ext (succ_nsmul _ _)
  zsmul_zero' _ := ScaledQ2.ext (zero_zsmul _)
  zsmul_succ' _ _ := ScaledQ2.ext (SubNegMonoid.zsmul_succ' _ _)
  zsmul_neg' _ _ := ScaledQ2.ext (SubNegMonoid.zsmul_neg' _ _)

/-- The rescaled `2`-adic additive group norm `x ↦ (3 / 4) * ‖x.val‖` on `ScaledQ2`. -/
def scaledQ2Norm : AddGroupNorm ScaledQ2 where
  toFun x := (3 / 4 : ℝ) * ‖x.val‖
  map_zero' := by change (3 / 4 : ℝ) * ‖(0 : ℚ_[2])‖ = 0; simp
  add_le' x y := by
    change (3 / 4 : ℝ) * ‖x.val + y.val‖ ≤ (3 / 4 : ℝ) * ‖x.val‖ + (3 / 4 : ℝ) * ‖y.val‖
    linarith [norm_add_le x.val y.val]
  neg' x := by change (3 / 4 : ℝ) * ‖-x.val‖ = (3 / 4 : ℝ) * ‖x.val‖; rw [norm_neg]
  eq_zero_of_map_eq_zero' x hx := ScaledQ2.ext <| norm_eq_zero.mp <| by linarith

instance : NormedAddCommGroup ScaledQ2 :=
  scaledQ2Norm.toNormedAddCommGroup

/-- The norm of `x : ScaledQ2` is `(3 / 4) * ‖x.val‖`. -/
@[simp]
theorem norm_scaledQ2 (x : ScaledQ2) : ‖x‖ = (3 / 4 : ℝ) * ‖x.val‖ := (rfl)

instance : IsUltrametricDist ScaledQ2 :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y ↦ by
    simp only [norm_scaledQ2, ← mul_max_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 3 / 4)]
    exact mul_le_mul_of_nonneg_left (IsUltrametricDist.norm_add_le_max x.val y.val) (by positivity)

instance : Module ℚ_[2] ScaledQ2 where
  smul a x := ⟨a * x.val⟩
  one_smul x := ScaledQ2.ext (one_mul x.val)
  mul_smul a b x := ScaledQ2.ext (mul_assoc a b x.val)
  smul_zero a := ScaledQ2.ext (mul_zero a)
  smul_add a x y := ScaledQ2.ext (mul_add a x.val y.val)
  add_smul a b x := ScaledQ2.ext (add_mul a b x.val)
  zero_smul x := ScaledQ2.ext (zero_mul x.val)

instance : NormedSpace ℚ_[2] ScaledQ2 where
  norm_smul_le a x := by
    change (3 / 4 : ℝ) * ‖a * x.val‖ ≤ ‖a‖ * ((3 / 4 : ℝ) * ‖x.val‖)
    rw [norm_mul]
    linarith

/-- Every nonzero vector in `ScaledQ2` has norm in `(3 / 4) * 2 ^ ℤ`, which misses `[7 / 8, 1]`,
yet `CompletedTensor.productNorm` evaluates `|⟨1⟩ ⊗ 1| = 3 / 4` directly in the original norm. -/
example :
    (∀ x : ScaledQ2, x ≠ 0 → ‖x‖ ∉ Icc (7 / 8 : ℝ) 1) ∧
      CompletedTensor.productNorm ℚ_[2] ScaledQ2 ℚ_[2]
        (CompletedTensor.tmul ℚ_[2] ScaledQ2 ℚ_[2] ⟨1⟩ 1) = 3 / 4 := by
  refine ⟨fun x hx hmem ↦ ?_, ?_⟩
  · have hxval : x.val ≠ 0 := fun h ↦ hx (ScaledQ2.ext h)
    rw [norm_scaledQ2, Padic.norm_eq_zpow_neg_valuation hxval, Nat.cast_ofNat, mem_Icc] at hmem
    rcases le_or_gt 1 x.val.valuation with hge | hlt
    · have hpow : (2 : ℝ) ^ (-x.val.valuation) ≤ 1 / 2 :=
        (zpow_le_zpow_right₀ (by norm_num) (by omega : -x.val.valuation ≤ -1)).trans_eq
          (by norm_num)
      linarith [hmem.1]
    · have hle0 : x.val.valuation ≤ 0 := by omega
      rcases eq_or_lt_of_le hle0 with hzero | hneg
      · rw [hzero] at hmem
        norm_num at hmem
      · have hpow : (2 : ℝ) ≤ (2 : ℝ) ^ (-x.val.valuation) :=
          (by norm_num : (2 : ℝ) = (2 : ℝ) ^ (1 : ℤ)).trans_le
            (zpow_le_zpow_right₀ (by norm_num) (by omega))
        linarith [hmem.2]
  · rw [CompletedTensor.productNorm_tmul, norm_scaledQ2]
    norm_num

/-- On `ScaledQ2 ⊗[ℚ_[2]] ℚ_[2]` and its completion, the open balls of `productSeminorm` and
`productNorm` form neighbourhood bases of `0`, `toCompletion` is injective, and tensoring with the
unit vector `1 : ℚ_[2]` preserves distances. -/
example (x y : ScaledQ2) :
    (@nhds (ScaledQ2 ⊗[ℚ_[2]] ℚ_[2]) (banachTensorTopology ℚ_[2] ScaledQ2 ℚ_[2]) 0).HasBasis
      (0 < ·) (fun r ↦ {u | productSeminorm ℚ_[2] ScaledQ2 ℚ_[2] u < r}) ∧
    (𝓝 (0 : CompletedTensor ℚ_[2] ScaledQ2 ℚ_[2])).HasBasis
      (0 < ·) (fun r ↦ {z | CompletedTensor.productNorm ℚ_[2] ScaledQ2 ℚ_[2] z < r}) ∧
    Function.Injective (CompletedTensor.toCompletion ℚ_[2] ScaledQ2 ℚ_[2]) ∧
    CompletedTensor.productNorm ℚ_[2] ScaledQ2 ℚ_[2]
      (CompletedTensor.tmul ℚ_[2] ScaledQ2 ℚ_[2] x 1 -
        CompletedTensor.tmul ℚ_[2] ScaledQ2 ℚ_[2] y 1) = ‖x - y‖ :=
  ⟨hasBasis_banachTensorTopology ℚ_[2] ScaledQ2 ℚ_[2],
    CompletedTensor.hasBasis_nhds_zero_productNorm ℚ_[2] ScaledQ2 ℚ_[2],
    CompletedTensor.toCompletion_injective ℚ_[2] ScaledQ2 ℚ_[2],
    CompletedTensor.productNorm_unitVector x y norm_one⟩

end ScaledNorm

end TauCeti.ProductSeminormExample
