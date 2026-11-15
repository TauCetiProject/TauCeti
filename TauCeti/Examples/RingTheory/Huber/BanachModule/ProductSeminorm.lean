/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.BanachModule.ProductSeminorm

/-!
# Checks for the nonarchimedean product seminorm and completed product norm

In `L ⊗[L] L` over a nonarchimedean normed field, `productSeminorm` evaluates `2 ⊗ 3 - 7 ⊗ 1` to
`1` in every characteristic (including characteristics `2` and `3`), vanishes identically when a
factor is the zero space `Fin 0 → L`, and collapses `1 ⊗ c + d ⊗ 1` to `‖c + d‖` (taking the value
`0` for `d = -c` even when the two-term presentation has positive maximum). On the completion
`CompletedTensor`, `productNorm` evaluates scalar pure tensors `a ⊗ w` to `‖a‖ * ‖w‖`, vanishes
for a zero-dimensional first factor, collapses `1 ⊗ a + b ⊗ 1` in `L ⊗̂_L L` to `‖a + b‖`, gives
the unit-vector distance `‖v - v'‖` when `‖w‖ = 1`, embeds the algebraic tensor product
injectively over a complete nontrivially normed field, and witnesses nondiscreteness of the tensor
topology on `L ⊗[L] L`.
-/

public section

open scoped TensorProduct NNReal Topology
open TauCeti.Huber BanachModule

section AlgebraicSeminorm

variable {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
  {W : Type*} [NormedAddCommGroup W] [IsUltrametricDist W] [NormedSpace L W]

/-- In `L ⊗[L] L`, the product seminorm of `2 ⊗ 3 - 7 ⊗ 1` is `1` in every residue characteristic
(including `2` and `3`), since `2 * 3 - 7 * 1 = -1`. -/
example :
    productSeminorm L L L ((2 : L) ⊗ₜ[L] (3 : L) - (7 : L) ⊗ₜ[L] (1 : L)) = 1 := by
  rw [productSeminorm_eq_norm_lid]
  simp only [map_sub, TensorProduct.lid_tmul, smul_eq_mul]
  have h : (2 : L) * 3 - 7 * 1 = -1 := by ring
  rw [h, norm_neg, norm_one]

/-- Tensoring the zero space `Fin 0 → L` gives product seminorm zero everywhere. -/
example (u : (Fin 0 → L) ⊗[L] W) : productSeminorm L (Fin 0 → L) W u = 0 := by
  simp

/-- In `L ⊗[L] L`, `productSeminorm` sends `1 ⊗ c + d ⊗ 1` to `‖c + d‖`. -/
example (c d : L) :
    productSeminorm L L L ((1 : L) ⊗ₜ[L] c + d ⊗ₜ[L] (1 : L)) = ‖c + d‖ := by
  rw [productSeminorm_eq_norm_lid]
  simp [map_add]

/-- When `d = -c` with `c ≠ 0`, `1 ⊗ c + (-c) ⊗ 1` has product seminorm `0` even though the
displayed two-term presentation has positive maximum `‖c‖`. -/
example {c : L} (hc : c ≠ 0) :
    productSeminorm L L L ((1 : L) ⊗ₜ[L] c + (-c) ⊗ₜ[L] (1 : L)) = 0 ∧
      0 < max (‖(1 : L)‖ * ‖c‖) (‖-c‖ * ‖(1 : L)‖) := by
  refine ⟨?_, ?_⟩
  · rw [productSeminorm_eq_norm_lid]
    simp [map_add]
  · simp [norm_pos_iff.mpr hc]

/-- Over a nontrivially normed nonarchimedean field `L`, `L ⊗[L] L` is nondiscrete in the Banach
tensor topology. -/
example : ¬ @DiscreteTopology (L ⊗[L] L) (banachTensorTopology L L L) :=
  have : Nontrivial (L ⊗[L] L) := (TensorProduct.lid L L).toEquiv.nontrivial
  not_discreteTopology_banachTensorTopology

end AlgebraicSeminorm

section TateBasis

variable {A V W : Type*} [SeminormedCommRing A] [TauCeti.NormedRing.IsTate A]
  [SeminormedAddCommGroup V] [Module A V] [IsBoundedSMul A V]
  [SeminormedAddCommGroup W] [Module A W] [IsBoundedSMul A W]

/-- Over a Tate seminormed commutative ring with contractive actions, the positive-radius balls of
`productSeminorm` form a neighbourhood basis of `0` in `banachTensorTopology`. -/
example :
    (@nhds (V ⊗[A] W) (banachTensorTopology A V W) 0).HasBasis (0 < ·)
      fun r ↦ {u | productSeminorm A V W u < r} :=
  hasBasis_banachTensorTopology ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩
    ⟨1, fun a w ↦ by simpa using norm_smul_le a w⟩

end TateBasis

section CompletedNorm

variable {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
  {V : Type*} [NormedAddCommGroup V] [IsUltrametricDist V] [NormedSpace L V]
  {W : Type*} [NormedAddCommGroup W] [IsUltrametricDist W] [NormedSpace L W]

/-- For a scalar first factor, `productNorm` of `a ⊗ w` is `‖a‖ * ‖w‖`. -/
example (a : L) (w : W) :
    CompletedTensor.productNorm L L W (CompletedTensor.tmul L L W a w) = ‖a‖ * ‖w‖ := by
  simp

/-- A zero-dimensional first factor `Fin 0 → L` gives `productNorm` zero on the entire completion.
-/
example (z : CompletedTensor L (Fin 0 → L) W) :
    CompletedTensor.productNorm L (Fin 0 → L) W z = 0 := by
  simp

/-- In `L ⊗̂_L L`, the completed product norm of `1 ⊗ a + b ⊗ 1` is `‖a + b‖`. -/
example (a b : L) :
    CompletedTensor.productNorm L L L
        (CompletedTensor.tmul L L L 1 a + CompletedTensor.tmul L L L b 1) =
      ‖a + b‖ := by
  rw [CompletedTensor.productNorm_eq_norm_lid]
  simp [map_add]

/-- In `L ⊗̂_L L`, `1 ⊗ a + (-a) ⊗ 1` has completed product norm `0`, strictly smaller than
`max ‖a‖ ‖-a‖` whenever `a ≠ 0`. -/
example {a : L} (ha : a ≠ 0) :
    CompletedTensor.productNorm L L L
        (CompletedTensor.tmul L L L 1 a + CompletedTensor.tmul L L L (-a) 1) <
      max ‖a‖ ‖-a‖ := by
  rw [CompletedTensor.productNorm_eq_norm_lid]
  simpa [map_add] using norm_pos_iff.mpr ha

/-- Tensoring on the right by a vector `w` of norm `1` preserves distances:
`productNorm (v ⊗ w - v' ⊗ w) = ‖v - v'‖`. -/
example (v v' : V) {w : W} (hw : ‖w‖ = 1) :
    CompletedTensor.productNorm L V W
        (CompletedTensor.tmul L V W v w - CompletedTensor.tmul L V W v' w) =
      ‖v - v'‖ :=
  CompletedTensor.productNorm_unitVector v v' hw

/-- Over a complete nontrivially normed nonarchimedean field `L`, the canonical map from the
algebraic tensor product `V ⊗[L] W` into `CompletedTensor L V W` is injective. -/
example {u₁ u₂ : V ⊗[L] W}
    (h : CompletedTensor.toCompletion L V W u₁ = CompletedTensor.toCompletion L V W u₂) :
    u₁ = u₂ :=
  CompletedTensor.injective_tensorProduct_of_field L V W h

end CompletedNorm
