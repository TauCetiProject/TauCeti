/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.Basic
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import TauCeti.Geometry.Symplectic.Lagrangian.Basic
import TauCeti.NumberTheory.Real.Irrational

/-!
# Cyclic groups of rotations of `ℂ^ι` and their fixed subspaces

The rotation `TauCeti.weightRotation θ : z_j ↦ exp(i θ_j) z_j` of `ℂ^ι`, written in real
coordinates `z_j = q_j + i p_j` as `EuclideanSpace ℝ ι × EuclideanSpace ℝ ι`, preserves the standard
symplectic form `Σ dq_j ∧ dp_j` (`TauCeti.stdSymplecticForm_weightRotation`) and the Euclidean
norm of every coordinate. This file studies the cyclic group it generates, whose elements are the
rotations by the integer multiples `n • θ`, `n : ℤ`; the nonnegative powers are
`weightRotation θ ^ n = weightRotation (n • θ)` for `n : ℕ` (`TauCeti.weightRotation_nsmul`).

* The group is infinite exactly when one of the angles is an irrational multiple of `2π`
  (`TauCeti.orderOf_weightRotation_eq_zero_iff`).
* Its common fixed set is the fixed set of the generator
  (`TauCeti.forall_weightRotation_zsmul_apply_eq_self_iff_apply_eq_self`): the points `z` with
  `z_j = 0` for every angle `θ_j ∉ 2πℤ` (`TauCeti.forall_weightRotation_zsmul_apply_eq_self_iff`).
* The fixed subspace has real dimension twice the number of angles in `2πℤ`
  (`TauCeti.finrank_eqLocus_weightRotation`).
* The fixed subspace is a symplectic subspace
  (`TauCeti.isSymplectic_eqLocus_weightRotation`). The rotation commutes with the complex
  structure `J(q, p) = (-p, q)`, multiplication by `i`
  (`TauCeti.weightRotation_product_apply`), so `J` preserves the fixed subspace, and `ω` tames `J`
  (`TauCeti.stdSymplecticForm_tames_product`).

For the rotation of a single coordinate `z_{j₀}` of `ℂ^ι` by an angle `θ₀ ∉ 2πℤ`, the fixed
subspace and the common fixed set of the cyclic group are the coordinate subspace `z_{j₀} = 0`, of
real dimension `2 (|ι| - 1)` (`TauCeti.mem_eqLocus_weightRotation_single_iff`,
`TauCeti.forall_weightRotation_zsmul_single_apply_eq_self_iff`,
`TauCeti.finrank_eqLocus_weightRotation_single`). When `θ₀ = 2π a` with `a` irrational, the
group is moreover infinite cyclic (`Irrational.orderOf_weightRotation_single`, and the
specializations `Irrational.mem_eqLocus_weightRotation_single_iff`,
`Irrational.forall_weightRotation_zsmul_single_apply_eq_self_iff`,
`Irrational.finrank_eqLocus_weightRotation_single`). For `ℂ²` and `j₀` the first coordinate, the
fixed locus is the plane `{0} × ℂ`, of dimension `2`. The group is not finite, and its fixed locus
is a symplectic subspace because the group preserves both `ω` and the Euclidean metric. By
contrast the shear `(q, p) ↦ (q + p, p)` of `ℝ²` preserves `ω` and no metric, and its fixed line
is Lagrangian (`TauCeti.fixedPoints_symplecticShear`,
`TauCeti.SymplecticForm.isLagrangian_prod_top_bot`).

## References

* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Homework 21, exercise 2 (fixed loci of symplectic actions preserving a metric).
-/

public section

open Real Module

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- **Infinite cyclic groups of rotations.** The rotation by the angles `θ` has infinite order
exactly when some `θ_j` is an irrational multiple of `2π`. -/
theorem orderOf_weightRotation_eq_zero_iff (θ : ι → ℝ) :
    orderOf (weightRotation θ) = 0 ↔ ∃ j, Irrational (θ j / (2 * π)) := by
  have : Fact (0 < 2 * π) := ⟨two_pi_pos⟩
  -- The rotation has finite order exactly when the angles have finite order in `(ℝ / 2πℤ)^ι`.
  have hfin : IsOfFinOrder (weightRotation θ) ↔
      IsOfFinAddOrder (fun j ↦ (θ j : AddCircle (2 * π))) := by
    simp only [isOfFinOrder_iff_pow_eq_one, isOfFinAddOrder_iff_nsmul_eq_zero,
      ← weightRotation_nsmul, ContinuousLinearMap.one_def, weightRotation_eq_id_iff, funext_iff,
      Pi.smul_apply, Pi.zero_apply, ← AddCircle.coe_nsmul, AddCircle.coe_eq_zero_iff, zsmul_eq_mul]
  have hpi : IsOfFinAddOrder (fun j ↦ (θ j : AddCircle (2 * π))) ↔
      ∀ j, IsOfFinAddOrder (θ j : AddCircle (2 * π)) :=
    ⟨IsOfFinAddOrder.apply, IsOfFinAddOrder.pi⟩
  rw [orderOf_eq_zero_iff, hfin, hpi]
  simp [AddCircle.isOfFinAddOrder_iff_exists_rat_eq_div, Irrational]

/-- The fixed subspace of the rotation by the angles `θ` is the subspace of `z` with
`z_j = q_j + i p_j = 0` for every angle `θ_j ∉ 2πℤ`. -/
theorem mem_eqLocus_weightRotation_iff (θ : ι → ℝ)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    x ∈ LinearMap.eqLocus (weightRotation θ).toLinearMap LinearMap.id ↔
      ∀ j, (¬ ∃ k : ℤ, k * (2 * π) = θ j) → x.1 j = 0 ∧ x.2 j = 0 := by
  rw [LinearMap.mem_eqLocus, ContinuousLinearMap.coe_coe, LinearMap.id_apply,
    weightRotation_apply_eq_self_iff]
  exact forall_congr' fun j ↦ by tauto

/-- The common fixed points of the cyclic group generated by a rotation are the fixed points of the
rotation. -/
theorem forall_weightRotation_zsmul_apply_eq_self_iff_apply_eq_self (θ : ι → ℝ)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    (∀ n : ℤ, weightRotation (n • θ) x = x) ↔ weightRotation θ x = x := by
  refine ⟨fun h ↦ by simpa using h 1, fun h n ↦ ?_⟩
  rw [weightRotation_apply_eq_self_iff] at h ⊢
  intro j hj
  obtain ⟨k, hk⟩ := h j hj
  exact ⟨n * k, by rw [Pi.smul_apply, zsmul_eq_mul, ← hk]; push_cast; ring⟩

/-- The common fixed points of the cyclic group generated by a rotation are the points `z` with
`z_j = 0` for every angle `θ_j ∉ 2πℤ`. -/
theorem forall_weightRotation_zsmul_apply_eq_self_iff (θ : ι → ℝ)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    (∀ n : ℤ, weightRotation (n • θ) x = x) ↔
      ∀ j, (¬ ∃ k : ℤ, k * (2 * π) = θ j) → x.1 j = 0 ∧ x.2 j = 0 := by
  rw [forall_weightRotation_zsmul_apply_eq_self_iff_apply_eq_self, ←
    mem_eqLocus_weightRotation_iff, LinearMap.mem_eqLocus, ContinuousLinearMap.coe_coe,
    LinearMap.id_apply]

/-- **Fixed directions of a rotation.** The fixed subspace of the rotation by the angles `θ` has
real dimension twice the number of angles `θ_j ∈ 2πℤ`. -/
theorem finrank_eqLocus_weightRotation (θ : ι → ℝ) :
    finrank ℝ (LinearMap.eqLocus (weightRotation θ).toLinearMap LinearMap.id) =
      2 * {j | ∃ k : ℤ, k * (2 * π) = θ j}.ncard :=
  finrank_eq_two_mul_ncard_of_mem_iff _ fun x ↦ by
    simpa only [Set.mem_ofPred_eq] using mem_eqLocus_weightRotation_iff θ x

/-- **The fixed subspace of a rotation is symplectic** for the standard symplectic form. -/
theorem isSymplectic_eqLocus_weightRotation (θ : ι → ℝ) :
    (stdSymplecticForm (V := EuclideanSpace ℝ ι)).IsSymplectic
      (LinearMap.eqLocus (weightRotation θ).toLinearMap LinearMap.id) :=
  stdSymplecticForm_tames_product.isSymplectic_of_mem_invtSubmodule <|
    (Module.End.mem_invtSubmodule _).2 fun x hx ↦ by
      rw [LinearMap.mem_eqLocus, ContinuousLinearMap.coe_coe, LinearMap.id_apply] at hx
      rw [Submodule.mem_comap, LinearMap.mem_eqLocus, ContinuousLinearMap.coe_coe,
        LinearMap.id_apply]
      exact (weightRotation_product_apply θ x).trans (congrArg _ hx)

/-! ### Rotating one coordinate -/

variable [DecidableEq ι] {θ₀ : ℝ}

/-- The fixed subspace of the rotation of the coordinate `z_{j₀}` of `ℂ^ι` by an angle
`θ₀ ∉ 2πℤ` is the coordinate subspace `z_{j₀} = 0`. -/
theorem mem_eqLocus_weightRotation_single_iff (hθ₀ : ∀ k : ℤ, (k : ℝ) * (2 * π) ≠ θ₀) (j₀ : ι)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    x ∈ LinearMap.eqLocus (weightRotation (Pi.single j₀ θ₀)).toLinearMap LinearMap.id ↔
      x.1 j₀ = 0 ∧ x.2 j₀ = 0 := by
  rw [mem_eqLocus_weightRotation_iff]
  refine ⟨fun h ↦ h j₀ ?_, fun h j hj ↦ ?_⟩
  · rw [Pi.single_eq_same]
    exact fun ⟨k, hk⟩ ↦ hθ₀ k hk
  by_cases hj₀ : j = j₀
  · exact hj₀ ▸ h
  · exact absurd ⟨0, by rw [Pi.single_eq_of_ne hj₀]; simp⟩ hj

/-- **The fixed locus of a single-coordinate rotation.** The points of `ℂ^ι` fixed by every power
of the rotation of the coordinate `z_{j₀}` by an angle `θ₀ ∉ 2πℤ` are those with `z_{j₀} = 0`. -/
theorem forall_weightRotation_zsmul_single_apply_eq_self_iff
    (hθ₀ : ∀ k : ℤ, (k : ℝ) * (2 * π) ≠ θ₀) (j₀ : ι)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    (∀ n : ℤ, weightRotation (n • Pi.single j₀ θ₀) x = x) ↔ x.1 j₀ = 0 ∧ x.2 j₀ = 0 := by
  rw [forall_weightRotation_zsmul_apply_eq_self_iff_apply_eq_self, ←
    mem_eqLocus_weightRotation_single_iff hθ₀ j₀, LinearMap.mem_eqLocus,
    ContinuousLinearMap.coe_coe, LinearMap.id_apply]

/-- The fixed subspace of the rotation of the coordinate `z_{j₀}` of `ℂ^ι` by an angle
`θ₀ ∉ 2πℤ` has real dimension `2 (|ι| - 1)`. -/
theorem finrank_eqLocus_weightRotation_single (hθ₀ : ∀ k : ℤ, (k : ℝ) * (2 * π) ≠ θ₀) (j₀ : ι) :
    finrank ℝ (LinearMap.eqLocus (weightRotation (Pi.single j₀ θ₀)).toLinearMap
      LinearMap.id) = 2 * (Fintype.card ι - 1) := by
  rw [finrank_eq_two_mul_ncard_of_mem_iff {j₀}ᶜ fun x ↦ by
      rw [mem_eqLocus_weightRotation_single_iff hθ₀ j₀]; simp,
    Set.ncard_compl, Set.ncard_singleton, Nat.card_eq_fintype_card]

end TauCeti

/-! ### Rotating one coordinate by an irrational angle -/

namespace Irrational

open TauCeti

variable {ι : Type*} [Fintype ι]

variable [DecidableEq ι] {a : ℝ} (ha : Irrational a) (j₀ : ι)
include ha

/-- The rotation of one coordinate of `ℂ^ι` by an irrational multiple of `2π` generates an
infinite cyclic group. -/
theorem orderOf_weightRotation_single :
    orderOf (weightRotation (Pi.single j₀ (2 * π * a))) = 0 :=
  (orderOf_weightRotation_eq_zero_iff _).mpr
    ⟨j₀, by rwa [Pi.single_eq_same, mul_div_cancel_left₀ _ (by positivity)]⟩

/-- The fixed subspace of the rotation of the coordinate `z_{j₀}` of `ℂ^ι` by an irrational
multiple of `2π` is the coordinate subspace `z_{j₀} = 0`. -/
theorem mem_eqLocus_weightRotation_single_iff (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    x ∈ LinearMap.eqLocus (weightRotation (Pi.single j₀ (2 * π * a))).toLinearMap
      LinearMap.id ↔ x.1 j₀ = 0 ∧ x.2 j₀ = 0 :=
  TauCeti.mem_eqLocus_weightRotation_single_iff (ha.intCast_mul_ne_mul two_pi_pos.ne') j₀ x

/-- **The fixed locus of an irrational rotation.** The points of `ℂ^ι` fixed by every power of the
rotation of the coordinate `z_{j₀}` by an irrational multiple of `2π` are those with `z_{j₀} = 0`.
-/
theorem forall_weightRotation_zsmul_single_apply_eq_self_iff
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    (∀ n : ℤ, weightRotation (n • Pi.single j₀ (2 * π * a)) x = x) ↔
      x.1 j₀ = 0 ∧ x.2 j₀ = 0 :=
  TauCeti.forall_weightRotation_zsmul_single_apply_eq_self_iff
    (ha.intCast_mul_ne_mul two_pi_pos.ne') j₀ x

/-- The fixed subspace of the rotation of the coordinate `z_{j₀}` of `ℂ^ι` by an irrational
multiple of `2π` has real dimension `2 (|ι| - 1)`; for `ℂ²` this real dimension is `2`. -/
theorem finrank_eqLocus_weightRotation_single :
    finrank ℝ (LinearMap.eqLocus (weightRotation (Pi.single j₀ (2 * π * a))).toLinearMap
      LinearMap.id) = 2 * (Fintype.card ι - 1) :=
  TauCeti.finrank_eqLocus_weightRotation_single (ha.intCast_mul_ne_mul two_pi_pos.ne') j₀

end Irrational
