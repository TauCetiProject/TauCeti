/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup.Bessel.HomogeneousCoordinates

/-!
# Homogeneous balls in the group `U⁰` of the split form

Let `𝕜` be `ℝ` or `ℂ` (any `RCLike` field) and `U⁰ = TauCeti.besselU0 ϱ (middleGram N)` the group of
isometries of the split form of `diag(1_κ, -N)` that are block unitriangular for the levels and
fix the frame. An element `u ∈ U⁰` has the coordinates `ω = Matrix.besselOmega u` and
`μ = Matrix.besselMu u`, defined by `u e*_b = e*_b - Σ_i ω_{ib} x_i - Σ_a μ_{ab} e_a`. With the
`ℓ²` operator norm on matrices, the **homogeneous ball** of radius `ρ` is

`B(ρ) = {u ∈ U⁰ : ‖ω‖ ≤ ρ, ‖μ‖ ≤ ρ²}`.

The composition law `ω(uv) = ω(u) + ω(v)`, `μ(uv) = μ(u) + μ(v) + ω(u)ᴴ ω(v)` gives
`B(ρ) B(ρ') ⊆ B(ρ + ρ')`, since `ρ² + ρ'² + ρρ' ≤ (ρ + ρ')²`, and `ω(u⁻¹) = -ω(u)`,
`μ(u⁻¹) = μ(u)ᴴ` give `B(ρ)⁻¹ = B(ρ)`.

## Main definitions

* `TauCeti.homogeneousBall ϱ κ N ρ`: the homogeneous ball `B(ρ)`.

## Main results

* `TauCeti.one_mem_homogeneousBall`, `TauCeti.homogeneousBall_mono`: `1 ∈ B(ρ)` for `ρ ≥ 0`, and
  `B(ρ) ⊆ B(ρ')` for `ρ ≤ ρ'`.
* `TauCeti.homogeneousBall_mul_subset`: `B(ρ) B(ρ') ⊆ B(ρ + ρ')`.
* `TauCeti.inv_homogeneousBall`: `B(ρ)⁻¹ = B(ρ)`.

## References

* the folder `grh` of https://github.com/lsernau/grh-lean at commit
  72fead102f663d5c7a407964a13dc0cf9d977207, declaration `New.RealPlace.besselHaar₀_homogeneousBall`.
* H. Xue, *Bessel models for real unitary groups: the tempered case*, Duke Math. J. 172 (2023).
-/

public section

open Matrix
open scoped Matrix.Norms.L2Operator Pointwise

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜] (ϱ : ℕ) (κ : Type*) [Fintype κ] [DecidableEq κ] (N : 𝕜)

/-- The **homogeneous ball** `B(ρ)`: the elements `u` of the group `U⁰` of the split form of
`diag(1_κ, -N)` whose coordinates satisfy `‖ω(u)‖ ≤ ρ` and `‖μ(u)‖ ≤ ρ ^ 2`, for the `ℓ²`
operator norm. -/
def homogeneousBall (ρ : ℝ) : Set (unitaryGroupOf (splitGram ϱ (middleGram (κ := κ) N))) :=
  {u | u ∈ besselU0 ϱ (middleGram N) ∧
    ‖besselOmega ((u : GL (BesselIndex ϱ κ) 𝕜) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) 𝕜)‖
      ≤ ρ ∧
    ‖besselMu ((u : GL (BesselIndex ϱ κ) 𝕜) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) 𝕜)‖
      ≤ ρ ^ 2}

variable {ϱ κ N}

@[simp] theorem mem_homogeneousBall {ρ : ℝ}
    {u : unitaryGroupOf (splitGram ϱ (middleGram (κ := κ) N))} :
    u ∈ homogeneousBall ϱ κ N ρ ↔ u ∈ besselU0 ϱ (middleGram N) ∧
      ‖besselOmega ((u : GL (BesselIndex ϱ κ) 𝕜) :
        Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) 𝕜)‖ ≤ ρ ∧
      ‖besselMu ((u : GL (BesselIndex ϱ κ) 𝕜) :
        Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) 𝕜)‖ ≤ ρ ^ 2 :=
  Iff.rfl

/-- The identity lies in every homogeneous ball of nonnegative radius. -/
theorem one_mem_homogeneousBall {ρ : ℝ} (hρ : 0 ≤ ρ) : 1 ∈ homogeneousBall ϱ κ N ρ :=
  ⟨one_mem _, by simpa using hρ, by simpa using sq_nonneg ρ⟩

/-- The homogeneous balls increase with the radius. -/
theorem homogeneousBall_mono : Monotone (homogeneousBall (𝕜 := 𝕜) ϱ κ N) := by
  intro ρ ρ' h u ⟨hu, hω, hμ⟩
  have hρ : 0 ≤ ρ := (norm_nonneg _).trans hω
  exact ⟨hu, hω.trans h, hμ.trans (pow_le_pow_left₀ hρ h 2)⟩

/-- **Homogeneous balls multiply**: `B(ρ) B(ρ') ⊆ B(ρ + ρ')`. -/
theorem homogeneousBall_mul_subset (ρ ρ' : ℝ) :
    homogeneousBall ϱ κ N ρ * homogeneousBall ϱ κ N ρ' ⊆ homogeneousBall ϱ κ N (ρ + ρ') := by
  rintro _ ⟨u, ⟨hu, hω, hμ⟩, v, ⟨hv, hω', hμ'⟩, rfl⟩
  have hv' := ((mem_besselU0 ϱ _).mp hv).2
  have hρ : 0 ≤ ρ := (norm_nonneg _).trans hω
  have hρ' : 0 ≤ ρ' := (norm_nonneg _).trans hω'
  refine ⟨mul_mem hu hv, ?_, ?_⟩
  · rw [besselOmega_mul hu hv']
    exact (norm_add_le _ _).trans (add_le_add hω hω')
  · rw [besselMu_mul hu hv']
    have hωω := (l2_opNorm_mul _ _).trans
      (mul_le_mul ((l2_opNorm_conjTranspose _).trans_le hω) hω' (norm_nonneg _) hρ)
    calc _ ≤ _ := norm_add₃_le
      _ ≤ ρ ^ 2 + ρ' ^ 2 + ρ * ρ' := add_le_add (add_le_add hμ hμ') hωω
      _ ≤ (ρ + ρ') ^ 2 := by linarith [mul_nonneg hρ hρ']

/-- The homogeneous balls are stable under inversion: `B(ρ)⁻¹ = B(ρ)`. -/
theorem inv_homogeneousBall (ρ : ℝ) :
    (homogeneousBall ϱ κ N ρ)⁻¹ = homogeneousBall ϱ κ N ρ := by
  have key (u) (hu : u ∈ homogeneousBall ϱ κ N ρ) : u⁻¹ ∈ homogeneousBall ϱ κ N ρ := by
    obtain ⟨hu, hω, hμ⟩ := hu
    refine ⟨inv_mem hu, ?_, ?_⟩
    · rwa [besselOmega_inv hu, norm_neg]
    · rwa [besselMu_inv, l2_opNorm_conjTranspose]
  ext u
  exact ⟨fun h ↦ inv_inv u ▸ key _ h, key u⟩

end TauCeti
