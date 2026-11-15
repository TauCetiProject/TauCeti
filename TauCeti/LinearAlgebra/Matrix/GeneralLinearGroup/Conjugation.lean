/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `GL`, its coercion to matrices, the scalar embedding, and the determinant occur in the
-- statements below.
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
-- The conjugation action `ConjAct (GL n R)` on matrices occurs in a statement below.
public import Mathlib.GroupTheory.GroupAction.ConjAct
-- Non-public: `Matrix.GeneralLinearGroup.center_eq_range_scalar`, that the centre of `GL n R`
-- is the scalars, is used only in a proof.
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-!
# Conjugation invariants in the general linear group

This file records elementary invariants of conjugation in a general linear group that are useful
across the concrete subgroup and conjugacy-class computations, and the fact that conjugation by an
element of `GL n R` determines that element up to a unit scalar. The latter is what makes the
conjugators of a family of inner automorphisms of `Mₙ(R)` multiply up to scalars, as in the
construction of the Galois `2`-cocycle of a split central simple algebra.

It also records that two square matrices lie in the same conjugation orbit of `GL n R` exactly when
the linear maps of `n → R` they define are conjugate by a linear automorphism, so that conjugacy of
matrices can be decided on the linear maps, for instance through Jordan-chain bases.

## Main results

* `Matrix.GeneralLinearGroup.det_sub_algebraMap_conj`: shifting a matrix by a scalar and taking its
  determinant is invariant under conjugation by `GL n R`.
* `Matrix.GeneralLinearGroup.forall_conj_eq_iff_exists_scalar_mul_eq`: two elements of `GL n R`
  induce the same conjugation of `GL n R` exactly when they differ by a unit scalar.
* `Matrix.GeneralLinearGroup.inv_mulVec_mulVec_of_eq_mul_mul_inv`: if `A = g * B * g⁻¹` then
  `g⁻¹ *ᵥ (A *ᵥ v) = B *ᵥ (g⁻¹ *ᵥ v)`.
* `Matrix.GeneralLinearGroup.scalar_injective`: for nonempty `n`, the scalar embedding
  `Rˣ → GL n R` is injective.
* `Matrix.mem_orbit_conjAct_iff_exists_linearEquiv_conj`: matrices are conjugate under `GL n R`
  exactly when their linear maps are conjugate by a linear automorphism of `n → R`.
-/

public section

namespace Matrix.GeneralLinearGroup

variable {n R : Type*} [Fintype n] [DecidableEq n]

/-- For nonempty `n`, the scalar embedding `Rˣ → GL n R` is injective. -/
theorem scalar_injective [Semiring R] [Nonempty n] :
    Function.Injective (scalar n : Rˣ →* GL n R) :=
  fun u v h ↦
    Units.ext (Matrix.scalar_inj.mp (by simpa only [coe_scalar] using congrArg Units.val h))

/-- Conjugating a matrix by `g` and applying it to a vector is the same as applying the original
matrix to the vector moved by `g⁻¹`: if `A = g * B * g⁻¹` then
`g⁻¹ *ᵥ (A *ᵥ v) = B *ᵥ (g⁻¹ *ᵥ v)`. -/
theorem inv_mulVec_mulVec_of_eq_mul_mul_inv [Semiring R] (g : GL n R)
    {A B : Matrix n n R} (h : A = (g : Matrix n n R) * B * (g⁻¹ : GL n R)) (v : n → R) :
    (g⁻¹ : GL n R) *ᵥ (A *ᵥ v) = B *ᵥ ((g⁻¹ : GL n R) *ᵥ v) := by
  rw [mulVec_mulVec, mulVec_mulVec, h, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Units.inv_mul, Matrix.one_mul]

variable [CommRing R]

/-- Shifting a matrix by a scalar and taking its determinant is invariant under conjugation by an
element of the general linear group. -/
theorem det_sub_algebraMap_conj (x : GL n R) (M : Matrix n n R) (a : R) :
    ((x⁻¹ : GL n R) * M * (x : Matrix n n R) - algebraMap R (Matrix n n R) a).det =
      (M - algebraMap R (Matrix n n R) a).det := by
  simpa [mul_sub, sub_mul, mul_assoc, ← Algebra.commutes] using
    det_units_conj' x (M - algebraMap R _ a)

/-- **An inner automorphism determines its conjugator up to a scalar.** Two elements `g` and `h`
of `GL n R` conjugate every element of `GL n R` in the same way exactly when `g` is `h` multiplied
by the scalar matrix of a unit `u`. -/
theorem forall_conj_eq_iff_exists_scalar_mul_eq {g h : GL n R} :
    (∀ x : GL n R, g * x * g⁻¹ = h * x * h⁻¹) ↔ ∃ u : Rˣ, scalar n u * h = g := by
  refine ⟨fun H ↦ ?_, ?_⟩
  · -- `h⁻¹ * g` commutes with every unit, so it is a scalar
    have hz : h⁻¹ * g ∈ Subgroup.center (GL n R) := Subgroup.mem_center_iff.mpr fun x ↦ by
      calc x * (h⁻¹ * g) = h⁻¹ * (h * x * h⁻¹) * g := by group
        _ = h⁻¹ * (g * x * g⁻¹) * g := by rw [H]
        _ = h⁻¹ * g * x := by group
    rw [center_eq_range_scalar] at hz
    obtain ⟨u, hu⟩ := hz
    exact ⟨u, by rw [scalar_commute, hu, mul_inv_cancel_left]⟩
  · rintro ⟨u, rfl⟩ x
    calc scalar n u * h * x * (scalar n u * h)⁻¹
        = scalar n u * (h * x * h⁻¹) * (scalar n u)⁻¹ := by group
      _ = h * x * h⁻¹ := by rw [scalar_commute, mul_inv_cancel_right]

end Matrix.GeneralLinearGroup

namespace Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommSemiring R]

/-- **Matrix conjugacy is conjugacy of linear maps.** The matrix `B` lies in the conjugation orbit
of `A` under `GL n R` exactly when a linear automorphism `e` of `n → R` conjugates `toLin' A` to
`toLin' B`. -/
theorem mem_orbit_conjAct_iff_exists_linearEquiv_conj {A B : Matrix n n R} :
    B ∈ MulAction.orbit (ConjAct (GL n R)) A ↔
      ∃ e : (n → R) ≃ₗ[R] n → R, e.conj (toLin' A) = toLin' B := by
  -- `GL n R` is the group of linear automorphisms of `n → R`, through `toLin'`.
  let ψ : GL n R ≃* ((n → R) ≃ₗ[R] n → R) :=
    (Units.mapEquiv toLinAlgEquiv'.toMulEquiv).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv R _)
  have key (g : GL n R) :
      (ψ g).conj (toLin' A) =
        toLin' ((g : Matrix n n R) * A * ((g⁻¹ : GL n R) : Matrix n n R)) := by
    refine LinearMap.ext fun v ↦ ?_
    -- Rewrite `(ψ g).symm` as `ψ g⁻¹`, and keep `simp` from turning it back.
    rw [LinearEquiv.conj_apply_apply, ← LinearEquiv.coe_inv, ← map_inv]
    simp [ψ, -map_inv, -LinearEquiv.coe_inv]
  simp only [MulAction.mem_orbit_iff, ConjAct.toConjAct.surjective.exists, ConjAct.units_smul_def,
    ConjAct.ofConjAct_toConjAct, ψ.surjective.exists, key, toLin'.injective.eq_iff]

end Matrix
