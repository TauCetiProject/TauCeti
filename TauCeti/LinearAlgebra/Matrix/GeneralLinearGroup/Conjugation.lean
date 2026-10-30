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
  determinant is invariant under conjugation.
* `Matrix.GeneralLinearGroup.exists_scalar_mul_eq_of_forall_conj_eq`: two elements of `GL n R`
  inducing the same conjugation of `GL n R` differ by a unit scalar.
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

variable [CommRing R]

/-- Shifting a matrix by a scalar and taking its determinant is invariant under conjugation in
the general linear group. -/
theorem det_sub_algebraMap_conj (g x : GL n R) (a : R) :
    (((x⁻¹ * g * x : GL n R) : Matrix n n R) - algebraMap R (Matrix n n R) a).det =
      ((g : Matrix n n R) - algebraMap R (Matrix n n R) a).det := by
  have hxx : ((x⁻¹ : GL n R) : Matrix n n R) * (x : Matrix n n R) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hcancel : ((x⁻¹ : GL n R) : Matrix n n R) *
      algebraMap R (Matrix n n R) a * (x : Matrix n n R) =
      algebraMap R (Matrix n n R) a := by
    rw [mul_assoc, Algebra.commutes a (x : Matrix n n R), ← mul_assoc, hxx, one_mul]
  have hsplit : ((x⁻¹ * g * x : GL n R) : Matrix n n R) -
      algebraMap R (Matrix n n R) a =
      ((x⁻¹ : GL n R) : Matrix n n R) *
        ((g : Matrix n n R) - algebraMap R (Matrix n n R) a) * (x : Matrix n n R) := by
    rw [mul_sub, sub_mul, hcancel, Units.val_mul, Units.val_mul]
  rw [hsplit, Matrix.coe_units_inv, Matrix.det_conj' x.isUnit]

/-- **An inner automorphism determines its conjugator up to a scalar.** If `g` and `h` in
`GL n R` conjugate every element of `GL n R` in the same way, then `g` is `h` multiplied by the
scalar matrix of a unit `u`. -/
theorem exists_scalar_mul_eq_of_forall_conj_eq {g h : GL n R}
    (H : ∀ x : GL n R, g * x * g⁻¹ = h * x * h⁻¹) :
    ∃ u : Rˣ, scalar n u * h = g := by
  -- `h⁻¹ * g` commutes with every unit, so it is a scalar
  have hz : h⁻¹ * g ∈ Subgroup.center (GL n R) := Subgroup.mem_center_iff.mpr fun x ↦ by
    calc x * (h⁻¹ * g) = h⁻¹ * (h * x * h⁻¹) * g := by group
      _ = h⁻¹ * (g * x * g⁻¹) * g := by rw [H]
      _ = h⁻¹ * g * x := by group
  rw [center_eq_range_scalar] at hz
  obtain ⟨u, hu⟩ := hz
  exact ⟨u, by rw [scalar_commute, hu, mul_inv_cancel_left]⟩

end Matrix.GeneralLinearGroup

namespace Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommSemiring R]

/-- **Matrix conjugacy is conjugacy of linear maps.** The matrix `B` lies in the conjugation orbit
of `A` under `GL n R` exactly when a linear automorphism `e` of `n → R` conjugates `toLin' A` to
`toLin' B`. -/
theorem mem_orbit_conjAct_iff_exists_linearEquiv_conj {A B : Matrix n n R} :
    B ∈ MulAction.orbit (ConjAct (GL n R)) A ↔
      ∃ e : (n → R) ≃ₗ[R] n → R, e.conj (toLin' A) = toLin' B := by
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨toLin'OfInv (ConjAct.ofConjAct g).inv_mul (ConjAct.ofConjAct g).mul_inv, ?_⟩
    -- `MulAction.orbit` is stated through the action map; reduce it to `g • A`.
    dsimp only
    rw [ConjAct.units_smul_def, toLin'_mul, toLin'_mul, LinearEquiv.conj_apply]
    refine LinearMap.ext fun v => ?_
    have hv := funext (toLin'OfInv_symm_apply (ConjAct.ofConjAct g).inv_mul
      (ConjAct.ofConjAct g).mul_inv v)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hv]
    exact funext (toLin'OfInv_apply _ _ _)
  · rintro ⟨e, he⟩
    have h₁ : LinearMap.toMatrix' (e : (n → R) →ₗ[R] n → R) * LinearMap.toMatrix' e.symm = 1 := by
      rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_symm, LinearMap.toMatrix'_id]
    have h₂ : LinearMap.toMatrix' (e.symm : (n → R) →ₗ[R] n → R) * LinearMap.toMatrix' e = 1 := by
      rw [← LinearMap.toMatrix'_comp, LinearEquiv.symm_comp, LinearMap.toMatrix'_id]
    refine ⟨ConjAct.toConjAct ⟨_, _, h₁, h₂⟩, Matrix.toLin'.injective ?_⟩
    -- As above, reduce the action map to `g • A`.
    dsimp only
    rw [← he, ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct, toLin'_mul, toLin'_mul,
      LinearEquiv.conj_apply]
    simp

end Matrix
