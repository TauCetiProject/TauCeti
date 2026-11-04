/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.OrthSum
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# Isometries, orthogonal sums and rescaling of theta series

An isometry preserves the theta series of a lattice and its translates. Multiplying a lattice
and a translate by a nonzero real scalar multiplies the upper-half-plane parameter by its square.
These statements use only reindexing, without discreteness or finite-dimensionality assumptions.

In the `L²` product `WithLp 2 (E × F)` we have `‖(x, y)‖² = ‖x‖² + ‖y‖²`, so each term of the
theta series of an orthogonal direct sum `L ⊕ M` is the product of a term for `L` and a term for
`M`, and the absolutely convergent series multiply: `θ_{(γ, δ) + (L ⊕ M)} = θ_{γ+L} · θ_{δ+M}`
and `Θ_{L ⊕ M} = Θ_L · Θ_M`. For instance `Θ_{E₈ ⊕ E₈} = Θ_{E₈}²`.

The reindexing uses Mathlib's `ZLattice.comap_equiv` and `Submodule.equivMapOfInjective`.
For the classical theta-series conventions see Serre, *A Course in Arithmetic*, Ch. VII §6,
and Ebeling, *Lattices and Codes*, Ch. 2.
-/

public section

open Complex WithLp
open scoped Real UpperHalfPlane Pointwise

namespace ZLattice

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace ℝ E] [NormedSpace ℝ F]

/-- Pulling a lattice and its translate back along a linear isometry preserves the theta series. -/
@[simp]
theorem thetaCoset_comap (L : Submodule ℤ E) (e : F ≃ₗᵢ[ℝ] E) (γ : F) (τ : ℍ) :
    thetaCoset (ZLattice.comap ℝ L e.toLinearEquiv.toLinearMap) γ τ = thetaCoset L (e γ) τ := by
  rw [thetaCoset_apply, thetaCoset_apply,
    ← (comap_equiv ℝ L e.toLinearEquiv).toEquiv.tsum_eq]
  refine tsum_congr fun v ↦ ?_
  have he : ((comap_equiv ℝ L e.toLinearEquiv) v : F) = e.symm (v : E) :=
    comap_equiv_apply ℝ L e.toLinearEquiv v
  simp only [LinearEquiv.coe_toEquiv, he]
  rw [← e.norm_map (γ + e.symm (v : E)), map_add, e.apply_symm_apply]

/-- Pulling a lattice back along a linear isometry preserves its theta series. -/
@[simp]
theorem thetaSeries_comap (L : Submodule ℤ E) (e : F ≃ₗᵢ[ℝ] E) (τ : ℍ) :
    thetaSeries (ZLattice.comap ℝ L e.toLinearEquiv.toLinearMap) τ = thetaSeries L τ := by
  simpa only [map_zero, thetaCoset_zero] using thetaCoset_comap L e 0 τ

/-- Rescaling a lattice and a translate multiplies the parameter by the square of the scalar.
The positive-real action on `ℍ` makes the domain of the rescaled parameter explicit. -/
theorem thetaCoset_smul (L : Submodule ℤ E) {c : ℝ} (hc : c ≠ 0) (γ : E) (τ : ℍ) :
    thetaCoset (c • L) (c • γ) τ =
      thetaCoset L γ ((⟨c ^ 2, sq_pos_of_ne_zero hc⟩ : {r : ℝ // 0 < r}) • τ) := by
  let e := Submodule.equivMapOfInjective (DistribSMul.toLinearMap ℤ E c)
    (smul_right_injective E hc) L
  rw [Submodule.pointwise_smul_def, thetaCoset_apply, thetaCoset_apply]
  -- Pointwise scalar multiplication of submodules is the image used by `e`.
  rw [← e.toEquiv.tsum_eq]
  refine tsum_congr fun v ↦ ?_
  have he : (e v : E) = c • (v : E) :=
    Submodule.coe_equivMapOfInjective_apply _ _ _ v
  simp only [LinearEquiv.coe_toEquiv, he]
  simp only [← smul_add, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, UpperHalfPlane.coe_pos_real_smul, Complex.real_smul]
  congr 1
  push_cast
  ring

/-- Rescaling a lattice by a nonzero real scalar multiplies the theta parameter by its square. -/
theorem thetaSeries_smul (L : Submodule ℤ E) {c : ℝ} (hc : c ≠ 0) (τ : ℍ) :
    thetaSeries (c • L) τ =
      thetaSeries L ((⟨c ^ 2, sq_pos_of_ne_zero hc⟩ : {r : ℝ // 0 < r}) • τ) := by
  simpa using thetaCoset_smul L hc 0 τ

/-! ### Orthogonal direct sums -/

section OrthSum

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] (L : Submodule ℤ E) [DiscreteTopology L]
  (M : Submodule ℤ F) [DiscreteTopology M]

/-- The theta series of a translate of an orthogonal direct sum is the product of the theta
series of the translates of the summands: `θ_{(γ, δ) + (L ⊕ M)} = θ_{γ+L} · θ_{δ+M}`. -/
@[simp]
theorem thetaCoset_orthSum (x : WithLp 2 (E × F)) :
    thetaCoset (orthSum L M) x = thetaCoset L x.fst * thetaCoset M x.snd := by
  ext τ
  rw [Pi.mul_apply, thetaCoset_apply, thetaCoset_apply, thetaCoset_apply,
    tsum_mul_tsum_of_summable_norm (summable_thetaCoset L _ τ).norm
      (summable_thetaCoset M _ τ).norm, ← (orthSumEquivProd L M).symm.toEquiv.tsum_eq]
  refine tsum_congr fun p ↦ ?_
  rw [← exp_add, prod_norm_sq_eq_of_L2]
  simp only [LinearEquiv.coe_toEquiv, coe_orthSumEquivProd_symm_apply, add_fst, add_snd,
    toLp_fst, toLp_snd]
  push_cast
  congr 1
  ring

/-- The theta series of an orthogonal direct sum is the product of the theta series of the
summands: `Θ_{L ⊕ M} = Θ_L · Θ_M`. -/
@[simp]
theorem thetaSeries_orthSum : thetaSeries (orthSum L M) = thetaSeries L * thetaSeries M := by
  simpa using thetaCoset_orthSum L M 0

end OrthSum

end ZLattice
