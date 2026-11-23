/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Complexification
public import TauCeti.LinearAlgebra.ExteriorPower.BaseChange
public import TauCeti.LinearAlgebra.ExteriorPower.SesquilinearForm

/-!
# Complexification of exterior-power sesquilinear Gram forms

For any real bilinear form `B : LinearMap.BilinForm ℝ V`, the `n`-th exterior power of the
complexification `ℂ ⊗[ℝ] V` carries two canonical sesquilinear Gram forms:

* `B.sesqComplexification.sesqExteriorPower n` on `⋀[ℂ]^n (ℂ ⊗[ℝ] V)`, induced by the
  sesquilinear complexification `B.sesqComplexification`;
* `LinearMap.BilinForm.sesqComplexification (B.sesqExteriorPower n)` on `ℂ ⊗[ℝ] ⋀[ℝ]^n V`,
  the sesquilinear complexification of the real `n`-th exterior Gram form.

This file transports these sesquilinear Gram forms between the two models across
`TauCeti.exteriorPower.equivBaseChange ℂ n`, without any finiteness, flatness, or basis assumption.
When `B` is symmetric, both transported forms are Hermitian.

## Main results

* `LinearMap.BilinForm.sesqExteriorPower_sesqComplexification_equivBaseChange_symm` and
  `LinearMap.BilinForm.sesqComplexification_sesqExteriorPower_equivBaseChange`: compatibility of
  `sesqExteriorPower` with `sesqComplexification` across
  `TauCeti.exteriorPower.equivBaseChange ℂ n`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §5.
* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 3rd ed., World Scientific (2020),
  §2.2.4.
-/

public section

open scoped TensorProduct
open LinearMap (BilinForm)
open Matrix

namespace LinearMap.BilinForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **Complexification commutes with exterior Gram forms on exterior powers** (inverse comparison
form): pulling `B.sesqComplexification.sesqExteriorPower n` back along
`(TauCeti.exteriorPower.equivBaseChange ℂ n).symm` gives the sesquilinear complexification of
`B.sesqExteriorPower n`. -/
@[simp]
theorem sesqExteriorPower_sesqComplexification_equivBaseChange_symm (B : BilinForm ℝ V) (n : ℕ)
    (x y : ℂ ⊗[ℝ] ⋀[ℝ]^n V) :
    B.sesqComplexification.sesqExteriorPower n
        ((TauCeti.exteriorPower.equivBaseChange ℂ n).symm x)
        ((TauCeti.exteriorPower.equivBaseChange ℂ n).symm y) =
      sesqComplexification (B.sesqExteriorPower n) x y := by
  let e := (TauCeti.exteriorPower.equivBaseChange (R := ℝ) ℂ (M := V) n).symm.toLinearMap
  let K := TauCeti.tmulConj (⋀[ℝ]^n V)
  have h : (((B.sesqComplexification.sesqExteriorPower n).comp e).compl₂ e ∘ₛₗ K :
        ℂ ⊗[ℝ] ⋀[ℝ]^n V →ₗ[ℂ] ℂ ⊗[ℝ] ⋀[ℝ]^n V →ₗ[ℂ] ℂ) =
      (sesqComplexification (B.sesqExteriorPower n) ∘ₛₗ K) := by
    apply TensorProduct.AlgebraTensorModule.curry_injective
    apply LinearMap.ext_ring
    refine LinearMap.ext_on_range (exteriorPower.ιMulti_span ℝ n V) fun u ↦ ?_
    apply TensorProduct.AlgebraTensorModule.curry_injective
    apply LinearMap.ext_ring
    refine LinearMap.ext_on_range (exteriorPower.ιMulti_span ℝ n V) fun v ↦ ?_
    simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
      LinearMap.restrictScalars_apply, LinearMap.comp_apply, LinearMap.compl₂_apply, K, e,
      TauCeti.tmulConj_tmul, map_one, LinearEquiv.coe_coe,
      TauCeti.exteriorPower.equivBaseChange_symm_tmul_ιMulti, one_smul,
      LinearMap.sesqExteriorPower_ιMulti_ιMulti, sesqComplexification_tmul_tmul, one_mul]
    have hmat : (Matrix.of fun i j ↦ ((B (u i) (v j) : ℝ) : ℂ)) =
        (algebraMap ℝ ℂ).mapMatrix (Matrix.of fun i j ↦ B (u i) (v j)) := by
      ext i j
      simp [Complex.coe_algebraMap]
    rw [hmat, ← RingHom.map_det, Complex.coe_algebraMap]
  simpa [K, e, TauCeti.tmulConj_tmulConj] using LinearMap.congr_fun₂ h (K x) y

/-- **Complexification commutes with exterior Gram forms on exterior powers** (forward cancellation
form): evaluating `sesqComplexification (B.sesqExteriorPower n)` on
`TauCeti.exteriorPower.equivBaseChange ℂ n` recovers
`B.sesqComplexification.sesqExteriorPower n`. -/
@[simp]
theorem sesqComplexification_sesqExteriorPower_equivBaseChange (B : BilinForm ℝ V) (n : ℕ)
    (x y : ⋀[ℂ]^n (ℂ ⊗[ℝ] V)) :
    sesqComplexification (B.sesqExteriorPower n)
        (TauCeti.exteriorPower.equivBaseChange ℂ n x)
        (TauCeti.exteriorPower.equivBaseChange ℂ n y) =
      B.sesqComplexification.sesqExteriorPower n x y := by
  rw [← sesqExteriorPower_sesqComplexification_equivBaseChange_symm,
    LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

end LinearMap.BilinForm
