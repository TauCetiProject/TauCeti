/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.Topology.Instances.AddCircle.Torus
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Toral endomorphisms

An integer matrix `A : Matrix ι ι ℤ` acts on the unit torus `UnitAddTorus ι = (ℝ / ℤ)^ι` by the
continuous additive map `TauCeti.toralEndomorphism A = Matrix.smulVecHom A UnitAddCircle`, the map
induced by the linear map `A : ℝ^ι → ℝ^ι` (`TauCeti.toralEndomorphism_coe_pi`). It is functorial in
the matrix (`TauCeti.toralEndomorphism_one`, `TauCeti.toralEndomorphism_mul`).

When `det A ≠ 0` the map is surjective (`TauCeti.toralEndomorphism_surjective`, from
`Matrix.smulVecHom_addCircle_surjective`), since every `t : ℝ^ι` is `A (A⁻¹ t)` over `ℝ`. A
continuous surjective additive homomorphism of compact groups carries a Haar measure to the Haar
measure of the same total mass (Mathlib's `AddMonoidHom.measurePreserving`), so the toral
endomorphism preserves the volume (`TauCeti.measurePreserving_toralEndomorphism`). When
`det A = ±1` the inverse matrix is again an integer matrix, and `TauCeti.toralAutomorphism A hA` is
the toral endomorphism as a continuous additive automorphism of the torus, hence a measurable one,
preserving volume (`TauCeti.measurePreserving_toralAutomorphism`).

The matrix `!![2, 0; 0, 1]` gives a volume-preserving endomorphism of the two-torus that is not
injective (`TauCeti.not_injective_toralEndomorphism_two_zero_zero_one`).

## Main definitions

* `TauCeti.toralEndomorphism A`: the continuous additive endomorphism of `UnitAddTorus ι` induced
  by the integer matrix `A`.
* `TauCeti.toralAutomorphism A hA`: for `IsUnit A.det`, the toral endomorphism as a continuous
  additive automorphism, with inverse `toralEndomorphism A⁻¹`.

## Main results

* `TauCeti.toralEndomorphism_surjective`: for `det A ≠ 0`, the toral endomorphism is surjective.
* `TauCeti.measurePreserving_toralEndomorphism`: for `det A ≠ 0`, the toral endomorphism preserves
  the volume.
* `TauCeti.measurePreserving_toralAutomorphism`: the toral automorphism preserves the volume.
-/

public section

open MeasureTheory Matrix

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- The toral endomorphism of `UnitAddTorus ι = (ℝ / ℤ)^ι` induced by an integer matrix `A`:
`x ↦ (k ↦ ∑ i, A k i • x i)`. -/
noncomputable def toralEndomorphism (A : Matrix ι ι ℤ) :
    UnitAddTorus ι →ₜ+ UnitAddTorus ι :=
  A.smulVecHom UnitAddCircle

/-- The toral endomorphism of `A` is the map `Matrix.smulVecHom A UnitAddCircle`, so the API of
`Matrix.smulVecHom` (its kernel, for instance) applies to it. -/
theorem toralEndomorphism_def (A : Matrix ι ι ℤ) :
    toralEndomorphism A = A.smulVecHom UnitAddCircle :=
  (rfl)

@[simp]
theorem toralEndomorphism_apply (A : Matrix ι ι ℤ) (x : UnitAddTorus ι) (k : ι) :
    toralEndomorphism A x k = ∑ i, A k i • x i :=
  A.smulVecHom_apply _ x k

/-- The toral endomorphism of `A` is induced by the linear map `A : ℝ^ι → ℝ^ι`. -/
theorem toralEndomorphism_coe_pi (A : Matrix ι ι ℤ) (t : ι → ℝ) :
    toralEndomorphism A (fun i ↦ (t i : UnitAddCircle)) =
      fun k ↦ ((A.map ((↑) : ℤ → ℝ) *ᵥ t) k : UnitAddCircle) :=
  A.smulVecHom_coe_pi (1 : ℝ) t

/-- The toral endomorphism of a product of matrices is the composite of their toral
endomorphisms. -/
theorem toralEndomorphism_mul (A B : Matrix ι ι ℤ) :
    toralEndomorphism (A * B) = (toralEndomorphism A).comp (toralEndomorphism B) :=
  Matrix.smulVecHom_mul B _ A

variable [DecidableEq ι]

/-- The identity matrix induces the identity of the torus. -/
@[simp]
theorem toralEndomorphism_one : toralEndomorphism (1 : Matrix ι ι ℤ) = .id _ :=
  Matrix.smulVecHom_one _

/-- A toral endomorphism of nonzero determinant is surjective. -/
theorem toralEndomorphism_surjective {A : Matrix ι ι ℤ} (hA : A.det ≠ 0) :
    Function.Surjective (toralEndomorphism A) :=
  Matrix.smulVecHom_addCircle_surjective (1 : ℝ) hA

/-- **Toral endomorphisms preserve volume.** For an integer matrix of nonzero determinant, the
toral endomorphism preserves the volume (Haar probability) of the torus. -/
theorem measurePreserving_toralEndomorphism {A : Matrix ι ι ℤ} (hA : A.det ≠ 0) :
    MeasurePreserving (toralEndomorphism A) volume volume :=
  AddMonoidHom.measurePreserving (f := (toralEndomorphism A : UnitAddTorus ι →+ UnitAddTorus ι))
    (toralEndomorphism A).continuous (toralEndomorphism_surjective hA) rfl

/-- The toral endomorphism of an integer matrix of determinant `±1` (a unit of `ℤ`), as a
continuous additive automorphism of the torus with inverse the toral endomorphism of `A⁻¹`. Its
measurable automorphism is `(toralAutomorphism A hA).toHomeomorph.toMeasurableEquiv`. -/
noncomputable def toralAutomorphism (A : Matrix ι ι ℤ) (hA : IsUnit A.det) :
    UnitAddTorus ι ≃ₜ+ UnitAddTorus ι where
  toFun := toralEndomorphism A
  invFun := toralEndomorphism A⁻¹
  left_inv x := by
    have h := DFunLike.congr_fun (toralEndomorphism_mul A⁻¹ A) x
    rw [Matrix.nonsing_inv_mul A hA, toralEndomorphism_one] at h
    simpa using h.symm
  right_inv x := by
    have h := DFunLike.congr_fun (toralEndomorphism_mul A A⁻¹) x
    rw [Matrix.mul_nonsing_inv A hA, toralEndomorphism_one] at h
    simpa using h.symm
  map_add' := map_add _
  continuous_toFun := (toralEndomorphism A).continuous
  continuous_invFun := (toralEndomorphism A⁻¹).continuous

@[simp]
theorem coe_toralAutomorphism (A : Matrix ι ι ℤ) (hA : IsUnit A.det) :
    ⇑(toralAutomorphism A hA) = toralEndomorphism A :=
  (rfl)

@[simp]
theorem coe_toralAutomorphism_symm (A : Matrix ι ι ℤ) (hA : IsUnit A.det) :
    ⇑(toralAutomorphism A hA).symm = toralEndomorphism A⁻¹ :=
  (rfl)

/-- A toral automorphism preserves the volume of the torus. -/
theorem measurePreserving_toralAutomorphism (A : Matrix ι ι ℤ) (hA : IsUnit A.det) :
    MeasurePreserving (toralAutomorphism A hA) volume volume :=
  measurePreserving_toralEndomorphism hA.ne_zero

/-- **Check.** The matrix `!![2, 0; 0, 1]` induces a volume-preserving endomorphism of the
two-torus. -/
theorem measurePreserving_toralEndomorphism_two_zero_zero_one :
    MeasurePreserving (toralEndomorphism !![(2 : ℤ), 0; 0, 1]) volume volume :=
  measurePreserving_toralEndomorphism (by simp [Matrix.det_fin_two])

/-- **Check.** The volume-preserving toral endomorphism of `!![2, 0; 0, 1]` is not injective: it
sends `([1/2], 0)` and `0` to `0`. -/
theorem not_injective_toralEndomorphism_two_zero_zero_one :
    ¬ Function.Injective (toralEndomorphism !![(2 : ℤ), 0; 0, 1]) := by
  intro h
  have hx : toralEndomorphism !![(2 : ℤ), 0; 0, 1] ![((1 / 2 : ℝ) : UnitAddCircle), 0] =
      toralEndomorphism !![(2 : ℤ), 0; 0, 1] 0 := by
    ext k
    fin_cases k <;> norm_num [Fin.sum_univ_two, ← AddCircle.coe_zsmul]
  -- `[1/2] = 0` would give an integer `n` with `n = 1/2`, so `2 * n = 1`.
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).1 (congr_fun (h hx) 0)
  have h2 : 2 * n = 1 := by
    rw [zsmul_one] at hn
    exact_mod_cast show (2 * n : ℝ) = 1 by rw [hn]; norm_num
  omega

end TauCeti
