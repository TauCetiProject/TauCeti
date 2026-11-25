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
public import TauCeti.Topology.Instances.AddCircle.Torus
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Toral endomorphisms

An integer matrix `A : Matrix ι ι ℤ` acts on the unit torus `UnitAddTorus ι = (ℝ / ℤ)^ι` by the
continuous additive map `TauCeti.toralEndomorphism A = Matrix.smulVecHom A UnitAddCircle`, the map
induced by the linear map `A : ℝ^ι → ℝ^ι` (`TauCeti.toralEndomorphism_coe_pi`). It is functorial in
the matrix (`TauCeti.toralEndomorphism_one`, `TauCeti.toralEndomorphism_mul`).

When `det A ≠ 0` the map is surjective (`Matrix.smulVecHom_addCircle_surjective`, for a circle of
any real period), since every `t : ℝ^ι` is `A (A⁻¹ t)` over `ℝ`. A continuous surjective additive
homomorphism of compact groups carries a Haar measure to the Haar measure of the same total mass
(Mathlib's `AddMonoidHom.measurePreserving`), so the toral endomorphism preserves the volume
(`TauCeti.measurePreserving_toralEndomorphism`). When `det A = ±1` the inverse matrix is again an
integer matrix, and `TauCeti.toralAutomorphism A hA` is the toral endomorphism as a measurable
automorphism of the torus, preserving volume (`TauCeti.measurePreserving_toralAutomorphism`).

The matrix `!![2, 0; 0, 1]` gives a volume-preserving endomorphism of the two-torus that is not
injective (`TauCeti.not_injective_toralEndomorphism_two_zero_zero_one`).

## Main definitions

* `TauCeti.toralEndomorphism A`: the continuous additive endomorphism of `UnitAddTorus ι` induced
  by the integer matrix `A`.
* `TauCeti.toralAutomorphism A hA`: for `IsUnit A.det`, the toral endomorphism as a measurable
  automorphism, with inverse `toralEndomorphism A⁻¹`.

## Main results

* `Matrix.smulVecHom_addCircle_surjective`: an integer matrix of nonzero determinant induces a
  surjective map of the torus `ι → AddCircle p`.
* `TauCeti.measurePreserving_toralEndomorphism`: for `det A ≠ 0`, the toral endomorphism preserves
  the volume.
* `TauCeti.measurePreserving_toralAutomorphism`: the toral automorphism preserves the volume.
-/

public section

open MeasureTheory Matrix

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An integer matrix of nonzero determinant induces a surjective map of the torus
`ι → AddCircle p`: the point `[t]` is the image of `[A⁻¹ t]`, the inverse taken over `ℝ`. -/
theorem smulVecHom_addCircle_surjective {A : Matrix ι ι ℤ} (hA : A.det ≠ 0) (p : ℝ) :
    Function.Surjective (A.smulVecHom (AddCircle p)) := by
  intro y
  choose t ht using fun i ↦ QuotientAddGroup.mk_surjective (y i)
  set B : Matrix ι ι ℝ := A.map ((↑) : ℤ → ℝ)
  have hB : IsUnit B.det := by
    rw [isUnit_iff_ne_zero, show B.det = ((A.det : ℤ) : ℝ) from
      ((Int.castRingHom ℝ).map_det A).symm]
    exact_mod_cast hA
  refine ⟨fun i ↦ ((B⁻¹ *ᵥ t) i : AddCircle p), ?_⟩
  rw [smulVecHom_coe_pi, mulVec_mulVec, mul_nonsing_inv B hB, one_mulVec]
  exact funext ht

end Matrix

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- The toral endomorphism of `UnitAddTorus ι = (ℝ / ℤ)^ι` induced by an integer matrix `A`:
`x ↦ (k ↦ ∑ i, A k i • x i)`. -/
noncomputable def toralEndomorphism (A : Matrix ι ι ℤ) :
    UnitAddTorus ι →ₜ+ UnitAddTorus ι :=
  A.smulVecHom UnitAddCircle

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
  Matrix.smulVecHom_addCircle_surjective hA 1

/-- **Toral endomorphisms preserve volume.** For an integer matrix of nonzero determinant, the
toral endomorphism preserves the volume (Haar probability) of the torus. -/
theorem measurePreserving_toralEndomorphism {A : Matrix ι ι ℤ} (hA : A.det ≠ 0) :
    MeasurePreserving (toralEndomorphism A) volume volume :=
  AddMonoidHom.measurePreserving (f := (toralEndomorphism A : UnitAddTorus ι →+ UnitAddTorus ι))
    (toralEndomorphism A).continuous (toralEndomorphism_surjective hA) rfl

/-- The toral endomorphism of an integer matrix of determinant `±1` (a unit of `ℤ`), as a
measurable automorphism of the torus with inverse the toral endomorphism of `A⁻¹`. -/
noncomputable def toralAutomorphism (A : Matrix ι ι ℤ) (hA : IsUnit A.det) :
    UnitAddTorus ι ≃ᵐ UnitAddTorus ι where
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
  measurable_toFun := (toralEndomorphism A).continuous.measurable
  measurable_invFun := (toralEndomorphism A⁻¹).continuous.measurable

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
    fin_cases k
    · simp only [toralEndomorphism_apply, Fin.sum_univ_two, Pi.zero_apply, smul_zero, add_zero,
        Fin.zero_eta, Fin.isValue, of_apply, cons_val', cons_val_zero, empty_val',
        cons_val_fin_one, cons_val_one]
      rw [← AddCircle.coe_zsmul, zsmul_eq_mul]
      norm_num
    · simp [toralEndomorphism_apply, Fin.sum_univ_two]
  have := congr_fun (h hx) 0
  simp only [Fin.isValue, cons_val_zero, Pi.zero_apply, AddCircle.coe_eq_zero_iff, zsmul_eq_mul,
    mul_one] at this
  obtain ⟨n, hn⟩ := this
  rcases le_or_gt n 0 with h0 | h0
  · have : (n : ℝ) ≤ 0 := by exact_mod_cast h0
    linarith
  · have : (1 : ℝ) ≤ n := by exact_mod_cast h0
    linarith

end TauCeti
