/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.Basic
public import TauCeti.Geometry.Hodge.BilinearForm
public import TauCeti.Geometry.Hodge.Conjugation

/-!
# Realification of an integral module

The realification of an integral module `V` is the scalar extension `ℝ ⊗[ℤ] V`.  If an
abstract complexification `Vℂ` of the same module is given through `IsBaseChange`, associativity
of scalar extension identifies `ℂ ⊗[ℝ] (ℝ ⊗[ℤ] V)` with `Vℂ`.  This equivalence
intertwines ordinary conjugation on the left with the lattice-induced conjugation on the right.

The comparison is the base-change bridge needed to transfer real linear data on an integral module,
such as an almost complex structure or the real scalar extension of an integral bilinear form, to
its chosen abstract complexification.  Under it the real points of the lattice-induced conjugation
are exactly the image of the realification, `1 ⊗ₜ x`, and a complexified integral form takes on
them the values of its real scalar extension.

## Main declarations

* `TauCeti.Hodge.Realification`: the real scalar extension of an integral module.
* `TauCeti.Hodge.realificationComplexEquiv`: the canonical comparison between its complexification
  and an abstract complexification of the original integral module.
* `TauCeti.Hodge.realificationComplexEquiv_conj`: compatibility of that comparison with
  conjugation.
* `TauCeti.Hodge.exists_eq_realificationComplexEquiv_one_tmul`: every real point of the abstract
  complexification comes from the realification.
* `TauCeti.Hodge.integralFormBaseChange_realificationComplexEquiv_one_tmul`: on such points a
  complexified integral form is the real scalar extension of that form.
-/

public section

namespace TauCeti.Hodge

open scoped TensorProduct

universe u v

variable {V : Type u} {Vℂ : Type v}
variable [AddCommGroup V] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℂ : V →ₗ[ℤ] Vℂ}

/-- The realification `ℝ ⊗[ℤ] V` of an integral module. -/
abbrev Realification (V : Type u) [AddCommGroup V] :=
  ℝ ⊗[ℤ] V

/-- The canonical map from an integral module to its realification. -/
def realificationMap : V →ₗ[ℤ] Realification V :=
  (TensorProduct.mk ℤ ℝ V) 1

/-- The canonical map to the realification sends an integral vector to the corresponding pure
tensor. -/
@[simp]
theorem realificationMap_apply (x : V) : realificationMap x = 1 ⊗ₜ[ℤ] x :=
  TensorProduct.mk_apply 1 x

/-- The canonical map to the realification is injective when the integral module is flat, in
particular when it is free. -/
theorem realificationMap_injective [Module.Flat ℤ V] :
    Function.Injective (realificationMap : V →ₗ[ℤ] Realification V) := by
  intro x y hxy
  exact Module.Flat.tensorProduct_mk_injective ℤ V ℝ (by simpa using hxy)

/-- The canonical comparison from the complexification of the realification to an abstract
complexification of the original integral module. -/
noncomputable def realificationComplexEquiv (hℂ : IsBaseChange ℂ ιℂ) :
    ℂ ⊗[ℝ] Realification V ≃ₗ[ℂ] Vℂ :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℝ ℂ ℂ V).trans hℂ.equiv

/-- The realification comparison sends a nested pure tensor to scalar multiplication of the
corresponding integral vector. -/
@[simp]
theorem realificationComplexEquiv_tmul_tmul (hℂ : IsBaseChange ℂ ιℂ)
    (z : ℂ) (r : ℝ) (x : V) :
    realificationComplexEquiv hℂ (z ⊗ₜ[ℝ] (r ⊗ₜ[ℤ] x)) = (z * r) • ιℂ x := by
  simp [realificationComplexEquiv, Algebra.smul_def, mul_comm]

/-- Passing an integral vector through realification and then complexification gives its image in
the chosen abstract complexification. -/
theorem realificationComplexEquiv_one_tmul_realificationMap
    (hℂ : IsBaseChange ℂ ιℂ) (x : V) :
    realificationComplexEquiv hℂ (1 ⊗ₜ[ℝ] realificationMap x) = ιℂ x := by
  rw [realificationMap_apply, realificationComplexEquiv_tmul_tmul]
  norm_num

/-- The inverse comparison sends an integral vector of the abstract complexification to the
corresponding nested pure tensor. -/
@[simp]
theorem realificationComplexEquiv_symm_ι (hℂ : IsBaseChange ℂ ιℂ) (x : V) :
    (realificationComplexEquiv hℂ).symm (ιℂ x) = 1 ⊗ₜ[ℝ] ((1 : ℝ) ⊗ₜ[ℤ] x) := by
  rw [LinearEquiv.symm_apply_eq, realificationComplexEquiv_tmul_tmul]
  norm_num

/-- The comparison between the iterated and abstract complexifications intertwines their
conjugations. -/
@[simp]
theorem realificationComplexEquiv_conj (hℂ : IsBaseChange ℂ ιℂ)
    (x : ℂ ⊗[ℝ] Realification V) :
    realificationComplexEquiv hℂ (tmulConj (Realification V) x) =
      latticeConj hℂ (realificationComplexEquiv hℂ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul z x =>
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
      | tmul r v =>
          rw [tmulConj_tmul, realificationComplexEquiv_tmul_tmul,
            realificationComplexEquiv_tmul_tmul, map_smulₛₗ]
          simp [map_mul]

/-- The inverse realification comparison intertwines lattice-induced conjugation with ordinary
conjugation. -/
@[simp]
theorem realificationComplexEquiv_symm_conj (hℂ : IsBaseChange ℂ ιℂ) (x : Vℂ) :
    (realificationComplexEquiv hℂ).symm (latticeConj hℂ x) =
      tmulConj (Realification V) ((realificationComplexEquiv hℂ).symm x) := by
  apply (realificationComplexEquiv hℂ).injective
  rw [realificationComplexEquiv_conj, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

/-! ### The real points of the abstract complexification -/

/-- Lattice-induced conjugation fixes the image of a real vector under the realification
comparison. -/
@[simp]
theorem latticeConj_realificationComplexEquiv_one_tmul (hℂ : IsBaseChange ℂ ιℂ)
    (x : Realification V) :
    latticeConj hℂ (realificationComplexEquiv hℂ (1 ⊗ₜ[ℝ] x)) =
      realificationComplexEquiv hℂ (1 ⊗ₜ[ℝ] x) := by
  rw [← realificationComplexEquiv_conj, tmulConj_tmul, map_one]

/-- **The real points of the abstract complexification are the realification.** Every vector
fixed by the lattice-induced conjugation is the image of a real vector under the realification
comparison. -/
theorem exists_eq_realificationComplexEquiv_one_tmul (hℂ : IsBaseChange ℂ ιℂ) {y : Vℂ}
    (hy : y ∈ realPoints (latticeConj hℂ)) :
    ∃ x : Realification V, y = realificationComplexEquiv hℂ (1 ⊗ₜ[ℝ] x) := by
  have hfix : tmulConj (Realification V) ((realificationComplexEquiv hℂ).symm y) =
      (realificationComplexEquiv hℂ).symm y := by
    rw [← realificationComplexEquiv_symm_conj, mem_realPoints.mp hy]
  obtain ⟨x, hx⟩ := (tmulConj_eq_self_iff _ _).mp hfix
  exact ⟨x, by rw [← hx, LinearEquiv.apply_symm_apply]⟩

/-- **On real points a complexified integral form is the real scalar extension of the form.**
The complexification of an integral bilinear form, evaluated on the images of two real vectors
under the realification comparison, is the real scalar extension of the form evaluated on those
vectors. -/
@[simp]
theorem integralFormBaseChange_realificationComplexEquiv_one_tmul (hℂ : IsBaseChange ℂ ιℂ)
    (Q : LinearMap.BilinForm ℤ V) (x y : Realification V) :
    integralFormBaseChange hℂ Q (realificationComplexEquiv hℂ (1 ⊗ₜ[ℝ] x))
      (realificationComplexEquiv hℂ (1 ⊗ₜ[ℝ] y)) = (Q.baseChange ℝ x y : ℂ) := by
  have hform : ((Q.baseChange ℝ).baseChange ℂ).compl₁₂
      (realificationComplexEquiv hℂ).symm.toLinearMap
      (realificationComplexEquiv hℂ).symm.toLinearMap = integralFormBaseChange hℂ Q :=
    integralFormBaseChange_unique hℂ Q _ fun v w ↦ by simp [Algebra.smul_def]
  rw [← hform]
  simp [Algebra.smul_def]

end TauCeti.Hodge
