/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import TauCeti.Geometry.Hodge.Conjugation

/-!
# Realification of an integral lattice

The realification of an integral module `V` is the scalar extension `ℝ ⊗[ℤ] V`.  If an
abstract complexification `Vℂ` of the same module is given through `IsBaseChange`, associativity
of scalar extension identifies `ℂ ⊗[ℝ] (ℝ ⊗[ℤ] V)` with `Vℂ`.  This equivalence
intertwines ordinary conjugation on the left with the lattice-induced conjugation on the right.

The comparison is the base-change bridge needed to transfer real linear data on a lattice, such as
an almost complex structure, to its chosen abstract complexification.

## Main declarations

* `TauCeti.Hodge.Realification`: the real scalar extension of an integral module.
* `TauCeti.Hodge.realificationComplexEquiv`: the canonical comparison between its complexification
  and an abstract complexification of the original integral module.
* `TauCeti.Hodge.realificationComplexEquiv_conj`: compatibility of that comparison with
  conjugation.
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

/-- The tensor-product realification satisfies the base-change interface. -/
theorem isBaseChange_realificationMap :
    IsBaseChange ℝ (realificationMap (V := V)) :=
  TensorProduct.isBaseChange ℤ V ℝ

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
@[simp]
theorem realificationComplexEquiv_one_tmul_realificationMap
    (hℂ : IsBaseChange ℂ ιℂ) (x : V) :
    realificationComplexEquiv hℂ (1 ⊗ₜ[ℝ] realificationMap x) = ιℂ x := by
  have hmap : realificationMap x = 1 ⊗ₜ[ℤ] x := rfl
  rw [hmap, realificationComplexEquiv_tmul_tmul]
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

end TauCeti.Hodge
