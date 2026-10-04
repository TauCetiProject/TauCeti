/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.ExteriorAlgebra.BaseChange
public import TauCeti.LinearAlgebra.TensorProduct.Submodule
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.LinearAlgebra.TensorProduct.Decomposition
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Scalar extension of exterior powers

For every commutative `R`-algebra `A`, the comparison identifies
`⋀[A]^n (A ⊗[R] M)` with `A ⊗[R] (⋀[R]^n M)`. It is natural in `M` and sends a
wedge of pure tensors to the product of their coefficients tensored with the original wedge.
No flatness or freeness assumption is needed: the grading splits the inclusion of each
exterior power into the exterior algebra before scalar extension.

These comparisons allow exterior powers of algebraic-group representations to be evaluated
on arbitrary value algebras, and identify scalar extensions of their exterior lines.
-/

public section

open scoped TensorProduct

variable {R : Type*} (A : Type*) {M N : Type*}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The exterior-algebra comparison preserves each homogeneous degree. -/
@[simp]
theorem TauCeti.exteriorAlgebraEquivBaseChange_map_exteriorPower (n : ℕ) :
    (⋀[A]^n (A ⊗[R] M)).map (TauCeti.exteriorAlgebraEquivBaseChange A).toLinearMap =
      (⋀[R]^n M).baseChange A := by
  simp only [_root_.ExteriorAlgebra.exteriorPower]
  rw [← AlgEquiv.toLinearEquiv_toLinearMap, ← AlgEquiv.toAlgHom_toLinearMap,
    Submodule.map_pow, Submodule.baseChange_pow]
  simp only [AlgEquiv.toAlgHom_toLinearMap, AlgEquiv.toLinearEquiv_toLinearMap]
  congr 1
  rw [← LinearMap.range_comp]
  have h : (TauCeti.exteriorAlgebraEquivBaseChange (M := M) A).toLinearMap.comp
      (_root_.ExteriorAlgebra.ι A) = (_root_.ExteriorAlgebra.ι R).baseChange A := by
    apply LinearMap.ext
    intro x
    exact TauCeti.exteriorAlgebraEquivBaseChange_ι A x
  rw [h]
  ext x
  exact SetLike.ext_iff.mp (LinearMap.lTensor_range
    (Q := A) (g := _root_.ExteriorAlgebra.ι R)) x

namespace TauCeti.exteriorPower

private theorem baseChange_subtype_injective (n : ℕ) :
    Function.Injective ((⋀[R]^n M).subtype.baseChange A) := by
  intro x y h
  exact DirectSum.toBaseChange_injective (S := A) (fun i ↦ ⋀[R]^i M) n
    (Subtype.ext h)

/-- Exterior powers commute with extension of scalars over arbitrary commutative rings. -/
noncomputable def equivBaseChange (n : ℕ) :
    (⋀[A]^n (A ⊗[R] M)) ≃ₗ[A] A ⊗[R] (⋀[R]^n M) :=
  ((TauCeti.exteriorAlgebraEquivBaseChange A).toLinearEquiv.ofSubmodules _ _
    (TauCeti.exteriorAlgebraEquivBaseChange_map_exteriorPower A n)).trans
      (LinearEquiv.ofInjective ((⋀[R]^n M).subtype.baseChange A)
        (baseChange_subtype_injective A n)).symm

/-- The exterior-power comparison is the restriction of the exterior-algebra comparison. -/
@[simp]
theorem subtype_baseChange_equivBaseChange (n : ℕ) (x : ⋀[A]^n (A ⊗[R] M)) :
    (⋀[R]^n M).subtype.baseChange A (equivBaseChange A n x) =
      TauCeti.exteriorAlgebraEquivBaseChange A (x : ExteriorAlgebra A (A ⊗[R] M)) := by
  exact (LinearEquiv.ofInjective_symm_apply _ (h := baseChange_subtype_injective A n) _).trans
    (LinearEquiv.ofSubmodules_apply _ _ x)

/-- A wedge of pure tensors corresponds to the product of the scalars tensored with the wedge. -/
@[simp]
theorem equivBaseChange_ιMulti_tmul {n : ℕ} (a : Fin n → A) (m : Fin n → M) :
    equivBaseChange A n (_root_.exteriorPower.ιMulti A n (fun i ↦ a i ⊗ₜ[R] m i)) =
      (∏ i, a i) ⊗ₜ[R] _root_.exteriorPower.ιMulti R n m := by
  apply baseChange_subtype_injective A n
  simp only [subtype_baseChange_equivBaseChange, _root_.exteriorPower.ιMulti_apply_coe,
    TauCeti.exteriorAlgebraEquivBaseChange_ιMulti_tmul, LinearMap.baseChange_tmul,
    Submodule.coe_subtype]

/-- The inverse comparison on the spanning pure tensors. -/
@[simp]
theorem equivBaseChange_symm_tmul_ιMulti {n : ℕ} (a : A) (m : Fin n → M) :
    (equivBaseChange A n).symm (a ⊗ₜ[R] _root_.exteriorPower.ιMulti R n m) =
      a • _root_.exteriorPower.ιMulti A n (fun i ↦ 1 ⊗ₜ[R] m i) := by
  apply (equivBaseChange A n).injective
  simp [TensorProduct.smul_tmul']

/-- The exterior-power comparison intertwines the maps induced by any linear map. -/
@[simp]
theorem equivBaseChange_map (n : ℕ) (f : M →ₗ[R] N) (x : ⋀[A]^n (A ⊗[R] M)) :
    equivBaseChange A n (_root_.exteriorPower.map n (f.baseChange A) x) =
      (_root_.exteriorPower.map n f).baseChange A (equivBaseChange A n x) := by
  apply baseChange_subtype_injective A n
  rw [subtype_baseChange_equivBaseChange, _root_.exteriorPower.coe_map]
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
    _root_.exteriorPower.subtype_comp_map_eq, LinearMap.baseChange_comp,
    LinearMap.comp_apply, subtype_baseChange_equivBaseChange]
  exact TauCeti.exteriorAlgebraEquivBaseChange_map A f x

end TauCeti.exteriorPower
