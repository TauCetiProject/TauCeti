/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangular.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transvection

/-!
# Transvections in the upper-unitriangular group

For a ring `R` and `i < j`, the transvection `e_ij(c) = 1 + c Eᵢⱼ` is upper unitriangular. This
file bundles it as an element `TauCeti.UpperUnitriangularGroup.transvection` of `Uₘ(R)` and
transfers the basic API of `TauCeti.transvectionUnit`: injectivity in the parameter, additivity,
inverses and the Chevalley commutator relation `[e_ij(c), e_jl(d)] = e_il(cd)`. It also records
the effect of right multiplication by `e_ij(c)` on the entries of a matrix, a column operation.

## Main declarations

* `TauCeti.UpperUnitriangularGroup.transvection`: the transvection `e_ij(c)`, `i < j`, as an
  element of `Uₘ(R)`.
* `TauCeti.UpperUnitriangularGroup.commutatorElement_transvection`: the Chevalley commutator
  relation in `Uₘ(R)`.
* `TauCeti.UpperUnitriangularGroup.coe_mul_transvection_apply`: right multiplication by
  `e_ij(c)` adds `c` times column `i` to column `j`.
-/

public section

open Matrix
open scoped commutatorElement

namespace TauCeti.UpperUnitriangularGroup

universe u

variable {R : Type u} [Ring R] {m : Type*} [Fintype m] [LinearOrder m] {i j l : m}

/-- The transvection `e_ij(c) = 1 + c Eᵢⱼ` with `i < j`, as an element of `Uₘ(R)`. -/
def transvection (hij : i < j) (c : R) : upperUnitriangularGroup m R :=
  ⟨transvectionUnit hij.ne c, by
    rw [mem_iff, isUpperUnitriangular_def]
    refine ⟨fun k l hlk ↦ ?_, fun k ↦ ?_⟩
    · have hlk' : l < k := hlk
      have hkl : ¬(i = k ∧ j = l) := fun h ↦ by
        obtain ⟨rfl, rfl⟩ := h
        exact hlk'.not_gt hij
      simp [coe_transvectionUnit_eq_one_add_single, hkl, one_apply_ne hlk'.ne']
    · have hkk : ¬(i = k ∧ j = k) := fun h ↦ hij.ne (h.1.trans h.2.symm)
      simp [coe_transvectionUnit_eq_one_add_single, hkk]⟩

/-- The underlying element of `GLₘ(R)` of `TauCeti.UpperUnitriangularGroup.transvection` is
`TauCeti.transvectionUnit`. -/
@[simp]
theorem coe_transvection (hij : i < j) (c : R) :
    ((transvection hij c : upperUnitriangularGroup m R) : GL m R) = transvectionUnit hij.ne c :=
  (rfl)

/-- Distinct parameters give distinct transvections. -/
theorem transvection_injective (hij : i < j) :
    Function.Injective (transvection (R := R) hij) := fun _ _ h ↦
  transvectionUnit_injective hij.ne (congrArg Subtype.val h :)

/-- Two transvections at the same position agree exactly when their parameters do. -/
@[simp]
theorem transvection_inj (hij : i < j) {c d : R} :
    transvection hij c = transvection hij d ↔ c = d :=
  (transvection_injective hij).eq_iff

/-- The transvection of parameter zero is the identity. -/
@[simp]
theorem transvection_zero (hij : i < j) : transvection hij (0 : R) = 1 :=
  Subtype.ext (transvectionUnit_zero hij.ne)

/-- A transvection is the identity exactly when its parameter is zero. -/
@[simp]
theorem transvection_eq_one_iff (hij : i < j) {c : R} : transvection hij c = 1 ↔ c = 0 := by
  rw [← transvection_zero hij, transvection_inj]

/-- The parameter of a transvection is additive. -/
@[simp]
theorem transvection_add (hij : i < j) (c d : R) :
    transvection hij (c + d) = transvection hij c * transvection hij d :=
  Subtype.ext (transvectionUnit_add hij.ne c d)

/-- The inverse of a transvection negates its parameter. -/
@[simp]
theorem transvection_inv (hij : i < j) (c : R) :
    (transvection hij c)⁻¹ = transvection hij (-c) :=
  Subtype.ext (transvectionUnit_inv hij.ne c)

/-- The Chevalley commutator relation in `Uₘ(R)`: `[e_ij(c), e_jl(d)] = e_il(cd)`. -/
theorem commutatorElement_transvection (hij : i < j) (hjl : j < l) (c d : R) :
    ⁅transvection hij c, transvection hjl d⁆ = transvection (hij.trans hjl) (c * d) :=
  Subtype.ext (commutatorElement_transvectionUnit hij.ne hjl.ne (hij.trans hjl).ne c d)

/-- Right multiplication by `e_ij(c)` adds `c` times column `i` to column `j`. -/
theorem coe_mul_transvection_apply (g : upperUnitriangularGroup m R) (hij : i < j)
    (c : R) (k l : m) :
    (((g * transvection hij c : upperUnitriangularGroup m R) : GL m R) : Matrix m m R) k l =
      ((g : GL m R) : Matrix m m R) k l +
        if l = j then ((g : GL m R) : Matrix m m R) k i * c else 0 := by
  simp only [Subgroup.coe_mul, Units.val_mul, coe_transvection,
    coe_transvectionUnit_eq_one_add_single, mul_add, mul_one, Matrix.add_apply]
  split_ifs with hlj
  · rw [hlj, mul_single_apply_same]
  · rw [mul_single_apply_of_ne (hbj := hlj)]

end TauCeti.UpperUnitriangularGroup
