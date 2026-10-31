/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Pivotal.Character
public import TauCeti.CategoryTheory.Semisimple.FrobeniusPerron

/-!
# Categorical dimensions are bounded by Frobenius–Perron dimensions

In a pivotal fusion category over `ℂ`, the absolute value of either categorical dimension of
an object is at most its Frobenius–Perron dimension. The categorical dimensions are
endomorphisms of the tensor unit; the statements read them as complex scalars through
`TauCeti.endAlgEquivOfSimple ℂ (𝟙_ C)`.

The bound follows from the corresponding bound for every complex character of the
Grothendieck ring (`TauCeti.SplitK0.norm_ringHom_of_le_frobeniusPerronDim`). On a simple class,
the value of a character is an eigenvalue of the fusion matrix, so its norm is bounded by the
spectral radius, which is the Frobenius–Perron dimension. Additivity and the triangle inequality
then give the bound for arbitrary objects. Neither a spherical structure nor positivity of the
categorical dimensions is required.

## Main results

* `TauCeti.norm_leftDim_le_frobeniusPerronDim`: the left categorical dimension bound.
* `TauCeti.norm_rightDim_le_frobeniusPerronDim`: the right categorical dimension bound.
* `TauCeti.norm_globalDim_le_frobeniusPerronGlobalDim`: the absolute value of the global
  dimension is at most the Frobenius–Perron dimension of the category.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15],
  Sections 3.3 and 4.7.
-/

public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace TauCeti

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [RigidCategory C] [PivotalCategory C] [Linear ℂ C]
  [MonoidalLinear ℂ C] [IsFiniteSemisimpleCategory C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  [EssentiallySmall.{w} C]

section Finite

variable [Finite (SimpleClasses C)]

/-- In a complex pivotal fusion category, the absolute value of the left categorical dimension
of any object is at most its Frobenius–Perron dimension. -/
theorem norm_leftDim_le_frobeniusPerronDim (X : C) :
    ‖endAlgEquivOfSimple ℂ (𝟙_ C) (End.of (leftDim X))‖ ≤ frobeniusPerronDim ℂ X := by
  simpa only [SplitK0.leftDimChar_of] using
    SplitK0.norm_ringHom_of_le_frobeniusPerronDim ℂ (SplitK0.leftDimChar ℂ C) X

/-- In a complex pivotal fusion category, the absolute value of the right categorical dimension
of any object is at most its Frobenius–Perron dimension. -/
theorem norm_rightDim_le_frobeniusPerronDim (X : C) :
    ‖endAlgEquivOfSimple ℂ (𝟙_ C) (End.of (rightDim X))‖ ≤ frobeniusPerronDim ℂ X := by
  simpa only [SplitK0.rightDimChar_of] using
    SplitK0.norm_ringHom_of_le_frobeniusPerronDim ℂ (SplitK0.rightDimChar ℂ C) X

end Finite

section GlobalDim

variable (C) [Fintype (SimpleClasses C)]

/-- In a complex pivotal fusion category, the absolute value of the global dimension is at most
the Frobenius–Perron dimension of the category. -/
theorem norm_globalDim_le_frobeniusPerronGlobalDim :
    ‖endAlgEquivOfSimple ℂ (𝟙_ C) (End.of (globalDim C))‖ ≤ frobeniusPerronGlobalDim.{w} ℂ C := by
  rw [endAlgEquivOfSimple_globalDim, Complex.norm_real, Real.norm_of_nonneg
    (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _), frobeniusPerronGlobalDim_def]
  exact Finset.sum_le_sum fun S _ ↦
    pow_le_pow_left₀ (norm_nonneg _) (norm_leftDim_le_frobeniusPerronDim S.repr) 2

end GlobalDim

end TauCeti
