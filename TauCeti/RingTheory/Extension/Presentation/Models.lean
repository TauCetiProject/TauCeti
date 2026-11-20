/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.RingTheory.Extension.Presentation.Core

/-!
# Finitely generated models of finitely presented algebras

A finitely presented algebra over `A` is obtained by base change from a finitely presented
algebra over a finitely generated `R`-subalgebra of `A`. This is the affine approximation
step for spreading out finitely presented algebras. For `R = ℤ`, finite generation makes
the coefficient subalgebra Noetherian by the Hilbert basis theorem.

The coefficient-model argument adapts
`Algebra.IsStandardSmoothOfRelativeDimension.exists_subalgebra_fg` from
`Mathlib.RingTheory.Smooth.NoetherianDescent` (Judith Ludwig and Christian Merten) to
finitely presented algebras. It uses `Algebra.Presentation.ModelOfHasCoeffs` and
`Algebra.Presentation.tensorModelOfHasCoeffsEquiv`.

## References

* The Stacks Project, Tags 00R0 and 05N9.
-/

public noncomputable section

universe u

open TensorProduct MvPolynomial

namespace Algebra.FinitePresentation

/-- A finitely presented `A`-algebra descends to a finitely generated `R`-subalgebra
`A₀` of `A`, with a finitely presented model `B₀` and a pushout square.
Taking `R = ℤ` makes `A₀` Noetherian by finite generation and the Hilbert basis theorem. -/
theorem exists_subalgebra_fg_isPushout
    (R : Type*) [CommRing R] (A : Type u) (B : Type*) [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B]
    [Algebra.FinitePresentation A B] :
    ∃ (A₀ : Subalgebra R A) (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra A₀ B₀)
      (_ : Algebra B₀ B) (_ : IsScalarTower A₀ B₀ B),
      A₀.FG ∧ Algebra.FinitePresentation A₀ B₀ ∧ Algebra.IsPushout A₀ A B₀ B := by
  let P := Presentation.ofFinitePresentation A B
  let A₀ : Subalgebra R A := Algebra.adjoin R P.coeffs
  have hA₀ : A₀.FG := Subalgebra.fg_def.mpr ⟨_, P.finite_coeffs, rfl⟩
  have : P.HasCoeffs A₀ := ⟨by
    rw [Subalgebra.setRange_algebraMap]
    exact Algebra.subset_adjoin⟩
  let B₀ := P.ModelOfHasCoeffs A₀
  let e := P.tensorModelOfHasCoeffsEquiv A₀
  let f : B₀ →ₐ[A₀] B :=
    (e.toAlgHom.restrictScalars A₀).comp Algebra.TensorProduct.includeRight
  let _ : Algebra B₀ B := f.toRingHom.toAlgebra
  have : IsScalarTower A₀ B₀ B := .of_algebraMap_eq fun x ↦ (f.commutes x).symm
  exact ⟨A₀, B₀, inferInstance, inferInstance, inferInstance, inferInstance, hA₀,
    inferInstance, ⟨IsBaseChange.of_equiv e.toLinearEquiv fun _ ↦ rfl⟩⟩

end Algebra.FinitePresentation
