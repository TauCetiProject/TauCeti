/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.ForgetGrading
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Matrix
-- Unfold the specialized basis locally to apply Mathlib's base-change matrix theorem.
import all TauCeti.Algebra.Polynomial.Laurent.Specialization
import TauCeti.LinearAlgebra.Basis.Basic

/-!
# Specializing the graded Cartan matrix

The graded Cartan matrix has Laurent-polynomial entries. Specializing the projective and module
bases coefficientwise shows that its value at a unit `ε` is the matrix of the specialized Cartan
map. At `q = 1`, the forgetful square identifies this matrix with the ordinary Cartan matrix
whenever forgetting grading carries the two specialized bases to the chosen ordinary bases.

No assertion that forgetting grading is an equivalence is needed. The basis compatibility
hypotheses already force the two forgetful maps to preserve coordinates, which is precisely the
information needed for the matrix comparison. In applications, the hypotheses are discharged by
graded projective and simple class bases whose underlying modules give the corresponding ordinary
bases.

## Main results

* `TauCeti.toMatrix_gradedCartanMapSpecialized`: specialization evaluates every entry of the
  graded Cartan matrix.
* `TauCeti.toMatrix_cartanMap_eq_map_gradedCartanMatrix`: at `q = 1`, compatible graded and
  ordinary bases give the ordinary Cartan matrix.

The convention is that rows are module coordinates and columns are projective coordinates, as in
Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", Section 2.2.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory

universe uk uA uI uJ

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A)

variable {I : Type uI} {J : Type uJ} [Fintype I] [DecidableEq I] [Finite J]

/-- **Specializing the graded Cartan matrix evaluates its entries.** The matrix of the Cartan map
specialized at `q = ε`, in the coefficientwise-specialized bases, is obtained by evaluating the
Laurent-polynomial graded Cartan matrix at `ε`. -/
theorem toMatrix_gradedCartanMapSpecialized (ε : ℤˣ)
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (bM : Module.Basis J (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜))) :
    LinearMap.toMatrix (LaurentSpecialization.basis ε bP)
        (LaurentSpecialization.basis ε bM) (gradedCartanMapSpecialized 𝒜 ε) =
      (gradedCartanMatrix 𝒜 bP bM).map (laurentEval ε) := by
  classical
  let _ : Algebra (LaurentPolynomial ℤ) ℤ := (laurentEval ε).toAlgebra
  have := LaurentSpecialization.isScalarTower ε
    (N := LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)) fun _ ↦ rfl
  have := LaurentSpecialization.isScalarTower ε
    (N := LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)) fun _ ↦ rfl
  have hP := LaurentSpecialization.isBaseChange ε
    (N := LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)) fun _ ↦ rfl
  have hspec : gradedCartanMapSpecialized 𝒜 ε =
      hP.linearMapLeftRightHom (LaurentSpecialization.mk ε) (gradedCartanMap 𝒜) :=
    LaurentSpecialization.hom_ext ε fun x ↦ by
      rw [gradedCartanMapSpecialized_mk, IsBaseChange.linearMapLeftRightHom_comp_apply]
  rw [hspec]
  refine (IsBaseChange.linearMapLeftRightHom_toMatrix (ibcM := hP)
    (ibcN := LaurentSpecialization.isBaseChange ε fun _ ↦ rfl) (b := bP) (c := bM)
    (f := gradedCartanMap 𝒜)).trans ?_
  ext i j
  rw [Matrix.map_apply, Matrix.map_apply, LinearMap.toMatrix_apply, gradedCartanMatrix_apply]
  rfl

/-- **At `q = 1`, forgetting grading recovers the ordinary Cartan matrix.** Suppose the
coefficientwise specializations of graded projective and module bases become chosen bases of
ordinary projective `K₀` and module `G₀` after forgetting grading. Then evaluating the graded
Cartan matrix at one gives the matrix of the ordinary Cartan map in those bases. -/
theorem toMatrix_cartanMap_eq_map_gradedCartanMatrix
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (bM : Module.Basis J (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)))
    (cP : Module.Basis I ℤ (ExactK0.{uA} (finiteProjectiveModulesExactStructure A)))
    (cM : Module.Basis J ℤ (ExactK0.{uA} (finiteModulesExactStructure A)))
    (hP : ∀ j, gradedFiniteProjectiveModulesForgetK0 𝒜
        (LaurentSpecialization.basis (1 : ℤˣ) bP j) = cP j)
    (hM : ∀ i, gradedFiniteModulesForgetK0 𝒜
        (LaurentSpecialization.basis (1 : ℤˣ) bM i) = cM i) :
    LinearMap.toMatrix cP cM (cartanMap A).toIntLinearMap =
      (gradedCartanMatrix 𝒜 bP bM).map (laurentEval (1 : ℤˣ)) := by
  classical
  let bP₁ := LaurentSpecialization.basis (1 : ℤˣ) bP
  let bM₁ := LaurentSpecialization.basis (1 : ℤˣ) bM
  have hrepr (x : LaurentSpecialization (1 : ℤˣ)
      (LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜))) :
      cM.repr (gradedFiniteModulesForgetK0 𝒜 x) = bM₁.repr x :=
    Module.Basis.repr_map_eq_of_map_basis bM₁ cM (gradedFiniteModulesForgetK0 𝒜) hM x
  have hcomm := gradedFiniteModulesForgetK0_comp_gradedCartanMapSpecialized 𝒜
  ext i j
  rw [LinearMap.toMatrix_apply, Matrix.map_apply, gradedCartanMatrix_apply]
  rw [← hP j]
  have hj := LinearMap.congr_fun hcomm (bP₁ j)
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at hj
  rw [← hj, hrepr]
  rw [LaurentSpecialization.basis_apply]
  rw [gradedCartanMapSpecialized_mk, LaurentSpecialization.basis_repr_mk_apply]

end TauCeti
