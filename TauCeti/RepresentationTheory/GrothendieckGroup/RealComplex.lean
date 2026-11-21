/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import TauCeti.RepresentationTheory.GrothendieckGroup.ExtEulerMatrix
public import TauCeti.RepresentationTheory.GrothendieckGroup.EulerDuality

/-!
# A nonsplit Euler form: the complex numbers over the reals

For the real algebra `ℂ`, the regular module is both simple and projective. Its composition
multiplicity in itself is one, whereas its endomorphism algebra has real dimension two.
The Cartan matrix is `[1]` and the integral multiplicity pairing has entry `1`, whereas
`TauCeti.RealComplex.projectiveExtEuler_of_of_eq_two` evaluates the projective Ext-Euler pairing
on the two generator classes to `2`. This pairing is not perfect over `ℤ`.

The ordinary Ext-Euler matrix in the simple-class basis is `[2]`.
`TauCeti.RealComplex.diagonal_finrank_end_eq_two` computes `D = [2]`, and
`TauCeti.RealComplex.cartanMatrix_transpose_mul_extEulerMatrix_eq_two` verifies `Cᵀ E = [2]`,
not the identity matrix. Every pair of finitely generated complex modules is Euler-admissible
because these modules are projective and their Hom spaces are finite-dimensional over `ℝ`.
This is an ungraded example; no graded/ungraded Ext comparison is asserted.

## References

* Peter Webb, *A Course in Finite Group Representation Theory*, Chapter 7, Sections 7.3--7.4,
  for the division-endomorphism correction to the projective/simple pairing.
-/

public section

noncomputable section

namespace TauCeti.RealComplex

open CategoryTheory
open scoped ModuleCat.Algebra Matrix

/-- The singleton simple family for the algebra `ℂ`. -/
abbrev simples (_ : Unit) : FGModuleCat.{0} ℂ := FGModuleCat.of ℂ ℂ

/-- The singleton indecomposable-projective family for the algebra `ℂ`. -/
abbrev projectives (_ : Unit) : (finiteProjectiveModules ℂ).FullSubcategory :=
  ⟨ModuleCat.of ℂ ℂ, finiteProjectiveModules_iff.mpr ⟨inferInstance, inferInstance⟩⟩

/-- The regular complex module is the only simple complex module, up to isomorphism. -/
theorem isExhaustiveSimpleFamily_simples : IsExhaustiveSimpleFamily simples :=
  isExhaustiveSimpleFamily_of_isLocalRing (simples ())

/-- The regular complex module is the only indecomposable finitely generated projective complex
module, up to isomorphism. -/
theorem isExhaustiveIndecomposableProjectiveFamily_projectives :
    IsExhaustiveIndecomposableProjectiveFamily projectives :=
  isExhaustiveIndecomposableProjectiveFamily_of_isLocalRing (projectives ()) (LinearEquiv.refl _ _)

/-- Every pair of finitely generated complex modules is Euler-admissible over `ℝ`. -/
theorem isEulerAdmissibleOn_isFG :
    IsEulerAdmissibleOn.{0} ℝ (ModuleCat.isFG ℂ) (ModuleCat.isFG ℂ) :=
  TauCeti.isEulerAdmissibleOn_isFG ℝ (finiteModules_le_admitsFiniteResolution ℂ)

/-- Endomorphisms of the regular complex module have real dimension two with the scalar
restriction used by the categorical Euler form. -/
@[simp] theorem finrank_end :
    letI : Module ℝ ℂ := Module.restrictScalars ℝ ℂ ℂ
    Module.finrank ℝ (Module.End ℂ ℂ) = 2 := by
  rw [Module.finrank_linearMap, Module.finrank_self, one_mul, Complex.finrank_real_complex]

/-- The categorical Hom space from the regular complex module to itself has real dimension two. -/
@[simp] theorem finrank_hom :
    Module.finrank ℝ (ModuleCat.of ℂ ℂ ⟶ ModuleCat.of ℂ ℂ) = 2 := by
  rw [ModuleCat.homLinearEquiv.finrank_eq]
  exact finrank_end

/-- The ordinary Ext-Euler value of the simple complex module over the reals is two, independently
of the chosen Ext universe and admissibility witness. -/
@[simp] theorem extEuler_eq_two [HasExt.{w} (ModuleCat.{0} ℂ)]
    (h : IsEulerAdmissible.{w} ℝ (ModuleCat.of ℂ ℂ) (ModuleCat.of ℂ ℂ)) :
    extEuler ℝ h = 2 := by
  rw [extEuler_projective, finrank_hom]
  norm_num

/-- The Cartan matrix for `ℂ` is the one-by-one identity matrix. -/
@[simp] theorem cartanMatrix_eq_one :
    cartanMatrix projectives simples (fun _ ↦ isIndecomposableModule_self ℂ)
      Subsingleton.pairwise isExhaustiveIndecomposableProjectiveFamily_projectives
        Subsingleton.pairwise isExhaustiveSimpleFamily_simples = 1 := by
  ext i j
  simp only [cartanMatrix_apply, Matrix.one_apply, Subsingleton.elim i j, ↓reduceIte]
  exact_mod_cast jordanHolderMultiplicity_eq_one_of_isSimpleModule_of_linearEquiv ℂ
    (LinearEquiv.refl ℂ ℂ)

/-- The integral projective/simple multiplicity pairing has entry one on the two generator
classes. -/
theorem projectiveSimplePairing_of_of_eq_one :
    projectiveSimplePairing projectives simples (fun _ ↦ isIndecomposableModule_self ℂ)
      Subsingleton.pairwise isExhaustiveIndecomposableProjectiveFamily_projectives
      Subsingleton.pairwise isExhaustiveSimpleFamily_simples
      (ExactK0.of (projectives ())) (ExactK0.of (simples ())) = 1 := by
  simp

/-- The projective Ext-Euler pairing has entry two on the two generator classes. -/
theorem projectiveExtEuler_of_of_eq_two :
    projectiveExtEuler ℝ ℂ (ExactK0.of (projectives ())) (ExactK0.of (simples ())) = 2 := by
  simp

/-- In the simple-class basis, the categorical Ext-Euler matrix over `ℝ` is `[2]`. -/
@[simp] theorem extEulerMatrix_eq_two :
    let b := (simpleClassBasis simples Subsingleton.pairwise isExhaustiveSimpleFamily_simples).map
      (finiteModulesExactK0Equiv ℂ).toIntLinearEquiv
    extEulerMatrix (ModuleCat.isFG ℂ) (ModuleCat.isFG ℂ)
      (isExtensionClosed_finiteModules ℂ) (isExtensionClosed_finiteModules ℂ)
      isEulerAdmissibleOn_isFG b b = 2 := by
  dsimp only
  ext i j
  rw [extEulerMatrix_of_of (X := simples i) (Y := simples j) (hi := by simp) (hj := by simp)]
  simp [Matrix.ofNat_apply, Subsingleton.elim i j]

/-- The diagonal matrix of simple endomorphism dimensions over `ℝ` is `[2]`. -/
theorem diagonal_finrank_end_eq_two :
    Matrix.diagonal (fun i : Unit ↦ (Module.finrank ℝ (Module.End ℂ (simples i).obj) : ℤ)) = 2 := by
  simp only [finrank_end, Nat.cast_ofNat]
  exact Matrix.diagonal_natCast 2

/-- For `ℂ` over `ℝ`, the Cartan/Ext-Euler product `Cᵀ E` equals the diagonal `[2]`. -/
theorem cartanMatrix_transpose_mul_extEulerMatrix_eq_two :
    let b := (simpleClassBasis simples Subsingleton.pairwise isExhaustiveSimpleFamily_simples).map
      (finiteModulesExactK0Equiv ℂ).toIntLinearEquiv
    (cartanMatrix projectives simples (fun _ ↦ isIndecomposableModule_self ℂ)
      Subsingleton.pairwise isExhaustiveIndecomposableProjectiveFamily_projectives
      Subsingleton.pairwise isExhaustiveSimpleFamily_simples)ᵀ *
      extEulerMatrix (ModuleCat.isFG ℂ) (ModuleCat.isFG ℂ)
        (isExtensionClosed_finiteModules ℂ) (isExtensionClosed_finiteModules ℂ)
        isEulerAdmissibleOn_isFG b b = 2 := by
  dsimp only
  rw [cartanMatrix_transpose_mul_extEulerMatrix_eq_diagonal _ _ _ _ _ _ _
    (f := fun _ ↦ LinearMap.id) (fun _ ↦ isProjectiveCover_id)]
  exact diagonal_finrank_end_eq_two

/-- The unweighted Cartan/Ext-Euler identity `Cᵀ E = I` fails for `ℂ` over `ℝ`. -/
theorem cartanMatrix_transpose_mul_extEulerMatrix_ne_one :
    let b := (simpleClassBasis simples Subsingleton.pairwise isExhaustiveSimpleFamily_simples).map
      (finiteModulesExactK0Equiv ℂ).toIntLinearEquiv
    (cartanMatrix projectives simples (fun _ ↦ isIndecomposableModule_self ℂ)
      Subsingleton.pairwise isExhaustiveIndecomposableProjectiveFamily_projectives
      Subsingleton.pairwise isExhaustiveSimpleFamily_simples)ᵀ *
      extEulerMatrix (ModuleCat.isFG ℂ) (ModuleCat.isFG ℂ)
        (isExtensionClosed_finiteModules ℂ) (isExtensionClosed_finiteModules ℂ)
        isEulerAdmissibleOn_isFG b b ≠ 1 := by
  dsimp only
  rw [cartanMatrix_transpose_mul_extEulerMatrix_eq_two]
  intro h
  have hentry := congrArg (fun M : Matrix Unit Unit ℤ ↦ M () ()) h
  norm_num [Matrix.ofNat_apply, Matrix.one_apply] at hentry

/-- The projective Ext-Euler pairing is not the integral multiplicity pairing for this nonsplit
real algebra. -/
theorem projectiveExtEuler_ne_projectiveSimplePairing :
    projectiveExtEuler ℝ ℂ ≠
      projectiveSimplePairing projectives simples (fun _ ↦ isIndecomposableModule_self ℂ)
        Subsingleton.pairwise isExhaustiveIndecomposableProjectiveFamily_projectives
        Subsingleton.pairwise isExhaustiveSimpleFamily_simples := by
  rw [ne_eq, projectiveExtEuler_eq_projectiveSimplePairing_iff _ _ _ _ _ _ _
    (f := fun _ ↦ LinearMap.id) (fun _ ↦ isProjectiveCover_id)]
  simp

/-- The projective Ext-Euler pairing for `ℂ` over `ℝ` is not perfect over `ℤ`. -/
theorem not_isPerfPair_projectiveExtEuler : ¬ (projectiveExtEuler ℝ ℂ).IsPerfPair := by
  rw [projectiveExtEuler_isPerfPair_iff projectives simples (fun _ ↦ isIndecomposableModule_self ℂ)
    Subsingleton.pairwise isExhaustiveIndecomposableProjectiveFamily_projectives
    Subsingleton.pairwise isExhaustiveSimpleFamily_simples
    (f := fun _ ↦ LinearMap.id) (fun _ ↦ isProjectiveCover_id)]
  simp

end TauCeti.RealComplex
