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
Consequently the Cartan matrix is `[1]`, the integral multiplicity pairing has entry `1`, and
both the projective Hom pairing and the Ext-Euler matrix have entry `2`.

This file computes these values using the categorical Cartan and Euler constructions. In
particular, `cartanMatrix_transpose_mul_extEulerMatrix_eq_diagonal` verifies `Cᵀ E = D = [2]`,
rather than the incorrect split-field identity `Cᵀ E = I`. Euler admissibility is proved for all
finitely generated
complex modules: they are projective and their Hom spaces are finite-dimensional over `ℝ`.
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
theorem simples_exhaustive : IsExhaustiveSimpleFamily simples :=
  isExhaustiveSimpleFamily_of_isLocalRing (simples ())

/-- The regular complex module is the only indecomposable finitely generated projective complex
module, up to isomorphism. -/
theorem projectives_exhaustive : IsExhaustiveIndecomposableProjectiveFamily projectives :=
  isExhaustiveIndecomposableProjectiveFamily_of_isLocalRing (projectives ()) (LinearEquiv.refl _ _)

/-- Every pair of finitely generated complex modules is Euler-admissible over `ℝ`. -/
theorem isEulerAdmissibleOn :
    IsEulerAdmissibleOn.{0} ℝ (ModuleCat.isFG ℂ) (ModuleCat.isFG ℂ) := by
  refine isEulerAdmissibleOn_of_projective ℝ (fun _ _ ↦ inferInstance) ?_
  intro X Y hX hY
  have : Module.Finite ℂ X := (ModuleCat.isFG_iff X).mp hX
  have : Module.Finite ℂ Y := (ModuleCat.isFG_iff Y).mp hY
  have : Module.Finite ℝ Y := Module.Finite.trans ℂ Y
  infer_instance

/-- Endomorphisms of the simple complex module have real dimension two, not one. -/
@[simp] theorem finrank_end : Module.finrank ℝ (Module.End ℂ (simples ()).obj) = 2 := by
  rw [Module.finrank_linearMap, Module.finrank_self, one_mul, Complex.finrank_real_complex]

/-- The raw Hom dimension of the regular complex module over the reals is two. -/
@[simp] theorem finrank_hom :
    Module.finrank ℝ ((projectives ()).obj ⟶ (simples ()).obj) = 2 := by
  rw [ModuleCat.homLinearEquiv.finrank_eq]
  exact finrank_end

/-- The ordinary Ext-Euler value of the simple complex module over the reals is two. -/
@[simp] theorem extEuler_eq_two :
    extEuler ℝ (isEulerAdmissibleOn.isEulerAdmissible (simples ()).property
      (simples ()).property) = 2 := by
  rw [extEuler_projective, finrank_hom]
  norm_num

/-- The Cartan matrix for `ℂ` is the one-by-one identity matrix. -/
@[simp] theorem cartanMatrix_eq_one :
    cartanMatrix projectives simples (fun _ ↦ isIndecomposableModule_self ℂ)
      Subsingleton.pairwise projectives_exhaustive Subsingleton.pairwise
        simples_exhaustive = 1 := by
  ext i j
  simp only [cartanMatrix_apply, Matrix.one_apply, Subsingleton.elim i j, ↓reduceIte]
  exact_mod_cast jordanHolderMultiplicity_eq_one_of_isSimpleModule_of_linearEquiv ℂ
    (LinearEquiv.refl ℂ ℂ)

/-- The integral projective/simple multiplicity pairing has entry one, even though the raw Hom
and Ext-Euler pairings have entry two. -/
theorem projectiveSimplePairing_eq_one :
    projectiveSimplePairing projectives simples (fun _ ↦ isIndecomposableModule_self ℂ)
      Subsingleton.pairwise projectives_exhaustive Subsingleton.pairwise simples_exhaustive
      (ExactK0.of (projectives ())) (ExactK0.of (simples ())) = 1 := by
  simp

/-- In the simple-class basis, the categorical Ext-Euler matrix over `ℝ` is `[2]`. -/
@[simp] theorem extEulerMatrix_eq_two :
    let b := (simpleClassBasis simples Subsingleton.pairwise simples_exhaustive).map
      (finiteModulesExactK0Equiv ℂ).toIntLinearEquiv
    extEulerMatrix (ModuleCat.isFG ℂ) (ModuleCat.isFG ℂ)
      (isExtensionClosed_finiteModules ℂ) (isExtensionClosed_finiteModules ℂ)
      isEulerAdmissibleOn b b = 2 := by
  dsimp only
  ext i j
  rw [extEulerMatrix_of_of (X := simples i) (Y := simples j) (hi := by simp) (hj := by simp)]
  simp [Matrix.ofNat_apply, Subsingleton.elim i j]

/-- The general-field identity specializes to `Cᵀ E = [2] = D`, not `Cᵀ E = I`. -/
theorem cartanMatrix_transpose_mul_extEulerMatrix_eq_diagonal :
    let b := (simpleClassBasis simples Subsingleton.pairwise simples_exhaustive).map
      (finiteModulesExactK0Equiv ℂ).toIntLinearEquiv
    (cartanMatrix projectives simples (fun _ ↦ isIndecomposableModule_self ℂ)
      Subsingleton.pairwise projectives_exhaustive Subsingleton.pairwise simples_exhaustive)ᵀ *
      extEulerMatrix (ModuleCat.isFG ℂ) (ModuleCat.isFG ℂ)
        (isExtensionClosed_finiteModules ℂ) (isExtensionClosed_finiteModules ℂ)
        isEulerAdmissibleOn b b =
      Matrix.diagonal (fun _ : Unit ↦ (Module.finrank ℝ (Module.End ℂ (simples ()).obj) : ℤ)) := by
  dsimp only
  rw [cartanMatrix_eq_one, Matrix.transpose_one, Matrix.one_mul, extEulerMatrix_eq_two, finrank_end]
  ext i j
  simp [Matrix.ofNat_apply, Subsingleton.elim i j]

/-- The raw projective Ext-Euler pairing is not the integral multiplicity pairing for this
nonsplit real algebra. -/
theorem projectiveExtEuler_ne_projectiveSimplePairing :
    projectiveExtEuler ℝ ℂ ≠
      projectiveSimplePairing projectives simples (fun _ ↦ isIndecomposableModule_self ℂ)
        Subsingleton.pairwise projectives_exhaustive Subsingleton.pairwise simples_exhaustive := by
  intro h
  have he := LinearMap.congr_fun₂ h (ExactK0.of (projectives ())) (ExactK0.of (simples ()))
  rw [projectiveExtEuler_of_of, projectiveSimplePairing_eq_one] at he
  rw [finrank_end] at he
  norm_num at he

end TauCeti.RealComplex
