/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.D4.Tripled.TrilinearForm
public import TauCeti.RepresentationTheory.Spin.Triality.Basic

/-!
# The trilinear form on the concrete type-D4 modules

The standard split vector module and the two half-spin modules in four polarization coordinates
carry a distinguished trilinear form. This file transports the integral coordinate form on the
tripled type-`D₄` weight table through the concrete vector and half-spin coordinate equivalences.

The transported form is nonzero, is cyclic under the concrete triality intertwiners, and is
invariant under the diagonal infinitesimal action of every positive, negative, and Cartan
Chevalley generator. The rational construction retains the coordinate form's fixed integral
normalization.

## Main declarations

* `SpinPolarizationData.d4TrialityTrilinearForm`: the bundled trilinear form on the vector,
  odd half-spin, and even half-spin modules.
* `SpinPolarizationData.d4TrialityTrilinearForm_ne_zero`: the transported form is nonzero.
* `SpinPolarizationData.d4TrialityTrilinearForm_cyclic`: the form is preserved by cyclically
  applying the three concrete triality intertwiners.
* The three `d4TrialityTrilinearForm_serreE_invariant`,
  `d4TrialityTrilinearForm_serreF_invariant`, and
  `d4TrialityTrilinearForm_serreH_invariant` theorems: infinitesimal invariance under the
  Chevalley generators.

## References

* J. F. Adams, *Lectures on Exceptional Lie Groups*, Chapter 3.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lecture 20.
-/

open scoped Matrix

public section

namespace TauCeti.SpinPolarizationData

open TauCeti.DynkinType
open TauCeti.D4Tripled

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V] {Q : QuadraticForm ℚ V}
  (P : SpinPolarizationData Q) (b : Module.Basis (Fin 4) ℚ P.W)

/-- The triality trilinear form on the standard split vector module, the odd half-spin module,
and the even half-spin module. -/
noncomputable def d4TrialityTrilinearForm :
    (Fin 4 ⊕ Fin 4 → ℚ) →ₗ[ℚ] spinMinus Q P →ₗ[ℚ] spinPlus Q P →ₗ[ℚ] ℚ :=
  ((trialityTrilinearForm ℚ).compl₁₂ D4Tripled.vectorBlockEquiv.toLinearMap
      (P.d4SpinMinusBlockEquiv b).toLinearMap).compr₂
    (LinearMap.lcomp ℚ ℚ (P.d4SpinPlusBlockEquiv b).toLinearMap)

/-- The concrete triality form is the coordinate form evaluated after the vector and half-spin
comparison equivalences. -/
@[simp]
theorem d4TrialityTrilinearForm_apply (v : Fin 4 ⊕ Fin 4 → ℚ)
    (x : spinMinus Q P) (y : spinPlus Q P) :
    P.d4TrialityTrilinearForm b v x y =
      trialityTrilinearForm ℚ (D4Tripled.vectorBlockEquiv v)
        (P.d4SpinMinusBlockEquiv b x) (P.d4SpinPlusBlockEquiv b y) := by
  rfl

/-- The concrete triality trilinear form is nonzero. -/
theorem d4TrialityTrilinearForm_ne_zero : P.d4TrialityTrilinearForm b ≠ 0 := by
  intro h
  apply trialityTrilinearForm_ne_zero ℚ
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  have hEval := congrArg
    (fun f => f (D4Tripled.vectorBlockEquiv.symm v)
      ((P.d4SpinMinusBlockEquiv b).symm x)
      ((P.d4SpinPlusBlockEquiv b).symm y)) h
  simpa only [d4TrialityTrilinearForm_apply, LinearEquiv.apply_symm_apply,
    LinearMap.zero_apply] using hEval

/-- The concrete triality form is preserved when the vector and half-spin modules are rotated
by their triality intertwiners. -/
theorem d4TrialityTrilinearForm_cyclic (v : Fin 4 ⊕ Fin 4 → ℚ)
    (x : spinMinus Q P) (y : spinPlus Q P) :
    P.d4TrialityTrilinearForm b v x y =
      P.d4TrialityTrilinearForm b
        (P.d4SpinPlusToVectorEquiv b y)
        (P.d4VectorToSpinMinusEquiv b v)
        (P.d4SpinMinusToSpinPlusEquiv b x) := by
  rw [d4TrialityTrilinearForm_apply, d4TrialityTrilinearForm_apply,
    trialityTrilinearForm_cyclic]
  simp only [vectorBlockEquiv_d4SpinPlusToVectorEquiv,
    d4SpinMinusBlockEquiv_d4VectorToSpinMinusEquiv,
    d4SpinPlusBlockEquiv_d4SpinMinusToSpinPlusEquiv,
    d4BlockTwoToZeroEquiv_apply, d4BlockZeroToOneEquiv_apply,
    d4BlockOneToTwoEquiv_apply]

/-- The concrete triality form is invariant under the diagonal action of every positive
Chevalley generator. -/
theorem d4TrialityTrilinearForm_serreE_invariant (hline : P.line = ⊥) (i : Fin 4)
    (v : Fin 4 ⊕ Fin 4 → ℚ) (x : spinMinus Q P) (y : spinPlus Q P) :
    P.d4TrialityTrilinearForm b
          (TypeDStd.raisingMatrix (K := ℚ) 4 (by omega) i *ᵥ v) x y +
        P.d4TrialityTrilinearForm b v
          (P.typeDSpinMinusLieRep b hline
            (TypeDStd.rootGenerator 4 (by omega) (.inl i)) x) y +
      P.d4TrialityTrilinearForm b v x
        (P.typeDSpinPlusLieRep b hline
          (TypeDStd.rootGenerator 4 (by omega) (.inl i)) y) = 0 := by
  simp only [d4TrialityTrilinearForm_apply, D4Tripled.vectorBlockEquiv_raising_mulVec,
    d4SpinMinusBlockEquiv_serreE, d4SpinPlusBlockEquiv_serreE]
  erw [← blockRaisingMatrix_eq_submatrixQ 1 i,
    ← blockRaisingMatrix_eq_submatrixQ 2 i]
  exact trialityTrilinearForm_raising_invariant ℚ i
    (D4Tripled.vectorBlockEquiv v) (P.d4SpinMinusBlockEquiv b x)
      (P.d4SpinPlusBlockEquiv b y)

/-- The concrete triality form is invariant under the diagonal action of every negative
Chevalley generator. -/
theorem d4TrialityTrilinearForm_serreF_invariant (hline : P.line = ⊥) (i : Fin 4)
    (v : Fin 4 ⊕ Fin 4 → ℚ) (x : spinMinus Q P) (y : spinPlus Q P) :
    P.d4TrialityTrilinearForm b
          (TypeDStd.loweringMatrix (K := ℚ) 4 (by omega) i *ᵥ v) x y +
        P.d4TrialityTrilinearForm b v
          (P.typeDSpinMinusLieRep b hline
            (TypeDStd.rootGenerator 4 (by omega) (.inr i)) x) y +
      P.d4TrialityTrilinearForm b v x
        (P.typeDSpinPlusLieRep b hline
          (TypeDStd.rootGenerator 4 (by omega) (.inr i)) y) = 0 := by
  simp only [d4TrialityTrilinearForm_apply, D4Tripled.vectorBlockEquiv_lowering_mulVec,
    d4SpinMinusBlockEquiv_serreF, d4SpinPlusBlockEquiv_serreF]
  erw [← blockLoweringMatrix_eq_submatrixQ 1 i,
    ← blockLoweringMatrix_eq_submatrixQ 2 i]
  exact trialityTrilinearForm_lowering_invariant ℚ i
    (D4Tripled.vectorBlockEquiv v) (P.d4SpinMinusBlockEquiv b x)
      (P.d4SpinPlusBlockEquiv b y)

/-- The concrete triality form is invariant under the diagonal action of every Cartan
Chevalley generator. -/
theorem d4TrialityTrilinearForm_serreH_invariant (hline : P.line = ⊥) (i : Fin 4)
    (v : Fin 4 ⊕ Fin 4 → ℚ) (x : spinMinus Q P) (y : spinPlus Q P) :
    P.d4TrialityTrilinearForm b
          (typeDDiagonalMatrix (fun j =>
            (typeDSimpleRoot 4 (by omega) i j : ℚ)) *ᵥ v) x y +
        P.d4TrialityTrilinearForm b v
          (P.typeDSpinMinusLieRep b hline
            (TypeDStd.cartanGenerator 4 (by omega) i) x) y +
      P.d4TrialityTrilinearForm b v x
        (P.typeDSpinPlusLieRep b hline
          (TypeDStd.cartanGenerator 4 (by omega) i) y) = 0 := by
  simp only [d4TrialityTrilinearForm_apply,
    D4Tripled.vectorBlockEquiv_cartanGenerator_mulVec,
    d4SpinMinusBlockEquiv_serreH, d4SpinPlusBlockEquiv_serreH]
  erw [← blockCartanGeneratorMatrix_eq_submatrixQ 1 i,
    ← blockCartanGeneratorMatrix_eq_submatrixQ 2 i]
  exact trialityTrilinearForm_cartan_invariant ℚ i
    (D4Tripled.vectorBlockEquiv v) (P.d4SpinMinusBlockEquiv b x)
      (P.d4SpinPlusBlockEquiv b y)

end TauCeti.SpinPolarizationData
