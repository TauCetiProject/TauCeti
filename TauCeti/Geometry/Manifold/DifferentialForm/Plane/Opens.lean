/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Plane.Complex
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.DifferentialForm.Closed
import TauCeti.Geometry.Manifold.DifferentialForm.Opens.ModelSpace
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz
import TauCeti.LinearAlgebra.Determinant.Basic

/-!
# Planar differential calculus on open subsets of `ℂ`

This file develops the coordinate calculus for differential forms on an arbitrary open subset
`U : TopologicalSpace.Opens ℂ`:

* **Pulled-back coordinate one-forms** (`TauCeti.mpullback_subtype_val_complexDx_eq_mextDeriv`,
  `TauCeti.mpullback_subtype_val_complexDy_eq_mextDeriv`,
  `TauCeti.mpullback_subtype_val_complexDz_eq_mextDeriv`,
  `TauCeti.mpullback_subtype_val_complexDzBar_eq_mextDeriv`, and their closedness
  `TauCeti.mextDeriv_mpullback_subtype_val_complex*`): restrictions of `dx, dy, dz, dbar z` to `U`
  are closed and equal the exterior derivatives of the restricted coordinate functions.
* **Coordinate differential decompositions** (`TauCeti.mextDeriv_ofFunction_opens_complex_real_eq`,
  `TauCeti.mextDeriv_ofFunction_opens_complex_eq_wirtinger`): for any function on `U` with an
  ambient representative, its exterior derivative decomposes along `dx, dy` and along `dz, dbar z`
  without regularity assumptions.
* **Canonical two-form coefficient** (`TauCeti.planarTwoFormCoeff`): every two-form `η` on `U` is
  uniquely determined by its evaluation on the positive frame `(1, i)`
  (`TauCeti.roughForm_two_eq_wedgeWith_complexDx_wedge_complexDy`,
  `TauCeti.roughForm_two_eq_wedgeWith_complexDz_wedgeWith_complexDzBar`,
  `TauCeti.planarTwoFormCoeff_injective`), and a `2`-form is `C^n` if and only if its coefficient
  is `C^n` (`TauCeti.IsSmoothForm.contMDiff_planarTwoFormCoeff`,
  `TauCeti.isSmoothForm_iff_contMDiff_planarTwoFormCoeff`).
* **Exterior derivatives of planar one-forms**
  (`TauCeti.planarTwoFormCoeff_mextDeriv_wedgeWith_complexDz`,
  `TauCeti.planarTwoFormCoeff_mextDeriv_wedgeWith_complexDzBar`,
  `TauCeti.planarTwoFormCoeff_mextDeriv_wedgeWith_complexDx_add_complexDy`): explicit coordinate
  formulas for `d(g dz)`, `d(f dbar z)`, and `d(a dx + b dy)` in terms of Wirtinger and real
  partial derivatives.

## References

* A. Rainer, *Advanced Complex Analysis*, §10 and Theorem 12.2.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Chapter I.
-/

public noncomputable section

open Complex Set TopologicalSpace
open scoped ContDiff Manifold ComplexConjugate Topology

namespace TauCeti

/-! ### Coordinate one-forms pulled back to an open subset `U ⊆ ℂ` -/

section OpenCoords

variable (U : Opens ℂ)

/-- On an open subset `U ⊆ ℂ`, the pullback of `dx` is `d(Re ∘ ι)`. -/
theorem mpullback_subtype_val_complexDx_eq_mextDeriv :
    mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) SmoothForm.complexDx.val =
      mextDeriv (RoughForm.ofFunction 𝓘(ℝ, ℂ) fun z : U ↦ (z : ℂ).re) := by
  rw [SmoothForm.complexDx_eq_mextDeriv]
  exact mpullback_mextDeriv_ofFunction
    (contMDiff_subtypeVal.mdifferentiable one_ne_zero)
    ((contMDiff_iff_contDiff.2 (Complex.reCLM.contDiff (n := 1))).mdifferentiable one_ne_zero)

/-- On an open subset `U ⊆ ℂ`, the pullback of `dy` is `d(Im ∘ ι)`. -/
theorem mpullback_subtype_val_complexDy_eq_mextDeriv :
    mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) SmoothForm.complexDy.val =
      mextDeriv (RoughForm.ofFunction 𝓘(ℝ, ℂ) fun z : U ↦ (z : ℂ).im) := by
  rw [SmoothForm.complexDy_eq_mextDeriv]
  exact mpullback_mextDeriv_ofFunction
    (contMDiff_subtypeVal.mdifferentiable one_ne_zero)
    ((contMDiff_iff_contDiff.2 (Complex.imCLM.contDiff (n := 1))).mdifferentiable one_ne_zero)

/-- On an open subset `U ⊆ ℂ`, the pullback of `dz` is `d ι`. -/
theorem mpullback_subtype_val_complexDz_eq_mextDeriv :
    mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) SmoothForm.complexDz.val =
      mextDeriv (RoughForm.ofFunction 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)) := by
  rw [SmoothForm.complexDz_eq_mextDeriv]
  exact mpullback_mextDeriv_ofFunction
    (contMDiff_subtypeVal.mdifferentiable one_ne_zero) mdifferentiable_id

/-- On an open subset `U ⊆ ℂ`, the pullback of `dbar z` is `d(conj ∘ ι)`. -/
theorem mpullback_subtype_val_complexDzBar_eq_mextDeriv :
    mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) SmoothForm.complexDzBar.val =
      mextDeriv (RoughForm.ofFunction 𝓘(ℝ, ℂ) fun z : U ↦ conj (z : ℂ)) := by
  rw [SmoothForm.complexDzBar_eq_mextDeriv]
  exact mpullback_mextDeriv_ofFunction
    (contMDiff_subtypeVal.mdifferentiable one_ne_zero)
    ((contMDiff_iff_contDiff.2
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff (n := 1))).mdifferentiable one_ne_zero)

/-- On an open subset `U ⊆ ℂ`, the pullback of `dx` is closed. -/
@[simp]
theorem mextDeriv_mpullback_subtype_val_complexDx :
    mextDeriv (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) SmoothForm.complexDx.val) =
      0 :=
  (SmoothForm.complexDx.isSmoothForm.of_le (by simp)).mextDeriv_mpullback_eq_zero
    SmoothForm.mextDeriv_complexDx contMDiff_subtypeVal

/-- On an open subset `U ⊆ ℂ`, the pullback of `dy` is closed. -/
@[simp]
theorem mextDeriv_mpullback_subtype_val_complexDy :
    mextDeriv (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) SmoothForm.complexDy.val) =
      0 :=
  (SmoothForm.complexDy.isSmoothForm.of_le (by simp)).mextDeriv_mpullback_eq_zero
    SmoothForm.mextDeriv_complexDy contMDiff_subtypeVal

/-- On an open subset `U ⊆ ℂ`, the pullback of `dz` is closed. -/
@[simp]
theorem mextDeriv_mpullback_subtype_val_complexDz :
    mextDeriv (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) SmoothForm.complexDz.val) =
      0 :=
  (SmoothForm.complexDz.isSmoothForm.of_le (by simp)).mextDeriv_mpullback_eq_zero
    SmoothForm.mextDeriv_complexDz contMDiff_subtypeVal

/-- On an open subset `U ⊆ ℂ`, the pullback of `dbar z` is closed. -/
@[simp]
theorem mextDeriv_mpullback_subtype_val_complexDzBar :
    mextDeriv (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) SmoothForm.complexDzBar.val) =
      0 :=
  (SmoothForm.complexDzBar.isSmoothForm.of_le (by simp)).mextDeriv_mpullback_eq_zero
    SmoothForm.mextDeriv_complexDzBar contMDiff_subtypeVal

end OpenCoords

/-! ### Planar frame evaluation helpers -/

section Helpers

private def planarCoordEquiv {U : Opens ℂ} (z : U) : TangentSpace 𝓘(ℝ, ℂ) z ≃L[ℝ] ℂ :=
  (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, ℂ)) z).trans
    (NormedSpace.fromTangentSpace (z : ℂ))

private theorem planarCoordEquiv_apply {U : Opens ℂ} (z : U) (v : TangentSpace 𝓘(ℝ, ℂ) z) :
    planarCoordEquiv z v =
      NormedSpace.fromTangentSpace (z : ℂ) (Manifold.tangentSpaceOpenEquiv z v) :=
  rfl

private theorem planarCoordEquiv_coe {U : Opens ℂ} (z : U) (v : TangentSpace 𝓘(ℝ, ℂ) z) :
    planarCoordEquiv z v = v := by
  rw [planarCoordEquiv_apply, NormedSpace.fromTangentSpace_apply,
    Manifold.tangentSpaceOpenEquiv_apply]

private theorem mpullback_planar_apply {U : Opens ℂ} {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] {k : ℕ}
    (η : RoughForm 𝓘(ℝ, ℂ) ℂ G k) (z : U) (v : Fin k → TangentSpace 𝓘(ℝ, ℂ) z) :
    mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) η z v =
      η (z : ℂ) fun i ↦
        (NormedSpace.fromTangentSpace (z : ℂ)).symm (planarCoordEquiv z (v i)) := by
  rw [mpullback_apply, Manifold.mfderiv_subtype_val]
  congr 1

private theorem wedgeWith_ofFunction_mpullback_apply {U : Opens ℂ} {F₁ F₂ F₃ : Type*}
    [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
    (B : F₁ →L[ℝ] F₂ →L[ℝ] F₃) {k : ℕ}
    (f : U → F₁) (η : RoughForm 𝓘(ℝ, ℂ) ℂ F₂ k)
    (z : U) (v : Fin (0 + k) → TangentSpace 𝓘(ℝ, ℂ) z) :
    RoughForm.wedgeWith B (RoughForm.ofFunction 𝓘(ℝ, ℂ) f)
      (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) η) z v =
      B (f z) (η (z : ℂ) fun i ↦
        (NormedSpace.fromTangentSpace (z : ℂ)).symm
          (planarCoordEquiv z (v (Fin.cast (zero_add k).symm i)))) := by
  rw [RoughForm.wedgeWith_apply_zero_left, RoughForm.ofFunction_apply, mpullback_planar_apply]
  rfl

private theorem flatOneFormEquiv_wedgeWith_ofFunction_mpullback {U : Opens ℂ}
    {F₁ F₂ F₃ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
    (B : F₁ →L[ℝ] F₂ →L[ℝ] F₃) (f : U → F₁)
    (η : RoughForm 𝓘(ℝ, ℂ) ℂ F₂ 1) (z : U) (a : ℂ) :
    RoughForm.flatOneFormEquiv U
      (RoughForm.wedgeWith B (RoughForm.ofFunction 𝓘(ℝ, ℂ) f)
        (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) η)) z a =
      B (f z) (η (z : ℂ) ![(NormedSpace.fromTangentSpace (z : ℂ)).symm a]) := by
  rw [RoughForm.flatOneFormEquiv_apply, wedgeWith_ofFunction_mpullback_apply]
  congr 2
  ext i
  rw [Subsingleton.elim i 0, planarCoordEquiv_coe]
  rfl

end Helpers

/-! ### Differential decompositions on an open subset `U ⊆ ℂ` -/

section Differentials

/-- Real coordinate differential decomposition on an open subset `U ⊆ ℂ`: for any function
`v : U → F` into a real normed space `F` and any ambient representative `v' : ℂ → F` agreeing
with `v` on `U`, `dv = (∂_x v') dx + (∂_y v') dy`. No regularity hypothesis is required for
this identity of totalized derivatives. -/
theorem mextDeriv_ofFunction_opens_complex_real_eq {U : Opens ℂ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {v : U → F} {v' : ℂ → F}
    (hv : ∀ z : U, v' z = v z) :
    mextDeriv (RoughForm.ofFunction 𝓘(ℝ, ℂ) v) =
      RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℝ).flip
          (RoughForm.ofFunction 𝓘(ℝ, ℂ) fun z : U ↦ fderiv ℝ v' z 1)
          (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) SmoothForm.complexDx.val) +
        RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℝ).flip
          (RoughForm.ofFunction 𝓘(ℝ, ℂ) fun z : U ↦ fderiv ℝ v' z Complex.I)
          (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
            SmoothForm.complexDy.val) := by
  have hv' : v = fun z : U ↦ v' z := funext fun z ↦ (hv z).symm
  apply (RoughForm.flatOneFormEquiv U).injective
  ext z a
  rw [hv', RoughForm.flatOneFormEquiv_mextDeriv_ofFunction, map_add, Pi.add_apply,
    add_apply, flatOneFormEquiv_wedgeWith_ofFunction_mpullback,
    flatOneFormEquiv_wedgeWith_ofFunction_mpullback]
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply,
    SmoothForm.complexDx_apply, SmoothForm.complexDy_apply, Matrix.cons_val_zero,
    ContinuousLinearEquiv.apply_symm_apply]
  have ha : a = a.re • (1 : ℂ) + a.im • Complex.I := by simp [Complex.real_smul]
  conv_lhs => rw [ha]
  rw [map_add, map_smul, map_smul]

/-- Complex Wirtinger differential decomposition on an open subset `U ⊆ ℂ`: for any function
`u : U → W` into a complex normed space `W` and any ambient representative `u' : ℂ → W`
agreeing with `u` on `U`, `du = (∂_z u') dz + (\bar∂ u') dbar z`. No regularity hypothesis is
required. -/
theorem mextDeriv_ofFunction_opens_complex_eq_wirtinger {U : Opens ℂ} {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℂ W] {u : U → W} {u' : ℂ → W}
    (hu : ∀ z : U, u' z = u z) :
    mextDeriv (RoughForm.ofFunction 𝓘(ℝ, ℂ) u) =
      RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℂ).flip
          (RoughForm.ofFunction 𝓘(ℝ, ℂ) fun z : U ↦ wirtingerDeriv u' z 1)
          (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
            SmoothForm.complexDz.val) +
        RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℂ).flip
          (RoughForm.ofFunction 𝓘(ℝ, ℂ) fun z : U ↦ conjWirtingerDeriv u' z 1)
          (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
            SmoothForm.complexDzBar.val) := by
  have hu' : u = fun z : U ↦ u' z := funext fun z ↦ (hu z).symm
  apply (RoughForm.flatOneFormEquiv U).injective
  ext z a
  rw [hu', RoughForm.flatOneFormEquiv_mextDeriv_ofFunction, map_add, Pi.add_apply,
    add_apply, flatOneFormEquiv_wedgeWith_ofFunction_mpullback,
    flatOneFormEquiv_wedgeWith_ofFunction_mpullback]
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply,
    SmoothForm.complexDz_apply, SmoothForm.complexDzBar_apply, Matrix.cons_val_zero,
    ContinuousLinearEquiv.apply_symm_apply]
  exact fderiv_apply_eq_smul_wirtingerDeriv_add_smul_conjWirtingerDeriv (f := u') (z : ℂ) a

end Differentials

/-! ### Unique coefficient extraction for planar two-forms -/

section TwoFormCoeff

/-- The canonical `dx ∧ dy` coefficient of a `2`-form `η` on an open subset `U ⊆ ℂ` with values
in a real normed space `F`: the evaluation of `η` at the positive coordinate frame `(1, i)`. -/
def planarTwoFormCoeff {U : Opens ℂ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (η : RoughForm 𝓘(ℝ, ℂ) U F 2) (z : U) : F :=
  η z ![(Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, ℂ)) z).symm
      ((NormedSpace.fromTangentSpace (z : ℂ)).symm 1),
    (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, ℂ)) z).symm
      ((NormedSpace.fromTangentSpace (z : ℂ)).symm Complex.I)]

/-- Evaluating `planarTwoFormCoeff η` at `z : U` applies `η z` to the positive coordinate frame
`(1, i)`. -/
theorem planarTwoFormCoeff_apply {U : Opens ℂ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (η : RoughForm 𝓘(ℝ, ℂ) U F 2) (z : U) :
    planarTwoFormCoeff η z =
      η z ![(Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, ℂ)) z).symm
          ((NormedSpace.fromTangentSpace (z : ℂ)).symm 1),
        (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, ℂ)) z).symm
          ((NormedSpace.fromTangentSpace (z : ℂ)).symm Complex.I)] := by
  rw [planarTwoFormCoeff]

private theorem planarTwoFormCoeff_eq_apply_symm {U : Opens ℂ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (η : RoughForm 𝓘(ℝ, ℂ) U F 2) (z : U) :
    planarTwoFormCoeff η z =
      η z ![(planarCoordEquiv z).symm 1, (planarCoordEquiv z).symm Complex.I] := by
  simp [planarTwoFormCoeff_apply, planarCoordEquiv]

private theorem planarTwoFormCoeff_wedgeWith_ofFunction_mpullback {U : Opens ℂ}
    {F₁ F₂ F₃ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
    (B : F₁ →L[ℝ] F₂ →L[ℝ] F₃) (h : U → F₁)
    (η : RoughForm 𝓘(ℝ, ℂ) ℂ F₂ 2) (z : U) :
    planarTwoFormCoeff
      (RoughForm.wedgeWith B (RoughForm.ofFunction 𝓘(ℝ, ℂ) h)
        (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) η)) z =
      B (h z) (η (z : ℂ)
        ![(NormedSpace.fromTangentSpace (z : ℂ)).symm 1,
          (NormedSpace.fromTangentSpace (z : ℂ)).symm Complex.I]) := by
  rw [planarTwoFormCoeff_eq_apply_symm, wedgeWith_ofFunction_mpullback_apply]
  congr 2
  ext i
  fin_cases i <;> simp [Fin.cast_eq_self]

@[simp]
theorem planarTwoFormCoeff_zero {U : Opens ℂ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (z : U) :
    planarTwoFormCoeff (0 : RoughForm 𝓘(ℝ, ℂ) U F 2) z = 0 := by
  simp [planarTwoFormCoeff_apply]

@[simp]
theorem planarTwoFormCoeff_add {U : Opens ℂ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (η₁ η₂ : RoughForm 𝓘(ℝ, ℂ) U F 2) (z : U) :
    planarTwoFormCoeff (η₁ + η₂) z =
      planarTwoFormCoeff η₁ z + planarTwoFormCoeff η₂ z := by
  simp [planarTwoFormCoeff_apply]

@[simp]
theorem planarTwoFormCoeff_smul {U : Opens ℂ} {R F : Type*} [Semiring R]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Module R F] [SMulCommClass ℝ R F]
    [ContinuousConstSMul R F] (c : R) (η : RoughForm 𝓘(ℝ, ℂ) U F 2) (z : U) :
    planarTwoFormCoeff (c • η) z = c • planarTwoFormCoeff η z := by
  simp [planarTwoFormCoeff_apply]

/-- Mapping coefficients commutes with extracting `planarTwoFormCoeff`. -/
@[simp]
theorem planarTwoFormCoeff_mapCoeff {U : Opens ℂ} {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) (η : RoughForm 𝓘(ℝ, ℂ) U F 2) (z : U) :
    planarTwoFormCoeff (RoughForm.mapCoeff L η) z = L (planarTwoFormCoeff η z) := by
  simp [planarTwoFormCoeff_apply]

/-- Evaluating `(h dx ∧ dy)` at the positive coordinate frame recovers `h`. -/
@[simp]
theorem planarTwoFormCoeff_wedgeWith_complexDx_wedge_complexDy {U : Opens ℂ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (h : U → F) (z : U) :
    planarTwoFormCoeff
      (RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℝ).flip
        (RoughForm.ofFunction 𝓘(ℝ, ℂ) h)
        (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
          (RoughForm.wedge SmoothForm.complexDx.val SmoothForm.complexDy.val))) z = h z := by
  rw [planarTwoFormCoeff_wedgeWith_ofFunction_mpullback]
  simp

/-- Every alternating two-form on `U ⊆ ℂ` with values in a real normed space `F` equals
`(planarTwoFormCoeff η) dx ∧ dy`. -/
theorem roughForm_two_eq_wedgeWith_complexDx_wedge_complexDy {U : Opens ℂ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (η : RoughForm 𝓘(ℝ, ℂ) U F 2) :
    η = RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℝ).flip
      (RoughForm.ofFunction 𝓘(ℝ, ℂ) (planarTwoFormCoeff η))
      (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
        (RoughForm.wedge SmoothForm.complexDx.val SmoothForm.complexDy.val)) := by
  funext z
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  let b : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) z) :=
    Complex.basisOneI.map (planarCoordEquiv z).symm.toLinearEquiv
  rw [AlternatingMap.eq_basis_det_smulRight b (η z).toAlternatingMap,
    AlternatingMap.eq_basis_det_smulRight b
      (RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℝ).flip
        (RoughForm.ofFunction 𝓘(ℝ, ℂ) (planarTwoFormCoeff η))
        (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
          (RoughForm.wedge SmoothForm.complexDx.val SmoothForm.complexDy.val)) z).toAlternatingMap]
  congr 1
  have hb : (⇑b : Fin 2 → TangentSpace 𝓘(ℝ, ℂ) z) =
      ![(planarCoordEquiv z).symm 1, (planarCoordEquiv z).symm Complex.I] := by
    ext i
    fin_cases i <;> simp [b]
  change (η z) ⇑b = _
  rw [hb, ← planarTwoFormCoeff_eq_apply_symm]
  exact (planarTwoFormCoeff_wedgeWith_complexDx_wedge_complexDy (planarTwoFormCoeff η) z).symm

/-- Two planar `2`-forms on `U ⊆ ℂ` agree iff their `dx ∧ dy` coefficients agree. -/
theorem planarTwoFormCoeff_injective {U : Opens ℂ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    Function.Injective (planarTwoFormCoeff (U := U) (F := F)) := by
  intro η₁ η₂ h
  rw [roughForm_two_eq_wedgeWith_complexDx_wedge_complexDy η₁,
    roughForm_two_eq_wedgeWith_complexDx_wedge_complexDy η₂, h]

/-- Evaluating `(h dz ∧ dbar z)` at the positive coordinate frame gives `-2i • h`. -/
@[simp]
theorem planarTwoFormCoeff_wedgeWith_complexDz_wedgeWith_complexDzBar {U : Opens ℂ} {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℂ W] (h : U → W) (z : U) :
    planarTwoFormCoeff
      (RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℂ).flip
        (RoughForm.ofFunction 𝓘(ℝ, ℂ) h)
        (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
          (RoughForm.wedgeWith (ContinuousLinearMap.mul ℝ ℂ)
            SmoothForm.complexDz.val SmoothForm.complexDzBar.val))) z = (-2 * Complex.I) • h z := by
  rw [planarTwoFormCoeff_wedgeWith_ofFunction_mpullback]
  simp [SmoothForm.complexDz_wedgeWith_complexDzBar_apply]

/-- Every alternating two-form on `U ⊆ ℂ` with values in a complex normed space `W` equals
`((-2i)⁻¹ • planarTwoFormCoeff η) dz ∧ dbar z`. -/
theorem roughForm_two_eq_wedgeWith_complexDz_wedgeWith_complexDzBar {U : Opens ℂ} {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℂ W] (η : RoughForm 𝓘(ℝ, ℂ) U W 2) :
    η = RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℂ).flip
      (RoughForm.ofFunction 𝓘(ℝ, ℂ) fun z : U ↦
        (-2 * Complex.I)⁻¹ • planarTwoFormCoeff η z)
      (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
        (RoughForm.wedgeWith (ContinuousLinearMap.mul ℝ ℂ)
          SmoothForm.complexDz.val SmoothForm.complexDzBar.val)) := by
  apply planarTwoFormCoeff_injective
  funext z
  rw [planarTwoFormCoeff_wedgeWith_complexDz_wedgeWith_complexDzBar, smul_smul,
    mul_inv_cancel₀ (by simp [Complex.I_ne_zero]), one_smul]

/-- A `C^n` planar `2`-form on an open subset `U ⊆ ℂ` has a `C^n` coefficient function. -/
theorem IsSmoothForm.contMDiff_planarTwoFormCoeff {U : Opens ℂ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {n : WithTop ℕ∞}
    {η : RoughForm 𝓘(ℝ, ℂ) U F 2} (hη : IsSmoothForm 𝓘(ℝ, ℂ) n η) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, F) n (planarTwoFormCoeff η) := by
  obtain ⟨η₀, hη₀, heq⟩ := hη.exists_contDiffOn_opens
  have hcomp : ContDiffOn ℝ n
      (fun z : ℂ ↦ ContinuousAlternatingMap.apply ℝ ℂ F (![1, Complex.I] : Fin 2 → ℂ) (η₀ z))
      (U : Set ℂ) :=
    (ContinuousAlternatingMap.apply ℝ ℂ F (![1, Complex.I] : Fin 2 → ℂ)).contDiff.comp_contDiffOn
      hη₀
  have hfn : (fun z : ℂ ↦ ContinuousAlternatingMap.apply ℝ ℂ F
      (![1, Complex.I] : Fin 2 → ℂ) (η₀ z)) ∘ (Subtype.val : U → ℂ) = planarTwoFormCoeff η := by
    funext z
    rw [Function.comp_apply, ContinuousAlternatingMap.apply_apply, planarTwoFormCoeff_eq_apply_symm,
      heq z]
    have hpt (a : ℂ) : (planarCoordEquiv z).symm a = (a : TangentSpace 𝓘(ℝ, ℂ) z) := by
      apply (planarCoordEquiv z).injective
      rw [ContinuousLinearEquiv.apply_symm_apply]
      exact (planarCoordEquiv_coe z a).symm
    congr 1
    ext i
    fin_cases i <;> exact (hpt _).symm
  exact hfn ▸ hcomp.contMDiff_comp_subtypeVal

/-- A planar `2`-form on an open subset `U ⊆ ℂ` is `C^n` if and only if its canonical `dx ∧ dy`
coefficient is `C^n`. -/
theorem isSmoothForm_iff_contMDiff_planarTwoFormCoeff {U : Opens ℂ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {n : WithTop ℕ∞}
    {η : RoughForm 𝓘(ℝ, ℂ) U F 2} :
    IsSmoothForm 𝓘(ℝ, ℂ) n η ↔ ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, F) n (planarTwoFormCoeff η) := by
  refine ⟨fun hη ↦ hη.contMDiff_planarTwoFormCoeff, fun hcoeff ↦ ?_⟩
  rw [roughForm_two_eq_wedgeWith_complexDx_wedge_complexDy η]
  refine (isSmoothForm_ofFunction_iff.2 hcoeff).wedgeWith _ ?_
  let η₀ : ℂ [⋀^Fin 2]→L[ℝ] ℝ :=
    ContinuousAlternatingMap.pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
      (ContinuousLinearMap.mul ℝ ℝ).continuous₂
      (ContinuousAlternatingMap.ofSubsingleton ℝ ℂ ℝ (0 : Fin 1) Complex.reCLM)
      (ContinuousAlternatingMap.ofSubsingleton ℝ ℂ ℝ (0 : Fin 1) Complex.imCLM)
  refine (isSmoothForm_opens_iff (ω₀ := fun _ ↦ η₀) fun z ↦ ?_).2 contDiffOn_const
  ext v
  have hv : v = ![v 0, v 1] := funext fun i ↦ by fin_cases i <;> rfl
  rw [hv]
  have lhs_eq : mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
      (RoughForm.wedge SmoothForm.complexDx.val SmoothForm.complexDy.val) z ![v 0, v 1] =
      (planarCoordEquiv z (v 0)).re * (planarCoordEquiv z (v 1)).im -
        (planarCoordEquiv z (v 1)).re * (planarCoordEquiv z (v 0)).im := by
    rw [mpullback_planar_apply]
    have h01 : (fun i ↦ (NormedSpace.fromTangentSpace (𝕜 := ℝ) (z : ℂ)).symm
          (planarCoordEquiv z (![v 0, v 1] i))) =
        ![(NormedSpace.fromTangentSpace (𝕜 := ℝ) (z : ℂ)).symm (planarCoordEquiv z (v 0)),
          (NormedSpace.fromTangentSpace (𝕜 := ℝ) (z : ℂ)).symm (planarCoordEquiv z (v 1))] := by
      ext i; fin_cases i <;> rfl
    rw [h01, SmoothForm.complexDx_wedge_complexDy_apply,
      ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
  have hw : (![v 0, v 1] : Fin 2 → ℂ) =
      ![planarCoordEquiv z (v 0), planarCoordEquiv z (v 1)] := by
    ext i; fin_cases i <;> exact (planarCoordEquiv_coe z _).symm
  have rhs_eq : η₀ ![v 0, v 1] =
      (planarCoordEquiv z (v 0)).re * (planarCoordEquiv z (v 1)).im -
        (planarCoordEquiv z (v 1)).re * (planarCoordEquiv z (v 0)).im := by
    rw [hw, ContinuousAlternatingMap.pairedWedge_apply_one_one]
    simp only [ContinuousLinearMap.mul_apply',
      ContinuousAlternatingMap.ofSubsingleton_apply_apply, Matrix.cons_val_zero,
      Complex.reCLM_apply, Complex.imCLM_apply]
  exact lhs_eq.trans rhs_eq.symm

end TwoFormCoeff

/-! ### Exterior derivatives of planar one-forms -/

section OneFormDeriv

private theorem planarTwoFormCoeff_mextDeriv_wedgeWith_of_isClosed {U : Opens ℂ}
    {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (B : F →L[ℝ] G →L[ℝ] H) {f : U → F} {f' : ℂ → F} (hf_eq : ∀ y : U, f' y = f y)
    {z : U} (hf : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, F) f z)
    {α : SmoothForm 𝓘(ℝ, ℂ) ℂ G 1} (hα : α.IsClosed) :
    planarTwoFormCoeff
      (mextDeriv (RoughForm.wedgeWith B (RoughForm.ofFunction 𝓘(ℝ, ℂ) f)
        (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) α.val))) z =
      B (fderiv ℝ f' z 1)
          (α.val (z : ℂ) ![(NormedSpace.fromTangentSpace (z : ℂ)).symm Complex.I]) -
        B (fderiv ℝ f' z Complex.I)
          (α.val (z : ℂ) ![(NormedSpace.fromTangentSpace (z : ℂ)).symm 1]) := by
  let αU : SmoothForm 𝓘(ℝ, ℂ) U G 1 :=
    SmoothForm.mpullback (Subtype.val : U → ℂ) contMDiff_subtypeVal α
  have hαU : mextDeriv αU.val = 0 := (SmoothForm.isClosed_def _).1 (hα.mpullback _ _)
  rw [← SmoothForm.coe_mpullback (Subtype.val : U → ℂ) contMDiff_subtypeVal α,
    planarTwoFormCoeff_eq_apply_symm,
    mextDeriv_wedgeWith B (mdifferentiableAt_ofFunction hf) (αU.mdifferentiableAt z),
    hαU, RoughForm.wedgeWith_zero_right]
  simp only [Pi.zero_apply, ContinuousAlternatingMap.coe_zero, smul_zero, add_zero,
    Function.comp_def, Fin.cast_eq_self, RoughForm.wedgeWith_apply_one_one,
    mextDeriv_ofFunction_apply, ← mvfderiv_apply_eq_mfderiv_apply,
    Manifold.mvfderiv_opens_eq_fderiv_apply hf_eq, ← planarCoordEquiv_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  rw [SmoothForm.coe_mpullback, mpullback_planar_apply, mpullback_planar_apply]
  congr 2 <;> congr 1 <;> ext i <;> rw [Subsingleton.elim i 0] <;>
    simp only [Matrix.cons_val_zero, ContinuousLinearEquiv.apply_symm_apply]

/-- For a differentiable function `g : U → W` into a complex normed space `W` with ambient
representative `g' : ℂ → W`, the `dx ∧ dy` coefficient of `d(g dz)` at `z` is
`2i • \bar∂ g'(z)`. -/
theorem planarTwoFormCoeff_mextDeriv_wedgeWith_complexDz {U : Opens ℂ} {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℂ W] {g : U → W} {g' : ℂ → W}
    (hg_eq : ∀ z : U, g' z = g z) {z : U}
    (hg : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, W) g z) :
    planarTwoFormCoeff
      (mextDeriv (RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℂ).flip
        (RoughForm.ofFunction 𝓘(ℝ, ℂ) g)
        (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
          SmoothForm.complexDz.val))) z =
      (2 * Complex.I) • conjWirtingerDeriv g' z 1 := by
  rw [planarTwoFormCoeff_mextDeriv_wedgeWith_of_isClosed _ hg_eq hg
    ((SmoothForm.isClosed_def _).2 SmoothForm.mextDeriv_complexDz)]
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply,
    SmoothForm.complexDz_apply, Matrix.cons_val_zero, ContinuousLinearEquiv.apply_symm_apply,
    conjWirtingerDeriv_apply, smul_smul, smul_add, smul_eq_mul, mul_one]
  have h1 : 2 * Complex.I * ((2 : ℂ)⁻¹ * Complex.I) = -1 := by
    calc 2 * Complex.I * ((2 : ℂ)⁻¹ * Complex.I)
        = Complex.I * Complex.I := by ring
      _ = -1 := Complex.I_mul_I
  have h2 : (2 : ℂ) * Complex.I * (2 : ℂ)⁻¹ = Complex.I := by ring
  rw [h1, h2, neg_one_smul, one_smul, sub_eq_add_neg]

/-- For a differentiable function `f : U → W` into a complex normed space `W` with ambient
representative `f' : ℂ → W`, the `dx ∧ dy` coefficient of `d(f dbar z)` at `z` is
`-2i • ∂_z f'(z)`. -/
theorem planarTwoFormCoeff_mextDeriv_wedgeWith_complexDzBar {U : Opens ℂ} {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℂ W] {f : U → W} {f' : ℂ → W}
    (hf_eq : ∀ z : U, f' z = f z) {z : U}
    (hf : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, W) f z) :
    planarTwoFormCoeff
      (mextDeriv (RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℂ).flip
        (RoughForm.ofFunction 𝓘(ℝ, ℂ) f)
        (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
          SmoothForm.complexDzBar.val))) z =
      (-2 * Complex.I) • wirtingerDeriv f' z 1 := by
  rw [planarTwoFormCoeff_mextDeriv_wedgeWith_of_isClosed _ hf_eq hf
    ((SmoothForm.isClosed_def _).2 SmoothForm.mextDeriv_complexDzBar)]
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply,
    SmoothForm.complexDzBar_apply, Matrix.cons_val_zero, ContinuousLinearEquiv.apply_symm_apply,
    conj_I, (starRingEnd ℂ).map_one, wirtingerDeriv_apply, smul_smul, smul_sub, smul_eq_mul,
    mul_one]
  have h1 : -2 * Complex.I * ((2 : ℂ)⁻¹ * Complex.I) = 1 := by
    calc -2 * Complex.I * ((2 : ℂ)⁻¹ * Complex.I)
        = -(Complex.I * Complex.I) := by ring
      _ = 1 := by rw [Complex.I_mul_I, neg_neg]
  have h2 : (-2 : ℂ) * Complex.I * (2 : ℂ)⁻¹ = -Complex.I := by ring
  rw [h1, h2, one_smul]

/-- For differentiable functions `a, b : U → F` into a real normed space `F` with ambient
representatives `a', b' : ℂ → F`, the `dx ∧ dy` coefficient of `d(a dx + b dy)` at `z` is
`∂_x b'(z) - ∂_y a'(z)`. -/
theorem planarTwoFormCoeff_mextDeriv_wedgeWith_complexDx_add_complexDy {U : Opens ℂ}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : U → F} {a' b' : ℂ → F}
    (ha_eq : ∀ z : U, a' z = a z) (hb_eq : ∀ z : U, b' z = b z)
    {z : U} (ha : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, F) a z)
    (hb : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, F) b z) :
    planarTwoFormCoeff
      (mextDeriv
        (RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℝ).flip
            (RoughForm.ofFunction 𝓘(ℝ, ℂ) a)
            (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
              SmoothForm.complexDx.val) +
          RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℝ).flip
            (RoughForm.ofFunction 𝓘(ℝ, ℂ) b)
            (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
              SmoothForm.complexDy.val))) z =
      fderiv ℝ b' z 1 - fderiv ℝ a' z Complex.I := by
  have hdx := (SmoothForm.mpullback (Subtype.val : U → ℂ) contMDiff_subtypeVal
    SmoothForm.complexDx).mdifferentiableAt z
  have hdy := (SmoothForm.mpullback (Subtype.val : U → ℂ) contMDiff_subtypeVal
    SmoothForm.complexDy).mdifferentiableAt z
  have ha' := RoughForm.differentiableWithinAt_range_inChartAt_of_mdifferentiableAt
    (RoughForm.ofFunction 𝓘(ℝ, ℂ) a) (mdifferentiableAt_ofFunction ha)
  have hb' := RoughForm.differentiableWithinAt_range_inChartAt_of_mdifferentiableAt
    (RoughForm.ofFunction 𝓘(ℝ, ℂ) b) (mdifferentiableAt_ofFunction hb)
  have hsum :
      mextDeriv
          (RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℝ).flip
              (RoughForm.ofFunction 𝓘(ℝ, ℂ) a)
              (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
                SmoothForm.complexDx.val) +
            RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℝ).flip
              (RoughForm.ofFunction 𝓘(ℝ, ℂ) b)
              (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
                SmoothForm.complexDy.val)) z =
        mextDeriv
            (RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℝ).flip
              (RoughForm.ofFunction 𝓘(ℝ, ℂ) a)
              (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
                SmoothForm.complexDx.val)) z +
          mextDeriv
            (RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℝ).flip
              (RoughForm.ofFunction 𝓘(ℝ, ℂ) b)
              (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
                SmoothForm.complexDy.val)) z := by
    rw [← SmoothForm.coe_mpullback (Subtype.val : U → ℂ) contMDiff_subtypeVal SmoothForm.complexDx,
      ← SmoothForm.coe_mpullback (Subtype.val : U → ℂ) contMDiff_subtypeVal SmoothForm.complexDy]
    exact mextDeriv_add
      (RoughForm.differentiableWithinAt_inChartAt_wedgeWith _ ha'
        (RoughForm.differentiableWithinAt_range_inChartAt_of_mdifferentiableAt _ hdx))
      (RoughForm.differentiableWithinAt_inChartAt_wedgeWith _ hb'
        (RoughForm.differentiableWithinAt_range_inChartAt_of_mdifferentiableAt _ hdy))
  rw [planarTwoFormCoeff_apply, hsum, ContinuousAlternatingMap.add_apply,
    ← planarTwoFormCoeff_apply, ← planarTwoFormCoeff_apply,
    planarTwoFormCoeff_mextDeriv_wedgeWith_of_isClosed _ ha_eq ha
      ((SmoothForm.isClosed_def _).2 SmoothForm.mextDeriv_complexDx),
    planarTwoFormCoeff_mextDeriv_wedgeWith_of_isClosed _ hb_eq hb
      ((SmoothForm.isClosed_def _).2 SmoothForm.mextDeriv_complexDy)]
  simp [sub_eq_add_neg, add_comm]

end OneFormDeriv

end TauCeti
