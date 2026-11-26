/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Plane.Complex
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Analysis.Complex.OperatorNorm
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.DifferentialForm.Closed
import TauCeti.Geometry.Manifold.DifferentialForm.Opens.ModelSpace
import TauCeti.Geometry.Manifold.DifferentialForm.Opens.Wedge
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz
import TauCeti.LinearAlgebra.Determinant.Basic

/-!
# Planar differential calculus on open subsets of `ℂ`

This file develops the coordinate calculus for differential forms on an arbitrary open subset
`U : TopologicalSpace.Opens ℂ`:

* **Pulled-back coordinate one-forms** (`TauCeti.mpullback_subtype_val_complexDx_eq_mextDeriv`,
  `TauCeti.mpullback_subtype_val_complexDy_eq_mextDeriv`,
  `TauCeti.mpullback_subtype_val_complexDz_eq_mextDeriv`,
  `TauCeti.mpullback_subtype_val_complexDzBar_eq_mextDeriv`, their closedness
  `TauCeti.mextDeriv_mpullback_subtype_val_complex*`, and regularity of planar `(1, 0)`/`(0, 1)`
  forms `TauCeti.isSmoothForm_wedgeWith_ofFunction_mpullback_complexDz`,
  `TauCeti.isSmoothForm_wedgeWith_ofFunction_mpullback_complexDzBar`): restrictions of
  `dx, dy, dz, dbar z` to `U` are closed and equal the exterior derivatives of the restricted
  coordinate functions.
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

/-- On an open subset `U ⊆ ℂ`, `g dz` is `C^n` whenever `g` is `C^n`. -/
theorem isSmoothForm_wedgeWith_ofFunction_mpullback_complexDz {U : Opens ℂ} {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℂ W] {n : WithTop ℕ∞} {g : U → W}
    (hg : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, W) n g) :
    IsSmoothForm 𝓘(ℝ, ℂ) n
      (RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℂ).flip
        (RoughForm.ofFunction 𝓘(ℝ, ℂ) g)
        (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) SmoothForm.complexDz.val)) :=
  (isSmoothForm_ofFunction_iff.2 hg).wedgeWith _
    ((SmoothForm.complexDz_eq_const ▸ SmoothForm.isSmoothForm_const _ n).mpullback
      contMDiff_subtypeVal)

/-- On an open subset `U ⊆ ℂ`, `f dbar z` is `C^n` whenever `f` is `C^n`. -/
theorem isSmoothForm_wedgeWith_ofFunction_mpullback_complexDzBar {U : Opens ℂ} {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℂ W] {n : WithTop ℕ∞} {f : U → W}
    (hf : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, W) n f) :
    IsSmoothForm 𝓘(ℝ, ℂ) n
      (RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℂ).flip
        (RoughForm.ofFunction 𝓘(ℝ, ℂ) f)
        (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) SmoothForm.complexDzBar.val)) :=
  (isSmoothForm_ofFunction_iff.2 hf).wedgeWith _
    ((SmoothForm.complexDzBar_eq_const ▸ SmoothForm.isSmoothForm_const _ n).mpullback
      contMDiff_subtypeVal)

end OpenCoords

/-! ### Planar frame evaluation helpers -/

section Helpers

private def planarCoordEquiv {U : Opens ℂ} (z : U) : TangentSpace 𝓘(ℝ, ℂ) z ≃L[ℝ] ℂ :=
  (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, ℂ)) z).trans
    (NormedSpace.fromTangentSpace (z : ℂ))

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
    add_apply, RoughForm.flatOneFormEquiv_wedgeWith_ofFunction_mpullback,
    RoughForm.flatOneFormEquiv_wedgeWith_ofFunction_mpullback]
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply,
    SmoothForm.complexDx_apply, SmoothForm.complexDy_apply, Matrix.cons_val_zero,
    ContinuousLinearEquiv.apply_symm_apply]
  exact (fderiv ℝ v' (z : ℂ)).apply_eq_re_smul_one_add_im_smul_I a

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
    add_apply, RoughForm.flatOneFormEquiv_wedgeWith_ofFunction_mpullback,
    RoughForm.flatOneFormEquiv_wedgeWith_ofFunction_mpullback]
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
  simp [planarTwoFormCoeff_apply, planarCoordEquiv, ContinuousLinearEquiv.symm_trans_apply]

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
  rw [planarTwoFormCoeff_apply, RoughForm.wedgeWith_ofFunction_mpullback_apply]
  congr 2
  ext i
  fin_cases i
  · simp only [Fin.cast_eq_self, Fin.zero_eta, Matrix.cons_val_zero,
      ContinuousLinearEquiv.apply_symm_apply]
  · simp only [Fin.cast_eq_self, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      ContinuousLinearEquiv.apply_symm_apply]

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
theorem planarTwoFormCoeff_neg {U : Opens ℂ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (η : RoughForm 𝓘(ℝ, ℂ) U F 2) (z : U) :
    planarTwoFormCoeff (-η) z = -planarTwoFormCoeff η z := by
  simp [planarTwoFormCoeff_apply]

@[simp]
theorem planarTwoFormCoeff_sub {U : Opens ℂ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (η₁ η₂ : RoughForm 𝓘(ℝ, ℂ) U F 2) (z : U) :
    planarTwoFormCoeff (η₁ - η₂) z =
      planarTwoFormCoeff η₁ z - planarTwoFormCoeff η₂ z := by
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
  simp only [ContinuousAlternatingMap.coe_toAlternatingMap]
  rw [hb, ← planarTwoFormCoeff_eq_apply_symm]
  exact (planarTwoFormCoeff_wedgeWith_complexDx_wedge_complexDy (planarTwoFormCoeff η) z).symm

/-- Two planar `2`-forms on `U ⊆ ℂ` agree iff their `dx ∧ dy` coefficients agree. -/
theorem planarTwoFormCoeff_injective {U : Opens ℂ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    Function.Injective (planarTwoFormCoeff (U := U) (F := F)) := by
  intro η₁ η₂ h
  rw [roughForm_two_eq_wedgeWith_complexDx_wedge_complexDy η₁,
    roughForm_two_eq_wedgeWith_complexDx_wedge_complexDy η₂, h]

/-- Two planar `2`-forms on `U ⊆ ℂ` are equal if and only if their `dx ∧ dy` coefficients are
equal. -/
@[simp]
theorem planarTwoFormCoeff_inj {U : Opens ℂ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {η₁ η₂ : RoughForm 𝓘(ℝ, ℂ) U F 2} :
    planarTwoFormCoeff η₁ = planarTwoFormCoeff η₂ ↔ η₁ = η₂ :=
  planarTwoFormCoeff_injective.eq_iff

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
    rw [Function.comp_apply, ContinuousAlternatingMap.apply_apply, planarTwoFormCoeff_apply, heq z,
      Manifold.tangentSpaceOpenEquiv_symm_apply, Manifold.tangentSpaceOpenEquiv_symm_apply,
      NormedSpace.fromTangentSpace_symm_apply, NormedSpace.fromTangentSpace_symm_apply]
    -- `TangentSpace 𝓘(ℝ, ℂ) z` and `TangentSpace 𝓘(ℝ, ℂ) (z : ℂ)` are definitionally `ℂ`.
    rfl
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
  rw [SmoothForm.complexDx_eq_const, SmoothForm.complexDy_eq_const]
  exact ((SmoothForm.isSmoothForm_const _ n).wedge
    (SmoothForm.isSmoothForm_const _ n)).mpullback contMDiff_subtypeVal

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
  have hf' : f = fun y : U ↦ f' y := funext fun y ↦ (hf_eq y).symm
  have hderiv (a : ℂ) :
      mextDeriv (RoughForm.ofFunction 𝓘(ℝ, ℂ) f) z
        ![(Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, ℂ)) z).symm
          ((NormedSpace.fromTangentSpace (z : ℂ)).symm a)] = fderiv ℝ f' (z : ℂ) a := by
    rw [hf', Manifold.tangentSpaceOpenEquiv_symm_apply, NormedSpace.fromTangentSpace_symm_apply,
      ← RoughForm.flatOneFormEquiv_apply, RoughForm.flatOneFormEquiv_mextDeriv_ofFunction]
  have hα_eval (a : ℂ) :
      αU.val z ![(Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, ℂ)) z).symm
          ((NormedSpace.fromTangentSpace (z : ℂ)).symm a)] =
        α.val (z : ℂ) ![(NormedSpace.fromTangentSpace (z : ℂ)).symm a] := by
    rw [SmoothForm.coe_mpullback, mpullback_apply]
    congr 1
    ext i
    fin_cases i
    simp only [Matrix.cons_val_fin_one, Manifold.mfderiv_subtype_val,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  rw [← SmoothForm.coe_mpullback (Subtype.val : U → ℂ) contMDiff_subtypeVal α,
    planarTwoFormCoeff_apply,
    mextDeriv_wedgeWith B (mdifferentiableAt_ofFunction hf) (αU.mdifferentiableAt z),
    hαU, RoughForm.wedgeWith_zero_right]
  simp only [Pi.zero_apply, ContinuousAlternatingMap.coe_zero, smul_zero, add_zero,
    Function.comp_def, Fin.cast_eq_self, RoughForm.wedgeWith_apply_one_one,
    hderiv, hα_eval]

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
    conjWirtingerDeriv_apply, smul_eq_mul, mul_one, smul_add, smul_smul]
  rw [show (2 * Complex.I) * (2⁻¹ : ℂ) = Complex.I by ring_nf,
    show (2 * Complex.I) * ((2⁻¹ : ℂ) * Complex.I) = -1 by ring_nf; simp [Complex.I_sq]]
  module

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
    conj_I, (starRingEnd ℂ).map_one, wirtingerDeriv_apply, smul_eq_mul, mul_one, smul_sub,
    smul_smul]
  rw [show (-2 * Complex.I) * (2⁻¹ : ℂ) = -Complex.I by ring_nf,
    show (-2 * Complex.I) * ((2⁻¹ : ℂ) * Complex.I) = 1 by ring_nf; simp [Complex.I_sq]]

private theorem differentiableWithinAt_inChartAt_wedgeWith_ofFunction_mpullback {U : Opens ℂ}
    {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (B : F →L[ℝ] G →L[ℝ] H) {f : U → F} {z : U}
    (hf : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, F) f z) (α : SmoothForm 𝓘(ℝ, ℂ) ℂ G 1) :
    DifferentiableWithinAt ℝ
      ((RoughForm.wedgeWith B (RoughForm.ofFunction 𝓘(ℝ, ℂ) f)
        (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) α.val)).inChartAt z)
      (range 𝓘(ℝ, ℂ)) (extChartAt 𝓘(ℝ, ℂ) z z) := by
  rw [← SmoothForm.coe_mpullback (Subtype.val : U → ℂ) contMDiff_subtypeVal α]
  exact RoughForm.differentiableWithinAt_inChartAt_wedgeWith B
    (RoughForm.differentiableWithinAt_range_inChartAt_of_mdifferentiableAt _
      (mdifferentiableAt_ofFunction hf))
    (RoughForm.differentiableWithinAt_range_inChartAt_of_mdifferentiableAt _
      ((SmoothForm.mpullback (Subtype.val : U → ℂ) contMDiff_subtypeVal α).mdifferentiableAt z))

private theorem mextDeriv_add_wedgeWith_ofFunction_mpullback {U : Opens ℂ}
    {F₁ F₂ F₃ F₄ H : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
    [NormedAddCommGroup F₄] [NormedSpace ℝ F₄] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (B₁ : F₁ →L[ℝ] F₂ →L[ℝ] H) (B₂ : F₃ →L[ℝ] F₄ →L[ℝ] H)
    {f₁ : U → F₁} {f₂ : U → F₃} {z : U}
    (hf₁ : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, F₁) f₁ z)
    (hf₂ : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, F₃) f₂ z)
    (α₁ : SmoothForm 𝓘(ℝ, ℂ) ℂ F₂ 1) (α₂ : SmoothForm 𝓘(ℝ, ℂ) ℂ F₄ 1) :
    mextDeriv
      (RoughForm.wedgeWith B₁ (RoughForm.ofFunction 𝓘(ℝ, ℂ) f₁)
          (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) α₁.val) +
        RoughForm.wedgeWith B₂ (RoughForm.ofFunction 𝓘(ℝ, ℂ) f₂)
          (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) α₂.val)) z =
      mextDeriv
        (RoughForm.wedgeWith B₁ (RoughForm.ofFunction 𝓘(ℝ, ℂ) f₁)
          (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) α₁.val)) z +
      mextDeriv
        (RoughForm.wedgeWith B₂ (RoughForm.ofFunction 𝓘(ℝ, ℂ) f₂)
          (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) α₂.val)) z :=
  mextDeriv_add
    (differentiableWithinAt_inChartAt_wedgeWith_ofFunction_mpullback B₁ hf₁ α₁)
    (differentiableWithinAt_inChartAt_wedgeWith_ofFunction_mpullback B₂ hf₂ α₂)

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
  rw [planarTwoFormCoeff_apply,
    mextDeriv_add_wedgeWith_ofFunction_mpullback _ _ ha hb SmoothForm.complexDx
      SmoothForm.complexDy,
    ContinuousAlternatingMap.add_apply, ← planarTwoFormCoeff_apply, ← planarTwoFormCoeff_apply,
    planarTwoFormCoeff_mextDeriv_wedgeWith_of_isClosed _ ha_eq ha
      ((SmoothForm.isClosed_def _).2 SmoothForm.mextDeriv_complexDx),
    planarTwoFormCoeff_mextDeriv_wedgeWith_of_isClosed _ hb_eq hb
      ((SmoothForm.isClosed_def _).2 SmoothForm.mextDeriv_complexDy)]
  simp [sub_eq_add_neg, add_comm]

end OneFormDeriv

end TauCeti
