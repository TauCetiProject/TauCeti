/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Plane.Complex
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Complex.Wirtinger.OpenSet
import TauCeti.Analysis.Normed.Module.Complexification
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Basic

/-!
# Planar coordinate forms and two-form exactness on open subsets of `ℂ`

On the real manifold `ℂ`, the coordinate one-forms `dx = d(Re)` (`TauCeti.SmoothForm.complexDx`),
`dy = d(Im)` (`TauCeti.SmoothForm.complexDy`), `dz = d(id)` (`TauCeti.SmoothForm.complexDz`), and
`dbar z = d(conj)` (`TauCeti.SmoothForm.complexDzBar`) pull back along the inclusion of any open
subset `U : TopologicalSpace.Opens ℂ` to closed smooth one-forms on `U`.

For any real normed space `F`, every alternating two-form `η : RoughForm 𝓘(ℝ, ℂ) U F 2` is
uniquely determined by its evaluation `TauCeti.planarTwoFormCoeff η` on the positive coordinate
frame `(1, i)`: we have `η = (planarTwoFormCoeff η) dx ∧ dy`, and when `W` is a complex normed
space, `η = ((-2i)⁻¹ • planarTwoFormCoeff η) dz ∧ dbar z`. If `η` is `C^n`, then so is its
coefficient.

Combining this coordinate calculus with global `\bar∂` solvability on arbitrary open subsets of `ℂ`
(`TauCeti.exists_contDiffOn_conjWirtingerDeriv_apply_one_eq`) yields:

* **Form-level closed completion**
  (`TauCeti.exists_contMDiff_mextDeriv_wedgeWith_complexDz_add_eq_zero`,
  `TauCeti.exists_contMDiff_mextDeriv_mul_complexDz_add_eq_zero`): for every `C^n` function `f`
  (`1 ≤ m`, `m + 1 ≤ n`) into a complex Banach space `W`, there is a `C^m` function `g` with
  `d(g dz + f dbar z) = 0`.
* **Explicit `(1, 0)`-primitive for complex Banach-valued two-forms**
  (`TauCeti.exists_contMDiff_mextDeriv_wedgeWith_complexDz_eq`): every `C^n` (`1 ≤ n`) two-form
  `η` on `U` with values in a complex Banach space `W` equals `d(g dz)` for a `C^n` function
  `g : U → W`.
* **Banach-valued two-form exactness**
  (`TauCeti.exists_isSmoothForm_mextDeriv_eq_of_opens_complex`,
  `TauCeti.exists_mextDerivₗ_eq_of_opens_complex`): by passing to the Banach complexification
  `TauCeti.Complexification F` and taking the real part via `TauCeti.RoughForm.mapCoeff`, every
  `C^n` (`1 ≤ n`) two-form on `U` with values in any real Banach space `F` (including `ℝ`, `ℂ`,
  and every complex Banach space) is exact.

No connectedness, simple connectivity, or nonemptiness hypothesis on `U` is assumed.

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

/-- Evaluation of the pullback of `dx` to an open subset `U ⊆ ℂ`.
Not `@[simp]`: `mpullback_apply` and `Manifold.mfderiv_subtype_val` already simplify the
left-hand side. -/
theorem mpullback_subtype_val_complexDx_apply (z : U)
    (v : Fin 1 → TangentSpace 𝓘(ℝ, ℂ) z) :
    mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) SmoothForm.complexDx.val z v =
      (NormedSpace.fromTangentSpace (z : ℂ) (Manifold.tangentSpaceOpenEquiv z (v 0))).re := by
  rw [mpullback_apply, SmoothForm.complexDx_apply]
  simp [Manifold.mfderiv_subtype_val]

/-- Evaluation of the pullback of `dy` to an open subset `U ⊆ ℂ`.
Not `@[simp]`: `mpullback_apply` and `Manifold.mfderiv_subtype_val` already simplify the
left-hand side. -/
theorem mpullback_subtype_val_complexDy_apply (z : U)
    (v : Fin 1 → TangentSpace 𝓘(ℝ, ℂ) z) :
    mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) SmoothForm.complexDy.val z v =
      (NormedSpace.fromTangentSpace (z : ℂ) (Manifold.tangentSpaceOpenEquiv z (v 0))).im := by
  rw [mpullback_apply, SmoothForm.complexDy_apply]
  simp [Manifold.mfderiv_subtype_val]

/-- Evaluation of the pullback of `dz` to an open subset `U ⊆ ℂ`.
Not `@[simp]`: `mpullback_apply` and `Manifold.mfderiv_subtype_val` already simplify the
left-hand side. -/
theorem mpullback_subtype_val_complexDz_apply (z : U)
    (v : Fin 1 → TangentSpace 𝓘(ℝ, ℂ) z) :
    mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) SmoothForm.complexDz.val z v =
      NormedSpace.fromTangentSpace (z : ℂ) (Manifold.tangentSpaceOpenEquiv z (v 0)) := by
  rw [mpullback_apply, SmoothForm.complexDz_apply]
  simp [Manifold.mfderiv_subtype_val]

/-- Evaluation of the pullback of `dbar z` to an open subset `U ⊆ ℂ`.
Not `@[simp]`: `mpullback_apply` and `Manifold.mfderiv_subtype_val` already simplify the
left-hand side. -/
theorem mpullback_subtype_val_complexDzBar_apply (z : U)
    (v : Fin 1 → TangentSpace 𝓘(ℝ, ℂ) z) :
    mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) SmoothForm.complexDzBar.val z v =
      conj (NormedSpace.fromTangentSpace (z : ℂ)
        (Manifold.tangentSpaceOpenEquiv z (v 0))) := by
  rw [mpullback_apply, SmoothForm.complexDzBar_apply]
  simp [Manifold.mfderiv_subtype_val]

/-- Evaluation of the pullback of `dx ∧ dy` to an open subset `U ⊆ ℂ`. -/
theorem mpullback_subtype_val_complexDx_wedge_complexDy_apply (z : U)
    (v w : TangentSpace 𝓘(ℝ, ℂ) z) :
    mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
        (RoughForm.wedge SmoothForm.complexDx.val SmoothForm.complexDy.val) z ![v, w] =
      (NormedSpace.fromTangentSpace (z : ℂ) (Manifold.tangentSpaceOpenEquiv z v)).re *
          (NormedSpace.fromTangentSpace (z : ℂ) (Manifold.tangentSpaceOpenEquiv z w)).im -
        (NormedSpace.fromTangentSpace (z : ℂ) (Manifold.tangentSpaceOpenEquiv z w)).re *
          (NormedSpace.fromTangentSpace (z : ℂ) (Manifold.tangentSpaceOpenEquiv z v)).im := by
  rw [mpullback_apply_pair, Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe,
    SmoothForm.complexDx_wedge_complexDy_apply]

/-- Evaluation of the pullback of `dz ∧ dbar z` to an open subset `U ⊆ ℂ`. -/
theorem mpullback_subtype_val_complexDz_wedgeWith_complexDzBar_apply (z : U)
    (v w : TangentSpace 𝓘(ℝ, ℂ) z) :
    mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
        (RoughForm.wedgeWith (ContinuousLinearMap.mul ℝ ℂ) SmoothForm.complexDz.val
          SmoothForm.complexDzBar.val) z ![v, w] =
      (-2 * Complex.I) *
        (((NormedSpace.fromTangentSpace (z : ℂ) (Manifold.tangentSpaceOpenEquiv z v)).re *
            (NormedSpace.fromTangentSpace (z : ℂ) (Manifold.tangentSpaceOpenEquiv z w)).im -
          (NormedSpace.fromTangentSpace (z : ℂ) (Manifold.tangentSpaceOpenEquiv z w)).re *
            (NormedSpace.fromTangentSpace (z : ℂ) (Manifold.tangentSpaceOpenEquiv z v)).im :
          ℝ) : ℂ) := by
  rw [mpullback_apply_pair, Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe,
    SmoothForm.complexDz_wedgeWith_complexDzBar_apply,
    SmoothForm.complexDx_wedge_complexDy_apply]

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

@[simp]
theorem mextDeriv_mpullback_subtype_val_complexDx :
    mextDeriv (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) SmoothForm.complexDx.val) =
      0 :=
  (SmoothForm.complexDx.isSmoothForm.of_le (by simp)).mextDeriv_mpullback_eq_zero
    SmoothForm.mextDeriv_complexDx contMDiff_subtypeVal

@[simp]
theorem mextDeriv_mpullback_subtype_val_complexDy :
    mextDeriv (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) SmoothForm.complexDy.val) =
      0 :=
  (SmoothForm.complexDy.isSmoothForm.of_le (by simp)).mextDeriv_mpullback_eq_zero
    SmoothForm.mextDeriv_complexDy contMDiff_subtypeVal

@[simp]
theorem mextDeriv_mpullback_subtype_val_complexDz :
    mextDeriv (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) SmoothForm.complexDz.val) =
      0 :=
  (SmoothForm.complexDz.isSmoothForm.of_le (by simp)).mextDeriv_mpullback_eq_zero
    SmoothForm.mextDeriv_complexDz contMDiff_subtypeVal

@[simp]
theorem mextDeriv_mpullback_subtype_val_complexDzBar :
    mextDeriv (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) SmoothForm.complexDzBar.val) =
      0 :=
  (SmoothForm.complexDzBar.isSmoothForm.of_le (by simp)).mextDeriv_mpullback_eq_zero
    SmoothForm.mextDeriv_complexDzBar contMDiff_subtypeVal

end OpenCoords

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
  ext z w
  rw [mextDeriv_ofFunction, ContinuousAlternatingMap.ofSubsingleton_apply_apply,
    Pi.add_apply, ContinuousAlternatingMap.add_apply, RoughForm.wedgeWith_apply',
    RoughForm.wedgeWith_apply', ContinuousAlternatingMap.pairedWedge_apply_zero_left,
    ContinuousAlternatingMap.pairedWedge_apply_zero_left]
  simp only [RoughForm.ofFunction_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lsmul_apply, mpullback_subtype_val_complexDx_apply,
    mpullback_subtype_val_complexDy_apply, Function.comp_apply, Fin.cast_refl, id_eq]
  rw [Manifold.mvfderiv_opens_eq_fderiv_apply hv z (w 0)]
  set a : ℂ := NormedSpace.fromTangentSpace (z : ℂ) (Manifold.tangentSpaceOpenEquiv z (w 0))
  have ha : a = a.re • (1 : ℂ) + a.im • Complex.I := by
    simp [Complex.real_smul]
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
  ext z w
  rw [mextDeriv_ofFunction, ContinuousAlternatingMap.ofSubsingleton_apply_apply,
    Pi.add_apply, ContinuousAlternatingMap.add_apply, RoughForm.wedgeWith_apply',
    RoughForm.wedgeWith_apply', ContinuousAlternatingMap.pairedWedge_apply_zero_left,
    ContinuousAlternatingMap.pairedWedge_apply_zero_left]
  simp only [RoughForm.ofFunction_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lsmul_apply, mpullback_subtype_val_complexDz_apply,
    mpullback_subtype_val_complexDzBar_apply, Function.comp_apply, Fin.cast_refl, id_eq]
  rw [Manifold.mvfderiv_opens_eq_fderiv_apply hu z (w 0)]
  exact fderiv_apply_eq_smul_wirtingerDeriv_add_smul_conjWirtingerDeriv (f := u') (z : ℂ) _

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

private def planarCoordEquiv {U : Opens ℂ} (z : U) : TangentSpace 𝓘(ℝ, ℂ) z ≃L[ℝ] ℂ :=
  (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, ℂ)) z).trans
    (NormedSpace.fromTangentSpace (z : ℂ))

private theorem planarCoordEquiv_apply {U : Opens ℂ} (z : U) (v : TangentSpace 𝓘(ℝ, ℂ) z) :
    planarCoordEquiv z v =
      NormedSpace.fromTangentSpace (z : ℂ) (Manifold.tangentSpaceOpenEquiv z v) :=
  rfl

private theorem planarTwoFormCoeff_eq_apply_symm {U : Opens ℂ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (η : RoughForm 𝓘(ℝ, ℂ) U F 2) (z : U) :
    planarTwoFormCoeff η z =
      η z ![(planarCoordEquiv z).symm 1, (planarCoordEquiv z).symm Complex.I] := by
  simp [planarTwoFormCoeff_apply, planarCoordEquiv]

private theorem comp_finCast_self {α : Type*} {n : ℕ} (h : n = n) (v : Fin n → α) :
    v ∘ Fin.cast h = v := by
  ext i
  simp

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
  refine b.ext_alternating fun v hv ↦ ?_
  have hv_pair : (fun i ↦ b (v i)) = ![b (v 0), b (v 1)] := by
    ext i
    fin_cases i <;> simp
  rw [ContinuousAlternatingMap.coe_toAlternatingMap, ContinuousAlternatingMap.coe_toAlternatingMap,
    hv_pair, RoughForm.wedgeWith_apply', ContinuousAlternatingMap.pairedWedge_apply_zero_left]
  simp only [RoughForm.ofFunction_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lsmul_apply, comp_finCast_self,
    mpullback_subtype_val_complexDx_wedge_complexDy_apply]
  have hb0 : b 0 = (planarCoordEquiv z).symm 1 := by simp [b]
  have hb1 : b 1 = (planarCoordEquiv z).symm Complex.I := by simp [b]
  match h0 : v 0, h1 : v 1 with
  | 0, 0 => exact absurd (hv (h0.trans h1.symm)) (by decide)
  | 0, 1 =>
    simp only [hb0, hb1, ← planarCoordEquiv_apply, ContinuousLinearEquiv.apply_symm_apply,
      planarTwoFormCoeff_eq_apply_symm]
    simp
  | 1, 0 =>
    have hswap :
        ![(planarCoordEquiv z).symm Complex.I, (planarCoordEquiv z).symm 1] =
          ![(planarCoordEquiv z).symm 1, (planarCoordEquiv z).symm Complex.I] ∘
            Equiv.swap (0 : Fin 2) 1 := by
      ext i
      fin_cases i <;> simp
    simp only [hb0, hb1, ← planarCoordEquiv_apply, ContinuousLinearEquiv.apply_symm_apply,
      planarTwoFormCoeff_eq_apply_symm]
    rw [hswap, ← ContinuousAlternatingMap.coe_toAlternatingMap,
      (η z).map_swap _ (i := 0) (j := 1) (by decide),
      ContinuousAlternatingMap.coe_toAlternatingMap]
    simp
  | 1, 1 => exact absurd (hv (h0.trans h1.symm)) (by decide)

/-- Evaluating `(h dx ∧ dy)` at the positive coordinate frame recovers `h`. -/
@[simp]
theorem planarTwoFormCoeff_wedgeWith_complexDx_wedge_complexDy {U : Opens ℂ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (h : U → F) (z : U) :
    planarTwoFormCoeff
      (RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℝ).flip
        (RoughForm.ofFunction 𝓘(ℝ, ℂ) h)
        (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
          (RoughForm.wedge SmoothForm.complexDx.val SmoothForm.complexDy.val))) z = h z := by
  rw [planarTwoFormCoeff_eq_apply_symm, RoughForm.wedgeWith_apply',
    ContinuousAlternatingMap.pairedWedge_apply_zero_left]
  simp only [RoughForm.ofFunction_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lsmul_apply, comp_finCast_self,
    mpullback_subtype_val_complexDx_wedge_complexDy_apply,
    ← planarCoordEquiv_apply, ContinuousLinearEquiv.apply_symm_apply]
  simp

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
  rw [planarTwoFormCoeff_eq_apply_symm, RoughForm.wedgeWith_apply',
    ContinuousAlternatingMap.pairedWedge_apply_zero_left]
  simp only [RoughForm.ofFunction_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lsmul_apply, comp_finCast_self,
    mpullback_subtype_val_complexDz_wedgeWith_complexDzBar_apply,
    ← planarCoordEquiv_apply, ContinuousLinearEquiv.apply_symm_apply]
  simp

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
  intro z
  have htriv :=
    (isSmoothForm_iff_forall_contMDiffAt_trivializationAt_apply.1 hη) z ![1, Complex.I]
  refine htriv.congr_of_eventuallyEq ?_
  filter_upwards [Manifold.eventually_tangentSpaceOpenEquiv_symmL_trivializationAt_eq
    (I := 𝓘(ℝ, ℂ)) z] with y hy
  rw [planarTwoFormCoeff_apply]
  congr 1
  ext i
  have hi := hy (![1, Complex.I] i)
  rw [TangentBundle.symmL_model_space] at hi
  apply (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, ℂ)) y).injective
  rw [Function.comp_apply, hi]
  fin_cases i
  · simp only [Fin.zero_eta, Matrix.cons_val_zero, ContinuousLinearEquiv.apply_symm_apply]
    exact NormedSpace.fromTangentSpace_symm_apply (y : ℂ) 1
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero,
      ContinuousLinearEquiv.apply_symm_apply]
    exact NormedSpace.fromTangentSpace_symm_apply (y : ℂ) Complex.I

end TwoFormCoeff

/-! ### Exterior derivatives of planar one-forms -/

section OneFormDeriv

private theorem mdifferentiableAt_mpullback_subtype_val {U : Opens ℂ} {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] {α : RoughForm 𝓘(ℝ, ℂ) ℂ G 1}
    (hα : IsSmoothForm 𝓘(ℝ, ℂ) ∞ α) (z : U) :
    MDifferentiableAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ [⋀^Fin 1]→L[ℝ] G))
      (fun y : U ↦ Bundle.TotalSpace.mk' (ℂ [⋀^Fin 1]→L[ℝ] G) y
        (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) α y)) z :=
  ((hα.mpullback (contMDiff_subtypeVal (n := ∞))).contMDiff z).mdifferentiableAt (by simp)

private theorem differentiableWithinAt_inChartAt_wedgeWith_ofFunction {U : Opens ℂ}
    {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (B : F →L[ℝ] G →L[ℝ] H) {f : U → F} {z : U}
    (hf : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, F) f z) {α : RoughForm 𝓘(ℝ, ℂ) ℂ G 1}
    (hα : IsSmoothForm 𝓘(ℝ, ℂ) ∞ α) :
    DifferentiableWithinAt ℝ
      ((RoughForm.wedgeWith B (RoughForm.ofFunction 𝓘(ℝ, ℂ) f)
        (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) α)).inChartAt z)
      (range 𝓘(ℝ, ℂ)) (extChartAt 𝓘(ℝ, ℂ) z z) := by
  set αU := mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) α
  rw [show (RoughForm.wedgeWith B (RoughForm.ofFunction 𝓘(ℝ, ℂ) f) αU).inChartAt z =
      fun w ↦ ContinuousAlternatingMap.pairedWedge B B.continuous₂
        ((RoughForm.ofFunction 𝓘(ℝ, ℂ) f).inChartAt z w) (αU.inChartAt z w) from
    funext (RoughForm.inChartAt_wedgeWith B _ αU z)]
  have hf_c := RoughForm.differentiableWithinAt_inChartAt (s := univ)
    (RoughForm.ofFunction 𝓘(ℝ, ℂ) f) (mdifferentiableAt_ofFunction hf).mdifferentiableWithinAt
  have hα_c := RoughForm.differentiableWithinAt_inChartAt (s := univ) αU
    (mdifferentiableAt_mpullback_subtype_val hα z).mdifferentiableWithinAt
  simp only [preimage_univ, univ_inter] at hf_c hα_c
  exact (differentiableWithinAt_const _).pairedWedge hf_c hα_c

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
  rw [planarTwoFormCoeff_eq_apply_symm,
    mextDeriv_wedgeWith (ContinuousLinearMap.lsmul ℝ ℂ).flip (mdifferentiableAt_ofFunction hg)
      (mdifferentiableAt_mpullback_subtype_val SmoothForm.complexDz.isSmoothForm z),
    mextDeriv_mpullback_subtype_val_complexDz, RoughForm.wedgeWith_zero_right]
  simp only [Pi.zero_apply, ContinuousAlternatingMap.coe_zero, smul_zero, add_zero,
    comp_finCast_self, RoughForm.wedgeWith_apply_one_one, mextDeriv_ofFunction,
    ContinuousAlternatingMap.ofSubsingleton_apply_apply, Matrix.cons_val_zero,
    mpullback_subtype_val_complexDz_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lsmul_apply, Manifold.mvfderiv_opens_eq_fderiv_apply hg_eq,
    ← planarCoordEquiv_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [conjWirtingerDeriv_apply, smul_smul, smul_add, smul_smul, smul_eq_mul, mul_one]
  have h1 : 2 * Complex.I * (2 : ℂ)⁻¹ = Complex.I := by ring
  rw [h1, Complex.I_mul_I, one_smul, neg_one_smul, sub_eq_add_neg]

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
  rw [planarTwoFormCoeff_eq_apply_symm,
    mextDeriv_wedgeWith (ContinuousLinearMap.lsmul ℝ ℂ).flip (mdifferentiableAt_ofFunction hf)
      (mdifferentiableAt_mpullback_subtype_val SmoothForm.complexDzBar.isSmoothForm z),
    mextDeriv_mpullback_subtype_val_complexDzBar, RoughForm.wedgeWith_zero_right]
  simp only [Pi.zero_apply, ContinuousAlternatingMap.coe_zero, smul_zero, add_zero,
    comp_finCast_self, RoughForm.wedgeWith_apply_one_one, mextDeriv_ofFunction,
    ContinuousAlternatingMap.ofSubsingleton_apply_apply, Matrix.cons_val_zero,
    mpullback_subtype_val_complexDzBar_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lsmul_apply, Manifold.mvfderiv_opens_eq_fderiv_apply hf_eq,
    ← planarCoordEquiv_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [conj_I, (starRingEnd ℂ).map_one, wirtingerDeriv_apply, smul_smul, smul_sub,
    smul_smul, smul_eq_mul, mul_one]
  have h1 : -2 * Complex.I * (2 : ℂ)⁻¹ = -Complex.I := by ring
  rw [h1, neg_mul, Complex.I_mul_I, neg_neg]

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
  rw [planarTwoFormCoeff_eq_apply_symm,
    mextDeriv_add
      (differentiableWithinAt_inChartAt_wedgeWith_ofFunction _ ha
        SmoothForm.complexDx.isSmoothForm)
      (differentiableWithinAt_inChartAt_wedgeWith_ofFunction _ hb
        SmoothForm.complexDy.isSmoothForm),
    ContinuousAlternatingMap.add_apply,
    mextDeriv_wedgeWith (ContinuousLinearMap.lsmul ℝ ℝ).flip (mdifferentiableAt_ofFunction ha)
      (mdifferentiableAt_mpullback_subtype_val SmoothForm.complexDx.isSmoothForm z),
    mextDeriv_wedgeWith (ContinuousLinearMap.lsmul ℝ ℝ).flip (mdifferentiableAt_ofFunction hb)
      (mdifferentiableAt_mpullback_subtype_val SmoothForm.complexDy.isSmoothForm z),
    mextDeriv_mpullback_subtype_val_complexDx, mextDeriv_mpullback_subtype_val_complexDy,
    RoughForm.wedgeWith_zero_right, RoughForm.wedgeWith_zero_right]
  simp only [Pi.zero_apply, ContinuousAlternatingMap.coe_zero, smul_zero, add_zero,
    comp_finCast_self, RoughForm.wedgeWith_apply_one_one, mextDeriv_ofFunction,
    ContinuousAlternatingMap.ofSubsingleton_apply_apply, Matrix.cons_val_zero,
    mpullback_subtype_val_complexDx_apply, mpullback_subtype_val_complexDy_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply,
    Manifold.mvfderiv_opens_eq_fderiv_apply ha_eq,
    Manifold.mvfderiv_opens_eq_fderiv_apply hb_eq,
    ← planarCoordEquiv_apply, ContinuousLinearEquiv.apply_symm_apply]
  simp [sub_eq_add_neg, add_comm]

end OneFormDeriv

/-! ### Closed completion and two-form exactness on open subsets of `ℂ` -/

section Exactness

/-- **Form-level closed completion (Banach-valued).** For any `C^n` function `f : U → W` on an
open subset `U ⊆ ℂ` into a complex Banach space `W`, with `1 ≤ m` and `m + 1 ≤ n`, there exists
a `C^m` function `g : U → W` such that the `W`-valued one-form `g dz + f dbar z` is closed. -/
theorem exists_contMDiff_mextDeriv_wedgeWith_complexDz_add_eq_zero {U : Opens ℂ} {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W] {m n : ℕ∞}
    (hm : 1 ≤ m) (hmn : m + 1 ≤ n) {f : U → W}
    (hf : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, W) n f) :
    ∃ g : U → W, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, W) m g ∧
      mextDeriv
        (RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℂ).flip
            (RoughForm.ofFunction 𝓘(ℝ, ℂ) g)
            (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
              SmoothForm.complexDz.val) +
          RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℂ).flip
            (RoughForm.ofFunction 𝓘(ℝ, ℂ) f)
            (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
              SmoothForm.complexDzBar.val)) = 0 := by
  let f' : ℂ → W := Subtype.val.extend f 0
  have hf'_eq (z : U) : f' z = f z := Subtype.val_injective.extend_apply f 0 z
  have hf' : ContDiffOn ℝ n f' (U : Set ℂ) := hf.contDiffOn_extend_subtypeVal 0
  obtain ⟨g', hg', hsol⟩ :=
    exists_contDiffOn_conjWirtingerDeriv_eq_wirtingerDeriv hm hmn U.isOpen hf'
  let g : U → W := g' ∘ Subtype.val
  have hg : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, W) m g := hg'.contMDiff_comp_subtypeVal
  refine ⟨g, hg, ?_⟩
  apply planarTwoFormCoeff_injective
  funext z
  have hgd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, W) g z :=
    (hg z).mdifferentiableAt (by exact_mod_cast (zero_lt_one.trans_le hm).ne')
  have hfd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, W) f z :=
    (hf z).mdifferentiableAt (by
      exact_mod_cast (zero_lt_one.trans_le (hm.trans (le_self_add.trans hmn))).ne')
  rw [planarTwoFormCoeff_apply, planarTwoFormCoeff_zero,
    mextDeriv_add
      (differentiableWithinAt_inChartAt_wedgeWith_ofFunction _ hgd
        SmoothForm.complexDz.isSmoothForm)
      (differentiableWithinAt_inChartAt_wedgeWith_ofFunction _ hfd
        SmoothForm.complexDzBar.isSmoothForm),
    ContinuousAlternatingMap.add_apply, ← planarTwoFormCoeff_apply, ← planarTwoFormCoeff_apply,
    planarTwoFormCoeff_mextDeriv_wedgeWith_complexDz (g := g) (g' := g') (fun _ ↦ rfl) hgd,
    planarTwoFormCoeff_mextDeriv_wedgeWith_complexDzBar hf'_eq hfd, hsol z z.property, ← add_smul]
  simp

/-- **Form-level closed completion (scalar `ℂ` multiplication pairing).** For any `C^n`
function `f : U → ℂ` on an open subset `U ⊆ ℂ` with `1 ≤ m` and `m + 1 ≤ n`, there exists a
`C^m` function `g : U → ℂ` with `d(g dz + f dbar z) = 0`, where the products are paired via
`ContinuousLinearMap.mul ℝ ℂ`. -/
theorem exists_contMDiff_mextDeriv_mul_complexDz_add_eq_zero {U : Opens ℂ} {m n : ℕ∞}
    (hm : 1 ≤ m) (hmn : m + 1 ≤ n) {f : U → ℂ}
    (hf : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n f) :
    ∃ g : U → ℂ, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) m g ∧
      mextDeriv
        (RoughForm.wedgeWith (ContinuousLinearMap.mul ℝ ℂ)
            (RoughForm.ofFunction 𝓘(ℝ, ℂ) g)
            (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
              SmoothForm.complexDz.val) +
          RoughForm.wedgeWith (ContinuousLinearMap.mul ℝ ℂ)
            (RoughForm.ofFunction 𝓘(ℝ, ℂ) f)
            (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
              SmoothForm.complexDzBar.val)) = 0 := by
  have hmul :
      (ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ)).flip = ContinuousLinearMap.mul ℝ ℂ := by
    ext a b
    simp [mul_comm]
  simpa only [hmul] using exists_contMDiff_mextDeriv_wedgeWith_complexDz_add_eq_zero hm hmn hf

/-- **Explicit `(1, 0)`-primitive for complex Banach-valued two-forms on open subsets of `ℂ`.**
Every `C^n` (`1 ≤ n`) two-form `η` on an arbitrary open subset `U ⊆ ℂ` with values in a
complex Banach space `W` equals `d(g dz)` for a `C^n` function `g : U → W`. -/
theorem exists_contMDiff_mextDeriv_wedgeWith_complexDz_eq {U : Opens ℂ} {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W] {n : ℕ∞} (hn : 1 ≤ n)
    {η : RoughForm 𝓘(ℝ, ℂ) U W 2} (hη : IsSmoothForm 𝓘(ℝ, ℂ) n η) :
    ∃ g : U → W, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, W) n g ∧
      mextDeriv
        (RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℂ).flip
          (RoughForm.ofFunction 𝓘(ℝ, ℂ) g)
          (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
            SmoothForm.complexDz.val)) = η := by
  let h : U → W := fun z ↦ (2 * Complex.I)⁻¹ • planarTwoFormCoeff η z
  have hh : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, W) n h :=
    (contMDiff_iff_contDiff.2
      (((2 * Complex.I)⁻¹ • ContinuousLinearMap.id ℂ W).restrictScalars ℝ).contDiff).comp
      hη.contMDiff_planarTwoFormCoeff
  let h' : ℂ → W := Subtype.val.extend h 0
  have hh'_eq (z : U) : h' z = h z := Subtype.val_injective.extend_apply h 0 z
  have hh' : ContDiffOn ℝ n h' (U : Set ℂ) := hh.contDiffOn_extend_subtypeVal 0
  obtain ⟨g', hg', hsol⟩ :=
    exists_contDiffOn_conjWirtingerDeriv_apply_one_eq hn U.isOpen hh'
  let g : U → W := g' ∘ Subtype.val
  have hg : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, W) n g := hg'.contMDiff_comp_subtypeVal
  refine ⟨g, hg, ?_⟩
  apply planarTwoFormCoeff_injective
  funext z
  have hgd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, W) g z :=
    (hg z).mdifferentiableAt (by exact_mod_cast (zero_lt_one.trans_le hn).ne')
  rw [planarTwoFormCoeff_mextDeriv_wedgeWith_complexDz (g := g) (g' := g') (fun _ ↦ rfl) hgd,
    hsol z z.property, hh'_eq z]
  have hne : (2 * Complex.I : ℂ) ≠ 0 := by simp [Complex.I_ne_zero]
  simp only [h, smul_smul, mul_inv_cancel₀ hne, one_smul]

/-- **Banach-valued two-form exactness on open subsets of `ℂ` (`C^n`).** Every `C^n` (`1 ≤ n`)
two-form on an arbitrary open subset `U ⊆ ℂ` with values in any real Banach space `F` (including
`ℝ`, `ℂ`, and every complex Banach space) is the exterior derivative of a `C^n` one-form. -/
theorem exists_isSmoothForm_mextDeriv_eq_of_opens_complex {U : Opens ℂ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {n : ℕ∞} (hn : 1 ≤ n)
    {η : RoughForm 𝓘(ℝ, ℂ) U F 2} (hη : IsSmoothForm 𝓘(ℝ, ℂ) n η) :
    ∃ β : RoughForm 𝓘(ℝ, ℂ) U F 1,
      IsSmoothForm 𝓘(ℝ, ℂ) n β ∧ mextDeriv β = η := by
  obtain ⟨g, hg, hdg⟩ :=
    exists_contMDiff_mextDeriv_wedgeWith_complexDz_eq (W := Complexification F) hn
      (hη.mapCoeff (Complexification.ofRealLI F).toContinuousLinearMap)
  set dz := mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) SmoothForm.complexDz.val
  let βℂ : RoughForm 𝓘(ℝ, ℂ) U (Complexification F) 1 :=
    RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℂ).flip
      (RoughForm.ofFunction 𝓘(ℝ, ℂ) g) dz
  have hβℂ : IsSmoothForm 𝓘(ℝ, ℂ) n βℂ := by
    have hdz : IsSmoothForm 𝓘(ℝ, ℂ) n dz :=
      (SmoothForm.complexDz.isSmoothForm.mpullback
        (contMDiff_subtypeVal (n := ∞))).of_le (by simp)
    exact (isSmoothForm_ofFunction_iff.2 hg).wedgeWith _ hdz
  refine ⟨RoughForm.mapCoeff (Complexification.reCLM F) βℂ, hβℂ.mapCoeff _, ?_⟩
  rw [mextDeriv_mapCoeff _ (hβℂ.of_le (by exact_mod_cast hn)), hdg]
  simp

/-- **Banach-valued two-form exactness on open subsets of `ℂ` (bundled smooth forms).** Every
smooth two-form on an arbitrary open subset `U ⊆ ℂ` with values in any real Banach space `F`
(including `ℝ`, `ℂ`, and every complex Banach space) is the exterior derivative of a smooth
one-form. -/
theorem exists_mextDerivₗ_eq_of_opens_complex {U : Opens ℂ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (η : SmoothForm 𝓘(ℝ, ℂ) U F 2) :
    ∃ β : SmoothForm 𝓘(ℝ, ℂ) U F 1, mextDerivₗ 𝓘(ℝ, ℂ) 1 β = η := by
  obtain ⟨β, hβ, hdβ⟩ :=
    exists_isSmoothForm_mextDeriv_eq_of_opens_complex (n := ⊤) le_top η.isSmoothForm
  exact ⟨⟨β, hβ.mem_smoothBundleForms⟩,
    Subtype.ext ((mextDerivₗ_apply 𝓘(ℝ, ℂ) 1 _).trans hdβ)⟩

end Exactness

end TauCeti
