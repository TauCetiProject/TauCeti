/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Plane.Complex
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Complex.Wirtinger.OpenSet
import TauCeti.Analysis.Normed.Module.Complexification
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.DifferentialForm.Closed
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

/-! ### Real and complex coordinate one-forms on `ℂ` -/

namespace SmoothForm

/-- The real-valued coordinate one-form `dx = d(Re)` on the real manifold `ℂ`. -/
def complexDx : SmoothForm 𝓘(ℝ, ℂ) ℂ ℝ 1 :=
  const (ContinuousAlternatingMap.ofSubsingleton ℝ ℂ ℝ (0 : Fin 1) Complex.reCLM)

/-- The real-valued coordinate one-form `dy = d(Im)` on the real manifold `ℂ`. -/
def complexDy : SmoothForm 𝓘(ℝ, ℂ) ℂ ℝ 1 :=
  const (ContinuousAlternatingMap.ofSubsingleton ℝ ℂ ℝ (0 : Fin 1) Complex.imCLM)

@[simp]
theorem complexDx_apply (z : ℂ) (v : Fin 1 → TangentSpace 𝓘(ℝ, ℂ) z) :
    complexDx.1 z v = (NormedSpace.fromTangentSpace z (v 0)).re := by
  simp [complexDx]

@[simp]
theorem complexDy_apply (z : ℂ) (v : Fin 1 → TangentSpace 𝓘(ℝ, ℂ) z) :
    complexDy.1 z v = (NormedSpace.fromTangentSpace z (v 0)).im := by
  simp [complexDy]

/-- On `ℂ`, `dx` is the exterior derivative of the real-part coordinate function. -/
theorem complexDx_eq_mextDeriv :
    complexDx.1 = mextDeriv (RoughForm.ofFunction 𝓘(ℝ, ℂ) Complex.re) := by
  ext z v
  rw [complexDx_apply, mextDeriv_ofFunction, ContinuousAlternatingMap.ofSubsingleton_apply_apply,
    mvfderiv_apply_eq_mfderiv_apply, mfderiv_eq_fderiv]
  change (NormedSpace.fromTangentSpace z (v 0)).re =
    (fderiv ℝ (⇑Complex.reCLM) z) (NormedSpace.fromTangentSpace z (v 0))
  rw [ContinuousLinearMap.fderiv]
  rfl

/-- On `ℂ`, `dy` is the exterior derivative of the imaginary-part coordinate function. -/
theorem complexDy_eq_mextDeriv :
    complexDy.1 = mextDeriv (RoughForm.ofFunction 𝓘(ℝ, ℂ) Complex.im) := by
  ext z v
  rw [complexDy_apply, mextDeriv_ofFunction, ContinuousAlternatingMap.ofSubsingleton_apply_apply,
    mvfderiv_apply_eq_mfderiv_apply, mfderiv_eq_fderiv]
  change (NormedSpace.fromTangentSpace z (v 0)).im =
    (fderiv ℝ (⇑Complex.imCLM) z) (NormedSpace.fromTangentSpace z (v 0))
  rw [ContinuousLinearMap.fderiv]
  rfl

/-- On `ℂ`, `dz` is the exterior derivative of the identity coordinate function. -/
theorem complexDz_eq_mextDeriv :
    complexDz.1 = mextDeriv (RoughForm.ofFunction 𝓘(ℝ, ℂ) (id : ℂ → ℂ)) := by
  ext z v
  rw [complexDz_apply, mextDeriv_ofFunction, ContinuousAlternatingMap.ofSubsingleton_apply_apply,
    mvfderiv_apply_eq_mfderiv_apply, mfderiv_id]
  rfl

/-- On `ℂ`, `dbar z` is the exterior derivative of complex conjugation. -/
theorem complexDzBar_eq_mextDeriv :
    complexDzBar.1 = mextDeriv (RoughForm.ofFunction 𝓘(ℝ, ℂ) (starRingEnd ℂ : ℂ → ℂ)) := by
  ext z v
  rw [complexDzBar_apply, mextDeriv_ofFunction,
    ContinuousAlternatingMap.ofSubsingleton_apply_apply, mvfderiv_apply_eq_mfderiv_apply,
    mfderiv_eq_fderiv]
  change conj (NormedSpace.fromTangentSpace z (v 0)) =
    (fderiv ℝ (⇑(Complex.conjCLE : ℂ →L[ℝ] ℂ)) z) (NormedSpace.fromTangentSpace z (v 0))
  rw [ContinuousLinearMap.fderiv]
  rfl

@[simp]
theorem mextDeriv_complexDx : mextDeriv complexDx.1 = 0 :=
  (isClosed_def _).1 (isClosed_const _)

@[simp]
theorem mextDeriv_complexDy : mextDeriv complexDy.1 = 0 :=
  (isClosed_def _).1 (isClosed_const _)

@[simp]
theorem mextDeriv_complexDz : mextDeriv complexDz.1 = 0 := by
  rw [complexDz_eq_const]
  exact (isClosed_def _).1 (isClosed_const _)

@[simp]
theorem mextDeriv_complexDzBar : mextDeriv complexDzBar.1 = 0 := by
  rw [complexDzBar_eq_mextDeriv]
  exact mextDeriv_mextDeriv_ofFunction
    (contMDiff_iff_contDiff.2 (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff)

/-- The real area two-form `dx ∧ dy` on `ℂ` evaluates to the planar determinant. -/
theorem complexDx_wedge_complexDy_apply (z : ℂ) (v w : TangentSpace 𝓘(ℝ, ℂ) z) :
    RoughForm.wedge complexDx.1 complexDy.1 z ![v, w] =
      (NormedSpace.fromTangentSpace z v).re * (NormedSpace.fromTangentSpace z w).im -
        (NormedSpace.fromTangentSpace z w).re * (NormedSpace.fromTangentSpace z v).im := by
  rw [RoughForm.wedge_apply_one_one, complexDx_apply, complexDy_apply, complexDx_apply,
    complexDy_apply]
  rfl

/-- The complex two-form `dz ∧ dbar z` on `ℂ` equals `-2i` times the real area determinant. -/
theorem complexDz_wedgeWith_complexDzBar_apply (z : ℂ) (v w : TangentSpace 𝓘(ℝ, ℂ) z) :
    RoughForm.wedgeWith (ContinuousLinearMap.mul ℝ ℂ) complexDz.1 complexDzBar.1 z ![v, w] =
      (-2 * Complex.I) * (RoughForm.wedge complexDx.1 complexDy.1 z ![v, w] : ℂ) := by
  rw [RoughForm.wedgeWith_apply_one_one, ContinuousLinearMap.mul_apply',
    ContinuousLinearMap.mul_apply', complexDz_apply, complexDzBar_apply, complexDz_apply,
    complexDzBar_apply, complexDx_wedge_complexDy_apply]
  set a := NormedSpace.fromTangentSpace z v
  set b := NormedSpace.fromTangentSpace z w
  apply Complex.ext <;> simp [a, b] <;> ring

end SmoothForm

/-! ### Coordinate one-forms pulled back to an open subset `U ⊆ ℂ` -/

section OpenCoords

variable (U : Opens ℂ)

/-- Evaluation of the pullback of `dx` to an open subset `U ⊆ ℂ`. -/
theorem mpullback_subtype_val_complexDx_apply (z : U)
    (v : Fin 1 → TangentSpace 𝓘(ℝ, ℂ) z) :
    mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) SmoothForm.complexDx.1 z v =
      (NormedSpace.fromTangentSpace (z : ℂ) (Manifold.tangentSpaceOpenEquiv z (v 0))).re := by
  rw [mpullback_apply, SmoothForm.complexDx_apply]
  simp [Manifold.mfderiv_subtype_val]

/-- Evaluation of the pullback of `dy` to an open subset `U ⊆ ℂ`. -/
theorem mpullback_subtype_val_complexDy_apply (z : U)
    (v : Fin 1 → TangentSpace 𝓘(ℝ, ℂ) z) :
    mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) SmoothForm.complexDy.1 z v =
      (NormedSpace.fromTangentSpace (z : ℂ) (Manifold.tangentSpaceOpenEquiv z (v 0))).im := by
  rw [mpullback_apply, SmoothForm.complexDy_apply]
  simp [Manifold.mfderiv_subtype_val]

/-- Evaluation of the pullback of `dz` to an open subset `U ⊆ ℂ`. -/
theorem mpullback_subtype_val_complexDz_apply (z : U)
    (v : Fin 1 → TangentSpace 𝓘(ℝ, ℂ) z) :
    mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) SmoothForm.complexDz.1 z v =
      NormedSpace.fromTangentSpace (z : ℂ) (Manifold.tangentSpaceOpenEquiv z (v 0)) := by
  rw [mpullback_apply, SmoothForm.complexDz_apply]
  simp [Manifold.mfderiv_subtype_val]

/-- Evaluation of the pullback of `dbar z` to an open subset `U ⊆ ℂ`. -/
theorem mpullback_subtype_val_complexDzBar_apply (z : U)
    (v : Fin 1 → TangentSpace 𝓘(ℝ, ℂ) z) :
    mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) SmoothForm.complexDzBar.1 z v =
      conj (NormedSpace.fromTangentSpace (z : ℂ)
        (Manifold.tangentSpaceOpenEquiv z (v 0))) := by
  rw [mpullback_apply, SmoothForm.complexDzBar_apply]
  simp [Manifold.mfderiv_subtype_val]

/-- Evaluation of the pullback of `dx ∧ dy` to an open subset `U ⊆ ℂ`. -/
theorem mpullback_subtype_val_complexDx_wedge_complexDy_apply (z : U)
    (v w : TangentSpace 𝓘(ℝ, ℂ) z) :
    mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
        (RoughForm.wedge SmoothForm.complexDx.1 SmoothForm.complexDy.1) z ![v, w] =
      (NormedSpace.fromTangentSpace (z : ℂ) (Manifold.tangentSpaceOpenEquiv z v)).re *
          (NormedSpace.fromTangentSpace (z : ℂ) (Manifold.tangentSpaceOpenEquiv z w)).im -
        (NormedSpace.fromTangentSpace (z : ℂ) (Manifold.tangentSpaceOpenEquiv z w)).re *
          (NormedSpace.fromTangentSpace (z : ℂ) (Manifold.tangentSpaceOpenEquiv z v)).im := by
  rw [mpullback_apply]
  have hcomp :
      (fun i : Fin 2 ↦
        mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) z (![v, w] i)) =
        ![Manifold.tangentSpaceOpenEquiv z v, Manifold.tangentSpaceOpenEquiv z w] := by
    ext i
    fin_cases i <;> (rw [Manifold.mfderiv_subtype_val]; rfl)
  rw [hcomp, SmoothForm.complexDx_wedge_complexDy_apply]

/-- Evaluation of the pullback of `dz ∧ dbar z` to an open subset `U ⊆ ℂ`. -/
theorem mpullback_subtype_val_complexDz_wedgeWith_complexDzBar_apply (z : U)
    (v w : TangentSpace 𝓘(ℝ, ℂ) z) :
    mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
        (RoughForm.wedgeWith (ContinuousLinearMap.mul ℝ ℂ) SmoothForm.complexDz.1
          SmoothForm.complexDzBar.1) z ![v, w] =
      (-2 * Complex.I) *
        (((NormedSpace.fromTangentSpace (z : ℂ) (Manifold.tangentSpaceOpenEquiv z v)).re *
            (NormedSpace.fromTangentSpace (z : ℂ) (Manifold.tangentSpaceOpenEquiv z w)).im -
          (NormedSpace.fromTangentSpace (z : ℂ) (Manifold.tangentSpaceOpenEquiv z w)).re *
            (NormedSpace.fromTangentSpace (z : ℂ) (Manifold.tangentSpaceOpenEquiv z v)).im :
          ℝ) : ℂ) := by
  rw [mpullback_apply]
  have hcomp :
      (fun i : Fin 2 ↦
        mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) z (![v, w] i)) =
        ![Manifold.tangentSpaceOpenEquiv z v, Manifold.tangentSpaceOpenEquiv z w] := by
    ext i
    fin_cases i <;> (rw [Manifold.mfderiv_subtype_val]; rfl)
  rw [hcomp, SmoothForm.complexDz_wedgeWith_complexDzBar_apply,
    SmoothForm.complexDx_wedge_complexDy_apply]

/-- On an open subset `U ⊆ ℂ`, the pullback of `dx` is `d(Re ∘ ι)`. -/
theorem mpullback_subtype_val_complexDx_eq_mextDeriv :
    mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) SmoothForm.complexDx.1 =
      mextDeriv (RoughForm.ofFunction 𝓘(ℝ, ℂ) fun z : U ↦ (z : ℂ).re) := by
  rw [SmoothForm.complexDx_eq_mextDeriv]
  exact mpullback_mextDeriv_ofFunction
    (contMDiff_subtype_val.mdifferentiable one_ne_zero)
    ((contMDiff_iff_contDiff.2 (Complex.reCLM.contDiff (n := 1))).mdifferentiable one_ne_zero)

/-- On an open subset `U ⊆ ℂ`, the pullback of `dy` is `d(Im ∘ ι)`. -/
theorem mpullback_subtype_val_complexDy_eq_mextDeriv :
    mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) SmoothForm.complexDy.1 =
      mextDeriv (RoughForm.ofFunction 𝓘(ℝ, ℂ) fun z : U ↦ (z : ℂ).im) := by
  rw [SmoothForm.complexDy_eq_mextDeriv]
  exact mpullback_mextDeriv_ofFunction
    (contMDiff_subtype_val.mdifferentiable one_ne_zero)
    ((contMDiff_iff_contDiff.2 (Complex.imCLM.contDiff (n := 1))).mdifferentiable one_ne_zero)

/-- On an open subset `U ⊆ ℂ`, the pullback of `dz` is `d ι`. -/
theorem mpullback_subtype_val_complexDz_eq_mextDeriv :
    mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) SmoothForm.complexDz.1 =
      mextDeriv (RoughForm.ofFunction 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)) := by
  rw [SmoothForm.complexDz_eq_mextDeriv]
  exact mpullback_mextDeriv_ofFunction
    (contMDiff_subtype_val.mdifferentiable one_ne_zero) mdifferentiable_id

/-- On an open subset `U ⊆ ℂ`, the pullback of `dbar z` is `d(conj ∘ ι)`. -/
theorem mpullback_subtype_val_complexDzBar_eq_mextDeriv :
    mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) SmoothForm.complexDzBar.1 =
      mextDeriv (RoughForm.ofFunction 𝓘(ℝ, ℂ) fun z : U ↦ conj (z : ℂ)) := by
  rw [SmoothForm.complexDzBar_eq_mextDeriv]
  exact mpullback_mextDeriv_ofFunction
    (contMDiff_subtype_val.mdifferentiable one_ne_zero)
    ((contMDiff_iff_contDiff.2
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff (n := 1))).mdifferentiable one_ne_zero)

@[simp]
theorem mextDeriv_mpullback_subtype_val_complexDx :
    mextDeriv (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) SmoothForm.complexDx.1) =
      0 :=
  (SmoothForm.complexDx.isSmoothForm.of_le (by simp)).mextDeriv_mpullback_eq_zero
    SmoothForm.mextDeriv_complexDx contMDiff_subtype_val

@[simp]
theorem mextDeriv_mpullback_subtype_val_complexDy :
    mextDeriv (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) SmoothForm.complexDy.1) =
      0 :=
  (SmoothForm.complexDy.isSmoothForm.of_le (by simp)).mextDeriv_mpullback_eq_zero
    SmoothForm.mextDeriv_complexDy contMDiff_subtype_val

@[simp]
theorem mextDeriv_mpullback_subtype_val_complexDz :
    mextDeriv (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) SmoothForm.complexDz.1) =
      0 :=
  (SmoothForm.complexDz.isSmoothForm.of_le (by simp)).mextDeriv_mpullback_eq_zero
    SmoothForm.mextDeriv_complexDz contMDiff_subtype_val

@[simp]
theorem mextDeriv_mpullback_subtype_val_complexDzBar :
    mextDeriv (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) SmoothForm.complexDzBar.1) =
      0 :=
  (SmoothForm.complexDzBar.isSmoothForm.of_le (by simp)).mextDeriv_mpullback_eq_zero
    SmoothForm.mextDeriv_complexDzBar contMDiff_subtype_val

end OpenCoords

/-! ### Differential decompositions on an open subset `U ⊆ ℂ` -/

section Differentials

private theorem mvfderiv_opens_complex_eq_fderiv {U : Opens ℂ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {u : U → F} {u' : ℂ → F}
    (hu : ∀ z : U, u' z = u z) (z : U) (v : TangentSpace 𝓘(ℝ, ℂ) z) :
    mvfderiv 𝓘(ℝ, ℂ) u z v =
      fderiv ℝ u' (z : ℂ)
        (NormedSpace.fromTangentSpace (z : ℂ) (Manifold.tangentSpaceOpenEquiv z v)) := by
  have hcomp : u = u' ∘ (Subtype.val : U → ℂ) := funext fun y ↦ (hu y).symm
  rw [hcomp]
  by_cases hd : DifferentiableAt ℝ u' (z : ℂ)
  · rw [mvfderiv_comp_apply z hd.mdifferentiableAt
        (contMDiff_subtype_val.mdifferentiableAt one_ne_zero),
      Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe, mvfderiv_eq_fderiv,
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  · have hnot : ¬ MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, F) (u' ∘ (Subtype.val : U → ℂ)) z := by
      rw [Manifold.mdifferentiableAt_comp_subtype_val_iff,
        mdifferentiableAt_iff_differentiableAt]
      exact hd
    rw [mvfderiv_apply_eq_mfderiv_apply, mfderiv_zero_of_not_mdifferentiableAt hnot,
      fderiv_zero_of_not_differentiableAt hd]
    rfl

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
          (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) SmoothForm.complexDx.1) +
        RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℝ).flip
          (RoughForm.ofFunction 𝓘(ℝ, ℂ) fun z : U ↦ fderiv ℝ v' z Complex.I)
          (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
            SmoothForm.complexDy.1) := by
  ext z w
  rw [mextDeriv_ofFunction, ContinuousAlternatingMap.ofSubsingleton_apply_apply,
    Pi.add_apply, ContinuousAlternatingMap.add_apply, RoughForm.wedgeWith_apply',
    RoughForm.wedgeWith_apply', ContinuousAlternatingMap.pairedWedge_apply_zero_left,
    ContinuousAlternatingMap.pairedWedge_apply_zero_left]
  simp only [RoughForm.ofFunction_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lsmul_apply, mpullback_subtype_val_complexDx_apply,
    mpullback_subtype_val_complexDy_apply, Function.comp_apply, Fin.cast_refl, id_eq]
  rw [mvfderiv_opens_complex_eq_fderiv hv z (w 0)]
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
            SmoothForm.complexDz.1) +
        RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℂ).flip
          (RoughForm.ofFunction 𝓘(ℝ, ℂ) fun z : U ↦ conjWirtingerDeriv u' z 1)
          (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
            SmoothForm.complexDzBar.1) := by
  ext z w
  rw [mextDeriv_ofFunction, ContinuousAlternatingMap.ofSubsingleton_apply_apply,
    Pi.add_apply, ContinuousAlternatingMap.add_apply, RoughForm.wedgeWith_apply',
    RoughForm.wedgeWith_apply', ContinuousAlternatingMap.pairedWedge_apply_zero_left,
    ContinuousAlternatingMap.pairedWedge_apply_zero_left]
  simp only [RoughForm.ofFunction_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lsmul_apply, mpullback_subtype_val_complexDz_apply,
    mpullback_subtype_val_complexDzBar_apply, Function.comp_apply, Fin.cast_refl, id_eq]
  rw [mvfderiv_opens_complex_eq_fderiv hu z (w 0)]
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

@[simp]
theorem planarTwoFormCoeff_zero {U : Opens ℂ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (z : U) :
    planarTwoFormCoeff (0 : RoughForm 𝓘(ℝ, ℂ) U F 2) z = 0 := by
  simp [planarTwoFormCoeff]

@[simp]
theorem planarTwoFormCoeff_add {U : Opens ℂ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (η₁ η₂ : RoughForm 𝓘(ℝ, ℂ) U F 2) (z : U) :
    planarTwoFormCoeff (η₁ + η₂) z =
      planarTwoFormCoeff η₁ z + planarTwoFormCoeff η₂ z := by
  simp [planarTwoFormCoeff]

@[simp]
theorem planarTwoFormCoeff_smul {U : Opens ℂ} {R F : Type*} [Semiring R]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Module R F] [SMulCommClass ℝ R F]
    [ContinuousConstSMul R F] (c : R) (η : RoughForm 𝓘(ℝ, ℂ) U F 2) (z : U) :
    planarTwoFormCoeff (c • η) z = c • planarTwoFormCoeff η z := by
  simp [planarTwoFormCoeff]

/-- Every alternating two-form on `U ⊆ ℂ` with values in a real normed space `F` equals
`(planarTwoFormCoeff η) dx ∧ dy`. -/
theorem roughForm_two_eq_wedgeWith_dx_wedge_dy {U : Opens ℂ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (η : RoughForm 𝓘(ℝ, ℂ) U F 2) :
    η = RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℝ).flip
      (RoughForm.ofFunction 𝓘(ℝ, ℂ) (planarTwoFormCoeff η))
      (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
        (RoughForm.wedge SmoothForm.complexDx.1 SmoothForm.complexDy.1)) := by
  ext z v
  have hv : v = ![v 0, v 1] := funext fun i ↦ by fin_cases i <;> rfl
  rw [hv, RoughForm.wedgeWith_apply', ContinuousAlternatingMap.pairedWedge_apply_zero_left]
  simp only [RoughForm.ofFunction_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lsmul_apply]
  have hcast : (![v 0, v 1] ∘ Fin.cast (Nat.zero_add 2).symm) = ![v 0, v 1] := by
    ext i; fin_cases i <;> rfl
  rw [hcast, mpullback_subtype_val_complexDx_wedge_complexDy_apply]
  set e : TangentSpace 𝓘(ℝ, ℂ) z ≃L[ℝ] ℂ :=
    (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, ℂ)) z).trans
      (NormedSpace.fromTangentSpace (z : ℂ))
  set a : ℂ := e (v 0)
  set b : ℂ := e (v 1)
  have hv0 : v 0 = a.re • e.symm 1 + a.im • e.symm Complex.I := by
    apply e.injective
    simp only [map_add, map_smul, ContinuousLinearEquiv.apply_symm_apply]
    change a = a.re • (1 : ℂ) + a.im • Complex.I
    simp [Complex.real_smul]
  have hv1 : v 1 = b.re • e.symm 1 + b.im • e.symm Complex.I := by
    apply e.injective
    simp only [map_add, map_smul, ContinuousLinearEquiv.apply_symm_apply]
    change b = b.re • (1 : ℂ) + b.im • Complex.I
    simp [Complex.real_smul]
  have h00 : η z ![e.symm 1, e.symm 1] = 0 :=
    (η z).map_eq_zero_of_eq _ (i := 0) (j := 1) rfl (by decide)
  have h11 : η z ![e.symm Complex.I, e.symm Complex.I] = 0 :=
    (η z).map_eq_zero_of_eq _ (i := 0) (j := 1) rfl (by decide)
  have hswap : (![e.symm 1, e.symm Complex.I] ∘ Equiv.swap (0 : Fin 2) 1) =
      ![e.symm Complex.I, e.symm 1] := by
    ext i; fin_cases i <;> rfl
  have h10 : η z ![e.symm Complex.I, e.symm 1] = -η z ![e.symm 1, e.symm Complex.I] := by
    simpa [hswap] using
      (η z).map_swap ![e.symm 1, e.symm Complex.I] (i := 0) (j := 1) (by decide)
  have hupd0 (u w u' : TangentSpace 𝓘(ℝ, ℂ) z) :
      Function.update ![u, w] 0 u' = ![u', w] := by
    ext i; fin_cases i <;> simp
  have hupd1 (u w w' : TangentSpace 𝓘(ℝ, ℂ) z) :
      Function.update ![u, w] 1 w' = ![u, w'] := by
    ext i; fin_cases i <;> simp
  have hadd0 (u₁ u₂ w : TangentSpace 𝓘(ℝ, ℂ) z) :
      η z ![u₁ + u₂, w] = η z ![u₁, w] + η z ![u₂, w] := by
    simpa [hupd0] using (η z).map_update_add ![u₁, w] 0 u₁ u₂
  have hsmul0 (r : ℝ) (u w : TangentSpace 𝓘(ℝ, ℂ) z) :
      η z ![r • u, w] = r • η z ![u, w] := by
    simpa [hupd0] using (η z).map_update_smul ![u, w] 0 r u
  have hadd1 (u w₁ w₂ : TangentSpace 𝓘(ℝ, ℂ) z) :
      η z ![u, w₁ + w₂] = η z ![u, w₁] + η z ![u, w₂] := by
    simpa [hupd1] using (η z).map_update_add ![u, w₁] 1 w₁ w₂
  have hsmul1 (r : ℝ) (u w : TangentSpace 𝓘(ℝ, ℂ) z) :
      η z ![u, r • w] = r • η z ![u, w] := by
    simpa [hupd1] using (η z).map_update_smul ![u, w] 1 r w
  change η z ![v 0, v 1] = (a.re * b.im - b.re * a.im) • η z ![e.symm 1, e.symm Complex.I]
  rw [hv0, hv1, hadd0, hsmul0, hsmul0, hadd1, hadd1, hsmul1, hsmul1, hsmul1, hsmul1,
    h00, h11, h10, smul_zero, zero_add, smul_zero, add_zero, smul_neg, smul_neg,
    smul_smul, smul_smul, sub_smul, mul_comm a.im b.re, sub_eq_add_neg]

/-- Evaluating `(h dx ∧ dy)` at the positive coordinate frame recovers `h`. -/
@[simp]
theorem planarTwoFormCoeff_wedgeWith_dx_wedge_dy {U : Opens ℂ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (h : U → F) (z : U) :
    planarTwoFormCoeff
      (RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℝ).flip
        (RoughForm.ofFunction 𝓘(ℝ, ℂ) h)
        (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
          (RoughForm.wedge SmoothForm.complexDx.1 SmoothForm.complexDy.1))) z = h z := by
  rw [planarTwoFormCoeff, RoughForm.wedgeWith_apply',
    ContinuousAlternatingMap.pairedWedge_apply_zero_left]
  simp only [RoughForm.ofFunction_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lsmul_apply]
  set e₁ : TangentSpace 𝓘(ℝ, ℂ) z :=
    (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, ℂ)) z).symm
      ((NormedSpace.fromTangentSpace (z : ℂ)).symm 1)
  set eI : TangentSpace 𝓘(ℝ, ℂ) z :=
    (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, ℂ)) z).symm
      ((NormedSpace.fromTangentSpace (z : ℂ)).symm Complex.I)
  have hcast : (![e₁, eI] ∘ Fin.cast (Nat.zero_add 2).symm) = ![e₁, eI] := by
    ext i; fin_cases i <;> rfl
  rw [hcast, mpullback_subtype_val_complexDx_wedge_complexDy_apply]
  simp only [e₁, eI, ContinuousLinearEquiv.apply_symm_apply]
  simp

/-- Two planar `2`-forms on `U ⊆ ℂ` agree iff their `dx ∧ dy` coefficients agree. -/
theorem planarTwoFormCoeff_injective {U : Opens ℂ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    Function.Injective (planarTwoFormCoeff (U := U) (F := F)) := by
  intro η₁ η₂ h
  rw [roughForm_two_eq_wedgeWith_dx_wedge_dy η₁, roughForm_two_eq_wedgeWith_dx_wedge_dy η₂, h]

/-- Evaluating `(h dz ∧ dbar z)` at the positive coordinate frame gives `-2i • h`. -/
@[simp]
theorem planarTwoFormCoeff_wedgeWith_dz_wedge_dzBar {U : Opens ℂ} {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℂ W] (h : U → W) (z : U) :
    planarTwoFormCoeff
      (RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℂ).flip
        (RoughForm.ofFunction 𝓘(ℝ, ℂ) h)
        (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
          (RoughForm.wedgeWith (ContinuousLinearMap.mul ℝ ℂ)
            SmoothForm.complexDz.1 SmoothForm.complexDzBar.1))) z = (-2 * Complex.I) • h z := by
  rw [planarTwoFormCoeff, RoughForm.wedgeWith_apply',
    ContinuousAlternatingMap.pairedWedge_apply_zero_left]
  simp only [RoughForm.ofFunction_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lsmul_apply]
  set e₁ : TangentSpace 𝓘(ℝ, ℂ) z :=
    (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, ℂ)) z).symm
      ((NormedSpace.fromTangentSpace (z : ℂ)).symm 1)
  set eI : TangentSpace 𝓘(ℝ, ℂ) z :=
    (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, ℂ)) z).symm
      ((NormedSpace.fromTangentSpace (z : ℂ)).symm Complex.I)
  have hcast : (![e₁, eI] ∘ Fin.cast (Nat.zero_add 2).symm) = ![e₁, eI] := by
    ext i; fin_cases i <;> rfl
  rw [hcast, mpullback_subtype_val_complexDz_wedgeWith_complexDzBar_apply]
  simp only [e₁, eI, ContinuousLinearEquiv.apply_symm_apply]
  simp

/-- Every alternating two-form on `U ⊆ ℂ` with values in a complex normed space `W` equals
`((-2i)⁻¹ • planarTwoFormCoeff η) dz ∧ dbar z`. -/
theorem roughForm_two_eq_wedgeWith_dz_wedge_dzBar {U : Opens ℂ} {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℂ W] (η : RoughForm 𝓘(ℝ, ℂ) U W 2) :
    η = RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℂ).flip
      (RoughForm.ofFunction 𝓘(ℝ, ℂ) fun z : U ↦
        (-2 * Complex.I)⁻¹ • planarTwoFormCoeff η z)
      (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
        (RoughForm.wedgeWith (ContinuousLinearMap.mul ℝ ℂ)
          SmoothForm.complexDz.1 SmoothForm.complexDzBar.1)) := by
  apply planarTwoFormCoeff_injective
  funext z
  rw [planarTwoFormCoeff_wedgeWith_dz_wedge_dzBar, smul_smul,
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
  rw [planarTwoFormCoeff]
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
  ((hα.mpullback (contMDiff_subtype_val (n := ∞))).contMDiff z).mdifferentiableAt (by simp)

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
          SmoothForm.complexDz.1))) z =
      (2 * Complex.I) • conjWirtingerDeriv g' z 1 := by
  rw [planarTwoFormCoeff,
    mextDeriv_wedgeWith (ContinuousLinearMap.lsmul ℝ ℂ).flip (mdifferentiableAt_ofFunction hg)
      (mdifferentiableAt_mpullback_subtype_val SmoothForm.complexDz.isSmoothForm z),
    mextDeriv_mpullback_subtype_val_complexDz, RoughForm.wedgeWith_zero_right]
  simp only [Pi.zero_apply, ContinuousAlternatingMap.coe_zero, smul_zero, add_zero]
  set e₁ : TangentSpace 𝓘(ℝ, ℂ) z :=
    (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, ℂ)) z).symm
      ((NormedSpace.fromTangentSpace (z : ℂ)).symm 1)
  set eI : TangentSpace 𝓘(ℝ, ℂ) z :=
    (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, ℂ)) z).symm
      ((NormedSpace.fromTangentSpace (z : ℂ)).symm Complex.I)
  have hcast : (![e₁, eI] ∘ Fin.cast (show 0 + 1 + 1 = 0 + 1 + 1 by omega)) = ![e₁, eI] := rfl
  rw [hcast, RoughForm.wedgeWith_apply_one_one]
  simp only [mextDeriv_ofFunction, ContinuousAlternatingMap.ofSubsingleton_apply_apply,
    Matrix.cons_val_zero, mpullback_subtype_val_complexDz_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply,
    mvfderiv_opens_complex_eq_fderiv hg_eq]
  have he1 :
      NormedSpace.fromTangentSpace (z : ℂ) (Manifold.tangentSpaceOpenEquiv z e₁) = 1 := by
    simp only [e₁, ContinuousLinearEquiv.apply_symm_apply]
  have heI : NormedSpace.fromTangentSpace (z : ℂ) (Manifold.tangentSpaceOpenEquiv z eI) =
      Complex.I := by
    simp only [eI, ContinuousLinearEquiv.apply_symm_apply]
  rw [he1, heI, conjWirtingerDeriv_apply, smul_smul, smul_add, smul_smul, smul_eq_mul, mul_one]
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
          SmoothForm.complexDzBar.1))) z =
      (-2 * Complex.I) • wirtingerDeriv f' z 1 := by
  rw [planarTwoFormCoeff,
    mextDeriv_wedgeWith (ContinuousLinearMap.lsmul ℝ ℂ).flip (mdifferentiableAt_ofFunction hf)
      (mdifferentiableAt_mpullback_subtype_val SmoothForm.complexDzBar.isSmoothForm z),
    mextDeriv_mpullback_subtype_val_complexDzBar, RoughForm.wedgeWith_zero_right]
  simp only [Pi.zero_apply, ContinuousAlternatingMap.coe_zero, smul_zero, add_zero]
  set e₁ : TangentSpace 𝓘(ℝ, ℂ) z :=
    (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, ℂ)) z).symm
      ((NormedSpace.fromTangentSpace (z : ℂ)).symm 1)
  set eI : TangentSpace 𝓘(ℝ, ℂ) z :=
    (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, ℂ)) z).symm
      ((NormedSpace.fromTangentSpace (z : ℂ)).symm Complex.I)
  have hcast : (![e₁, eI] ∘ Fin.cast (show 0 + 1 + 1 = 0 + 1 + 1 by omega)) = ![e₁, eI] := rfl
  rw [hcast, RoughForm.wedgeWith_apply_one_one]
  simp only [mextDeriv_ofFunction, ContinuousAlternatingMap.ofSubsingleton_apply_apply,
    Matrix.cons_val_zero, mpullback_subtype_val_complexDzBar_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply,
    mvfderiv_opens_complex_eq_fderiv hf_eq]
  have he1 :
      NormedSpace.fromTangentSpace (z : ℂ) (Manifold.tangentSpaceOpenEquiv z e₁) = 1 := by
    simp only [e₁, ContinuousLinearEquiv.apply_symm_apply]
  have heI : NormedSpace.fromTangentSpace (z : ℂ) (Manifold.tangentSpaceOpenEquiv z eI) =
      Complex.I := by
    simp only [eI, ContinuousLinearEquiv.apply_symm_apply]
  rw [he1, heI, conj_I, (starRingEnd ℂ).map_one, wirtingerDeriv_apply, smul_smul, smul_sub,
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
              SmoothForm.complexDx.1) +
          RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℝ).flip
            (RoughForm.ofFunction 𝓘(ℝ, ℂ) b)
            (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
              SmoothForm.complexDy.1))) z =
      fderiv ℝ b' z 1 - fderiv ℝ a' z Complex.I := by
  rw [planarTwoFormCoeff,
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
  simp only [Pi.zero_apply, ContinuousAlternatingMap.coe_zero, smul_zero, add_zero]
  set e₁ : TangentSpace 𝓘(ℝ, ℂ) z :=
    (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, ℂ)) z).symm
      ((NormedSpace.fromTangentSpace (z : ℂ)).symm 1)
  set eI : TangentSpace 𝓘(ℝ, ℂ) z :=
    (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, ℂ)) z).symm
      ((NormedSpace.fromTangentSpace (z : ℂ)).symm Complex.I)
  have hcast : (![e₁, eI] ∘ Fin.cast (show 0 + 1 + 1 = 0 + 1 + 1 by omega)) = ![e₁, eI] := rfl
  rw [hcast, RoughForm.wedgeWith_apply_one_one, RoughForm.wedgeWith_apply_one_one]
  simp only [mextDeriv_ofFunction, ContinuousAlternatingMap.ofSubsingleton_apply_apply,
    Matrix.cons_val_zero, mpullback_subtype_val_complexDx_apply,
    mpullback_subtype_val_complexDy_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lsmul_apply, mvfderiv_opens_complex_eq_fderiv ha_eq,
    mvfderiv_opens_complex_eq_fderiv hb_eq]
  have he1 :
      NormedSpace.fromTangentSpace (z : ℂ) (Manifold.tangentSpaceOpenEquiv z e₁) = 1 := by
    simp only [e₁, ContinuousLinearEquiv.apply_symm_apply]
  have heI : NormedSpace.fromTangentSpace (z : ℂ) (Manifold.tangentSpaceOpenEquiv z eI) =
      Complex.I := by
    simp only [eI, ContinuousLinearEquiv.apply_symm_apply]
  rw [he1, heI]
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
              SmoothForm.complexDz.1) +
          RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℂ).flip
            (RoughForm.ofFunction 𝓘(ℝ, ℂ) f)
            (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
              SmoothForm.complexDzBar.1)) = 0 := by
  let f' : ℂ → W := Subtype.val.extend f 0
  have hf'_eq (z : U) : f' z = f z := Subtype.val_injective.extend_apply f 0 z
  have hf' : ContDiffOn ℝ n f' (U : Set ℂ) := fun z hz ↦
    (contMDiffAt_iff_contDiffAt.1 ((hf ⟨z, hz⟩).extend_subtypeVal 0)).contDiffWithinAt
  obtain ⟨g', hg', hsol⟩ :=
    exists_contDiffOn_conjWirtingerDeriv_eq_wirtingerDeriv hm hmn U.isOpen hf'
  let g : U → W := fun z ↦ g' z
  have hg : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, W) m g := fun z ↦
    contMDiffAt_subtype_iff.2
      (contMDiffAt_iff_contDiffAt.2 (hg'.contDiffAt (U.isOpen.mem_nhds z.2)))
  refine ⟨g, hg, ?_⟩
  apply planarTwoFormCoeff_injective
  funext z
  have hgd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, W) g z :=
    (hg z).mdifferentiableAt (by exact_mod_cast (zero_lt_one.trans_le hm).ne')
  have hfd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, W) f z :=
    (hf z).mdifferentiableAt (by
      exact_mod_cast (zero_lt_one.trans_le (hm.trans (le_self_add.trans hmn))).ne')
  rw [planarTwoFormCoeff, planarTwoFormCoeff_zero,
    mextDeriv_add
      (differentiableWithinAt_inChartAt_wedgeWith_ofFunction _ hgd
        SmoothForm.complexDz.isSmoothForm)
      (differentiableWithinAt_inChartAt_wedgeWith_ofFunction _ hfd
        SmoothForm.complexDzBar.isSmoothForm),
    ContinuousAlternatingMap.add_apply]
  change planarTwoFormCoeff (mextDeriv _) z + planarTwoFormCoeff (mextDeriv _) z = 0
  rw [planarTwoFormCoeff_mextDeriv_wedgeWith_complexDz (g' := g') (fun _ ↦ rfl) hgd,
    planarTwoFormCoeff_mextDeriv_wedgeWith_complexDzBar hf'_eq hfd, hsol z z.2, ← add_smul]
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
              SmoothForm.complexDz.1) +
          RoughForm.wedgeWith (ContinuousLinearMap.mul ℝ ℂ)
            (RoughForm.ofFunction 𝓘(ℝ, ℂ) f)
            (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ)
              SmoothForm.complexDzBar.1)) = 0 := by
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
            SmoothForm.complexDz.1)) = η := by
  let L : W →L[ℝ] W :=
    ((2 * Complex.I)⁻¹ • ContinuousLinearMap.id ℂ W).restrictScalars ℝ
  let h : U → W := fun z ↦ L (planarTwoFormCoeff η z)
  have hh : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, W) n h :=
    (contMDiff_iff_contDiff.2 L.contDiff).comp hη.contMDiff_planarTwoFormCoeff
  let h' : ℂ → W := Subtype.val.extend h 0
  have hh'_eq (z : U) : h' z = h z := Subtype.val_injective.extend_apply h 0 z
  have hh' : ContDiffOn ℝ n h' (U : Set ℂ) := fun z hz ↦
    (contMDiffAt_iff_contDiffAt.1 ((hh ⟨z, hz⟩).extend_subtypeVal 0)).contDiffWithinAt
  obtain ⟨g', hg', hsol⟩ :=
    exists_contDiffOn_conjWirtingerDeriv_apply_one_eq hn U.isOpen hh'
  let g : U → W := fun z ↦ g' z
  have hg : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, W) n g := fun z ↦
    contMDiffAt_subtype_iff.2
      (contMDiffAt_iff_contDiffAt.2 (hg'.contDiffAt (U.isOpen.mem_nhds z.2)))
  refine ⟨g, hg, ?_⟩
  apply planarTwoFormCoeff_injective
  funext z
  have hgd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, W) g z :=
    (hg z).mdifferentiableAt (by exact_mod_cast (zero_lt_one.trans_le hn).ne')
  rw [planarTwoFormCoeff_mextDeriv_wedgeWith_complexDz (g := g) (g' := g') (fun _ ↦ rfl) hgd,
    hsol z z.2, hh'_eq z]
  have hne : (2 * Complex.I : ℂ) ≠ 0 := by simp [Complex.I_ne_zero]
  change
    (2 * Complex.I) • ((2 * Complex.I)⁻¹ • planarTwoFormCoeff η z) = planarTwoFormCoeff η z
  rw [smul_smul, mul_inv_cancel₀ hne, one_smul]

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
  set dz := mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : U → ℂ) SmoothForm.complexDz.1
  let βℂ : RoughForm 𝓘(ℝ, ℂ) U (Complexification F) 1 :=
    RoughForm.wedgeWith (ContinuousLinearMap.lsmul ℝ ℂ).flip
      (RoughForm.ofFunction 𝓘(ℝ, ℂ) g) dz
  have hβℂ : IsSmoothForm 𝓘(ℝ, ℂ) n βℂ := by
    have hdz : IsSmoothForm 𝓘(ℝ, ℂ) n dz :=
      (SmoothForm.complexDz.isSmoothForm.mpullback
        (contMDiff_subtype_val (n := ∞))).of_le (by simp)
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
