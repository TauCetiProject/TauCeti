/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Lift
public import TauCeti.Geometry.Manifold.Algebra.ComplexSmoothFunctions
public import TauCeti.Geometry.Manifold.VectorField.Derivation

/-!
# Complex derivations are complexified vector fields

Let `A = C^n(M, ℝ)` and `A_ℂ = C^n(M, ℂ)` be the real-smooth real- and complex-valued functions
on a real manifold `M`. A complex-linear derivation `δ` of `A_ℂ` is determined by its values on
real functions, and there it splits into real and imaginary parts `δ u = D₁ u + i D₂ u`, where
`D₁ = δ.re` and `D₂ = δ.im` are derivations of `A`. Conversely every derivation `D` of `A` extends
complex-linearly to `D.complexify`, with `D.complexify (u + i v) = D u + i D v`. Together these
identify the complex derivations of `A_ℂ` with the complexification `ℂ ⊗[ℝ] Der(A)`, the derivation
`δ` corresponding to `1 ⊗ δ.re + i ⊗ δ.im`; this uses no smoothness or dimension assumptions.

On a finite-dimensional, Hausdorff, boundaryless real manifold, derivations of `C^∞(M, ℝ)` are
smooth vector fields (`TauCeti.derivationEquivSmoothVectorField`). Composing gives the complexified
derivation dictionary: complex derivations of `C^∞(M, ℂ)` are complex-linearly equivalent to
`ℂ ⊗[ℝ] Γ∞(TM)`, the derivation `δ` going to `1 ⊗ X + i ⊗ Y` exactly when `δ u = X u + i Y u` for
real smooth `u`, equivalently `δ (u + i v) = X u - Y v + i (Y u + X v)`. No continuity of the
derivations is assumed.

## Main definitions

* `Derivation.re`, `Derivation.im`: the real derivations `u ↦ Re (δ u)` and `u ↦ Im (δ u)` of a
  complex derivation `δ`.
* `Derivation.complexify`: the complex-linear extension of a real derivation, and
  `Derivation.complexifyLinearMap`, the same as a real-linear map.
* `TauCeti.complexDerivationEquivComplexifiedDerivation`: complex derivations of `C^n(M, ℂ)` are
  the complexification of the real derivations of `C^n(M, ℝ)`.
* `TauCeti.complexDerivationEquivComplexifiedVectorField`: complex derivations of `C^∞(M, ℂ)` are
  complexified smooth vector fields.

## Main results

* `Derivation.ext_re_im`: a complex derivation is determined by its real and imaginary parts.
* `Derivation.re_lie`, `Derivation.im_lie`: the commutator of complex derivations has the parts
  of the complexified bracket,
  `[X₁ + i Y₁, X₂ + i Y₂] = [X₁, X₂] - [Y₁, Y₂] + i ([X₁, Y₂] + [Y₁, X₂])`; in terms of vector
  fields and the manifold Lie bracket these are `Derivation.vectorField_re_lie` and
  `Derivation.vectorField_im_lie`.
* `TauCeti.complexDerivationEquivComplexifiedVectorField_eq_iff`: the equivalence sends `δ` to
  `1 ⊗ X + i ⊗ Y` exactly when `δ u = X u + i Y u` for every real smooth `u`.
* `TauCeti.complexDerivationEquivComplexifiedVectorField_symm_apply_apply`: the inverse formula
  `δ (u + i v) = X u - Y v + i (Y u + X v)`.
* `TauCeti.exists_complexDerivationEquivComplexifiedVectorField`: the existence of such an
  equivalence.
-/

public section

noncomputable section

open scoped Manifold ContDiff TensorProduct

open ContMDiffMap VectorField

namespace Derivation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

section ComplexDerivation

variable (δ : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯)

/-- The real part of a complex derivation `δ` of complex-valued smooth functions, as a derivation
of real-valued smooth functions: `u ↦ Re (δ u)`. -/
def re : Derivation ℝ C^n⟮I, M; ℝ⟯ C^n⟮I, M; ℝ⟯ :=
  Derivation.mk' (ContMDiffMap.re ∘ₗ (δ : _ →ₗ[ℂ] _).restrictScalars ℝ ∘ₗ ofReal.toLinearMap)
    fun u v ↦ by simp [mul_re]

/-- The imaginary part of a complex derivation `δ` of complex-valued smooth functions, as a
derivation of real-valued smooth functions: `u ↦ Im (δ u)`. -/
def im : Derivation ℝ C^n⟮I, M; ℝ⟯ C^n⟮I, M; ℝ⟯ :=
  Derivation.mk' (ContMDiffMap.im ∘ₗ (δ : _ →ₗ[ℂ] _).restrictScalars ℝ ∘ₗ ofReal.toLinearMap)
    fun u v ↦ by simp [mul_im]

/-- The real part of a complex derivation is `u ↦ Re (δ u)`. -/
theorem re_apply (u : C^n⟮I, M; ℝ⟯) : δ.re u = (δ (ofReal u)).re :=
  (rfl)

/-- The imaginary part of a complex derivation is `u ↦ Im (δ u)`. -/
theorem im_apply (u : C^n⟮I, M; ℝ⟯) : δ.im u = (δ (ofReal u)).im :=
  (rfl)

/-- On real functions a complex derivation is its real part plus `i` times its imaginary part. -/
theorem apply_ofReal (u : C^n⟮I, M; ℝ⟯) :
    δ (ofReal u) = ofReal (δ.re u) + Complex.I • ofReal (δ.im u) :=
  (ofReal_re_add_I_smul_im _).symm

/-- The real part of `δ (u + i v)` is `δ.re u - δ.im v`. -/
@[simp]
theorem apply_re (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) : (δ f).re = δ.re f.re - δ.im f.im := by
  conv_lhs => rw [← ofReal_re_add_I_smul_im f, map_add, map_smul, apply_ofReal, apply_ofReal]
  simp [sub_eq_add_neg]

/-- The imaginary part of `δ (u + i v)` is `δ.re v + δ.im u`. -/
@[simp]
theorem apply_im (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) : (δ f).im = δ.re f.im + δ.im f.re := by
  conv_lhs => rw [← ofReal_re_add_I_smul_im f, map_add, map_smul, apply_ofReal, apply_ofReal]
  simp [add_comm]

/-- A complex derivation is determined by its real and imaginary parts. -/
theorem ext_re_im {δ₁ δ₂ : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯}
    (hre : δ₁.re = δ₂.re) (him : δ₁.im = δ₂.im) : δ₁ = δ₂ := by
  ext1 f
  exact ContMDiffMap.ext_re_im (by simp [hre, him]) (by simp [hre, him])

/-- Two complex derivations are equal exactly when their real and imaginary parts are. -/
theorem ext_re_im_iff {δ₁ δ₂ : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯} :
    δ₁ = δ₂ ↔ δ₁.re = δ₂.re ∧ δ₁.im = δ₂.im :=
  ⟨fun h ↦ by simp [h], fun h ↦ ext_re_im h.1 h.2⟩

@[simp]
theorem re_zero : (0 : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯).re = 0 := by
  ext1 u
  rw [re_apply]
  simp

@[simp]
theorem im_zero : (0 : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯).im = 0 := by
  ext1 u
  rw [im_apply]
  simp

@[simp]
theorem re_add (δ₁ δ₂ : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    (δ₁ + δ₂).re = δ₁.re + δ₂.re := by
  ext1 u
  rw [re_apply (δ₁ + δ₂)]
  simp

@[simp]
theorem im_add (δ₁ δ₂ : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    (δ₁ + δ₂).im = δ₁.im + δ₂.im := by
  ext1 u
  rw [im_apply (δ₁ + δ₂)]
  simp

@[simp]
theorem re_smul (r : ℝ) : (r • δ).re = r • δ.re := by
  ext1 u
  rw [re_apply (r • δ)]
  simp

@[simp]
theorem im_smul (r : ℝ) : (r • δ).im = r • δ.im := by
  ext1 u
  rw [im_apply (r • δ)]
  simp

/-- The real part of a complex multiple of a complex derivation. -/
@[simp]
theorem re_complex_smul (z : ℂ) : (z • δ).re = z.re • δ.re - z.im • δ.im := by
  ext1 u
  rw [re_apply (z • δ)]
  simp

/-- The imaginary part of a complex multiple of a complex derivation. -/
@[simp]
theorem im_complex_smul (z : ℂ) : (z • δ).im = z.re • δ.im + z.im • δ.re := by
  ext1 u
  rw [im_apply (z • δ)]
  simp

/-- Multiplying a complex derivation by a real function multiplies its real part. -/
@[simp]
theorem re_ofReal_smul (g : C^n⟮I, M; ℝ⟯) : (ofReal g • δ).re = g • δ.re := by
  ext1 u
  rw [re_apply (ofReal g • δ)]
  simp [mul_re]

/-- Multiplying a complex derivation by a real function multiplies its imaginary part. -/
@[simp]
theorem im_ofReal_smul (g : C^n⟮I, M; ℝ⟯) : (ofReal g • δ).im = g • δ.im := by
  ext1 u
  rw [im_apply (ofReal g • δ)]
  simp [mul_im]

/-- **Commutators of complex derivations, real part.** The real part of `[δ₁, δ₂]` is
`[δ₁.re, δ₂.re] - [δ₁.im, δ₂.im]`. -/
theorem re_lie (δ₁ δ₂ : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    ⁅δ₁, δ₂⁆.re = ⁅δ₁.re, δ₂.re⁆ - ⁅δ₁.im, δ₂.im⁆ := by
  ext1 u
  rw [re_apply ⁅δ₁, δ₂⁆, commutator_apply, map_sub]
  simp [commutator_apply]
  abel

/-- **Commutators of complex derivations, imaginary part.** The imaginary part of `[δ₁, δ₂]` is
`[δ₁.re, δ₂.im] + [δ₁.im, δ₂.re]`. -/
theorem im_lie (δ₁ δ₂ : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    ⁅δ₁, δ₂⁆.im = ⁅δ₁.re, δ₂.im⁆ + ⁅δ₁.im, δ₂.re⁆ := by
  ext1 u
  rw [im_apply ⁅δ₁, δ₂⁆, commutator_apply, map_sub]
  simp [commutator_apply]
  abel

end ComplexDerivation

section Complexify

variable (D : Derivation ℝ C^n⟮I, M; ℝ⟯ C^n⟮I, M; ℝ⟯)

/-- The complex-linear extension of a derivation `D` of real-valued smooth functions to the
complex-valued ones: `D.complexify (u + i v) = D u + i D v`. -/
def complexify : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ :=
  Derivation.mk'
    { toFun f := ofReal (D f.re) + Complex.I • ofReal (D f.im)
      map_add' f g := by
        simp only [map_add, smul_add]
        abel
      map_smul' z f := by
        ext x
        apply Complex.ext <;> simp <;> ring }
    fun f g ↦ by
      ext x
      apply Complex.ext <;> simp [mul_re, mul_im] <;> ring

@[simp]
theorem complexify_apply (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    D.complexify f = ofReal (D f.re) + Complex.I • ofReal (D f.im) :=
  (rfl)

/-- The complex-linear extension of a real derivation agrees with it on real functions. -/
theorem complexify_ofReal (u : C^n⟮I, M; ℝ⟯) : D.complexify (ofReal u) = ofReal (D u) := by
  simp

@[simp]
theorem re_complexify : D.complexify.re = D := by
  ext1 u
  rw [re_apply]
  simp

@[simp]
theorem im_complexify : D.complexify.im = 0 := by
  ext1 u
  rw [im_apply]
  simp

@[simp]
theorem complexify_add (D₁ D₂ : Derivation ℝ C^n⟮I, M; ℝ⟯ C^n⟮I, M; ℝ⟯) :
    (D₁ + D₂).complexify = D₁.complexify + D₂.complexify :=
  ext_re_im (by simp) (by simp)

@[simp]
theorem complexify_smul (r : ℝ) : (r • D).complexify = r • D.complexify :=
  ext_re_im (by simp) (by simp)

/-- The complexification of real derivations preserves commutators. -/
@[simp]
theorem complexify_lie (D₁ D₂ : Derivation ℝ C^n⟮I, M; ℝ⟯ C^n⟮I, M; ℝ⟯) :
    ⁅D₁, D₂⁆.complexify = ⁅D₁.complexify, D₂.complexify⁆ :=
  ext_re_im (by rw [re_lie]; simp) (by rw [im_lie]; ext1; simp [commutator_apply])

/-- The complexification of derivations of real-valued smooth functions, as a real-linear map
into the complex derivations of complex-valued smooth functions. -/
def complexifyLinearMap :
    Derivation ℝ C^n⟮I, M; ℝ⟯ C^n⟮I, M; ℝ⟯ →ₗ[ℝ]
      Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ where
  toFun := Derivation.complexify
  map_add' := complexify_add
  map_smul' r D := complexify_smul D r

@[simp]
theorem complexifyLinearMap_apply (D : Derivation ℝ C^n⟮I, M; ℝ⟯ C^n⟮I, M; ℝ⟯) :
    complexifyLinearMap D = D.complexify :=
  (rfl)

end Complexify

end Derivation

namespace TauCeti

open Derivation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

/-- **Complex derivations are complexified real derivations.** Complex-linear derivations of the
complex-valued smooth functions `C^n(M, ℂ)` correspond complex-linearly to the complexification
`ℂ ⊗[ℝ] Der(C^n(M, ℝ))` of the real derivations, a complex derivation `δ` going to
`1 ⊗ δ.re + i ⊗ δ.im`; the inverse sends `z ⊗ D` to `z • D.complexify`. -/
def complexDerivationEquivComplexifiedDerivation :
    Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ ≃ₗ[ℂ]
      ℂ ⊗[ℝ] Derivation ℝ C^n⟮I, M; ℝ⟯ C^n⟮I, M; ℝ⟯ :=
  LinearEquiv.symm
    { toLinearMap := complexifyLinearMap.liftBaseChange ℂ
      invFun δ := 1 ⊗ₜ δ.re + Complex.I ⊗ₜ δ.im
      left_inv t := by
        induction t using TensorProduct.inductionOn with
        | tmul z D =>
          simp only [LinearMap.toFun_eq_coe, LinearMap.liftBaseChange_tmul,
            complexifyLinearMap_apply, re_complex_smul, im_complex_smul, re_complexify,
            im_complexify, smul_zero, sub_zero, zero_add]
          rw [← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.add_tmul]
          congr 1
          simpa [mul_comm] using z.re_add_im
        | add t₁ t₂ h₁ h₂ =>
          simp only [LinearMap.toFun_eq_coe] at h₁ h₂ ⊢
          rw [map_add, re_add, im_add, TensorProduct.tmul_add, TensorProduct.tmul_add,
            add_add_add_comm, h₁, h₂]
      right_inv δ := ext_re_im (by simp) (by simp) }

/-- The complex derivation dictionary sends `δ` to `1 ⊗ δ.re + i ⊗ δ.im`. -/
@[simp]
theorem complexDerivationEquivComplexifiedDerivation_apply
    (δ : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    complexDerivationEquivComplexifiedDerivation δ = 1 ⊗ₜ δ.re + Complex.I ⊗ₜ δ.im :=
  (rfl)

/-- The inverse of the complex derivation dictionary sends `z ⊗ D` to `z • D.complexify`. -/
@[simp]
theorem complexDerivationEquivComplexifiedDerivation_symm_tmul (z : ℂ)
    (D : Derivation ℝ C^n⟮I, M; ℝ⟯ C^n⟮I, M; ℝ⟯) :
    complexDerivationEquivComplexifiedDerivation.symm (z ⊗ₜ D) = z • D.complexify :=
  (rfl)

/-- The complex derivation dictionary sends `δ` to `1 ⊗ D₁ + i ⊗ D₂` exactly when
`δ u = D₁ u + i D₂ u` for every real smooth function `u`. -/
theorem complexDerivationEquivComplexifiedDerivation_eq_iff
    (δ : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯)
    (D₁ D₂ : Derivation ℝ C^n⟮I, M; ℝ⟯ C^n⟮I, M; ℝ⟯) :
    complexDerivationEquivComplexifiedDerivation δ = 1 ⊗ₜ D₁ + Complex.I ⊗ₜ D₂ ↔
      ∀ u, δ (ofReal u) = ofReal (D₁ u) + Complex.I • ofReal (D₂ u) := by
  rw [← LinearEquiv.eq_symm_apply, map_add,
    complexDerivationEquivComplexifiedDerivation_symm_tmul,
    complexDerivationEquivComplexifiedDerivation_symm_tmul, one_smul]
  refine ⟨fun h u ↦ by simp [h], fun h ↦ ext_re_im ?_ ?_⟩ <;> ext1 u
  · rw [Derivation.re_apply, h]
    simp
  · rw [Derivation.im_apply, h]
    simp

section VectorField

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]

/-- **Complex derivations are complexified vector fields.** On a finite-dimensional, Hausdorff,
boundaryless real manifold, complex-linear derivations of `C^∞(M, ℂ)` correspond complex-linearly
to `ℂ ⊗[ℝ] Γ∞(TM)`: a derivation `δ` goes to `1 ⊗ X + i ⊗ Y`, where `X` and `Y` are the vector
fields of its real and imaginary parts. No continuity of the derivations is assumed. -/
def complexDerivationEquivComplexifiedVectorField :
    Derivation ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ ≃ₗ[ℂ]
      ℂ ⊗[ℝ] Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  complexDerivationEquivComplexifiedDerivation.trans
    (LinearEquiv.baseChange ℝ ℂ _ _ (derivationEquivSmoothVectorField.restrictScalars ℝ))

@[simp]
theorem complexDerivationEquivComplexifiedVectorField_apply
    (δ : Derivation ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    complexDerivationEquivComplexifiedVectorField δ =
      1 ⊗ₜ derivationEquivSmoothVectorField δ.re +
        Complex.I ⊗ₜ derivationEquivSmoothVectorField δ.im := by
  simp [complexDerivationEquivComplexifiedVectorField]

@[simp]
theorem complexDerivationEquivComplexifiedVectorField_symm_tmul (z : ℂ)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    complexDerivationEquivComplexifiedVectorField.symm (z ⊗ₜ X) =
      z • (vectorFieldDerivation X).complexify := by
  simp [complexDerivationEquivComplexifiedVectorField]

/-- The complexified derivation dictionary sends `δ` to `1 ⊗ X + i ⊗ Y` exactly when
`δ u = X u + i Y u` for every real smooth function `u`. -/
theorem complexDerivationEquivComplexifiedVectorField_eq_iff
    (δ : Derivation ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯)
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    complexDerivationEquivComplexifiedVectorField δ = 1 ⊗ₜ X + Complex.I ⊗ₜ Y ↔
      ∀ (u : C^∞⟮I, M; ℝ⟯) (x : M),
        δ (ofReal u) x = (mvfderiv I u x (X x) : ℂ) + (mvfderiv I u x (Y x) : ℂ) * Complex.I := by
  have hXY : (1 : ℂ) ⊗ₜ[ℝ] X + Complex.I ⊗ₜ[ℝ] Y =
      LinearEquiv.baseChange ℝ ℂ _ _ (derivationEquivSmoothVectorField.restrictScalars ℝ)
        (1 ⊗ₜ derivationEquivSmoothVectorField.symm X +
          Complex.I ⊗ₜ derivationEquivSmoothVectorField.symm Y) := by
    simp only [map_add, LinearEquiv.baseChange_tmul, LinearEquiv.restrictScalars_apply,
      LinearEquiv.apply_symm_apply]
  rw [complexDerivationEquivComplexifiedVectorField, LinearEquiv.trans_apply, hXY,
    (LinearEquiv.injective _).eq_iff, complexDerivationEquivComplexifiedDerivation_eq_iff]
  refine forall_congr' fun u ↦ ?_
  rw [DFunLike.ext_iff]
  simp [mul_comm]

/-- **The inverse formula.** The complex derivation corresponding to `1 ⊗ X + i ⊗ Y` sends
`f = u + i v` to `X u - Y v + i (Y u + X v)`. -/
theorem complexDerivationEquivComplexifiedVectorField_symm_apply_apply
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (f : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) (x : M) :
    complexDerivationEquivComplexifiedVectorField.symm (1 ⊗ₜ X + Complex.I ⊗ₜ Y) f x =
      (mvfderiv I f.re x (X x) - mvfderiv I f.im x (Y x) : ℝ) +
        (mvfderiv I f.re x (Y x) + mvfderiv I f.im x (X x) : ℝ) * Complex.I := by
  rw [map_add, complexDerivationEquivComplexifiedVectorField_symm_tmul,
    complexDerivationEquivComplexifiedVectorField_symm_tmul, one_smul]
  apply Complex.ext <;> simp <;> ring

/-- **The complexified derivation dictionary.** On a finite-dimensional, Hausdorff, boundaryless
real manifold there is a complex-linear equivalence between complex-linear derivations of
`C^∞(M, ℂ)` and `ℂ ⊗[ℝ] Γ∞(TM)` sending `δ` to `1 ⊗ X + i ⊗ Y` exactly when
`δ u = X u + i Y u` for every real smooth function `u`. -/
theorem exists_complexDerivationEquivComplexifiedVectorField :
    ∃ e : Derivation ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ ≃ₗ[ℂ]
        ℂ ⊗[ℝ] Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯,
      ∀ δ X Y, e δ = 1 ⊗ₜ X + Complex.I ⊗ₜ Y ↔
        ∀ (u : C^∞⟮I, M; ℝ⟯) (x : M), δ (ofReal u) x =
          (mvfderiv I u x (X x) : ℂ) + (mvfderiv I u x (Y x) : ℂ) * Complex.I :=
  ⟨complexDerivationEquivComplexifiedVectorField,
    complexDerivationEquivComplexifiedVectorField_eq_iff⟩

/-- **Complexified brackets, real part.** The real part of the commutator of complex derivations
has the vector field `[X₁, X₂] - [Y₁, Y₂]`, where `Xᵢ` and `Yᵢ` are the vector fields of the real
and imaginary parts of `δᵢ`. -/
theorem _root_.Derivation.vectorField_re_lie
    (δ₁ δ₂ : Derivation ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) (x : M) :
    ⁅δ₁, δ₂⁆.re.vectorField x =
      mlieBracket I δ₁.re.vectorField δ₂.re.vectorField x -
        mlieBracket I δ₁.im.vectorField δ₂.im.vectorField x := by
  refine (Derivation.eq_vectorField_iff.mpr fun f ↦ ?_).symm
  rw [map_sub, ← vectorField_lie, ← vectorField_lie, mvfderiv_vectorField, mvfderiv_vectorField,
    re_lie]
  simp

/-- **Complexified brackets, imaginary part.** The imaginary part of the commutator of complex
derivations has the vector field `[X₁, Y₂] + [Y₁, X₂]`, where `Xᵢ` and `Yᵢ` are the vector fields
of the real and imaginary parts of `δᵢ`. -/
theorem _root_.Derivation.vectorField_im_lie
    (δ₁ δ₂ : Derivation ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) (x : M) :
    ⁅δ₁, δ₂⁆.im.vectorField x =
      mlieBracket I δ₁.re.vectorField δ₂.im.vectorField x +
        mlieBracket I δ₁.im.vectorField δ₂.re.vectorField x := by
  rw [im_lie, vectorField_add, vectorField_lie, vectorField_lie]

end VectorField

end TauCeti
