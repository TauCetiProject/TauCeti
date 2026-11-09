/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Algebra.ComplexSmoothFunctions
public import TauCeti.Geometry.Manifold.VectorField.Derivation
public import TauCeti.LinearAlgebra.Complex.Conjugation

/-!
# Complex derivations of complex-valued smooth functions

Let `A = C^n(M, ℝ)` and `A_ℂ = C^n(M, ℂ)` be the real- and complex-valued `C^n` functions on a
real manifold `M`, where differentiability of complex-valued functions is taken over `ℝ`. A
complex-linear derivation `δ` of `A_ℂ` is determined by its restriction to real functions, and
taking real and imaginary parts of that restriction gives two real derivations `δ.re` and `δ.im`
of `A`. Conversely a real derivation `D` of `A` complexifies to the complex derivation
`D.complexify : u + i v ↦ D u + i D v`. This gives the complex-linear equivalence
`ℂ ⊗[ℝ] Der(A) ≃ Der_ℂ(A_ℂ)` sending `c ⊗ D` to `c • D.complexify`, under which
`δ (u + i v) = X u - Y v + i (Y u + X v)` for `δ` corresponding to `1 ⊗ X + i ⊗ Y`.

On a finite-dimensional, Hausdorff, boundaryless real manifold, derivations of `C^∞(M, ℝ)` are
smooth vector fields (`TauCeti.derivationEquivSmoothVectorField`). Hence complex-linear
derivations of `C^∞(M, ℂ)` are the complexified smooth vector fields `ℂ ⊗[ℝ] Γ∞(TM)`: `δ`
corresponds to `1 ⊗ X + i ⊗ Y` exactly when `δ u = X u + i Y u` for every real smooth `u`. The
commutator of complex derivations corresponds to the complex-bilinear extension of the Lie
bracket of vector fields. No continuity of the derivations is assumed.

## Main definitions

* `Derivation.complexify`: the complex derivation of `C^n(M, ℂ)` induced by a real derivation of
  `C^n(M, ℝ)`.
* `Derivation.re`, `Derivation.im`: the real derivations of `C^n(M, ℝ)` given by the real and
  imaginary parts of a complex derivation of `C^n(M, ℂ)` on real functions.
* `TauCeti.derivationComplexificationEquiv`: the complex-linear equivalence
  `ℂ ⊗[ℝ] Der(C^n(M, ℝ)) ≃ₗ[ℂ] Der_ℂ(C^n(M, ℂ))`.
* `TauCeti.complexDerivationEquivComplexifiedVectorField`: the complex-linear equivalence between
  complex derivations of `C^∞(M, ℂ)` and `ℂ ⊗[ℝ] Γ∞(TM)`.

## Main results

* `Derivation.apply_eq_ofReal_add_I_smul_ofReal`: `δ (u + i v) = X u - Y v + i (Y u + X v)` with
  `X = δ.re`, `Y = δ.im`.
* `Derivation.complexify_lie`, `Derivation.re_lie`, `Derivation.im_lie`: complexification is a
  Lie algebra map, and the commutator of complex derivations is the complex-bilinear extension
  of the commutator of real derivations.
* `TauCeti.complexDerivationEquivComplexifiedVectorField_eq_iff` and
  `TauCeti.exists_complexDerivationEquivComplexifiedVectorField`: `δ` corresponds to
  `1 ⊗ X + i ⊗ Y` exactly when `δ u x = du_x (X x) + du_x (Y x) i` for all real smooth `u`.
* `TauCeti.complexDerivationEquivComplexifiedVectorField_symm_apply_apply`: the inverse
  differentiates `f` by `df.re (X) - df.im (Y) + i (df.re (Y) + df.im (X))`.
* `TauCeti.complexDerivationEquivComplexifiedVectorField_lie_eq_iff`: the commutator corresponds
  to the complexified Lie bracket of vector fields.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, Lemma 3.3, p. 16.
* D. Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, §1.2.
-/

public section

noncomputable section

open ContMDiffMap VectorField
open scoped ContDiff Manifold TensorProduct

section Algebraic

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

namespace Derivation

/-! ### Complexification of real derivations -/

/-- The complexification of a real derivation `D` of `C^n(M, ℝ)`: the complex derivation of
`C^n(M, ℂ)` acting by `D` on real and imaginary parts, `u + i v ↦ D u + i D v`. -/
def complexify (D : Derivation ℝ C^n⟮I, M; ℝ⟯ C^n⟮I, M; ℝ⟯) :
    Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ :=
  Derivation.mk'
    { toFun f := ofReal (D f.re) + Complex.I • ofReal (D f.im)
      map_add' f g := by
        simp only [map_add, smul_add]
        abel
      map_smul' c f := by
        apply ext_re_im <;> simp <;> abel }
    fun f g ↦ by
      apply ext_re_im <;> simp [mul_re, mul_im] <;> ring

@[simp]
theorem complexify_apply (D : Derivation ℝ C^n⟮I, M; ℝ⟯ C^n⟮I, M; ℝ⟯)
    (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    D.complexify f = ofReal (D f.re) + Complex.I • ofReal (D f.im) :=
  (rfl)

/-- The complexification of `D` acts on real functions by `D`. -/
theorem complexify_ofReal (D : Derivation ℝ C^n⟮I, M; ℝ⟯ C^n⟮I, M; ℝ⟯)
    (u : C^n⟮I, M; ℝ⟯) : D.complexify (ofReal u) = ofReal (D u) := by
  apply ext_re_im <;> simp

/-- Complexification of real derivations, as a real-linear map. -/
def complexifyₗ :
    Derivation ℝ C^n⟮I, M; ℝ⟯ C^n⟮I, M; ℝ⟯ →ₗ[ℝ]
      Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ where
  toFun := complexify
  map_add' D₁ D₂ := by
    ext f : 1
    apply ext_re_im <;> simp
  map_smul' r D := by
    ext f : 1
    apply ext_re_im <;> simp

@[simp]
theorem complexifyₗ_apply (D : Derivation ℝ C^n⟮I, M; ℝ⟯ C^n⟮I, M; ℝ⟯) :
    complexifyₗ D = D.complexify :=
  (rfl)

/-- Complexifying `g • D` multiplies the complexification of `D` by the real function `g`. -/
theorem complexify_smul (g : C^n⟮I, M; ℝ⟯) (D : Derivation ℝ C^n⟮I, M; ℝ⟯ C^n⟮I, M; ℝ⟯) :
    (g • D).complexify = ofReal g • D.complexify := by
  ext f : 1
  apply ext_re_im <;> simp [mul_re, mul_im]

/-- **Complexification is a Lie algebra map**: the complexification of the commutator of real
derivations is the commutator of their complexifications. -/
theorem complexify_lie (D₁ D₂ : Derivation ℝ C^n⟮I, M; ℝ⟯ C^n⟮I, M; ℝ⟯) :
    ⁅D₁, D₂⁆.complexify = ⁅D₁.complexify, D₂.complexify⁆ := by
  ext f : 1
  apply ext_re_im <;> simp [commutator_apply]

/-! ### Real and imaginary parts of complex derivations -/

/-- The real part of a complex derivation `δ` of `C^n(M, ℂ)`: the real derivation
`u ↦ Re (δ u)` of `C^n(M, ℝ)`. -/
def re (δ : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    Derivation ℝ C^n⟮I, M; ℝ⟯ C^n⟮I, M; ℝ⟯ :=
  Derivation.mk'
    { toFun u := (δ (ofReal u)).re
      map_add' u v := by simp
      map_smul' r u := by
        ext x
        simp [δ.map_smul_of_tower] }
    fun u v ↦ by
      simp [mul_re]

/-- The imaginary part of a complex derivation `δ` of `C^n(M, ℂ)`: the real derivation
`u ↦ Im (δ u)` of `C^n(M, ℝ)`. -/
def im (δ : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    Derivation ℝ C^n⟮I, M; ℝ⟯ C^n⟮I, M; ℝ⟯ :=
  Derivation.mk'
    { toFun u := (δ (ofReal u)).im
      map_add' u v := by simp
      map_smul' r u := by
        ext x
        simp [δ.map_smul_of_tower] }
    fun u v ↦ by
      simp [mul_im]

@[simp]
theorem re_apply (δ : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯)
    (u : C^n⟮I, M; ℝ⟯) : δ.re u = (δ (ofReal u)).re :=
  (rfl)

@[simp]
theorem im_apply (δ : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯)
    (u : C^n⟮I, M; ℝ⟯) : δ.im u = (δ (ofReal u)).im :=
  (rfl)

/-- On a real function, a complex derivation is its real part plus `i` times its imaginary part. -/
theorem apply_ofReal (δ : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯)
    (u : C^n⟮I, M; ℝ⟯) : δ (ofReal u) = ofReal (δ.re u) + Complex.I • ofReal (δ.im u) :=
  (ofReal_re_add_I_smul_im _).symm

/-- **A complex derivation through its real and imaginary parts.** With `X = δ.re` and
`Y = δ.im`, `δ (u + i v) = X u - Y v + i (Y u + X v)`. -/
theorem apply_eq_ofReal_add_I_smul_ofReal
    (δ : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯)
    (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    δ f = ofReal (δ.re f.re - δ.im f.im) + Complex.I • ofReal (δ.im f.re + δ.re f.im) := by
  conv_lhs => rw [← ofReal_re_add_I_smul_im f]
  rw [map_add, map_smul, apply_ofReal, apply_ofReal]
  apply ext_re_im
  · simp [sub_eq_add_neg]
  · simp

/-- A complex derivation is determined by its real and imaginary parts. -/
theorem complexify_re_add_I_smul_complexify_im
    (δ : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    δ.re.complexify + Complex.I • δ.im.complexify = δ := by
  ext f : 1
  rw [apply_eq_ofReal_add_I_smul_ofReal δ f]
  apply ext_re_im <;> simp <;> abel

@[simp]
theorem re_complexify (D : Derivation ℝ C^n⟮I, M; ℝ⟯ C^n⟮I, M; ℝ⟯) : D.complexify.re = D := by
  ext u
  simp

@[simp]
theorem im_complexify (D : Derivation ℝ C^n⟮I, M; ℝ⟯ C^n⟮I, M; ℝ⟯) : D.complexify.im = 0 := by
  ext u
  simp

@[simp]
theorem re_add (δ₁ δ₂ : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    (δ₁ + δ₂).re = δ₁.re + δ₂.re := by
  ext u
  simp

@[simp]
theorem im_add (δ₁ δ₂ : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    (δ₁ + δ₂).im = δ₁.im + δ₂.im := by
  ext u
  simp

@[simp]
theorem re_smul (c : ℂ) (δ : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    (c • δ).re = c.re • δ.re - c.im • δ.im := by
  ext u
  simp

@[simp]
theorem im_smul (c : ℂ) (δ : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    (c • δ).im = c.re • δ.im + c.im • δ.re := by
  ext u
  simp

/-- Multiplying a complex derivation by a real function `g` multiplies its real part by `g`. -/
@[simp]
theorem re_ofReal_smul (g : C^n⟮I, M; ℝ⟯)
    (δ : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    (ofReal g • δ).re = g • δ.re := by
  ext u
  simp [mul_re]

/-- Multiplying a complex derivation by a real function `g` multiplies its imaginary part
by `g`. -/
@[simp]
theorem im_ofReal_smul (g : C^n⟮I, M; ℝ⟯)
    (δ : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    (ofReal g • δ).im = g • δ.im := by
  ext u
  simp [mul_im]

/-- The real part of a commutator of complex derivations is `⁅X₁, X₂⁆ - ⁅Y₁, Y₂⁆`, where
`Xᵢ = δᵢ.re` and `Yᵢ = δᵢ.im`. -/
theorem re_lie (δ₁ δ₂ : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    ⁅δ₁, δ₂⁆.re = ⁅δ₁.re, δ₂.re⁆ - ⁅δ₁.im, δ₂.im⁆ := by
  conv_lhs => rw [← complexify_re_add_I_smul_complexify_im δ₁,
    ← complexify_re_add_I_smul_complexify_im δ₂]
  simp [← complexify_lie, sub_eq_add_neg]

/-- The imaginary part of a commutator of complex derivations is `⁅X₁, Y₂⁆ + ⁅Y₁, X₂⁆`, where
`Xᵢ = δᵢ.re` and `Yᵢ = δᵢ.im`. -/
theorem im_lie (δ₁ δ₂ : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    ⁅δ₁, δ₂⁆.im = ⁅δ₁.re, δ₂.im⁆ + ⁅δ₁.im, δ₂.re⁆ := by
  conv_lhs => rw [← complexify_re_add_I_smul_complexify_im δ₁,
    ← complexify_re_add_I_smul_complexify_im δ₂]
  simp [← complexify_lie]
  abel

end Derivation

namespace TauCeti

open Derivation

/-- **Complex derivations are complexified real derivations.** The complex-linear equivalence
`ℂ ⊗[ℝ] Der(C^n(M, ℝ)) ≃ₗ[ℂ] Der_ℂ(C^n(M, ℂ))` sending `c ⊗ D` to `c • D.complexify`. Its
inverse sends `δ` to `1 ⊗ δ.re + i ⊗ δ.im`. -/
def derivationComplexificationEquiv :
    ℂ ⊗[ℝ] Derivation ℝ C^n⟮I, M; ℝ⟯ C^n⟮I, M; ℝ⟯ ≃ₗ[ℂ]
      Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ :=
  { (complexifyₗ (I := I) (M := M) (n := n)).liftBaseChange ℂ with
    invFun δ := 1 ⊗ₜ[ℝ] δ.re + Complex.I ⊗ₜ[ℝ] δ.im
    left_inv u := by
      obtain ⟨D₁, D₂, rfl⟩ := exists_one_tmul_add_I_tmul u
      simp
    right_inv δ := by
      simpa using complexify_re_add_I_smul_complexify_im δ }

@[simp]
theorem derivationComplexificationEquiv_tmul (c : ℂ)
    (D : Derivation ℝ C^n⟮I, M; ℝ⟯ C^n⟮I, M; ℝ⟯) :
    derivationComplexificationEquiv (c ⊗ₜ[ℝ] D) = c • D.complexify :=
  (rfl)

@[simp]
theorem derivationComplexificationEquiv_symm_apply
    (δ : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    derivationComplexificationEquiv.symm δ = 1 ⊗ₜ[ℝ] δ.re + Complex.I ⊗ₜ[ℝ] δ.im :=
  (rfl)

end TauCeti

end Algebraic

section VectorField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]

namespace TauCeti

open Derivation

/-- **Complex derivations are complexified vector fields.** On a finite-dimensional, Hausdorff,
boundaryless real manifold, the complex-linear equivalence between complex-linear derivations of
`C^∞(M, ℂ)` and `ℂ ⊗[ℝ] Γ∞(TM)` sending `δ` to `1 ⊗ X + i ⊗ Y`, where `X` and `Y` are the vector
fields of the real derivations `δ.re` and `δ.im`. No continuity of the derivations is assumed. -/
def complexDerivationEquivComplexifiedVectorField :
    Derivation ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ ≃ₗ[ℂ]
      ℂ ⊗[ℝ] Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  derivationComplexificationEquiv.symm ≪≫ₗ
    (derivationEquivSmoothVectorField.restrictScalars ℝ).baseChange ℝ ℂ _ _

/-- The complexified vector field of `δ` is `1 ⊗ X + i ⊗ Y`, where `X` and `Y` are the vector
fields of `δ.re` and `δ.im`. -/
theorem complexDerivationEquivComplexifiedVectorField_apply
    (δ : Derivation ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    complexDerivationEquivComplexifiedVectorField δ =
      1 ⊗ₜ[ℝ] derivationEquivSmoothVectorField δ.re +
        Complex.I ⊗ₜ[ℝ] derivationEquivSmoothVectorField δ.im := by
  simp [complexDerivationEquivComplexifiedVectorField]

/-- The real part of the complexified vector field of `δ` is the vector field of `δ.re`. -/
@[simp]
theorem realPart_complexDerivationEquivComplexifiedVectorField
    (δ : Derivation ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    realPart Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯
        (complexDerivationEquivComplexifiedVectorField δ) =
      derivationEquivSmoothVectorField δ.re := by
  simp [complexDerivationEquivComplexifiedVectorField_apply]

/-- The imaginary part of the complexified vector field of `δ` is the vector field of `δ.im`. -/
@[simp]
theorem imaginaryPart_complexDerivationEquivComplexifiedVectorField
    (δ : Derivation ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    imaginaryPart Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯
        (complexDerivationEquivComplexifiedVectorField δ) =
      derivationEquivSmoothVectorField δ.im := by
  simp [complexDerivationEquivComplexifiedVectorField_apply]

/-- **Characterization of the complexified vector field.** A complex derivation `δ` corresponds
to `1 ⊗ X + i ⊗ Y` exactly when `δ u x = du_x (X x) + du_x (Y x) i` for every real smooth `u`. -/
theorem complexDerivationEquivComplexifiedVectorField_eq_iff
    {δ : Derivation ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯}
    {X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯} :
    complexDerivationEquivComplexifiedVectorField δ = 1 ⊗ₜ[ℝ] X + Complex.I ⊗ₜ[ℝ] Y ↔
      ∀ (u : C^∞⟮I, M; ℝ⟯) (x : M),
        δ (ofReal u) x = (mvfderiv I u x (X x) : ℂ) + (mvfderiv I u x (Y x) : ℂ) * Complex.I := by
  have key (D : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯)
      (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
      derivationEquivSmoothVectorField D = Z ↔ ∀ u x, D u x = mvfderiv I u x (Z x) := by
    rw [← LinearEquiv.eq_symm_apply, Derivation.ext_iff]
    simp [ContMDiffMap.ext_iff]
  rw [complexDerivationEquivComplexifiedVectorField_apply, one_tmul_add_I_tmul_inj, key, key]
  -- `mvfderiv` takes values in a tangent space of `ℝ`, on which `simp` does not see the real
  -- and imaginary parts of the coercion to `ℂ`; `simp only` rewrites them syntactically.
  simp only [Derivation.re_apply, Derivation.im_apply, ContMDiffMap.re_apply,
    ContMDiffMap.im_apply, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
    mul_one, sub_zero, zero_add, add_zero, forall_and]

/-- **Complex derivations and complexified vector fields.** On a finite-dimensional, Hausdorff,
boundaryless real manifold there is a complex-linear equivalence between complex-linear
derivations of `C^∞(M, ℂ)` and `ℂ ⊗[ℝ] Γ∞(TM)` sending `δ` to `1 ⊗ X + i ⊗ Y` exactly when
`δ u = X u + i Y u` for every real smooth `u`. -/
theorem exists_complexDerivationEquivComplexifiedVectorField :
    ∃ e : Derivation ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ ≃ₗ[ℂ]
        ℂ ⊗[ℝ] Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯,
      ∀ δ X Y, e δ = (1 : ℂ) ⊗ₜ[ℝ] X + Complex.I ⊗ₜ[ℝ] Y ↔
        ∀ (u : C^∞⟮I, M; ℝ⟯) (x : M), δ (ofReal u) x =
          (mvfderiv I u x (X x) : ℂ) + (mvfderiv I u x (Y x) : ℂ) * Complex.I :=
  ⟨complexDerivationEquivComplexifiedVectorField, fun _ _ _ ↦
    complexDerivationEquivComplexifiedVectorField_eq_iff⟩

/-- **The inverse formula.** The complex derivation of `1 ⊗ X + i ⊗ Y` sends `f = u + i v` to
`X u - Y v + i (Y u + X v)`, evaluated pointwise through differentials. -/
theorem complexDerivationEquivComplexifiedVectorField_symm_apply_apply
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (f : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) (x : M) :
    complexDerivationEquivComplexifiedVectorField.symm (1 ⊗ₜ[ℝ] X + Complex.I ⊗ₜ[ℝ] Y) f x =
      ((mvfderiv I f.re x (X x) - mvfderiv I f.im x (Y x) : ℝ) : ℂ) +
        ((mvfderiv I f.re x (Y x) + mvfderiv I f.im x (X x) : ℝ) : ℂ) * Complex.I := by
  simp only [complexDerivationEquivComplexifiedVectorField, LinearEquiv.trans_symm,
    LinearEquiv.trans_apply, map_add]
  apply Complex.ext <;> simp <;> ring

/-- **Commutators are complexified Lie brackets.** If `δ₁` and `δ₂` correspond to
`1 ⊗ X₁ + i ⊗ Y₁` and `1 ⊗ X₂ + i ⊗ Y₂`, then `⁅δ₁, δ₂⁆` corresponds to `1 ⊗ Z + i ⊗ W` exactly
when `Z = [X₁, X₂] - [Y₁, Y₂]` and `W = [X₁, Y₂] + [Y₁, X₂]`, the complex-bilinear extension of
the Lie bracket of vector fields. -/
theorem complexDerivationEquivComplexifiedVectorField_lie_eq_iff
    {δ₁ δ₂ : Derivation ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯}
    {X₁ Y₁ X₂ Y₂ Z W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (h₁ : complexDerivationEquivComplexifiedVectorField δ₁ = 1 ⊗ₜ[ℝ] X₁ + Complex.I ⊗ₜ[ℝ] Y₁)
    (h₂ : complexDerivationEquivComplexifiedVectorField δ₂ = 1 ⊗ₜ[ℝ] X₂ + Complex.I ⊗ₜ[ℝ] Y₂) :
    complexDerivationEquivComplexifiedVectorField ⁅δ₁, δ₂⁆ = 1 ⊗ₜ[ℝ] Z + Complex.I ⊗ₜ[ℝ] W ↔
      ∀ x, Z x = mlieBracket I X₁ X₂ x - mlieBracket I Y₁ Y₂ x ∧
        W x = mlieBracket I X₁ Y₂ x + mlieBracket I Y₁ X₂ x := by
  rw [complexDerivationEquivComplexifiedVectorField_apply, one_tmul_add_I_tmul_inj] at h₁ h₂ ⊢
  obtain ⟨rfl, rfl⟩ := h₁
  obtain ⟨rfl, rfl⟩ := h₂
  simp only [re_lie, im_lie, map_sub, map_add, ContMDiffSection.ext_iff,
    ContMDiffSection.coe_sub, ContMDiffSection.coe_add, Pi.sub_apply, Pi.add_apply,
    Derivation.coe_derivationEquivSmoothVectorField, Derivation.vectorField_lie, ← forall_and,
    eq_comm]

end TauCeti

end VectorField
