/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.BaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Lift
public import TauCeti.Geometry.Manifold.Algebra.ComplexSmoothFunctions
public import TauCeti.Geometry.Manifold.VectorField.Derivation
public import TauCeti.LinearAlgebra.Complex.Conjugation

/-!
# Complex derivations of complex-valued smooth functions

On a real manifold `M`, the complex-valued smooth functions `C^n(M, ℂ)` form a complex algebra.
Its complex-linear derivations are exactly the complexifications of real derivations of
`C^n(M, ℝ)`: a complex derivation `δ` is determined by its values on real functions, and
splitting these values into real and imaginary parts gives two real derivations `δ.re` and
`δ.im` with `δ u = δ.re u + i δ.im u` for real `u`. Conversely, a real derivation `D` extends to
the complex derivation `D (u + i v) = D u + i D v`.

Combining this with the identification of real derivations with smooth vector fields, on a
finite-dimensional, Hausdorff, boundaryless real manifold the complex derivations of
`C^∞(M, ℂ)` correspond complex-linearly to the complexified vector fields `ℂ ⊗[ℝ] Γ(TM)`: the
element `1 ⊗ X + i ⊗ Y` acts by `δ (u + i v) = X u - Y v + i (Y u + X v)`.

## Main definitions

* `Derivation.re`, `Derivation.im`: the real and imaginary parts of a complex derivation of
  `C^n(M, ℂ)`, real derivations of `C^n(M, ℝ)`.
* `Derivation.complexify`: the complexification of a real derivation of `C^n(M, ℝ)`, as a
  real-linear map.
* `Derivation.complexifyEquiv`: the complex-linear equivalence between `ℂ ⊗[ℝ] Der(C^n(M, ℝ))`
  and the complex derivations of `C^n(M, ℂ)`.
* `TauCeti.complexDerivationEquivComplexifiedVectorField`: the complex-linear equivalence between
  the complex derivations of `C^∞(M, ℂ)` and the complexified smooth vector fields.

## Main results

* `Derivation.ext_ofReal`: a complex derivation of `C^n(M, ℂ)` is determined by its values on
  real-valued functions.
* `Derivation.complexifyEquiv_lie`: the complexification equivalence intertwines the
  base-changed Lie bracket of real derivations with the commutator of complex derivations.
* `Derivation.re_lie`, `Derivation.im_lie`: the real and imaginary parts of the commutator of
  complex derivations, `⁅X₁ + i Y₁, X₂ + i Y₂⁆ = ⁅X₁, X₂⁆ - ⁅Y₁, Y₂⁆ + i (⁅X₁, Y₂⁆ + ⁅Y₁, X₂⁆)`.
* `TauCeti.complexDerivationEquivComplexifiedVectorField_eq_iff`: a complex derivation `δ`
  corresponds to `1 ⊗ X + i ⊗ Y` exactly when `δ u = X u + i Y u` for every real smooth `u`.
* `TauCeti.exists_complexDerivationEquivComplexifiedVectorField`: the complexified derivation
  dictionary.
* `TauCeti.complexDerivationEquivComplexifiedVectorField_lie_eq_iff`: the commutator of complex
  derivations corresponds to the complex-bilinear extension of the Lie bracket of vector fields.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, Lemma 3.3, p. 16, for the real dictionary that this file complexifies.
-/

public section

noncomputable section

open scoped Manifold ContDiff TensorProduct

namespace Derivation

section Complexify

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

/-- The real part of a complex derivation `δ` of `C^n(M, ℂ)`: the real derivation of
`C^n(M, ℝ)` sending `u` to the real part of `δ u`. -/
def re (δ : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    Derivation ℝ C^n⟮I, M; ℝ⟯ C^n⟮I, M; ℝ⟯ :=
  Derivation.mk'
    (ContMDiffMap.re ∘ₗ ((δ : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯).restrictScalars ℝ)
      ∘ₗ ContMDiffMap.ofReal.toLinearMap)
    fun u v ↦ by
      ext x
      simp [ContMDiffMap.mul_re]

/-- The imaginary part of a complex derivation `δ` of `C^n(M, ℂ)`: the real derivation of
`C^n(M, ℝ)` sending `u` to the imaginary part of `δ u`. -/
def im (δ : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    Derivation ℝ C^n⟮I, M; ℝ⟯ C^n⟮I, M; ℝ⟯ :=
  Derivation.mk'
    (ContMDiffMap.im ∘ₗ ((δ : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯).restrictScalars ℝ)
      ∘ₗ ContMDiffMap.ofReal.toLinearMap)
    fun u v ↦ by
      ext x
      simp [ContMDiffMap.mul_im]

@[simp]
theorem re_apply (δ : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯)
    (u : C^n⟮I, M; ℝ⟯) : δ.re u = (δ (ContMDiffMap.ofReal u)).re :=
  (rfl)

@[simp]
theorem im_apply (δ : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯)
    (u : C^n⟮I, M; ℝ⟯) : δ.im u = (δ (ContMDiffMap.ofReal u)).im :=
  (rfl)

/-- A complex derivation acts on a real function through its real and imaginary parts. -/
theorem ofReal_re_add_I_smul_ofReal_im
    (δ : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) (u : C^n⟮I, M; ℝ⟯) :
    ContMDiffMap.ofReal (δ.re u) + Complex.I • ContMDiffMap.ofReal (δ.im u) =
      δ (ContMDiffMap.ofReal u) :=
  ContMDiffMap.ofReal_re_add_I_smul_im _

/-- A complex derivation of `C^n(M, ℂ)` is determined by its values on real-valued functions. -/
theorem ext_ofReal {δ₁ δ₂ : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯}
    (h : ∀ u : C^n⟮I, M; ℝ⟯, δ₁ (ContMDiffMap.ofReal u) = δ₂ (ContMDiffMap.ofReal u)) :
    δ₁ = δ₂ := by
  ext f
  rw [← ContMDiffMap.ofReal_re_add_I_smul_im f, map_add, map_add, map_smul, map_smul, h, h]

/-- A complex derivation of `C^n(M, ℂ)` is determined by its real and imaginary parts. -/
theorem ext_re_im {δ₁ δ₂ : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯}
    (hre : δ₁.re = δ₂.re) (him : δ₁.im = δ₂.im) : δ₁ = δ₂ :=
  ext_ofReal fun u ↦ by
    rw [← ofReal_re_add_I_smul_ofReal_im, ← ofReal_re_add_I_smul_ofReal_im, hre, him]

@[simp]
theorem re_zero : (0 : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯).re = 0 := by
  ext u x
  simp

@[simp]
theorem im_zero : (0 : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯).im = 0 := by
  ext u x
  simp

@[simp]
theorem re_add (δ₁ δ₂ : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    (δ₁ + δ₂).re = δ₁.re + δ₂.re := by
  ext u x
  simp

@[simp]
theorem im_add (δ₁ δ₂ : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    (δ₁ + δ₂).im = δ₁.im + δ₂.im := by
  ext u x
  simp

/-- Real part of a complex multiple of a complex derivation. -/
@[simp]
theorem complex_smul_re (z : ℂ) (δ : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    (z • δ).re = z.re • δ.re - z.im • δ.im := by
  ext u x
  simp

/-- Imaginary part of a complex multiple of a complex derivation. -/
@[simp]
theorem complex_smul_im (z : ℂ) (δ : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    (z • δ).im = z.re • δ.im + z.im • δ.re := by
  ext u x
  simp

/-- The complexification of a real derivation `D` of `C^n(M, ℝ)`: the complex derivation of
`C^n(M, ℂ)` acting by `D` on real and imaginary parts, `D (u + i v) = D u + i D v`. -/
def complexify :
    Derivation ℝ C^n⟮I, M; ℝ⟯ C^n⟮I, M; ℝ⟯ →ₗ[ℝ]
      Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ where
  toFun D := Derivation.mk'
    { toFun f := ContMDiffMap.ofReal (D f.re) + Complex.I • ContMDiffMap.ofReal (D f.im)
      map_add' f g := by
        simp only [map_add, smul_add]
        abel
      map_smul' z f := by
        ext x
        apply Complex.ext <;> simp <;> ring }
    fun f g ↦ by
      ext x
      apply Complex.ext <;> simp [ContMDiffMap.mul_re, ContMDiffMap.mul_im] <;> ring
  map_add' D₁ D₂ := by
    ext f x
    apply Complex.ext <;> simp
  map_smul' r D := by
    ext f x
    apply Complex.ext <;> simp

/-- The complexification of `D` acts on `f` through the real and imaginary parts of `f`. -/
@[simp]
theorem complexify_apply (D : Derivation ℝ C^n⟮I, M; ℝ⟯ C^n⟮I, M; ℝ⟯)
    (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    complexify D f = ContMDiffMap.ofReal (D f.re) + Complex.I • ContMDiffMap.ofReal (D f.im) :=
  (rfl)

/-- The complexification of `D` extends `D` from real to complex functions. -/
theorem complexify_apply_ofReal (D : Derivation ℝ C^n⟮I, M; ℝ⟯ C^n⟮I, M; ℝ⟯)
    (u : C^n⟮I, M; ℝ⟯) : complexify D (ContMDiffMap.ofReal u) = ContMDiffMap.ofReal (D u) := by
  simp

@[simp]
theorem re_complexify (D : Derivation ℝ C^n⟮I, M; ℝ⟯ C^n⟮I, M; ℝ⟯) : (complexify D).re = D := by
  ext u x
  simp

@[simp]
theorem im_complexify (D : Derivation ℝ C^n⟮I, M; ℝ⟯ C^n⟮I, M; ℝ⟯) : (complexify D).im = 0 := by
  ext u x
  simp

/-- Every complex derivation is the complexification of its real part plus `i` times the
complexification of its imaginary part. -/
theorem complexify_re_add_I_smul_complexify_im
    (δ : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    complexify δ.re + Complex.I • complexify δ.im = δ :=
  ext_re_im (by simp) (by simp)

/-- The base change of complexification recovers a tensor from the real and imaginary parts of
its image. -/
private theorem tmul_re_add_I_tmul_im_liftBaseChange
    (t : ℂ ⊗[ℝ] Derivation ℝ C^n⟮I, M; ℝ⟯ C^n⟮I, M; ℝ⟯) :
    1 ⊗ₜ (complexify.liftBaseChange ℂ t).re + Complex.I ⊗ₜ (complexify.liftBaseChange ℂ t).im =
      t := by
  induction t using TensorProduct.inductionOn with
  | tmul z D =>
    simp only [LinearMap.liftBaseChange_tmul, complex_smul_re, complex_smul_im, re_complexify,
      im_complexify, smul_zero, sub_zero, zero_add]
    rw [← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.add_tmul]
    congr 1
    apply Complex.ext <;> simp
  | add t₁ t₂ h₁ h₂ =>
    rw [map_add, re_add, im_add, TensorProduct.tmul_add, TensorProduct.tmul_add]
    conv_rhs => rw [← h₁, ← h₂]
    abel

/-- **Complexification of derivations.** Complex derivations of `C^n(M, ℂ)` are the base change
to `ℂ` of real derivations of `C^n(M, ℝ)`: `z ⊗ D` acts as `z` times the complexification of `D`,
and the inverse sends `δ` to `1 ⊗ δ.re + i ⊗ δ.im`. -/
def complexifyEquiv :
    ℂ ⊗[ℝ] Derivation ℝ C^n⟮I, M; ℝ⟯ C^n⟮I, M; ℝ⟯ ≃ₗ[ℂ]
      Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ where
  toLinearMap := complexify.liftBaseChange ℂ
  invFun δ := 1 ⊗ₜ δ.re + Complex.I ⊗ₜ δ.im
  left_inv := tmul_re_add_I_tmul_im_liftBaseChange
  right_inv δ := by simpa using complexify_re_add_I_smul_complexify_im δ

@[simp]
theorem complexifyEquiv_tmul (z : ℂ) (D : Derivation ℝ C^n⟮I, M; ℝ⟯ C^n⟮I, M; ℝ⟯) :
    complexifyEquiv (z ⊗ₜ D) = z • complexify D :=
  (rfl)

@[simp]
theorem complexifyEquiv_symm_apply
    (δ : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    complexifyEquiv.symm δ = 1 ⊗ₜ δ.re + Complex.I ⊗ₜ δ.im :=
  (rfl)

/-- Complexification turns the commutator of real derivations into the commutator of their
complexifications. -/
theorem complexify_lie (D₁ D₂ : Derivation ℝ C^n⟮I, M; ℝ⟯ C^n⟮I, M; ℝ⟯) :
    complexify ⁅D₁, D₂⁆ = ⁅complexify D₁, complexify D₂⁆ := by
  ext f x
  apply Complex.ext <;> simp [commutator_apply]

/-- **The complexified bracket.** The complexification equivalence intertwines the Lie bracket
of `ℂ ⊗[ℝ] Der(C^n(M, ℝ))`, given on pure tensors by `⁅z ⊗ D₁, w ⊗ D₂⁆ = z w ⊗ ⁅D₁, D₂⁆`, with
the commutator of complex derivations. -/
theorem complexifyEquiv_lie (t₁ t₂ : ℂ ⊗[ℝ] Derivation ℝ C^n⟮I, M; ℝ⟯ C^n⟮I, M; ℝ⟯) :
    complexifyEquiv ⁅t₁, t₂⁆ = ⁅complexifyEquiv t₁, complexifyEquiv t₂⁆ := by
  induction t₁ using TensorProduct.inductionOn with
  | add s₁ s₂ h₁ h₂ =>
    -- The base-changed bracket elaborates through its `Bracket` instance rather than the
    -- `LieRing` projection, so `rw [add_lie]` does not see it; the term `add_lie` does.
    exact (congrArg complexifyEquiv (add_lie s₁ s₂ t₂)).trans
      (by rw [map_add, h₁, h₂, map_add, add_lie])
  | tmul z D₁ =>
    induction t₂ using TensorProduct.inductionOn with
    | add s₁ s₂ h₁ h₂ =>
      exact (congrArg complexifyEquiv (lie_add (z ⊗ₜ[ℝ] D₁) s₁ s₂)).trans
        (by rw [map_add, h₁, h₂, map_add, lie_add])
    | tmul w D₂ =>
      rw [LieAlgebra.ExtendScalars.bracket_tmul, complexifyEquiv_tmul, complexifyEquiv_tmul,
        complexifyEquiv_tmul, complexify_lie, smul_lie, lie_smul, smul_smul]

/-- Complexifying `g • D` multiplies the complexification of `D` by the real function `g`. -/
theorem complexify_smul (g : C^n⟮I, M; ℝ⟯) (D : Derivation ℝ C^n⟮I, M; ℝ⟯ C^n⟮I, M; ℝ⟯) :
    complexify (g • D) = ContMDiffMap.ofReal g • complexify D := by
  ext f x
  apply Complex.ext <;> simp

/-- Multiplying a complex derivation by a real function `g` multiplies its real part by `g`. -/
@[simp]
theorem re_ofReal_smul (g : C^n⟮I, M; ℝ⟯)
    (δ : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    (ContMDiffMap.ofReal g • δ).re = g • δ.re := by
  ext u x
  simp [ContMDiffMap.mul_re]

/-- Multiplying a complex derivation by a real function `g` multiplies its imaginary part
by `g`. -/
@[simp]
theorem im_ofReal_smul (g : C^n⟮I, M; ℝ⟯)
    (δ : Derivation ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    (ContMDiffMap.ofReal g • δ).im = g • δ.im := by
  ext u x
  simp [ContMDiffMap.mul_im]

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

end Complexify

end Derivation

namespace TauCeti

section ComplexifiedVectorField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]

/-- **Complex derivations are complexified vector fields.** On a finite-dimensional, Hausdorff,
boundaryless real manifold, the complex derivations of `C^∞(M, ℂ)` correspond complex-linearly
to `ℂ ⊗[ℝ] Γ(TM)`: a derivation `δ` goes to `1 ⊗ X + i ⊗ Y`, where `X` and `Y` are the vector
fields of its real and imaginary parts. -/
def complexDerivationEquivComplexifiedVectorField :
    Derivation ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ ≃ₗ[ℂ]
      ℂ ⊗[ℝ] Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  Derivation.complexifyEquiv.symm.trans
    ((derivationEquivSmoothVectorField.restrictScalars ℝ).baseChange ℝ ℂ _ _)

/-- The equivalence sends a complex derivation to `1 ⊗ X + i ⊗ Y`, where `X` and `Y` are the
vector fields of its real and imaginary parts. -/
@[simp]
theorem complexDerivationEquivComplexifiedVectorField_apply
    (δ : Derivation ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    complexDerivationEquivComplexifiedVectorField δ =
      1 ⊗ₜ derivationEquivSmoothVectorField δ.re +
        Complex.I ⊗ₜ derivationEquivSmoothVectorField δ.im := by
  simp [complexDerivationEquivComplexifiedVectorField]

/-- The real part of the complexified vector field of `δ` is the vector field of `δ.re`. -/
theorem _root_.Derivation.realPart_complexDerivationEquivComplexifiedVectorField
    (δ : Derivation ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    realPart Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯
        (complexDerivationEquivComplexifiedVectorField δ) =
      derivationEquivSmoothVectorField δ.re := by
  simp

/-- The imaginary part of the complexified vector field of `δ` is the vector field of `δ.im`. -/
theorem _root_.Derivation.imaginaryPart_complexDerivationEquivComplexifiedVectorField
    (δ : Derivation ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    imaginaryPart Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯
        (complexDerivationEquivComplexifiedVectorField δ) =
      derivationEquivSmoothVectorField δ.im := by
  simp

/-- The inverse equivalence sends `z ⊗ X` to `z` times the complexified derivative along `X`. -/
@[simp]
theorem complexDerivationEquivComplexifiedVectorField_symm_tmul (z : ℂ)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    complexDerivationEquivComplexifiedVectorField.symm (z ⊗ₜ X) =
      z • Derivation.complexify (vectorFieldDerivation X) := by
  simp [complexDerivationEquivComplexifiedVectorField]

/-- **The inverse formula.** The complexified vector field `1 ⊗ X + i ⊗ Y` acts on `u + i v` by
`X u - Y v + i (Y u + X v)`. -/
theorem complexDerivationEquivComplexifiedVectorField_symm_apply_apply
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (f : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) (x : M) :
    complexDerivationEquivComplexifiedVectorField.symm (1 ⊗ₜ X + Complex.I ⊗ₜ Y) f x =
      ((mvfderiv I f.re x (X x) - mvfderiv I f.im x (Y x) : ℝ) : ℂ) +
        ((mvfderiv I f.re x (Y x) + mvfderiv I f.im x (X x) : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;> simp <;> ring

/-- A complex derivation `δ` corresponds to `1 ⊗ X + i ⊗ Y` exactly when it differentiates every
real smooth function `u` as `δ u = X u + i Y u`. -/
theorem complexDerivationEquivComplexifiedVectorField_eq_iff
    {δ : Derivation ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯}
    {X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯} :
    complexDerivationEquivComplexifiedVectorField δ = 1 ⊗ₜ X + Complex.I ⊗ₜ Y ↔
      ∀ (u : C^∞⟮I, M; ℝ⟯) (x : M), δ (ContMDiffMap.ofReal u) x =
        (mvfderiv I u x (X x) : ℂ) + (mvfderiv I u x (Y x) : ℂ) * Complex.I := by
  rw [← LinearEquiv.eq_symm_apply]
  refine ⟨fun h u x ↦ ?_, fun h ↦ Derivation.ext_ofReal fun u ↦ ContMDiffMap.ext fun x ↦ ?_⟩
  · rw [h]
    simp [mul_comm]
  · rw [h]
    simp [mul_comm]

/-- **The complexified derivation dictionary.** On a finite-dimensional, Hausdorff, boundaryless
real manifold, the complex derivations of `C^∞(M, ℂ)` correspond complex-linearly and bijectively
to `ℂ ⊗[ℝ] Γ(TM)`, the derivation `δ` going to `1 ⊗ X + i ⊗ Y` exactly when
`δ u = X u + i Y u` for every real smooth `u`. -/
theorem exists_complexDerivationEquivComplexifiedVectorField :
    ∃ e : Derivation ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ ≃ₗ[ℂ]
        ℂ ⊗[ℝ] Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯,
      ∀ δ X Y, e δ = 1 ⊗ₜ X + Complex.I ⊗ₜ Y ↔
        ∀ (u : C^∞⟮I, M; ℝ⟯) (x : M), δ (ContMDiffMap.ofReal u) x =
          (mvfderiv I u x (X x) : ℂ) + (mvfderiv I u x (Y x) : ℂ) * Complex.I :=
  ⟨complexDerivationEquivComplexifiedVectorField, fun _ _ _ ↦
    complexDerivationEquivComplexifiedVectorField_eq_iff⟩

/-- **Commutators are complexified Lie brackets.** If `δ₁` and `δ₂` correspond to
`1 ⊗ X₁ + i ⊗ Y₁` and `1 ⊗ X₂ + i ⊗ Y₂`, then `⁅δ₁, δ₂⁆` corresponds to `1 ⊗ Z + i ⊗ W` exactly
when `Z = [X₁, X₂] - [Y₁, Y₂]` and `W = [X₁, Y₂] + [Y₁, X₂]`, the complex-bilinear extension of
the Lie bracket of vector fields. -/
theorem complexDerivationEquivComplexifiedVectorField_lie_eq_iff
    {δ₁ δ₂ : Derivation ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯}
    {X₁ Y₁ X₂ Y₂ Z W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (h₁ : complexDerivationEquivComplexifiedVectorField δ₁ = 1 ⊗ₜ X₁ + Complex.I ⊗ₜ Y₁)
    (h₂ : complexDerivationEquivComplexifiedVectorField δ₂ = 1 ⊗ₜ X₂ + Complex.I ⊗ₜ Y₂) :
    complexDerivationEquivComplexifiedVectorField ⁅δ₁, δ₂⁆ = 1 ⊗ₜ Z + Complex.I ⊗ₜ W ↔
      ∀ x, Z x = VectorField.mlieBracket I X₁ X₂ x - VectorField.mlieBracket I Y₁ Y₂ x ∧
        W x = VectorField.mlieBracket I X₁ Y₂ x + VectorField.mlieBracket I Y₁ X₂ x := by
  rw [complexDerivationEquivComplexifiedVectorField_apply, one_tmul_add_I_tmul_inj] at h₁ h₂ ⊢
  obtain ⟨rfl, rfl⟩ := h₁
  obtain ⟨rfl, rfl⟩ := h₂
  simp only [Derivation.re_lie, Derivation.im_lie, map_sub, map_add, ContMDiffSection.ext_iff,
    ContMDiffSection.coe_sub, ContMDiffSection.coe_add, Pi.sub_apply, Pi.add_apply,
    Derivation.coe_derivationEquivSmoothVectorField, Derivation.vectorField_lie, ← forall_and,
    eq_comm]

end ComplexifiedVectorField

end TauCeti
