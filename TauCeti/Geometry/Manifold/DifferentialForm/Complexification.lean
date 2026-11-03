/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.MapCoeff
public import TauCeti.LinearAlgebra.Complex.Conjugation

/-!
# Complexification of real-valued smooth forms

Complex-valued smooth forms on a real manifold are the scalar extension of real-valued
smooth forms. `TauCeti.SmoothForm.complexificationEquiv` identifies these spaces by sending
`c ⊗ ω` to `c • mapCoeff Complex.ofRealCLM ω`. Its inverse takes real and imaginary parts
of the coefficients. This is an algebraic tensor product: only the two real components
are needed, with no completion or finite-dimensionality assumption on the manifold.

The identification commutes with exterior differentiation, smooth pullback and conjugation.
In particular, closedness and the existence of a smooth primitive can be tested separately
on the real and imaginary parts. These comparisons allow scalar extension of the real
de Rham complex while retaining the same differential-form carrier.

The scalar extension uses Mathlib's `LinearMap.liftBaseChange`, and the two-component
decomposition of a tensor uses `TauCeti.exists_one_tmul_add_I_tmul`.
-/

public section

noncomputable section

open scoped Manifold TensorProduct ComplexConjugate

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] {k : ℕ}

/-- A complex-valued smooth form is the sum of its real part and `I` times its imaginary part,
with both real-valued forms included through the coefficient map. -/
@[simp]
theorem ofReal_realPart_add_I_smul_ofReal_imaginaryPart (ω : SmoothForm I M ℂ k) :
    mapCoeff Complex.ofRealCLM (mapCoeff Complex.reCLM ω) +
      Complex.I • mapCoeff Complex.ofRealCLM (mapCoeff Complex.imCLM ω) = ω := by
  apply Subtype.ext
  funext x
  ext v
  simpa [RoughForm.mapCoeff_apply, smul_eq_mul, mul_comm] using
    Complex.re_add_im (ω.1 x v)

private theorem liftBaseChange_ofReal_bijective :
    Function.Bijective
      ((mapCoeff (I := I) (M := M) (k := k) Complex.ofRealCLM).liftBaseChange ℂ) := by
  constructor
  · apply (LinearMap.ker_eq_bot).mp
    apply eq_bot_iff.mpr
    intro u hu
    obtain ⟨α, β, rfl⟩ := exists_one_tmul_add_I_tmul u
    have h : mapCoeff Complex.ofRealCLM α +
        Complex.I • mapCoeff Complex.ofRealCLM β = 0 := by
      simpa using hu
    have hα : α = 0 := by
      apply Subtype.ext
      funext x
      ext v
      have := congrArg (fun η : SmoothForm I M ℂ k ↦ (η.1 x v).re) h
      simpa [RoughForm.mapCoeff_apply, smul_eq_mul] using this
    have hβ : β = 0 := by
      apply Subtype.ext
      funext x
      ext v
      have := congrArg (fun η : SmoothForm I M ℂ k ↦ (η.1 x v).im) h
      simpa [RoughForm.mapCoeff_apply, smul_eq_mul] using this
    simp [hα, hβ]
  · intro ω
    refine ⟨1 ⊗ₜ[ℝ] mapCoeff Complex.reCLM ω +
      Complex.I ⊗ₜ[ℝ] mapCoeff Complex.imCLM ω, ?_⟩
    simp

/-- Complex-valued smooth forms are the complexification of real-valued smooth forms.
The map sends `c ⊗ ω` to the form with values `c * ω`. -/
def complexificationEquiv :
    (ℂ ⊗[ℝ] SmoothForm I M ℝ k) ≃ₗ[ℂ] SmoothForm I M ℂ k :=
  LinearEquiv.ofBijective (mapCoeff Complex.ofRealCLM |>.liftBaseChange ℂ)
    liftBaseChange_ofReal_bijective

/-- The complexification equivalence on pure tensors. -/
@[simp]
theorem complexificationEquiv_tmul (c : ℂ) (ω : SmoothForm I M ℝ k) :
    complexificationEquiv (c ⊗ₜ[ℝ] ω) = c • mapCoeff Complex.ofRealCLM ω :=
  (rfl)

/-- The inverse complexification map separates the real and imaginary coefficients. -/
@[simp]
theorem complexificationEquiv_symm_apply (ω : SmoothForm I M ℂ k) :
    complexificationEquiv.symm ω =
      1 ⊗ₜ[ℝ] mapCoeff Complex.reCLM ω +
        Complex.I ⊗ₜ[ℝ] mapCoeff Complex.imCLM ω := by
  apply complexificationEquiv.injective
  simp

/-- Complexification intertwines conjugation of the scalar tensor factor with conjugation of
form coefficients. -/
theorem complexificationEquiv_tmulConj (u : ℂ ⊗[ℝ] SmoothForm I M ℝ k) :
    complexificationEquiv (tmulConj _ u) =
      mapCoeff (Complex.conjCLE : ℂ →L[ℝ] ℂ) (complexificationEquiv u) := by
  induction u using TensorProduct.inductionOn with
  | add u v hu hv => simp [hu, hv]
  | tmul c ω =>
    rw [tmulConj_tmul, complexificationEquiv_tmul, complexificationEquiv_tmul,
      mapCoeff_conj_smul]
    congr 1
    apply Subtype.ext
    funext x
    ext v
    simp [RoughForm.mapCoeff_apply]

section ExteriorDerivative

variable [IsManifold I 2 M]

/-- The complexification equivalence commutes with exterior differentiation. -/
theorem complexificationEquiv_baseChange_mextDerivₗ (u : ℂ ⊗[ℝ] SmoothForm I M ℝ k) :
    complexificationEquiv ((mextDerivₗ I (F := ℝ) k).baseChange ℂ u) =
      mextDerivₗ I k (complexificationEquiv u) := by
  induction u using TensorProduct.inductionOn with
  | add u v hu hv => simp [hu, hv]
  | tmul c ω => simp

/-- A complex-valued smooth form is closed exactly when its real and imaginary parts are closed. -/
theorem mextDerivₗ_eq_zero_iff_realPart_imaginaryPart (ω : SmoothForm I M ℂ k) :
    mextDerivₗ I k ω = 0 ↔
      mextDerivₗ I k (mapCoeff Complex.reCLM ω) = 0 ∧
        mextDerivₗ I k (mapCoeff Complex.imCLM ω) = 0 := by
  constructor
  · intro h
    simp [h]
  · rintro ⟨hRe, hIm⟩
    have h := ofReal_realPart_add_I_smul_ofReal_imaginaryPart (mextDerivₗ I k ω)
    simpa [← mextDerivₗ_mapCoeff, hRe, hIm] using h.symm

/-- A complex-valued form has a smooth primitive exactly when its real and imaginary parts
both have smooth primitives. -/
theorem exists_mextDerivₗ_eq_iff_realPart_imaginaryPart (ω : SmoothForm I M ℂ (k + 1)) :
    (∃ η : SmoothForm I M ℂ k, mextDerivₗ I k η = ω) ↔
      (∃ α : SmoothForm I M ℝ k, mextDerivₗ I k α = mapCoeff Complex.reCLM ω) ∧
        (∃ β : SmoothForm I M ℝ k, mextDerivₗ I k β = mapCoeff Complex.imCLM ω) := by
  constructor
  · rintro ⟨η, rfl⟩
    exact ⟨⟨mapCoeff Complex.reCLM η, mextDerivₗ_mapCoeff _ _⟩,
      ⟨mapCoeff Complex.imCLM η, mextDerivₗ_mapCoeff _ _⟩⟩
  · rintro ⟨⟨α, hα⟩, ⟨β, hβ⟩⟩
    refine ⟨mapCoeff Complex.ofRealCLM α + Complex.I • mapCoeff Complex.ofRealCLM β, ?_⟩
    simp [hα, hβ]

end ExteriorDerivative

section Pullback

open scoped ContDiff

variable {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' 1 M']

/-- The complexification equivalence is natural for smooth pullback. -/
theorem complexificationEquiv_baseChange_mpullback (f : M → M') (hf : ContMDiff I I' ∞ f)
    (u : ℂ ⊗[ℝ] SmoothForm I' M' ℝ k) :
    complexificationEquiv ((mpullback f hf).baseChange ℂ u) =
      mpullback f hf (complexificationEquiv u) := by
  induction u using TensorProduct.inductionOn with
  | add u v hu hv => simp [hu, hv]
  | tmul c φ => simp

end Pullback

end TauCeti.SmoothForm
