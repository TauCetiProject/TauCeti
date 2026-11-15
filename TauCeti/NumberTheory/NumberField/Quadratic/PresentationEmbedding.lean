/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Quadratic.ComplexEmbedding
public import TauCeti.NumberTheory.QuadraticOrder.Embedding

/-!
# Complex embeddings of presented imaginary quadratic fields

A chosen square root `δ` of a negative integer `D` in a quadratic number field determines
an embedding into `ℂ`: transport `QuadraticAlgebra.complexEmbedding` through
`TauCeti.QuadraticOrder.algEquivOfSqrt`. It is the unique embedding sending `δ` to
`√(-D) * I`, equivalently the unique one sending `δ` into the upper half-plane.

Isomorphisms between two such presentations send the chosen root to the chosen root or its
negative. The corresponding complex embeddings therefore commute with the isomorphism or
commute after complex conjugation. These comparisons fix the orientation when transporting
quadratic orders and their ideal lattices into `ℂ`.
-/

public section

open QuadraticAlgebra Complex ComplexConjugate

namespace TauCeti.QuadraticOrder

variable {K L M : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Field M] [NumberField M]
variable (D : ℤ) [Fact (¬ IsSquare D)]
variable (δ : K) (hδ : δ ^ 2 = (D : K)) (hK : Module.finrank ℚ K = 2)

/-- The embedding of a presented quadratic field for which the chosen root has
nonnegative imaginary part. -/
noncomputable def complexEmbeddingOfSqrt (hD : (D : ℚ) ≤ 0) : K →ₐ[ℚ] ℂ :=
  (complexEmbedding hD).comp (algEquivOfSqrt D δ hδ hK).symm.toAlgHom

/-- In model coordinates the transported embedding is the distinguished model embedding. -/
theorem complexEmbeddingOfSqrt_apply_algEquivOfSqrt (hD : (D : ℚ) ≤ 0)
    (z : QuadraticAlgebra ℚ (D : ℚ) 0) :
    complexEmbeddingOfSqrt D δ hδ hK hD (algEquivOfSqrt D δ hδ hK z) =
      complexEmbedding hD z := by
  simp only [complexEmbeddingOfSqrt, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply]

/-- The chosen square root maps to the square root with nonnegative imaginary part. -/
@[simp] theorem complexEmbeddingOfSqrt_apply_sqrt (hD : (D : ℚ) ≤ 0) :
    complexEmbeddingOfSqrt D δ hδ hK hD δ = (√(-(D : ℝ)) : ℂ) * I := by
  simpa using complexEmbeddingOfSqrt_apply_algEquivOfSqrt D δ hδ hK hD ω

/-- An embedding is the transported distinguished embedding exactly when it has the prescribed
value on the chosen square root. -/
theorem eq_complexEmbeddingOfSqrt_iff (hD : (D : ℚ) ≤ 0) (φ : K →ₐ[ℚ] ℂ) :
    φ = complexEmbeddingOfSqrt D δ hδ hK hD ↔
      φ δ = (√(-(D : ℝ)) : ℂ) * I := by
  constructor
  · rintro rfl
    exact complexEmbeddingOfSqrt_apply_sqrt D δ hδ hK hD
  · intro hφ
    have h : φ.comp (algEquivOfSqrt D δ hδ hK).toAlgHom = complexEmbedding hD := by
      apply QuadraticAlgebra.algHom_ext
      simpa using hφ
    ext x
    obtain ⟨z, rfl⟩ := (algEquivOfSqrt D δ hδ hK).surjective x
    simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      complexEmbeddingOfSqrt_apply_algEquivOfSqrt] using AlgHom.congr_fun h z

/-- Positivity of the imaginary part of the root characterizes the distinguished embedding. -/
theorem eq_complexEmbeddingOfSqrt_iff_im_pos (hD : (D : ℚ) < 0) (φ : K →ₐ[ℚ] ℂ) :
    φ = complexEmbeddingOfSqrt D δ hδ hK hD.le ↔ 0 < (φ δ).im := by
  have h := QuadraticAlgebra.ringHom_eq_complexEmbedding_iff hD
    (φ.comp (algEquivOfSqrt D δ hδ hK).toAlgHom).toRingHom
  constructor
  · rintro rfl
    have hpos : 0 < -(D : ℝ) := by exact_mod_cast neg_pos.mpr hD
    simpa using Real.sqrt_pos.mpr hpos
  · intro hφ
    apply (eq_complexEmbeddingOfSqrt_iff D δ hδ hK hD.le φ).mpr
    have heq := h.mpr (by simpa using hφ)
    simpa using RingHom.congr_fun heq ω

variable (η : L) (hη : η ^ 2 = (D : L)) (hL : Module.finrank ℚ L = 2)

/-- Root-preserving algebra maps preserve the distinguished complex embedding. -/
theorem complexEmbeddingOfSqrt_comp_of_map_sqrt (hD : (D : ℚ) ≤ 0)
    (σ : K →ₐ[ℚ] L) (hσ : σ δ = η) :
    (complexEmbeddingOfSqrt D η hη hL hD).comp σ =
      complexEmbeddingOfSqrt D δ hδ hK hD := by
  apply (eq_complexEmbeddingOfSqrt_iff D δ hδ hK hD _).mpr
  simp [hσ]

/-- Root-reversing algebra maps conjugate the distinguished complex embedding. -/
theorem complexEmbeddingOfSqrt_comp_of_map_sqrt_eq_neg (hD : (D : ℚ) ≤ 0)
    (σ : K →ₐ[ℚ] L) (hσ : σ δ = -η) :
    (complexEmbeddingOfSqrt D η hη hL hD).comp σ =
      (Complex.conjAe.toAlgHom.restrictScalars ℚ).comp
        (complexEmbeddingOfSqrt D δ hδ hK hD) := by
  have h : ((complexEmbeddingOfSqrt D η hη hL hD).comp σ).comp
      (algEquivOfSqrt D δ hδ hK).toAlgHom =
      ((Complex.conjAe.toAlgHom.restrictScalars ℚ).comp
        (complexEmbeddingOfSqrt D δ hδ hK hD)).comp
          (algEquivOfSqrt D δ hδ hK).toAlgHom := by
    apply QuadraticAlgebra.algHom_ext
    simp [hσ]
  ext x
  obtain ⟨z, rfl⟩ := (algEquivOfSqrt D δ hδ hK).surjective x
  exact AlgHom.congr_fun h z

/-- Pullback preserves the distinguished embedding if and only if it preserves the root. -/
@[simp] theorem complexEmbeddingOfSqrt_comp_eq_iff (hD : (D : ℚ) ≤ 0) (σ : K →ₐ[ℚ] L) :
    (complexEmbeddingOfSqrt D η hη hL hD).comp σ =
      complexEmbeddingOfSqrt D δ hδ hK hD ↔ σ δ = η := by
  constructor
  · intro h
    apply (complexEmbeddingOfSqrt D η hη hL hD).injective
    simpa using AlgHom.congr_fun h δ
  · exact complexEmbeddingOfSqrt_comp_of_map_sqrt D δ hδ hK η hη hL hD σ

/-- Pullback conjugates the distinguished embedding if and only if it reverses the root. -/
@[simp] theorem complexEmbeddingOfSqrt_comp_eq_conjugate_iff (hD : (D : ℚ) ≤ 0)
    (σ : K →ₐ[ℚ] L) :
    (complexEmbeddingOfSqrt D η hη hL hD).comp σ =
        (Complex.conjAe.toAlgHom.restrictScalars ℚ).comp
          (complexEmbeddingOfSqrt D δ hδ hK hD) ↔ σ δ = -η := by
  constructor
  · intro h
    apply (complexEmbeddingOfSqrt D η hη hL hD).injective
    simpa using AlgHom.congr_fun h δ
  · exact complexEmbeddingOfSqrt_comp_of_map_sqrt_eq_neg D δ hδ hK η hη hL hD σ

/-- Every algebra map between presentations preserves or conjugates the chosen embedding. -/
theorem complexEmbeddingOfSqrt_comp_eq_or_eq_conjugate (hD : (D : ℚ) ≤ 0)
    (σ : K →ₐ[ℚ] L) :
    (complexEmbeddingOfSqrt D η hη hL hD).comp σ =
        complexEmbeddingOfSqrt D δ hδ hK hD ∨
      (complexEmbeddingOfSqrt D η hη hL hD).comp σ =
        (Complex.conjAe.toAlgHom.restrictScalars ℚ).comp
          (complexEmbeddingOfSqrt D δ hδ hK hD) := by
  have hs : (σ δ) ^ 2 = η ^ 2 := by rw [← map_pow, hδ, map_intCast, hη]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
  · exact Or.inl (complexEmbeddingOfSqrt_comp_of_map_sqrt D δ hδ hK η hη hL hD σ h)
  · exact Or.inr (complexEmbeddingOfSqrt_comp_of_map_sqrt_eq_neg D δ hδ hK η hη hL hD σ h)

/-- The inverse of a root-preserving isomorphism also preserves the chosen embeddings. -/
theorem complexEmbeddingOfSqrt_comp_symm_of_map_sqrt (hD : (D : ℚ) ≤ 0)
    (σ : K ≃ₐ[ℚ] L) (hσ : σ δ = η) :
    (complexEmbeddingOfSqrt D δ hδ hK hD).comp σ.symm.toAlgHom =
      complexEmbeddingOfSqrt D η hη hL hD := by
  apply complexEmbeddingOfSqrt_comp_of_map_sqrt D η hη hL δ hδ hK hD σ.symm.toAlgHom
  exact σ.symm_apply_eq.mpr hσ.symm

/-- Composing root-preserving identifications preserves the chosen embedding. -/
theorem complexEmbeddingOfSqrt_comp_trans_of_map_sqrt (hD : (D : ℚ) ≤ 0)
    (ζ : M) (hζ : ζ ^ 2 = (D : M)) (hM : Module.finrank ℚ M = 2)
    (σ : K ≃ₐ[ℚ] L) (τ : L ≃ₐ[ℚ] M) (hσ : σ δ = η) (hτ : τ η = ζ) :
    (complexEmbeddingOfSqrt D ζ hζ hM hD).comp (σ.trans τ).toAlgHom =
      complexEmbeddingOfSqrt D δ hδ hK hD := by
  apply complexEmbeddingOfSqrt_comp_of_map_sqrt D δ hδ hK ζ hζ hM hD (σ.trans τ).toAlgHom
  simpa using (congrArg τ hσ).trans hτ

end TauCeti.QuadraticOrder
