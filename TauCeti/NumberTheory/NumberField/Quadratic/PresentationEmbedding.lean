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

variable {K : Type*} [Field K] [NumberField K]
variable (D : ℤ) [Fact (¬ IsSquare D)]
variable (δ : K) (hδ : δ ^ 2 = (D : K)) (hK : Module.finrank ℚ K = 2)

/-- The embedding of a presented quadratic field for which the chosen root has
nonnegative imaginary part. -/
noncomputable def complexEmbeddingOfSqrt (hD : (D : ℚ) ≤ 0) : K →ₐ[ℚ] ℂ :=
  (complexEmbedding hD).comp (algEquivOfSqrt D δ hδ hK).symm.toAlgHom

/-- The chosen embedding is the model embedding composed with the inverse field identification. -/
theorem complexEmbeddingOfSqrt_def (hD : (D : ℚ) ≤ 0) :
    complexEmbeddingOfSqrt D δ hδ hK hD =
      (complexEmbedding hD).comp (algEquivOfSqrt D δ hδ hK).symm.toAlgHom := (rfl)

/-- Pullback to the quadratic model recovers its distinguished embedding. -/
@[simp] theorem complexEmbeddingOfSqrt_comp_algEquivOfSqrt (hD : (D : ℚ) ≤ 0) :
    (complexEmbeddingOfSqrt D δ hδ hK hD).comp (algEquivOfSqrt D δ hδ hK).toAlgHom =
      complexEmbedding hD := by
  simp [complexEmbeddingOfSqrt_def, AlgHom.comp_assoc]

/-- In model coordinates the transported embedding is the distinguished model embedding. -/
theorem complexEmbeddingOfSqrt_apply_algEquivOfSqrt (hD : (D : ℚ) ≤ 0)
    (z : QuadraticAlgebra ℚ (D : ℚ) 0) :
    complexEmbeddingOfSqrt D δ hδ hK hD (algEquivOfSqrt D δ hδ hK z) =
      complexEmbedding hD z :=
  AlgHom.congr_fun (complexEmbeddingOfSqrt_comp_algEquivOfSqrt D δ hδ hK hD) z

/-- The chosen square root maps to the square root with nonnegative imaginary part. -/
@[simp] theorem complexEmbeddingOfSqrt_apply_sqrt (hD : (D : ℚ) ≤ 0) :
    complexEmbeddingOfSqrt D δ hδ hK hD δ = (√(-(D : ℝ)) : ℂ) * I := by
  simpa only [algEquivOfSqrt_apply_omega, complexEmbedding_omega, Rat.cast_intCast] using
    complexEmbeddingOfSqrt_apply_algEquivOfSqrt D δ hδ hK hD ω

/-- An embedding is the transported distinguished embedding exactly when it has the prescribed
value on the chosen square root. -/
theorem eq_complexEmbeddingOfSqrt_iff (hD : (D : ℚ) ≤ 0) (φ : K →ₐ[ℚ] ℂ) :
    φ = complexEmbeddingOfSqrt D δ hδ hK hD ↔
      φ δ = (√(-(D : ℝ)) : ℂ) * I := by
  rw [← complexEmbeddingOfSqrt_apply_sqrt D δ hδ hK hD]
  exact ⟨fun h => AlgHom.congr_fun h δ, algHom_ext_of_sqrt D δ hδ hK⟩

/-- Positivity of the imaginary part of the root characterizes the distinguished embedding. -/
theorem eq_complexEmbeddingOfSqrt_iff_im_pos (hD : (D : ℚ) ≤ 0) (φ : K →ₐ[ℚ] ℂ) :
    φ = complexEmbeddingOfSqrt D δ hδ hK hD ↔ 0 < (φ δ).im := by
  have hD' : (D : ℚ) < 0 := hD.lt_of_ne fun h =>
    (Fact.out : ¬ IsSquare D) (Int.cast_eq_zero.mp h ▸ IsSquare.zero)
  have h := QuadraticAlgebra.ringHom_eq_complexEmbedding_iff hD'
    (φ.comp (algEquivOfSqrt D δ hδ hK).toAlgHom).toRingHom
  constructor
  · rintro rfl
    simpa [algEquivOfSqrt_apply_omega] using (h.mp (by simp))
  · intro hφ
    apply (eq_complexEmbeddingOfSqrt_iff D δ hδ hK hD φ).mpr
    have heq := h.mpr (by simpa [algEquivOfSqrt_apply_omega] using hφ)
    simpa [algEquivOfSqrt_apply_omega] using RingHom.congr_fun heq ω

/-- The conjugate embedding is characterized by the negative of the distinguished root value. -/
theorem eq_conjAe_comp_complexEmbeddingOfSqrt_iff (hD : (D : ℚ) ≤ 0) (φ : K →ₐ[ℚ] ℂ) :
    φ = (Complex.conjAe.toAlgHom.restrictScalars ℚ).comp (complexEmbeddingOfSqrt D δ hδ hK hD) ↔
      φ δ = -((√(-(D : ℝ)) : ℂ) * I) := by
  constructor
  · rintro rfl
    simp
  · intro h
    apply algHom_ext_of_sqrt D δ hδ hK
    simpa using h

/-- Negativity of the imaginary part of the root characterizes the conjugate embedding. -/
theorem eq_conjAe_comp_complexEmbeddingOfSqrt_iff_im_neg (hD : (D : ℚ) ≤ 0) (φ : K →ₐ[ℚ] ℂ) :
    φ = (Complex.conjAe.toAlgHom.restrictScalars ℚ).comp (complexEmbeddingOfSqrt D δ hδ hK hD) ↔
      (φ δ).im < 0 := by
  let c := Complex.conjAe.toAlgHom.restrictScalars ℚ
  have h := eq_complexEmbeddingOfSqrt_iff_im_pos D δ hδ hK hD (c.comp φ)
  constructor
  · rintro rfl
    simpa [c] using h.mp (AlgHom.ext fun x => by simp [c])
  · intro hφ
    have heq := h.mpr (by simpa [c] using hφ)
    exact AlgHom.ext fun x => by simpa [c] using congrArg conj (AlgHom.congr_fun heq x)

/-- The distinguished embedding for the opposite root is the conjugate embedding. -/
theorem complexEmbeddingOfSqrt_neg (hD : (D : ℚ) ≤ 0) :
    complexEmbeddingOfSqrt D (-δ) (by simpa using hδ) hK hD =
      (Complex.conjAe.toAlgHom.restrictScalars ℚ).comp (complexEmbeddingOfSqrt D δ hδ hK hD) := by
  apply (eq_conjAe_comp_complexEmbeddingOfSqrt_iff D δ hδ hK hD _).mpr
  simpa only [map_neg, neg_neg] using congrArg Neg.neg
    (complexEmbeddingOfSqrt_apply_sqrt D (-δ) (by simpa using hδ) hK hD)

/-- Every embedding is the distinguished embedding for the chosen root or its conjugate. -/
theorem eq_complexEmbeddingOfSqrt_or_eq_conjAe_comp (hD : (D : ℚ) ≤ 0) (φ : K →ₐ[ℚ] ℂ) :
    φ = complexEmbeddingOfSqrt D δ hδ hK hD ∨
      φ = (Complex.conjAe.toAlgHom.restrictScalars ℚ).comp
        (complexEmbeddingOfSqrt D δ hδ hK hD) := by
  have : Fact (¬ IsSquare (D : ℚ)) := ⟨Rat.isSquare_intCast_iff.not.mpr Fact.out⟩
  rcases QuadraticAlgebra.ringHom_eq_or_eq_conjugate hD
      (φ.comp (algEquivOfSqrt D δ hδ hK).toAlgHom).toRingHom with h | h
  · left
    apply (eq_complexEmbeddingOfSqrt_iff D δ hδ hK hD φ).mpr
    simpa [algEquivOfSqrt_apply_omega] using RingHom.congr_fun h ω
  · right
    apply (eq_conjAe_comp_complexEmbeddingOfSqrt_iff D δ hδ hK hD φ).mpr
    simpa [algEquivOfSqrt_apply_omega, NumberField.ComplexEmbedding.conjugate_coe_eq] using
      RingHom.congr_fun h ω

variable {L : Type*} [Field L] [NumberField L]
variable (η : L) (hη : η ^ 2 = (D : L)) (hL : Module.finrank ℚ L = 2)

/-- Root-preserving algebra maps preserve the distinguished complex embedding. -/
theorem complexEmbeddingOfSqrt_comp_of_map_sqrt (hD : (D : ℚ) ≤ 0)
    (σ : K →ₐ[ℚ] L) (hσ : σ δ = η) :
    (complexEmbeddingOfSqrt D η hη hL hD).comp σ =
      complexEmbeddingOfSqrt D δ hδ hK hD := by
  apply (eq_complexEmbeddingOfSqrt_iff D δ hδ hK hD _).mpr
  simp [hσ]

/-- A root-preserving algebra map does not change the complex image of an element. -/
theorem complexEmbeddingOfSqrt_apply_of_map_sqrt (hD : (D : ℚ) ≤ 0)
    (σ : K →ₐ[ℚ] L) (hσ : σ δ = η) (x : K) :
    complexEmbeddingOfSqrt D η hη hL hD (σ x) = complexEmbeddingOfSqrt D δ hδ hK hD x :=
  AlgHom.congr_fun (complexEmbeddingOfSqrt_comp_of_map_sqrt D δ hδ hK η hη hL hD σ hσ) x

/-- Root-reversing algebra maps conjugate the distinguished complex embedding. -/
theorem complexEmbeddingOfSqrt_comp_of_map_sqrt_eq_neg (hD : (D : ℚ) ≤ 0)
    (σ : K →ₐ[ℚ] L) (hσ : σ δ = -η) :
    (complexEmbeddingOfSqrt D η hη hL hD).comp σ =
      (Complex.conjAe.toAlgHom.restrictScalars ℚ).comp
        (complexEmbeddingOfSqrt D δ hδ hK hD) := by
  apply (eq_conjAe_comp_complexEmbeddingOfSqrt_iff D δ hδ hK hD _).mpr
  simp [hσ]

/-- A root-reversing algebra map conjugates the complex image of an element. -/
theorem complexEmbeddingOfSqrt_apply_of_map_sqrt_eq_neg (hD : (D : ℚ) ≤ 0)
    (σ : K →ₐ[ℚ] L) (hσ : σ δ = -η) (x : K) :
    complexEmbeddingOfSqrt D η hη hL hD (σ x) = conj (complexEmbeddingOfSqrt D δ hδ hK hD x) :=
  AlgHom.congr_fun (complexEmbeddingOfSqrt_comp_of_map_sqrt_eq_neg D δ hδ hK η hη hL hD σ hσ) x

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
@[simp] theorem complexEmbeddingOfSqrt_comp_eq_conjAe_comp_iff (hD : (D : ℚ) ≤ 0)
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
theorem complexEmbeddingOfSqrt_comp_eq_or_eq_conjAe_comp (hD : (D : ℚ) ≤ 0)
    (σ : K →ₐ[ℚ] L) :
    (complexEmbeddingOfSqrt D η hη hL hD).comp σ =
        complexEmbeddingOfSqrt D δ hδ hK hD ∨
      (complexEmbeddingOfSqrt D η hη hL hD).comp σ =
        (Complex.conjAe.toAlgHom.restrictScalars ℚ).comp
          (complexEmbeddingOfSqrt D δ hδ hK hD) :=
  eq_complexEmbeddingOfSqrt_or_eq_conjAe_comp D δ hδ hK hD _

end TauCeti.QuadraticOrder
