/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Quadratic.ComplexEmbedding
public import TauCeti.NumberTheory.QuadraticOrder.Embedding

/-!
# The distinguished complex embedding of a presented imaginary quadratic field

Let `K` be a quadratic number field presented by a square root `θ ∈ K` of a negative integer `d`.
Evaluation at `θ` identifies the model `ℚ(√d) = QuadraticAlgebra ℚ d 0` with `K`
(`TauCeti.QuadraticOrder.algEquivOfSqrt`), and the model carries the distinguished embedding
`QuadraticAlgebra.complexEmbedding`, `ω ↦ √(-d) · i`. Their composite
`TauCeti.QuadraticOrder.complexEmbeddingOfSqrt` is the complex embedding `ι_K` of `K` that sends
`θ` to the square root `√(-d) · i` of `d` in the upper half-plane. This file proves that this
property characterizes `ι_K`, and that `ι_K` is natural in the presentation:

* it is compatible with the model equivalences: on the model `ℚ(√d)` presented by `ω` it is the
  distinguished embedding, and its composite with the model equivalence `ℚ(√d) ≃ₐ[ℚ] K` is the
  distinguished embedding of the model;
* along a `ℚ`-isomorphism `σ : K ≃ₐ[ℚ] L` it is transported to the embedding of `L` presented by
  `σ θ`. If `L` is presented by `η` with `η² = d`, then `σ θ = ±η`, and `ι_L ∘ σ` is `ι_K` when
  `σ θ = η` and the complex conjugate of `ι_K` when `σ θ = -η`;
* rescaling the presentation by a rational `u`, from `θ` to `η = u θ` with `η² = u² d`, keeps
  `ι_K` when `u > 0` and conjugates it when `u < 0`. In particular `-θ` presents the complex
  conjugate embedding. These are the presented-field counterparts of the comparisons
  `QuadraticAlgebra.complexEmbedding_comp_smulOmegaEquiv_of_pos` and
  `QuadraticAlgebra.complexEmbedding_comp_smulOmegaEquiv_of_neg` between the models.

These fix the orientation of an imaginary quadratic field together with its presentation, so that
complex lattices, upper half-plane points and singular moduli attached to `K` do not depend on
further choices.

## Main definitions and results

* `TauCeti.QuadraticOrder.complexEmbeddingOfSqrt`: the embedding `ι_K : K →ₐ[ℚ] ℂ`.
* `TauCeti.QuadraticOrder.complexEmbeddingOfSqrt_apply_sqrt`: `ι_K θ = √(-d) · i`.
* `TauCeti.QuadraticOrder.eq_complexEmbeddingOfSqrt_iff`: `ι_K` is the only `ℚ`-algebra map
  `K → ℂ` sending `θ` to `√(-d) · i`.
* `TauCeti.QuadraticOrder.ringHom_eq_complexEmbeddingOfSqrt_iff`: a complex embedding of `K` is
  `ι_K` exactly when it sends `θ` into the upper half-plane.
* `TauCeti.QuadraticOrder.ringHom_eq_complexEmbeddingOfSqrt_or_eq_conjugate`: `ι_K` and its
  conjugate are the two complex embeddings of `K`.
* `TauCeti.QuadraticOrder.complexEmbeddingOfSqrt_algEquivOfSqrt`,
  `TauCeti.QuadraticOrder.ringHom_comp_algEquivOfSqrt_eq_complexEmbedding_iff`,
  `TauCeti.QuadraticOrder.complexEmbeddingOfSqrt_omega`: compatibility with the model
  equivalences, whose composites with `ℚ`-isomorphisms are described by
  `TauCeti.QuadraticOrder.algEquivOfSqrt_trans`.
* `TauCeti.QuadraticOrder.complexEmbeddingOfSqrt_algEquiv_apply`,
  `TauCeti.QuadraticOrder.complexEmbeddingOfSqrt_apply_algEquiv_of_apply_eq`,
  `TauCeti.QuadraticOrder.complexEmbeddingOfSqrt_apply_algEquiv_of_apply_eq_neg`: naturality
  along `ℚ`-isomorphisms.
* `TauCeti.QuadraticOrder.complexEmbeddingOfSqrt_eq_of_eq_smul_of_pos`,
  `TauCeti.QuadraticOrder.complexEmbeddingOfSqrt_apply_of_eq_smul_of_neg`,
  `TauCeti.QuadraticOrder.complexEmbeddingOfSqrt_neg_apply`: rescaling the presentation.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7 (the embedding `ℚ(√D) ⊆ ℂ` with `√D = i √(-D)`).
-/

public section

open Complex ComplexConjugate Module NumberField QuadraticAlgebra

namespace TauCeti.QuadraticOrder

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]

private theorem sqrt_neg_intCast_pos {d : ℤ} (hd : d < 0) : 0 < √(-(d : ℝ)) :=
  Real.sqrt_pos.mpr (by simpa using hd)

/-- **The distinguished complex embedding of a presented imaginary quadratic field.** For a
quadratic number field `K` and a square root `θ ∈ K` of a negative integer `d`, this is the
composite of the model equivalence `K ≃ₐ[ℚ] ℚ(√d)`, sending `θ` to `ω`, with the distinguished
embedding `QuadraticAlgebra.complexEmbedding` of the model. It sends `θ` to `√(-d) · i`
(`complexEmbeddingOfSqrt_apply_sqrt`), and is the only `ℚ`-algebra map `K → ℂ` doing so
(`eq_complexEmbeddingOfSqrt_iff`). -/
noncomputable def complexEmbeddingOfSqrt (d : ℤ) (hd : d < 0) (θ : K) (hθ : θ ^ 2 = (d : K))
    (hK : finrank ℚ K = 2) : K →ₐ[ℚ] ℂ :=
  haveI : Fact (¬ IsSquare d) := ⟨not_isSquare_of_neg hd⟩
  (complexEmbedding (a := (d : ℚ)) (by exact_mod_cast hd.le)).comp
    (algEquivOfSqrt d θ hθ hK).symm.toAlgHom

section Basic

variable {d : ℤ} (hd : d < 0) {θ : K} (hθ : θ ^ 2 = (d : K)) (hK : finrank ℚ K = 2)

/-- `ι_K` is the distinguished embedding of the model, read through the model equivalence. -/
theorem complexEmbeddingOfSqrt_apply [Fact (¬ IsSquare d)] (x : K) :
    complexEmbeddingOfSqrt d hd θ hθ hK x =
      complexEmbedding (a := (d : ℚ)) (by exact_mod_cast hd.le)
        ((algEquivOfSqrt d θ hθ hK).symm x) :=
  (rfl)

/-- **Compatibility with the model equivalence**: `ι_K` composed with the model equivalence
`ℚ(√d) ≃ₐ[ℚ] K` is the distinguished embedding of the model. -/
-- Not `@[simp]`: `algEquivOfSqrt_apply` rewrites the argument to `z.re • 1 + z.im • θ` first, and
-- `complexEmbeddingOfSqrt_apply_sqrt` then evaluates the result.
theorem complexEmbeddingOfSqrt_algEquivOfSqrt [Fact (¬ IsSquare d)]
    (z : QuadraticAlgebra ℚ (d : ℚ) 0) :
    complexEmbeddingOfSqrt d hd θ hθ hK (algEquivOfSqrt d θ hθ hK z) =
      complexEmbedding (a := (d : ℚ)) (by exact_mod_cast hd.le) z := by
  rw [complexEmbeddingOfSqrt_apply, AlgEquiv.symm_apply_apply]

/-- **`ι_K` sends the chosen square root `θ` of `d` to `√(-d) · i`**, the square root of `d` in
the upper half-plane. -/
@[simp]
theorem complexEmbeddingOfSqrt_apply_sqrt :
    complexEmbeddingOfSqrt d hd θ hθ hK θ = (√(-(d : ℝ)) : ℂ) * I := by
  have : Fact (¬ IsSquare d) := ⟨not_isSquare_of_neg hd⟩
  have h := complexEmbeddingOfSqrt_algEquivOfSqrt hd hθ hK ω
  rwa [algEquivOfSqrt_apply_omega, complexEmbedding_omega, Rat.cast_intCast] at h

/-- **`ι_K` is characterized by its value at `θ`**: a `ℚ`-algebra map `K → ℂ` is `ι_K` exactly
when it sends `θ` to `√(-d) · i`. -/
theorem eq_complexEmbeddingOfSqrt_iff (φ : K →ₐ[ℚ] ℂ) :
    φ = complexEmbeddingOfSqrt d hd θ hθ hK ↔ φ θ = (√(-(d : ℝ)) : ℂ) * I := by
  have : Fact (¬ IsSquare d) := ⟨not_isSquare_of_neg hd⟩
  refine ⟨fun h ↦ h ▸ complexEmbeddingOfSqrt_apply_sqrt hd hθ hK, fun h ↦ ?_⟩
  set e := algEquivOfSqrt d θ hθ hK
  have hω : e ω = θ := algEquivOfSqrt_apply_omega d θ hθ hK
  have hcomp : φ.comp e.toAlgHom = (complexEmbeddingOfSqrt d hd θ hθ hK).comp e.toAlgHom :=
    algHom_ext (by simp [hω, h])
  ext x
  simpa using AlgHom.congr_fun hcomp (e.symm x)

/-- **Transport along the model equivalence**: a complex embedding of `K` is `ι_K` exactly when its
composite with the model equivalence `ℚ(√d) ≃ₐ[ℚ] K` is the distinguished embedding of the
model. -/
-- Not `@[simp]`: it is the transport step behind the `K`-side characterizations below, which are
-- the intended interface.
theorem ringHom_comp_algEquivOfSqrt_eq_complexEmbedding_iff [Fact (¬ IsSquare d)]
    (φ : K →+* ℂ) :
    φ.comp (algEquivOfSqrt d θ hθ hK : QuadraticAlgebra ℚ (d : ℚ) 0 →+* K) =
        (complexEmbedding (a := (d : ℚ)) (by exact_mod_cast hd.le) :
          QuadraticAlgebra ℚ (d : ℚ) 0 →+* ℂ) ↔
      φ = (complexEmbeddingOfSqrt d hd θ hθ hK : K →+* ℂ) := by
  refine ⟨fun h ↦ RingHom.ext fun x ↦ ?_, ?_⟩
  · rw [RingHom.coe_coe, complexEmbeddingOfSqrt_apply]
    simpa using RingHom.congr_fun h ((algEquivOfSqrt d θ hθ hK).symm x)
  · rintro rfl
    ext z
    exact complexEmbeddingOfSqrt_algEquivOfSqrt hd hθ hK z

/-- **The upper half-plane picks out `ι_K`**: a complex embedding of `K` is `ι_K` exactly when it
sends `θ` to a complex number with positive imaginary part. -/
theorem ringHom_eq_complexEmbeddingOfSqrt_iff (φ : K →+* ℂ) :
    φ = (complexEmbeddingOfSqrt d hd θ hθ hK : K →+* ℂ) ↔ 0 < (φ θ).im := by
  have : Fact (¬ IsSquare d) := ⟨not_isSquare_of_neg hd⟩
  rw [← ringHom_comp_algEquivOfSqrt_eq_complexEmbedding_iff hd hθ hK,
    ringHom_eq_complexEmbedding_iff (by exact_mod_cast hd), RingHom.comp_apply, RingHom.coe_coe,
    algEquivOfSqrt_apply_omega]

/-- **The two complex embeddings of a presented imaginary quadratic field**: every complex
embedding of `K` is `ι_K` or its complex conjugate. -/
theorem ringHom_eq_complexEmbeddingOfSqrt_or_eq_conjugate (φ : K →+* ℂ) :
    φ = (complexEmbeddingOfSqrt d hd θ hθ hK : K →+* ℂ) ∨
      φ = ComplexEmbedding.conjugate (complexEmbeddingOfSqrt d hd θ hθ hK : K →+* ℂ) := by
  have : Fact (¬ IsSquare d) := ⟨not_isSquare_of_neg hd⟩
  set e := algEquivOfSqrt d θ hθ hK
  rcases ringHom_eq_or_eq_conjugate (by exact_mod_cast hd.le)
      (φ.comp (e : QuadraticAlgebra ℚ (d : ℚ) 0 →+* K)) with h | h
  · exact Or.inl ((ringHom_comp_algEquivOfSqrt_eq_complexEmbedding_iff hd hθ hK φ).mp h)
  · refine Or.inr (RingHom.ext fun x ↦ ?_)
    rw [ComplexEmbedding.conjugate_coe_eq, RingHom.coe_coe, complexEmbeddingOfSqrt_apply]
    simpa [e, ComplexEmbedding.conjugate_coe_eq] using RingHom.congr_fun h (e.symm x)

end Basic

section Model

variable {d : ℤ} [Fact (¬ IsSquare d)]

/-- **On the model, `ι_K` is the distinguished embedding**: the model `ℚ(√d)`, presented by its
generator `ω`, has `ι = QuadraticAlgebra.complexEmbedding`. -/
@[simp]
theorem complexEmbeddingOfSqrt_omega (hd : d < 0)
    (hω : (ω : QuadraticAlgebra ℚ (d : ℚ) 0) ^ 2 = (d : _))
    (hK : finrank ℚ (QuadraticAlgebra ℚ (d : ℚ) 0) = 2) :
    complexEmbeddingOfSqrt d hd ω hω hK = complexEmbedding (by exact_mod_cast hd.le) := by
  refine AlgHom.ext fun z ↦ ?_
  rw [complexEmbeddingOfSqrt_apply, algEquivOfSqrt_omega, AlgEquiv.refl_symm, AlgEquiv.coe_refl,
    id_eq]

end Model

section Naturality

variable {d : ℤ} {θ : K} (hθ : θ ^ 2 = (d : K)) (hK : finrank ℚ K = 2)

variable (hd : d < 0)

/-- **Naturality of `ι` along an isomorphism**: transporting the presentation `θ` of `K` along a
`ℚ`-isomorphism `σ : K ≃ₐ[ℚ] L` gives the presentation `σ θ` of `L`, whose distinguished embedding
pulls back along `σ` to that of `K`. -/
@[simp]
theorem complexEmbeddingOfSqrt_algEquiv_apply (σ : K ≃ₐ[ℚ] L) (x : K) :
    complexEmbeddingOfSqrt d hd (σ θ) (sq_map_of_sq_eq_intCast σ hθ)
        (σ.toLinearEquiv.finrank_eq.symm.trans hK) (σ x) =
      complexEmbeddingOfSqrt d hd θ hθ hK x := by
  have h := (eq_complexEmbeddingOfSqrt_iff hd hθ hK
    ((complexEmbeddingOfSqrt d hd (σ θ) (sq_map_of_sq_eq_intCast σ hθ)
      (σ.toLinearEquiv.finrank_eq.symm.trans hK)).comp (σ : K →ₐ[ℚ] L))).mpr (by simp)
  exact AlgHom.congr_fun h x

/-- **Rescaling the presentation by a positive rational keeps the embedding.** If `θ² = d`,
`η² = e` with `e < 0`, and `η = u θ` for a rational `u > 0`, then the presentations `θ` and `η` of
`K` define the same distinguished embedding. -/
theorem complexEmbeddingOfSqrt_eq_of_eq_smul_of_pos {e : ℤ} (he : e < 0) {η : K}
    (hη : η ^ 2 = (e : K)) {u : ℚ} (hu : 0 < u) (h : η = u • θ) :
    complexEmbeddingOfSqrt e he η hη hK = complexEmbeddingOfSqrt d hd θ hθ hK := by
  have hde : (e : ℝ) = (u : ℝ) ^ 2 * d := by
    have hK' : ((e : ℚ) : K) = ((u ^ 2 * d : ℚ) : K) := by
      rw [h, Rat.smul_def] at hη
      push_cast
      linear_combination -hη + (u : K) ^ 2 * hθ
    have := (Rat.cast_injective (α := K) hK')
    exact_mod_cast this
  have hs : √(-(e : ℝ)) = u * √(-(d : ℝ)) := by
    rw [hde, ← mul_neg, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by exact_mod_cast hu.le)]
  symm
  rw [eq_complexEmbeddingOfSqrt_iff, h, map_rat_smul, complexEmbeddingOfSqrt_apply_sqrt, hs,
    Rat.smul_def]
  push_cast
  ring

/-- **The opposite presentation gives the conjugate embedding**: `-θ` presents `K` with the complex
conjugate of the embedding presented by `θ`. -/
theorem complexEmbeddingOfSqrt_neg_apply (x : K) :
    complexEmbeddingOfSqrt d hd (-θ) (by rw [neg_sq, hθ]) hK x =
      conj (complexEmbeddingOfSqrt d hd θ hθ hK x) := by
  have hpos := sqrt_neg_intCast_pos hd
  have h := (ringHom_eq_complexEmbeddingOfSqrt_iff hd (by rw [neg_sq, hθ]) hK
    (ComplexEmbedding.conjugate (complexEmbeddingOfSqrt d hd θ hθ hK : K →+* ℂ))).mpr
    (by simpa [ComplexEmbedding.conjugate_coe_eq] using hpos)
  simpa [ComplexEmbedding.conjugate_coe_eq] using (RingHom.congr_fun h x).symm

/-- **Rescaling the presentation by a negative rational conjugates the embedding.** If `θ² = d`,
`η² = e` with `e < 0`, and `η = u θ` for a rational `u < 0`, then the distinguished embedding
presented by `η` is the complex conjugate of the one presented by `θ`. -/
theorem complexEmbeddingOfSqrt_apply_of_eq_smul_of_neg {e : ℤ} (he : e < 0) {η : K}
    (hη : η ^ 2 = (e : K)) {u : ℚ} (hu : u < 0) (h : η = u • θ) (x : K) :
    complexEmbeddingOfSqrt e he η hη hK x = conj (complexEmbeddingOfSqrt d hd θ hθ hK x) := by
  have hη' : (-η) ^ 2 = (e : K) := by rw [neg_sq, hη]
  have h' : -η = (-u) • θ := by rw [h, neg_smul]
  rw [← complexEmbeddingOfSqrt_eq_of_eq_smul_of_pos hθ hK hd he hη' (neg_pos.mpr hu) h',
    complexEmbeddingOfSqrt_neg_apply hη hK he, conj_conj]

variable {η : L} (hη : η ^ 2 = (d : L)) (hL : finrank ℚ L = 2)

/-- **Naturality, same orientation.** If a `ℚ`-isomorphism `σ : K ≃ₐ[ℚ] L` sends the presentation
`θ` of `K` to the presentation `η` of `L`, then `ι_L ∘ σ = ι_K`. -/
theorem complexEmbeddingOfSqrt_apply_algEquiv_of_apply_eq (σ : K ≃ₐ[ℚ] L) (h : σ θ = η)
    (x : K) :
    complexEmbeddingOfSqrt d hd η hη hL (σ x) = complexEmbeddingOfSqrt d hd θ hθ hK x := by
  subst h
  exact complexEmbeddingOfSqrt_algEquiv_apply hθ hK hd σ x

/-- **Naturality, opposite orientation.** If a `ℚ`-isomorphism `σ : K ≃ₐ[ℚ] L` sends the
presentation `θ` of `K` to `-η` for the presentation `η` of `L`, then `ι_L ∘ σ` is the complex
conjugate of `ι_K`. -/
theorem complexEmbeddingOfSqrt_apply_algEquiv_of_apply_eq_neg (σ : K ≃ₐ[ℚ] L) (h : σ θ = -η)
    (x : K) :
    complexEmbeddingOfSqrt d hd η hη hL (σ x) = conj (complexEmbeddingOfSqrt d hd θ hθ hK x) := by
  have hη' : η = -σ θ := by rw [h, neg_neg]
  subst hη'
  rw [complexEmbeddingOfSqrt_neg_apply (sq_map_of_sq_eq_intCast σ hθ) hL hd,
    complexEmbeddingOfSqrt_algEquiv_apply hθ hK hd σ x]

end Naturality

end TauCeti.QuadraticOrder
