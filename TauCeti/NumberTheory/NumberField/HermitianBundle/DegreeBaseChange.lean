/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import TauCeti.NumberTheory.NumberField.HermitianBundle.BaseChange
public import TauCeti.NumberTheory.NumberField.HermitianBundle.Degree

/-!
# The Arakelov degree under base change: the archimedean part

Let `L/K` be a finite extension of number fields and `(E, h)` a hermitian metric over `𝓞 K`. Every
complex embedding `σ` of `K` has exactly `[L : K]` extensions `τ` to `L`
(`TauCeti.NumberField.card_extension`), and the base-changed metric at `τ` is `h` at `τ|K`. So
for a section `s : E` the archimedean term of the degree of `1 ⊗ s` in `Ē_{𝓞 L}` is `[L : K]`
times that of `s` (`TauCeti.HermitianMetric.sum_log_norm_baseChange_one_tmul`). When `s`
generates `E`, `1 ⊗ s` generates `𝓞 L ⊗ E`, both index terms vanish, and
`deg(Ē_{𝓞 L}) = [L : K] deg(Ē)` (`TauCeti.HermitianMetric.sectionDegree_baseChange_of_span_eq_top`).

This is the archimedean half of ArakelovGeometryAndAbelianHeights §1.6 ("each `σ ∈ Σ_K` has
exactly `[L:K]` extensions `τ ∈ Σ_L` with `‖s‖_τ = ‖s‖_σ`") and the statement for lines with a
generating section.

## Main statements

* `TauCeti.NumberField.card_extension`: `σ : K →+* ℂ` has `[L : K]` extensions to `L`.
* `TauCeti.NumberField.sum_comp_algebraMap`: `Σ_τ g(τ|K) = [L : K] Σ_σ g(σ)`.
* `TauCeti.HermitianMetric.sum_log_norm_baseChange_one_tmul`: the archimedean term of the degree
  is multiplied by `[L : K]` under base change.
* `TauCeti.HermitianMetric.span_one_tmul_eq_top`: base change of a generating section generates.
* `TauCeti.HermitianMetric.sectionDegree_baseChange_of_span_eq_top`: for a generating section,
  `deg(1 ⊗ s) = [L : K] deg(s)`.
-/

public noncomputable section

open scoped TensorProduct
open NumberField NumberField.ComplexEmbedding

namespace TauCeti

namespace NumberField

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- The extensions of `σ : K →+* ℂ` to `L` are the `K`-algebra maps `L → ℂ` for the algebra
structure `σ` on `ℂ`. -/
def extensionEquivAlgHom (σ : K →+* ℂ) :
    ComplexEmbedding.Extension L σ ≃ @AlgHom K L ℂ _ _ _ _ σ.toAlgebra :=
  letI := σ.toAlgebra
  { toFun τ := { τ.val with commutes' := fun x ↦ RingHom.congr_fun (Extension.comp_eq τ) x }
    invFun φ := ⟨φ.toRingHom, ⟨RingHom.ext fun x ↦ φ.commutes x⟩⟩
    left_inv _ := rfl
    right_inv _ := rfl }

variable (L) in
/-- **Each complex embedding of `K` has `[L : K]` extensions to `L`.** -/
theorem card_extension [CharZero K] (σ : K →+* ℂ) :
    Nat.card (ComplexEmbedding.Extension L σ) = Module.finrank K L := by
  let := σ.toAlgebra
  rw [Nat.card_congr (extensionEquivAlgHom σ), Nat.card_eq_fintype_card, AlgHom.card]

/-- Summing a function of the restriction `τ|K` over the complex embeddings `τ` of `L` gives
`[L : K]` times the sum over the complex embeddings of `K`. -/
theorem sum_comp_algebraMap [CharZero K] [Fintype (K →+* ℂ)] [Fintype (L →+* ℂ)] {M : Type*}
    [AddCommMonoid M] (g : (K →+* ℂ) → M) :
    ∑ τ : L →+* ℂ, g (τ.comp (algebraMap K L)) = Module.finrank K L • ∑ σ : K →+* ℂ, g σ := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun τ : L →+* ℂ ↦ τ.comp (algebraMap K L)),
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [Finset.sum_congr rfl fun τ hτ ↦ by rw [(Finset.mem_filter.1 hτ).2], Finset.sum_const]
  congr 1
  rw [← card_extension L σ, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp [ComplexEmbedding.liesOver_iff]

end NumberField

namespace HermitianMetric

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] (h : HermitianMetric K E)

/-- **The archimedean term under base change**: `Σ_τ log ‖1 ⊗ s‖_τ = [L : K] Σ_σ log ‖s‖_σ`,
since each `σ` has `[L : K]` extensions `τ`, at which `‖1 ⊗ s‖_τ = ‖s‖_σ`. -/
theorem sum_log_norm_baseChange_one_tmul (s : E) :
    ∑ τ : L →+* ℂ, Real.log (h.baseChange.norm τ (1 ⊗ₜ ((1 : 𝓞 L) ⊗ₜ s))) =
      Module.finrank K L * ∑ σ : K →+* ℂ, Real.log (h.norm σ (1 ⊗ₜ s)) := by
  simp only [norm_baseChange_tmul_tmul, map_one, norm_one, one_mul]
  rw [NumberField.sum_comp_algebraMap (fun σ ↦ Real.log (h.norm σ (1 ⊗ₜ s))), nsmul_eq_mul]

omit [NumberField K] [NumberField L] in
/-- If `s` generates `E`, then `1 ⊗ s` generates `𝓞 L ⊗ E`. -/
theorem span_one_tmul_eq_top {s : E} (hs : Submodule.span (𝓞 K) {s} = ⊤) :
    Submodule.span (𝓞 L) {(1 : 𝓞 L) ⊗ₜ[𝓞 K] s} = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun x ↦ ?_
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => exact add_mem hx hy
  | tmul a x =>
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 (hs ▸ Submodule.mem_top : x ∈ _)
    rw [Submodule.mem_span_singleton]
    refine ⟨a * algebraMap (𝓞 K) (𝓞 L) c, ?_⟩
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← TensorProduct.smul_tmul,
      Algebra.smul_def, mul_comm]

/-- **The degree under base change, for a generating section**: if `s` generates `E`, then
`deg(Ē_{𝓞 L}) = [L : K] deg(Ē)`, both computed with `s` and `1 ⊗ s`. -/
theorem sectionDegree_baseChange_of_span_eq_top {s : E} (hs : Submodule.span (𝓞 K) {s} = ⊤) :
    h.baseChange.sectionDegree ((1 : 𝓞 L) ⊗ₜ s) = Module.finrank K L * h.sectionDegree s := by
  rw [sectionDegree_def, sectionDegree_def, span_one_tmul_eq_top hs, hs,
    sum_log_norm_baseChange_one_tmul, Submodule.cardQuot_top]
  simp

end HermitianMetric

end TauCeti
