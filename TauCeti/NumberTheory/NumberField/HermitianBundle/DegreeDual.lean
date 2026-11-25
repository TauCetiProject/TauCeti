/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import TauCeti.NumberTheory.NumberField.HermitianBundle.Degree
public import TauCeti.NumberTheory.NumberField.HermitianBundle.Dual

/-!
# The Arakelov degree of the dual of a hermitian line

Let `(E, h)` be a hermitian metric over `𝓞 K` and `s : E` a generating section. Each complex fibre
`ℂ ⊗_σ E` is the line spanned by `1 ⊗ s`, so for a functional `f` on `E` the dual norm is
`‖f‖_σ = |σ(f s)| / ‖s‖_σ` (`TauCeti.HermitianMetric.norm_dual_one_tmul_mul_norm`). When `f s = 1`,
`f` generates `E^∨`, `‖f‖_σ = ‖s‖_σ⁻¹`, and `deg(Ē^∨) = -deg(Ē)`, both degrees computed with these
sections (`TauCeti.HermitianMetric.sectionDegree_dual_of_span_eq_top`).

This is the dual statement `deg(L^∨) = −deg(L)` of ArakelovGeometryAndAbelianHeights §1.5 for a
hermitian line with a generating section, the case `𝔞 = O_K` of the roadmap's computation, in which
`s^∨` lies in `L^∨` and `‖s^∨‖_σ = ‖s‖_σ^{−1}`.

## Main statements

* `TauCeti.HermitianMetric.exists_eq_smul_one_tmul`: the complex fibres are spanned by `1 ⊗ s`.
* `TauCeti.HermitianMetric.norm_dual_one_tmul_mul_norm`: `‖f‖_σ ‖s‖_σ = |σ(f s)|`.
* `TauCeti.HermitianMetric.span_singleton_dual_eq_top`: `f` with `f s = 1` generates `E^∨`.
* `TauCeti.HermitianMetric.sectionDegree_dual_of_span_eq_top`: `deg(Ē^∨) = -deg(Ē)`.
-/

public noncomputable section

open scoped TensorProduct ComplexConjugate
open NumberField NumberField.ComplexEmbedding

namespace TauCeti.HermitianMetric

variable {K : Type*} [Field K] {E : Type*} [AddCommGroup E] [Module (𝓞 K) E]
  (h : HermitianMetric K E)

/-- If `s` generates `E`, every vector of the complex fibre at `σ` is a complex multiple of
`1 ⊗ s`. -/
theorem exists_eq_smul_one_tmul {s : E} (hs : Submodule.span (𝓞 K) {s} = ⊤) (σ : K →+* ℂ)
    (u : Codomain σ ⊗[𝓞 K] E) : ∃ c : ℂ, u = c • (1 ⊗ₜ[𝓞 K] s) := by
  induction u using TensorProduct.inductionOn with
  | add u v hu hv =>
    obtain ⟨c, rfl⟩ := hu
    obtain ⟨d, rfl⟩ := hv
    exact ⟨c + d, (add_smul c d _).symm⟩
  | tmul z x =>
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 (hs ▸ Submodule.mem_top : x ∈ _)
    refine ⟨Codomain.equiv σ z * σ a, ?_⟩
    rw [Codomain.tmul_eq_smul, Codomain.tmul_smul, smul_smul, mul_comm]

/-- If `s` generates `E` and `f s = 1`, then `f` generates `E^∨`: every functional `g` is
`g(s) • f`. -/
theorem span_singleton_dual_eq_top {s : E} (hs : Submodule.span (𝓞 K) {s} = ⊤)
    {f : Module.Dual (𝓞 K) E} (hf : f s = 1) :
    Submodule.span (𝓞 K) {f} = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun g ↦ Submodule.mem_span_singleton.2 ⟨g s, ?_⟩
  ext x
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 (hs ▸ Submodule.mem_top : x ∈ _)
  simp [hf, mul_comm]

variable [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E]

/-- The dual norm of `a` is the norm of its Riesz vector. -/
theorem norm_dual_eq_norm_dualVector (σ : K →+* ℂ) (a : Codomain σ ⊗[𝓞 K] Module.Dual (𝓞 K) E) :
    h.dual.norm σ a = h.norm σ (h.dualVector σ a) := by
  rw [norm_def, norm_def, dual_form_apply]

/-- **The dual norm of a line**: if `s` generates `E`, then `‖f‖_σ ‖s‖_σ = |σ(f s)|` for every
functional `f`. -/
theorem norm_dual_one_tmul_mul_norm {s : E} (hs : Submodule.span (𝓞 K) {s} = ⊤) (σ : K →+* ℂ)
    (f : Module.Dual (𝓞 K) E) :
    h.dual.norm σ (1 ⊗ₜ f) * h.norm σ (1 ⊗ₜ s) = ‖σ (f s)‖ := by
  obtain ⟨c, hc⟩ := exists_eq_smul_one_tmul hs σ (h.dualVector σ (1 ⊗ₜ f))
  have hform : h.form σ (h.dualVector σ (1 ⊗ₜ f)) (1 ⊗ₜ s) = σ (f s) := by
    rw [form_dualVector, dualPairing_tmul_tmul]
    simp
  rw [hc, LinearMap.map_smulₛₗ₂, smul_eq_mul, form_self_eq_norm_sq] at hform
  rw [norm_dual_eq_norm_dualVector, hc, norm_smul, ← hform, norm_mul, Complex.norm_conj,
    Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
  ring

variable [NumberField K] in
/-- **The degree of the dual of a line**: if `s` generates `E` and `f s = 1`, then
`deg(Ē^∨) = -deg(Ē)`, computed with `f` and `s`. -/
theorem sectionDegree_dual_of_span_eq_top {s : E} (hs : Submodule.span (𝓞 K) {s} = ⊤)
    {f : Module.Dual (𝓞 K) E} (hf : f s = 1) :
    h.dual.sectionDegree f = -h.sectionDegree s := by
  have hlog (σ : K →+* ℂ) :
      Real.log (h.dual.norm σ (1 ⊗ₜ f)) = -Real.log (h.norm σ (1 ⊗ₜ s)) := by
    have hmul := h.norm_dual_one_tmul_mul_norm hs σ f
    have h1 : ‖σ ((f s : 𝓞 K) : K)‖ = 1 := by simp [hf]
    rw [h1] at hmul
    rw [eq_inv_of_mul_eq_one_left hmul, Real.log_inv]
  rw [sectionDegree_def, sectionDegree_def, span_singleton_dual_eq_top hs hf, hs,
    Submodule.cardQuot_top]
  simp [hlog]

end TauCeti.HermitianMetric
