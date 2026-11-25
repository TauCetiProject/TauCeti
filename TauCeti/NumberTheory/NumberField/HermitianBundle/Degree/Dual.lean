/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.HermitianBundle.Degree.Tensor
public import Mathlib.RingTheory.PicardGroup

/-!
# The Arakelov degree of the dual of a hermitian line

Let `(E, h)` be a hermitian line over the ring of integers `𝓞 K` of a number field: `E` an
invertible `𝓞 K`-module. For nonzero sections `s : E` and `f : E^∨` with `f s ≠ 0`, the degrees
computed with `f` on the dual line and with `s` on `E` add up to zero
(`TauCeti.HermitianMetric.sectionDegree_dual_add_sectionDegree`):

`deg(Ē^∨) = -deg(Ē)`.

This does not need `s` to generate `E` (main's `sectionDegree_dual_of_span_eq_top` treats that
case). The proof goes through the tensor product `E^∨ ⊗ E`. On one side, the degree is additive on
tensor products (`TauCeti.HermitianMetric.sectionDegree_tmul`). On the other, the contraction
`E^∨ ⊗ E ≃ 𝓞 K`, `f ⊗ s ↦ f s`, carries the lattice `𝓞 K (f ⊗ s)` to the ideal `(f s)`, and the
norms satisfy `‖f‖_σ ‖s‖_σ = |σ(f s)|`
(`TauCeti.HermitianMetric.norm_dual_one_tmul_mul_norm_of_finrank_eq_one`), the Cauchy–Schwarz
equality in the complex fibre of a line. So the degree of `E^∨ ⊗ E` computed with `f ⊗ s` is that
of the trivial line `Ō_K` computed with `f s`, which is `0` by the product formula.

## Main results

* `NumberField.ComplexEmbedding.Codomain.exists_eq_smul_one_tmul_of_finrank_eq_one`: the complex
  fibre of a module of generic rank one is spanned by `1 ⊗ s` for any nonzero `s`.
* `TauCeti.HermitianMetric.norm_dual_one_tmul_mul_norm_of_finrank_eq_one`: on a line,
  `‖f‖_σ ‖s‖_σ = |σ(f s)|`.
* `TauCeti.HermitianMetric.sectionDegree_tmul_eq_zero_of_contraction`: the degree of `E^∨ ⊗ E`
  computed with `f ⊗ s` is `0`.
* `TauCeti.HermitianMetric.sectionDegree_dual_add_sectionDegree`: `deg(Ē^∨) + deg(Ē) = 0`.

## References

* J.-B. Bost, *Périodes et isogénies des variétés abéliennes sur les corps de nombres*,
  Séminaire Bourbaki 795, Appendice A.3, p. 147.
* L. Szpiro, *Degrés, intersections, hauteurs*, Astérisque 127, §1.2, Corollaire, p. 14.
-/

public noncomputable section

open scoped TensorProduct
open NumberField NumberField.ComplexEmbedding

namespace NumberField.ComplexEmbedding.Codomain

variable {K : Type*} [Field K] [NumberField K] (σ : K →+* ℂ) {E : Type*} [AddCommGroup E]
  [Module (𝓞 K) E] [Module.IsTorsionFree (𝓞 K) E]

/-- If `E` has generic rank one and `s ≠ 0`, the complex fibre at `σ` is the line spanned by
`1 ⊗ s`: every vector is a complex multiple of `1 ⊗ s`. -/
theorem exists_eq_smul_one_tmul_of_finrank_eq_one (hE : Module.finrank K (K ⊗[𝓞 K] E) = 1)
    {s : E} (hs : s ≠ 0) (u : Codomain σ ⊗[𝓞 K] E) : ∃ c : ℂ, u = c • (1 ⊗ₜ[𝓞 K] s) := by
  induction u using TensorProduct.inductionOn with
  | tmul c x =>
    obtain ⟨a, b, ha, hab⟩ := Module.exists_smul_eq_smul_of_finrank_eq_one hE hs x
    have hσa : σ a ≠ 0 := by simpa using ha
    have h : σ a • (c ⊗ₜ[𝓞 K] x) = σ b • (c ⊗ₜ[𝓞 K] s) := by
      rw [← tmul_smul, ← tmul_smul, hab]
    refine ⟨equiv σ c * σ b / σ a, ?_⟩
    rw [← inv_smul_smul₀ hσa (c ⊗ₜ[𝓞 K] x), h, tmul_eq_smul σ c s, smul_smul, smul_smul]
    congr 1
    field_simp
  | add u v hu hv =>
    obtain ⟨c, rfl⟩ := hu
    obtain ⟨d, rfl⟩ := hv
    exact ⟨c + d, (add_smul c d _).symm⟩

end NumberField.ComplexEmbedding.Codomain

namespace TauCeti.HermitianMetric

variable {K : Type*} [Field K] [NumberField K] {E : Type*} [AddCommGroup E] [Module (𝓞 K) E]
  (h : HermitianMetric K E)

/-- **The dual norm on a line**: if `E` has generic rank one, then `‖f‖_σ ‖s‖_σ = |σ(f s)|` for
every section `s` and functional `f`. -/
theorem norm_dual_one_tmul_mul_norm_of_finrank_eq_one [Module.Finite (𝓞 K) E]
    [Module.Projective (𝓞 K) E] (hE : Module.finrank K (K ⊗[𝓞 K] E) = 1) (σ : K →+* ℂ)
    (s : E) (f : Module.Dual (𝓞 K) E) :
    h.dual.norm σ (1 ⊗ₜ f) * h.norm σ (1 ⊗ₜ s) = ‖σ (f s)‖ := by
  obtain rfl | hs := eq_or_ne s 0
  · simp
  obtain ⟨c, hc⟩ :=
    Codomain.exists_eq_smul_one_tmul_of_finrank_eq_one σ hE hs (h.dualVector σ (1 ⊗ₜ f))
  have hform : h.form σ (h.dualVector σ (1 ⊗ₜ f)) (1 ⊗ₜ s) = σ (f s) := by
    rw [form_dualVector, dualPairing_tmul_tmul]
    simp
  rw [hc, LinearMap.map_smulₛₗ₂, smul_eq_mul, form_self_eq_norm_sq] at hform
  rw [norm_dual_eq_norm_dualVector, hc, norm_smul, ← hform, norm_mul, Complex.norm_conj,
    Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
  ring

/-- **The degree of `E^∨ ⊗ E` computed with `f ⊗ s` is zero**, for a hermitian line `E` and
`f s ≠ 0`: the contraction `E^∨ ⊗ E ≃ 𝓞 K` carries `𝓞 K (f ⊗ s)` to the ideal `(f s)`, and
`‖f ⊗ s‖_σ = |σ(f s)|`, so this is the degree of `Ō_K` computed with `f s`. -/
theorem sectionDegree_tmul_eq_zero_of_contraction [Module.Invertible (𝓞 K) E] {s : E}
    {f : Module.Dual (𝓞 K) E} (hfs : f s ≠ 0) : (h.dual.tmul h).sectionDegree (f ⊗ₜ s) = 0 := by
  have hE := Module.Invertible.finrank_eq_one K (K ⊗[𝓞 K] E)
  set e := Module.Invertible.linearEquiv (𝓞 K) E
  have he : e (f ⊗ₜ s) = f s := by simp [e, Module.Invertible.linearEquiv]
  have key : (h.dual.tmul h).sectionDegree (f ⊗ₜ s) = (trivial K).sectionDegree (f s) := by
    rw [sectionDegree_def, sectionDegree_def]
    congr 3
    · rw [Submodule.cardQuot, Submodule.cardQuot, ← AddSubgroup.index_map_equiv _ e.toAddEquiv]
      congr 1
      ext x
      simp [Submodule.mem_span_singleton, ← he]
    · ext σ
      rw [norm_tmul_tmul, norm_dual_one_tmul_mul_norm_of_finrank_eq_one h hE σ s,
        norm_trivial_tmul]
  rw [key]
  exact HermitianBundle.sectionDegree_trivial hfs

/-- **The degree of the dual of a hermitian line**: for nonzero sections `s : E` and
`f : E^∨` with `f s ≠ 0`, `deg(Ē^∨) + deg(Ē) = 0`, computed with `f` and `s`. -/
theorem sectionDegree_dual_add_sectionDegree [Module.Invertible (𝓞 K) E] {s : E}
    {f : Module.Dual (𝓞 K) E} (hfs : f s ≠ 0) :
    h.dual.sectionDegree f + h.sectionDegree s = 0 := by
  have hs : s ≠ 0 := by
    rintro rfl
    exact hfs (map_zero f)
  have hf : f ≠ 0 := by
    rintro rfl
    exact hfs rfl
  have : Finite (Module.Dual (𝓞 K) E ⧸ Submodule.span (𝓞 K) {f}) :=
    Module.finite_quotient_span_singleton_of_finrank_eq_one (F := K)
      (Module.Invertible.finrank_eq_one K (K ⊗[𝓞 K] Module.Dual (𝓞 K) E)) hf
  rw [← h.dual.sectionDegree_tmul h hf hs, sectionDegree_tmul_eq_zero_of_contraction h hfs]

/-- `deg(Ē^∨) = -deg(Ē)` for a hermitian line, computed with `f` and `s` with `f s ≠ 0`. -/
theorem sectionDegree_dual_eq_neg [Module.Invertible (𝓞 K) E] {s : E}
    {f : Module.Dual (𝓞 K) E} (hfs : f s ≠ 0) :
    h.dual.sectionDegree f = -h.sectionDegree s :=
  eq_neg_of_add_eq_zero_left (h.sectionDegree_dual_add_sectionDegree hfs)

end TauCeti.HermitianMetric
