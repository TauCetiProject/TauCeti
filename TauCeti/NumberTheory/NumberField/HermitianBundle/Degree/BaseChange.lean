/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import TauCeti.NumberTheory.NumberField.ComplexEmbedding.Extension
public import TauCeti.NumberTheory.NumberField.HermitianBundle.BaseChange
public import TauCeti.NumberTheory.NumberField.HermitianBundle.Degree.Basic

/-!
# The Arakelov degree under base change: the archimedean part

Let `L/K` be a finite extension of number fields and `(E, h)` a hermitian metric over `𝓞 K`. Every
complex embedding `σ` of `K` has exactly `[L : K]` extensions `τ` to `L`
(`NumberField.ComplexEmbedding.natCard_extension`), and the base-changed metric at `τ` is `h` at
`τ|K`. So for a section `s : E` the archimedean term of the degree of `1 ⊗ s` in `Ē_{𝓞 L}` is
`[L : K]` times that of `s` (`TauCeti.HermitianMetric.sum_log_norm_baseChange_one_tmul`). When `s`
generates `E`, `1 ⊗ s` generates `𝓞 L ⊗ E`, both index terms vanish, and
`deg(Ē_{𝓞 L}) = [L : K] deg(Ē)` (`TauCeti.HermitianMetric.sectionDegree_baseChange_of_span_eq_top`).

## Main statements

* `TauCeti.HermitianMetric.sum_log_norm_baseChange_one_tmul`: the archimedean term of the degree
  is multiplied by `[L : K]` under base change.
* `TauCeti.HermitianMetric.sectionDegree_baseChange_of_span_eq_top`: for a generating section,
  `deg(1 ⊗ s) = [L : K] deg(s)`.

## References

* P. Deligne, *Preuves des conjectures de Tate et de Shafarevitch*, Séminaire Bourbaki 616,
  §1.2 (Remarque), p. 27.
* G. Faltings, *Endlichkeitssätze für abelsche Varietäten über Zahlkörpern*, Invent. Math. 73,
  §3, p. 354.
* X. Yuan, S.-W. Zhang, *The arithmetic Hodge index theorem for adelic line bundles*,
  arXiv:1507.06903v3, §1.1, pp. 2–3.
-/

public noncomputable section

open scoped TensorProduct
open NumberField NumberField.ComplexEmbedding

namespace TauCeti

namespace HermitianMetric

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] (h : HermitianMetric K E)

/-- **The archimedean term under base change**: `Σ_τ log ‖1 ⊗ s‖_τ = [L : K] Σ_σ log ‖s‖_σ`,
since each `σ` has `[L : K]` extensions `τ`, at which `‖1 ⊗ s‖_τ = ‖s‖_σ`. -/
theorem sum_log_norm_baseChange_one_tmul (s : E) :
    ∑ τ : L →+* ℂ, Real.log (h.baseChange.norm τ (1 ⊗ₜ ((1 : 𝓞 L) ⊗ₜ s))) =
      Module.finrank K L * ∑ σ : K →+* ℂ, Real.log (h.norm σ (1 ⊗ₜ s)) := by
  simp only [norm_baseChange_tmul_tmul, map_one, norm_one, one_mul]
  rw [sum_comp_algebraMap (fun σ ↦ Real.log (h.norm σ (1 ⊗ₜ s))), nsmul_eq_mul]

/-- **The degree under base change, for a generating section**: if `s` generates `E`, then
`deg(Ē_{𝓞 L}) = [L : K] deg(Ē)`, both computed with `s` and `1 ⊗ s`. -/
theorem sectionDegree_baseChange_of_span_eq_top {s : E} (hs : Submodule.span (𝓞 K) {s} = ⊤) :
    h.baseChange.sectionDegree ((1 : 𝓞 L) ⊗ₜ s) = Module.finrank K L * h.sectionDegree s := by
  have hs' : Submodule.span (𝓞 L) {(1 : 𝓞 L) ⊗ₜ[𝓞 K] s} = ⊤ := by
    rw [← Submodule.baseChange_top (R := 𝓞 K) (M := E) (𝓞 L), ← hs, Submodule.baseChange_span,
      Set.image_singleton, TensorProduct.mk_apply]
  rw [sectionDegree_def, sectionDegree_def, hs', hs,
    sum_log_norm_baseChange_one_tmul, Submodule.cardQuot_top]
  simp

end HermitianMetric

end TauCeti
