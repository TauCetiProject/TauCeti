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
public import TauCeti.RingTheory.Ideal.Norm.TensorProduct

/-!
# The Arakelov degree under base change

Let `L/K` be a finite extension of number fields and `(E, h)` a hermitian metric over `𝓞 K`. Every
complex embedding `σ` of `K` has exactly `[L : K]` extensions `τ` to `L`
(`NumberField.ComplexEmbedding.natCard_extension`), and the base-changed metric at `τ` is `h` at
`τ|K`. So for a section `s : E` the archimedean term of the degree of `1 ⊗ s` in `Ē_{𝓞 L}` is
`[L : K]` times that of `s` (`TauCeti.HermitianMetric.sum_log_norm_baseChange_one_tmul`). The
index of `𝓞 L (1 ⊗ s)` in `𝓞 L ⊗ E` is `#(E / 𝓞 K s) ^ [L : K]`
(`TauCeti.cardQuot_span_one_tmul`, from Mathlib's `Ideal.absNorm_algebraMap`), so the index term
is multiplied by `[L : K]` too, and the section degrees satisfy `deg(1 ⊗ s) = [L : K] deg(s)`
for every `s` (`TauCeti.HermitianMetric.sectionDegree_baseChange`). For a nonzero section `s` of a
hermitian line this is the Arakelov degree identity `deg(Ē_{𝓞 L}) = [L : K] deg(Ē)`.

More generally, if the base change `Ē_{𝓞 L}` is a sublattice of finite index of a hermitian bundle
`F` over `𝓞 L` with the same metrics, then for a nonzero section `s` of a hermitian line `Ē`,
`deg(F) = [L : K] deg(Ē) + log #(F / Ē_{𝓞 L})`
(`TauCeti.HermitianMetric.sectionDegree_map_baseChange`).

## Main statements

* `TauCeti.HermitianMetric.sum_log_norm_baseChange_one_tmul`: the archimedean term of the degree
  is multiplied by `[L : K]` under base change.
* `TauCeti.HermitianMetric.sectionDegree_baseChange`: `deg(1 ⊗ s) = [L : K] deg(s)`.
* `TauCeti.HermitianMetric.sectionDegree_map_baseChange`: for a norm-preserving embedding
  `f : 𝓞 L ⊗ E → F` of finite cokernel, `deg(f (1 ⊗ s)) = [L : K] deg(s) + log #(F / f(𝓞 L ⊗ E))`.

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

/-- **The degree under base change**: the section degrees satisfy
`deg(1 ⊗ s) = [L : K] deg(s)` for every section `s`. When `s` is a nonzero section of a hermitian
line, this is the Arakelov degree identity `deg(Ē_{𝓞 L}) = [L : K] deg(Ē)`. -/
theorem sectionDegree_baseChange (s : E) :
    h.baseChange.sectionDegree ((1 : 𝓞 L) ⊗ₜ s) = Module.finrank K L * h.sectionDegree s := by
  rw [sectionDegree_def, sectionDegree_def, sum_log_norm_baseChange_one_tmul,
    cardQuot_span_one_tmul (𝓞 L) s, IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L, Nat.cast_pow,
    Real.log_pow]
  ring

/-- **The degree of a lattice containing a base change**. Let `f : 𝓞 L ⊗ E → F` be an injective
`𝓞 L`-linear map preserving the norms, with `F / f(𝓞 L ⊗ E)` finite. For a section `s` with
`E / 𝓞 K s` finite, `deg(f (1 ⊗ s)) = [L : K] deg(s) + log #(F / f(𝓞 L ⊗ E))`. When `s` is a
nonzero section of a hermitian line, this is `deg(F) = [L : K] deg(Ē) + log #(F / f(𝓞 L ⊗ E))`. -/
theorem sectionDegree_map_baseChange {F : Type*} [AddCommGroup F] [Module (𝓞 L) F]
    {g : HermitianMetric L F} (f : 𝓞 L ⊗[𝓞 K] E →ₗ[𝓞 L] F) (hf : Function.Injective f)
    (hnorm : ∀ τ x, g.norm τ (1 ⊗ₜ f x) = h.baseChange.norm τ (1 ⊗ₜ x)) (s : E)
    [Finite (E ⧸ Submodule.span (𝓞 K) {s})] [Finite (F ⧸ LinearMap.range f)] :
    g.sectionDegree (f ((1 : 𝓞 L) ⊗ₜ s)) =
      Module.finrank K L * h.sectionDegree s + Real.log (LinearMap.range f).cardQuot := by
  have := finite_quotient_span_one_tmul (R := 𝓞 K) (𝓞 L) (s := s)
  rw [h.baseChange.sectionDegree_map_eq_add_log_cardQuot_range f hf hnorm,
    sectionDegree_baseChange]

end HermitianMetric

end TauCeti
