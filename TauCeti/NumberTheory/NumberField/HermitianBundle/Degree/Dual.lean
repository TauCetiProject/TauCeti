/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.HermitianBundle.Degree.Tensor
public import TauCeti.NumberTheory.NumberField.HermitianBundle.Dual
public import Mathlib.RingTheory.PicardGroup

import TauCeti.RingTheory.Ideal.Norm.AbsNorm
import TauCeti.RingTheory.PicardGroup.Contraction

/-!
# The Arakelov degree of the dual of a hermitian line

Let `(E, h)` be a hermitian line over the ring of integers `𝓞 K` of a number field: `E` an
invertible `𝓞 K`-module. For nonzero sections `s : E` and `f : E^∨` with `f s ≠ 0`, the degrees
computed with `f` on the dual line and with `s` on `E` add up to zero
(`TauCeti.HermitianMetric.sectionDegree_dual_add_sectionDegree`):

`deg(Ē^∨) = -deg(Ē)`.

The section `s` need not generate `E`. The proof goes through the tensor product `E^∨ ⊗ E`. On
one side, the degree is additive on tensor products (`TauCeti.HermitianMetric.sectionDegree_tmul`).
On the other, the contraction `E^∨ ⊗ E ≃ 𝓞 K`, `f ⊗ s ↦ f s`, carries the lattice `𝓞 K (f ⊗ s)`
to the ideal `(f s)`, and the norms satisfy `‖f‖_σ ‖s‖_σ = |σ(f s)|`
(`TauCeti.HermitianMetric.norm_dual_one_tmul_mul_norm`), the Cauchy–Schwarz equality in the
complex fibre of a line. So the degree of `E^∨ ⊗ E` computed with `f ⊗ s` is that of the trivial
line `Ō_K` computed with `f s`, which is `0` by the product formula.

## Main results

* `TauCeti.HermitianMetric.sectionDegree_dual_tmul_eq_zero`: the degree of `E^∨ ⊗ E` computed
  with `f ⊗ s` is `0`.
* `TauCeti.HermitianMetric.sectionDegree_dual_add_sectionDegree`: `deg(Ē^∨) + deg(Ē) = 0`.
* `TauCeti.HermitianMetric.sectionDegree_dual_eq_neg`: `deg(Ē^∨) = -deg(Ē)`.

## References

* J.-B. Bost, *Périodes et isogénies des variétés abéliennes sur les corps de nombres*,
  Séminaire Bourbaki 795, Appendice A.3, p. 147.
* L. Szpiro, *Degrés, intersections, hauteurs*, Astérisque 127, §1.2, Corollaire, p. 14.
-/

public noncomputable section

open scoped TensorProduct
open NumberField NumberField.ComplexEmbedding

namespace TauCeti.HermitianMetric

variable {K : Type*} [Field K] [NumberField K] {E : Type*} [AddCommGroup E] [Module (𝓞 K) E]
  (h : HermitianMetric K E)

/-- **The degree of `E^∨ ⊗ E` computed with `f ⊗ s` is zero**, for a hermitian line `E` and
`f s ≠ 0`. -/
theorem sectionDegree_dual_tmul_eq_zero [Module.Invertible (𝓞 K) E] {s : E}
    {f : Module.Dual (𝓞 K) E} (hfs : f s ≠ 0) : (h.dual.tmul h).sectionDegree (f ⊗ₜ s) = 0 := by
  have hE := Module.Invertible.finrank_eq_one K (K ⊗[𝓞 K] E)
  have hcard : Submodule.cardQuot (Submodule.span (𝓞 K) {f ⊗ₜ[𝓞 K] s}) =
      (Submodule.span (𝓞 K) {f s}).cardQuot := by
    rw [← Submodule.cardQuot_span_singleton_map_equiv (Module.Invertible.linearEquiv (𝓞 K) E),
      Module.Invertible.linearEquiv_tmul]
  have hnorm (σ : K →+* ℂ) :
      (h.dual.tmul h).norm σ (1 ⊗ₜ (f ⊗ₜ s)) = (trivial K).norm σ (1 ⊗ₜ f s) := by
    rw [norm_tmul_tmul, h.norm_dual_one_tmul_mul_norm σ hE s, norm_trivial_tmul]
  have key : (h.dual.tmul h).sectionDegree (f ⊗ₜ s) = (trivial K).sectionDegree (f s) := by
    simp only [sectionDegree_def, hcard, hnorm]
  rw [key]
  exact HermitianBundle.sectionDegree_trivial hfs

/-- **The degree of the dual of a hermitian line**: for nonzero sections `s : E` and
`f : E^∨` with `f s ≠ 0`, `deg(Ē^∨) + deg(Ē) = 0`, computed with `f` and `s`. -/
theorem sectionDegree_dual_add_sectionDegree [Module.Invertible (𝓞 K) E] {s : E}
    {f : Module.Dual (𝓞 K) E} (hfs : f s ≠ 0) :
    h.dual.sectionDegree f + h.sectionDegree s = 0 := by
  have hs : s ≠ 0 := ne_zero_of_map hfs
  have hf : f ≠ 0 := by
    rintro rfl
    exact hfs (LinearMap.zero_apply s)
  have : Finite (Module.Dual (𝓞 K) E ⧸ Submodule.span (𝓞 K) {f}) :=
    Module.finite_quotient_span_singleton_of_finrank_eq_one (F := K)
      (Module.Invertible.finrank_eq_one K (K ⊗[𝓞 K] Module.Dual (𝓞 K) E)) hf
  rw [← h.dual.sectionDegree_tmul h hf hs, sectionDegree_dual_tmul_eq_zero h hfs]

/-- `deg(Ē^∨) = -deg(Ē)` for a hermitian line, computed with `f` and `s` with `f s ≠ 0`. -/
theorem sectionDegree_dual_eq_neg [Module.Invertible (𝓞 K) E] {s : E}
    {f : Module.Dual (𝓞 K) E} (hfs : f s ≠ 0) :
    h.dual.sectionDegree f = -h.sectionDegree s :=
  eq_neg_of_add_eq_zero_left (h.sectionDegree_dual_add_sectionDegree hfs)

end TauCeti.HermitianMetric
