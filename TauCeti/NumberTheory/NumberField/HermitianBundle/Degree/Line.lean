/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.HermitianBundle.Degree.Tensor

import TauCeti.LinearAlgebra.TensorProduct.Separation
import TauCeti.RingTheory.PicardGroup.Contraction

/-!
# The Arakelov degree of a hermitian line

For a hermitian line `(E, h)` over the ring of integers `𝓞 K` of a number field, every nonzero
section `s` computes the same degree `log #(E / 𝓞 K • s) - Σ_σ log ‖s‖_σ`
(`TauCeti.HermitianMetric.sectionDegree_eq_sectionDegree`, the product formula). This file names
that common value `TauCeti.HermitianMetric.lineDegree h`, the **Arakelov degree** `deg^(Ē)`, and
proves that it is an invariant of the isometry class and additive on tensor products.

## Main definitions

* `TauCeti.HermitianMetric.lineDegree`: the Arakelov degree of a hermitian line, the degree
  computed with a chosen nonzero section.

## Main results

* `TauCeti.HermitianMetric.lineDegree_eq_sectionDegree`: on a line, the degree computed with any
  nonzero section.
* `TauCeti.HermitianMetric.IsometryEquiv.lineDegree_eq`: isometric lines have the same degree.
* `TauCeti.HermitianMetric.lineDegree_tmul`: `deg^(L ⊗ M) = deg^(L) + deg^(M)` for invertible
  `L` and `M`.
* `TauCeti.HermitianMetric.lineDegree_rescale`: `deg^(L(c)) = deg^(L) + [K : ℚ] c`.
* `TauCeti.HermitianMetric.lineDegree_trivial`: `deg^(Ō_K) = 0`.

## References

* L. Szpiro, *Degrés, intersections, hauteurs*, Astérisque 127, §1.1–1.2.
* J.-B. Bost, *Périodes et isogénies des variétés abéliennes sur les corps de nombres*,
  Séminaire Bourbaki 795, Appendice A.3.
-/

public noncomputable section

open scoped TensorProduct nonZeroDivisors
open NumberField NumberField.ComplexEmbedding

namespace TauCeti.HermitianMetric

variable {K : Type*} [Field K] [NumberField K] {E F : Type*} [AddCommGroup E] [Module (𝓞 K) E]
  [AddCommGroup F] [Module (𝓞 K) F] (h : HermitianMetric K E) (h' : HermitianMetric K F)

/-- The **Arakelov degree of a hermitian line** `(E, h)`: the degree
`log #(E / 𝓞 K • s) - Σ_σ log ‖s‖_σ` computed with a chosen nonzero section `s` (with `s = 0` if
`E = 0`). On a line every nonzero section gives the same value
(`TauCeti.HermitianMetric.lineDegree_eq_sectionDegree`). -/
def lineDegree : ℝ :=
  h.sectionDegree (Classical.epsilon fun s : E ↦ s ≠ 0)

/-- **The degree of a line is computed by any nonzero section.** -/
theorem lineDegree_eq_sectionDegree [Module.Finite (𝓞 K) E] [Module.Flat (𝓞 K) E]
    (hE : Module.finrank K (K ⊗[𝓞 K] E) = 1) {s : E} (hs : s ≠ 0) :
    h.lineDegree = h.sectionDegree s :=
  h.sectionDegree_eq_sectionDegree hE (Classical.epsilon_spec (p := fun s : E ↦ s ≠ 0) ⟨s, hs⟩) hs

/-- The degree of an invertible hermitian line is computed by any nonzero section. -/
theorem lineDegree_eq_sectionDegree_of_invertible [Module.Invertible (𝓞 K) E] {s : E}
    (hs : s ≠ 0) : h.lineDegree = h.sectionDegree s :=
  h.lineDegree_eq_sectionDegree (Module.Invertible.finrank_eq_one K (K ⊗[𝓞 K] E)) hs

variable {h h'} in
/-- **Isometric lines have the same degree.** -/
theorem IsometryEquiv.lineDegree_eq [Module.Finite (𝓞 K) E] [Module.Flat (𝓞 K) E]
    (hE : Module.finrank K (K ⊗[𝓞 K] E) = 1) (e : IsometryEquiv h h') :
    h.lineDegree = h'.lineDegree := by
  have : Module.Finite (𝓞 K) F := Module.Finite.equiv e.toLinearEquiv
  have : Module.Flat (𝓞 K) F := Module.Flat.of_linearEquiv e.toLinearEquiv.symm
  have hF : Module.finrank K (K ⊗[𝓞 K] F) = 1 := by
    rw [← hE]
    exact (LinearEquiv.finrank_eq (e.toLinearEquiv.baseChange (𝓞 K) K E F)).symm
  have : Nontrivial E := (subsingleton_or_nontrivial E).resolve_left fun _ ↦
    not_nontrivial (K ⊗[𝓞 K] E) (Module.nontrivial_of_finrank_eq_succ hE)
  obtain ⟨s, hs⟩ := exists_ne (0 : E)
  rw [h.lineDegree_eq_sectionDegree hE hs, ← IsometryEquiv.sectionDegree_map h e s,
    h'.lineDegree_eq_sectionDegree hF ((map_ne_zero_iff e e.toLinearEquiv.injective).2 hs)]

/-- **Additivity of the degree on tensor products**: `deg^(L ⊗ M) = deg^(L) + deg^(M)` for
invertible `𝓞 K`-modules `L` and `M`. -/
@[simp]
theorem lineDegree_tmul [Module.Invertible (𝓞 K) E] [Module.Invertible (𝓞 K) F] :
    (h.tmul h').lineDegree = h.lineDegree + h'.lineDegree := by
  have := Module.Invertible.nontrivial (𝓞 K) E
  have := Module.Invertible.nontrivial (𝓞 K) F
  obtain ⟨s, hs⟩ := exists_ne (0 : E)
  obtain ⟨t, ht⟩ := exists_ne (0 : F)
  have : Finite (E ⧸ Submodule.span (𝓞 K) {s}) :=
    Module.finite_quotient_span_singleton_of_finrank_eq_one (F := K)
      (Module.Invertible.finrank_eq_one K (K ⊗[𝓞 K] E)) hs
  rw [(h.tmul h').lineDegree_eq_sectionDegree_of_invertible (TauCeti.tmul_ne_zero hs ht),
    h.lineDegree_eq_sectionDegree_of_invertible hs, h'.lineDegree_eq_sectionDegree_of_invertible ht,
    h.sectionDegree_tmul h' hs ht]

/-- Rescaling the metric by `e^{-c}` adds `[K : ℚ] c` to the degree of a nonzero flat bundle:
both degrees are computed with the same chosen section. -/
@[simp]
theorem lineDegree_rescale [Module.Flat (𝓞 K) E] [Nontrivial E] (c : ℝ) :
    (h.rescale c).lineDegree = h.lineDegree + Module.finrank ℚ K * c := by
  unfold lineDegree
  exact h.sectionDegree_rescale c (Classical.epsilon_spec (p := fun s : E ↦ s ≠ 0) (exists_ne 0))

/-- The trivial hermitian line `Ō_K` has degree `0`. -/
@[simp]
theorem lineDegree_trivial : (trivial K).lineDegree = 0 := by
  rw [(trivial K).lineDegree_eq_sectionDegree_of_invertible one_ne_zero, sectionDegree_trivial_one]

end TauCeti.HermitianMetric
