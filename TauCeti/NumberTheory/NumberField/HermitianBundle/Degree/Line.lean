/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.HermitianBundle.Degree.Tensor
public import TauCeti.NumberTheory.NumberField.ArakelovDivisor.HermitianLine

import TauCeti.RingTheory.PicardGroup.Contraction

/-!
# The Arakelov degree of a hermitian line

For a hermitian line `(E, h)` over the ring of integers `𝓞 K` of a number field, every nonzero
section `s` computes the same degree `log #(E / 𝓞 K • s) - Σ_σ log ‖s‖_σ`
(`TauCeti.HermitianMetric.sectionDegree_eq_sectionDegree`, the product formula). This file names
that common value `TauCeti.HermitianMetric.lineDegree h`, the **Arakelov degree** `deg^(Ē)`, and
proves that it is an invariant of the isometry class, additive on tensor products and equal to
the degree of `D` on the line `O(D)` of an Arakelov divisor.

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
* `TauCeti.ArakelovDivisor.lineDegree_hermitianMetric`: `deg^(O(D)) = deg^(D)`.

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
  obtain ⟨s, hs⟩ : ∃ s : E, s ≠ 0 := by
    by_contra! h0
    have : Subsingleton E := ⟨fun x y ↦ (h0 x).trans (h0 y).symm⟩
    have : Subsingleton (K ⊗[𝓞 K] E) := inferInstance
    simp [Module.finrank_zero_of_subsingleton] at hE
  rw [h.lineDegree_eq_sectionDegree hE hs, ← IsometryEquiv.sectionDegree_map h e s,
    h'.lineDegree_eq_sectionDegree hF ((map_ne_zero_iff e e.toLinearEquiv.injective).2 hs)]

/-- **Additivity of the degree on tensor products**: `deg^(L ⊗ M) = deg^(L) + deg^(M)` for
invertible `𝓞 K`-modules `L` and `M`. -/
theorem lineDegree_tmul [Module.Invertible (𝓞 K) E] [Module.Invertible (𝓞 K) F] :
    (h.tmul h').lineDegree = h.lineDegree + h'.lineDegree := by
  have := Module.Invertible.nontrivial (𝓞 K) E
  have := Module.Invertible.nontrivial (𝓞 K) F
  obtain ⟨s, hs⟩ := exists_ne (0 : E)
  obtain ⟨t, ht⟩ := exists_ne (0 : F)
  have : Finite (E ⧸ Submodule.span (𝓞 K) {s}) :=
    Module.finite_quotient_span_singleton_of_finrank_eq_one (F := K)
      (Module.Invertible.finrank_eq_one K (K ⊗[𝓞 K] E)) hs
  -- `s ⊗ t ≠ 0`, since its norms `‖s‖_σ ‖t‖_σ` are positive.
  have hst : s ⊗ₜ[𝓞 K] t ≠ 0 := by
    intro h0
    obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have := h.norm_tmul_tmul h' σ s t
    rw [h0, TensorProduct.tmul_zero, norm_zero] at this
    exact (mul_pos (h.norm_pos (Codomain.one_tmul_ne_zero σ hs))
      (h'.norm_pos (Codomain.one_tmul_ne_zero σ ht))).ne' this.symm
  rw [(h.tmul h').lineDegree_eq_sectionDegree_of_invertible hst,
    h.lineDegree_eq_sectionDegree_of_invertible hs, h'.lineDegree_eq_sectionDegree_of_invertible ht,
    h.sectionDegree_tmul h' hs ht]

/-- Rescaling the metric by `e^{-c}` adds `[K : ℚ] c` to the degree of an invertible line. -/
theorem lineDegree_rescale [Module.Invertible (𝓞 K) E] (c : ℝ) :
    (h.rescale c).lineDegree = h.lineDegree + Module.finrank ℚ K * c := by
  have := Module.Invertible.nontrivial (𝓞 K) E
  obtain ⟨s, hs⟩ := exists_ne (0 : E)
  rw [(h.rescale c).lineDegree_eq_sectionDegree_of_invertible hs,
    h.lineDegree_eq_sectionDegree_of_invertible hs, h.sectionDegree_rescale c hs]

/-- The trivial hermitian line `Ō_K` has degree `0`. -/
@[simp]
theorem lineDegree_trivial : (trivial K).lineDegree = 0 := by
  rw [(trivial K).lineDegree_eq_sectionDegree_of_invertible one_ne_zero, sectionDegree_trivial_one]

end TauCeti.HermitianMetric

namespace TauCeti.ArakelovDivisor

variable {K : Type*} [Field K] [NumberField K]

/-- **The Arakelov degree of `O(D)` is the degree of `D`.** -/
@[simp]
theorem lineDegree_hermitianMetric (D : ArakelovDivisor K) :
    D.hermitianMetric.lineDegree = degree K D := by
  obtain ⟨s, hs⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    ((FractionalIdeal.coeToSubmodule_ne_bot).mpr (Units.ne_zero (D.finitePart⁻¹)))
  set s' : (((D.finitePart⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) :
      Submodule (𝓞 K) K) := ⟨s, hs.1⟩
  have hs' : s' ≠ 0 := fun h0 ↦ hs.2 (congrArg Subtype.val h0)
  exact D.sectionDegree_hermitianMetric (Classical.epsilon_spec (p := fun s ↦ s ≠ 0) ⟨s', hs'⟩)

end TauCeti.ArakelovDivisor
