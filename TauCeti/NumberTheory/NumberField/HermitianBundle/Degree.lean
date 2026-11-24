/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Arakelov.SectionDegree
public import TauCeti.NumberTheory.NumberField.HermitianBundle.Basic
public import Mathlib.RingTheory.FractionalIdeal.Norm

import TauCeti.NumberTheory.NumberField.FractionalIdeal
import TauCeti.RingTheory.FractionalIdeal.Norm

/-!
# The Arakelov degree of a hermitian line

For a hermitian metric `h` on an `𝓞 K`-module `E` and a section `s : E`, the expression
`deg(s) = log #(E / 𝓞 K • s) - Σ_σ log ‖s‖_σ`, summed over the complex embeddings `σ`, is the
Arakelov degree of the hermitian line `(E, h)` when `E` has rank one and `s ≠ 0`. Summed over the
infinite places it is `log #(E / 𝓞 K • s) - Σ_v mult(v) log ‖s‖_v`, the multiplicity `mult(v)`
counting the embeddings inducing `v`. It is `TauCeti.sectionDegreeOfNorms` for the norms
`x ↦ ‖1 ⊗ x‖_σ`.

## Main definitions

* `TauCeti.HermitianMetric.sectionDegree`: the degree computed with a section.

## Main statements

* `TauCeti.HermitianMetric.sectionDegree_eq_sum_infinitePlace`: the sum over infinite places.
* `TauCeti.HermitianMetric.sectionDegree_trivial_one`: `deg(Ō_K) = 0`.
* `TauCeti.HermitianMetric.sectionDegree_rescale`: `deg(Ē(c)) = deg(Ē) + [K : ℚ] c`.
* `TauCeti.HermitianMetric.IsometryEquiv.sectionDegree_map`: isometric lines have equal degree.
* `TauCeti.HermitianMetric.sectionDegree_fractionalIdeal`:
  `deg(𝔞, e^{-λ_v} |·|_v) = -log N(𝔞) + Σ_v mult(v) λ_v`.

## References

* P. Deligne, *Preuves des conjectures de Tate et de Shafarevitch*, Séminaire Bourbaki 616,
  §1.1, pp. 25–26.
* L. Szpiro, *Degrés, intersections, hauteurs*, Astérisque 127, §1.1–1.2, Corollaire, p. 14.
-/

public noncomputable section

open scoped TensorProduct nonZeroDivisors
open NumberField NumberField.ComplexEmbedding

namespace TauCeti.HermitianMetric

variable {K : Type*} [Field K] [NumberField K] {E F : Type*} [AddCommGroup E] [Module (𝓞 K) E]
  [AddCommGroup F] [Module (𝓞 K) F] (h : HermitianMetric K E)

/-- The expression `log #(E / 𝓞 K • s) - Σ_σ log ‖s‖_σ` attached to a section `s`, the sum
running over all field embeddings `σ : K →+* ℂ`. For a nonzero section of a hermitian line
bundle this is its Arakelov degree. -/
def sectionDegree (s : E) : ℝ :=
  sectionDegreeOfNorms (fun σ x => h.norm σ (1 ⊗ₜ x)) s

/-- The degree computed with `s` is `log #(E / 𝓞 K • s) - Σ_σ log ‖s‖_σ`. -/
theorem sectionDegree_def (s : E) : h.sectionDegree s =
    Real.log (Submodule.span (𝓞 K) {s}).cardQuot - ∑ σ : K →+* ℂ, Real.log (h.norm σ (1 ⊗ₜ s)) :=
  sectionDegreeOfNorms_def _ _

/-- The degree computed with `s`, summed over the infinite places with their multiplicities:
`log #(E / 𝓞 K • s) - Σ_v mult(v) log ‖s‖_v`. -/
theorem sectionDegree_eq_sum_infinitePlace (s : E) : h.sectionDegree s =
    Real.log (Submodule.span (𝓞 K) {s}).cardQuot -
      ∑ v : InfinitePlace K, v.mult * Real.log (h.placeNorm v s) := by
  rw [sectionDegree_def]
  congr 1
  simp_rw [← h.placeNorm_mk]
  classical
  rw [← Finset.sum_fiberwise Finset.univ InfinitePlace.mk]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_congr rfl fun σ hσ => by rw [(Finset.mem_filter.1 hσ).2], Finset.sum_const,
    ← nsmul_eq_mul, ← InfinitePlace.card_filter_mk_eq]

/-- Rescaling the metric by `e^{-c}` adds `[K : ℚ] c` to the degree computed with a nonzero
section of a flat module. -/
theorem sectionDegree_rescale [Module.Flat (𝓞 K) E] (c : ℝ) {s : E} (hs : s ≠ 0) :
    (h.rescale c).sectionDegree s = h.sectionDegree s + Module.finrank ℚ K * c := by
  simp only [sectionDegree, norm_rescale]
  exact sectionDegreeOfNorms_exp_neg_mul _ c fun σ =>
    (h.norm_pos (Codomain.one_tmul_ne_zero σ hs)).ne'

/-- Isometric bundles have the same degree: the degree computed with `e s` is the degree computed
with `s`. -/
@[simp]
theorem _root_.TauCeti.HermitianMetric.IsometryEquiv.sectionDegree_map {h' : HermitianMetric K F}
    (e : IsometryEquiv h h') (s : E) : h'.sectionDegree (e s) = h.sectionDegree s := by
  have hcard : (Submodule.span (𝓞 K) {e s}).cardQuot = (Submodule.span (𝓞 K) {s}).cardQuot := by
    rw [Submodule.cardQuot, Submodule.cardQuot,
      ← AddSubgroup.index_map_equiv _ e.toLinearEquiv.toAddEquiv]
    congr 1
    ext x
    simp [Submodule.mem_span_singleton]
  simp only [sectionDegree_def, hcard, e.norm_tmul_map]

/-- The degree of `Ō_K` computed with the section `1` is zero. -/
@[simp]
theorem sectionDegree_trivial_one : (trivial K).sectionDegree 1 = 0 :=
  sectionDegreeOfNorms_eq_zero Ideal.span_singleton_one fun σ => by simp

/-- The degree of the hermitian line `(𝔞, e^{-λ_v} |·|_v)` of a nonzero fractional ideal, computed
with any nonzero section, is `-log N(𝔞) + Σ_v mult(v) λ_v`. -/
theorem sectionDegree_fractionalIdeal {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0)
    (w : InfinitePlace K → ℝ) {s : (I : Submodule (𝓞 K) K)} (hs : s ≠ 0) :
    (fractionalIdeal I hI w).sectionDegree s =
      -Real.log (FractionalIdeal.absNorm I) + ∑ v : InfinitePlace K, v.mult * w v := by
  have hs' : (s : K) ≠ 0 := fun h => hs (Subtype.ext h)
  have hN : (0 : ℝ) < |(Algebra.norm ℚ (s : K) : ℝ)| := by
    exact_mod_cast abs_pos.2 ((Algebra.norm_ne_zero_iff).2 hs')
  have hA : (0 : ℝ) < FractionalIdeal.absNorm I := by
    exact_mod_cast FractionalIdeal.absNorm_pos hI
  have hcard : ((Submodule.span (𝓞 K) {s}).cardQuot : ℝ) =
      |(Algebra.norm ℚ (s : K) : ℝ)| / FractionalIdeal.absNorm I := by
    have := congrArg (fun q : ℚ => (q : ℝ)) (cardQuot_span_singleton_fractionalIdeal hs)
    push_cast at this
    exact this
  have hprod : ∑ v : InfinitePlace K, v.mult * Real.log (v (s : K)) =
      Real.log |(Algebra.norm ℚ (s : K) : ℝ)| := by
    have h := InfinitePlace.prod_eq_abs_norm (s : K)
    push_cast at h
    rw [← h, Real.log_prod fun v _ => pow_ne_zero _ (v.pos_iff.2 hs').ne']
    simp only [Real.log_pow]
  have hlog v :
      Real.log ((fractionalIdeal I hI w).placeNorm v s) = -w v + Real.log (v (s : K)) := by
    rw [placeNorm_fractionalIdeal, Real.log_mul (Real.exp_pos _).ne' (v.pos_iff.2 hs').ne',
      Real.log_exp]
  rw [sectionDegree_eq_sum_infinitePlace, hcard, Real.log_div hN.ne' hA.ne', ← hprod]
  simp only [hlog, mul_add, Finset.sum_add_distrib, mul_neg, Finset.sum_neg_distrib]
  ring

end TauCeti.HermitianMetric
