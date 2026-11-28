/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.HermitianBundle.Degree.Line
public import TauCeti.RingTheory.FractionalIdeal.Section

import Mathlib.RingTheory.Flat.TorsionFree
import TauCeti.NumberTheory.NumberField.FractionalIdeal
import TauCeti.NumberTheory.NumberField.RingOfIntegers.Norm
import TauCeti.RingTheory.FractionalIdeal.Norm
import TauCeti.RingTheory.Ideal.Norm.AbsNorm

/-!
# Arakelov degree from a generic section

A nonzero generic section `t` of a hermitian line `E` determines the fractional ideal
`I = {a : K | a • t ∈ E}`. The degree is `-log N(I) - Σ_σ log ‖t‖_σ`, with one term for
each complex embedding. This permits degree computations with a rational trivialization,
even when the chosen section has denominators.

## References

* P. Deligne, *Preuve des conjectures de Tate et de Shafarevitch (d'après G. Faltings)*,
  Séminaire Bourbaki 616, §1.1.
* L. Szpiro, *Degrés, intersections, hauteurs*, Astérisque 127, §1.1–1.2.
-/

public noncomputable section

open scoped TensorProduct nonZeroDivisors
open NumberField NumberField.ComplexEmbedding _root_.FractionalIdeal TauCeti.FractionalIdeal

namespace TauCeti.HermitianMetric

variable {K E : Type*} [Field K] [AddCommGroup E] [Module (𝓞 K) E]
  (h : HermitianMetric K E)

variable [NumberField K] [Module.Finite (𝓞 K) E] [Module.Flat (𝓞 K) E]

/-- The Arakelov degree from a nonzero generic section `t` is the negative logarithm of the
absolute norm of its coefficient ideal, minus the sum of its logarithmic norms. -/
theorem lineDegree_eq_neg_log_absNorm_ofSection_sub_sum_log_genericNorm
    (hE : Module.finrank K (K ⊗[𝓞 K] E) = 1) {t : K ⊗[𝓞 K] E} (ht : t ≠ 0) :
    h.lineDegree = -Real.log (absNorm (ofSection hE ht)) -
      ∑ σ : K →+* ℂ, Real.log (h.genericNorm σ t) := by
  have : Nontrivial E := (subsingleton_or_nontrivial E).resolve_left fun _ ↦
    ht (Subsingleton.elim _ _)
  obtain ⟨s, hs⟩ := exists_ne (0 : E)
  let e := linearEquivOfSection hE ht
  let a : K := e s
  have ha : a ≠ 0 := fun hz ↦ hs (e.injective (Subtype.ext (by simpa [a] using hz)))
  have haσ (σ : K →+* ℂ) : ‖σ a‖ ≠ 0 := norm_ne_zero_iff.mpr ((map_ne_zero σ).2 ha)
  have hcard : ((Submodule.span (𝓞 K) {s}).cardQuot : ℝ) =
      |(Algebra.norm ℚ a : ℝ)| / absNorm (ofSection hE ht) := by
    exact_mod_cast (Submodule.cardQuot_span_singleton_map_equiv e s) ▸
      cardQuot_span_singleton_fractionalIdeal (e.map_ne_zero_iff.mpr hs)
  have hσ (σ : K →+* ℂ) :
      Real.log (h.norm σ (1 ⊗ₜ[𝓞 K] s)) =
        Real.log ‖σ a‖ + Real.log (h.genericNorm σ t) := by
    rw [← genericNorm_one_tmul, ← linearEquivOfSection_apply_smul hE ht s,
      genericNorm_smul, Real.log_mul (haσ σ) ((h.genericNorm_pos_iff σ).2 ht).ne']
  have hprod : ∑ σ : K →+* ℂ, Real.log ‖σ a‖ = Real.log |(Algebra.norm ℚ a : ℝ)| := by
    rw [← prod_norm_embedding_eq_abs_norm, Real.log_prod fun σ _ ↦ haσ σ]
  have hN : (|(Algebra.norm ℚ a : ℝ)| : ℝ) ≠ 0 := by
    rw [← prod_norm_embedding_eq_abs_norm]
    exact Finset.prod_ne_zero_iff.mpr fun σ _ ↦ haσ σ
  have hI : (absNorm (ofSection hE ht) : ℝ) ≠ 0 := by
    exact_mod_cast (absNorm_pos (ofSection_ne_zero hE ht)).ne'
  rw [h.lineDegree_eq_sectionDegree hE hs, sectionDegree_def, hcard, Real.log_div hN hI]
  simp_rw [hσ, Finset.sum_add_distrib, hprod]
  ring

end TauCeti.HermitianMetric
