/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.HermitianBundle.Degree.Line
public import TauCeti.RingTheory.FractionalIdeal.Section

import Mathlib.RingTheory.Flat.TorsionFree
import TauCeti.LinearAlgebra.TensorProduct.Separation
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
open NumberField NumberField.ComplexEmbedding FractionalIdeal

namespace TauCeti.HermitianMetric

variable {K E : Type*} [Field K] [AddCommGroup E] [Module (𝓞 K) E]
  (h : HermitianMetric K E)

/-- The norm of a generic-fibre vector after scalar extension to the complex embedding `σ`. -/
def genericNorm (σ : K →+* ℂ) (t : K ⊗[𝓞 K] E) : ℝ :=
  h.norm σ (((TensorProduct.AlgebraTensorModule.cancelBaseChange (𝓞 K) K (Codomain σ)
    (Codomain σ) E).restrictScalars ℂ) (1 ⊗ₜ[K] t))

/-- For an integral section, its generic norm is the norm of its image in the complex fibre. -/
@[simp]
theorem genericNorm_one_tmul (σ : K →+* ℂ) (x : E) :
    h.genericNorm σ (1 ⊗ₜ[𝓞 K] x) = h.norm σ (1 ⊗ₜ[𝓞 K] x) := by
  simp [genericNorm, LinearEquiv.restrictScalars_apply]

/-- Multiplying a generic vector by `a` multiplies its norm at `σ` by `|σ(a)|`. -/
@[simp]
theorem genericNorm_smul (σ : K →+* ℂ) (a : K) (t : K ⊗[𝓞 K] E) :
    h.genericNorm σ (a • t) = ‖σ a‖ * h.genericNorm σ t := by
  have hσ : a • (1 : Codomain σ) = σ a • (1 : Codomain σ) := by
    rw [Algebra.smul_def, Algebra.smul_def, ← Codomain.equiv_algebraMap σ a,
      Codomain.algebraMap_equiv]
  rw [genericNorm, ← TensorProduct.smul_tmul, hσ, ← TensorProduct.smul_tmul', map_smul,
    norm_smul, genericNorm]

/-- The zero generic vector has norm zero at every embedding. -/
@[simp]
theorem genericNorm_zero (σ : K →+* ℂ) : h.genericNorm σ 0 = 0 := by
  simp [genericNorm]

/-- A generic vector has strictly positive norm at every embedding exactly when it is nonzero. -/
@[simp]
theorem genericNorm_pos_iff (σ : K →+* ℂ) {t : K ⊗[𝓞 K] E} :
    0 < h.genericNorm σ t ↔ t ≠ 0 := by
  constructor
  · rintro hp rfl
    simp at hp
  · intro ht
    exact h.norm_pos ((LinearEquiv.map_ne_zero_iff _).2 (TauCeti.tmul_ne_zero one_ne_zero ht))

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

namespace NumberField

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E] [Module (𝓞 K) E]
  [Module.Finite (𝓞 K) E] [Module.IsTorsionFree (𝓞 K) E]

/-- For an integral section `s` of a rank-one lattice, the reciprocal norm of its coefficient
ideal is the index of the cyclic submodule generated by `s`. -/
theorem cardQuot_span_singleton_eq_inv_absNorm_ofSection
    (hE : Module.finrank K (K ⊗[𝓞 K] E) = 1) {s : E} (ht : (1 : K) ⊗ₜ[𝓞 K] s ≠ 0) :
    ((Submodule.span (𝓞 K) {s}).cardQuot : ℚ) = (absNorm (ofSection hE ht))⁻¹ := by
  have hs : s ≠ 0 := fun hs ↦ ht (by simp [hs])
  let e := linearEquivOfSection hE ht
  rw [← Submodule.cardQuot_span_singleton_map_equiv e s,
    cardQuot_span_singleton_fractionalIdeal (e.map_ne_zero_iff.mpr hs)]
  simp [e, one_div]

end NumberField
