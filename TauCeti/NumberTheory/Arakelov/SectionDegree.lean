/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# The degree computed with a section, for a family of norms

For an `𝓞 K`-module `E`, a family `ν σ : E → ℝ` of norms indexed by the complex embeddings
`σ : K →+* ℂ` and a section `s : E`, the expression `log #(E / 𝓞 K • s) - Σ_σ log ν_σ(s)` is the
Arakelov degree of a hermitian line computed with a nonzero section. Each model of hermitian
bundles specializes it to its own norms.

## Main definitions

* `TauCeti.sectionDegreeOfNorms`: the expression `log #(E / 𝓞 K • s) - Σ_σ log ν_σ(s)`.

## Main statements

* `TauCeti.sectionDegreeOfNorms_exp_neg_mul`: multiplying every norm by `e^{-c}` adds
  `[K : ℚ] c`.
* `TauCeti.sectionDegreeOfNorms_eq_zero`: a generating section of norm `1` everywhere has
  degree `0`.

## References

* P. Deligne, *Preuves des conjectures de Tate et de Shafarevitch*, Séminaire Bourbaki 616,
  §1.1, pp. 25–26.
* L. Szpiro, *Degrés, intersections, hauteurs*, Astérisque 127, §1.2, p. 13.
-/

public noncomputable section

open NumberField

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K] {E : Type*} [AddCommGroup E] [Module (𝓞 K) E]

/-- The expression `log #(E / 𝓞 K • s) - Σ_σ log ν_σ(s)` attached to a family of norms `ν` and a
section `s`, the sum running over all field embeddings `σ : K →+* ℂ`. -/
def sectionDegreeOfNorms (ν : (K →+* ℂ) → E → ℝ) (s : E) : ℝ :=
  Real.log (Submodule.span (𝓞 K) {s}).cardQuot - ∑ σ : K →+* ℂ, Real.log (ν σ s)

/-- The degree computed with `s` is `log #(E / 𝓞 K • s) - Σ_σ log ν_σ(s)`. -/
theorem sectionDegreeOfNorms_def (ν : (K →+* ℂ) → E → ℝ) (s : E) :
    sectionDegreeOfNorms ν s =
      Real.log (Submodule.span (𝓞 K) {s}).cardQuot - ∑ σ : K →+* ℂ, Real.log (ν σ s) :=
  (rfl)

/-- Multiplying every norm by `e^{-c}` adds `[K : ℚ] c` to the degree computed with a section
of nonzero norms. -/
theorem sectionDegreeOfNorms_exp_neg_mul (ν : (K →+* ℂ) → E → ℝ) (c : ℝ) {s : E}
    (hs : ∀ σ, ν σ s ≠ 0) :
    sectionDegreeOfNorms (fun σ x => Real.exp (-c) * ν σ x) s =
      sectionDegreeOfNorms ν s + Module.finrank ℚ K * c := by
  have h σ : Real.log (Real.exp (-c) * ν σ s) = -c + Real.log (ν σ s) := by
    rw [Real.log_mul (Real.exp_pos _).ne' (hs σ), Real.log_exp]
  simp only [sectionDegreeOfNorms_def, h, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, NumberField.Embeddings.card, nsmul_eq_mul]
  ring

/-- A section generating `E` and of norm `1` at every embedding has degree `0`. -/
theorem sectionDegreeOfNorms_eq_zero {ν : (K →+* ℂ) → E → ℝ} {s : E}
    (hs : Submodule.span (𝓞 K) {s} = ⊤) (hν : ∀ σ, ν σ s = 1) : sectionDegreeOfNorms ν s = 0 := by
  simp [sectionDegreeOfNorms_def, hs, hν, Submodule.cardQuot_top]

end TauCeti
