/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAnalytic.Semianalytic.PartiallySemialgebraic

/-!
# Reindexing polynomial fibre coordinates

Partial semialgebraicity is preserved by selecting or repeating fibre coordinates. These
pullbacks put several graph relations into one coordinate space before eliminating their
auxiliary variables. Analytic changes of the base and reindexing of the fibre are separate
operations: no analytic dependence on a quantified fibre variable is introduced.
-/

public section

open Filter MvPolynomial Set Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι κ : Type*}

/-- Selecting or repeating fibre coordinates preserves polynomial dependence on the fibre
with analytic coefficients. -/
theorem IsAnalyticCoeffPolynomialOn.comp_snd {U : Set E} {f : E × (ι → ℝ) → ℝ}
    (hf : IsAnalyticCoeffPolynomialOn U f) (r : ι → κ) :
    IsAnalyticCoeffPolynomialOn U (fun p : E × (κ → ℝ) => f (p.1, p.2 ∘ r)) := by
  classical
  obtain ⟨P, hP, hfP⟩ := isAnalyticCoeffPolynomialOn_def.1 hf
  refine isAnalyticCoeffPolynomialOn_def.2
    ⟨rename r P, fun d => ?_, fun p => by rw [eval₂_rename, hfP]⟩
  have heq : (rename r P).coeff d =
      ∑ m ∈ P.support, if m.mapDomain r = d then P.coeff m else 0 := by
    conv_lhs => rw [P.as_sum, map_sum, coeff_sum]
    simp only [rename_monomial, coeff_monomial]
  rw [heq]
  exact Finset.analyticOnNhd_sum _ fun m _ => by
    split_ifs
    exacts [hP m, analyticOnNhd_const]

/-- Pulling back a finite Boolean presentation by a reindexing of the fibre preserves it. -/
theorem IsAnalyticCoeffBooleanCombination.preimage_comp_snd {U : Set E}
    {s : Set (E × (ι → ℝ))} (hs : IsAnalyticCoeffBooleanCombination U s) (r : ι → κ) :
    IsAnalyticCoeffBooleanCombination U
      ((fun p : E × (κ → ℝ) => (p.1, p.2 ∘ r)) ⁻¹' s) :=
  setOf_isAnalyticCoeffBooleanCombination_subset
    ((isSetAlgebra_setOf_isAnalyticCoeffBooleanCombination κ U).preimage
      (fun p : E × (κ → ℝ) => (p.1, p.2 ∘ r)))
    (fun _ hf => (hf.comp_snd r).isAnalyticCoeffBooleanCombination_setOf_eq_zero)
    (fun _ hf => (hf.comp_snd r).isAnalyticCoeffBooleanCombination_setOf_pos) hs

/-- Partial semialgebraicity over a base point is preserved by selecting or repeating fibre
coordinates. -/
theorem PartiallySemialgebraicAt.preimage_comp_snd {s : Set (E × (ι → ℝ))} {u : E}
    (hs : PartiallySemialgebraicAt s u) (r : ι → κ) :
    PartiallySemialgebraicAt ((fun p : E × (κ → ℝ) => (p.1, p.2 ∘ r)) ⁻¹' s) u := by
  obtain ⟨U, hU, t, ht, hst⟩ := partiallySemialgebraicAt_def.1 hs
  refine partiallySemialgebraicAt_def.2 ⟨U, hU, _, ht.preimage_comp_snd r, ?_⟩
  exact congrArg ((fun p : E × (κ → ℝ) => (p.1, p.2 ∘ r)) ⁻¹' ·) hst

/-- Partial semialgebraicity is preserved by selecting or repeating fibre coordinates. -/
theorem IsPartiallySemialgebraic.preimage_comp_snd {s : Set (E × (ι → ℝ))}
    (hs : IsPartiallySemialgebraic s) (r : ι → κ) :
    IsPartiallySemialgebraic ((fun p : E × (κ → ℝ) => (p.1, p.2 ∘ r)) ⁻¹' s) :=
  isPartiallySemialgebraic_iff.2 fun u => (hs.partiallySemialgebraicAt u).preimage_comp_snd r

end TauCeti
