/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Entropic.Duality

/-!
# Symmetric Schrödinger potentials

For a bounded measurable symmetric cost, a positive temperature and a probability law `μ`, the
entropic transport problem from `μ` to itself has a Gibbs representation with the same potential
in both coordinates. This symmetric potential is unique `μ`-almost everywhere: unlike a pair of
potentials, it has no additive-constant ambiguity. Its integral gives half of the self-transport
value. This is the self-potential representation used to study the debiased entropic transport
cost and Sinkhorn negentropy.

The results require no topology. They use strong entropic duality and uniqueness of potential
pairs from `TauCeti.MeasureTheory.OptimalTransport.Entropic.Duality`: exchanging the two
potentials preserves their value, and their average is a symmetric representative.

## References

* J. Feydy, T. Séjourné, F.-X. Vialard, S. Amari, A. Trouvé and G. Peyré,
  *Interpolating between optimal transport and MMD using Sinkhorn divergences*,
  AISTATS 2019, §2, for symmetric self-potentials and Sinkhorn negentropy.
* M. Nutz, *Introduction to Entropic Optimal Transport*, lecture notes, 2021,
  for the uniqueness of Schrödinger potentials modulo constants.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace TauCeti

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  {c : X × X → ℝ≥0∞} {ε B : ℝ≥0} {f g : X → ℝ}

/-- Symmetric entropic dual maximisers have no additive-constant ambiguity: they agree almost
everywhere. The cost need not be symmetric for this uniqueness statement. -/
theorem ae_eq_of_entropicDualValue_self_eq (hc : Measurable c) (hcB : ∀ z, c z ≤ B)
    (hε : ε ≠ 0) (hf : Integrable f μ) (hg : Integrable g μ)
    (hexf : Integrable (entropicGibbsFactor c ε f f) (μ.prod μ))
    (hexg : Integrable (entropicGibbsFactor c ε g g) (μ.prod μ))
    (hfval : entropicDualValue c ε μ μ f f = (entropicTransportCost c ε μ μ).toReal)
    (hgval : entropicDualValue c ε μ μ g g = (entropicTransportCost c ε μ μ).toReal) :
    f =ᵐ[μ] g := by
  obtain ⟨a, ha, ha'⟩ :=
    exists_ae_eq_add_const_of_entropicDualValue_eq_toReal_entropicTransportCost
      hc hcB hε hf hf hexf hfval hg hg hexg hgval
  filter_upwards [ha, ha'] with x hx hx'
  linarith

/-- **Existence of a symmetric self-potential.** For a bounded measurable symmetric cost and a
positive temperature, the self-transport dual problem is attained by a bounded measurable
potential used in both coordinates. -/
theorem exists_entropicDualValue_self_eq (hc : Measurable c) (hcB : ∀ z, c z ≤ B)
    (hcs : c ∘ Prod.swap = c) (hε : ε ≠ 0) :
    ∃ (f : X → ℝ) (C : ℝ), Measurable f ∧ (∀ x, |f x| ≤ C) ∧
      entropicDualValue c ε μ μ f f = (entropicTransportCost c ε μ μ).toReal := by
  obtain ⟨φ, ψ, C, hφ, hψ, hφC, hψC, hval⟩ :=
    exists_entropicDualValue_eq_toReal_entropicTransportCost (μ := μ) (ν := μ) hc hcB hε
  have hφi : Integrable φ μ := .of_bound hφ.aestronglyMeasurable C (ae_of_all _ hφC)
  have hψi : Integrable ψ μ := .of_bound hψ.aestronglyMeasurable C (ae_of_all _ hψC)
  have hswap : entropicDualValue c ε μ μ ψ φ = (entropicTransportCost c ε μ μ).toReal := by
    conv_lhs => rw [← hcs, entropicDualValue_comp_swap]
    exact hval
  obtain ⟨a, ha, -⟩ :=
    exists_ae_eq_add_const_of_entropicDualValue_eq_toReal_entropicTransportCost hc hcB hε
      hφi hψi (integrable_entropicGibbsFactor_of_le hc hφ hψ
        (fun x ↦ le_of_abs_le (hφC x)) (fun x ↦ le_of_abs_le (hψC x))) hval
      hψi hφi (integrable_entropicGibbsFactor_of_le hc hψ hφ
        (fun x ↦ le_of_abs_le (hψC x)) (fun x ↦ le_of_abs_le (hφC x))) hswap
  -- Averaging preserves the bound, and agrees a.e. with opposite constant shifts of the pair.
  refine ⟨fun x ↦ (φ x + ψ x) / 2, C, (hφ.add hψ).div_const _, fun x ↦ ?_, ?_⟩
  · calc |(φ x + ψ x) / 2| = |φ x + ψ x| / 2 := by norm_num [abs_div]
         _ ≤ (|φ x| + |ψ x|) / 2 := by gcongr; exact abs_add_le _ _
         _ ≤ C := by linarith [hφC x, hψC x]
  · have hleft : (fun x ↦ (φ x + ψ x) / 2) =ᵐ[μ] (fun x ↦ φ x + -(a / 2)) :=
      ha.mono fun x hx ↦ by dsimp only at hx ⊢; linarith
    have hright : (fun x ↦ (φ x + ψ x) / 2) =ᵐ[μ] (fun x ↦ ψ x - -(a / 2)) :=
      ha.mono fun x hx ↦ by dsimp only at hx ⊢; linarith
    rw [entropicDualValue_congr_ae hleft hright,
      entropicDualValue_add_const_sub_const hφi hψi rfl]
    exact hval

/-- **The symmetric Gibbs representation of self-transport.** There is a bounded measurable
self-potential `f` whose Gibbs density defines a coupling of `μ` with itself, and the finite
entropic self-transport value is exactly `2 * ∫ f dμ`. -/
theorem exists_isCoupling_entropicGibbsFactor_self (hc : Measurable c) (hcB : ∀ z, c z ≤ B)
    (hcs : c ∘ Prod.swap = c) (hε : ε ≠ 0) :
    ∃ (f : X → ℝ) (C : ℝ), Measurable f ∧ (∀ x, |f x| ≤ C) ∧
      IsCoupling
        ((μ.prod μ).withDensity fun z ↦ ENNReal.ofReal (entropicGibbsFactor c ε f f z)) μ μ ∧
      entropicDualValue c ε μ μ f f = (entropicTransportCost c ε μ μ).toReal ∧
      (entropicTransportCost c ε μ μ).toReal = 2 * ∫ x, f x ∂μ := by
  obtain ⟨f, C, hf, hfC, hfval⟩ := exists_entropicDualValue_self_eq (μ := μ) hc hcB hcs hε
  have hfi : Integrable f μ := .of_bound hf.aestronglyMeasurable C (ae_of_all _ hfC)
  have hexp := integrable_entropicGibbsFactor_of_le (μ := μ) (ν := μ) (ε := ε) hc hf hf
    (fun x ↦ le_of_abs_le (hfC x)) (fun x ↦ le_of_abs_le (hfC x))
  obtain ⟨π, hπ, hopt, -⟩ :=
    exists_isCoupling_lintegral_add_mul_klDiv_eq_entropicTransportCost (μ := μ) (ν := μ) hc hcB hε
  have hπeq : π = (μ.prod μ).withDensity fun z ↦
      ENNReal.ofReal (entropicGibbsFactor c ε f f z) :=
    (hπ.entropicDualValue_eq_toReal_lintegral_add_mul_klDiv_iff hc.aemeasurable hε hfi hfi hexp
      (hopt ▸ entropicTransportCost_ne_top_of_ae_le (ae_of_all _ hcB) ε)).1 (hopt ▸ hfval)
  refine ⟨f, C, hf, hfC, hπeq ▸ hπ, hfval, ?_⟩
  rw [← hfval, hπ.entropicDualValue_eq_of_eq_withDensity hπeq hexp,
    kantorovichDualValue_def, two_mul]

end TauCeti
