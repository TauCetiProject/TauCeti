/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Expect
public import TauCeti.RepresentationTheory.SU2.Weyl.Integration
import Mathlib.Algebra.Order.BigOperators.Expect
import TauCeti.Analysis.Normed.Operator.Dense

/-!
# The Weyl criterion for `SU(2)`

For finite samples of elements of `SU(2)`, convergence to Haar probability against continuous
class functions is equivalent to the vanishing of the averages of the nontrivial symmetric-power
characters. Samples are finite sets of indices, so repeated group elements retain their
multiplicities. Eventual nonemptiness accounts for the trivial character.

See K. S. Kedlaya, *Notes on analytic number theory*, §24.2, for the character criterion on compact
groups. Here the dense character span is `SU2.characterSpan`.
-/

public section

open Filter MeasureTheory
open scoped BigOperators Topology

namespace TauCeti.SU2

variable {ι κ : Type*} {l : Filter κ}

/-- Averages over finite samples converge against every continuous class function precisely when
they converge to zero against each positive-degree symmetric-power character. -/
theorem tendsto_expect_classFunction_iff (s : κ → Finset ι) (g : ι → SU2)
    (hs : ∀ᶠ k in l, (s k).Nonempty) :
    (∀ f : C(SU2, ℂ), (∀ u a : SU2, f (u * a * u⁻¹) = f a) →
      Tendsto (fun k ↦ 𝔼 i ∈ s k, f (g i)) l (𝓝 (∫ a, f a ∂haarProb SU2))) ↔
    ∀ d : ℕ, d ≠ 0 →
      Tendsto (fun k ↦ 𝔼 i ∈ s k, (symPower d).character (g i)) l (𝓝 0) := by
  constructor
  · intro h d hd
    simpa [symPowerCharacter_apply, integral_character_symPower, hd] using
      h (symPowerCharacter d) (fun u a ↦ by
        simpa only [symPowerCharacter_apply] using Representation.char_conj (symPower d) a u)
  · intro h f hf
    let A (k : κ) : C(SU2, ℂ) →L[ℂ] ℂ :=
      ((s k).card : ℂ)⁻¹ • ∑ i ∈ s k, ContinuousMap.evalCLM ℂ (g i)
    let H : C(SU2, ℂ) →L[ℂ] ℂ := haarAverage SU2
    have hA (k : κ) (v : C(SU2, ℂ)) : A k v = 𝔼 i ∈ s k, v (g i) := by
      simp [A, Finset.expect_eq_sum_div_card, div_eq_inv_mul]
    have hbound : ∀ᶠ k in l, ‖A k‖ ≤ 1 := hs.mono fun k hk ↦
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v ↦ by
        rw [hA, one_mul]
        exact (RCLike.norm_expect_le (K := ℂ)).trans
          (Finset.expect_le hk fun i _ ↦ v.norm_coe_le_norm _)
    let M : Submodule ℂ C(SU2, ℂ) :=
      { carrier := {v | Tendsto (fun k ↦ A k v) l (𝓝 (H v))}
        zero_mem' := by
          simpa using (tendsto_const_nhds : Tendsto (fun _ : κ ↦ (0 : ℂ)) l (𝓝 0))
        add_mem' := fun hu hv ↦ by simpa only [Set.mem_ofPred_eq, map_add] using hu.add hv
        smul_mem' := fun c _ hv ↦ by
          simpa only [Set.mem_ofPred_eq, map_smul] using hv.const_smul c }
    have hspan : characterSpan ≤ M := characterSpan_le_iff.mpr fun d ↦ by
      have hH : H (symPowerCharacter d) = if d = 0 then 1 else 0 := by
        simp [H, haarAverage_apply, symPowerCharacter_apply]
      -- Expose membership in the locally defined submodule of convergent test functions.
      change Tendsto (fun k ↦ A k (symPowerCharacter d)) l (𝓝 (H (symPowerCharacter d)))
      simp only [hA, hH, symPowerCharacter_apply]
      by_cases hd : d = 0
      · subst d
        simpa using tendsto_const_nhds.congr'
          (hs.mono fun k hk ↦ (Finset.expect_const hk (1 : ℂ)).symm)
      · simpa [hd] using h d hd
    have hlim : Tendsto (fun k ↦ A k f) l (𝓝 (H f)) := by
      refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
      have hε' : 0 < ε / 3 := by positivity
      obtain ⟨v, hv, hfv⟩ := exists_mem_characterSpan_norm_sub_lt hf hε'
      have hvlim : Tendsto (fun k ↦ A k v) l (𝓝 (H v)) := hspan hv
      filter_upwards [hbound, Metric.tendsto_nhds.mp hvlim _ hε'] with k hk hkv
      have hHv : ‖H‖ ≤ 1 := norm_haarAverage_le_one SU2
      have hle := ContinuousLinearMap.norm_sub_apply_le_of_norm_le hk hHv f v
      rw [dist_eq_norm] at hkv ⊢
      linarith
    simpa only [hA, H, haarAverage_apply] using hlim

end TauCeti.SU2
