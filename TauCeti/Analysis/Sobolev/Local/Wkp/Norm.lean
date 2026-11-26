/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Norm
public import TauCeti.Analysis.Sobolev.Wkp.Basic
import TauCeti.Analysis.InnerProductSpace.Dual
import TauCeti.Analysis.Sobolev.Wkp.Chain

/-!
# The `W^{k,p}` size and the norm of `W^{k,p}(Ω)`

For a real function `u` on an open planar set `Ω`, the extended `W^{k,p}(Ω)` norm
`TauCeti.eLpNormWkp p Ω k u` sums the `Lᵖ(Ω)` norms of `u` and of its iterated weak derivatives,
which take values in iterated continuous linear maps. The space `TauCeti.Wkp volume Ω p k` records
the iterated weak derivatives as iterated gradients instead. This file shows that a function of
finite `W^{k,p}(Ω)` norm is represented by an element of `Wkp volume Ω p k` whose norm is at most
`eLpNormWkp p Ω k u` (`TauCeti.exists_wkp_norm_le_eLpNormWkp`). Bounds stated with
`eLpNormWkp`, such as the interior estimates of elliptic equations, thereby become bounds in the
space `Wkp`, to which Rellich's theorem applies. The analogue for the space `TauCeti.W1p` is
`TauCeti.exists_w1p_enorm_le_eLpNormWkp`.

The proof builds a chain of iterated weak gradients from the weak derivatives realizing the norm,
reading the first derivative through the inverse Riesz isomorphism, which has norm at most one,
and bounds the norm of the element of `Wkp` built from the chain by
`TauCeti.Wkp.exists_value_iteratedGradient_ae_eq_of_chain`.

## Main declarations

* `TauCeti.exists_wkp_norm_le_eLpNormWkp`: a real function of finite `W^{k,p}(Ω)` norm is an
  element of `Wkp volume Ω p k` of no larger norm.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal

namespace TauCeti

variable {p : ℝ≥0∞} {Ω : Opens ℂ}

/-- A field `g` at level `j` of finite `W^{n,p}(Ω)` norm is the level-`j` member of a chain of
iterated gradients on `Ω`, from level `j` through `j + n`, each the weak derivative of the
previous one and each in `Lᵖ(Ω)`, whose `Lᵖ(Ω)` norms add up to at most `‖g‖_{W^{n,p}(Ω)}`. -/
private theorem exists_iteratedGradient_chain_of_eLpNormWkp_ne_top (n : ℕ) :
    ∀ (j : ℕ) (g : ℂ → IteratedGradient ℂ j), eLpNormWkp p Ω n g ≠ ∞ →
      ∃ G : (i : ℕ) → ℂ → IteratedGradient ℂ i, G j = g ∧
        (∀ i, j ≤ i → i < j + n → HasWeakFDerivOn volume Ω (G i) (G (i + 1))) ∧
        (∀ i, j ≤ i → i ≤ j + n → MemLp (G i) p (volume.restrict Ω)) ∧
        ∑ i ∈ Finset.Ico j (j + n + 1), eLpNorm (G i) p (volume.restrict Ω) ≤
          eLpNormWkp p Ω n g := by
  induction n with
  | zero =>
    intro j g hg
    refine ⟨Function.update (fun i _ => 0) j g, Function.update_self .., fun i _ hi =>
      absurd hi (by omega), fun i hji hi => ?_, by simp⟩
    obtain rfl : i = j := by omega
    simpa using memLp_of_eLpNormWkp_ne_top hg
  | succ n ih =>
    intro j g hg
    obtain ⟨D, hD, hDn, hgeq⟩ := exists_hasWeakFDerivOn_eLpNormWkp_succ_eq_of_ne_top hg
    obtain ⟨G, hGD, hG, hGp, hGs⟩ := ih (j + 1) D hDn
    refine ⟨Function.update G j g, Function.update_self .., fun i hji hi => ?_,
      fun i hji hi => ?_, ?_⟩
    · rcases Nat.lt_or_eq_of_le hji with hji | rfl
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hG i hji (by omega)
      · rw [Function.update_self, Function.update_of_ne (by omega), hGD]
        exact hD
    · rcases Nat.lt_or_eq_of_le hji with hji | rfl
      · rw [Function.update_of_ne (by omega)]
        exact hGp i hji (by omega)
      · rw [Function.update_self]
        exact memLp_of_eLpNormWkp_ne_top hg
    · rw [Finset.sum_eq_sum_Ico_succ_bot (by omega), Function.update_self, hgeq,
        show j + (n + 1) + 1 = j + 1 + n + 1 by omega]
      gcongr
      refine le_of_eq_of_le (Finset.sum_congr rfl fun i hi => ?_) hGs
      rw [Function.update_of_ne (by simp only [Finset.mem_Ico] at hi; omega)]

variable [Fact (1 ≤ p)]

/-- **A function of finite `W^{k,p}(Ω)` norm is an element of `W^{k,p}(Ω)`.** A real function `u`
on an open planar set `Ω` whose `W^{k,p}(Ω)` norm `TauCeti.eLpNormWkp p Ω k u` is finite is
represented by an element of `Wkp volume Ω p k` whose norm is at most `eLpNormWkp p Ω k u`. -/
theorem exists_wkp_norm_le_eLpNormWkp {k : ℕ} {u : ℂ → ℝ} (hu : eLpNormWkp p Ω k u ≠ ∞) :
    ∃ v : Wkp volume Ω p k, Wkp.value k v =ᵐ[volume.restrict Ω] u ∧
      ENNReal.ofReal ‖v‖ ≤ eLpNormWkp p Ω k u := by
  cases k with
  | zero =>
    have hu' := memLp_of_eLpNormWkp_ne_top hu
    refine ⟨hu'.toLp u, by rw [Wkp.value_zero]; exact hu'.coeFn_toLp, ?_⟩
    rw [eLpNormWkp_zero] at hu ⊢
    exact (congrArg ENNReal.ofReal (Lp.norm_toLp u hu')).trans_le
      (ENNReal.ofReal_toReal hu).le
  | succ n =>
    obtain ⟨D, hD, hDn, hueq⟩ := exists_hasWeakFDerivOn_eLpNormWkp_succ_eq_of_ne_top hu
    -- The first gradient is the first weak derivative read through the inverse Riesz map.
    have hR : eLpNormWkp p Ω n (fun z => InnerProductSpace.toDualSymmL (D z)) ≤
        eLpNormWkp p Ω n D :=
      eLpNormWkp_clm_comp_le_of_norm_le_one _ (ContinuousLinearMap.opNorm_le_bound _ zero_le_one
        fun q => by simp)
    obtain ⟨G, hG0, hG, hGp, hGs⟩ :=
      exists_iteratedGradient_chain_of_eLpNormWkp_ne_top n 0 _ (ne_top_of_le_ne_top hDn hR)
    have h0 : HasWeakFDerivOn volume Ω u (fun z => innerSL ℝ (G 0 z)) := by
      simpa only [hG0, InnerProductSpace.toDualSymmL_apply,
        InnerProductSpace.innerSL_toDual_symm] using hD
    obtain ⟨v, hv, -, hnorm⟩ := Wkp.exists_value_iteratedGradient_ae_eq_of_chain n
      (memLp_of_eLpNormWkp_ne_top hu) h0 (fun i hi => hG i (Nat.zero_le i) (by omega))
      fun i hi => hGp i (Nat.zero_le i) (by omega)
    refine ⟨v, hv, hnorm.trans ?_⟩
    rw [hueq, Finset.range_eq_Ico]
    gcongr
    simp only [zero_add] at hGs
    exact hGs.trans hR

end TauCeti
