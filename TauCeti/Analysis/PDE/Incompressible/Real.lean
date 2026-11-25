/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Incompressible.Solenoidal
import TauCeti.Analysis.Sobolev.WeakDeriv.Interval
import TauCeti.Analysis.Calculus.LineDeriv.Basic
import TauCeti.MeasureTheory.Function.LocallyAEConst

/-!
# Solenoidal fields on the real line

Weak divergence in dimension one is the ordinary weak derivative. A solenoidal field on the
real line is almost everywhere constant, and finite `Lᵖ` norm forces this constant to vanish.
-/

public section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

/-- On the real line, weak divergence is the weak derivative in the direction `1`. -/
theorem hasWeakDivergenceOn_real_iff {μ : Measure ℝ} {Ω : Opens ℝ} {u g : ℝ → ℝ} :
    HasWeakDivergenceOn μ Ω u g ↔ HasWeakLineDerivOn μ Ω u g 1 := by
  rw [hasWeakDivergenceOn_iff, hasWeakLineDerivOn_iff_testFunction]
  have hcomplete : CompleteSpace ℝ := inferInstance
  simp [hcomplete, gradient_eq_deriv', lineDeriv_one, smul_eq_mul, mul_comm]

/-- A solenoidal field on the whole real line agrees almost everywhere with a constant. -/
theorem IsSolenoidalOn.exists_ae_eq_const {u : ℝ → ℝ} (hu : IsSolenoidalOn volume ⊤ u) :
    ∃ c : ℝ, u =ᵐ[volume] fun _ ↦ c := by
  have hd := hasWeakDivergenceOn_real_iff.mp (isSolenoidalOn_iff_hasWeakDivergenceOn.mp hu)
  suffices h : ∃ c : ℝ, u =ᵐ[volume.restrict (univ : Set ℝ)] fun _ ↦ c by
    simpa only [Measure.restrict_univ] using h
  refine isPreconnected_univ.exists_ae_eq_const_of_forall_nhds isLindelof_univ ?_
  intro x _
  obtain ⟨c, hc⟩ := (hd.mono (Ω' := ⟨Ioo (x - 1) (x + 1), isOpen_Ioo⟩) le_top).exists_ae_eq_const
  exact ⟨c, Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (by linarith), hc⟩

/-- For every finite exponent `p ≥ 1`, the solenoidal subspace on the real line is zero. -/
theorem solenoidalLp_real_eq_bot {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    solenoidalLp ℝ p = ⊥ := by
  refine le_antisymm (fun u hu ↦ ClosedSubmodule.mem_bot.mpr ?_) bot_le
  obtain ⟨c, hc⟩ := (mem_solenoidalLp_iff.mp hu).exists_ae_eq_const
  have hmem := (Lp.memLp u).ae_eq hc
  have hzero : c = 0 := by
    have hp0 : p ≠ 0 := ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))
    simpa only [Real.volume_univ, lt_self_iff_false, or_false] using
      (memLp_const_iff hp0 hp).mp hmem
  exact Lp.ext (hc.trans (hzero ▸ (Lp.coeFn_zero ℝ p volume).symm))

end TauCeti
