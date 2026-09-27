/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Restriction
public import TauCeti.MeasureTheory.Function.Lp.LocalApproximateIdentity

/-!
# Convergence of interior mollifications of Sobolev derivative fields

The value and every recorded weak derivative of a domain Sobolev function are `Lᵖ` classes.
Extend each field by zero, mollify it on the ambient space, and restrict back to an open
subdomain. For finite `p`, these fields converge in the local `Lᵖ` norm as the bump radius
tends to zero. This is the norm-convergence input for constructing local smooth Sobolev
approximations; the derivative identities for the mollifications are separate.

## References

L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.3.1.
-/

public section

noncomputable section

namespace TauCeti

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega U : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

local instance : (mu.restrict (univ : Set E)).IsAddHaarMeasure := by
  rw [Measure.restrict_univ]
  infer_instance

/-- Mollification of the zero extension of the value of `u ∈ W^{k,p}(Ω)` converges in
`Lᵖ(U)` to the value of the restriction, for every open `U ⊆ Ω` and `p < ∞`. -/
theorem Wkp.tendsto_mollified_value (hp : p ≠ ∞) (hU : U ≤ Omega)
    {I : Type*} {l : Filter I} {phi : I → ContDiffBump (0 : E)}
    (hphi : Tendsto (fun i => (phi i).rOut) l (nhds 0))
    (k : ℕ) (u : Wkp mu Omega p k) :
    Tendsto (fun i =>
      Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by
        simpa only [one_smul] using Measure.restrict_mono_set mu
          (subset_univ (U : Set E))) <|
        normedBumpLp hp (phi i) (mu.restrict (univ : Set E))
          (extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet (subset_univ _)
            (Wkp.value k u))) l (nhds (Wkp.value k (Wkp.restrictL hU k u))) := by
  rw [Wkp.value_restrictL]
  exact tendsto_normedBumpLp_extendByZero_restrict hp Omega.isOpen.measurableSet
    (SetLike.coe_subset_coe.mpr hU) hphi (Wkp.value k u)

/-- Mollification of the zero extension of the highest derivative of
`u ∈ W^{k+1,p}(Ω)` converges in `Lᵖ(U)` to the corresponding derivative of its restriction.
Together with the value case, this controls every component of the iterated graph norm. -/
theorem Wkp.tendsto_mollified_iteratedGradient (hp : p ≠ ∞) (hU : U ≤ Omega)
    {I : Type*} {l : Filter I} {phi : I → ContDiffBump (0 : E)}
    (hphi : Tendsto (fun i => (phi i).rOut) l (nhds 0))
    (k : ℕ) (u : Wkp mu Omega p (k + 1)) :
    Tendsto (fun i =>
      Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by
        simpa only [one_smul] using Measure.restrict_mono_set mu
          (subset_univ (U : Set E))) <|
        normedBumpLp hp (phi i) (mu.restrict (univ : Set E))
          (extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet (subset_univ _)
            (Wkp.iteratedGradient k u))) l
      (nhds (Wkp.iteratedGradient k (Wkp.restrictL hU (k + 1) u))) := by
  rw [Wkp.iteratedGradient_restrictL]
  exact tendsto_normedBumpLp_extendByZero_restrict hp Omega.isOpen.measurableSet
    (SetLike.coe_subset_coe.mpr hU) hphi
    (Wkp.iteratedGradient k u)

end TauCeti
