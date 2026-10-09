/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Basic
public import TauCeti.Analysis.Distribution.Sobolev

/-!
# Agreement of first-order weak and Bessel Sobolev regularity

A real `L²` function on a finite-dimensional real inner product space belongs to
Mathlib's Bessel-potential space `H^{1,2}` exactly when it is the value of a weak-derivative
Sobolev function in `W^{1,2}`. The comparison complexifies the real function, since
Mathlib's Bessel-potential interface uses the complex Fourier transform. Equality of values
is almost everywhere, as appropriate for these spaces.

Weak directional derivatives agree with the distributional derivatives of the associated
tempered distribution, connecting the weak-gradient and Bessel-potential descriptions.

Use `TauCeti.HasWeakFDerivOn.memSobolev_one h` for the weak-to-Bessel inclusion and
`MeasureTheory.Lp.memSobolev_one_iff_exists_w1p_value_eq u` for the whole-space equivalence.

## References

* L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.8.
* M. Taylor, *Partial Differential Equations I*, Chapter 4.
* `MeasureTheory.Lp.exists_w1p_value_eq_of_memSobolev_one` (Bessel-to-weak inclusion).
* `TauCeti.hasWeakLineDerivOn_iff_lineDerivOp_toTemperedDistribution_ofReal_eq`
  (agreement of weak and distributional directional derivatives).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TemperedDistribution TopologicalSpace
open scoped ENNReal LineDeriv InnerProductSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E]

/-- A real `L²` function with an `L²` weak gradient has first-order Bessel regularity. -/
theorem HasWeakFDerivOn.memSobolev_one
    {u : Lp ℝ 2 (volume : Measure E)} {g : Lp E 2 (volume : Measure E)}
    (h : HasWeakFDerivOn volume ⊤ u (fun x => innerSL ℝ (g x))) :
    MemSobolev 1 2 (Lp.toTemperedDistribution (Complex.ofRealCLM.compLp u)) := by
  rw [← zero_add (1 : ℝ), TemperedDistribution.memSobolev_add_one_iff]
  refine ⟨memSobolev_zero_iff.mpr ⟨_, rfl⟩, fun v => ?_⟩
  let d : Lp ℝ 2 (volume : Measure E) := (innerSL ℝ v).compLp g
  have hd : HasWeakLineDerivOn volume ⊤ u d v := by
    refine (h.hasWeakLineDerivOn v).congr_ae_deriv ?_
    simp only [Opens.coe_top, Measure.restrict_univ]
    filter_upwards [(innerSL ℝ v).coeFn_compLp g] with x hx
    simpa only [innerSL_apply_apply, real_inner_comm] using hx.symm
  rw [(hasWeakLineDerivOn_iff_lineDerivOp_toTemperedDistribution_ofReal_eq u d v).mp hd]
  exact memSobolev_zero_iff.mpr ⟨_, rfl⟩

end TauCeti
