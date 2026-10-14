/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Graphon.StandardBorelModel.Basic

/-!
# Regression for the carrier-free graphon representation

`Graphon.exists_comap_natBool` factors a jointly measurable kernel through one map in each
coordinate, then retains symmetry and the `[0, 1]` range in the factor graphon. This regression
uses an uncountable carrier with the discrete measurable space and a point-mass probability
measure, so the factorization cannot rely on a standard Borel structure or on the measure seeing
more than one point. Its nonconstant strict representative checks that both coordinates of the
factorization retain the original values; the factor's symmetry and range are checked everywhere,
including outside the image of the carrier map.

## References

* S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*, NYJM Monographs 4
  (2013), Lemma 7.3 and Theorem 7.1.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti.DenseGraphLimits

-- The uncountable carrier is discrete, so it is not being supplied with a standard Borel
-- structure. The point mass below is nevertheless a probability measure.
/-- The discrete measurable space on the real carrier used by the regression below. -/
local instance instMeasurableSpaceRealTauCeti : MeasurableSpace ℝ := ⊤

/-- A strict graphon on the uncountable discrete carrier, supported on one point in each
coordinate. -/
private def carrierWitness : Graphon ℝ (Measure.dirac (0 : ℝ)) where
  toFun x y := if x = 0 ∧ y = 0 then 1 else 0
  symm' := by
    intro x y
    simp [and_comm]
  meas' := by
    have hzero : MeasurableSet ({0} : Set ℝ) := by simp
    apply Measurable.ite
    · exact hzero.preimage measurable_fst |>.inter (hzero.preimage measurable_snd)
    · exact measurable_const
    · exact measurable_const
  bdd' := by
    refine ⟨1, ?_⟩
    intro x y
    split_ifs <;> norm_num
  mem01' := by
    intro x y
    split_ifs <;> norm_num

private theorem carrierWitness_apply (x y : ℝ) :
    carrierWitness x y = if x = 0 ∧ y = 0 then 1 else 0 := rfl

/-- On an uncountable carrier with the discrete measurable space, a nonconstant pointwise graphon
still factors through a Cantor-space graphon, and the factor retains its laws everywhere. -/
example : ∃ (q : ℝ → ℕ → Bool) (hq : Measurable q)
    (V : Graphon (ℕ → Bool) ((Measure.dirac (0 : ℝ)).map q)),
      V.comap q hq (Measure.dirac (0 : ℝ)) = carrierWitness ∧
        (∀ a b, V a b = V b a ∧ V a b ∈ Set.Icc (0 : ℝ) 1) ∧
        V (q 0) (q 0) = 1 ∧ V (q 0) (q 1) = 0 := by
  obtain ⟨q, hq, V, hV⟩ := carrierWitness.exists_comap_natBool
  refine ⟨q, hq, V, hV, ?_, ?_, ?_⟩
  · intro a b
    exact ⟨V.symm a b, V.mem_Icc a b⟩
  · have h := congrArg (fun X : Graphon ℝ (Measure.dirac 0) => X 0 0) hV
    rw [Graphon.comap_apply] at h
    rw [carrierWitness_apply] at h
    norm_num at h
    exact h
  · have h := congrArg (fun X : Graphon ℝ (Measure.dirac 0) => X 0 1) hV
    rw [Graphon.comap_apply] at h
    rw [carrierWitness_apply] at h
    norm_num at h
    exact h

end DenseGraphLimits

end TauCeti
