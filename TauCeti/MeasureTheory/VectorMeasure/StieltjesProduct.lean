/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.VectorMeasure.FiniteHorizon
public import Mathlib.MeasureTheory.VectorMeasure.IntegrationByParts

/-!
# Integration by parts on a finite horizon

Continuous bounded-variation paths on a closed horizon satisfy the Stieltjes product rule
with both endpoint terms. The integrals use `BoundedVariationOn.vectorMeasureIcc`, so they
exclude an initial atom and require no assumptions on either path outside the horizon.
The formula holds on every subinterval of that same horizon, without reconstructing the
integrator's measure at each observation time. It applies to general continuous bilinear
pairings, including multiplication, scalar multiplication and inner products.

This supplies the finite-variation product rule used in change-of-variables and
integrating-factor arguments. It does not identify a pathwise integral with a stochastic
integral or assert a product rule for discontinuous paths without jump corrections.

The proof applies Mathlib's
`BoundedVariationOn.setIntegral_Ioc_leftLim_vectorMeasure_eq_sub` to the constant extensions
and uses their continuity to remove the one-sided limits.

## References

* P. E. Protter, *Stochastic Integration and Differential Equations*, second edition,
  Chapter I, finite-variation integration.
-/

public section

open MeasureTheory Set

namespace BoundedVariationOn

variable {α E F G : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
  [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α]
  [DenselyOrdered α] [CompactIccSpace α]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  {f : α → E} {g : α → F} {a b c d : α}

/-- Integration by parts for continuous BV paths on a finite horizon, over any subinterval.
The measures are constructed on `[a,b]`, while the two integrals are over `(c,d]`.
No regularity or variation bound outside `[a,b]` is required. -/
theorem setIntegral_Ioc_vectorMeasureIcc_eq_sub
    (hf : BoundedVariationOn f (Icc a b)) (hg : BoundedVariationOn g (Icc a b))
    (hab : a ≤ b) (hfc : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g (Icc a b))
    (B : E →L[ℝ] F →L[ℝ] G) (hc : c ∈ Icc a b) (hd : d ∈ Icc a b) (hcd : c ≤ d) :
    ∫ᵛ x in Ioc c d, f x ∂[B; hg.vectorMeasureIcc hab] =
      B (f d) (g d) - B (f c) (g c) -
        ∫ᵛ x in Ioc c d, g x ∂[B.flip; hf.vectorMeasureIcc hab] := by
  let f' := Set.IccExtend hab (f ∘ Subtype.val)
  let g' := Set.IccExtend hab (g ∘ Subtype.val)
  have hcf : Continuous f' := hfc.domRestrict.Icc_extend'
  have hcg : Continuous g' := hgc.domRestrict.Icc_extend'
  have h := (hf.IccExtend hab).setIntegral_Ioc_leftLim_vectorMeasure_eq_sub
    (B := B) (hg.IccExtend hab) hcd
  have hleft : f'.leftLim = f' := funext fun _ ↦ hcf.continuousAt.continuousWithinAt.leftLim_eq
  have hright : g'.rightLim = g' := funext fun _ ↦ hcg.continuousAt.continuousWithinAt.rightLim_eq
  have hfr : f'.rightLim = f' := funext fun _ ↦ hcf.continuousAt.continuousWithinAt.rightLim_eq
  rw [hleft, hright, hfr] at h
  have hf' : EqOn f' f (Icc a b) := fun x hx ↦ IccExtend_of_mem hab _ hx
  have hg' : EqOn g' g (Icc a b) := fun x hx ↦ IccExtend_of_mem hab _ hx
  rw [hf' hd, hg' hd, hf' hc, hg' hc] at h
  have hsub : Ioc c d ⊆ Ioc a b := Ioc_subset_Ioc hc.1 hd.2
  simp only [vectorMeasureIcc_def,
    VectorMeasure.restrict_restrict _ measurableSet_Ioc measurableSet_Ioc,
    inter_eq_left.mpr hsub]
  rw [← VectorMeasure.setIntegral_congr_fun (fun x hx ↦ hf' (Ioc_subset_Icc_self (hsub hx))),
    ← VectorMeasure.setIntegral_congr_fun (fun x hx ↦ hg' (Ioc_subset_Icc_self (hsub hx)))]
  exact h

end BoundedVariationOn
