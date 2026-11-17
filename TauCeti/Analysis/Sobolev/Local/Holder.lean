/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Holder
public import TauCeti.Analysis.Sobolev.Local.Basic

/-!
# Products of local `Lᵖ` functions

This file records two ways of producing `Lᵖ` functions from local `Lᵖ` functions on a set
`U ⊆ ℂ`, in the form used by weak formulations of first-order equations.

* **Hölder's inequality on compact subsets** (`TauCeti.MemLpLoc.clm_apply`): a locally `Lᵖ`
  field of continuous linear maps applied to a locally `L^q` field is locally `Lʳ` for
  `1/p + 1/q = 1/r`. With `p = ∞` this covers locally bounded coefficient fields.
* **Compactly supported cutoffs** (`TauCeti.MemLpLoc.memLp_smul_of_hasCompactSupport`): a
  continuous compactly supported factor supported in `U` turns a locally `Lᵖ` function on `U`
  into a function in `Lᵖ` of the whole plane.
-/

public section

open MeasureTheory

namespace TauCeti

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G] {p q r : ENNReal} {U : Set ℂ} {f : ℂ → F}

/-- **Hölder's inequality on compact subsets**: a locally `Lᵖ` field of continuous linear maps
applied to a locally `L^q` field is locally `Lʳ` for `1/p + 1/q = 1/r`. -/
theorem MemLpLoc.clm_apply [ENNReal.HolderTriple p q r] {A : ℂ → F →L[ℝ] G} {w : ℂ → F}
    (hA : MemLpLoc p U A) (hw : MemLpLoc q U w) : MemLpLoc r U (fun z => A z (w z)) :=
  memLpLoc_iff.2 fun K hK hc => (ContinuousLinearMap.id ℝ (F →L[ℝ] G)).memLp_of_bilin r
    (memLpLoc_iff.1 hA K hK hc) (memLpLoc_iff.1 hw K hK hc)

/-- A continuous compactly supported factor supported in `U` turns a locally `Lᵖ` function on `U`
into a function in `Lᵖ` of the whole plane. -/
theorem MemLpLoc.memLp_smul_of_hasCompactSupport {χ : ℂ → ℝ} (hf : MemLpLoc p U f)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hsupp : tsupport χ ⊆ U) :
    MemLp (fun z => χ z • f z) p volume := by
  have hcl : IsClosed (tsupport χ) := isClosed_tsupport χ
  have heq : (fun z => χ z • f z) = (tsupport χ).indicator (fun z => χ z • f z) := by
    refine (Set.indicator_eq_self.2 ?_).symm
    exact (Function.support_smul_subset_left χ f).trans (subset_tsupport χ)
  rw [heq, memLp_indicator_iff_restrict hcl.measurableSet.nullMeasurableSet]
  exact memLpLoc_iff.1 (hf.continuousOn_smul hχ.continuousOn) _ hsupp hχc

end TauCeti
