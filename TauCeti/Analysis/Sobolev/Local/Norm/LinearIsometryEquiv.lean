/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Norm
public import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# The `W^{k,p}` size under linear isometric equivalences

A linear isometric equivalence `e : F ≃ₗᵢ[ℝ] G` of the codomain preserves the `W^{k,p}` size
`TauCeti.eLpNormWkp`. Its main use is the passage to `ULift G` through
`LinearIsometryEquiv.ulift`, which moves the values of a map to a larger universe so that an
induction on the order can pass from `g` to `fderiv ℝ g`, and back again without changing any
norm.

## Main declarations

* `TauCeti.eLpNormWkp_linearIsometryEquiv_comp`: `‖e ∘ f‖_{W^{k,p}(U)} = ‖f‖_{W^{k,p}(U)}`.
-/

public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G] {p : ℝ≥0∞} {U : Set ℂ} {k : ℕ}

/-- A linear isometric equivalence does not increase the `W^{k,p}` size. -/
private theorem eLpNormWkp_linearIsometryEquiv_comp_le [CompleteSpace G] (e : F ≃ₗᵢ[ℝ] G)
    (f : ℂ → F) : eLpNormWkp p U k (fun z => e (f z)) ≤ eLpNormWkp p U k f := by
  have hn : ‖(e.toContinuousLinearEquiv : F →L[ℝ] G)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by simp
  have he : ‖(e.toContinuousLinearEquiv : F →L[ℝ] G)‖ₑ ≤ 1 :=
    (ofReal_norm _).symm.trans_le (ENNReal.ofReal_le_one.2 hn)
  calc
    _ ≤ ‖(e.toContinuousLinearEquiv : F →L[ℝ] G)‖ₑ * eLpNormWkp p U k f :=
      eLpNormWkp_clm_comp_le (e.toContinuousLinearEquiv : F →L[ℝ] G)
    _ ≤ 1 * eLpNormWkp p U k f := by gcongr
    _ = _ := one_mul _

/-- **Linear isometric equivalences preserve the `W^{k,p}` size.** For a linear isometric
equivalence `e : F ≃ₗᵢ[ℝ] G` between complete spaces, `‖e ∘ f‖_{W^{k,p}(U)} = ‖f‖_{W^{k,p}(U)}`. -/
theorem eLpNormWkp_linearIsometryEquiv_comp [CompleteSpace F] [CompleteSpace G]
    (e : F ≃ₗᵢ[ℝ] G) (f : ℂ → F) :
    eLpNormWkp p U k (fun z => e (f z)) = eLpNormWkp p U k f := by
  refine le_antisymm (eLpNormWkp_linearIsometryEquiv_comp_le e f) ?_
  calc
    _ = eLpNormWkp p U k (fun z => e.symm (e (f z))) := by simp
    _ ≤ _ := eLpNormWkp_linearIsometryEquiv_comp_le e.symm _

end TauCeti
