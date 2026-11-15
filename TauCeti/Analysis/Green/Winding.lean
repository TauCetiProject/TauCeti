/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.FiniteSum

/-!
# Green's theorem for absolutely continuous curves

For a closed AC curve, a real `C¹` field on an open neighborhood of the trace and winding
support satisfies the winding-weighted circulation identity. Both integrability statements
are conclusions. A cutoff is constructed before applying the global polygonal theorem;
uniform, derivative `L¹`, and winding-weight `L¹` approximation pass the identity to the curve.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace TauCeti.Green

/-- Green's theorem for a closed absolutely continuous curve with index vanishing outside
the open field domain. The winding numbers may be unbounded and the curve may intersect itself. -/
theorem green_ac_winding {γ : ℝ → ℂ} {a b : ℝ} {U : Set ℂ} {P Q : ℂ → ℝ}
    (hab : a < b) (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b)
    (hU : IsOpen U) (htrace : γ '' uIcc a b ⊆ U)
    (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U)
    (hindex : ∀ z ∉ U, Contour.windingNumber γ a b z = 0) :
    IntervalIntegrable (circulationFun P Q γ) volume a b ∧
      IntegrableOn (fun z ↦ windingWeight γ a b z * curl P Q z) U ∧
      (∫ t in a..b, circulationFun P Q γ t) =
        ∫ z in U, windingWeight γ a b z * curl P Q z := by
  have h := green_ac_winding_sum (s := {()}) (γ := fun _ : Unit ↦ γ)
    (a := fun _ ↦ a) (b := fun _ ↦ b) (w := fun _ ↦ (1 : ℤ))
    (fun _ _ ↦ hab) (fun _ _ ↦ hγ) (fun _ _ ↦ hclosed) hU
    (fun _ _ ↦ htrace) hP hQ (fun z hz ↦ by simpa using hindex z hz)
  simpa only [Finset.sum_singleton, Int.cast_one, one_mul, Finset.mem_singleton,
    forall_eq, forall_const, true_implies] using h

/-- Global real `C¹` fields satisfy Green's theorem for every closed AC curve, with both
integrability conclusions. Compact support of the field is not required. -/
theorem green_ac {γ : ℝ → ℂ} {a b : ℝ} {P Q : ℂ → ℝ}
    (hab : a < b) (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b)
    (hP : ContDiff ℝ 1 P) (hQ : ContDiff ℝ 1 Q) :
    IntervalIntegrable (circulationFun P Q γ) volume a b ∧
      Integrable (fun z ↦ windingWeight γ a b z * curl P Q z) ∧
      (∫ t in a..b, circulationFun P Q γ t) =
        ∫ z : ℂ, windingWeight γ a b z * curl P Q z := by
  simpa only [IntegrableOn, Measure.restrict_univ, setIntegral_univ] using
    green_ac_winding hab hγ hclosed isOpen_univ (subset_univ _)
      hP.contDiffOn hQ.contDiffOn (fun z hz ↦ False.elim (hz (mem_univ z)))

end TauCeti.Green
