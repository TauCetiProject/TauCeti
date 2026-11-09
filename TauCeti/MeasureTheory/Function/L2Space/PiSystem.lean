/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.MeasureTheory.Integral.PiSystem
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Density of indicators of a generating π-system

The indicators of a generating π-system of finite-measure sets span a dense subspace of
real L² when countably many members cover the space. This applies in particular to elementary
predictable rectangles. Orthogonality gives vanishing set integrals; local integrability on
the finite-measure covering sets then gives almost-everywhere vanishing.
-/

public section

open MeasureTheory Set

namespace MeasureTheory.Measure

/-- Indicators of a generating π-system of finite-measure sets have dense span in real L²
if countably many members of the system cover the space. -/
theorem dense_span_indicatorConstLp_of_isPiSystem
    {X κ : Type*} {m : MeasurableSpace X} [Countable κ]
    (μ : Measure X) {C : Set (Set X)}
    (hgen : MeasurableSpace.generateFrom C = m) (hpi : IsPiSystem C)
    (hfinite : ∀ R ∈ C, μ R ≠ ⊤)
    (s : κ → Set X) (hs : ∀ n, s n ∈ C) (hcover : ⋃ n, s n = univ) :
    Dense (Submodule.span ℝ (range (fun R : C ↦
      indicatorConstLp 2 (hgen ▸ MeasurableSpace.measurableSet_generateFrom R.property)
        (hfinite R R.property) (1 : ℝ))) : Set (Lp ℝ 2 μ)) := by
  let K := Submodule.span ℝ (range (fun R : C ↦
    indicatorConstLp 2 (hgen ▸ MeasurableSpace.measurableSet_generateFrom R.property)
      (hfinite R R.property) (1 : ℝ)))
  apply Submodule.dense_iff_topologicalClosure_eq_top.2
  apply Submodule.orthogonal_eq_bot_iff.1
  rw [Submodule.orthogonal_closure]
  apply eq_bot_iff.2
  intro f hf
  apply (Submodule.mem_bot ℝ).2
  apply Lp.eq_zero_iff_ae_eq_zero.2
  refine TauCeti.ae_eq_zero_of_forall_setIntegral_eq_zero_of_isPiSystem hgen hpi s hs hcover ?_ ?_
  · intro n
    have : IsFiniteMeasure (μ.restrict (s n)) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using (hfinite _ (hs n)).lt_top⟩
    exact ((Lp.memLp f).restrict (s n)).integrable (by norm_num)
  · intro R hR
    have hi := (K.mem_orthogonal f).1 hf _ (Submodule.subset_span (mem_range_self ⟨R, hR⟩))
    rwa [L2.inner_indicatorConstLp_one] at hi

end MeasureTheory.Measure
