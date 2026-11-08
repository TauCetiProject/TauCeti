/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.CrossedProduct.Full
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.HilbertSum

/-!
# Full integrated representations and Hilbert direct sums

Integration on the full crossed product commutes with arbitrary Hilbert direct sums of
covariant representations. The coordinatewise identity for vector integrals extends from
the dense compact-support algebra by continuity. Both the index type and summand Hilbert
spaces lie in the universe supported by `CovariantRepresentation.integratedFull`.

This extends the direct-sum compatibility of `integratedOperator` to `integratedFull`,
following Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2.
-/

public section

noncomputable section

open MeasureTheory
open scoped CStarAlgebra

namespace TauCeti.CStarAction.CovariantRepresentation

universe u v

variable {G : Type u} {A : Type v} {ι : Type (max u v)} {H : ι → Type (max u v)}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
  [∀ i, CompleteSpace (H i)] {α : CStarAction G A}
  (P : ∀ i, CovariantRepresentation α (H i)) (μ : Measure G) [μ.IsHaarMeasure]

/-- Evaluation in a Hilbert summand commutes with the full integrated representation. -/
@[simp]
theorem integratedFull_hilbertSum_apply (a : FullCrossedProduct α μ) (x : lp H 2) (i : ι) :
    (hilbertSum P).integratedFull μ a x i = (P i).integratedFull μ a (x i) := by
  -- Use bundled evaluation to avoid relying on the coercion from `lp` through `PreLp`.
  suffices h : lp.evalCLM ℂ H 2 i ((hilbertSum P).integratedFull μ a x) =
      (P i).integratedFull μ a (x i) by
    simpa only [lp.evalCLM_apply] using h
  induction a using FullCrossedProduct.induction_on with
  | hp =>
    exact isClosed_eq
      ((lp.evalCLM ℂ H 2 i).continuous.comp
        ((map_continuous ((hilbertSum P).integratedFull μ)).clm_apply continuous_const))
      ((map_continuous ((P i).integratedFull μ)).clm_apply continuous_const)
  | ih f =>
    simp only [integratedFull_of, integratedStarAlgHom_apply, lp.evalCLM_apply,
      integratedOperator_hilbertSum_apply]

/-- Full integration turns a Hilbert direct sum of covariant pairs into the Hilbert direct sum
of their full integrated representations. -/
theorem integratedFull_hilbertSum (a : FullCrossedProduct α μ) :
    (hilbertSum P).integratedFull μ a =
      lp.mapCLM 2 (fun i => (P i).integratedFull μ a) (norm_nonneg a)
        (fun i => NonUnitalStarAlgHom.norm_apply_le ((P i).integratedFull μ) a) := by
  ext x i
  simpa only [lp.mapCLM_apply_coe] using integratedFull_hilbertSum_apply P μ a x i

end TauCeti.CStarAction.CovariantRepresentation
