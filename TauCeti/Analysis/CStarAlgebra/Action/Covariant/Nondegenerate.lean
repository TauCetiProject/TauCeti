/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Integrated
public import TauCeti.Analysis.CStarAlgebra.Representation.Nondegenerate
import TauCeti.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.UrysohnsLemma

/-!
# Nondegeneracy of integrated covariant representations

The integrated form of a covariant pair generates the same closed subspace as its coefficient
representation. In particular, its ranges span a dense subspace exactly when the coefficient
representation is nondegenerate. This identifies the nondegenerate representations on the two
sides of the integrated-form correspondence, without assuming unital coefficients.

The proof tests matrix coefficients against compactly supported continuous scalar functions.
Only local compactness, the R₁ separation axiom, finiteness of the measure on compact sets and
positivity on nonempty open sets are needed; Haar invariance is not required.

## References

Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2.
The vector integral is `CovariantRepresentation.integratedOperator`; localization uses Mathlib's
compact-support Urysohn lemma and Tau Ceti's continuous square-integral vanishing criterion.
-/

public section

noncomputable section

open MeasureTheory
open scoped CompactlySupported InnerProductSpace

namespace TauCeti.CStarAction.CovariantRepresentation

variable {G A H : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [OpensMeasurableSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} (P : CovariantRepresentation α H)
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
  [LocallyCompactSpace G] [R1Space G] [μ.IsOpenPosMeasure]

/-- A vector is orthogonal to every integrated range exactly when it is orthogonal to every
coefficient range. -/
theorem forall_inner_integratedOperator_eq_zero_iff (w : H) :
    (∀ (f : C_c(G, A)) (v : H), ⟪w, P.integratedOperator μ f v⟫_ℂ = 0) ↔
      ∀ (a : A) (v : H), ⟪w, P.coefficient a v⟫_ℂ = 0 := by
  constructor
  · intro h a v
    obtain ⟨b, hb, hbc, -, -⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen
      (K := ({1} : Set G)) (V := Set.univ) isCompact_singleton isOpen_univ (Set.subset_univ _)
    have hbcs : HasCompactSupport b := hbc
    let ψ : G → ℂ := fun g => ⟪w, P.coefficient a (P.group g v)⟫_ℂ
    have hψ : Continuous ψ := by
      exact continuous_const.inner ((P.coefficient a).continuous.comp (P.continuous_orbit v))
    let χ : C_c(G, ℂ) :=
      ⟨⟨fun g => (b g : ℂ) * ψ g, (Complex.continuous_ofReal.comp b.continuous).mul hψ⟩,
        (hbcs.comp_left Complex.ofReal_zero).mul_right⟩
    let f : C_c(G, A) :=
      ⟨⟨fun g => (star (χ g) * (b g : ℂ)) • a, by fun_prop⟩,
        (star χ).hasCompactSupport.mul_right.smul_right⟩
    -- This coefficient test turns the vanishing matrix coefficient into the squared norm of χ.
    have hχ : ∫ g, starRingEnd ℂ (χ g) * χ g ∂μ = 0 := by
      simpa only [inner_integratedOperator_apply, f, χ, ψ,
        CompactlySupportedContinuousMap.coe_mk, ContinuousMap.coe_mk, map_smul,
        smul_apply, inner_smul_right, mul_assoc, starRingEnd_apply] using h f v
    have hz := χ.continuous.eq_zero_of_integral_conj_mul_self_eq_zero
      (χ.continuous.memLp_of_hasCompactSupport χ.hasCompactSupport) hχ
    have hb1 : b 1 = 1 := hb (Set.mem_singleton 1)
    simpa [χ, ψ, hb1] using congrFun hz 1
  · intro h f v
    rw [P.inner_integratedOperator_apply]
    exact integral_eq_zero_of_ae (.of_forall fun g => h (f g) (P.group g v))

/-- The orthogonal complements of the spans of the integrated and coefficient ranges coincide.
This includes degenerate coefficient representations. -/
theorem orthogonal_span_integratedOperator :
    (Submodule.span ℂ (⋃ f : C_c(G, A), Set.range (P.integratedOperator μ f)))ᗮ =
      (Submodule.span ℂ (⋃ a : A, Set.range (P.coefficient a)))ᗮ := by
  ext w
  -- Orthogonality to a span is containment of that span in the kernel of the inner product.
  have hspan (s : Set H) :
      w ∈ (Submodule.span ℂ s)ᗮ ↔ ∀ x ∈ s, ⟪w, x⟫_ℂ = 0 := by
    rw [Submodule.mem_orthogonal']
    exact Submodule.span_le (p := (innerSL ℂ w).ker)
  simp only [hspan, Set.forall_mem_iUnion, Set.forall_mem_range]
  exact P.forall_inner_integratedOperator_eq_zero_iff μ w

/-- The integrated form generates precisely the closed essential subspace of the coefficient
representation. -/
theorem topologicalClosure_span_integratedOperator :
    (Submodule.span ℂ (⋃ f : C_c(G, A), Set.range (P.integratedOperator μ f))).topologicalClosure =
      (Submodule.span ℂ (⋃ a : A, Set.range (P.coefficient a))).topologicalClosure := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure,
    ← Submodule.orthogonal_orthogonal_eq_closure, P.orthogonal_span_integratedOperator μ]

/-- Nondegeneracy is preserved and reflected by the integrated form on compactly supported
continuous coefficient functions. -/
theorem dense_span_integratedOperator_iff :
    Dense (Submodule.span ℂ (⋃ f : C_c(G, A), Set.range (P.integratedOperator μ f)) : Set H) ↔
      P.coefficient.IsNondegenerate := by
  rw [NonUnitalStarAlgHom.isNondegenerate_iff_dense,
    Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.dense_iff_topologicalClosure_eq_top, P.topologicalClosure_span_integratedOperator μ]

end TauCeti.CStarAction.CovariantRepresentation
