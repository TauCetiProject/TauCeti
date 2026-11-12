/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.CrossedProduct.Full
public import TauCeti.Analysis.CStarAlgebra.Representation.Nondegenerate
import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Intertwiner

/-!
# Covariant representations and the full crossed product

The integrated representation of the full crossed product generates the same closed essential
subspace as its coefficient representation. Thus nondegeneracy is preserved and reflected by
integration. For a nondegenerate source pair, bounded intertwiners of the integrated
representations are exactly the simultaneous coefficient and group intertwiners. This also
identifies the commutants, and determines a nondegenerate covariant pair from its integrated
representation. Applying the intertwiner equivalence to a unitary operator gives compatibility
with unitary equivalence.

These results allow possibly nonunital coefficients and degenerate target representations;
no separability or global σ-finiteness is assumed. The Hilbert spaces lie in the universe used
to define the full crossed-product norm.

## References

Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2. We extend Tau Ceti's compact-support
results `topologicalClosure_span_integratedOperator`, `comp_integratedOperator_iff` and
`ext_integratedOperator` along the dense map `FullCrossedProduct.of`, using the characteristic
equation `CovariantRepresentation.integratedFull_of`.
-/

public section

noncomputable section

open MeasureTheory
open scoped CompactlySupported CStarAlgebra

namespace TauCeti.CStarAction.CovariantRepresentation

universe u v

variable {G : Type u} {A : Type v} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NonUnitalCStarAlgebra A] {α : CStarAction G A} (μ : Measure G) [μ.IsHaarMeasure]
  {H K : Type (max u v)} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (P : CovariantRepresentation α H)

/-- Completing the integrated form preserves its closed essential subspace, which is the
closed essential subspace of the coefficient representation, even for a degenerate pair. -/
theorem topologicalClosure_span_integratedFull :
    (Submodule.span ℂ (⋃ x : FullCrossedProduct α μ,
      Set.range (P.integratedFull μ x))).topologicalClosure =
      (Submodule.span ℂ (⋃ a : A, Set.range (P.coefficient a))).topologicalClosure := by
  rw [← P.topologicalClosure_span_integratedOperator μ]
  apply le_antisymm
  · refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_)
      (Submodule.isClosed_topologicalClosure _)
    intro y hy
    obtain ⟨x, v, rfl⟩ := Set.mem_iUnion.1 hy
    clear hy
    induction x using FullCrossedProduct.induction_on with
    | hp =>
      exact (Submodule.isClosed_topologicalClosure
        (Submodule.span ℂ (⋃ f : C_c(G, A), Set.range (P.integratedOperator μ f)))).preimage
        (f := fun x : FullCrossedProduct α μ => P.integratedFull μ x v) (by fun_prop)
    | ih f =>
      rw [integratedFull_of, integratedStarAlgHom_apply]
      exact Submodule.le_topologicalClosure _
        (Submodule.subset_span (Set.mem_iUnion.2 ⟨f.ofConv, v, rfl⟩))
  · apply Submodule.topologicalClosure_mono
    refine Submodule.span_le.2 ?_
    intro y hy
    obtain ⟨f, v, rfl⟩ := Set.mem_iUnion.1 hy
    have h := Submodule.subset_span (R := ℂ)
      (s := ⋃ x : FullCrossedProduct α μ, Set.range (P.integratedFull μ x))
      (Set.mem_iUnion.2 ⟨FullCrossedProduct.of α μ (ConvolutionAlgebra.toConv f), v, rfl⟩)
    simpa only [integratedFull_of, integratedStarAlgHom_apply,
      ConvolutionAlgebra.ofConv_toConv] using h

/-- The integrated representation of the full crossed product is nondegenerate exactly when
the coefficient representation is nondegenerate. -/
@[simp]
theorem isNondegenerate_integratedFull_iff :
    (P.integratedFull μ).IsNondegenerate ↔ P.coefficient.IsNondegenerate := by
  rw [NonUnitalStarAlgHom.isNondegenerate_iff_dense,
    NonUnitalStarAlgHom.isNondegenerate_iff_dense,
    Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.dense_iff_topologicalClosure_eq_top, P.topologicalClosure_span_integratedFull μ]

variable {P} {Q : CovariantRepresentation α K}

/-- A bounded operator intertwining the coefficient and group representations intertwines
their representations of the full crossed product, without nondegeneracy assumptions. -/
theorem comp_integratedFull {T : H →L[ℂ] K}
    (hπ : ∀ a, T ∘L P.coefficient a = Q.coefficient a ∘L T)
    (hU : ∀ g, T ∘L P.group g = Q.group g ∘L T) (x : FullCrossedProduct α μ) :
    T ∘L P.integratedFull μ x = Q.integratedFull μ x ∘L T := by
  induction x using FullCrossedProduct.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih f =>
    simpa only [integratedFull_of, integratedStarAlgHom_apply] using
      comp_integratedOperator μ hπ hU f.ofConv

/-- For a nondegenerate source pair, bounded intertwiners of the full crossed-product
representations are precisely the simultaneous coefficient and group intertwiners. In
particular this applies to unitary equivalences of representations. -/
theorem comp_integratedFull_iff (hP : P.coefficient.IsNondegenerate) {T : H →L[ℂ] K} :
    (∀ x, T ∘L P.integratedFull μ x = Q.integratedFull μ x ∘L T) ↔
      (∀ a, T ∘L P.coefficient a = Q.coefficient a ∘L T) ∧
        ∀ g, T ∘L P.group g = Q.group g ∘L T := by
  refine ⟨fun h => (comp_integratedOperator_iff μ hP).1 fun f => ?_,
    fun h => comp_integratedFull μ h.1 h.2⟩
  simpa only [integratedFull_of, integratedStarAlgHom_apply,
    ConvolutionAlgebra.ofConv_toConv] using
    h (FullCrossedProduct.of α μ (ConvolutionAlgebra.toConv f))

/-- A covariant pair with nondegenerate coefficient representation is determined by its
representation of the full crossed product. -/
theorem ext_integratedFull {P Q : CovariantRepresentation α H}
    (hP : P.coefficient.IsNondegenerate) (h : P.integratedFull μ = Q.integratedFull μ) :
    P = Q := by
  apply ext_integratedOperator μ hP
  intro f
  have hf := DFunLike.congr_fun h
    (FullCrossedProduct.of α μ (ConvolutionAlgebra.toConv f))
  simpa only [integratedFull_of, integratedStarAlgHom_apply,
    ConvolutionAlgebra.ofConv_toConv] using hf

/-- For a nondegenerate coefficient representation, the commutant of the integrated full
crossed-product representation equals the simultaneous coefficient and group commutant.
Consequently the integrated representation and the pair have the same scalar-commutant
criterion for irreducibility. -/
theorem centralizer_range_integratedFull (hP : P.coefficient.IsNondegenerate) :
    Set.centralizer (Set.range (P.integratedFull μ)) =
      Set.centralizer (Set.range P.coefficient ∪ Set.range P.group) := by
  ext T
  have h := comp_integratedFull_iff μ hP (Q := P) (T := T)
  simp only [← ContinuousLinearMap.mul_def] at h
  simp only [Set.mem_centralizer_iff, Set.mem_union, or_imp, forall_and, Set.forall_mem_range]
  simpa only [eq_comm (a := T * _)] using h

end TauCeti.CStarAction.CovariantRepresentation
