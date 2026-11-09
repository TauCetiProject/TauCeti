/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Nondegenerate

/-!
# Recovering covariant pairs and their intertwiners from integrated forms

Let `(π, U)` be a covariant representation of a point-norm continuous action `α` of `G` on a
possibly nonunital C⋆-algebra `A`, and let `π ⋊ U` be its integrated form on `C_c(G, A)` with
respect to a left-invariant measure. The integrated form turns the canonical left multipliers of
the convolution algebra into the operators of the pair:

`(π ⋊ U)(a • f) = π(a) (π ⋊ U)(f)` and `(π ⋊ U)(r • f) = U_r (π ⋊ U)(f)`,

where `(a • f) s = a * f s` and `(r • f) s = α r (f (r⁻¹ * s))` is `CStarAction.translate`;
these are `integratedOperator_smul` and `integratedOperator_translate`. When `π` is
nondegenerate the vectors `(π ⋊ U)(f) v` span a dense subspace, so these formulas determine
`π(a)` and `U_r` from the integrated form. Consequently:

* a covariant pair with nondegenerate coefficient representation is determined by its integrated
  form, `CovariantRepresentation.ext_integratedOperator`;
* a bounded operator intertwines two covariant pairs exactly when it intertwines their integrated
  forms, provided the source pair is nondegenerate, `comp_integratedOperator_iff`; the forward
  implication `comp_integratedOperator` needs no nondegeneracy. In particular a unitary
  equivalence of covariant pairs is the same as a unitary equivalence of their integrated forms;
* the commutant of the integrated form is the commutant of the pair,
  `centralizer_range_integratedOperator`, so the pair is irreducible exactly when its integrated
  form is.

No unit in `A`, separability, second countability or σ-finiteness is assumed. Density of the
integrated ranges uses local compactness, the R₁ axiom and positivity of the measure on nonempty
open sets, as in `dense_span_integratedOperator_iff`.

## References

Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2, for the formulas expressing a
covariant pair through its integrated form and the resulting correspondence of intertwiners.
-/

public section

noncomputable section

open MeasureTheory
open scoped CompactlySupported

namespace TauCeti.CStarAction.CovariantRepresentation

variable {G A H K : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [OpensMeasurableSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {α : CStarAction G A} (P : CovariantRepresentation α H) (μ : Measure G)
  [IsFiniteMeasureOnCompacts μ]

variable {P} {Q : CovariantRepresentation α K}

/-- An operator intertwining two covariant pairs intertwines their integrated forms. -/
theorem comp_integratedOperator {T : H →L[ℂ] K}
    (hπ : ∀ a, T ∘L P.coefficient a = Q.coefficient a ∘L T)
    (hU : ∀ g, T ∘L P.group g = Q.group g ∘L T) (f : C_c(G, A)) :
    T ∘L P.integratedOperator μ f = Q.integratedOperator μ f ∘L T := by
  ext v
  simp only [ContinuousLinearMap.comp_apply, integratedOperator_apply]
  rw [← T.integral_comp_comm (P.integrable_integrand μ f v)]
  congr 1 with g
  rw [← ContinuousLinearMap.comp_apply T, hπ, ContinuousLinearMap.comp_apply,
    ← ContinuousLinearMap.comp_apply T, hU, ContinuousLinearMap.comp_apply]

variable [IsTopologicalGroup G] [LocallyCompactSpace G] [R1Space G] [MeasurableMul G]
  [μ.IsMulLeftInvariant]
  [μ.IsOpenPosMeasure]

/-- If the source pair has a nondegenerate coefficient representation, an operator intertwines
two covariant pairs exactly when it intertwines their integrated forms. -/
theorem comp_integratedOperator_iff (hP : P.coefficient.IsNondegenerate) {T : H →L[ℂ] K} :
    (∀ f, T ∘L P.integratedOperator μ f = Q.integratedOperator μ f ∘L T) ↔
      (∀ a, T ∘L P.coefficient a = Q.coefficient a ∘L T) ∧
        ∀ g, T ∘L P.group g = Q.group g ∘L T := by
  refine ⟨fun h => ?_, fun h f => comp_integratedOperator μ h.1 h.2 f⟩
  have hd := (P.dense_span_integratedOperator_iff μ).2 hP
  -- An operator realized on both sides by the same multiplier `F` of `C_c(G, A)` is intertwined
  -- on the vectors `(π ⋊ U)(f) v`, which span a dense subspace.
  have key {S : H →L[ℂ] H} {S' : K →L[ℂ] K} (F : C_c(G, A) → C_c(G, A))
      (hS : ∀ f, P.integratedOperator μ (F f) = S * P.integratedOperator μ f)
      (hS' : ∀ f, Q.integratedOperator μ (F f) = S' * Q.integratedOperator μ f) :
      T ∘L S = S' ∘L T := by
    refine ContinuousLinearMap.ext_on hd fun x hx => ?_
    obtain ⟨f, v, rfl⟩ := Set.mem_iUnion.1 hx
    have h₁ := congr($(h (F f)) v)
    have h₂ := congr($(h f) v)
    simp only [ContinuousLinearMap.comp_apply] at h₁ h₂ ⊢
    rw [← mul_apply_eq_comp, ← hS, h₁, hS', mul_apply_eq_comp, ← h₂]
  exact ⟨fun a => key (a • ·) (P.integratedOperator_smul μ a) (Q.integratedOperator_smul μ a),
    fun g => key (α.translate g) (P.integratedOperator_translate μ g)
      (Q.integratedOperator_translate μ g)⟩

/-- A covariant pair with nondegenerate coefficient representation is determined by its
integrated form. -/
theorem ext_integratedOperator {P Q : CovariantRepresentation α H}
    (hP : P.coefficient.IsNondegenerate)
    (h : ∀ f, P.integratedOperator μ f = Q.integratedOperator μ f) : P = Q := by
  obtain ⟨hπ, hU⟩ := (comp_integratedOperator_iff μ hP (Q := Q)
    (T := ContinuousLinearMap.id ℂ H)).1 fun f => by simp [h]
  ext1
  · ext a v
    simpa using congr($(hπ a) v)
  · exact DFunLike.ext _ _ fun g => by simpa using hU g

/-- If the coefficient representation is nondegenerate, the commutant of the integrated form is
the commutant of the covariant pair. In particular the pair is irreducible exactly when its
integrated form is. -/
theorem centralizer_range_integratedOperator (hP : P.coefficient.IsNondegenerate) :
    Set.centralizer (Set.range (P.integratedOperator μ)) =
      Set.centralizer (Set.range P.coefficient ∪ Set.range P.group) := by
  ext T
  have := comp_integratedOperator_iff μ hP (Q := P) (T := T)
  simp only [← ContinuousLinearMap.mul_def] at this
  simp only [Set.mem_centralizer_iff, Set.mem_union, or_imp, forall_and, Set.forall_mem_range]
  simpa only [eq_comm (a := T * _)] using this

end TauCeti.CStarAction.CovariantRepresentation
