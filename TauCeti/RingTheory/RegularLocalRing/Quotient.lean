/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.RegularLocalRing.Basic
import TauCeti.RingTheory.Ideal.Quotient.Operations
import TauCeti.Data.Fin.Tuple.Basic
import TauCeti.Algebra.Module.SpanRank

/-!
# Regular systems of parameters adapted to a regular quotient

For a regular local ring with regular quotient by an arbitrary ideal, construct a minimal
generating family of the maximal ideal whose initial segment generates that ideal.
This gives local equations for a regular quotient as part of a minimal system of parameters,
including the zero ideal and zero-dimensional cases.

## Main results

* `Ideal.exists_regularSystem_of_quotient`: the full generating family,
  including the zero-ideal and zero-dimensional cases.

The parameter-selection input is `Ideal.exists_mem_notMem_maximalIdeal_sq_of_quotient` in
`TauCeti.RingTheory.RegularLocalRing.Basic`.

## References

* [Stacks Project, Lemma 10.106.4](https://stacks.math.columbia.edu/tag/00NR).
-/

public section

open IsLocalRing Ideal Pointwise IsRegularLocalRing

universe u

namespace Ideal

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

private theorem exists_regularSystem_aux (dimension : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R],
    (maximalIdeal R).spanFinrank = dimension →
    ∀ (I : Ideal R) [IsRegularLocalRing (R ⧸ I)],
    ∃ size count : ℕ, ∃ generators : Fin size → R,
      count ≤ size ∧ span (Set.range generators) = maximalIdeal R ∧
      (maximalIdeal R).spanFinrank = size ∧
      I = span (generators '' {index | (index : ℕ) < count}) := by
  classical
  induction dimension using Nat.strong_induction_on with
  | h dimension induction =>
    intro R _ _ hdimension I _
    by_cases hzero : I = ⊥
    · obtain ⟨generators, hspan⟩ :=
        (Submodule.FG.spanFinrank_le_iff_exists_fin_generating_family
          (maximalIdeal R).fg_of_isNoetherianRing _).mp le_rfl
      exact ⟨_, 0, generators, Nat.zero_le _, hspan, rfl, by simp [hzero]⟩
    obtain ⟨parameter, hmem, hsquare⟩ := exists_mem_notMem_maximalIdeal_sq_of_quotient I hzero
    have hmax : parameter ∈ maximalIdeal R :=
      le_maximalIdeal (Ideal.Quotient.nontrivial_iff.mp inferInstance) hmem
    have hparameter : parameter ≠ 0 := fun heq ↦ hsquare (heq ▸ (zero_mem _))
    let quotient := R ⧸ span {parameter}
    let quotientMap := Ideal.Quotient.mk (span {parameter})
    have : IsRegularLocalRing quotient :=
      TauCeti.IsRegularLocalRing.quotient_span_singleton hmax hsquare
    have hle : span {parameter} ≤ I := (span_singleton_le_iff_mem _).mpr hmem
    have : IsRegularLocalRing (quotient ⧸ I.map quotientMap) :=
      .of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hle).symm
    have hdrop : (maximalIdeal quotient).spanFinrank + 1 = (maximalIdeal R).spanFinrank :=
      TauCeti.IsRegularLocalRing.spanFinrank_maximalIdeal_quotient_span_singleton_add_one hmax
        hparameter
    obtain ⟨size, count, generators, hcount, hspan, hsize, hideal⟩ :=
      induction (maximalIdeal quotient).spanFinrank (by omega) quotient rfl
        (I.map quotientMap)
    choose lifts hlifts using fun index ↦ Ideal.Quotient.mk_surjective (generators index)
    have hcomp : quotientMap ∘ lifts = generators := funext hlifts
    refine ⟨size + 1, count + 1, Fin.cons parameter lifts, Nat.add_le_add_right hcount 1,
      ?_, by omega, ?_⟩
    · rw [Fin.range_cons]
      apply span_insert_eq_of_quotient _ hmax
      rw [← Set.range_comp, hcomp, hspan]
      exact (map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective).symm
    · simp only [Order.lt_add_one_iff, Fin.image_cons_le_eq_insert]
      symm
      apply span_insert_eq_of_quotient _ hmem
      rw [← Set.image_comp, hcomp, ← hideal]

/-- A regular quotient is cut out by an initial segment of a regular system of parameters.
The family has exactly the embedding dimension many entries and generates the maximal ideal.
No dimension or generating-family hypothesis is imposed on the ideal. -/
@[stacks 00NR]
theorem exists_regularSystem_of_quotient (I : Ideal R)
    [IsRegularLocalRing (R ⧸ I)] :
    ∃ size count : ℕ, ∃ generators : Fin size → R,
      count ≤ size ∧ span (Set.range generators) = maximalIdeal R ∧
      (maximalIdeal R).spanFinrank = size ∧
      I = span (generators '' {index | (index : ℕ) < count}) :=
  exists_regularSystem_aux _ R rfl I

end Ideal
