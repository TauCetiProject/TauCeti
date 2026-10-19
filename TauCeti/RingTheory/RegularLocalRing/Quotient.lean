/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.RegularLocalRing.Basic
import TauCeti.RingTheory.Ideal.Maps
import TauCeti.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# Regular systems of parameters adapted to a regular quotient

For a regular local ring with regular quotient by an arbitrary ideal, construct a minimal
generating family of the maximal ideal whose initial segment generates that ideal.
This gives local equations for a regular quotient as part of a minimal system of parameters,
including the zero ideal and zero-dimensional cases.

## Main results

* `Ideal.exists_mem_notMem_maximalIdeal_sq_of_quotient`: a nonzero ideal
  with regular local quotient contains an element outside the square of the maximal ideal.
* `Ideal.exists_regularSystem_of_quotient`: the full generating family,
  including the zero-ideal and zero-dimensional cases.

## References

* [Stacks Project, Lemma 10.106.4](https://stacks.math.columbia.edu/tag/00NR).
-/

public section

open IsLocalRing Ideal Pointwise IsRegularLocalRing

universe universeLevel

namespace Ideal

variable {ring : Type universeLevel} [CommRing ring] [IsRegularLocalRing ring]

/-- A nonzero ideal of a regular local ring with regular quotient contains a parameter. -/
theorem exists_mem_notMem_maximalIdeal_sq_of_quotient (ideal : Ideal ring)
    [IsRegularLocalRing (ring ⧸ ideal)] (hne : ideal ≠ ⊥) :
    ∃ parameter ∈ ideal, parameter ∉ maximalIdeal ring ^ 2 := by
  by_contra! hall
  have hemb := TauCeti.IsLocalRing.spanFinrank_map_maximalIdeal_quotient_of_le_sq
    (maximalIdeal ring).fg_of_isNoetherianRing hall
  rw [map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective] at hemb
  obtain ⟨element, hmem, hzero⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hle : span {element} ≤ ideal := (span_singleton_le_iff_mem _).mpr hmem
  have hdim := ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle)
    (Ideal.Quotient.factor_surjective hle)
  have hdrop := ringKrullDim_quotient_succ_le_of_nonZeroDivisor
    (mem_nonZeroDivisors_of_ne_zero hzero)
  have hbad := (add_le_add hdim (le_refl 1)).trans hdrop
  rw [← spanFinrank_maximalIdeal (R := ring ⧸ ideal),
    ← spanFinrank_maximalIdeal (R := ring), hemb] at hbad
  exact absurd hbad (by norm_cast; omega)

private theorem exists_regularSystem_aux (dimension : ℕ) :
    ∀ (ring : Type universeLevel) [CommRing ring] [IsRegularLocalRing ring],
    (maximalIdeal ring).spanFinrank = dimension →
    ∀ (ideal : Ideal ring) [IsRegularLocalRing (ring ⧸ ideal)],
    ∃ size count : ℕ, ∃ generators : Fin size → ring,
      count ≤ size ∧ span (Set.range generators) = maximalIdeal ring ∧
      (maximalIdeal ring).spanFinrank = size ∧
      ideal = span (generators '' {index | (index : ℕ) < count}) := by
  classical
  induction dimension using Nat.strong_induction_on with
  | h dimension induction =>
    intro ring _ _ hdimension ideal _
    by_cases hzero : ideal = ⊥
    · obtain ⟨generators, hcard, hspan⟩ :=
        Submodule.FG.exists_span_finset_card_eq_spanFinrank
          (maximalIdeal ring).fg_of_isNoetherianRing
      refine ⟨generators.card, 0, fun index ↦ (generators.equivFin.symm index).val,
        Nat.zero_le _, ?_, hcard.symm, ?_⟩
      · have hrange : Set.range (fun index ↦ (generators.equivFin.symm index).val) =
            (generators : Set ring) := by
          ext element
          simp only [Set.mem_range, Finset.mem_coe]
          exact ⟨fun ⟨index, heq⟩ ↦ heq ▸ (generators.equivFin.symm index).property,
            fun hmem ↦ ⟨generators.equivFin ⟨element, hmem⟩, by simp⟩⟩
        rw [hrange]
        exact hspan
      · simp [hzero]
    obtain ⟨parameter, hmem, hsquare⟩ := exists_mem_notMem_maximalIdeal_sq_of_quotient ideal hzero
    have hmax : parameter ∈ maximalIdeal ring :=
      le_maximalIdeal (Ideal.Quotient.nontrivial_iff.mp inferInstance) hmem
    have hparameter : parameter ≠ 0 := fun heq ↦ hsquare (heq ▸ (zero_mem _))
    let quotient := ring ⧸ span {parameter}
    let quotientMap := Ideal.Quotient.mk (span {parameter})
    have : IsRegularLocalRing quotient :=
      TauCeti.IsRegularLocalRing.quotient_span_singleton hmax hsquare
    have hle : span {parameter} ≤ ideal := (span_singleton_le_iff_mem _).mpr hmem
    have : IsRegularLocalRing (quotient ⧸ ideal.map quotientMap) :=
      .of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hle).symm
    have hdrop : (maximalIdeal quotient).spanFinrank + 1 =
        (maximalIdeal ring).spanFinrank := by
      have hdim := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero hparameter) hmax
      rw [← spanFinrank_maximalIdeal (R := quotient),
        ← spanFinrank_maximalIdeal (R := ring)] at hdim
      exact_mod_cast hdim
    obtain ⟨size, count, generators, hcount, hspan, hsize, hideal⟩ :=
      induction (maximalIdeal quotient).spanFinrank (by omega) quotient rfl
        (ideal.map quotientMap)
    choose lifts hlifts using fun index ↦ Ideal.Quotient.mk_surjective (generators index)
    have hcomp : quotientMap ∘ lifts = generators := funext hlifts
    refine ⟨size + 1, count + 1, Fin.cons parameter lifts, Nat.add_le_add_right hcount 1,
      ?_, by omega, ?_⟩
    · rw [Fin.range_cons]
      apply span_insert_eq_of_quotient _ hmax
      rw [← Set.range_comp, hcomp, hspan]
      exact (map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective).symm
    · simp only [Order.lt_add_one_iff, Fin.image_cons_le]
      symm
      apply span_insert_eq_of_quotient _ hmem
      rw [← Set.image_comp, hcomp, ← hideal]

/-- A regular quotient is cut out by an initial segment of a regular system of parameters.
The family has exactly the embedding dimension many entries and generates the maximal ideal.
No dimension or generating-family hypothesis is imposed on the ideal. -/
@[stacks 00NR]
theorem exists_regularSystem_of_quotient (ideal : Ideal ring)
    [IsRegularLocalRing (ring ⧸ ideal)] :
    ∃ size count : ℕ, ∃ generators : Fin size → ring,
      count ≤ size ∧ span (Set.range generators) = maximalIdeal ring ∧
      (maximalIdeal ring).spanFinrank = size ∧
      ideal = span (generators '' {index | (index : ℕ) < count}) :=
  exists_regularSystem_aux _ ring rfl ideal

end Ideal
