/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.RegularLocalRing.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# Regular systems of parameters adapted to a regular quotient

For a regular local ring with regular quotient by an arbitrary ideal, construct a minimal
generating family of the maximal ideal whose initial segment generates that ideal.
The construction selects one parameter in the ideal, takes its quotient, and inducts on the
embedding dimension. The zero ideal is handled by a minimal finite generating set.

## Main results

* `TauCeti.IsRegularLocalRing.exists_mem_notMem_maximalIdeal_sq_of_quotient`: a nonzero ideal
  with regular local quotient contains an element outside the square of the maximal ideal.
* `TauCeti.IsRegularLocalRing.exists_regularSystem_of_quotient`: the full generating family,
  including the zero-ideal and zero-dimensional cases.

## References

* [Stacks Project, Lemma 10.106.4](https://stacks.math.columbia.edu/tag/00NR).

This is a new formalization of the arbitrary-ideal statement, not a port of an existing proof.
-/

public section

open IsLocalRing Ideal Pointwise IsRegularLocalRing

universe u

namespace TauCeti.IsRegularLocalRing

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- A nonzero ideal of a regular local ring with regular quotient contains a parameter. -/
theorem exists_mem_notMem_maximalIdeal_sq_of_quotient (ideal : Ideal R)
    [IsRegularLocalRing (R ⧸ ideal)] (hne : ideal ≠ ⊥) :
    ∃ parameter ∈ ideal, parameter ∉ maximalIdeal R ^ 2 := by
  by_contra! hall
  have hemb := TauCeti.IsLocalRing.spanFinrank_map_maximalIdeal_quotient_of_le_sq
    (maximalIdeal R).fg_of_isNoetherianRing hall
  rw [map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective] at hemb
  obtain ⟨element, hmem, hzero⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hle : span {element} ≤ ideal := (span_singleton_le_iff_mem _).mpr hmem
  have hdim := ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle)
    (Ideal.Quotient.factor_surjective hle)
  have hdrop := ringKrullDim_quotient_succ_le_of_nonZeroDivisor
    (mem_nonZeroDivisors_of_ne_zero hzero)
  have hbad := (add_le_add hdim (le_refl 1)).trans hdrop
  rw [← spanFinrank_maximalIdeal (R := R ⧸ ideal),
    ← spanFinrank_maximalIdeal (R := R), hemb] at hbad
  exact absurd hbad (by norm_cast; omega)

omit [IsRegularLocalRing R] in
private lemma span_insert_eq_of_quotient (ideal : Ideal R) {parameter : R}
    (hmem : parameter ∈ ideal) (generators : Set R)
    (himage : span ((Ideal.Quotient.mk (span {parameter})) '' generators) =
      ideal.map (Ideal.Quotient.mk (span {parameter}))) :
    span (insert parameter generators) = ideal := by
  have hmap : (span (insert parameter generators)).map (Ideal.Quotient.mk (span {parameter})) =
      ideal.map (Ideal.Quotient.mk (span {parameter})) := by
    rw [map_span, Set.image_insert_eq, Ideal.Quotient.eq_zero_iff_mem.mpr
      (mem_span_singleton_self parameter), span_insert_zero, himage]
  have heq := (map_eq_iff_sup_ker_eq_of_surjective _ Ideal.Quotient.mk_surjective).mp hmap
  rw [Ideal.mk_ker, sup_of_le_left (span_mono (Set.singleton_subset_iff.mpr
    (Set.mem_insert parameter generators))), sup_of_le_left
      ((span_singleton_le_iff_mem _).mpr hmem)] at heq
  exact heq

omit [CommRing R] [IsRegularLocalRing R] in
private lemma image_cons_initial {size count : ℕ} (parameter : R) (generators : Fin size → R) :
    Fin.cons parameter generators '' {index | (index : ℕ) < count + 1} =
      insert parameter (generators '' {index | (index : ℕ) < count}) := by
  ext element
  simp [Set.mem_image, Fin.exists_fin_succ, eq_comm]

private theorem exists_regularSystem_aux (dimension : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R],
    (maximalIdeal R).spanFinrank = dimension →
    ∀ (ideal : Ideal R) [IsRegularLocalRing (R ⧸ ideal)],
    ∃ size count : ℕ, ∃ generators : Fin size → R,
      count ≤ size ∧ span (Set.range generators) = maximalIdeal R ∧
      (maximalIdeal R).spanFinrank = size ∧
      ideal = span (generators '' {index | (index : ℕ) < count}) := by
  classical
  induction dimension using Nat.strong_induction_on with
  | h dimension induction =>
    intro R _ _ hdimension ideal _
    by_cases hzero : ideal = ⊥
    · obtain ⟨generators, hcard, hspan⟩ :=
        Submodule.FG.exists_span_finset_card_eq_spanFinrank
          (maximalIdeal R).fg_of_isNoetherianRing
      refine ⟨generators.card, 0, fun index ↦ (generators.equivFin.symm index).val,
        Nat.zero_le _, ?_, hcard.symm, ?_⟩
      · have hrange : Set.range (fun index ↦ (generators.equivFin.symm index).val) =
            (generators : Set R) := by
          ext element
          simp only [Set.mem_range, Finset.mem_coe]
          exact ⟨fun ⟨index, heq⟩ ↦ heq ▸ (generators.equivFin.symm index).property,
            fun hmem ↦ ⟨generators.equivFin ⟨element, hmem⟩, by simp⟩⟩
        rw [hrange]
        exact hspan
      · simp [hzero]
    obtain ⟨parameter, hmem, hsquare⟩ := exists_mem_notMem_maximalIdeal_sq_of_quotient ideal hzero
    have hmax : parameter ∈ maximalIdeal R :=
      le_maximalIdeal (Ideal.Quotient.nontrivial_iff.mp inferInstance) hmem
    have hparameter : parameter ≠ 0 := fun heq ↦ hsquare (heq ▸ (zero_mem _))
    let quotient := R ⧸ span {parameter}
    let quotientMap := Ideal.Quotient.mk (span {parameter})
    have : IsRegularLocalRing quotient := quotient_span_singleton hmax hsquare
    have hle : span {parameter} ≤ ideal := (span_singleton_le_iff_mem _).mpr hmem
    have : IsRegularLocalRing (quotient ⧸ ideal.map quotientMap) :=
      .of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hle).symm
    have hdrop : (maximalIdeal quotient).spanFinrank + 1 =
        (maximalIdeal R).spanFinrank := by
      have hdim := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero hparameter) hmax
      rw [← spanFinrank_maximalIdeal (R := quotient),
        ← spanFinrank_maximalIdeal (R := R)] at hdim
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
    · rw [image_cons_initial]
      symm
      apply span_insert_eq_of_quotient _ hmem
      rw [← Set.image_comp, hcomp, ← hideal]

/-- A regular quotient is cut out by an initial segment of a regular system of parameters.
The family has exactly the embedding dimension many entries and generates the maximal ideal.
No dimension or generating-family hypothesis is imposed on the ideal. -/
@[stacks 00NR]
theorem exists_regularSystem_of_quotient (ideal : Ideal R)
    [IsRegularLocalRing (R ⧸ ideal)] :
    ∃ size count : ℕ, ∃ generators : Fin size → R,
      count ≤ size ∧ span (Set.range generators) = maximalIdeal R ∧
      (maximalIdeal R).spanFinrank = size ∧
      ideal = span (generators '' {index | (index : ℕ) < count}) :=
  exists_regularSystem_aux _ R rfl ideal

end TauCeti.IsRegularLocalRing
