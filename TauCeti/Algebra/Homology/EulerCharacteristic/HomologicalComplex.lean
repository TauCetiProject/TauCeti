/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.EulerCharacteristic
public import TauCeti.Algebra.Category.ModuleCat.Finrank
public import TauCeti.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Euler--Poincaré for homological complexes of arbitrary shape

Mathlib defines `HomologicalComplex.eulerChar` and `HomologicalComplex.homologyEulerChar` for a
complex `K : HomologicalComplex (ModuleCat R) c` of any shape `c : ComplexShape ι` equipped with
alternating signs `[c.EulerCharSigns]`. Existing files establish Euler--Poincaré for chain
complexes over a division ring indexed by `ℕ`
(`TauCeti.Algebra.Homology.EulerCharacteristic.ChainComplex`) and for bounded cochain complexes
indexed by `ℤ` over a Noetherian ring
(`TauCeti.Algebra.Homology.EulerCharacteristic.Finite`). Pages of a spectral sequence, however, are
complexes indexed by `ℤ × ℤ` whose differential direction changes from page to page.

This file proves the Euler--Poincaré identity for complexes of arbitrary shape `c` over any ring
`R` satisfying the strong rank condition and rank--nullity (`[StrongRankCondition R]` and
`[HasRankNullity R]`, covering division rings and commutative domains such as `ℤ`, with no
Noetherian assumption):

* `HomologicalComplex.finite_homology`: over any ring, if `K.X i` is a Noetherian `R`-module, then
  `K.homology i` is finitely generated.
* `HomologicalComplex.finrank_X_eq`: at any index `i` where `K.X i` is finitely generated,
  `finrank (K.X i)` equals `finrank (K.homology i)` plus the ranks of the incoming and outgoing
  boundary submodules.
* `HomologicalComplex.sum_finrank_X_eq_sum_finrank_homology`: on any finite set `s : Finset ι`
  whose boundary differentials into and out of `s` vanish, the signed sums of term finranks and
  homology finranks over `s` agree; the boundary ranks cancel pairwise across `s × s` via
  `c.χ_next`.
* `HomologicalComplex.eulerChar_eq_homologyEulerChar`: if every term `K.X i` is finitely generated
  and `K.X i` is nonzero for only finitely many indices `i`, then
  `K.eulerChar = K.homologyEulerChar`.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Sections 1.1 and 1.3.
* Jean-Pierre Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54
  (1951), 425--505, Chapter II, Section 4.
-/

public section

open CategoryTheory Limits Module

universe u v

namespace HomologicalComplex

section Finite

variable {R : Type u} [Ring R] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex (ModuleCat.{v} R) c)

/-- If the term `K.X i` of a homological complex of `R`-modules is a Noetherian module, then its
homology `K.homology i` is finitely generated. -/
theorem finite_homology (i : ι) [IsNoetherian R (K.X i)] :
    Module.Finite R (K.homology i) :=
  have : IsNoetherian R (K.sc i).X₂ := ‹IsNoetherian R (K.X i)›
  (K.sc i).finite_homology

/-- For an index `i`, if the incoming differential from `c.prev i` vanishes whenever
`c.prev i ∉ s`, then the rank of `im (K.d (c.prev i) i)` equals the sum over `j ∈ s` of the ranks
of `im (K.d j i)`. -/
private lemma finrank_range_d_prev_eq_sum [Nontrivial R] {s : Finset ι} {i : ι}
    (hprev : c.prev i ∉ s → K.d (c.prev i) i = 0) :
    finrank R (LinearMap.range (K.d (c.prev i) i).hom) =
      ∑ j ∈ s, finrank R (LinearMap.range (K.d j i).hom) := by
  symm
  refine Finset.sum_eq_single (c.prev i) (fun j _ hj ↦ ?_) (fun hmem ↦ ?_)
  · rw [K.shape j i (fun h ↦ hj (c.prev_eq' h).symm), ModuleCat.hom_zero, LinearMap.range_zero]
    exact finrank_zero_of_subsingleton
  · rw [hprev hmem, ModuleCat.hom_zero, LinearMap.range_zero]
    exact finrank_zero_of_subsingleton

/-- For an index `i`, if the outgoing differential to `c.next i` vanishes whenever
`c.next i ∉ s`, then the rank of `im (K.d i (c.next i))` equals the sum over `j ∈ s` of the ranks
of `im (K.d i j)`. -/
private lemma finrank_range_d_next_eq_sum [Nontrivial R] {s : Finset ι} {i : ι}
    (hnext : c.next i ∉ s → K.d i (c.next i) = 0) :
    finrank R (LinearMap.range (K.d i (c.next i)).hom) =
      ∑ j ∈ s, finrank R (LinearMap.range (K.d i j).hom) := by
  symm
  refine Finset.sum_eq_single (c.next i) (fun j _ hj ↦ ?_) (fun hmem ↦ ?_)
  · rw [K.shape i j (fun h ↦ hj (c.next_eq' h).symm), ModuleCat.hom_zero, LinearMap.range_zero]
    exact finrank_zero_of_subsingleton
  · rw [hnext hmem, ModuleCat.hom_zero, LinearMap.range_zero]
    exact finrank_zero_of_subsingleton

end Finite

section RankNullity

variable {R : Type u} [Ring R] [StrongRankCondition R] [HasRankNullity.{v} R]
  {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex (ModuleCat.{v} R) c)

/-- **Rank--nullity at one index of a homological complex.** Over a ring satisfying the strong rank
condition and rank--nullity, if `K.X i` is finitely generated, its rank is the rank of
`K.homology i` plus the ranks of the incoming and outgoing boundary submodules. -/
theorem finrank_X_eq (i : ι) [Module.Finite R (K.X i)] :
    finrank R (K.X i) = finrank R (K.homology i) +
      finrank R (LinearMap.range (K.d (c.prev i) i).hom) +
      finrank R (LinearMap.range (K.d i (c.next i)).hom) := by
  have : Module.Finite R (K.sc' (c.prev i) i (c.next i)).X₂ := ‹Module.Finite R (K.X i)›
  have hH : finrank R (K.sc' (c.prev i) i (c.next i)).homology +
      finrank R (LinearMap.range (K.d (c.prev i) i).hom) =
        finrank R (LinearMap.ker (K.d i (c.next i)).hom) :=
    (K.sc' (c.prev i) i (c.next i)).finrank_homology_add_finrank_range_f
  have e : K.homology i ≅ (K.sc' (c.prev i) i (c.next i)).homology :=
    ShortComplex.homologyMapIso (K.isoSc' (c.prev i) i (c.next i) rfl rfl)
  have hker := (LinearMap.ker (K.d i (c.next i)).hom).finrank_quotient_add_finrank
  rw [((K.d i (c.next i)).hom).quotKerEquivRange.finrank_eq] at hker
  rw [← e.toLinearEquiv.finrank_eq] at hH
  lia

variable [c.EulerCharSigns]

/-- **Euler--Poincaré on a finite index set.** Let `s : Finset ι` be a finite set of indices on
which the terms of `K` are finitely generated, and suppose that every differential entering `s` from
outside `s` or leaving `s` to outside `s` vanishes. Then the signed sums over `s` of the term
finranks and of the homology finranks agree. -/
theorem sum_finrank_X_eq_sum_finrank_homology (s : Finset ι)
    (hfin : ∀ i ∈ s, Module.Finite R (K.X i))
    (hprev : ∀ i ∈ s, c.prev i ∉ s → K.d (c.prev i) i = 0)
    (hnext : ∀ i ∈ s, c.next i ∉ s → K.d i (c.next i) = 0) :
    ∑ i ∈ s, (c.χ i : ℤ) * finrank R (K.X i) =
      ∑ i ∈ s, (c.χ i : ℤ) * finrank R (K.homology i) := by
  have hstep (i : ι) (hi : i ∈ s) :
      (c.χ i : ℤ) * finrank R (K.X i) = (c.χ i : ℤ) * finrank R (K.homology i) +
        ((∑ j ∈ s, (c.χ i : ℤ) * finrank R (LinearMap.range (K.d j i).hom)) +
          ∑ j ∈ s, (c.χ i : ℤ) * finrank R (LinearMap.range (K.d i j).hom)) := by
    have := hfin i hi
    rw [K.finrank_X_eq i, finrank_range_d_prev_eq_sum K (hprev i hi),
      finrank_range_d_next_eq_sum K (hnext i hi)]
    push_cast
    rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum, add_assoc]
  rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, Finset.sum_add_distrib]
  suffices hcancel :
      (∑ i ∈ s, ∑ j ∈ s, (c.χ i : ℤ) * finrank R (LinearMap.range (K.d j i).hom)) +
        (∑ i ∈ s, ∑ j ∈ s, (c.χ i : ℤ) * finrank R (LinearMap.range (K.d i j).hom)) = 0 by
    rw [hcancel, add_zero]
  rw [Finset.sum_comm (s := s) (t := s), ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  by_cases hrel : c.Rel i j
  · rw [c.χ_next hrel, Units.val_neg, neg_mul, neg_add_cancel]
  · rw [K.shape i j hrel, ModuleCat.hom_zero, LinearMap.range_zero, finrank_zero_of_subsingleton]
    simp

/-- If `K.X i` vanishes outside a finite set `s` and is finitely generated on `s`, then the signed
sums over `s` of the term finranks and of the homology finranks agree. -/
theorem sum_finrank_X_eq_sum_finrank_homology_of_isZero (s : Finset ι)
    (hfin : ∀ i ∈ s, Module.Finite R (K.X i)) (hzero : ∀ i ∉ s, IsZero (K.X i)) :
    ∑ i ∈ s, (c.χ i : ℤ) * finrank R (K.X i) =
      ∑ i ∈ s, (c.χ i : ℤ) * finrank R (K.homology i) :=
  K.sum_finrank_X_eq_sum_finrank_homology s hfin
    (fun _ _ h ↦ (hzero _ h).eq_of_src _ _)
    (fun _ _ h ↦ (hzero _ h).eq_of_tgt _ _)

/-- **Euler--Poincaré for a finitely supported complex of arbitrary shape.** Over a ring satisfying
the strong rank condition and rank--nullity, if every term `K.X i` is finitely generated and `K.X i`
is nonzero for only finitely many indices `i`, Mathlib's Euler characteristic of the terms of `K`
equals its homology Euler characteristic. -/
theorem eulerChar_eq_homologyEulerChar [∀ i, Module.Finite R (K.X i)]
    (hK : {i : ι | ¬ IsZero (K.X i)}.Finite) :
    K.eulerChar = K.homologyEulerChar := by
  let s := hK.toFinset
  have hzero (i : ι) (hi : i ∉ s) : IsZero (K.X i) := by
    by_contra h
    exact hi (hK.mem_toFinset.2 h)
  rw [K.eulerChar_eq_sum_finSet_of_finrankSupport_subset s
      ((GradedObject.finrankSupport_subset_iff _ _).2 fun i hi ↦
        ModuleCat.finrank_eq_zero_of_isZero (hzero i hi)),
    K.homologyEulerChar_eq_sum_finSet_of_finrankSupport_subset s
      ((GradedObject.finrankSupport_subset_iff _ _).2 fun i hi ↦
        ModuleCat.finrank_eq_zero_of_isZero
          (((K.exactAt_iff i).2 (ShortComplex.exact_of_isZero_X₂ _ (hzero i hi))).isZero_homology))]
  exact K.sum_finrank_X_eq_sum_finrank_homology_of_isZero s (fun _ _ ↦ inferInstance) hzero

end RankNullity

end HomologicalComplex
