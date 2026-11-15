/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.EulerCharacteristic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Dimension.RankNullity
import TauCeti.Algebra.Category.ModuleCat.Finrank
import TauCeti.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Euler–Poincaré for arbitrary complex shapes

Mathlib defines `HomologicalComplex.eulerChar` and `HomologicalComplex.homologyEulerChar` for any
index type `ι` and any `c : ComplexShape ι` equipped with alternating signs `c.EulerCharSigns`.
Whereas `ChainComplex.eulerChar_eq_homologyEulerChar` and
`CochainComplex.eulerChar_eq_homologyEulerChar` treat chain complexes on `ℕ` and cochain complexes
on `ℤ`, spectral sequence pages live on `ℤ × ℤ` with shape `ComplexShape.up' ⟨r, 1 - r⟩`.
This file proves the Euler–Poincaré equality `K.eulerChar = K.homologyEulerChar` for an arbitrary
`c : ComplexShape ι`, over any ring `R` satisfying `StrongRankCondition` and `HasRankNullity`
(covering division rings as well as commutative domains such as `ℤ`, with no Noetherianity
hypothesis), for every complex `K` with finitely generated terms that vanishes outside a finite set
of indices.

At each index `i`, rank–nullity on the short complex `K.sc i` gives
```text
finrank R (K.X i) =
  finrank R (K.homology i) + finrank R (im d_{prev i, i}) + finrank R (im d_{i, next i})
```
(`HomologicalComplex.finrank_X_eq_finrank_homology_add`). Multiplying by `c.χ i` and summing over a
finite set `s` outside which `K.X` vanishes rewrites both boundary sums over the pairs `(i, j)` in
`s ×ˢ s` with `c.Rel i j`, where they cancel term by term because `c.χ j = -c.χ i`
(`HomologicalComplex.sum_eulerCharSigns_finrank_X_eq_sum_finrank_homology`). No linear ordering or
induction on the index type is needed.

Finally, we equip `ComplexShape.up' u` on `ℤ × ℤ` when `u.1 + u.2` is odd — and in particular the
shape `ComplexShape.up' ⟨r, 1 - r⟩` of page `r` of a cohomological spectral sequence — with
total-degree `EulerCharSigns`.

## Main results

* `CategoryTheory.ShortComplex.finrank_X₂_eq_finrank_homology_add`: rank–nullity decomposition of
  the middle term of a short complex of modules.
* `HomologicalComplex.finrank_X_eq_finrank_homology_add`: degreewise rank–nullity for a
  homological complex of any shape.
* `HomologicalComplex.sum_eulerCharSigns_finrank_X_eq_sum_finrank_homology`: finite-sum
  Euler–Poincaré over any `Finset` containing all nonzero terms.
* `HomologicalComplex.eulerChar_eq_homologyEulerChar_of_forall_notMem` and
  `HomologicalComplex.eulerChar_eq_homologyEulerChar_of_finite`: Mathlib's term and homology Euler
  characteristics agree for finitely supported complexes of finitely generated modules.
* `ComplexShape.eulerCharSignsCohomologicalSpectralSequence`: total-degree alternating signs on the
  shape `ComplexShape.up' ⟨r, 1 - r⟩` of page `r` of a cohomological spectral sequence.

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge University Press, 1994,
  Sections 1.1 and 1.3.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Chapter 1.
-/

public section

open CategoryTheory Limits Module

universe u v

namespace CategoryTheory.ShortComplex

variable {R : Type u} [Ring R] [StrongRankCondition R] [HasRankNullity.{v} R]

/-- For a short complex `X₁ ⟶ X₂ ⟶ X₃` of modules with `X₂` finitely generated, over a ring
satisfying `StrongRankCondition` and `HasRankNullity`, the rank of `X₂` is the rank of the homology
plus the ranks of the incoming and outgoing images. -/
theorem finrank_X₂_eq_finrank_homology_add (S : ShortComplex (ModuleCat.{v} R))
    [Module.Finite R S.X₂] :
    finrank R S.X₂ =
      finrank R S.homology + finrank R (LinearMap.range S.f.hom) +
        finrank R (LinearMap.range S.g.hom) := by
  have h₁ := S.finrank_homology_add_finrank_range_f
  have h₂ := (LinearMap.ker S.g.hom).finrank_quotient_add_finrank
  rw [S.g.hom.quotKerEquivRange.finrank_eq] at h₂
  lia

end CategoryTheory.ShortComplex

namespace HomologicalComplex

section EulerPoincare

variable {R : Type u} [Ring R] [StrongRankCondition R] [HasRankNullity.{v} R]
  {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex (ModuleCat.{v} R) c)

/-- At any index `i` of a homological complex of modules, when `K.X i` is finitely generated, its
rank is the rank of `K.homology i` plus the ranks of the incoming and outgoing boundaries. -/
theorem finrank_X_eq_finrank_homology_add (i : ι) [Module.Finite R (K.X i)] :
    finrank R (K.X i) =
      finrank R (K.homology i) + finrank R (LinearMap.range (K.d (c.prev i) i).hom) +
        finrank R (LinearMap.range (K.d i (c.next i)).hom) :=
  have : Module.Finite R (K.sc i).X₂ := ‹Module.Finite R (K.X i)›
  (K.sc i).finrank_X₂_eq_finrank_homology_add

omit [HasRankNullity.{v} R] in
/-- Outside the edges of `c` inside a finite set `s` containing all nonzero terms of `K`, every
outgoing boundary `im d_{i, next i}` has rank zero, so its signed sum over `s` equals the sum over
the directed edges of `c` in `s ×ˢ s`. -/
private lemma sum_chi_finrank_range_d_next [c.EulerCharSigns]
    [DecidablePred fun ij : ι × ι ↦ c.Rel ij.1 ij.2] {s : Finset ι}
    (hs : ∀ i ∉ s, IsZero (K.X i)) :
    ∑ i ∈ s, (c.χ i : ℤ) * finrank R (LinearMap.range (K.d i (c.next i)).hom) =
      ∑ ij ∈ (s ×ˢ s).filter (fun ij ↦ c.Rel ij.1 ij.2),
        (c.χ ij.1 : ℤ) * finrank R (LinearMap.range (K.d ij.1 ij.2).hom) := by
  classical
  rw [Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  by_cases hrel : c.Rel i (c.next i) ∧ c.next i ∈ s
  · rw [Finset.sum_eq_single (c.next i)]
    · simp [hrel.1]
    · intro j _ hjne
      exact ite_eq_right_iff.2 fun h : c.Rel i j ↦ absurd (c.next_eq' h).symm hjne
    · exact fun hnot ↦ absurd hrel.2 hnot
  · rw [Finset.sum_eq_zero]
    · have hd0 : K.d i (c.next i) = 0 := by
        by_cases hr : c.Rel i (c.next i)
        · exact (hs (c.next i) fun hmem ↦ hrel ⟨hr, hmem⟩).eq_of_tgt _ _
        · exact K.shape _ _ hr
      rw [hd0, ModuleCat.hom_zero, LinearMap.range_zero, finrank_eq_zero_of_subsingleton]
      simp
    · intro j hj
      simp only [ite_eq_right_iff]
      intro hij
      exact absurd ⟨c.next_eq' hij ▸ hij, c.next_eq' hij ▸ hj⟩ hrel

omit [HasRankNullity.{v} R] in
/-- Symmetrically, the signed sum over `s` of the incoming boundary ranks `im d_{prev j, j}` equals
the sum over the directed edges of `c` in `s ×ˢ s`, weighted by `c.χ ij.2`. -/
private lemma sum_chi_finrank_range_d_prev [c.EulerCharSigns]
    [DecidablePred fun ij : ι × ι ↦ c.Rel ij.1 ij.2] {s : Finset ι}
    (hs : ∀ i ∉ s, IsZero (K.X i)) :
    ∑ j ∈ s, (c.χ j : ℤ) * finrank R (LinearMap.range (K.d (c.prev j) j).hom) =
      ∑ ij ∈ (s ×ˢ s).filter (fun ij ↦ c.Rel ij.1 ij.2),
        (c.χ ij.2 : ℤ) * finrank R (LinearMap.range (K.d ij.1 ij.2).hom) := by
  classical
  rw [Finset.sum_filter, Finset.sum_product_right]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  by_cases hrel : c.Rel (c.prev j) j ∧ c.prev j ∈ s
  · rw [Finset.sum_eq_single (c.prev j)]
    · simp [hrel.1]
    · intro i _ hine
      exact ite_eq_right_iff.2 fun h : c.Rel i j ↦ absurd (c.prev_eq' h).symm hine
    · exact fun hnot ↦ absurd hrel.2 hnot
  · rw [Finset.sum_eq_zero]
    · have hd0 : K.d (c.prev j) j = 0 := by
        by_cases hr : c.Rel (c.prev j) j
        · exact (hs (c.prev j) fun hmem ↦ hrel ⟨hr, hmem⟩).eq_of_src _ _
        · exact K.shape _ _ hr
      rw [hd0, ModuleCat.hom_zero, LinearMap.range_zero, finrank_eq_zero_of_subsingleton]
      simp
    · intro i hi
      simp only [ite_eq_right_iff]
      intro hij
      exact absurd ⟨c.prev_eq' hij ▸ hij, c.prev_eq' hij ▸ hi⟩ hrel

/-- **Euler–Poincaré over a finite support set for an arbitrary complex shape.** If `K` vanishes
outside `s` and its terms on `s` are finitely generated, the alternating sums of ranks of its terms
and of its homology over `s` coincide. -/
theorem sum_eulerCharSigns_finrank_X_eq_sum_finrank_homology [c.EulerCharSigns] {s : Finset ι}
    (hs : ∀ i ∉ s, IsZero (K.X i)) (hfin : ∀ i ∈ s, Module.Finite R (K.X i)) :
    ∑ i ∈ s, (c.χ i : ℤ) * finrank R (K.X i) =
      ∑ i ∈ s, (c.χ i : ℤ) * finrank R (K.homology i) := by
  classical
  have hstep : ∑ i ∈ s, (c.χ i : ℤ) * finrank R (K.X i) =
      ∑ i ∈ s, (c.χ i : ℤ) * finrank R (K.homology i) +
        (∑ i ∈ s, (c.χ i : ℤ) * finrank R (LinearMap.range (K.d (c.prev i) i).hom) +
          ∑ i ∈ s, (c.χ i : ℤ) * finrank R (LinearMap.range (K.d i (c.next i)).hom)) := by
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have := hfin i hi
    rw [K.finrank_X_eq_finrank_homology_add i]
    push_cast
    ring
  rw [hstep, K.sum_chi_finrank_range_d_prev hs, K.sum_chi_finrank_range_d_next hs,
    ← Finset.sum_add_distrib]
  suffices hcancel : ∑ ij ∈ (s ×ˢ s).filter (fun ij ↦ c.Rel ij.1 ij.2),
      ((c.χ ij.2 : ℤ) * finrank R (LinearMap.range (K.d ij.1 ij.2).hom) +
        (c.χ ij.1 : ℤ) * finrank R (LinearMap.range (K.d ij.1 ij.2).hom)) = 0 by
    rw [hcancel, add_zero]
  refine Finset.sum_eq_zero fun ij hij ↦ ?_
  rw [c.χ_next (Finset.mem_filter.1 hij).2]
  simp

/-- **Euler–Poincaré for a complex of arbitrary shape supported in a finite set.** Over a ring
satisfying `StrongRankCondition` and `HasRankNullity`, if `K` vanishes outside `s : Finset ι` and
has finitely generated terms on `s`, then `K.eulerChar = K.homologyEulerChar`. -/
theorem eulerChar_eq_homologyEulerChar_of_forall_notMem [c.EulerCharSigns] {s : Finset ι}
    (hs : ∀ i ∉ s, IsZero (K.X i)) (hfin : ∀ i ∈ s, Module.Finite R (K.X i)) :
    K.eulerChar = K.homologyEulerChar := by
  nontriviality R
  rw [K.eulerChar_eq_sum_finSet_of_finrankSupport_subset s
      ((GradedObject.finrankSupport_subset_iff _ _).2 fun i hi ↦
        ModuleCat.finrank_eq_zero_of_isZero (hs i hi)),
    K.homologyEulerChar_eq_sum_finSet_of_finrankSupport_subset s
      ((GradedObject.finrankSupport_subset_iff _ _).2 fun i hi ↦
        ModuleCat.finrank_eq_zero_of_isZero
          (((K.exactAt_iff i).2 (ShortComplex.exact_of_isZero_X₂ _ (hs i hi))).isZero_homology))]
  exact K.sum_eulerCharSigns_finrank_X_eq_sum_finrank_homology hs hfin

/-- **Euler–Poincaré for a finitely supported complex of arbitrary shape.** If `K` has finitely
many nonzero terms and every term is finitely generated, `K.eulerChar = K.homologyEulerChar`. -/
theorem eulerChar_eq_homologyEulerChar_of_finite [c.EulerCharSigns]
    (hsupp : {i : ι | ¬ IsZero (K.X i)}.Finite) (hfin : ∀ i, Module.Finite R (K.X i)) :
    K.eulerChar = K.homologyEulerChar :=
  K.eulerChar_eq_homologyEulerChar_of_forall_notMem
    (s := hsupp.toFinset)
    (fun i hi ↦ by
      by_contra hnot
      exact hi (hsupp.mem_toFinset.2 hnot))
    fun i _ ↦ hfin i

end EulerPoincare

end HomologicalComplex

namespace ComplexShape

/-- Any translation shape `ComplexShape.up' u` on `ℤ × ℤ` whose total-degree shift `u.1 + u.2` is
odd carries total-degree Euler characteristic signs `pq ↦ (-1)^(pq.1 + pq.2)`. -/
@[instance_reducible]
def eulerCharSignsUp'ProdInt {u : ℤ × ℤ} (hu : Odd (u.1 + u.2)) :
    (ComplexShape.up' u).EulerCharSigns where
  χ pq := (pq.1 + pq.2).negOnePow
  χ_next {pq pq'} (h : pq + u = pq') := by
    subst h
    obtain ⟨k, hk⟩ := hu
    have hsum : (pq + u).1 + (pq + u).2 = (pq.1 + pq.2) + (2 * k) + 1 := by
      simp only [Prod.fst_add, Prod.snd_add]
      lia
    rw [hsum, Int.negOnePow_succ, Int.negOnePow_add, Int.negOnePow_even (2 * k) ⟨k, by lia⟩,
      mul_one]

@[simp]
lemma eulerCharSignsUp'ProdInt_χ {u : ℤ × ℤ} (hu : Odd (u.1 + u.2)) (pq : ℤ × ℤ) :
    (letI := eulerCharSignsUp'ProdInt hu; (ComplexShape.up' u).χ pq) = (pq.1 + pq.2).negOnePow :=
  (rfl)

/-- Page `r` of a cohomological spectral sequence has differential bidegree `(r, 1 - r)`, of total
degree `1`, so its total-degree sign `(-1)^(p + q)` alternates along every differential,
independently of `r`. -/
instance eulerCharSignsCohomologicalSpectralSequence (r : ℤ) :
    (ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)).EulerCharSigns :=
  eulerCharSignsUp'ProdInt ⟨0, by lia⟩

lemma eulerCharSignsCohomologicalSpectralSequence_χ (r : ℤ) (pq : ℤ × ℤ) :
    (ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)).χ pq = (pq.1 + pq.2).negOnePow :=
  (rfl)

end ComplexShape
