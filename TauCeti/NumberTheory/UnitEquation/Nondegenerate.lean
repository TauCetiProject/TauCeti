/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Option
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Ring.Hom.Defs

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Field.Rat
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic.NormNum

/-!
# Nondegenerate solutions of linear unit equations

The unit equation theorem says that for nonzero coefficients `α₁, …, αₙ` in a field of
characteristic zero and a finitely generated subgroup `Γ` of its multiplicative group, the equation
`α₁ x₁ + ⋯ + αₙ xₙ = 1` has only finitely many solutions `x ∈ Γⁿ` for which no nonempty subsum
`∑ i ∈ I, αᵢ xᵢ` vanishes.  The restriction is necessary: once a subsum vanishes, multiplying all
of its coordinates by a common element of `Γ` gives another solution, so an infinite `Γ` yields
infinitely many.  The homogeneous form of the theorem treats
`∑ αᵢ xᵢ = 0` with no vanishing proper nonempty subsum, up to scaling.

This file defines both nondegeneracy conditions, over an arbitrary semiring so that they can be
transported along specialization homomorphisms out of finitely generated rings, and proves the
elementary manipulations used to reduce general solutions to nondegenerate ones:

* `TauCeti.IsNondegenerateSolution α x`: `∑ αᵢ xᵢ = 1` and no nonempty subsum vanishes;
* `TauCeti.IsNondegenerateHomogeneousSolution α x`: `∑ αᵢ xᵢ = 0` and no proper nonempty
  subsum vanishes;
* `TauCeti.isNondegenerateSolution_mul_div_iff`: nonzero factors of the unknowns may be moved to
  the coefficients;
* `TauCeti.exists_sum_eq_zero_and_isNondegenerateSolution_compl`: every solution of
  `∑ αᵢ xᵢ = 1` restricts to a nondegenerate solution on the complement of a vanishing subsum;
* `TauCeti.isNondegenerateHomogeneousSolution_option_iff`: dehomogenization, adjoining the term
  `-1 · 1`;
* `TauCeti.IsNondegenerateHomogeneousSolution.merge`: two proportional unknowns may be merged into
  one, as in the induction proving finiteness of the ratios `xᵢ / xⱼ`;
* `TauCeti.isNondegenerateSolution_div_of_minimal`: dividing a minimal vanishing subsum by one of
  its terms gives a nondegenerate solution in fewer unknowns;
* `TauCeti.IsNondegenerateSolution.merge`: the terms of a nondegenerate solution over a set of
  indices may be merged into one of them.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), Chapter 8, Section 8.3.
* J.-H. Evertse, H. P. Schlickewei, W. M. Schmidt, *Linear equations in variables which lie in a
  multiplicative group*, Ann. of Math. 155 (2002), Section 3.
-/

public section

open Finset
open scoped Finset

namespace TauCeti

variable {R S ι κ : Type*} [Fintype ι] [Fintype κ]

section Defs

variable [Semiring R]

/-- A solution `x` of the linear equation `∑ αᵢ xᵢ = 1` is *nondegenerate* if no nonempty
subsum `∑ i ∈ I, αᵢ xᵢ` vanishes. -/
def IsNondegenerateSolution (α x : ι → R) : Prop :=
  ∑ i, α i * x i = 1 ∧ ∀ I : Finset ι, I.Nonempty → ∑ i ∈ I, α i * x i ≠ 0

/-- A solution `x` of the homogeneous linear equation `∑ αᵢ xᵢ = 0` is *nondegenerate* if no
proper nonempty subsum `∑ i ∈ I, αᵢ xᵢ` vanishes. -/
def IsNondegenerateHomogeneousSolution (α x : ι → R) : Prop :=
  ∑ i, α i * x i = 0 ∧ ∀ I : Finset ι, I.Nonempty → I ≠ univ → ∑ i ∈ I, α i * x i ≠ 0

theorem isNondegenerateSolution_iff {α x : ι → R} :
    IsNondegenerateSolution α x ↔
      ∑ i, α i * x i = 1 ∧ ∀ I : Finset ι, I.Nonempty → ∑ i ∈ I, α i * x i ≠ 0 :=
  Iff.rfl

theorem isNondegenerateHomogeneousSolution_iff {α x : ι → R} :
    IsNondegenerateHomogeneousSolution α x ↔
      ∑ i, α i * x i = 0 ∧
        ∀ I : Finset ι, I.Nonempty → I ≠ univ → ∑ i ∈ I, α i * x i ≠ 0 :=
  Iff.rfl

end Defs

namespace IsNondegenerateSolution

section Semiring

variable [Semiring R] {α x : ι → R}

theorem sum_eq_one (h : IsNondegenerateSolution α x) : ∑ i, α i * x i = 1 :=
  h.1

theorem subsum_ne_zero (h : IsNondegenerateSolution α x) {I : Finset ι} (hI : I.Nonempty) :
    ∑ i ∈ I, α i * x i ≠ 0 :=
  h.2 I hI

/-- Every term of a nondegenerate solution is nonzero. -/
theorem ne_zero (h : IsNondegenerateSolution α x) (i : ι) : α i * x i ≠ 0 := by
  simpa using h.subsum_ne_zero (singleton_nonempty i)

/-- A nondegenerate solution stays nondegenerate under a ring homomorphism that is injective on
the subsums `∑ i ∈ I, αᵢ xᵢ`.  This is how nondegenerate solutions in a finitely generated ring
are specialized. -/
theorem map [Semiring S] (h : IsNondegenerateSolution α x) (φ : R →+* S)
    (hφ : Set.InjOn φ (Set.range fun I : Finset ι ↦ ∑ i ∈ I, α i * x i)) :
    IsNondegenerateSolution (φ ∘ α) (φ ∘ x) := by
  refine ⟨by simp [← map_mul, ← map_sum, h.sum_eq_one], fun I hI hφI ↦ ?_⟩
  refine h.subsum_ne_zero hI (hφ ⟨I, rfl⟩ ⟨∅, sum_empty⟩ ?_)
  simpa [map_sum, map_mul] using hφI

/-- Reindexing a nondegenerate solution along an equivalence of index types gives a
nondegenerate solution. -/
theorem comp_equiv (h : IsNondegenerateSolution α x) (e : κ ≃ ι) :
    IsNondegenerateSolution (α ∘ e) (x ∘ e) := by
  refine ⟨(e.sum_comp fun i ↦ α i * x i).trans h.sum_eq_one, fun J hJ ↦ ?_⟩
  simpa [sum_map] using h.subsum_ne_zero (hJ.map (f := e.toEmbedding))

/-- An injective ring homomorphism preserves and reflects nondegenerate solutions. This moves
solutions between a field and a subring containing their coordinates and coefficients. -/
@[simp]
theorem _root_.TauCeti.isNondegenerateSolution_map_iff [Semiring S] {φ : R →+* S}
    (hφ : Function.Injective φ) : IsNondegenerateSolution (φ ∘ α) (φ ∘ x) ↔
      IsNondegenerateSolution α x := by
  simp only [isNondegenerateSolution_iff, Function.comp_apply, ← map_mul, ← map_sum,
    hφ.eq_iff' (map_one φ), ne_eq, map_eq_zero_iff φ hφ]

/-- If a solution of `∑ αᵢ xᵢ = 1` has a vanishing subsum over `I` and no vanishing nonempty
subsum disjoint from `I`, then its restriction to the complement of `I` is nondegenerate. -/
theorem restrict [DecidableEq ι] {I : Finset ι} (h : ∑ i, α i * x i = 1)
    (hI : ∑ i ∈ I, α i * x i = 0)
    (hJ : ∀ J : Finset ι, J.Nonempty → Disjoint J I → ∑ i ∈ J, α i * x i ≠ 0) :
    IsNondegenerateSolution (fun i : ↥(Iᶜ) ↦ α i) (fun i ↦ x i) := by
  refine ⟨?_, fun J hJne ↦ ?_⟩
  · rw [sum_coe_sort Iᶜ fun i ↦ α i * x i, ← h, ← sum_add_sum_compl I, hI, zero_add]
  · have hdisj : Disjoint (J.map (Function.Embedding.subtype _)) I :=
      disjoint_left.mpr fun i hi ↦ by
        obtain ⟨j, -, rfl⟩ := mem_map.mp hi
        exact mem_compl.mp j.property
    simpa [sum_map] using hJ _ hJne.map hdisj

end Semiring

/-- Moving nonzero factors `cᵢ` from the unknowns to the coefficients: `x / c` is a nondegenerate
solution of `∑ αᵢ cᵢ wᵢ = 1` exactly when `x` is one of `∑ αᵢ xᵢ = 1`, since the terms
`αᵢ cᵢ (xᵢ / cᵢ) = αᵢ xᵢ` agree. -/
@[simp]
theorem _root_.TauCeti.isNondegenerateSolution_mul_div_iff [Semifield R] {α x c : ι → R}
    (hc : ∀ i, c i ≠ 0) :
    IsNondegenerateSolution (α * c) (x / c) ↔ IsNondegenerateSolution α x := by
  have h (i : ι) : (α * c) i * (x / c) i = α i * x i := by
    rw [Pi.mul_apply, Pi.div_apply, mul_assoc, mul_div_cancel₀ _ (hc i)]
  simp only [isNondegenerateSolution_iff, h]

/-- With a single unknown, `α x = 1` is a nondegenerate solution. -/
theorem _root_.TauCeti.isNondegenerateSolution_of_subsingleton [Semiring R] [Nontrivial R]
    [Subsingleton ι] {α x : ι → R} (i : ι) (h : α i * x i = 1) :
    IsNondegenerateSolution α x := by
  have huniv : ∀ I : Finset ι, I.Nonempty → I = {i} := fun I hI ↦
    (hI.subset_singleton_iff.mp fun j _ ↦ mem_singleton.mpr (Subsingleton.elim j i))
  refine ⟨?_, fun I hI ↦ ?_⟩
  · rw [huniv univ ⟨i, mem_univ i⟩, sum_singleton, h]
  · rw [huniv I hI, sum_singleton, h]
    exact one_ne_zero

end IsNondegenerateSolution

section Semiring

variable [Semiring R] {α x : ι → R}

/-- Every solution of `∑ αᵢ xᵢ = 1` has a vanishing subsum over some `I` such that its
restriction to `Iᶜ` is a nondegenerate solution. -/
theorem exists_sum_eq_zero_and_isNondegenerateSolution_compl [DecidableEq ι]
    (h : ∑ i, α i * x i = 1) :
    ∃ I : Finset ι, ∑ i ∈ I, α i * x i = 0 ∧
      IsNondegenerateSolution (fun i : ↥(Iᶜ) ↦ α i) (fun i ↦ x i) := by
  classical
  let s : Finset (Finset ι) := univ.filter fun I ↦ ∑ i ∈ I, α i * x i = 0
  obtain ⟨I, hI⟩ := s.exists_maximal ⟨∅, by simp [s]⟩
  have hI0 : ∑ i ∈ I, α i * x i = 0 := (mem_filter.mp hI.prop).2
  refine ⟨I, hI0, IsNondegenerateSolution.restrict h hI0 fun J hJ hJI hJ0 ↦ ?_⟩
  have hunion : I ∪ J ∈ s := by
    simp [s, sum_union hJI.symm, hI0, hJ0]
  have hsub : J ⊆ I :=
    subset_union_right.trans (hI.le_of_ge hunion subset_union_left)
  obtain ⟨j, hj⟩ := hJ
  exact disjoint_left.mp hJI hj (hsub hj)

/-- A solution in two unknowns is nondegenerate exactly when both terms are nonzero. -/
theorem isNondegenerateSolution_fin_two_iff {α x : Fin 2 → R} :
    IsNondegenerateSolution α x ↔
      α 0 * x 0 + α 1 * x 1 = 1 ∧ α 0 * x 0 ≠ 0 ∧ α 1 * x 1 ≠ 0 := by
  refine ⟨fun h ↦ ⟨by simpa [Fin.sum_univ_two] using h.sum_eq_one, h.ne_zero 0, h.ne_zero 1⟩,
    fun ⟨hsum, h0, h1⟩ ↦ ⟨by simpa [Fin.sum_univ_two] using hsum, fun I hI ↦ ?_⟩⟩
  obtain rfl | rfl | rfl : I = {0} ∨ I = {1} ∨ I = univ := by revert I; decide
  · simpa using h0
  · simpa using h1
  · rw [Fin.sum_univ_two, hsum]
    intro h10
    exact h0 (by rw [← mul_one (α 0 * x 0), h10, mul_zero])

end Semiring

namespace IsNondegenerateHomogeneousSolution

variable [Semiring R] {α x : ι → R}

theorem sum_eq_zero (h : IsNondegenerateHomogeneousSolution α x) : ∑ i, α i * x i = 0 :=
  h.1

theorem subsum_ne_zero (h : IsNondegenerateHomogeneousSolution α x) {I : Finset ι}
    (hI : I.Nonempty) (hIu : I ≠ univ) : ∑ i ∈ I, α i * x i ≠ 0 :=
  h.2 I hI hIu

/-- With at least two unknowns, every term of a nondegenerate homogeneous solution is
nonzero. -/
theorem ne_zero [Nontrivial ι] (h : IsNondegenerateHomogeneousSolution α x) (i : ι) :
    α i * x i ≠ 0 := by
  simpa using h.subsum_ne_zero (singleton_nonempty i) (singleton_ne_univ i)

end IsNondegenerateHomogeneousSolution

/-- Rescaling a homogeneous solution by a nonzero scalar preserves nondegeneracy. -/
@[simp]
theorem isNondegenerateHomogeneousSolution_smul_iff [CommSemiring R] [NoZeroDivisors R]
    {α x : ι → R} {c : R} (hc : c ≠ 0) :
    IsNondegenerateHomogeneousSolution α (c • x) ↔ IsNondegenerateHomogeneousSolution α x := by
  have hsum : ∀ I : Finset ι, ∑ i ∈ I, α i * (c • x) i = c * ∑ i ∈ I, α i * x i := fun I ↦ by
    simp [mul_sum, mul_left_comm]
  simp only [isNondegenerateHomogeneousSolution_iff, hsum, mul_eq_zero, hc, false_or, ne_eq]

namespace IsNondegenerateHomogeneousSolution

variable [CommSemiring R] {α x : ι → R}

theorem smul [NoZeroDivisors R] (h : IsNondegenerateHomogeneousSolution α x) {c : R}
    (hc : c ≠ 0) : IsNondegenerateHomogeneousSolution α (c • x) :=
  (isNondegenerateHomogeneousSolution_smul_iff hc).mpr h

/-- Merging two proportional unknowns: if `x p = β * x q` with `p ≠ q`, dropping the unknown
`x p` and replacing the coefficient `α q` by `α q + β * α p` gives a nondegenerate homogeneous
solution in one unknown fewer. -/
theorem merge [DecidableEq ι] (h : IsNondegenerateHomogeneousSolution α x) {p q : ι}
    (hpq : p ≠ q) {β : R} (hx : x p = β * x q) :
    IsNondegenerateHomogeneousSolution
      (fun i : {i // i ≠ p} ↦ Function.update α q (α q + β * α p) i) (fun i ↦ x i) := by
  let e : {i // i ≠ p} ↪ ι := Function.Embedding.subtype _
  let q' : {i // i ≠ p} := ⟨q, hpq.symm⟩
  -- A subsum of the merged equation is the original subsum over the same indices, together with
  -- the index `p` exactly when `q` is among them.
  have key : ∀ J : Finset {i // i ≠ p},
      ∑ j ∈ J, Function.update α q (α q + β * α p) j * x j =
        ∑ i ∈ (if q' ∈ J then insert p (J.map e) else J.map e), α i * x i := by
    intro J
    have hpJ : p ∉ J.map e := fun hp ↦ by
      obtain ⟨j, -, hj⟩ := mem_map.mp hp
      exact j.property hj
    have hupd : ∀ j : {i // i ≠ p}, Function.update α q (α q + β * α p) j * x j =
        α j * x j + if j = q' then α p * x p else 0 := by
      intro j
      by_cases hj : j = q'
      · subst hj
        simp [q', hx, add_mul, mul_left_comm, mul_assoc]
      · have hjq : (j : ι) ≠ q := fun hjq ↦ hj (Subtype.ext hjq)
        simp [Function.update_of_ne hjq, hj]
    simp only [hupd, sum_add_distrib, sum_ite_eq']
    split_ifs <;> simp [sum_insert hpJ, sum_map, e, add_comm]
  refine ⟨?_, fun J hJ hJu ↦ ?_⟩
  · have hins : insert p ((univ : Finset {i // i ≠ p}).map e) = univ :=
      eq_univ_of_forall fun i ↦ by
        by_cases hip : i = p
        · simp [hip]
        · exact mem_insert_of_mem (mem_map.mpr ⟨⟨i, hip⟩, mem_univ _, rfl⟩)
    rw [key]
    simp only [mem_univ, ↓reduceIte, hins]
    exact h.sum_eq_zero
  · obtain ⟨j₀, hj₀⟩ : ∃ j₀, j₀ ∉ J := by
      by_contra! hall
      exact hJu (eq_univ_of_forall hall)
    have hj₀' : (j₀ : ι) ∉ insert p (J.map e) := by
      simp only [mem_insert, mem_map, not_or]
      exact ⟨j₀.property, fun ⟨j, hj, hjj⟩ ↦ hj₀ (Subtype.ext hjj ▸ hj)⟩
    rw [key]
    split_ifs
    · exact h.subsum_ne_zero (insert_nonempty _ _)
        fun hu ↦ hj₀' (hu ▸ mem_univ _)
    · exact h.subsum_ne_zero hJ.map
        fun hu ↦ hj₀' (mem_insert_of_mem (hu ▸ mem_univ _))

end IsNondegenerateHomogeneousSolution

/-- A homogeneous solution in two unknowns is nondegenerate exactly when both terms are
nonzero. -/
theorem isNondegenerateHomogeneousSolution_fin_two_iff [Semiring R] {α x : Fin 2 → R} :
    IsNondegenerateHomogeneousSolution α x ↔
      α 0 * x 0 + α 1 * x 1 = 0 ∧ α 0 * x 0 ≠ 0 ∧ α 1 * x 1 ≠ 0 := by
  refine ⟨fun h ↦ ⟨by simpa [Fin.sum_univ_two] using h.sum_eq_zero, h.ne_zero 0, h.ne_zero 1⟩,
    fun ⟨hsum, h0, h1⟩ ↦ ⟨by simpa [Fin.sum_univ_two] using hsum, fun I hI hIu ↦ ?_⟩⟩
  obtain rfl | rfl | rfl : I = {0} ∨ I = {1} ∨ I = univ := by revert I; decide
  · simpa using h0
  · simpa using h1
  · exact absurd rfl hIu

/-- Dehomogenization: adjoining the term `(-1) · 1` turns nondegenerate solutions of
`∑ αᵢ xᵢ = 1` into nondegenerate solutions of the homogeneous equation, and conversely. -/
theorem isNondegenerateHomogeneousSolution_option_iff [Ring R] {α x : Option κ → R}
    (hα : α none = -1) (hx : x none = 1) :
    IsNondegenerateHomogeneousSolution α x ↔
      IsNondegenerateSolution (α ∘ some) (x ∘ some) := by
  classical
  have htotal : ∑ i, α i * x i = 0 ↔ ∑ i, (α ∘ some) i * (x ∘ some) i = 1 := by
    rw [Fintype.sum_option, hα, hx, neg_one_mul, neg_add_eq_zero, eq_comm]
    rfl
  refine ⟨fun h ↦ ⟨htotal.mp h.sum_eq_zero, fun J hJ ↦ ?_⟩, fun h ↦ ⟨htotal.mpr h.sum_eq_one,
    fun I hI hIu ↦ ?_⟩⟩
  · have hnone : none ∉ J.map Function.Embedding.some := by simp
    simpa [sum_map] using h.subsum_ne_zero hJ.map fun hu ↦ hnone (hu ▸ mem_univ _)
  · by_cases hnone : none ∈ I
    · -- The subsum over `I = {none} ∪ J` is `-1 + ∑ J`; it is nonzero because the subsum over
      -- the nonempty complement of `J` is nonzero.
      have hI' : I = insertNone (eraseNone I) := by
        rw [insertNone_eraseNone, insert_eq_of_mem hnone]
      obtain ⟨j, hj⟩ : ∃ j, j ∉ eraseNone I := by
        by_contra! hall
        refine hIu (eq_univ_of_forall fun i ↦ ?_)
        cases i with
        | none => exact hnone
        | some j => exact mem_eraseNone.mp (hall j)
      have hcompl := h.subsum_ne_zero (I := (eraseNone I)ᶜ) ⟨j, mem_compl.mpr hj⟩
      have hsplit := sum_add_sum_compl (eraseNone I) fun i ↦ (α ∘ some) i * (x ∘ some) i
      rw [h.sum_eq_one] at hsplit
      rw [hI', sum_insertNone, hα, hx, neg_one_mul, ne_eq, neg_add_eq_zero]
      intro h1
      apply hcompl
      simpa [← h1] using hsplit
    · have hI' : I = (eraseNone I).map Function.Embedding.some := by
        rw [map_some_eraseNone, erase_eq_of_notMem hnone]
      have hne : (eraseNone I).Nonempty := by
        obtain ⟨i, hi⟩ := hI
        cases i with
        | none => exact absurd hi hnone
        | some j => exact ⟨j, mem_eraseNone.mpr hi⟩
      rw [hI', sum_map]
      simpa using h.subsum_ne_zero hne

section DivisionRing

variable {K : Type*}

omit [Fintype ι] in
/-- Dividing a minimal vanishing subsum by one of its terms: if `∑_{i ∈ I} cᵢyᵢ = 0` with
`2 ≤ |I|` and no nonempty proper subsum vanishes, then for `i₁ ∈ I` the ratios `zᵢ = yᵢ / yᵢ₁`
form a nondegenerate solution of `∑_{i ∈ I \ {i₁}} (-cᵢ / cᵢ₁) zᵢ = 1`. -/
theorem isNondegenerateSolution_div_of_minimal [Field K] [DecidableEq ι] {c y : ι → K}
    {I : Finset ι} {i₁ : ι} (hi₁ : i₁ ∈ I) (hI : 2 ≤ #I) (hI0 : ∑ i ∈ I, c i * y i = 0)
    (hmin : ∀ J ⊂ I, J.Nonempty → ∑ i ∈ J, c i * y i ≠ 0) :
    IsNondegenerateSolution (fun j : ↥(I.erase i₁) ↦ -c j / c i₁)
      (fun j : ↥(I.erase i₁) ↦ y j / y i₁) := by
  have herase : I.erase i₁ ⊂ I := erase_ssubset hi₁
  have hne : (I.erase i₁).Nonempty := by
    rw [← card_pos, card_erase_of_mem hi₁]
    omega
  have hsplit : ∑ i ∈ I.erase i₁, c i * y i = -(c i₁ * y i₁) := by
    rw [eq_neg_iff_add_eq_zero, sum_erase_add _ _ hi₁, hI0]
  have hc₁ : c i₁ * y i₁ ≠ 0 := by
    rw [← neg_ne_zero, ← hsplit]
    exact hmin _ herase hne
  -- Every subsum of the new equation is a subsum of the old one divided by `-cᵢ₁yᵢ₁`.
  have key (J : Finset ↥(I.erase i₁)) :
      ∑ j ∈ J, -c j / c i₁ * (y j / y i₁) =
        -(∑ i ∈ J.map (Function.Embedding.subtype _), c i * y i) / (c i₁ * y i₁) := by
    rw [sum_map, neg_div, sum_div, ← sum_neg_distrib]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [Function.Embedding.subtype_apply, div_mul_div_comm, neg_mul, neg_div]
  refine isNondegenerateSolution_iff.mpr ⟨?_, fun J hJ ↦ ?_⟩
  · have huniv : (univ : Finset ↥(I.erase i₁)).map (Function.Embedding.subtype _) = I.erase i₁ :=
      by ext; simp
    rw [key, huniv, hsplit, neg_neg, div_self hc₁]
  · rw [key]
    refine div_ne_zero (neg_ne_zero.mpr (hmin _ ?_ hJ.map)) hc₁
    refine LE.le.trans_ssubset (fun i hi ↦ ?_) herase
    obtain ⟨j, -, rfl⟩ := mem_map.mp hi
    exact j.property

/-- Merging the terms over `insert i₁ I` of a nondegenerate solution `y` of `∑ yᵢ = 1` into the
term at `i₁`: the unknowns `yᵢ` for `i ∉ I \ {i₁}` form a nondegenerate solution of the equation
whose coefficient at `i₁` is `1 + ∑_{i ∈ I \ {i₁}} yᵢ / yᵢ₁` and whose other coefficients are `1`.
The argument adapts that of `TauCeti.IsNondegenerateHomogeneousSolution.merge`. -/
theorem IsNondegenerateSolution.merge [DivisionSemiring K] [DecidableEq ι] {y : ι → K}
    (hy : IsNondegenerateSolution 1 y) (I : Finset ι) (i₁ : ι) :
    IsNondegenerateSolution
      (fun i : {i // i ∉ I.erase i₁} ↦
        if (i : ι) = i₁ then 1 + ∑ j : ↥(I.erase i₁), y j / y i₁ else 1)
      (fun i ↦ y i) := by
  have hi₁ : y i₁ ≠ 0 := by simpa using hy.ne_zero i₁
  let e : {i // i ∉ I.erase i₁} ↪ ι := Function.Embedding.subtype _
  have hi₁' : i₁ ∉ I.erase i₁ := notMem_erase i₁ I
  -- A subsum of the merged equation is the subsum of `y` over the same indices, together with
  -- `I \ {i₁}` exactly when `i₁` is among them.
  have key (J : Finset {i // i ∉ I.erase i₁}) :
      ∑ i ∈ J, (if (i : ι) = i₁ then 1 + ∑ j : ↥(I.erase i₁), y j / y i₁ else 1) * y i =
        ∑ i ∈ (if ⟨i₁, hi₁'⟩ ∈ J then J.map e ∪ I.erase i₁ else J.map e), y i := by
    have hdisj : Disjoint (J.map e) (I.erase i₁) := disjoint_left.mpr fun i hi ↦ by
      obtain ⟨j, -, rfl⟩ := mem_map.mp hi
      exact j.property
    have hterm (i : {i // i ∉ I.erase i₁}) :
        (if (i : ι) = i₁ then 1 + ∑ j : ↥(I.erase i₁), y j / y i₁ else 1) * y i =
          y i + if i = ⟨i₁, hi₁'⟩ then ∑ j ∈ I.erase i₁, y j else 0 := by
      by_cases hi : i = ⟨i₁, hi₁'⟩
      · subst hi
        simp only [↓reduceIte, add_mul, one_mul, sum_mul, div_mul_cancel₀ _ hi₁]
        rw [sum_coe_sort (I.erase i₁) y]
      · have hi' : (i : ι) ≠ i₁ := fun h ↦ hi (Subtype.ext h)
        simp [hi, hi']
    simp only [hterm, sum_add_distrib, sum_ite_eq']
    split_ifs <;> simp [sum_union hdisj, sum_map, e]
  refine isNondegenerateSolution_iff.mpr ⟨?_, fun J hJ ↦ ?_⟩
  · have huniv : (univ : Finset {i // i ∉ I.erase i₁}).map e ∪ I.erase i₁ = univ :=
      eq_univ_of_forall fun i ↦ by
        by_cases hi : i ∈ I.erase i₁
        · exact mem_union_right _ hi
        · exact mem_union_left _ (mem_map.mpr ⟨⟨i, hi⟩, mem_univ _, rfl⟩)
    rw [key]
    simp only [mem_univ, ↓reduceIte, huniv]
    simpa using hy.sum_eq_one
  · rw [key]
    have hne : (if ⟨i₁, hi₁'⟩ ∈ J then J.map e ∪ I.erase i₁ else J.map e).Nonempty := by
      split_ifs
      · exact hJ.map.mono subset_union_left
      · exact hJ.map
    simpa using hy.subsum_ne_zero hne

end DivisionRing

/-- `1/2 + 1/2 = 1` is a nondegenerate solution. -/
example : IsNondegenerateSolution (R := ℚ) ![1, 1] ![1 / 2, 1 / 2] := by
  rw [isNondegenerateSolution_fin_two_iff]
  norm_num

/-- `2 - 2 + 1 = 1` is a degenerate solution: its first two terms cancel. -/
example : ¬ IsNondegenerateSolution (R := ℚ) ![1, -1, 1] ![2, 2, 1] := fun h ↦
  h.subsum_ne_zero (I := {0, 1}) (insert_nonempty _ _) (by simp)

/-- `1 - 1 + 1 - 1 = 0` is a degenerate homogeneous solution. -/
example : ¬ IsNondegenerateHomogeneousSolution (R := ℚ) ![1, -1, 1, -1] ![1, 1, 1, 1] :=
  fun h ↦ h.subsum_ne_zero (I := {0, 1}) (insert_nonempty _ _) (by decide) (by simp)

end TauCeti
