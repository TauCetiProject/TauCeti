/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.DirectSum.Finite

/-!
# Direct sums whose summands vanish outside a finite set

A direct sum `⨁ i, M i` over an infinite index type still behaves like a finite one as soon as all
but finitely many summands are trivial: a family graded by `ℤ` with finitely many nonzero degrees
is the standard example.  `TauCeti.DirectSum.restrictLinearEquiv` identifies such a direct sum with
the direct sum over a finite set of indices carrying the nonzero summands;
`TauCeti.DirectSum.restrictSubtypeLinearEquiv` more generally identifies it with the direct sum
over the subtype of indices satisfying a predicate outside which the summands are trivial.  The
two consequences a graded dimension count needs follow: such a direct sum is a finite module, and
its dimension is the finite sum of the dimensions of its summands.  Mathlib's
`Module.finrank_directSum` asks the index type itself to be finite, which a family graded by `ℤ`
does not satisfy.  The parallel count for an *internal* decomposition of a fixed module is in
`TauCeti.LinearAlgebra.Dimension.DirectSum`.

## Main definitions

* `TauCeti.DirectSum.restrictSubtypeLinearEquiv`: the equivalence
  `(⨁ i, M i) ≃ₗ[R] ⨁ i : {i // p i}, M i` for a predicate `p` outside which the summands are
  trivial.
* `TauCeti.DirectSum.restrictLinearEquiv`: the equivalence `(⨁ i, M i) ≃ₗ[R] ⨁ i : s, M i` for a
  finite set `s` outside which the summands are trivial.
* `TauCeti.DirectSum.componentLinearEquiv`: the extreme case of a single surviving index, where
  the direct sum is the equivalence `(⨁ i, M i) ≃ₗ[R] M d`.

## Main results

* `TauCeti.DirectSum.finite_of_subsingleton_notMem`: such a direct sum is a finite module.
* `TauCeti.finrank_directSum_eq_sum`: its dimension is the sum of the dimensions of the summands
  indexed by the finite set.
-/

public section

open scoped DirectSum

namespace TauCeti

universe u v w

variable {ι : Type v} [DecidableEq ι]

section Restriction

variable {R : Type u} [Semiring R] (M : ι → Type w)
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- **Restricting a direct sum to the indices satisfying a predicate.**  If every summand at an
index outside `p` is trivial, then `⨁ i, M i` is the direct sum of the summands indexed by the
subtype `{i // p i}`. -/
def DirectSum.restrictSubtypeLinearEquiv (p : ι → Prop) [DecidablePred p]
    (hp : ∀ i, ¬ p i → Subsingleton (M i)) :
    (⨁ i, M i) ≃ₗ[R] ⨁ i : {i // p i}, M i :=
  LinearEquiv.ofLinearMap
    (DirectSum.toModule R ι _ fun i ↦
      if h : p i then DirectSum.lof R {i // p i} (fun j ↦ M j) ⟨i, h⟩ else 0)
    (DirectSum.toModule R {i // p i} _ fun i ↦ DirectSum.lof R ι M i)
    (DirectSum.linearMap_ext R fun i ↦ LinearMap.ext fun x ↦ by
      simp [i.2])
    (DirectSum.linearMap_ext R fun i ↦ LinearMap.ext fun x ↦ by
      by_cases h : p i
      · simp [h]
      · have := hp i h
        simp [Subsingleton.elim x 0])

/-- The subtype restriction equivalence sends the summand at an index satisfying `p` to the same
summand. -/
@[simp]
theorem DirectSum.restrictSubtypeLinearEquiv_lof (p : ι → Prop) [DecidablePred p]
    (hp : ∀ i, ¬ p i → Subsingleton (M i)) {i : ι} (hi : p i) (x : M i) :
    DirectSum.restrictSubtypeLinearEquiv (R := R) M p hp (DirectSum.lof R ι M i x) =
      DirectSum.lof R {i // p i} (fun j ↦ M j) ⟨i, hi⟩ x := by
  simp [DirectSum.restrictSubtypeLinearEquiv, hi]

/-- The subtype restriction equivalence sends a summand at an index outside `p` to zero. -/
@[simp]
theorem DirectSum.restrictSubtypeLinearEquiv_lof_of_not (p : ι → Prop) [DecidablePred p]
    (hp : ∀ i, ¬ p i → Subsingleton (M i)) {i : ι} (hi : ¬ p i) (x : M i) :
    DirectSum.restrictSubtypeLinearEquiv (R := R) M p hp (DirectSum.lof R ι M i x) = 0 := by
  simp [DirectSum.restrictSubtypeLinearEquiv, hi]

/-- The subtype restriction equivalence is inverse to the evident inclusion of the summands
indexed by `{i // p i}`. -/
@[simp]
theorem DirectSum.restrictSubtypeLinearEquiv_symm_lof (p : ι → Prop) [DecidablePred p]
    (hp : ∀ i, ¬ p i → Subsingleton (M i)) (i : {i // p i}) (x : M i) :
    (DirectSum.restrictSubtypeLinearEquiv (R := R) M p hp).symm
        (DirectSum.lof R {i // p i} (fun j ↦ M j) i x) = DirectSum.lof R ι M i x := by
  simp [DirectSum.restrictSubtypeLinearEquiv]

/-- Each component of the subtype restriction of an element is the corresponding component of that
element. -/
@[simp]
theorem DirectSum.restrictSubtypeLinearEquiv_apply (p : ι → Prop) [DecidablePred p]
    (hp : ∀ i, ¬ p i → Subsingleton (M i)) (x : ⨁ i, M i) (i : {i // p i}) :
    DirectSum.restrictSubtypeLinearEquiv (R := R) M p hp x i = x i := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of j y =>
    rw [← DirectSum.lof_eq_of R]
    by_cases hj : p j <;> simp [hj] <;> simp [DirectSum.lof_eq_of, DirectSum.of_apply] <;> grind
  | add x y hx hy => simp [hx, hy]

/-- Each component of the inverse subtype restriction is the corresponding component at an index
satisfying `p`, and zero at an index outside `p`. -/
@[simp]
theorem DirectSum.restrictSubtypeLinearEquiv_symm_apply (p : ι → Prop) [DecidablePred p]
    (hp : ∀ i, ¬ p i → Subsingleton (M i)) (y : ⨁ i : {i // p i}, M i) (i : ι) :
    (DirectSum.restrictSubtypeLinearEquiv (R := R) M p hp).symm y i =
      if hi : p i then y ⟨i, hi⟩ else 0 := by
  split_ifs with hi
  · rw [← DirectSum.restrictSubtypeLinearEquiv_apply (R := R) M p hp _ ⟨i, hi⟩,
      LinearEquiv.apply_symm_apply]
  · have := hp i hi
    exact Subsingleton.elim _ _

/-- **Restricting a direct sum to a finite set of indices.**  If every summand outside a finite
set `s` is trivial, then `⨁ i, M i` is the direct sum of the summands indexed by `s`.  This is
`TauCeti.DirectSum.restrictSubtypeLinearEquiv` for membership in `s`. -/
def DirectSum.restrictLinearEquiv (s : Finset ι) (hs : ∀ i ∉ s, Subsingleton (M i)) :
    (⨁ i, M i) ≃ₗ[R] ⨁ i : s, M i :=
  DirectSum.restrictSubtypeLinearEquiv M (· ∈ s) hs

/-- The restriction equivalence sends the summand at an index of `s` to the same summand. -/
@[simp]
theorem DirectSum.restrictLinearEquiv_lof (s : Finset ι) (hs : ∀ i ∉ s, Subsingleton (M i))
    {i : ι} (hi : i ∈ s) (x : M i) :
    DirectSum.restrictLinearEquiv (R := R) M s hs (DirectSum.lof R ι M i x) =
      DirectSum.lof R s (fun j : s ↦ M j) ⟨i, hi⟩ x :=
  DirectSum.restrictSubtypeLinearEquiv_lof M (· ∈ s) hs hi x

/-- The restriction equivalence sends a summand outside `s` to zero. -/
@[simp]
theorem DirectSum.restrictLinearEquiv_lof_of_notMem (s : Finset ι)
    (hs : ∀ i ∉ s, Subsingleton (M i)) {i : ι} (hi : i ∉ s) (x : M i) :
    DirectSum.restrictLinearEquiv (R := R) M s hs (DirectSum.lof R ι M i x) = 0 :=
  DirectSum.restrictSubtypeLinearEquiv_lof_of_not M (· ∈ s) hs hi x

/-- The restriction equivalence is inverse to the evident inclusion of the summands indexed by
`s`. -/
@[simp]
theorem DirectSum.restrictLinearEquiv_symm_lof (s : Finset ι) (hs : ∀ i ∉ s, Subsingleton (M i))
    (i : s) (x : M i) :
    (DirectSum.restrictLinearEquiv (R := R) M s hs).symm
        (DirectSum.lof R s (fun j : s ↦ M j) i x) = DirectSum.lof R ι M i x :=
  DirectSum.restrictSubtypeLinearEquiv_symm_lof M (· ∈ s) hs i x

/-- Each component of the restriction of an element is the corresponding component of that
element. -/
@[simp]
theorem DirectSum.restrictLinearEquiv_apply (s : Finset ι) (hs : ∀ i ∉ s, Subsingleton (M i))
    (x : ⨁ i, M i) (i : s) :
    DirectSum.restrictLinearEquiv (R := R) M s hs x i = x i :=
  DirectSum.restrictSubtypeLinearEquiv_apply M (· ∈ s) hs x i

/-- Each component of the inverse restriction is the corresponding component at an index of `s`,
and zero at an index outside `s`. -/
@[simp]
theorem DirectSum.restrictLinearEquiv_symm_apply (s : Finset ι)
    (hs : ∀ i ∉ s, Subsingleton (M i)) (y : ⨁ i : s, M i) (i : ι) :
    (DirectSum.restrictLinearEquiv (R := R) M s hs).symm y i =
      if hi : i ∈ s then y ⟨i, hi⟩ else 0 :=
  DirectSum.restrictSubtypeLinearEquiv_symm_apply M (· ∈ s) hs y i

/-- **A direct sum concentrated in a single index is that summand.**  This is the extreme case of
`TauCeti.DirectSum.restrictLinearEquiv`, in the form in which a grading concentrated in one degree
meets it. -/
def DirectSum.componentLinearEquiv (d : ι) (hd : ∀ i, i ≠ d → Subsingleton (M i)) :
    (⨁ i, M i) ≃ₗ[R] M d :=
  LinearEquiv.ofLinearMap (DirectSum.component R ι M d) (DirectSum.lof R ι M d)
    (LinearMap.ext fun x ↦ by simp)
    (DirectSum.linearMap_ext R fun i ↦ LinearMap.ext fun x ↦ by
      obtain rfl | h := eq_or_ne i d
      · simp
      · have := hd i h
        simp [Subsingleton.elim x 0])

/-- The equivalence with a single surviving summand is the projection to that summand. -/
@[simp]
theorem DirectSum.componentLinearEquiv_apply (d : ι) (hd : ∀ i, i ≠ d → Subsingleton (M i))
    (x : ⨁ i, M i) :
    DirectSum.componentLinearEquiv (R := R) M d hd x = DirectSum.component R ι M d x :=
  (rfl)

/-- Its inverse is the inclusion of that summand. -/
@[simp]
theorem DirectSum.componentLinearEquiv_symm_apply (d : ι) (hd : ∀ i, i ≠ d → Subsingleton (M i))
    (x : M d) :
    (DirectSum.componentLinearEquiv (R := R) M d hd).symm x = DirectSum.lof R ι M d x :=
  (rfl)

omit [DecidableEq ι] in
/-- A direct sum whose potentially nontrivial summands lie in a finite set and are finite modules
is a finite module, even though the index type may be infinite. -/
theorem DirectSum.finite_of_subsingleton_notMem (s : Finset ι)
    [∀ i : s, Module.Finite R (M i)] (hs : ∀ i ∉ s, Subsingleton (M i)) :
    Module.Finite R (⨁ i, M i) := by
  classical
  exact Module.Finite.equiv (DirectSum.restrictLinearEquiv M s hs).symm

omit [DecidableEq ι] in
/-- **The dimension of a direct sum with finitely many nonzero summands.**  Unlike
`Module.finrank_directSum`, the index type here may be infinite; what is asked instead is a finite
set of finite free summands outside which the summands are trivial. -/
theorem finrank_directSum_eq_sum [StrongRankCondition R] (s : Finset ι)
    [∀ i : s, Module.Free R (M i)] [∀ i : s, Module.Finite R (M i)]
    (hs : ∀ i ∉ s, Subsingleton (M i)) :
    Module.finrank R (⨁ i, M i) = ∑ i ∈ s, Module.finrank R (M i) := by
  classical
  rw [(DirectSum.restrictLinearEquiv M s hs).finrank_eq, Module.finrank_directSum,
    Finset.sum_coe_sort s fun i ↦ Module.finrank R (M i)]

end Restriction

end TauCeti
