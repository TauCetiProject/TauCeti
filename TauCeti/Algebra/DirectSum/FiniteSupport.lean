/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.DirectSum.Finite

/-!
# Direct sums whose summands vanish outside a finite set

A direct sum `⨁ i, M i` over an infinite index type still behaves like a finite one as soon as all
but finitely many summands are trivial: a family graded by `ℤ` with finitely many nonzero degrees
is the standard example.  `TauCeti.DirectSum.restrictLinearEquiv` identifies such a direct sum with
the direct sum over a finite set of indices carrying the nonzero summands.  The two consequences
a graded dimension count needs follow: such a direct sum is a finite module, and its dimension is
the finite sum of the dimensions of its summands.  Mathlib's `Module.finrank_directSum` asks the
index type itself to be finite, which a family graded by `ℤ` does not satisfy.  The parallel
count for an *internal* decomposition of a fixed module is in
`TauCeti.LinearAlgebra.Dimension.DirectSum`.

## Main definitions

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

/-- **Restricting a direct sum to a finite set of indices.**  If every summand outside a finite
set `s` is trivial, then `⨁ i, M i` is the direct sum of the summands indexed by `s`. -/
def DirectSum.restrictLinearEquiv (s : Finset ι) (hs : ∀ i ∉ s, Subsingleton (M i)) :
    (⨁ i, M i) ≃ₗ[R] ⨁ i : s, M i :=
  LinearEquiv.ofLinearMap
    (DirectSum.toModule R ι _ fun i ↦
      if h : i ∈ s then DirectSum.lof R s (fun j : s ↦ M j) ⟨i, h⟩ else 0)
    (DirectSum.toModule R s _ fun i ↦ DirectSum.lof R ι M i)
    (DirectSum.linearMap_ext R fun i ↦ LinearMap.ext fun x ↦ by
      simp [DirectSum.toModule_lof, i.2])
    (DirectSum.linearMap_ext R fun i ↦ LinearMap.ext fun x ↦ by
      by_cases h : i ∈ s
      · simp [DirectSum.toModule_lof, h]
      · have := hs i h
        rw [Subsingleton.elim x 0]
        simp)

/-- The restriction equivalence sends the summand at an index of `s` to the same summand. -/
@[simp]
theorem DirectSum.restrictLinearEquiv_lof (s : Finset ι) (hs : ∀ i ∉ s, Subsingleton (M i))
    {i : ι} (hi : i ∈ s) (x : M i) :
    DirectSum.restrictLinearEquiv (R := R) M s hs (DirectSum.lof R ι M i x) =
      DirectSum.lof R s (fun j : s ↦ M j) ⟨i, hi⟩ x := by
  refine (DirectSum.toModule_lof (φ := fun i ↦
    if h : i ∈ s then DirectSum.lof R s (fun j : s ↦ M j) ⟨i, h⟩ else 0) R i x).trans ?_
  simp [hi]

/-- The restriction equivalence is inverse to the evident inclusion of the summands indexed by
`s`. -/
@[simp]
theorem DirectSum.restrictLinearEquiv_symm_lof (s : Finset ι) (hs : ∀ i ∉ s, Subsingleton (M i))
    (i : s) (x : M i) :
    (DirectSum.restrictLinearEquiv (R := R) M s hs).symm
        (DirectSum.lof R s (fun j : s ↦ M j) i x) = DirectSum.lof R ι M i x :=
  DirectSum.toModule_lof (φ := fun i : s ↦ DirectSum.lof R ι M i) R i x

/-- **A direct sum concentrated in a single index is that summand.**  This is the extreme case of
`TauCeti.DirectSum.restrictLinearEquiv`, in the form in which a grading concentrated in one degree
meets it. -/
def DirectSum.componentLinearEquiv (d : ι) (hd : ∀ i, i ≠ d → Subsingleton (M i)) :
    (⨁ i, M i) ≃ₗ[R] M d :=
  LinearEquiv.ofLinearMap (DirectSum.component R ι M d) (DirectSum.lof R ι M d)
    (LinearMap.ext fun x ↦ by simp)
    (DirectSum.linearMap_ext R fun i ↦ LinearMap.ext fun x ↦ by
      by_cases h : i = d
      · subst h
        simp
      · have := hd i h
        rw [Subsingleton.elim x 0]
        simp)

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
/-- A direct sum of finite modules whose summands are trivial outside a finite set of indices is
a finite module, even though the index type may be infinite. -/
theorem DirectSum.finite_of_subsingleton_notMem [∀ i, Module.Finite R (M i)] (s : Finset ι)
    (hs : ∀ i ∉ s, Subsingleton (M i)) : Module.Finite R (⨁ i, M i) := by
  classical
  exact Module.Finite.equiv (DirectSum.restrictLinearEquiv M s hs).symm

end Restriction

section Finrank

variable {K : Type u} [DivisionRing K] (M : ι → Type w) [∀ i, AddCommGroup (M i)]
  [∀ i, Module K (M i)] [∀ i, Module.Finite K (M i)]

omit [DecidableEq ι] in
/-- **The dimension of a direct sum with finitely many nonzero summands.**  Unlike
`Module.finrank_directSum`, the index type here may be infinite; what is asked instead is a finite
set of indices outside which the summands are trivial. -/
theorem finrank_directSum_eq_sum (s : Finset ι) (hs : ∀ i ∉ s, Subsingleton (M i)) :
    Module.finrank K (⨁ i, M i) = ∑ i ∈ s, Module.finrank K (M i) := by
  classical
  rw [(DirectSum.restrictLinearEquiv M s hs).finrank_eq, Module.finrank_directSum]
  exact Finset.sum_coe_sort s fun i ↦ Module.finrank K (M i)

end Finrank

end TauCeti
