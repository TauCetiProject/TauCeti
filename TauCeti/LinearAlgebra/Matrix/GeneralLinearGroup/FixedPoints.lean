/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `OnePoint K` with the Möbius action of `GL (Fin 2) K` is the model of the projective line used
-- here, and `Matrix.GeneralLinearGroup.fixpointPolynomial_aeval_eq_zero_iff` is what reads the
-- affine fixed points off a polynomial.
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
-- `Matrix.ProjGenLinGroup.mk` occurs in the statements below, and `OnePoint.instMulActionPGL` is
-- the action of `PGL(2, K)` on the projective line that the statements about an element of
-- `PGL(2, K)` use.
public import TauCeti.Topology.Compactification.OnePoint.ProjectiveLine
-- `Set.ncard` occurs in the statements below.
public import Mathlib.Data.Set.Card
-- Non-public: `Polynomial.natDegree_linear_le` and `Polynomial.natDegree_quadratic_le` bound the
-- degree of the fixed-point polynomial, in the proof only.
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-!
# Fixed points of the Möbius action on the projective line

An invertible `2 × 2` matrix acts on the projective line `ℙ¹(K)`, modelled by `OnePoint K`, by the
Möbius transformation `t ↦ (a t + b) / (c t + d)`. Its fixed points in the affine part are the
roots of Mathlib's `Matrix.GeneralLinearGroup.fixpointPolynomial`, which is
`c X² + (d − a) X − b`, of degree at most two, and `∞` is fixed exactly when `c = 0`. The
polynomial vanishes identically exactly for a scalar matrix, which fixes everything.

So a matrix that is not scalar fixes **at most two** points of `ℙ¹(K)`: if it fixes `∞` the
polynomial has degree at most one, so it contributes at most one more point, and otherwise all the
fixed points are among its at most two roots. Contrapositively, a matrix fixing three distinct
points of `ℙ¹(K)` is scalar, so an element of `PGL₂(K)` fixing three distinct points is trivial,
and two elements agreeing on three distinct points are equal. This **three-point rigidity** is what
makes a subgroup of `PGL₂(K)` embed into the permutations of any invariant set of at least three
points of `ℙ¹(K)`.

## Main results

* `Matrix.GeneralLinearGroup.encard_fixedBy_le_two`, with the `Set.ncard` form
  `Matrix.GeneralLinearGroup.ncard_fixedBy_le_two`: a matrix that is not scalar fixes at most two
  points of the projective line.
* `Matrix.GeneralLinearGroup.mem_center_of_forall_smul_eq`: a matrix fixing a set of at least three
  points of the projective line is scalar, hence central.  The hypothesis is on `Set.encard`, which
  measures an infinite set of fixed points correctly.
* `Matrix.ProjGenLinGroup.eq_one_of_forall_smul_eq` and
  `Matrix.ProjGenLinGroup.eq_of_forall_smul_eq`: **three-point rigidity in `PGL₂(K)`**, and the
  uniqueness form — two elements acting the same way on a set of at least three points of the
  projective line are equal.  For a matrix `g`, `OnePoint.pglMk_smul` turns a hypothesis about the
  Möbius action of `g` into one about the action of its class.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Exercise 1.2.
-/

public section

open OnePoint Polynomial

open scoped MatrixGroups

namespace Matrix.GeneralLinearGroup

section Field

variable {K : Type*} [Field K] [DecidableEq K] {g : GL (Fin 2) K}

/-- The fixed points of a matrix that is not scalar are contained in a set of at most two points of
the projective line: the roots of its fixed-point polynomial, together with `∞` when that is
fixed. -/
private theorem exists_finset_fixedBy_subset (hg : g ∉ Subgroup.center (GL (Fin 2) K)) :
    ∃ s : Finset (OnePoint K), s.card ≤ 2 ∧ MulAction.fixedBy (OnePoint K) g ⊆ ↑s := by
  classical
  have hzero : g.fixpointPolynomial ≠ 0 := fun h ↦
    hg (mem_center_iff_val_mem_range_scalar.mpr (fixpointPolynomial_eq_zero_iff.mp h))
  have hroot : ∀ t : K, g • (t : OnePoint K) = t → t ∈ g.fixpointPolynomial.roots := fun t ht ↦ by
    rw [mem_roots hzero, IsRoot]
    simpa using fixpointPolynomial_aeval_eq_zero_iff.mpr ht
  set s : Finset (OnePoint K) :=
    g.fixpointPolynomial.roots.toFinset.image (fun t : K ↦ (t : OnePoint K))
  have hcard : s.card ≤ g.fixpointPolynomial.natDegree :=
    Finset.card_image_le.trans ((Multiset.toFinset_card_le _).trans (card_roots' _))
  by_cases hinfty : g 1 0 = 0
  · refine ⟨insert ∞ s, ?_, ?_⟩
    · -- With `∞` fixed the fixed-point polynomial is linear, so it has at most one root.
      have hdeg : g.fixpointPolynomial.natDegree ≤ 1 := by
        rw [fixpointPolynomial, hinfty, map_zero, zero_mul, zero_add, sub_eq_add_neg, ← C_neg]
        exact natDegree_linear_le
      exact (Finset.card_insert_le _ _).trans (by omega)
    · intro c hc
      cases c with
      | infty => exact Finset.mem_insert_self _ _
      | coe t =>
        refine Finset.mem_insert_of_mem ?_
        exact Finset.mem_image_of_mem _ (Multiset.mem_toFinset.mpr (hroot t hc))
  · -- Otherwise every fixed point is a root of the quadratic fixed-point polynomial.
    have hdeg : g.fixpointPolynomial.natDegree ≤ 2 := by
      rw [fixpointPolynomial, sub_eq_add_neg, ← C_neg]
      exact natDegree_quadratic_le
    refine ⟨s, hcard.trans hdeg, ?_⟩
    intro c hc
    cases c with
    | infty => exact absurd (smul_infty_eq_self_iff.mp hc) hinfty
    | coe t => exact Finset.mem_image_of_mem _ (Multiset.mem_toFinset.mpr (hroot t hc))

/-- The fixed points of a matrix that is not scalar form a finite subset of the projective
line. -/
theorem finite_fixedBy_of_notMem_center (hg : g ∉ Subgroup.center (GL (Fin 2) K)) :
    (MulAction.fixedBy (OnePoint K) g).Finite := by
  obtain ⟨s, -, hsub⟩ := exists_finset_fixedBy_subset hg
  exact s.finite_toSet.subset hsub

/-- **A matrix that is not scalar fixes at most two points of the projective line**: its fixed
points are among the at most two roots of its fixed-point polynomial, and `∞` is fixed only when
that polynomial has degree at most one. -/
theorem encard_fixedBy_le_two (hg : g ∉ Subgroup.center (GL (Fin 2) K)) :
    (MulAction.fixedBy (OnePoint K) g).encard ≤ 2 := by
  obtain ⟨s, hcard, hsub⟩ := exists_finset_fixedBy_subset hg
  refine (Set.encard_le_encard hsub).trans ?_
  rw [Set.encard_coe_eq_coe_finsetCard]
  exact_mod_cast hcard

/-- The `Set.ncard` form of `Matrix.GeneralLinearGroup.encard_fixedBy_le_two`, for counting
arguments on the finite fixed-point set of a matrix that is not scalar. -/
theorem ncard_fixedBy_le_two (hg : g ∉ Subgroup.center (GL (Fin 2) K)) :
    (MulAction.fixedBy (OnePoint K) g).ncard ≤ 2 := by
  obtain ⟨s, hcard, hsub⟩ := exists_finset_fixedBy_subset hg
  refine (Set.ncard_le_ncard hsub s.finite_toSet).trans ?_
  rwa [Set.ncard_coe_finset]

/-- A matrix fixing at least three points of the projective line is central.  The count is
`Set.encard`, so an infinite fixed-point set satisfies the hypothesis. -/
theorem mem_center_of_three_le_encard_fixedBy
    (h : 3 ≤ (MulAction.fixedBy (OnePoint K) g).encard) : g ∈ Subgroup.center (GL (Fin 2) K) := by
  by_contra hg
  exact absurd (h.trans (encard_fixedBy_le_two hg)) (by norm_num)

/-- **Three-point rigidity**: a matrix fixing a set of at least three points of the projective line
is scalar, hence central in `GL₂(K)`. -/
theorem mem_center_of_forall_smul_eq {S : Set (OnePoint K)} (hS : ∀ c ∈ S, g • c = c)
    (hcard : 3 ≤ S.encard) : g ∈ Subgroup.center (GL (Fin 2) K) :=
  mem_center_of_three_le_encard_fixedBy
    (hcard.trans (Set.encard_le_encard fun c hc ↦ hS c hc))

end Field

end Matrix.GeneralLinearGroup

namespace Matrix.ProjGenLinGroup

variable {K : Type*} [Field K] [DecidableEq K]

/-- **Three-point rigidity in `PGL₂(K)`**: an element of `PGL₂(K)` fixing a set of at least three
points of the projective line is the identity. -/
theorem eq_one_of_forall_smul_eq {x : PGL(2, K)} {S : Set (OnePoint K)} (hS : ∀ c ∈ S, x • c = c)
    (hcard : 3 ≤ S.encard) : x = 1 := by
  obtain ⟨g, rfl⟩ := mk_surjective x
  exact mk_eq_one.mpr (GeneralLinearGroup.mem_center_of_forall_smul_eq
    (fun c hc ↦ by simpa using hS c hc) hcard)

/-- **A Möbius transformation is determined by three points**: two elements of `PGL₂(K)` acting the
same way on a set of at least three points of the projective line are equal. -/
theorem eq_of_forall_smul_eq {x y : PGL(2, K)} {S : Set (OnePoint K)} (hS : ∀ c ∈ S, x • c = y • c)
    (hcard : 3 ≤ S.encard) : x = y := by
  have key : ∀ c ∈ S, (y⁻¹ * x) • c = c := fun c hc ↦ by
    rw [mul_smul, hS c hc, ← mul_smul, inv_mul_cancel, one_smul]
  have hone := eq_one_of_forall_smul_eq key hcard
  rw [inv_mul_eq_one] at hone
  exact hone.symm

end Matrix.ProjGenLinGroup
