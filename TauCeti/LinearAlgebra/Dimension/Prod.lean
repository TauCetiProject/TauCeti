/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.RankNullity

import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod
import Mathlib.RingTheory.Finiteness.Prod

/-!
# Dimensions of products of modules

Mathlib's `Module.finrank_prod` and `Module.finrank_pi_fintype` compute the `finrank` of binary
and finite dependent products of finite free modules. This file records three relaxations:

* For the square `M × M` of a free module over a semiring with the strong rank condition, no
  finiteness is needed: if `M` is not finite then neither is `M × M`, and both dimensions are `0`
  by convention (`Module.finrank_prod_self`).
* A free module of positive dimension is finite, so the dimensions of factors of dimensions
  `m + 1` and `n + 1` add without a separate finiteness hypothesis
  (`Module.finrank_prod_eq_succ`). The sum is written `d + 1` together with a proof of
  `(m + 1) + (n + 1) = d + 1`, the form used for products of local orientations.
* Over a ring satisfying the strong rank condition and rank--nullity (`HasRankNullity`), such as a
  division ring or a commutative domain, no freeness is needed: the `finrank` of a binary product
  (`Module.finrank_prod_of_hasRankNullity`) or a finite dependent product
  (`Module.finrank_pi_fintype_of_hasRankNullity`) of finitely generated modules is the sum of their
  `finrank`s, covering finitely generated modules with torsion (such as finite abelian groups).
-/

public section

universe u v w

namespace Module

section Free

variable (R M : Type*) [Semiring R] [StrongRankCondition R] [AddCommMonoid M] [Module R M]
  [Module.Free R M]

/-- The dimension of `M × M` is twice that of `M`, whether or not `M` is finite. -/
theorem finrank_prod_self : finrank R (M × M) = 2 * finrank R M := by
  by_cases hM : Module.Finite R M
  · rw [Module.finrank_prod, two_mul]
  · have : ¬ Module.Finite R (M × M) := fun h =>
      hM (Module.Finite.of_surjective (LinearMap.fst R M M) Prod.fst_surjective)
    rw [finrank_of_not_finite hM, finrank_of_not_finite this, mul_zero]

variable {R M} {M' : Type*} [AddCommMonoid M'] [Module R M'] [Module.Free R M'] {m n d : ℕ}

/-- If `M` and `M'` have dimensions `m + 1` and `n + 1`, where `(m + 1) + (n + 1) = d + 1`, then
`M × M'` has dimension `d + 1`. Both factors are finite because their dimensions are positive. -/
theorem finrank_prod_eq_succ (hM : finrank R M = m + 1) (hM' : finrank R M' = n + 1)
    (hd : m + 1 + (n + 1) = d + 1) : finrank R (M × M') = d + 1 := by
  have := finite_of_finrank_eq_succ hM
  have := finite_of_finrank_eq_succ hM'
  rw [Module.finrank_prod, hM, hM', hd]

end Free

section HasRankNullity

/-- Over a ring satisfying the strong rank condition and rank--nullity, the `finrank` of a product
of two finitely generated modules is the sum of their `finrank`s (without assuming freeness). -/
theorem finrank_prod_of_hasRankNullity {R : Type u} {M : Type v} {N : Type w}
    [Ring R] [StrongRankCondition R] [HasRankNullity.{max v w} R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N] :
    finrank R (M × N) = finrank R M + finrank R N := by
  have h := (LinearMap.ker (LinearMap.fst R M N)).finrank_quotient_add_finrank
  rw [((LinearMap.fst R M N).quotKerEquivOfSurjective Prod.fst_surjective).finrank_eq,
    LinearMap.ker_fst, ← (LinearEquiv.ofInjective _ LinearMap.inr_injective).finrank_eq] at h
  exact h.symm

/-- Over a ring satisfying the strong rank condition and rank--nullity, the `finrank` of a finite
dependent product of finitely generated modules is the sum of their `finrank`s (without assuming
freeness). The index type `ι` may lie in any universe `w`; only `HasRankNullity.{v} R` is required
in the universe `v` of the modules `M i`. -/
theorem finrank_pi_fintype_of_hasRankNullity {R : Type u} {ι : Type w} [Fintype ι]
    {M : ι → Type v} [Ring R] [StrongRankCondition R] [HasRankNullity.{v} R]
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, Module.Finite R (M i)] :
    finrank R (∀ i, M i) = ∑ i, finrank R (M i) := by
  suffices hfin : ∀ (n : ℕ) (N : Fin n → Type v) [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
      [∀ i, Module.Finite R (N i)],
      finrank R (∀ i, N i) = ∑ i, finrank R (N i) by
    let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
    have : ∀ j, Module.Finite R (M (e j)) := fun j ↦ inferInstance
    rw [(LinearEquiv.piCongrLeft R M e).symm.finrank_eq, hfin (Fintype.card ι) (fun j ↦ M (e j))]
    exact Fintype.sum_equiv e _ _ fun _ ↦ rfl
  intro n
  induction n with
  | zero =>
    intro N _ _ _
    simp [finrank_zero_of_subsingleton]
  | succ n ih =>
    intro N _ _ _
    let e := (LinearEquiv.piCongrLeft' R N (finSuccEquiv n)).trans
      (LinearEquiv.piOptionEquivProd R (M := fun o ↦ N ((finSuccEquiv n).symm o)))
    have : Module.Finite R (∀ j : Fin n, N ((finSuccEquiv n).symm (some j))) :=
      Module.Finite.pi
    rw [e.finrank_eq, finrank_prod_of_hasRankNullity,
      ih (fun j ↦ N ((finSuccEquiv n).symm (some j))), Fin.sum_univ_succ]
    rfl

end HasRankNullity

end Module
