/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import TauCeti.RingTheory.Idempotents.Corner.Basic

/-!
# The two-sided Peirce decomposition

Let `e₁, …, eₙ` be a complete family of orthogonal idempotents in a semiring `A` that is a module
over a semiring `k` compatibly with multiplication. Every `x ∈ A` is the sum `∑ᵢ ∑ⱼ eᵢ x eⱼ`, and
this decomposition is unique: `A` is the internal direct sum of the corners `eᵢ A eⱼ`
(`TauCeti.cornerSubmodule k (e i) (e j)`), indexed by pairs `(i, j)`. The component of `x` at
`(i, j)` is `eᵢ x eⱼ`.

This is the decomposition in which a generalized matrix algebra is written as a matrix of blocks,
and in which the trace of a block matrix is read off from the diagonal. The one-sided version, the
decomposition `M = ⨁ᵢ eᵢ M` of a module, is `TauCeti.isInternal_smul_top`.

## Main results

* `TauCeti.mul_mem_cornerSubmodule`: the Peirce multiplication rule `(eAf)(fAg) ⊆ eAg`.
* `OrthogonalIdempotents.mul_coeLinearMap_cornerSubmodule_mul`: cutting a sum of elements
  `zᵢⱼ ∈ eᵢ A eⱼ` down by `eₖ` on the left and `eₗ` on the right recovers `zₖₗ`.
* `CompleteOrthogonalIdempotents.isInternal_cornerSubmodule`: **the two-sided Peirce
  decomposition** `A = ⨁_{(i, j)} eᵢ A eⱼ`.
* `CompleteOrthogonalIdempotents.coe_ofBijective_coeLinearMap_cornerSubmodule_symm_apply`: the
  component of `x` at `(i, j)` is `eᵢ x eⱼ`.

## References

* T. Y. Lam, *A First Course in Noncommutative Rings*, 2nd ed., Graduate Texts in Mathematics 131,
  Springer, 2001, §21.
-/

public section

open scoped DirectSum

namespace TauCeti

/-- **The Peirce multiplication rule** `(eAf)(fAg) ⊆ eAg`. No idempotency is needed. -/
theorem mul_mem_cornerSubmodule {k A : Type*} [Semiring k] [NonUnitalSemiring A] [Module k A]
    [SMulCommClass k A A] [IsScalarTower k A A] {e f g x y : A}
    (hx : x ∈ cornerSubmodule k e f) (hy : y ∈ cornerSubmodule k f g) :
    x * y ∈ cornerSubmodule k e g := by
  rw [cornerSubmodule_def, LinearMap.mem_range] at hx hy
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  simp only [LinearMap.mulLeftRight_apply]
  have h : e * a * f * (f * b * g) = e * (a * f * (f * b)) * g := by simp only [mul_assoc]
  rw [h]
  exact mul_mul_mem_cornerSubmodule k e g _

end TauCeti

namespace OrthogonalIdempotents

variable {k A ι : Type*} [Semiring k] [Semiring A] [Module k A] [SMulCommClass k A A]
  [IsScalarTower k A A] {e : ι → A}

/-- An element of the corner `eᵢ A eⱼ` is killed on the left by every `eₖ` with `k ≠ i`. -/
theorem mul_eq_zero_of_mem_cornerSubmodule (he : OrthogonalIdempotents e) {i j l : ι}
    (hli : l ≠ i) {x : A} (hx : x ∈ TauCeti.cornerSubmodule k (e i) (e j)) : e l * x = 0 := by
  rw [← TauCeti.mul_eq_self_of_mem_cornerSubmodule (he.idem i) hx, ← mul_assoc, he.ortho hli,
    zero_mul]

/-- An element of the corner `eᵢ A eⱼ` is killed on the right by every `eₗ` with `l ≠ j`. -/
theorem mul_eq_zero_of_mem_cornerSubmodule_right (he : OrthogonalIdempotents e) {i j l : ι}
    (hjl : j ≠ l) {x : A} (hx : x ∈ TauCeti.cornerSubmodule k (e i) (e j)) : x * e l = 0 := by
  rw [← TauCeti.mul_eq_self_of_mem_cornerSubmodule_right (he.idem j) hx, mul_assoc, he.ortho hjl,
    mul_zero]

/-- **Cutting a sum down to one corner reads off a component**: if `z` is a family of elements
`zᵢⱼ ∈ eᵢ A eⱼ`, then `eₖ (∑ zᵢⱼ) eₗ = zₖₗ`. This is what makes the two-sided Peirce
decomposition direct. -/
theorem mul_coeLinearMap_cornerSubmodule_mul [DecidableEq ι] (he : OrthogonalIdempotents e)
    (z : ⨁ p : ι × ι, TauCeti.cornerSubmodule k (e p.1) (e p.2)) (i j : ι) :
    e i * DirectSum.coeLinearMap (fun p : ι × ι ↦ TauCeti.cornerSubmodule k (e p.1) (e p.2)) z *
      e j = (z (i, j) : A) := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | of p x =>
    obtain ⟨i', j'⟩ := p
    obtain ⟨x, hx⟩ := x
    rw [DirectSum.coeLinearMap_of]
    rcases eq_or_ne (i, j) (i', j') with h | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      rw [DirectSum.of_eq_same, (TauCeti.mem_cornerSubmodule_iff k (he.idem i) (he.idem j)).1 hx]
    · rw [DirectSum.of_eq_of_ne _ _ _ h, ZeroMemClass.coe_zero]
      rcases eq_or_ne i i' with rfl | hi
      · have hj : j' ≠ j := fun hj ↦ h (by rw [hj])
        rw [mul_assoc, he.mul_eq_zero_of_mem_cornerSubmodule_right hj hx, mul_zero]
      · rw [he.mul_eq_zero_of_mem_cornerSubmodule hi hx, zero_mul]
  | add z w hz hw =>
    rw [map_add, mul_add, add_mul, hz, hw, DFinsupp.add_apply, Submodule.coe_add]

end OrthogonalIdempotents

namespace CompleteOrthogonalIdempotents

variable {k A ι : Type*} [Semiring k] [Semiring A] [Module k A] [SMulCommClass k A A]
  [IsScalarTower k A A] [Fintype ι] {e : ι → A}

/-- Every element is the sum of its cuts by a complete family of orthogonal idempotents:
`x = ∑ᵢ ∑ⱼ eᵢ x eⱼ`. Only completeness `∑ᵢ eᵢ = 1` is used. -/
theorem sum_sum_mul_mul (he : CompleteOrthogonalIdempotents e) (x : A) :
    ∑ i, ∑ j, e i * x * e j = x := by
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul, he.complete, one_mul, mul_one]

variable [DecidableEq ι]

/-- **The two-sided Peirce decomposition.** A complete family of orthogonal idempotents decomposes
`A` as the internal direct sum `A = ⨁_{(i, j)} eᵢ A eⱼ` of its corners. -/
theorem isInternal_cornerSubmodule (he : CompleteOrthogonalIdempotents e) :
    DirectSum.IsInternal fun p : ι × ι ↦ TauCeti.cornerSubmodule k (e p.1) (e p.2) := by
  -- Injectivity: each component is recovered by cutting down to its corner. Surjectivity: the
  -- terms of `x = ∑ᵢ ∑ⱼ eᵢ x eⱼ` lie in the corners.
  refine ⟨fun z w hzw ↦ DFinsupp.ext fun p ↦ Subtype.ext ?_, ?_⟩
  · replace hzw : DirectSum.coeLinearMap
        (fun p : ι × ι ↦ TauCeti.cornerSubmodule k (e p.1) (e p.2)) z =
        DirectSum.coeLinearMap (fun p : ι × ι ↦ TauCeti.cornerSubmodule k (e p.1) (e p.2)) w :=
      hzw
    rw [← he.toOrthogonalIdempotents.mul_coeLinearMap_cornerSubmodule_mul z p.1 p.2,
      ← he.toOrthogonalIdempotents.mul_coeLinearMap_cornerSubmodule_mul w p.1 p.2, hzw]
  · refine (LinearMap.range_eq_top (f := DirectSum.coeLinearMap
      fun p : ι × ι ↦ TauCeti.cornerSubmodule k (e p.1) (e p.2))).1 ?_
    rw [DirectSum.range_coeLinearMap, eq_top_iff]
    intro x _
    rw [← he.sum_sum_mul_mul x]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.sum_mem _ fun j _ ↦
      Submodule.mem_iSup_of_mem (i, j) (TauCeti.mul_mul_mem_cornerSubmodule k _ _ x)

/-- **The `(i, j)` component of `x` in the two-sided Peirce decomposition is `eᵢ x eⱼ`.** The
isomorphism `⨁_{(i, j)} eᵢ A eⱼ ≃ₗ[k] A` is the canonical
`LinearEquiv.ofBijective (DirectSum.coeLinearMap _)` of an internal direct sum. -/
@[simp]
theorem coe_ofBijective_coeLinearMap_cornerSubmodule_symm_apply
    (he : CompleteOrthogonalIdempotents e) (x : A) (p : ι × ι) :
    (((LinearEquiv.ofBijective
      (DirectSum.coeLinearMap fun p : ι × ι ↦ TauCeti.cornerSubmodule k (e p.1) (e p.2))
      he.isInternal_cornerSubmodule).symm x p : TauCeti.cornerSubmodule k (e p.1) (e p.2)) : A) =
      e p.1 * x * e p.2 := by
  -- `LinearEquiv.ofBijective f _` has `f` as its underlying function.
  have h : DirectSum.coeLinearMap (fun p : ι × ι ↦ TauCeti.cornerSubmodule k (e p.1) (e p.2))
      ((LinearEquiv.ofBijective
        (DirectSum.coeLinearMap fun p : ι × ι ↦ TauCeti.cornerSubmodule k (e p.1) (e p.2))
        he.isInternal_cornerSubmodule).symm x) = x :=
    (LinearEquiv.ofBijective
      (DirectSum.coeLinearMap fun p : ι × ι ↦ TauCeti.cornerSubmodule k (e p.1) (e p.2))
      he.isInternal_cornerSubmodule).apply_symm_apply x
  rw [← he.toOrthogonalIdempotents.mul_coeLinearMap_cornerSubmodule_mul _ p.1 p.2, h]

end CompleteOrthogonalIdempotents
