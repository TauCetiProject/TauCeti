/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Antidiagonal
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Tactic.Abel

/-!
# Height in a freely generated additive cone

For a family `v` independent over `ℕ`, its `ℕ`-span is a free additive cone. Its height is the
sum of its unique nonnegative coordinates. Height is additive, vanishes only at zero, and
has finite sublevel sets when the family is finite. In an additive group the cone is pointed,
and translating its bounded-height pieces gives finite lower intervals.

The final result proves finiteness of the pairs of weights in two translated negative cones
with a prescribed sum. This is the local finiteness needed to convolve cone-supported series.
No positive-definite form or nonsingular Cartan matrix is needed: for simple roots one uses
independence in the full weight space, not independence after restriction to the coroot span.

The construction uses `LinearIndependent.repr` and `Finsupp.degree`; bounded-height finiteness
is transported from `Finsupp.finite_of_degree_le`.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, §§1.1 and 9.1,
  for the positive root cone and the order on weights.
-/

public section

namespace LinearIndependent

variable {ι M : Type*}

section Monoid

variable [AddCommMonoid M] {v : ι → M}

/-- The height of an element of the nonnegative span of an independent family is the sum of
its coordinates. For simple roots, this is the usual root height on the positive root cone. -/
noncomputable def natSpanHeight (hv : LinearIndependent ℕ v) :
    Submodule.span ℕ (Set.range v) →+ ℕ :=
  Finsupp.degree.comp hv.repr.toAddMonoidHom

/-- Height is computed by the unique nonnegative coordinates. -/
theorem natSpanHeight_apply (hv : LinearIndependent ℕ v)
    (x : Submodule.span ℕ (Set.range v)) :
    hv.natSpanHeight x = (hv.repr x).degree := (rfl)

/-- The height of a linear combination is the sum of its coefficients. -/
@[simp]
theorem natSpanHeight_linearCombinationEquiv (hv : LinearIndependent ℕ v) (c : ι →₀ ℕ) :
    hv.natSpanHeight (hv.linearCombinationEquiv c) = c.degree := by
  rw [natSpanHeight_apply, hv.repr_eq (hv.linearCombinationEquiv_apply_coe c).symm]

/-- Each generator has height one. -/
@[simp]
theorem natSpanHeight_generator (hv : LinearIndependent ℕ v) (i : ι) :
    hv.natSpanHeight ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩ = 1 := by
  rw [natSpanHeight_apply, hv.repr_eq_single i _ rfl, Finsupp.degree_single]

/-- Zero is the only element of height zero in an independent nonnegative span. -/
@[simp]
theorem natSpanHeight_eq_zero_iff (hv : LinearIndependent ℕ v)
    (x : Submodule.span ℕ (Set.range v)) : hv.natSpanHeight x = 0 ↔ x = 0 := by
  rw [natSpanHeight_apply, Finsupp.degree_eq_zero_iff]
  constructor
  · intro hx
    apply Subtype.ext
    rw [← hv.linearCombination_repr x, hx, map_zero]
    rfl
  · rintro rfl
    exact map_zero _

/-- A finite independent family has only finitely many nonnegative combinations of bounded
height. The ambient monoid need not be finite or finitely generated. -/
theorem finite_natSpanHeight_le [Finite ι] (hv : LinearIndependent ℕ v) (n : ℕ) :
    {x : Submodule.span ℕ (Set.range v) | hv.natSpanHeight x ≤ n}.Finite := by
  refine ((Finsupp.finite_of_degree_le (σ := ι) n).image hv.linearCombinationEquiv).subset ?_
  intro x hx
  refine ⟨hv.repr x, hx, ?_⟩
  exact hv.linearCombinationEquiv.apply_symm_apply x

/-- There are only finitely many decompositions of an element of an independent cone
as a sum of two elements of that cone, even when the generating family is infinite. -/
theorem finite_natSpan_antidiagonal (hv : LinearIndependent ℕ v)
    (z : Submodule.span ℕ (Set.range v)) :
    {p : Submodule.span ℕ (Set.range v) × Submodule.span ℕ (Set.range v) |
      p.1 + p.2 = z}.Finite := by
  classical
  refine ((Finset.antidiagonal (hv.repr z)).finite_toSet.image
    (fun p ↦ (hv.linearCombinationEquiv p.1, hv.linearCombinationEquiv p.2))).subset ?_
  rintro ⟨x, y⟩ hxy
  refine ⟨(hv.repr x, hv.repr y), ?_, ?_⟩
  · simp only [Finset.mem_coe, Finset.mem_antidiagonal]
    rw [← map_add, hxy]
  · exact Prod.ext (hv.linearCombinationEquiv.apply_symm_apply x)
      (hv.linearCombinationEquiv.apply_symm_apply y)

end Monoid

section Group

variable [AddCommGroup M] {v : ι → M}

/-- The nonnegative span of an independent family is pointed: if both `x` and `-x` belong
to it, then `x = 0`. -/
theorem eq_zero_of_mem_natSpan_of_neg_mem (hv : LinearIndependent ℕ v) {x : M}
    (hx : x ∈ Submodule.span ℕ (Set.range v))
    (hnx : -x ∈ Submodule.span ℕ (Set.range v)) : x = 0 := by
  let a : Submodule.span ℕ (Set.range v) := ⟨x, hx⟩
  let b : Submodule.span ℕ (Set.range v) := ⟨-x, hnx⟩
  have hab : a + b = 0 := Subtype.ext (add_neg_cancel x)
  have h := congrArg hv.natSpanHeight hab
  rw [map_add, map_zero] at h
  have ha : a = 0 := (hv.natSpanHeight_eq_zero_iff a).mp (by omega)
  exact congrArg Subtype.val ha

/-- Subtracting a bounded-height element of a finite independent cone from a fixed weight
produces only finitely many weights. -/
theorem finite_sub_natSpanHeight_le [Finite ι] (hv : LinearIndependent ℕ v) (lam : M) (n : ℕ) :
    {μ : M | ∃ β : Submodule.span ℕ (Set.range v),
      μ = lam - β ∧ hv.natSpanHeight β ≤ n}.Finite := by
  refine ((hv.finite_natSpanHeight_le n).image
    (fun β : Submodule.span ℕ (Set.range v) ↦ lam - (β : M))).subset ?_
  rintro μ ⟨β, rfl, hβ⟩
  exact ⟨β, hβ, rfl⟩

/-- The cone order on weights is antisymmetric, even if a Cartan matrix describing their
pairings with simple coroots is singular. -/
theorem eq_of_sub_mem_natSpan_of_sub_mem (hv : LinearIndependent ℕ v) {lam μ : M}
    (h₁ : lam - μ ∈ Submodule.span ℕ (Set.range v))
    (h₂ : μ - lam ∈ Submodule.span ℕ (Set.range v)) : lam = μ := by
  apply sub_eq_zero.mp
  exact hv.eq_zero_of_mem_natSpan_of_neg_mem h₁ (by simpa using h₂)

/-- Only finitely many pairs in two translated negative cones have a prescribed sum.
This gives finite convolution coefficients for functions supported in such cones. -/
theorem finite_pairs_sub_mem_natSpan (hv : LinearIndependent ℕ v) (lam μ ξ : M) :
    {p : M × M | lam - p.1 ∈ Submodule.span ℕ (Set.range v) ∧
      μ - p.2 ∈ Submodule.span ℕ (Set.range v) ∧ p.1 + p.2 = ξ}.Finite := by
  by_cases hz : lam + μ - ξ ∈ Submodule.span ℕ (Set.range v)
  · let z : Submodule.span ℕ (Set.range v) := ⟨lam + μ - ξ, hz⟩
    refine ((hv.finite_natSpan_antidiagonal z).image
      (fun p ↦ (lam - (p.1 : M), μ - (p.2 : M)))).subset ?_
    rintro ⟨x, y⟩ ⟨hx, hy, hxy⟩
    refine ⟨(⟨lam - x, hx⟩, ⟨μ - y, hy⟩), ?_, ?_⟩
    · apply Subtype.ext
      dsimp [z]
      rw [← hxy]
      abel
    · simp
  · have hempty : {p : M × M | lam - p.1 ∈ Submodule.span ℕ (Set.range v) ∧
        μ - p.2 ∈ Submodule.span ℕ (Set.range v) ∧ p.1 + p.2 = ξ} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ⟨x, y⟩ ⟨hx, hy, hxy⟩
      apply hz
      convert Submodule.add_mem (Submodule.span ℕ (Set.range v)) hx hy using 1
      rw [← hxy]
      abel
    rw [hempty]
    exact Set.finite_empty

end Group

end LinearIndependent
