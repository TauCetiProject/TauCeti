/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.GroupTheory.Subgroup.Center
public import TauCeti.GroupTheory.GroupExtension.Of.FactorSet
public import TauCeti.Algebra.GroupAction.Trivial
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.AddHorizontal
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Basic
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Differential
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Horizontal
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.LinearCombination

/-!
# The grading of the strands algebra

The strands algebra `A(n)` of Lipshitz, Ozsváth and Thurston is graded by a nonabelian group
`G'(n)`, a central extension of the relative homology group `H₁([1, n], {1, …, n}) ≅ ℤ ^ (n - 1)`
by the Maslov component. An element of `G'(n)` is a pair `(j, β)` of a half-integer `j` and a
class `β`, and the product is

  `(j₁, β₁) (j₂, β₂) = (j₁ + j₂ + L(β₁, β₂), β₁ + β₂)`,  `L(β₁, β₂) = m(β₂, ∂β₁)`,

where `m(β, p)` is the *multiplicity* of `β` at the point `p`, the average of the multiplicities of
`β` on the two intervals adjacent to `p`, extended linearly to formal sums of points. A strand
diagram `φ : S → T` has the class `[φ]` of its strands, the sum of the intervals `[s, φ s]`, and the
grading

  `gr(φ) = (inv(φ) - m([φ], S), [φ])`.

When the product of two diagrams in the strands algebra is nonzero, the grading is multiplicative,
`gr(φ ψ) = gr(φ) gr(ψ)` (`TauCeti.StrandDiagram.grading_trans`), so the span of the diagrams of
grading `g` is a family of submodules with `A_g A_h ⊆ A_{g h}`
(`TauCeti.StrandsAlgebra.mul_mem_gradedPart`). The central element `λ = (1, 0)` records the Maslov
grading: diagrams with the same source and target differ in grading by the power of `λ` given by
the difference of their crossing numbers (`TauCeti.StrandDiagram.grading_eq_lambda_zpow_mul`), so
the differential, which resolves one crossing, has degree `λ⁻¹`. The graded parts are built from
the parts of an arbitrary function on strand diagrams (`TauCeti.StrandsAlgebra.gradedPartBy`), whose
compatibility with the product and the differential also serves refinements of the grading.

The boundary also measures how far the strands climb: the *length* of a diagram
(`TauCeti.StrandDiagram.length`), the sum over its strands of the number of points each strand
passes, is additive under concatenation and vanishes exactly on the identity diagrams
(`TauCeti.StrandDiagram.length_eq_zero_iff`).

## Conventions

We work, as `TauCeti.StrandsAlgebra` does, with an arbitrary finite linear order `α` in place of
`{1, …, n}`. A class `β ∈ H₁([1, n], {1, …, n})` is recorded by its boundary `∂β`, a function
`α → ℤ`: since `H₁([1, n]) = 0`, the boundary map identifies `H₁([1, n], {1, …, n})` with the
functions of total sum zero. The boundary of the class of a diagram `φ : S → T` is the indicator of
`T` minus that of `S` (`TauCeti.StrandDiagram.boundary`). In these terms the multiplicity is
`m(β, p) = -∑_{y < p} ∂β(y) - ∂β(p) / 2`, and for the class of a diagram this is the average of the
number of strands passing just below and just above `p`
(`TauCeti.StrandDiagram.pointMultiplicity_boundary`). The Maslov component is taken in `ℚ`, and
the grading group is the central extension `TauCeti.FactorSet.Extension` of `α → ℤ` by `ℚ` built
from the bimultiplicative factor set `L` (`TauCeti.StrandGradingGroup.linkingFactorSet`), with the
action trivial, so that `λ` is the image of `1` under its central inclusion `TauCeti.FactorSet.inl`.
Lipshitz, Ozsváth and Thurston's `G'(n)` is the subgroup `TauCeti.StrandGradingGroup.gPrime`
of `TauCeti.StrandGradingGroup (Fin n)` of the elements `(j, β)` with boundary of total sum zero
and `j ≡ ε(β) (mod 1)`, where `ε(β)` is a quarter of the number of points at which `∂β` is odd,
and every grading of a diagram lies in it (`TauCeti.StrandDiagram.grading_mem_gPrime`). Modulo
`1`, `ε(β)` is a quarter of the sum of the squares of the coefficients of `∂β`
(`TauCeti.StrandGradingGroup.mem_gPrime_iff_sum_sq`), and `L(β₁, β₂)` is half the sum of the
products of the coefficients of `∂β₁` and `∂β₂`, which is why the congruence is preserved by the
product.

## Main definitions

* `TauCeti.StrandGradingGroup α`: the grading group, with its group structure.
* `TauCeti.StrandGradingGroup.pointMultiplicity`: the multiplicity `m(β, p)` of a class at a point.
* `TauCeti.StrandGradingGroup.linking`: the bilinear form `L(β₁, β₂) = m(β₂, ∂β₁)`.
* `TauCeti.StrandGradingGroup.linkingFactorSet`: `L` as a factor set for the trivial action.
* `TauCeti.StrandGradingGroup.lambda`: the central element `λ = (1, 0)`.
* `TauCeti.StrandGradingGroup.gPrime`: the subgroup `G'(n)`.
* `TauCeti.StrandDiagram.boundary`: the boundary of the class of the strands of a diagram.
* `TauCeti.StrandDiagram.length`: the total length of the strands of a diagram.
* `TauCeti.StrandDiagram.grading`: the grading `gr(φ)` of a strand diagram.
* `TauCeti.StrandsAlgebra.gradedPartBy`: the elements supported on the diagrams on which a given
  function on strand diagrams takes a given value.
* `TauCeti.StrandsAlgebra.gradedPart`: the elements supported on the diagrams of a given grading.

## Main results

* `TauCeti.StrandDiagram.length_eq_zero_iff`: a diagram has length zero exactly when it is an
  identity diagram.
* `TauCeti.StrandDiagram.trans_eq_idOn_source_iff`: a concatenation is an identity diagram exactly
  when both factors are.
* `TauCeti.StrandGradingGroup.linking_add_linking_swap`, `TauCeti.StrandGradingGroup.linking_self`:
  the symmetric part of `L` is minus the product of the total sums of the boundaries, so `L` is
  antisymmetric on boundaries of total sum zero.
* `TauCeti.StrandGradingGroup.mem_zpowers_lambda_iff`: the elements of `G'(n)` with zero class
  are the powers of `λ`.
* `TauCeti.StrandDiagram.grading_trans`: the grading is multiplicative on composable diagrams.
* `TauCeti.StrandDiagram.grading_idOn`: the identity diagrams have grading `1`.
* `TauCeti.StrandDiagram.grading_mem_gPrime`: every grading of a diagram lies in `G'(n)`.
* `TauCeti.StrandDiagram.grading_eq_lambda_zpow_mul`: diagrams with the same ends differ in
  grading by a power of `λ`.
* `TauCeti.StrandDiagram.grading_addHorizontal`, `TauCeti.StrandDiagram.grading_swapHorizontal`:
  adding horizontal strands away from the ends, or moving a horizontal strand to a free point, does
  not change the grading.
* `TauCeti.StrandDiagram.grading_resolve`, `TauCeti.StrandsAlgebra.differential_mem_gradedPart`:
  every term of the differential of `φ` has grading `λ⁻¹ gr(φ)`, so the differential maps the part
  of grading `g` to the part of grading `λ⁻¹ g`.
* `TauCeti.StrandsAlgebra.mul_mem_gradedPart`, `TauCeti.StrandsAlgebra.one_mem_gradedPart`,
  `TauCeti.StrandsAlgebra.iSup_gradedPart`: the graded parts multiply according to the group law,
  contain the unit in degree `1`, and span the algebra; a strand diagram lies in the part of its
  own grading only (`TauCeti.StrandsAlgebra.of_mem_gradedPart_iff`).
* `TauCeti.StrandsAlgebra.iSupIndep_gradedPart`, `TauCeti.StrandsAlgebra.isInternal_gradedPart`:
  the graded parts are independent, so over a ring the algebra is their internal direct sum.
* `TauCeti.StrandsAlgebra.mem_gradedPart_iff_of_basis`: a linear isomorphism of strands algebras
  given by a bijection of diagrams that transforms gradings by an injective map carries graded parts
  onto graded parts.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §3.3.1 (the
  group `G'(n)` and Lemma 3.35, the multiplicity `m`, the grading of `A(n, k)` and its
  compatibility with the product and the differential) and Proposition 3.40 (the grading is
  unchanged by adding horizontal strands).
-/

public section

open Finset

namespace TauCeti

namespace StrandGradingGroup

variable {α : Type*} [LinearOrder α] [Fintype α]

/-- The multiplicity `m(β, p)` at the point `p` of the class `β` with boundary `δ`: the average
of the multiplicities of `β` on the two intervals adjacent to `p`. In terms of the boundary it is
`-∑_{y < p} δ y - δ p / 2`. -/
def pointMultiplicity (p : α) : (α → ℤ) →+ ℚ where
  toFun δ := -∑ y ∈ ({y | y < p} : Finset α), (δ y : ℚ) - δ p / 2
  map_zero' := by simp
  map_add' δ δ' := by
    simp only [Pi.add_apply, Int.cast_add, Finset.sum_add_distrib]
    ring

theorem pointMultiplicity_apply (p : α) (δ : α → ℤ) :
    pointMultiplicity p δ = -∑ y ∈ ({y | y < p} : Finset α), (δ y : ℚ) - δ p / 2 :=
  (rfl)

/-- The multiplicity `m(β, p)` is a half-integer. -/
theorem exists_pointMultiplicity_eq (p : α) (δ : α → ℤ) :
    ∃ k : ℤ, pointMultiplicity p δ = k / 2 :=
  ⟨-2 * ∑ y ∈ ({y | y < p} : Finset α), δ y - δ p, by
    rw [pointMultiplicity_apply]
    push_cast
    ring⟩

/-- The bilinear form `L(β₁, β₂) = m(β₂, ∂β₁)` of Lipshitz, Ozsváth and Thurston, which
defines the product of the grading group. -/
def linking : (α → ℤ) →+ (α → ℤ) →+ ℚ where
  toFun δ₁ := ∑ p, δ₁ p • pointMultiplicity p
  map_zero' := by simp
  map_add' δ₁ δ₂ := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem linking_apply (δ₁ δ₂ : α → ℤ) :
    linking δ₁ δ₂ = ∑ p, (δ₁ p : ℚ) * pointMultiplicity p δ₂ := by
  simp [linking, AddMonoidHom.finsetSum_apply, zsmul_eq_mul]

/-- The form `L` takes half-integral values. -/
theorem exists_linking_eq (δ₁ δ₂ : α → ℤ) :
    ∃ k : ℤ, linking δ₁ δ₂ = k / 2 := by
  choose k hk using fun p ↦ exists_pointMultiplicity_eq p δ₂
  refine ⟨∑ p, δ₁ p * k p, ?_⟩
  simp [linking_apply, hk, div_eq_mul_inv, Finset.sum_mul, mul_assoc]

/-- The multiplicity `m(β, p)` in terms of the boundary at and above `p` rather than below it:
`m(β, p) = ∑_{y > p} δ y + δ p / 2 - ∑_y δ y`. -/
theorem pointMultiplicity_eq_sum_gt (p : α) (δ : α → ℤ) :
    pointMultiplicity p δ =
      ∑ y ∈ ({y | p < y} : Finset α), (δ y : ℚ) + δ p / 2 - ∑ y, (δ y : ℚ) := by
  have h : ∑ y, (δ y : ℚ) = ∑ y ∈ ({y | y < p} : Finset α), (δ y : ℚ) + δ p +
      ∑ y ∈ ({y | p < y} : Finset α), (δ y : ℚ) := by
    have hp : (δ p : ℚ) = ∑ y, if p = y then (δ y : ℚ) else 0 := by simp
    rw [Finset.sum_filter, Finset.sum_filter, hp, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rcases lt_trichotomy y p with hy | rfl | hy
    · simp [hy, hy.ne', hy.not_gt]
    · simp
    · simp [hy, hy.ne, hy.not_gt]
  rw [pointMultiplicity_apply, h]
  ring

/-- **The symmetric part of `L`** is minus the product of the total sums of the boundaries:
`L(β₁, β₂) + L(β₂, β₁) = -(∑ ∂β₁) (∑ ∂β₂)`. So `L` is antisymmetric on the classes of
`H₁([1, n], {1, …, n})`, whose boundaries have total sum zero. -/
theorem linking_add_linking_swap (δ₁ δ₂ : α → ℤ) :
    linking δ₁ δ₂ + linking δ₂ δ₁ = -((∑ x, (δ₁ x : ℚ)) * ∑ x, (δ₂ x : ℚ)) := by
  -- Exchanging the two summation variables turns the pairs `y < p` into the pairs `p < y`.
  have hswap : ∑ p, (δ₂ p : ℚ) * ∑ y ∈ ({y | y < p} : Finset α), (δ₁ y : ℚ) =
      ∑ p, (δ₁ p : ℚ) * ∑ y ∈ ({y | p < y} : Finset α), (δ₂ y : ℚ) := by
    simp only [Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun y _ ↦ by rw [mul_comm]
  have hdiag : ∑ p, (δ₂ p : ℚ) * (δ₁ p / 2) = ∑ p, (δ₁ p : ℚ) * (δ₂ p / 2) :=
    Finset.sum_congr rfl fun p _ ↦ by ring
  have h₂₁ : linking δ₂ δ₁ =
      -∑ p, (δ₁ p : ℚ) * (pointMultiplicity p δ₂ + ∑ x, (δ₂ x : ℚ)) := by
    simp only [linking_apply, pointMultiplicity_eq_sum_gt _ δ₂, sub_add_cancel]
    simp only [pointMultiplicity_apply, mul_sub, mul_neg, mul_add, Finset.sum_sub_distrib,
      Finset.sum_neg_distrib, Finset.sum_add_distrib, hswap, hdiag]
    ring
  rw [h₂₁, linking_apply]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
  ring

/-- `L(β, β) = -(∑ ∂β)² / 2`, which vanishes on the classes of `H₁([1, n], {1, …, n})`. -/
theorem linking_self (δ : α → ℤ) : linking δ δ = -(∑ x, (δ x : ℚ)) ^ 2 / 2 := by
  linear_combination (1 / 2 : ℚ) * linking_add_linking_swap δ δ

/-- Modulo `1`, the form `L(β₁, β₂)` is half the sum of the products of the coefficients of
`∂β₁` and `∂β₂`. -/
theorem exists_linking_eq_add (δ₁ δ₂ : α → ℤ) :
    ∃ k : ℤ, linking δ₁ δ₂ = k + (∑ p, (δ₁ p : ℚ) * δ₂ p) / 2 := by
  have h (p : α) : (δ₁ p : ℚ) * pointMultiplicity p δ₂ =
      -(δ₁ p * (∑ y ∈ ({y | y < p} : Finset α), δ₂ y + δ₂ p) : ℤ) + (δ₁ p : ℚ) * δ₂ p / 2 := by
    rw [pointMultiplicity_apply]
    push_cast
    ring
  refine ⟨-∑ p, δ₁ p * (∑ y ∈ ({y | y < p} : Finset α), δ₂ y + δ₂ p), ?_⟩
  rw [linking_apply, Finset.sum_congr rfl fun p _ ↦ h p, Finset.sum_add_distrib, ← Finset.sum_div]
  push_cast
  simp only [Finset.sum_neg_distrib]

omit [LinearOrder α] in
/-- The number of points at which a boundary `δ` is odd, the number of parity changes of the
class, is congruent modulo `4` to the sum of the squares of the coefficients of `δ`. -/
theorem exists_sum_sq_eq (δ : α → ℤ) :
    ∃ m : ℤ, ∑ x, δ x ^ 2 = #{x | Odd (δ x)} + 4 * m := by
  have h (x : α) : ∃ m : ℤ, δ x ^ 2 = (if Odd (δ x) then 1 else 0) + 4 * m := by
    rcases Int.even_or_odd' (δ x) with ⟨a, ha | ha⟩
    · refine ⟨a ^ 2, ?_⟩
      rw [ha, ite_eq_right_iff.2 fun h ↦ absurd h (Int.not_odd_iff_even.2 ⟨a, by ring⟩)]
      ring
    · refine ⟨a ^ 2 + a, ?_⟩
      rw [ite_eq_left_iff.2 fun h ↦ absurd ⟨a, ha⟩ h, ha]
      ring
  choose m hm using h
  refine ⟨∑ x, m x, ?_⟩
  rw [Finset.sum_congr rfl fun x _ ↦ hm x, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.natCast_card_filter]

omit [LinearOrder α] in
/-- The congruence `j ≡ #(parity changes of β) / 4 (mod 1)` defining Lipshitz, Ozsváth and
Thurston's group `G'(n)`, written with the sum of the squares of the coefficients of `δ = ∂β` in
place of the number of points where `δ` is odd. -/
theorem exists_eq_add_card_odd_iff (j : ℚ) (δ : α → ℤ) :
    (∃ k : ℤ, j = k + (#{x | Odd (δ x)} : ℚ) / 4) ↔ ∃ k : ℤ, j = k + (∑ x, (δ x : ℚ) ^ 2) / 4 := by
  obtain ⟨m, hm⟩ := exists_sum_sq_eq δ
  have hm' : ∑ x, (δ x : ℚ) ^ 2 = #{x | Odd (δ x)} + 4 * m := by exact_mod_cast hm
  rw [hm']
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k - m, by push_cast; ring⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k + m, by push_cast; ring⟩

end StrandGradingGroup

section GradingGroup

attribute [local instance] trivialMulDistribMulAction

variable {α : Type*} [LinearOrder α] [Fintype α]

/-- The form `L`, written multiplicatively, as a factor set of `Multiplicative (α → ℤ)` with values
in `Multiplicative ℚ` for the trivial action. -/
def StrandGradingGroup.linkingFactorSet : FactorSet (Multiplicative (α → ℤ)) (Multiplicative ℚ) :=
  FactorSet.ofBimultiplicative
    { toFun δ₁ := AddMonoidHom.toMultiplicative (StrandGradingGroup.linking δ₁.toAdd)
      map_one' := by ext; simp
      map_mul' δ₁ δ₂ := by ext; simp }
    trivialMulDistribMulAction_smul

@[simp]
theorem StrandGradingGroup.linkingFactorSet_apply
    (p : Multiplicative (α → ℤ) × Multiplicative (α → ℤ)) :
    linkingFactorSet p = .ofAdd (linking p.1.toAdd p.2.toAdd) :=
  FactorSet.ofBimultiplicative_apply _ _ p

/-- The grading group of the strands algebra on a finite linear order `α`: the central extension
of the group of boundaries `∂β : α → ℤ` of classes `β ∈ H₁([1, n], {1, …, n})` by the Maslov
component in `ℚ`, built from the factor set `L`. An element is a pair of a Maslov component
`maslov` and a boundary `boundary`, multiplied by
`(j₁, β₁) (j₂, β₂) = (j₁ + j₂ + L(β₁, β₂), β₁ + β₂)`. For `α = Fin n`, Lipshitz, Ozsváth and
Thurston's group `G'(n)` is its subgroup `StrandGradingGroup.gPrime` of elements with
boundary of total sum zero whose Maslov component is congruent modulo `1` to a quarter of the number
of points at which the boundary is odd. -/
abbrev StrandGradingGroup (α : Type*) [LinearOrder α] [Fintype α] : Type _ :=
  (StrandGradingGroup.linkingFactorSet (α := α)).Extension

namespace StrandGradingGroup

/-- The Maslov component of an element of the grading group. -/
def maslov (g : StrandGradingGroup α) : ℚ :=
  g.left.toAdd

/-- The boundary `∂β` of the homology class `β` of an element of the grading group, which
determines it. -/
def boundary (g : StrandGradingGroup α) : α → ℤ :=
  g.right.toAdd

/-- The element of the grading group with Maslov component `j` and boundary `δ`. -/
def mk (j : ℚ) (δ : α → ℤ) : StrandGradingGroup α :=
  ⟨.ofAdd j, .ofAdd δ⟩

@[simp]
theorem mk_maslov (j : ℚ) (δ : α → ℤ) : (mk j δ).maslov = j :=
  (rfl)

@[simp]
theorem mk_boundary (j : ℚ) (δ : α → ℤ) : (mk j δ).boundary = δ :=
  (rfl)

@[ext]
theorem ext {g h : StrandGradingGroup α} (hm : g.maslov = h.maslov)
    (hb : g.boundary = h.boundary) : g = h :=
  FactorSet.Extension.ext hm hb

@[simp]
theorem one_maslov : (1 : StrandGradingGroup α).maslov = 0 :=
  (rfl)

@[simp]
theorem one_boundary : (1 : StrandGradingGroup α).boundary = 0 :=
  (rfl)

@[simp]
theorem mul_maslov (g h : StrandGradingGroup α) :
    (g * h).maslov = g.maslov + h.maslov + linking g.boundary h.boundary := by
  simp [maslov, boundary]

@[simp]
theorem mul_boundary (g h : StrandGradingGroup α) :
    (g * h).boundary = g.boundary + h.boundary :=
  (rfl)

@[simp]
theorem inv_maslov (g : StrandGradingGroup α) :
    g⁻¹.maslov = -g.maslov + linking g.boundary g.boundary := by
  simp only [maslov, boundary, FactorSet.Extension.inv_left, linkingFactorSet_apply,
    trivialMulDistribMulAction_smul, toAdd_inv, toAdd_mul, toAdd_ofAdd, map_neg]
  ring

@[simp]
theorem inv_boundary (g : StrandGradingGroup α) : g⁻¹.boundary = -g.boundary :=
  (rfl)

/-- The central element `λ = (1, 0)` of the grading group, the image of `1` under the inclusion
of the Maslov component, which shifts the Maslov component by one. The differential of the
strands algebra has degree `λ⁻¹`. -/
def lambda : StrandGradingGroup α :=
  FactorSet.inl _ (.ofAdd 1)

@[simp]
theorem lambda_maslov : (lambda : StrandGradingGroup α).maslov = 1 := by
  simp [lambda, maslov]

@[simp]
theorem lambda_boundary : (lambda : StrandGradingGroup α).boundary = 0 := by
  simp [lambda, boundary]

/-- The powers of `λ` shift only the Maslov component. -/
theorem lambda_zpow (n : ℤ) : (lambda : StrandGradingGroup α) ^ n = mk n 0 := by
  rw [lambda, ← map_zpow, ← ofAdd_zsmul, zsmul_one]
  ext <;> simp [maslov, boundary, mk]

theorem lambda_zpow_mul (n : ℤ) (g : StrandGradingGroup α) :
    lambda ^ n * g = mk (n + g.maslov) g.boundary := by
  rw [lambda_zpow]
  ext <;> simp

theorem mul_lambda_zpow (g : StrandGradingGroup α) (n : ℤ) :
    g * lambda ^ n = mk (g.maslov + n) g.boundary := by
  rw [lambda_zpow]
  ext <;> simp

/-- `λ` is central. -/
theorem lambda_mem_center : (lambda : StrandGradingGroup α) ∈ Subgroup.center _ :=
  FactorSet.inl_range_le_center _ trivialMulDistribMulAction_smul ⟨_, rfl⟩

/-- The grading group `G'(n)` of Lipshitz, Ozsváth and Thurston, for `α = Fin n`: the subgroup of
the elements `(j, β)` with boundary of total sum zero and `j ≡ ε(β) (mod 1)`, where `ε(β)` is a
quarter of the number of parity changes of `β`, the points at which `∂β` is odd. Such a `j` is a
half-integer (`TauCeti.StrandGradingGroup.exists_maslov_eq_of_mem_gPrime`). -/
def gPrime : Subgroup (StrandGradingGroup α) where
  carrier := {g | (∃ k : ℤ, g.maslov = k + (#{x | Odd (g.boundary x)} : ℚ) / 4) ∧
    ∑ x, g.boundary x = 0}
  mul_mem' := by
    rintro g h ⟨hk₁, hg⟩ ⟨hk₂, hh⟩
    obtain ⟨k₁, hk₁⟩ := (exists_eq_add_card_odd_iff _ _).1 hk₁
    obtain ⟨k₂, hk₂⟩ := (exists_eq_add_card_odd_iff _ _).1 hk₂
    obtain ⟨k₃, hk₃⟩ := exists_linking_eq_add g.boundary h.boundary
    refine ⟨(exists_eq_add_card_odd_iff _ _).2 ⟨k₁ + k₂ + k₃, ?_⟩, ?_⟩
    · rw [mul_maslov, hk₁, hk₂, hk₃, mul_boundary]
      simp only [Pi.add_apply, Int.cast_add, add_sq, Finset.sum_add_distrib, mul_assoc,
        ← Finset.mul_sum]
      ring
    · simp [Finset.sum_add_distrib, hg, hh]
  one_mem' := ⟨(exists_eq_add_card_odd_iff _ _).2 ⟨0, by simp⟩, by simp⟩
  inv_mem' := by
    rintro g ⟨hk₁, hg⟩
    obtain ⟨k₁, hk₁⟩ := (exists_eq_add_card_odd_iff _ _).1 hk₁
    obtain ⟨k₂, hk₂⟩ := exists_linking_eq_add g.boundary g.boundary
    refine ⟨(exists_eq_add_card_odd_iff _ _).2 ⟨-k₁ + k₂, ?_⟩, ?_⟩
    · rw [inv_maslov, hk₁, hk₂, inv_boundary]
      simp only [Pi.neg_apply, Int.cast_neg, neg_sq, ← sq]
      push_cast
      ring
    · simp [hg]

theorem mem_gPrime {g : StrandGradingGroup α} :
    g ∈ gPrime ↔
      (∃ k : ℤ, g.maslov = k + (#{x | Odd (g.boundary x)} : ℚ) / 4) ∧ ∑ x, g.boundary x = 0 :=
  Iff.rfl

/-- Membership in `G'(n)`, with the sum of the squares of the coefficients of the boundary in place
of the number of parity changes. -/
theorem mem_gPrime_iff_sum_sq {g : StrandGradingGroup α} :
    g ∈ gPrime ↔
      (∃ k : ℤ, g.maslov = k + (∑ x, (g.boundary x : ℚ) ^ 2) / 4) ∧ ∑ x, g.boundary x = 0 := by
  rw [mem_gPrime, exists_eq_add_card_odd_iff]

/-- The Maslov component of an element of `G'(n)` is a half-integer. -/
theorem exists_maslov_eq_of_mem_gPrime {g : StrandGradingGroup α} (hg : g ∈ gPrime) :
    ∃ k : ℤ, g.maslov = k / 2 := by
  obtain ⟨⟨k, hk⟩, hs⟩ := mem_gPrime_iff_sum_sq.1 hg
  choose m hm using fun x ↦ Int.even_mul_pred_self (g.boundary x)
  have hsq : ∑ x, g.boundary x ^ 2 = 2 * ∑ x, m x := by
    rw [← zero_add (2 * _), ← hs, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    linear_combination hm x
  have hsq' : ∑ x, (g.boundary x : ℚ) ^ 2 = 2 * ∑ x, m x := by exact_mod_cast hsq
  refine ⟨2 * k + ∑ x, m x, ?_⟩
  rw [hk, hsq']
  push_cast
  ring

theorem lambda_mem_gPrime : (lambda : StrandGradingGroup α) ∈ gPrime :=
  mem_gPrime_iff_sum_sq.2 ⟨⟨1, by simp⟩, by simp⟩

/-- Every class with boundary of total sum zero is the class of an element of `G'(n)`, with
Maslov component `ε(β)`. -/
theorem mk_mem_gPrime {δ : α → ℤ} (hδ : ∑ x, δ x = 0) :
    mk ((#{x | Odd (δ x)} : ℚ) / 4) δ ∈ gPrime :=
  ⟨⟨0, by simp⟩, by simpa using hδ⟩

/-- **The kernel of the class map on `G'(n)`.** The elements of `G'(n)` with zero class are exactly
the powers of `λ`: the condition `j ≡ ε(0) = 0 (mod 1)` makes their Maslov component an integer. -/
theorem mem_zpowers_lambda_iff {g : StrandGradingGroup α} :
    g ∈ Subgroup.zpowers lambda ↔ g ∈ gPrime ∧ g.boundary = 0 := by
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨zpow_mem lambda_mem_gPrime n, by simp [lambda_zpow]⟩
  · rintro ⟨⟨⟨k, hk⟩, -⟩, hb⟩
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    rw [lambda_zpow]
    ext
    · simp [hk, hb]
    · simp [hb]

end StrandGradingGroup

end GradingGroup

namespace StrandDiagram

open StrandGradingGroup

variable {α : Type*} [LinearOrder α] [Fintype α]

/-- The boundary of the class `[φ]` of the strands of a diagram `φ : S → T`: the indicator of
the end points `T` minus that of the starting points `S`. -/
def boundary (φ : StrandDiagram α) : α → ℤ :=
  fun x ↦ (if x ∈ φ.target then 1 else 0) - if x ∈ φ.source then 1 else 0

theorem boundary_apply (φ : StrandDiagram α) (x : α) :
    φ.boundary x = (if x ∈ φ.target then 1 else 0) - if x ∈ φ.source then 1 else 0 :=
  (rfl)

@[simp]
theorem boundary_idOn (s : Finset α) : (idOn s).boundary = 0 := by
  ext x
  simp [boundary_apply]

/-- The class of a concatenation is the sum of the classes. -/
theorem boundary_trans_of_target_eq {φ ψ : StrandDiagram α} (h : φ.target = ψ.source) :
    (φ.trans ψ).boundary = φ.boundary + ψ.boundary := by
  ext x
  simp only [boundary_apply, Pi.add_apply, source_trans_of_target_eq h,
    target_trans_of_target_eq h, h]
  ring

/-- The total length of the strands of a diagram `φ : S → T`: the sum, over its strands, of the
number of points of `α` that the strand climbs, `∑_{x ∈ S} (r (φ x) - r x)` where `r x` is the
number of points below `x` (`TauCeti.StrandDiagram.length_eq_sum`). It is written through the
boundary of the class of `φ`, so that it is visibly additive under concatenation. -/
def length (φ : StrandDiagram α) : ℤ :=
  ∑ x, (#{y | y < x} : ℤ) * φ.boundary x

theorem length_def (φ : StrandDiagram α) :
    φ.length = ∑ x, (#{y | y < x} : ℤ) * φ.boundary x :=
  (rfl)

/-- A strand starts at or below its end point, so fewer points lie below its start. -/
private theorem card_filter_lt_le_card_filter_lt_endpoint {φ : StrandDiagram α} {x : α}
    (hx : x ∈ φ.source) : #{y | y < x} ≤ #{y | y < φ.endpoint x} :=
  card_le_card fun y hy ↦ by
    simp only [mem_filter, mem_univ, true_and] at hy ⊢
    exact hy.trans_le (φ.le_of_mem (endpoint_mem hx))

/-- A strand with as many points below its end point as below its start is horizontal. -/
private theorem endpoint_eq_of_card_filter_lt_eq {φ : StrandDiagram α} {x : α}
    (hx : x ∈ φ.source) (h : #{y | y < φ.endpoint x} = #{y | y < x}) : φ.endpoint x = x := by
  by_contra hne
  have hlt : x < φ.endpoint x := (φ.le_of_mem (endpoint_mem hx)).lt_of_ne (Ne.symm hne)
  refine h.not_gt (card_lt_card ⟨fun y hy ↦ ?_, fun hsub ↦ ?_⟩)
  · simp only [mem_filter, mem_univ, true_and] at hy ⊢
    exact hy.trans hlt
  · have hxx := hsub (by simpa using hlt)
    simp at hxx

/-- The length of a diagram is the sum, over its strands, of the number of points the strand
climbs. -/
theorem length_eq_sum (φ : StrandDiagram α) :
    φ.length = ∑ x ∈ φ.source, ((#{y | y < φ.endpoint x} : ℤ) - #{y | y < x}) := by
  have himage : ∑ x ∈ φ.target, (#{y | y < x} : ℤ) =
      ∑ x ∈ φ.source, (#{y | y < φ.endpoint x} : ℤ) := by
    rw [target_eq_image, sum_image φ.injOn_getD]
    simp only [endpoint_def]
  simp only [length_def, boundary_apply, mul_sub, mul_ite, mul_one, mul_zero, sum_sub_distrib,
    sum_ite_mem, univ_inter, himage]

/-- The length of a diagram is nonnegative: every strand goes upwards. -/
theorem length_nonneg (φ : StrandDiagram α) : 0 ≤ φ.length := by
  rw [length_eq_sum]
  exact sum_nonneg fun x hx ↦ sub_nonneg.2 (by
    exact_mod_cast card_filter_lt_le_card_filter_lt_endpoint hx)

@[simp]
theorem length_idOn (s : Finset α) : (idOn s).length = 0 := by
  simp [length_def]

/-- **A diagram has length zero exactly when it is an identity diagram.** -/
theorem length_eq_zero_iff {φ : StrandDiagram α} : φ.length = 0 ↔ φ = idOn φ.source := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ length_idOn _⟩
  rw [length_eq_sum] at h
  have hterm := (sum_eq_zero_iff_of_nonneg fun x hx ↦ sub_nonneg.2 (by
    exact_mod_cast card_filter_lt_le_card_filter_lt_endpoint hx)).1 h
  ext i j
  by_cases hi : i ∈ φ.source
  · have hend : φ.endpoint i = i :=
      endpoint_eq_of_card_filter_lt_eq hi (by exact_mod_cast sub_eq_zero.1 (hterm i hi))
    have hmem := endpoint_mem hi
    rw [hend] at hmem
    rw [idOn_apply, ite_eq_left hi, Option.mem_def.1 hmem]
  · rw [apply_eq_none_of_notMem_source hi, idOn_apply, ite_eq_right hi]

/-- A diagram that is not an identity diagram has positive length. -/
theorem length_pos {φ : StrandDiagram α} (h : φ ≠ idOn φ.source) : 0 < φ.length :=
  φ.length_nonneg.lt_of_ne fun h' ↦ h (length_eq_zero_iff.1 h'.symm)

/-- The length of a diagram is at most the square of the number of points. -/
theorem length_le (φ : StrandDiagram α) : φ.length ≤ Fintype.card α ^ 2 := by
  have hterm (x : α) : (#{y | y < x} : ℤ) * φ.boundary x ≤ Fintype.card α := by
    have hb : φ.boundary x ≤ 1 := by
      rw [boundary_apply]
      split_ifs <;> norm_num
    have hr : (#{y | y < x} : ℤ) ≤ Fintype.card α := by
      exact_mod_cast card_le_univ _
    calc (#{y | y < x} : ℤ) * φ.boundary x ≤ #{y | y < x} * 1 :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ ≤ Fintype.card α := by rwa [mul_one]
  calc φ.length ≤ ∑ _x : α, (Fintype.card α : ℤ) := sum_le_sum fun x _ ↦ hterm x
    _ = Fintype.card α ^ 2 := by simp [sq]

/-- **Lengths add under concatenation.** -/
theorem length_trans_of_target_eq {φ ψ : StrandDiagram α} (h : φ.target = ψ.source) :
    (φ.trans ψ).length = φ.length + ψ.length := by
  simp only [length_def, boundary_trans_of_target_eq h, Pi.add_apply, mul_add, sum_add_distrib]

/-- **A concatenation is an identity diagram exactly when both factors are.** -/
theorem trans_eq_idOn_source_iff {φ ψ : StrandDiagram α} (h : φ.target = ψ.source) :
    φ.trans ψ = idOn (φ.trans ψ).source ↔ φ = idOn φ.source ∧ ψ = idOn ψ.source := by
  rw [← length_eq_zero_iff, ← length_eq_zero_iff, ← length_eq_zero_iff,
    length_trans_of_target_eq h]
  have := φ.length_nonneg
  have := ψ.length_nonneg
  omega

/-- A diagram has as many end points as starting points, so the boundary of its class has total
sum zero. -/
theorem sum_boundary (φ : StrandDiagram α) : ∑ x, φ.boundary x = 0 := by
  simp only [boundary_apply, Finset.sum_sub_distrib, Finset.sum_boole, Finset.filter_mem_eq_inter,
    Finset.univ_inter, card_target, sub_self]

/-- The boundary of the class of a diagram, summed over the points below `p`, counts the strands
passing over `p`: those starting below `p` and ending at or above it. -/
private theorem sum_boundary_lt (φ : StrandDiagram α) (p : α) :
    ∑ y ∈ ({y | y < p} : Finset α), φ.boundary y =
      -#{s ∈ φ.source | s < p ∧ p ≤ (φ s).getD s} := by
  have hT : #{t ∈ φ.target | t < p} = #{s ∈ φ.source | (φ s).getD s < p} := by
    rw [target_eq_image φ, Finset.filter_image, card_image_of_injOn]
    exact (injOn_getD φ).mono (Finset.filter_subset _ _)
  have hdisj : Disjoint ({s ∈ φ.source | (φ s).getD s < p} : Finset α)
      {s ∈ φ.source | s < p ∧ p ≤ (φ s).getD s} := by
    rw [Finset.disjoint_filter]
    exact fun s _ h h' ↦ not_lt.2 h'.2 h
  have hS : #{s ∈ φ.source | s < p} =
      #{s ∈ φ.source | (φ s).getD s < p} + #{s ∈ φ.source | s < p ∧ p ≤ (φ s).getD s} := by
    rw [← Finset.card_union_of_disjoint hdisj]
    congr 1
    ext s
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hs, hsp⟩
      by_cases h : (φ s).getD s < p
      · exact Or.inl ⟨hs, h⟩
      · exact Or.inr ⟨hs, hsp, not_lt.1 h⟩
    · rintro (⟨hs, h⟩ | ⟨hs, hsp, -⟩)
      · exact ⟨hs, (le_getD hs).trans_lt h⟩
      · exact ⟨hs, hsp⟩
  have hsum : ∑ y ∈ ({y | y < p} : Finset α), φ.boundary y =
      (#{t ∈ φ.target | t < p} : ℤ) - #{s ∈ φ.source | s < p} := by
    simp only [boundary_apply, Finset.sum_sub_distrib, Finset.sum_boole, Finset.filter_filter]
    congr 3 <;> ext <;> simp [and_comm]
  rw [hsum, hT, hS]
  push_cast
  ring

/-- Exactly one strand ends at a point of the target, and none ends elsewhere. -/
private theorem card_filter_getD_eq (φ : StrandDiagram α) (p : α) :
    #{s ∈ φ.source | (φ s).getD s = p} = if p ∈ φ.target then 1 else 0 := by
  rw [target_eq_image φ]
  split_ifs with h
  · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 h
    rw [Finset.card_eq_one]
    refine ⟨s, Finset.eq_singleton_iff_unique_mem.2 ⟨by simp [hs], fun t ht ↦ ?_⟩⟩
    rw [Finset.mem_filter] at ht
    exact injOn_getD φ ht.1 hs ht.2
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun s hs hsp ↦ h (Finset.mem_image.2 ⟨s, hs, hsp⟩)

/-- The strands meeting the level of `p`, from `s ≤ p` to `φ s ≥ p`, are those passing just
above `p` together with the one ending at `p`, and also those passing just below `p` together
with the one starting at `p`. -/
private theorem card_filter_le_lt_add (φ : StrandDiagram α) (p : α) :
    #{s ∈ φ.source | s ≤ p ∧ p < (φ s).getD s} + (if p ∈ φ.target then 1 else 0) =
      #{s ∈ φ.source | s < p ∧ p ≤ (φ s).getD s} + (if p ∈ φ.source then 1 else 0) := by
  have hS : #{s ∈ φ.source | s = p} = if p ∈ φ.source then 1 else 0 := by
    rw [Finset.filter_eq']
    split_ifs <;> simp
  have hdisj₁ : Disjoint ({s ∈ φ.source | s ≤ p ∧ p < (φ s).getD s} : Finset α)
      {s ∈ φ.source | (φ s).getD s = p} := by
    rw [Finset.disjoint_filter]
    exact fun s _ h h' ↦ lt_irrefl p (h.2.trans_eq h')
  have hdisj₂ : Disjoint ({s ∈ φ.source | s < p ∧ p ≤ (φ s).getD s} : Finset α)
      {s ∈ φ.source | s = p} := by
    rw [Finset.disjoint_filter]
    exact fun s _ h h' ↦ h.1.ne h'
  rw [← card_filter_getD_eq, ← hS, ← Finset.card_union_of_disjoint hdisj₁,
    ← Finset.card_union_of_disjoint hdisj₂]
  congr 1
  ext s
  simp only [Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro (⟨hs, hsp, hps⟩ | ⟨hs, rfl⟩)
    · rcases hsp.lt_or_eq with hsp | rfl
      · exact Or.inl ⟨hs, hsp, hps.le⟩
      · exact Or.inr ⟨hs, rfl⟩
    · rcases (le_getD hs).lt_or_eq with h | h
      · exact Or.inl ⟨hs, h, le_rfl⟩
      · exact Or.inr ⟨hs, h⟩
  · rintro (⟨hs, hsp, hps⟩ | ⟨hs, rfl⟩)
    · rcases hps.lt_or_eq with hps | hps
      · exact Or.inl ⟨hs, hsp.le, hps⟩
      · exact Or.inr ⟨hs, hps.symm⟩
    · rcases (le_getD hs).lt_or_eq with h | h
      · exact Or.inl ⟨hs, le_rfl, h⟩
      · exact Or.inr ⟨hs, h.symm⟩

/-- **The multiplicity of the class of a diagram.** At a point `p`, the multiplicity of the class
of the strands of `φ` is the average of the number of strands passing just below `p` (from
`s < p` to `φ s ≥ p`) and the number passing just above `p` (from `s ≤ p` to `φ s > p`). This is
the definition of Lipshitz, Ozsváth and Thurston. -/
theorem pointMultiplicity_boundary (φ : StrandDiagram α) (p : α) :
    pointMultiplicity p φ.boundary =
      ((#{s ∈ φ.source | s < p ∧ p ≤ (φ s).getD s} : ℚ) +
        #{s ∈ φ.source | s ≤ p ∧ p < (φ s).getD s}) / 2 := by
  have hcount := congrArg (fun z : ℕ ↦ (z : ℚ)) (card_filter_le_lt_add φ p)
  have hsum := congrArg (fun z : ℤ ↦ (z : ℚ)) (sum_boundary_lt φ p)
  simp only [Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at hcount
  simp only [Int.cast_sum, Int.cast_neg, Int.cast_natCast] at hsum
  rw [pointMultiplicity_apply, hsum, boundary_apply]
  push_cast
  linear_combination (-1 / 2 : ℚ) * hcount

/-- The form `L(∂[φ], β) = m(β, T) - m(β, S)`: the boundary of the class of `φ : S → T` is the
formal difference `T - S` of its end points and starting points. -/
theorem linking_boundary (φ : StrandDiagram α) (δ : α → ℤ) :
    linking φ.boundary δ =
      ∑ t ∈ φ.target, pointMultiplicity t δ - ∑ s ∈ φ.source, pointMultiplicity s δ := by
  simp only [linking_apply, boundary_apply, Int.cast_sub, Int.cast_ite, Int.cast_one,
    Int.cast_zero, sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib,
    Finset.sum_ite_mem, Finset.univ_inter]

/-- The grading `gr(φ) = (inv(φ) - m([φ], S), [φ])` of a strand diagram `φ : S → T` in the
grading group of the strands algebra. -/
def grading (φ : StrandDiagram α) : StrandGradingGroup α :=
  StrandGradingGroup.mk (φ.inversionCount - ∑ s ∈ φ.source, pointMultiplicity s φ.boundary)
    φ.boundary

@[simp]
theorem grading_maslov (φ : StrandDiagram α) :
    φ.grading.maslov = φ.inversionCount - ∑ s ∈ φ.source, pointMultiplicity s φ.boundary :=
  (rfl)

@[simp]
theorem grading_boundary (φ : StrandDiagram α) : φ.grading.boundary = φ.boundary :=
  (rfl)

/-- The Maslov component of the grading of a diagram is a half-integer. -/
theorem exists_grading_maslov_eq (φ : StrandDiagram α) :
    ∃ k : ℤ, φ.grading.maslov = k / 2 := by
  choose k hk using fun s ↦ exists_pointMultiplicity_eq s φ.boundary
  refine ⟨2 * φ.inversionCount - ∑ s ∈ φ.source, k s, ?_⟩
  simp only [grading_maslov, hk]
  push_cast
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  ring

/-- The identity diagrams, the idempotents of the strands algebra, have grading `1`. -/
@[simp]
theorem grading_idOn (s : Finset α) : (idOn s).grading = 1 := by
  ext <;> simp

/-- **The grading is multiplicative.** If the product of two strand diagrams in the strands
algebra is nonzero, the grading of their concatenation is the product of their gradings. -/
theorem grading_trans {φ ψ : StrandDiagram α} (h : φ.Composable ψ) :
    (φ.trans ψ).grading = φ.grading * ψ.grading := by
  ext
  · simp only [grading_maslov, mul_maslov, grading_boundary, h.inversionCount_trans,
      source_trans_of_target_eq h.target_eq, boundary_trans_of_target_eq h.target_eq,
      linking_boundary, ← h.target_eq, map_add, Finset.sum_add_distrib, Nat.cast_add]
    ring
  · simp [boundary_trans_of_target_eq h.target_eq]

/-- **Diagrams with the same ends differ in grading by a power of `λ`.** Two diagrams with the
same starting and end points have the same class, and their gradings differ by `λ` raised to the
difference of their crossing numbers. In particular a diagram obtained by resolving one crossing
of `φ`, lowering the crossing number by one, has grading `λ⁻¹ gr(φ)`: this is why the
differential of the strands algebra has degree `λ⁻¹`. -/
theorem grading_eq_lambda_zpow_mul {φ ψ : StrandDiagram α} (hs : ψ.source = φ.source)
    (ht : ψ.target = φ.target) :
    ψ.grading = lambda ^ ((ψ.inversionCount : ℤ) - φ.inversionCount) * φ.grading := by
  have hb : ψ.boundary = φ.boundary := by
    ext x
    simp [boundary_apply, hs, ht]
  rw [lambda_zpow_mul]
  ext
  · simp only [grading_maslov, mk_maslov, hs, hb]
    push_cast
    ring
  · simp [hb]

/-- The sum of the squares of the coefficients of the boundary of `φ : S → T` is twice the number
of starting points that are not end points. -/
private theorem sum_boundary_sq (φ : StrandDiagram α) :
    ∑ x, φ.boundary x ^ 2 = -2 * ∑ s ∈ φ.source, φ.boundary s := by
  have hT : ∑ t ∈ φ.target, φ.boundary t + ∑ s ∈ φ.source, φ.boundary s = 0 := by
    simp only [boundary_apply, Finset.sum_sub_distrib, Finset.sum_boole,
      Finset.filter_mem_eq_inter, Finset.inter_self, Finset.inter_comm φ.source, card_target]
    ring
  calc ∑ x, φ.boundary x ^ 2
      = ∑ x, φ.boundary x * ((if x ∈ φ.target then 1 else 0) - if x ∈ φ.source then 1 else 0) := by
        simp only [sq]
        rfl
    _ = ∑ t ∈ φ.target, φ.boundary t - ∑ s ∈ φ.source, φ.boundary s := by
        simp only [mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
          Finset.sum_ite_mem, Finset.univ_inter]
    _ = -2 * ∑ s ∈ φ.source, φ.boundary s := by linear_combination hT

/-- The grading of a diagram lies in the grading group `G'(n)` of Lipshitz, Ozsváth and
Thurston. -/
theorem grading_mem_gPrime (φ : StrandDiagram α) : φ.grading ∈ gPrime := by
  refine mem_gPrime_iff_sum_sq.2 ⟨⟨φ.inversionCount +
    ∑ s ∈ φ.source, (∑ y ∈ ({y | y < s} : Finset α), φ.boundary y + φ.boundary s), ?_⟩,
    φ.sum_boundary⟩
  have hsq : ∑ x, (φ.boundary x : ℚ) ^ 2 = -2 * ∑ s ∈ φ.source, (φ.boundary s : ℚ) := by
    exact_mod_cast φ.sum_boundary_sq
  rw [grading_maslov, grading_boundary, hsq]
  simp only [pointMultiplicity_apply, Int.cast_add, Int.cast_natCast, Int.cast_sum,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.sum_div]
  ring

/-! ### Horizontal strands and the grading -/

section Horizontal

variable {φ : StrandDiagram α} {a b p : α}

/-- At a point `p` which is either the position of a horizontal strand of `φ` or not an end of any
strand of `φ`, the multiplicity of the class of `φ` is the number of strands crossing a horizontal
strand at `p`. -/
theorem pointMultiplicity_boundary_eq_crossingCount
    (hp : ∀ x ∈ φ.source, x = p ↔ φ.endpoint x = p) :
    pointMultiplicity p φ.boundary = φ.crossingCount p := by
  have h₁ : ({s ∈ φ.source | s < p ∧ p ≤ (φ s).getD s} : Finset α) =
      {x ∈ φ.source | x < p ∧ p < φ.endpoint x} := by
    refine filter_congr fun x hx ↦ ?_
    rw [← endpoint_def]
    refine and_congr_right fun hxp ↦ ⟨fun h ↦ lt_of_le_of_ne h fun h' ↦ ?_, le_of_lt⟩
    exact hxp.ne ((hp x hx).2 h'.symm)
  have h₂ : ({s ∈ φ.source | s ≤ p ∧ p < (φ s).getD s} : Finset α) =
      {x ∈ φ.source | x < p ∧ p < φ.endpoint x} := by
    refine filter_congr fun x hx ↦ ?_
    rw [← endpoint_def]
    refine ⟨fun ⟨hxp, hpx⟩ ↦ ⟨lt_of_le_of_ne hxp fun h ↦ ?_, hpx⟩, fun h ↦ ⟨h.1.le, h.2⟩⟩
    exact hpx.ne ((hp x hx).1 h).symm
  rw [pointMultiplicity_boundary, h₁, h₂, crossingCount_def]
  ring

/-- **Adding one horizontal strand does not change the grading.** At a point `p` where no strand of
`φ` starts or ends, a horizontal strand adds one crossing for each strand passing over `p`, and the
multiplicity of the class at `p`, which `m([φ], S)` gains, is that same number. -/
theorem grading_addHorizontal_singleton (hs : p ∉ φ.source) (ht : p ∉ φ.target) :
    (φ.addHorizontal {p}).grading = φ.grading := by
  set φ' := φ.addHorizontal {p}
  have hs' : φ'.source = insert p φ.source := by
    rw [source_addHorizontal (disjoint_singleton_right.2 ht), union_comm, ← insert_eq]
  have ht' : φ'.target = insert p φ.target := by
    rw [target_addHorizontal (disjoint_singleton_right.2 hs), union_comm, ← insert_eq]
  have hb : φ'.boundary = φ.boundary := by
    ext x
    rcases eq_or_ne x p with rfl | hxp
    · simp [boundary_apply, hs', ht', hs, ht]
    · simp [boundary_apply, hs', ht', hxp]
  have hfp : φ'.endpoint p = p := endpoint_eq_of_mem (by simp [φ'])
  have hf (x : α) (hx : x ∈ φ.source) : φ'.endpoint x = φ.endpoint x := by
    rw [endpoint_def, endpoint_def, addHorizontal_apply_of_notMem (disjoint_singleton_right.2 ht)
      (by simpa using fun h : x = p ↦ hs (h ▸ hx))]
  have hinv : φ'.inversionCount = φ.inversionCount + φ.crossingCount p := by
    rw [inversionCount_def, inversionCount_def, inversions_def, inversions_def, hs',
      card_inversions_insert _ hs, inversions_congr hf, crossingCount_def, hfp]
    have h₀ : #{x ∈ φ.source | p < x ∧ φ'.endpoint x < p} = 0 := by
      refine card_eq_zero.2 (filter_eq_empty_iff.2 fun x hx ⟨hpx, hxp⟩ ↦ ?_)
      rw [hf x hx] at hxp
      exact (hpx.trans_le (φ.le_of_mem (endpoint_mem hx))).not_gt hxp
    rw [h₀, add_zero]
    congr 2
    exact filter_congr fun x hx ↦ by rw [hf x hx]
  have hm : pointMultiplicity p φ.boundary = φ.crossingCount p :=
    pointMultiplicity_boundary_eq_crossingCount fun x hx ↦
      ⟨fun h ↦ absurd (h ▸ hx) hs, fun h ↦ absurd (h ▸ endpoint_mem_target hx) ht⟩
  ext
  · rw [grading_maslov, grading_maslov, hb, hs', sum_insert hs, hm, hinv]
    push_cast
    ring
  · rw [grading_boundary, grading_boundary, hb]

/-- **Adding horizontal strands does not change the grading** (Lipshitz, Ozsváth and Thurston,
Proposition 3.40): if `U` avoids the starting and end points of `φ`, then `φ.addHorizontal U` has
the grading of `φ`. -/
theorem grading_addHorizontal {U : Finset α} (hs : Disjoint φ.source U)
    (ht : Disjoint φ.target U) : (φ.addHorizontal U).grading = φ.grading := by
  induction U using Finset.induction_on with
  | empty => simp
  | insert p U hpU ih =>
    have hsU := disjoint_of_subset_right (subset_insert p U) hs
    have htU := disjoint_of_subset_right (subset_insert p U) ht
    rw [insert_eq, union_comm, ← addHorizontal_addHorizontal, grading_addHorizontal_singleton,
      ih hsU htU]
    · rw [source_addHorizontal htU, mem_union, not_or]
      exact ⟨disjoint_right.1 hs (mem_insert_self p U), hpU⟩
    · rw [target_addHorizontal hsU, mem_union, not_or]
      exact ⟨disjoint_right.1 ht (mem_insert_self p U), hpU⟩

/-- **Moving a horizontal strand does not change the grading.** Moving the horizontal strand at `a`
to a point `b` at which no strand starts or ends trades the crossings with a horizontal strand at
`a` for those with one at `b`, and `m([φ], S)` changes by the same amount. -/
@[simp]
theorem grading_swapHorizontal (φ : StrandDiagram α) (a b : α) :
    (φ.swapHorizontal a b).grading = φ.grading := by
  wlog h : φ.CanMoveHorizontal a b generalizing a b
  · by_cases h' : φ.CanMoveHorizontal b a
    · rw [swapHorizontal_comm]
      exact this b a h'
    · rw [swapHorizontal_of_not h h']
  set φ' := φ.swapHorizontal a b
  have haS : a ∈ φ.source := mem_source.2 ⟨a, h.mem⟩
  have haT : a ∈ φ.target := mem_target.2 ⟨a, h.mem⟩
  have hab := h.ne
  have hb : φ'.boundary = φ.boundary := by
    ext x
    simp only [boundary_apply, φ', source_swapHorizontal h, target_swapHorizontal h, mem_insert,
      mem_erase]
    rcases eq_or_ne x a with rfl | hxa
    · simp [haS, haT, hab]
    rcases eq_or_ne x b with rfl | hxb
    · simp [h.notMem_source, h.notMem_target]
    · simp [hxa, hxb]
  have hfa : φ.endpoint a = a := endpoint_eq_of_mem h.mem
  have hma : pointMultiplicity a φ.boundary = φ.crossingCount a :=
    pointMultiplicity_boundary_eq_crossingCount fun x hx ↦
      ⟨fun h ↦ h ▸ hfa, fun h' ↦ φ.endpoint_injOn hx haS (h'.trans hfa.symm)⟩
  have hmb : pointMultiplicity b φ.boundary = φ.crossingCount b :=
    pointMultiplicity_boundary_eq_crossingCount fun x hx ↦
      ⟨fun h' ↦ absurd (h' ▸ hx) h.notMem_source,
        fun h' ↦ absurd (h' ▸ endpoint_mem_target hx) h.notMem_target⟩
  have hinv := inversionCount_swapHorizontal_add h
  have hs' : φ'.source = insert b (φ.source.erase a) := source_swapHorizontal h
  have hsum : ∑ s ∈ φ'.source, pointMultiplicity s φ.boundary + pointMultiplicity a φ.boundary =
      ∑ s ∈ φ.source, pointMultiplicity s φ.boundary + pointMultiplicity b φ.boundary := by
    rw [hs', sum_insert fun hb' ↦ h.notMem_source (mem_of_mem_erase hb'),
      ← add_sum_erase _ _ haS]
    ring
  ext
  · rw [grading_maslov, grading_maslov, hb]
    have hinv' : ((φ'.inversionCount : ℕ) : ℚ) + φ.crossingCount a =
        φ.inversionCount + φ.crossingCount b := by exact_mod_cast hinv
    rw [hma, hmb] at hsum
    linear_combination hinv' - hsum
  · rw [grading_boundary, grading_boundary, hb]

end Horizontal

end StrandDiagram

namespace StrandsAlgebra

open StrandDiagram

variable (R : Type*) {α G : Type*} [CommSemiring R] [LinearOrder α]

/-- The part of the strands algebra of degree `g` for a function `d` on strand diagrams: the
elements supported on the strand diagrams `φ` with `d φ = g`, that is, the image of
`Finsupp.supported` under the basis of strand diagrams. -/
noncomputable def gradedPartBy (d : StrandDiagram α → G) (g : G) :
    Submodule R (StrandsAlgebra R α) :=
  (Finsupp.supported R R {φ : StrandDiagram α | d φ = g}).map
    ((basis R α).repr.symm : (StrandDiagram α →₀ R) →ₗ[R] StrandsAlgebra R α)

variable {R}

section GradedPartBy

variable {d : StrandDiagram α → G}

/-- An element has degree `g` for `d` exactly when every strand diagram in its support has
degree `g`. -/
theorem mem_gradedPartBy {g : G} {x : StrandsAlgebra R α} :
    x ∈ gradedPartBy R d g ↔ ∀ φ ∈ ((basis R α).repr x).support, d φ = g := by
  rw [gradedPartBy, Submodule.mem_map_equiv, LinearEquiv.symm_symm, Finsupp.mem_supported]
  rfl

/-- The part of degree `g` for `d` is the span of the strand diagrams of degree `g`. -/
theorem gradedPartBy_eq_span (d : StrandDiagram α → G) (g : G) :
    gradedPartBy R d g = Submodule.span R (of '' {φ | d φ = g}) := by
  rw [gradedPartBy, Finsupp.supported_eq_span_single, Submodule.map_span, ← Set.image_comp]
  congr 2
  ext φ
  simp [← basis_apply]

/-- A strand diagram lies in the part of degree `g` for `d` exactly when its degree is `g`. -/
theorem of_mem_gradedPartBy_iff [Nontrivial R] {φ : StrandDiagram α} {g : G} :
    (of φ : StrandsAlgebra R α) ∈ gradedPartBy R d g ↔ d φ = g := by
  rw [mem_gradedPartBy, ← basis_apply, Module.Basis.repr_self,
    Finsupp.support_single _ one_ne_zero]
  simp

theorem of_mem_gradedPartBy (d : StrandDiagram α → G) (φ : StrandDiagram α) :
    (of φ : StrandsAlgebra R α) ∈ gradedPartBy R d (d φ) :=
  mem_gradedPartBy.2 fun ψ hψ ↦ by
    rw [← basis_apply, Module.Basis.repr_self] at hψ
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hψ)]

/-- Every element of the strands algebra is a sum of elements homogeneous for `d`. -/
theorem iSup_gradedPartBy (d : StrandDiagram α → G) : ⨆ g : G, gradedPartBy R d g = ⊤ := by
  have h : ⋃ g : G, {φ : StrandDiagram α | d φ = g} = Set.univ :=
    Set.iUnion_eq_univ_iff.2 fun φ ↦ ⟨d φ, rfl⟩
  simp only [gradedPartBy, ← Submodule.map_iSup, ← Finsupp.supported_iUnion, h,
    Finsupp.supported_univ, Submodule.map_top, LinearEquiv.range]

/-- The parts of different degrees for `d` are independent. -/
theorem iSupIndep_gradedPartBy (d : StrandDiagram α → G) :
    iSupIndep (gradedPartBy R d) := by
  refine LinearMap.iSupIndep_map _ (basis R α).repr.symm.injective fun g ↦
    (Finsupp.disjoint_supported_supported (s := {φ : StrandDiagram α | d φ = g})
      (t := {φ | d φ ≠ g})
      (Set.disjoint_left.2 fun _ hφ hφ' ↦ hφ' hφ)).mono_right ?_
  exact iSup₂_le fun h hne ↦ Finsupp.supported_mono fun φ (hφ : d φ = h) ↦ hφ.trans_ne hne

variable [Fintype α]

/-- If `d` is multiplicative on composable strand diagrams, the product of elements of degrees `g`
and `h` for `d` has degree `g * h`. -/
theorem mul_mem_gradedPartBy [Mul G]
    (hd : ∀ {φ ψ : StrandDiagram α}, φ.Composable ψ → d (φ.trans ψ) = d φ * d ψ)
    {g h : G} {x y : StrandsAlgebra R α}
    (hx : x ∈ gradedPartBy R d g) (hy : y ∈ gradedPartBy R d h) :
    x * y ∈ gradedPartBy R d (g * h) := by
  rw [gradedPartBy_eq_span] at hx hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, hφ, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨ψ, hψ, rfl⟩ := hy
      rw [of_mul_of]
      split_ifs with hφψ
      · rw [← (hφ : d φ = g), ← (hψ : d ψ = h), ← hd hφψ]
        exact of_mem_gradedPartBy d _
      · exact zero_mem _
    | zero => rw [mul_zero]; exact zero_mem _
    | add y y' _ _ hy hy' => rw [mul_add]; exact add_mem hy hy'
    | smul r y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add x x' _ _ hx hx' => rw [add_mul]; exact add_mem hx hx'
  | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx

end GradedPartBy

variable (R) [Fintype α]

/-- The part of the strands algebra of grading `g`: the elements supported on the strand diagrams
of grading `g`. -/
noncomputable def gradedPart (g : StrandGradingGroup α) : Submodule R (StrandsAlgebra R α) :=
  gradedPartBy R grading g

variable {R}

/-- An element has grading `g` exactly when every strand diagram in its support has grading `g`. -/
theorem mem_gradedPart {g : StrandGradingGroup α} {x : StrandsAlgebra R α} :
    x ∈ gradedPart R g ↔ ∀ φ ∈ ((basis R α).repr x).support, φ.grading = g :=
  mem_gradedPartBy

/-- The part of grading `g` is the span of the strand diagrams of grading `g`. -/
theorem gradedPart_eq_span (g : StrandGradingGroup α) :
    gradedPart R g = Submodule.span R (of '' {φ | φ.grading = g}) :=
  gradedPartBy_eq_span _ g

/-- A linear isomorphism of strands algebras given on basis elements by a bijection of diagrams
which transforms gradings by an injective map `F` carries the part of grading `g` onto the part of
grading `F g`. -/
theorem mem_gradedPart_iff_of_basis {β : Type*} [LinearOrder β] [Fintype β]
    (L : StrandsAlgebra R α ≃ₗ[R] StrandsAlgebra R β)
    (E : StrandDiagram α ≃ StrandDiagram β) {F : StrandGradingGroup α → StrandGradingGroup β}
    (hF : F.Injective) (hL : ∀ φ, L (of φ) = of (E φ)) (hE : ∀ φ, (E φ).grading = F φ.grading)
    {g : StrandGradingGroup α} {x : StrandsAlgebra R α} :
    L x ∈ gradedPart R (F g) ↔ x ∈ gradedPart R g := by
  have himage : E '' {φ | φ.grading = g} = {ψ | ψ.grading = F g} := by
    rw [E.image_eq_preimage_symm]
    ext ψ
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [← hF.eq_iff, ← hE, Equiv.apply_symm_apply]
  have hmap : (gradedPart R g).map (L : StrandsAlgebra R α →ₗ[R] StrandsAlgebra R β) =
      gradedPart R (F g) := by
    rw [gradedPart_eq_span, gradedPart_eq_span, Submodule.map_span, Set.image_image]
    simp only [LinearEquiv.coe_coe, hL]
    rw [← Set.image_image of E, himage]
  rw [← hmap, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]

/-- A strand diagram lies in the part of grading `g` exactly when its grading is `g`. -/
theorem of_mem_gradedPart_iff [Nontrivial R] {φ : StrandDiagram α} {g : StrandGradingGroup α} :
    (of φ : StrandsAlgebra R α) ∈ gradedPart R g ↔ φ.grading = g :=
  of_mem_gradedPartBy_iff

theorem of_mem_gradedPart (φ : StrandDiagram α) :
    (of φ : StrandsAlgebra R α) ∈ gradedPart R φ.grading :=
  of_mem_gradedPartBy _ φ

theorem idem_mem_gradedPart (s : Finset α) :
    (idem s : StrandsAlgebra R α) ∈ gradedPart R 1 := by
  rw [idem_def]
  simpa using of_mem_gradedPart (R := R) (idOn s)

/-- The unit of the strands algebra has grading `1`. -/
theorem one_mem_gradedPart : (1 : StrandsAlgebra R α) ∈ gradedPart R 1 := by
  rw [← sum_idem]
  exact Submodule.sum_mem _ fun s _ ↦ idem_mem_gradedPart s

/-- **The strands algebra is graded by the grading group**: the product of elements of
gradings `g` and `h` has grading `g * h`. -/
theorem mul_mem_gradedPart {g h : StrandGradingGroup α} {x y : StrandsAlgebra R α}
    (hx : x ∈ gradedPart R g) (hy : y ∈ gradedPart R h) : x * y ∈ gradedPart R (g * h) :=
  mul_mem_gradedPartBy grading_trans hx hy

/-- Every element of the strands algebra is a sum of homogeneous elements. -/
theorem iSup_gradedPart : ⨆ g : StrandGradingGroup α, gradedPart R g = ⊤ :=
  iSup_gradedPartBy _

/-- The parts of different gradings are independent. -/
theorem iSupIndep_gradedPart : iSupIndep (gradedPart R : StrandGradingGroup α → _) :=
  iSupIndep_gradedPartBy _

/-- Over a ring, the strands algebra is the internal direct sum of its graded parts. -/
theorem isInternal_gradedPart {R : Type*} [CommRing R] [DecidableEq (StrandGradingGroup α)] :
    DirectSum.IsInternal (gradedPart R : StrandGradingGroup α → Submodule R (StrandsAlgebra R α)) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top iSupIndep_gradedPart iSup_gradedPart

end StrandsAlgebra

/-! ### The differential has degree `λ⁻¹` -/

namespace StrandDiagram

open StrandGradingGroup

variable {α : Type*} [LinearOrder α] [Fintype α]

/-- **The differential has degree `λ⁻¹`**: resolving a crossing of `φ` that lowers the number of
crossings by one gives a diagram of grading `λ⁻¹ gr(φ)`. -/
theorem grading_resolve {φ : StrandDiagram α} {p : α × α} (h : p ∈ φ.resolvableInversions) :
    (φ.resolve p).grading = lambda⁻¹ * φ.grading := by
  rw [grading_eq_lambda_zpow_mul (source_resolve φ p) (target_resolve φ p),
    ← (mem_resolvableInversions.1 h).2]
  push_cast
  rw [sub_add_cancel_left, zpow_neg_one]

end StrandDiagram

namespace StrandsAlgebra

open StrandDiagram StrandGradingGroup

variable {R α : Type*} [CommSemiring R] [LinearOrder α] [Fintype α]

/-- If resolving any crossing of a strand diagram changes its degree for `d` by `f`, then the
differential maps the part of degree `g` for `d` to the part of degree `f g`. -/
theorem differential_mem_gradedPartBy {G : Type*} {d : StrandDiagram α → G} {f : G → G}
    (hd : ∀ {φ : StrandDiagram α} {p : α × α}, p ∈ φ.resolvableInversions →
      d (φ.resolve p) = f (d φ))
    {x : StrandsAlgebra R α} {g : G} (hx : x ∈ gradedPartBy R d g) :
    differential R α x ∈ gradedPartBy R d (f g) := by
  rw [gradedPartBy_eq_span] at hx
  refine (Submodule.span_le (p := (gradedPartBy R d _).comap (differential R α))).2 ?_ hx
  rintro _ ⟨φ, rfl, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, differential_of]
  exact Submodule.sum_mem _ fun p hp ↦ hd hp ▸ of_mem_gradedPartBy d _

/-- **The differential has degree `λ⁻¹`**: it maps the part of grading `g` to the part of grading
`λ⁻¹ g`. -/
theorem differential_mem_gradedPart {x : StrandsAlgebra R α} {g : StrandGradingGroup α}
    (hx : x ∈ gradedPart R g) : differential R α x ∈ gradedPart R (lambda⁻¹ * g) :=
  differential_mem_gradedPartBy (f := (lambda⁻¹ * ·)) grading_resolve hx

end StrandsAlgebra

end TauCeti
