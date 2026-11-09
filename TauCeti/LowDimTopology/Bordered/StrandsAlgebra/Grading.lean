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
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Basic
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
the differential, which resolves one crossing, has degree `λ⁻¹`.

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
of `TauCeti.StrandGradingGroup (Fin n)` of the elements with half-integral Maslov component and
boundary of total sum zero, and every grading of a diagram lies in it
(`TauCeti.StrandDiagram.grading_mem_gPrime`).

## Main definitions

* `TauCeti.StrandGradingGroup α`: the grading group, with its group structure.
* `TauCeti.StrandGradingGroup.pointMultiplicity`: the multiplicity `m(β, p)` of a class at a point.
* `TauCeti.StrandGradingGroup.linking`: the bilinear form `L(β₁, β₂) = m(β₂, ∂β₁)`.
* `TauCeti.StrandGradingGroup.linkingFactorSet`: `L` as a factor set for the trivial action.
* `TauCeti.StrandGradingGroup.lambda`: the central element `λ = (1, 0)`.
* `TauCeti.StrandGradingGroup.gPrime`: the subgroup `G'(n)`.
* `TauCeti.StrandDiagram.boundary`: the boundary of the class of the strands of a diagram.
* `TauCeti.StrandDiagram.grading`: the grading `gr(φ)` of a strand diagram.
* `TauCeti.StrandsAlgebra.gradedPart`: the elements supported on the diagrams of a given grading.

## Main results

* `TauCeti.StrandDiagram.grading_trans`: the grading is multiplicative on composable diagrams.
* `TauCeti.StrandDiagram.grading_idOn`: the identity diagrams have grading `1`.
* `TauCeti.StrandDiagram.grading_mem_gPrime`: every grading of a diagram lies in `G'(n)`.
* `TauCeti.StrandDiagram.grading_eq_lambda_zpow_mul`: diagrams with the same ends differ in
  grading by a power of `λ`.
* `TauCeti.StrandsAlgebra.mul_mem_gradedPart`, `TauCeti.StrandsAlgebra.one_mem_gradedPart`,
  `TauCeti.StrandsAlgebra.iSup_gradedPart`: the graded parts multiply according to the group law,
  contain the unit in degree `1`, and span the algebra; a strand diagram lies in the part of its
  own grading only (`TauCeti.StrandsAlgebra.of_mem_gradedPart_iff`).
* `TauCeti.StrandsAlgebra.iSupIndep_gradedPart`, `TauCeti.StrandsAlgebra.isInternal_gradedPart`:
  the graded parts are independent, so over a ring the algebra is their internal direct sum.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §3.3.1 (the
  group `G'(n)`, the multiplicity `m`, the grading of `A(n, k)` and its compatibility with the
  product and the differential).
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
half-integral Maslov component and boundary of total sum zero. -/
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
the elements with half-integral Maslov component and boundary of total sum zero. -/
def gPrime : Subgroup (StrandGradingGroup α) where
  carrier := {g | (∃ k : ℤ, g.maslov = k / 2) ∧ ∑ x, g.boundary x = 0}
  mul_mem' := by
    rintro g h ⟨⟨k₁, hk₁⟩, hg⟩ ⟨⟨k₂, hk₂⟩, hh⟩
    obtain ⟨k₃, hk₃⟩ := exists_linking_eq g.boundary h.boundary
    refine ⟨⟨k₁ + k₂ + k₃, ?_⟩, ?_⟩
    · rw [mul_maslov, hk₁, hk₂, hk₃]
      push_cast
      ring
    · simp [Finset.sum_add_distrib, hg, hh]
  one_mem' := ⟨⟨0, by simp⟩, by simp⟩
  inv_mem' := by
    rintro g ⟨⟨k₁, hk₁⟩, hg⟩
    obtain ⟨k₂, hk₂⟩ := exists_linking_eq g.boundary g.boundary
    refine ⟨⟨-k₁ + k₂, ?_⟩, ?_⟩
    · rw [inv_maslov, hk₁, hk₂]
      push_cast
      ring
    · simp [hg]

theorem mem_gPrime {g : StrandGradingGroup α} :
    g ∈ gPrime ↔ (∃ k : ℤ, g.maslov = k / 2) ∧ ∑ x, g.boundary x = 0 :=
  Iff.rfl

theorem lambda_mem_gPrime : (lambda : StrandGradingGroup α) ∈ gPrime :=
  ⟨⟨2, by simp⟩, by simp⟩

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

/-- The grading of a diagram lies in the grading group `G'(n)` of Lipshitz, Ozsváth and
Thurston. -/
theorem grading_mem_gPrime (φ : StrandDiagram α) : φ.grading ∈ gPrime :=
  ⟨φ.exists_grading_maslov_eq, φ.sum_boundary⟩

end StrandDiagram

namespace StrandsAlgebra

open StrandDiagram

variable (R : Type*) {α : Type*} [CommSemiring R] [LinearOrder α] [Fintype α]

/-- The part of the strands algebra of grading `g`: the elements supported on the strand diagrams
of grading `g`, that is, the image of `Finsupp.supported` under the basis of strand diagrams. -/
noncomputable def gradedPart (g : StrandGradingGroup α) : Submodule R (StrandsAlgebra R α) :=
  (Finsupp.supported R R {φ : StrandDiagram α | φ.grading = g}).map
    ((basis R α).repr.symm : (StrandDiagram α →₀ R) →ₗ[R] StrandsAlgebra R α)

variable {R}

/-- An element has grading `g` exactly when every strand diagram in its support has grading `g`. -/
theorem mem_gradedPart {g : StrandGradingGroup α} {x : StrandsAlgebra R α} :
    x ∈ gradedPart R g ↔ ∀ φ ∈ ((basis R α).repr x).support, φ.grading = g := by
  rw [gradedPart, Submodule.mem_map_equiv, LinearEquiv.symm_symm, Finsupp.mem_supported]
  rfl

/-- The part of grading `g` is the span of the strand diagrams of grading `g`. -/
theorem gradedPart_eq_span (g : StrandGradingGroup α) :
    gradedPart R g = Submodule.span R (of '' {φ | φ.grading = g}) := by
  rw [gradedPart, Finsupp.supported_eq_span_single, Submodule.map_span, ← Set.image_comp]
  congr 2
  ext φ
  simp [← basis_apply]

/-- A strand diagram lies in the part of grading `g` exactly when its grading is `g`. -/
theorem of_mem_gradedPart_iff [Nontrivial R] {φ : StrandDiagram α} {g : StrandGradingGroup α} :
    (of φ : StrandsAlgebra R α) ∈ gradedPart R g ↔ φ.grading = g := by
  rw [mem_gradedPart, ← basis_apply, Module.Basis.repr_self,
    Finsupp.support_single _ one_ne_zero]
  simp

theorem of_mem_gradedPart (φ : StrandDiagram α) :
    (of φ : StrandsAlgebra R α) ∈ gradedPart R φ.grading :=
  mem_gradedPart.2 fun ψ hψ ↦ by
    rw [← basis_apply, Module.Basis.repr_self] at hψ
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hψ)]

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
    (hx : x ∈ gradedPart R g) (hy : y ∈ gradedPart R h) : x * y ∈ gradedPart R (g * h) := by
  rw [gradedPart_eq_span] at hx hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, hφ, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨ψ, hψ, rfl⟩ := hy
      rw [of_mul_of]
      split_ifs with hφψ
      · rw [← (hφ : φ.grading = g), ← (hψ : ψ.grading = h), ← grading_trans hφψ]
        exact of_mem_gradedPart _
      · exact zero_mem _
    | zero => rw [mul_zero]; exact zero_mem _
    | add y y' _ _ hy hy' => rw [mul_add]; exact add_mem hy hy'
    | smul r y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add x x' _ _ hx hx' => rw [add_mul]; exact add_mem hx hx'
  | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx

/-- Every element of the strands algebra is a sum of homogeneous elements. -/
theorem iSup_gradedPart : ⨆ g : StrandGradingGroup α, gradedPart R g = ⊤ := by
  have h : ⋃ g : StrandGradingGroup α, {φ : StrandDiagram α | φ.grading = g} = Set.univ :=
    Set.iUnion_eq_univ_iff.2 fun φ ↦ ⟨φ.grading, rfl⟩
  simp only [gradedPart, ← Submodule.map_iSup, ← Finsupp.supported_iUnion, h,
    Finsupp.supported_univ, Submodule.map_top, LinearEquiv.range]

/-- The parts of different gradings are independent. -/
theorem iSupIndep_gradedPart : iSupIndep (gradedPart R : StrandGradingGroup α → _) := by
  refine LinearMap.iSupIndep_map _ (basis R α).repr.symm.injective fun g ↦
    (Finsupp.disjoint_supported_supported (s := {φ : StrandDiagram α | φ.grading = g})
      (t := {φ | φ.grading ≠ g})
      (Set.disjoint_left.2 fun _ hφ hφ' ↦ hφ' hφ)).mono_right ?_
  exact iSup₂_le fun h hne ↦ Finsupp.supported_mono fun φ (hφ : φ.grading = h) ↦ hφ.trans_ne hne

/-- Over a ring, the strands algebra is the internal direct sum of its graded parts. -/
theorem isInternal_gradedPart {R : Type*} [CommRing R] [DecidableEq (StrandGradingGroup α)] :
    DirectSum.IsInternal (gradedPart R : StrandGradingGroup α → Submodule R (StrandsAlgebra R α)) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top iSupIndep_gradedPart iSup_gradedPart

end StrandsAlgebra

end TauCeti
