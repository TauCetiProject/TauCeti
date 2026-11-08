/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.Trivial
public import TauCeti.GroupTheory.GroupExtension.Of.FactorSet
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Differential

/-!
# The unrefined grading of the strands algebra

Lipshitz, Ozsváth and Thurston grade the strands algebra `A(n)` by a noncommutative group
`G'(n)`, a central extension of the relative homology group `H₁(Z', a)` of an oriented interval
`Z'` relative to the `n` points `a` of the strands, by the half-integers. This file constructs the
group and the grading for an arbitrary finite linear order `α` in place of `{1, …, n}`, and proves
that the strands algebra is graded by it: products multiply gradings, and the differential lowers
the grading by the central element `λ`.

## The group

A relative `1`-chain `c` of the interval is recorded by its boundary `∂c`, a function `α → ℤ` of
total weight zero: since `H₁(Z') = 0`, the boundary map identifies `H₁(Z', a)` with these
functions (`TauCeti.StrandsAlgebra.H1`). The segment `[s, t]` from `s` to `t` has boundary
`t - s`. The *multiplicity* `m(c, p)` of `c` at a point `p` is the average of its local
multiplicities just below and just above `p`; it is a half-integer, extended linearly to
`0`-chains in the second argument. Twice the multiplicity is the integer-valued bilinear map
`TauCeti.StrandsAlgebra.twiceMultiplicity`. The grading group is the set of pairs `(j, c)` with
`j ∈ ½ℤ` and `c ∈ H₁(Z', a)`, multiplied by

  `(j₁, c₁) * (j₂, c₂) = (j₁ + j₂ + m(c₂, ∂c₁), c₁ + c₂)`.

Every half-integer here is recorded by its double: the *Maslov component* `j` is stored as the
integer `2 j`, so `G'(n)` is the extension of `H₁(Z', a)` by `ℤ` built from the factor set
`(c₁, c₂) ↦ 2 m(c₂, ∂c₁)` (`TauCeti.StrandsAlgebra.gradingFactorSet`), through the general
construction `TauCeti.FactorSet.Extension`. The central element `λ = (1, 0)` is
`TauCeti.StrandsAlgebra.GradingGroup.lambda`. The group is not commutative, since the correction
term `m(c₂, ∂c₁)` is not symmetric in `c₁` and `c₂`: for `s < t < u` it is `1/2` on
`([s, t], [t, u])` and `-1/2` on `([t, u], [s, t])`.

## The grading

A strand diagram `φ : S → T` has the homology class `[φ] = ∑ s ∈ S, [s, φ s]`, whose boundary is
`T - S` (`TauCeti.StrandDiagram.homologyClass`), and the Maslov component
`ι(φ) = inv(φ) - m([φ], S)` (`TauCeti.StrandDiagram.twiceMaslovComponent` is `2 ι(φ)`). Its grading
is `gr'(φ) = (ι(φ), [φ])` (`TauCeti.StrandDiagram.grading`).

## Main definitions

* `TauCeti.StrandsAlgebra.H1`: the relative homology `H₁(Z', a)`, by boundaries.
* `TauCeti.StrandsAlgebra.twiceMultiplicity`: twice the multiplicity `m(c, d)`.
* `TauCeti.StrandsAlgebra.GradingGroup`: the grading group `G'(n)`, with its central element
  `TauCeti.StrandsAlgebra.GradingGroup.lambda`.
* `TauCeti.StrandDiagram.grading`: the grading `gr'` of a strand diagram.
* `TauCeti.StrandsAlgebra.gradedPiece`: the span of the strand diagrams of a given grading.

## Main results

* `TauCeti.StrandDiagram.Composable.grading_trans`: `gr'(φ ψ) = gr'(φ) gr'(ψ)` when the product
  of `φ` and `ψ` is nonzero.
* `TauCeti.StrandDiagram.grading_resolve`: every term of the differential of `φ` has grading
  `λ⁻¹ gr'(φ)`.
* `TauCeti.StrandsAlgebra.mul_mem_gradedPiece`, `TauCeti.StrandsAlgebra.one_mem_gradedPiece_one`
  and `TauCeti.StrandsAlgebra.differential_mem_gradedPiece`: the strands algebra is a
  `G'(n)`-graded differential algebra, its differential having degree `λ⁻¹`.
* `TauCeti.StrandsAlgebra.isInternal_gradedPiece`: the strands algebra is the internal direct
  sum of its graded pieces.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §3.3.1
  (the unrefined grading on `A(n, k)`).
-/

public section

noncomputable section

open Finset

namespace TauCeti

attribute [local instance] trivialMulDistribMulAction

namespace StrandsAlgebra

variable (α : Type*) [Fintype α]

/-- The relative homology group `H₁(Z', a)` of an oriented interval `Z'` relative to the finite
set `a` of points of `α`, each class recorded by its boundary: the integer functions on `α` of total
weight zero. Since `H₁(Z') = 0`, the boundary map identifies `H₁(Z', a)` with this subgroup of
`H₀(a) = α → ℤ`; the segment from `s` to `t` corresponds to `Pi.single t 1 - Pi.single s 1`. -/
def H1 : AddSubgroup (α → ℤ) where
  carrier := {f | ∑ i, f i = 0}
  add_mem' {f g} hf hg := by simp_all [sum_add_distrib]
  zero_mem' := by simp
  neg_mem' {f} hf := by simp_all

variable {α}

@[simp]
theorem mem_H1 {f : α → ℤ} : f ∈ H1 α ↔ ∑ i, f i = 0 :=
  Iff.rfl

variable [LinearOrder α]

/-- Twice the multiplicity `m(c, d)` of a relative `1`-chain `c` of the interval at a `0`-chain
`d`, where `c` is given by its boundary `f = ∂c`. At a point `p` the local multiplicities of `c`
just below and just above `p` are `-∑ q < p, f q` and `-∑ q ≤ p, f q`, and `m(c, p)` is their
average; `m(c, d) = ∑ p, d p * m(c, p)`. -/
def twiceMultiplicity : (α → ℤ) →+ (α → ℤ) →+ ℤ :=
  AddMonoidHom.mk'
    (fun f ↦ AddMonoidHom.mk' (fun d ↦ ∑ p, d p * -(∑ q with q < p, f q + ∑ q with q ≤ p, f q))
      fun d d' ↦ by simp [add_mul, sum_add_distrib])
    fun f f' ↦ AddMonoidHom.ext fun d ↦ by
      simp only [AddMonoidHom.mk'_apply, Pi.add_apply, sum_add_distrib, AddMonoidHom.add_apply]
      rw [← sum_add_distrib]
      exact sum_congr rfl fun p _ ↦ by ring

theorem twiceMultiplicity_apply (f d : α → ℤ) :
    twiceMultiplicity f d = ∑ p, d p * -(∑ q with q < p, f q + ∑ q with q ≤ p, f q) :=
  (rfl)

variable (α) in
/-- The factor set of the grading group `G'(n)`: on a pair of classes `(c₁, c₂)` of `H₁(Z', a)`,
twice `m(c₂, ∂c₁)`. It is bimultiplicative, so it is a factor set for the trivial action. -/
def gradingFactorSet : FactorSet (Multiplicative (H1 α)) (Multiplicative ℤ) :=
  FactorSet.ofBimultiplicative
    { toFun a :=
        { toFun b := .ofAdd (twiceMultiplicity (b.toAdd : α → ℤ) (a.toAdd : α → ℤ))
          map_one' := by simp
          map_mul' b b' := by simp [← ofAdd_add] }
      map_one' := MonoidHom.ext fun b ↦ by simp
      map_mul' a a' := MonoidHom.ext fun b ↦ by simp [← ofAdd_add] }
    trivialMulDistribMulAction_smul

@[simp]
theorem gradingFactorSet_apply (p : Multiplicative (H1 α) × Multiplicative (H1 α)) :
    gradingFactorSet α p =
      .ofAdd (twiceMultiplicity (p.2.toAdd : α → ℤ) (p.1.toAdd : α → ℤ)) :=
  FactorSet.ofBimultiplicative_apply _ _ p

variable (α) in
/-- The grading group `G'(n)` of the strands algebra of Lipshitz, Ozsváth and Thurston: pairs of a
Maslov component `j ∈ ½ℤ` and a class `c ∈ H₁(Z', a)`, multiplied by
`(j₁, c₁) * (j₂, c₂) = (j₁ + j₂ + m(c₂, ∂c₁), c₁ + c₂)`. An element `x` stores twice its Maslov
component in `x.left` and its class in `x.right`. It is the central extension of
`H₁(Z', a)` by `ℤ` built from `TauCeti.StrandsAlgebra.gradingFactorSet`. -/
abbrev GradingGroup : Type _ :=
  (gradingFactorSet α).Extension

namespace GradingGroup

variable (α) in
/-- The central element `λ = (1, 0)` of the grading group, of Maslov component `1`. The
differential of the strands algebra has degree `λ⁻¹`. -/
def lambda : GradingGroup α :=
  FactorSet.inl _ (.ofAdd 2)

@[simp]
theorem lambda_left : (lambda α).left = .ofAdd 2 :=
  FactorSet.inl_left _ _

@[simp]
theorem lambda_right : (lambda α).right = 1 :=
  FactorSet.inl_right _ _

/-- The element `λ` is central. -/
theorem lambda_mem_center : lambda α ∈ Subgroup.center (GradingGroup α) :=
  FactorSet.inl_range_le_center _ trivialMulDistribMulAction_smul ⟨_, rfl⟩

/-- Multiplying by `λ` adds one to the Maslov component, that is two to its double. -/
theorem lambda_mul (x : GradingGroup α) : lambda α * x = ⟨.ofAdd 2 * x.left, x.right⟩ := by
  ext <;> simp

end GradingGroup

end StrandsAlgebra

namespace StrandDiagram

open StrandsAlgebra

variable {α : Type*} [LinearOrder α] [Fintype α] {φ ψ : StrandDiagram α}

/-- The homology class `[φ] = ∑ s ∈ S, [s, φ s]` in `H₁(Z', a)` of a strand diagram `φ : S → T`,
recorded by its boundary `∑ s ∈ S, (φ s - s)`. -/
def homologyClass (φ : StrandDiagram α) : H1 α :=
  ⟨∑ x ∈ φ.source, (Pi.single (φ.endpoint x) 1 - Pi.single x 1), by
    rw [mem_H1]
    simp only [Finset.sum_apply, Pi.sub_apply]
    rw [sum_comm]
    simp⟩

/-- The boundary of the homology class of `φ : S → T` is `T - S`. -/
theorem coe_homologyClass (φ : StrandDiagram α) :
    (φ.homologyClass : α → ℤ) =
      (φ.target : Set α).indicator 1 - (φ.source : Set α).indicator 1 := by
  ext i
  have h := sum_source_endpoint φ fun y ↦ (Pi.single y (1 : ℤ) : α → ℤ) i
  simp only [homologyClass, Finset.sum_apply, Pi.sub_apply, sum_sub_distrib, h]
  simp [Set.indicator_apply, Pi.single_apply]

@[simp]
theorem homologyClass_idOn (s : Finset α) : (idOn s).homologyClass = 0 := by
  ext1
  simp [coe_homologyClass]

/-- Homology classes add under concatenation. -/
theorem homologyClass_trans_of_target_eq (h : φ.target = ψ.source) :
    (φ.trans ψ).homologyClass = φ.homologyClass + ψ.homologyClass := by
  ext1
  rw [AddSubgroup.coe_add, coe_homologyClass, coe_homologyClass, coe_homologyClass,
    source_trans_of_target_eq h, target_trans_of_target_eq h, h]
  abel

/-- Resolving a crossing does not change the homology class. -/
@[simp]
theorem homologyClass_resolve (φ : StrandDiagram α) (p : α × α) :
    (φ.resolve p).homologyClass = φ.homologyClass := by
  ext1
  rw [coe_homologyClass, coe_homologyClass, source_resolve, target_resolve]

/-- Twice the Maslov component `ι(φ) = inv(φ) - m([φ], S)` of a strand diagram `φ : S → T`. -/
def twiceMaslovComponent (φ : StrandDiagram α) : ℤ :=
  2 * φ.inversionCount -
    twiceMultiplicity (φ.homologyClass : α → ℤ) ((φ.source : Set α).indicator 1)

theorem twiceMaslovComponent_def (φ : StrandDiagram α) :
    φ.twiceMaslovComponent = 2 * φ.inversionCount -
      twiceMultiplicity (φ.homologyClass : α → ℤ) ((φ.source : Set α).indicator 1) :=
  (rfl)

@[simp]
theorem twiceMaslovComponent_idOn (s : Finset α) : (idOn s).twiceMaslovComponent = 0 := by
  simp [twiceMaslovComponent_def]

/-- The Maslov component is additive on composable diagrams up to the correction term
`m([ψ], ∂[φ])` of the grading group. -/
theorem Composable.twiceMaslovComponent_trans (h : φ.Composable ψ) :
    (φ.trans ψ).twiceMaslovComponent = φ.twiceMaslovComponent + ψ.twiceMaslovComponent +
      twiceMultiplicity (ψ.homologyClass : α → ℤ) (φ.homologyClass : α → ℤ) := by
  have key : twiceMultiplicity (ψ.homologyClass : α → ℤ) (φ.homologyClass : α → ℤ) =
      twiceMultiplicity (ψ.homologyClass : α → ℤ) ((ψ.source : Set α).indicator 1) -
        twiceMultiplicity (ψ.homologyClass : α → ℤ) ((φ.source : Set α).indicator 1) := by
    rw [coe_homologyClass φ, map_sub, h.target_eq]
  rw [key, twiceMaslovComponent_def, twiceMaslovComponent_def, twiceMaslovComponent_def,
    h.inversionCount_trans,
    homologyClass_trans_of_target_eq h.target_eq, source_trans_of_target_eq h.target_eq,
    AddSubgroup.coe_add, map_add, AddMonoidHom.add_apply]
  push_cast
  ring

/-- Resolving a crossing that lowers the number of crossings by one lowers the Maslov component
by one. -/
theorem twiceMaslovComponent_resolve {p : α × α} (h : p ∈ φ.resolvableInversions) :
    (φ.resolve p).twiceMaslovComponent + 2 = φ.twiceMaslovComponent := by
  rw [twiceMaslovComponent_def, twiceMaslovComponent_def, homologyClass_resolve, source_resolve,
    ← (mem_resolvableInversions.1 h).2]
  push_cast
  ring

/-- The grading `gr'(φ) = (ι(φ), [φ])` of a strand diagram in the grading group `G'(n)`. -/
def grading (φ : StrandDiagram α) : GradingGroup α :=
  ⟨.ofAdd φ.twiceMaslovComponent, .ofAdd φ.homologyClass⟩

@[simp]
theorem grading_left (φ : StrandDiagram α) : φ.grading.left = .ofAdd φ.twiceMaslovComponent :=
  (rfl)

@[simp]
theorem grading_right (φ : StrandDiagram α) : φ.grading.right = .ofAdd φ.homologyClass :=
  (rfl)

/-- The idempotent diagrams have trivial grading. -/
@[simp]
theorem grading_idOn (s : Finset α) : (idOn s).grading = 1 := by
  ext <;> simp

/-- **The grading is multiplicative**: if the product of `φ` and `ψ` in the strands algebra is
nonzero, then `gr'(φ ψ) = gr'(φ) gr'(ψ)`. -/
theorem Composable.grading_trans (h : φ.Composable ψ) :
    (φ.trans ψ).grading = φ.grading * ψ.grading := by
  ext
  · simp [h.twiceMaslovComponent_trans, ← ofAdd_add]
  · simp [homologyClass_trans_of_target_eq h.target_eq, ← ofAdd_add]

/-- **The differential has degree `λ⁻¹`**: resolving a crossing of `φ` that lowers the number of
crossings by one gives a diagram of grading `λ⁻¹ gr'(φ)`. -/
theorem grading_resolve {p : α × α} (h : p ∈ φ.resolvableInversions) :
    (φ.resolve p).grading = (GradingGroup.lambda α)⁻¹ * φ.grading := by
  rw [eq_inv_mul_iff_mul_eq, GradingGroup.lambda_mul]
  ext
  · simp [← twiceMaslovComponent_resolve h, ← ofAdd_add, add_comm]
  · simp

end StrandDiagram

namespace StrandsAlgebra

open StrandDiagram

variable (R : Type*) {α : Type*} [CommSemiring R] [LinearOrder α] [Fintype α]

/-- The graded piece of the strands algebra in degree `g` of the grading group: the elements
whose coordinates in the basis of strand diagrams are supported on the diagrams of grading `g`. -/
def gradedPiece (g : GradingGroup α) : Submodule R (StrandsAlgebra R α) :=
  (Finsupp.supported R R (grading ⁻¹' {g})).comap (basis R α).repr.toLinearMap

/-- The graded piece of degree `g` is the span of the strand diagrams of grading `g`. -/
theorem gradedPiece_eq_span (g : GradingGroup α) :
    gradedPiece R g = Submodule.span R (of '' {φ | φ.grading = g}) := by
  rw [gradedPiece, Submodule.comap_equiv_eq_map_symm, Finsupp.supported_eq_span_single,
    Submodule.map_span, Set.image_image]
  simp only [LinearEquiv.coe_coe, Module.Basis.repr_symm_single_one, basis_apply, Set.preimage,
    Set.mem_singleton_iff]

theorem of_mem_gradedPiece (φ : StrandDiagram α) :
    (of φ : StrandsAlgebra R α) ∈ gradedPiece R φ.grading := by
  rw [gradedPiece, Submodule.mem_comap, LinearEquiv.coe_coe, ← basis_apply, Module.Basis.repr_self]
  exact Finsupp.single_mem_supported R 1 rfl

variable {R}

/-- An element lies in the graded piece of degree `g` exactly when every strand diagram in its
support has grading `g`. -/
theorem mem_gradedPiece_iff {x : StrandsAlgebra R α} {g : GradingGroup α} :
    x ∈ gradedPiece R g ↔ ∀ φ ∈ ((basis R α).repr x).support, φ.grading = g := by
  simp [gradedPiece, Finsupp.mem_supported, Set.subset_def]

theorem idem_mem_gradedPiece_one (s : Finset α) :
    (idem s : StrandsAlgebra R α) ∈ gradedPiece R 1 := by
  have h := of_mem_gradedPiece R (idOn s)
  rwa [grading_idOn, ← idem_def] at h

/-- The unit of the strands algebra has trivial grading. -/
theorem one_mem_gradedPiece_one : (1 : StrandsAlgebra R α) ∈ gradedPiece R 1 := by
  rw [← sum_idem]
  exact sum_mem fun s _ ↦ idem_mem_gradedPiece_one s

/-- **The strands algebra is graded by `G'(n)`**: the product of elements of degrees `g` and `h`
has degree `g * h`. -/
theorem mul_mem_gradedPiece {x y : StrandsAlgebra R α} {g h : GradingGroup α}
    (hx : x ∈ gradedPiece R g) (hy : y ∈ gradedPiece R h) : x * y ∈ gradedPiece R (g * h) := by
  have hxy := Submodule.mul_mem_mul hx hy
  rw [gradedPiece_eq_span, gradedPiece_eq_span, Submodule.span_mul_span] at hxy
  refine Submodule.span_le.2 ?_ hxy
  rintro _ ⟨_, ⟨φ, rfl, rfl⟩, _, ⟨ψ, rfl, rfl⟩, rfl⟩
  simp only [SetLike.mem_coe, of_mul_of]
  split_ifs with hc
  · rw [← hc.grading_trans]
    exact of_mem_gradedPiece R _
  · exact zero_mem _

/-- **The differential has degree `λ⁻¹`**: it maps the graded piece of degree `g` to that of
degree `λ⁻¹ g`. -/
theorem differential_mem_gradedPiece {x : StrandsAlgebra R α} {g : GradingGroup α}
    (hx : x ∈ gradedPiece R g) :
    differential R α x ∈ gradedPiece R ((GradingGroup.lambda α)⁻¹ * g) := by
  rw [gradedPiece_eq_span] at hx
  refine (Submodule.span_le (p := (gradedPiece R _).comap (differential R α))).2 ?_ hx
  rintro _ ⟨φ, rfl, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, differential_of]
  exact sum_mem fun p hp ↦ grading_resolve hp ▸ of_mem_gradedPiece R _

/-- The graded pieces of the strands algebra span it. -/
theorem iSup_gradedPiece : ⨆ g : GradingGroup α, gradedPiece R g = ⊤ := by
  simp only [gradedPiece, Submodule.comap_equiv_eq_map_symm, ← Submodule.map_iSup,
    ← Finsupp.supported_iUnion, ← Set.preimage_iUnion, Set.iUnion_of_singleton, Set.preimage_univ,
    Finsupp.supported_univ, Submodule.map_top, LinearEquiv.range]

/-- **The strands algebra is the internal direct sum of its graded pieces.** -/
theorem isInternal_gradedPiece [DecidableEq (GradingGroup α)] :
    DirectSum.IsInternal (gradedPiece R : GradingGroup α → _) := by
  classical
  refine ⟨fun x y hxy ↦ DirectSum.ext fun g ↦ Subtype.ext ((basis R α).repr.injective ?_),
    fun x ↦ ?_⟩
  · -- Restricting to the diagrams of grading `g` recovers the component of degree `g`.
    have key (z : DirectSum (GradingGroup α) fun h ↦ gradedPiece R h) :
        (basis R α).repr (z g) = Finsupp.restrictDom R R (grading ⁻¹' {g})
          ((basis R α).repr (DirectSum.coeAddMonoidHom _ z)) := by
      induction z using DirectSum.induction_on with
      | zero => simp
      | of h w =>
        have hw : ↑((basis R α).repr w).support ⊆ grading ⁻¹' {h} :=
          (Finsupp.mem_supported _ _).1 (Submodule.mem_comap.1 w.2)
        rw [DirectSum.coeAddMonoidHom_of, DirectSum.coe_of_apply, Finsupp.restrictDom_apply]
        split_ifs with hhg
        · subst hhg
          exact ((Finsupp.filter_eq_self_iff _ _).2 fun φ hφ ↦
            hw (Finsupp.mem_support_iff.2 hφ)).symm
        · rw [Submodule.coe_zero, map_zero, eq_comm, Finsupp.filter_eq_zero_iff]
          exact fun φ hφ ↦ Finsupp.notMem_support_iff.1 fun h' ↦ hhg ((hw h').symm.trans hφ)
      | add z z' hz hz' => simp only [DirectSum.add_apply, Submodule.coe_add, map_add, hz, hz']
    rw [key, key, hxy]
  · -- Every element is a finite sum of homogeneous elements, by `iSup_gradedPiece`.
    have hx : x ∈ ⨆ g, gradedPiece R g := by
      rw [iSup_gradedPiece]
      exact Submodule.mem_top
    induction hx using Submodule.iSup_induction' with
    | mem g y hy => exact ⟨DirectSum.of _ g ⟨y, hy⟩, DirectSum.coeAddMonoidHom_of _ _ _⟩
    | zero => exact ⟨0, map_zero _⟩
    | add y y' _ _ hy hy' =>
      obtain ⟨z, rfl⟩ := hy
      obtain ⟨z', rfl⟩ := hy'
      exact ⟨z + z', map_add _ _ _⟩

/-- The graded pieces of the strands algebra are independent. -/
theorem iSupIndep_gradedPiece : iSupIndep (gradedPiece R : GradingGroup α → _) := by
  classical
  exact isInternal_gradedPiece.submodule_iSupIndep

end StrandsAlgebra

end TauCeti
