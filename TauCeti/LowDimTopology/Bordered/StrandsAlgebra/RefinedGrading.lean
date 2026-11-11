/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Grading.Basic
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Matched

/-!
# The refined grading of the algebra of a matching

The strands algebra is graded by the group `StrandGradingGroup α`, through the grading
`gr'(φ) = (inv(φ) - m([φ], S), [φ])` of a strand diagram `φ : S → T`
(`TauCeti.StrandDiagram.grading`). For the algebra `A(Z)` of a pointed matched circle `Z`, with
matching `M`, Lipshitz, Ozsváth and Thurston refine this grading to one with values in a smaller
group `G(Z)`, whose elements have homology class in `H₁(F(Z))` for the surface `F(Z)` of `Z`. This
refinement is the grading that is compatible with gluing bordered Heegaard diagrams.

A class with boundary `∂β : α → ℤ` closes up to a class on `F(Z)` exactly when its boundary
cancels along every matched pair: `M_*(∂β) = 0`, where `M_*` adds the coefficients over each pair
(`TauCeti.StrandGradingGroup.pushBoundary`). The elements of the grading group with this property
form the subgroup `TauCeti.StrandGradingGroup.matchedSubgroup M`, which contains the central
element `λ`; Lipshitz, Ozsváth and Thurston's `G(Z)` is its intersection with their group
`G'(4k)`.

The grading of a diagram itself does not lie in this subgroup: `M_*(∂[φ])` is the difference
`M(T) - M(S)` of the matched pairs occupied at the two ends. The refinement corrects this by a
choice of **grading refinement data** (`TauCeti.MatchedGradingRefinement M s₀`): a base set `s₀`
of pairs and, for every set `s` of pairs of the same size, an element `ψ(s)` of `G'` with
`M_*(∂ψ(s)) = s - s₀` (`TauCeti.MatchedGradingRefinement.shift`). The refined grading of a diagram
`φ : S → T` is

  `gr(φ) = ψ(M(S)) gr'(φ) ψ(M(T))⁻¹`

(`TauCeti.MatchedGradingRefinement.grading`). When `M` is injective on `S` and on `T` and
`#S = #s₀`, as for the diagrams of the summand `A(Z, i)` of `A(Z)` containing `I(s₀)`, it lies in
`matchedSubgroup M` (`TauCeti.MatchedGradingRefinement.grading_mem_matchedSubgroup`), and so in
`G(Z)` (`TauCeti.MatchedGradingRefinement.grading_mem_gPrime_inf_matchedSubgroup`). The refined
grading is multiplicative on composable diagrams, sends identity diagrams to `1`, and changes by
the central `λ` exactly as the unrefined one, so the differential still has degree `λ⁻¹`.

It is constant on the summands of each generator `a(ρ, h)` of `A(Z)`, the sum of the diagrams
obtained from `ρ` by adding a horizontal strand at one point of each pair in `h`. For the unrefined
grading this is the observation of Lipshitz, Ozsváth and Thurston that adding a horizontal strand
at a point `p` changes the crossing number and `m([φ], S)` by the same amount, the multiplicity of
`[φ]` at `p` (`TauCeti.StrandDiagram.grading_addHorizontal`); moving a horizontal strand between
two free points likewise leaves the grading unchanged
(`TauCeti.StrandDiagram.grading_swapHorizontal`). Since the summands occupy the same pairs, their
refined gradings agree too.

Grading refinement data exist whenever every pair is the image of a point
(`TauCeti.MatchedGradingRefinement.nonempty`), and two choices with the same base set give gradings
conjugate by the elements `ψ'(s) ψ(s)⁻¹` of `matchedSubgroup M`, which depend only on the
idempotents at the two ends (`TauCeti.MatchedGradingRefinement.grading_eq_mul_grading_mul_inv`).

## Main definitions

* `TauCeti.StrandGradingGroup.pushBoundary M`: the map `M_*` adding the coefficients of a boundary
  over the fibres of `M`.
* `TauCeti.StrandGradingGroup.matchedSubgroup M`: the elements of the grading group whose boundary
  cancels along every fibre of `M`.
* `TauCeti.MatchedGradingRefinement M s₀`: grading refinement data with base set `s₀`.
* `TauCeti.MatchedGradingRefinement.grading`: the refined grading of a strand diagram.
* `TauCeti.MatchedGradingRefinement.gradedPart`: the span of the diagrams of a given refined
  grading.

## Main results

* `TauCeti.MatchedGradingRefinement.grading_mem_matchedSubgroup`,
  `TauCeti.MatchedGradingRefinement.grading_mem_gPrime_inf_matchedSubgroup`: refined gradings of
  the diagrams of `A(Z, i)` lie in `matchedSubgroup M`, and in `G(Z)`.
* `TauCeti.MatchedGradingRefinement.grading_trans`,
  `TauCeti.MatchedGradingRefinement.grading_idOn`,
  `TauCeti.MatchedGradingRefinement.grading_eq_lambda_zpow_mul`,
  `TauCeti.MatchedGradingRefinement.grading_resolve`: the refined grading is a grading.
* `TauCeti.MatchedGradingRefinement.horizontalCompletion_mem_gradedPart`,
  `TauCeti.MatchedGradingRefinement.matchedIdem_mem_gradedPart`,
  `TauCeti.MatchedGradingRefinement.mul_mem_gradedPart`,
  `TauCeti.MatchedGradingRefinement.differential_mem_gradedPart`: the generators `a(ρ, h)` and the
  idempotents `I(s)` are homogeneous, products multiply gradings and the differential has degree
  `λ⁻¹`; a strand diagram lies in the part of its own refined grading only
  (`TauCeti.MatchedGradingRefinement.of_mem_gradedPart_iff`).
* `TauCeti.MatchedGradingRefinement.nonempty`: grading refinement data exist.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §3.3.2 (the
  group `G(Z)`, Lemma 3.43, the grading refinement data (3.44), Lemma 3.45 and Remark 3.46).
-/

public section

noncomputable section

open Finset

namespace TauCeti

namespace StrandGradingGroup

variable {α β : Type*} [Fintype α] [DecidableEq β]

/-! ### Boundaries along a matching -/

/-- The map `M_*` on boundaries: the coefficient at `b` of `M_*(δ)` is the sum of the coefficients
of `δ` over the points that `M` sends to `b`. For the matching of a pointed matched circle it adds
the coefficients at the two points of each matched pair. -/
def pushBoundary (M : α → β) : (α → ℤ) →+ (β → ℤ) where
  toFun δ b := ∑ x with M x = b, δ x
  map_zero' := by
    ext
    simp
  map_add' δ δ' := by
    ext
    simp [sum_add_distrib]

theorem pushBoundary_apply (M : α → β) (δ : α → ℤ) (b : β) :
    pushBoundary M δ b = ∑ x with M x = b, δ x :=
  (rfl)

/-- `M_*` sends the indicator of a set on which `M` is injective to the indicator of its image. -/
theorem pushBoundary_indicator [DecidableEq α] {M : α → β} {S : Finset α} (hS : Set.InjOn M S) :
    pushBoundary M (fun x ↦ if x ∈ S then 1 else 0) = fun b ↦ if b ∈ S.image M then 1 else 0 := by
  ext b
  rw [pushBoundary_apply, sum_boole, filter_filter]
  split_ifs with hb
  · obtain ⟨a, ha, rfl⟩ := mem_image.1 hb
    rw [card_eq_one.2 ⟨a, ?_⟩, Nat.cast_one]
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    refine ⟨fun h ↦ hS h.2 ha h.1, ?_⟩
    rintro rfl
    exact ⟨rfl, ha⟩
  · rw [card_eq_zero.2 (filter_eq_empty_iff.2 fun x _ h ↦ hb (mem_image.2 ⟨x, h.2, h.1⟩)),
      Nat.cast_zero]

variable [LinearOrder α]

/-- The subgroup of the grading group of the elements whose boundary cancels along every fibre of
`M`: `M_*(∂β) = 0`. For the matching `M` of a pointed matched circle `Z`, these are the elements
whose class closes up to a class on the surface `F(Z)`, and the group `G(Z)` of Lipshitz, Ozsváth
and Thurston is the intersection of this subgroup with their group `G'(4k)`. -/
def matchedSubgroup (M : α → β) : Subgroup (StrandGradingGroup α) where
  carrier := {g | pushBoundary M g.boundary = 0}
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_ofPred_eq, mul_boundary, map_add] at hg hh ⊢
    rw [hg, hh, add_zero]
  one_mem' := by simp
  inv_mem' {g} hg := by
    simp only [Set.mem_ofPred_eq, inv_boundary, map_neg] at hg ⊢
    rw [hg, neg_zero]

theorem mem_matchedSubgroup {M : α → β} {g : StrandGradingGroup α} :
    g ∈ matchedSubgroup M ↔ pushBoundary M g.boundary = 0 :=
  Iff.rfl

theorem lambda_mem_matchedSubgroup (M : α → β) :
    (lambda : StrandGradingGroup α) ∈ matchedSubgroup M := by
  simp [mem_matchedSubgroup]

end StrandGradingGroup

namespace StrandDiagram

open StrandGradingGroup

variable {α : Type*} [LinearOrder α] [Fintype α] {φ : StrandDiagram α} {a b p : α}

/-- When `M` is injective on the starting points and on the end points of `φ : S → T`, the boundary
of its class is carried by `M_*` to the difference `M(T) - M(S)` of the occupied pairs. -/
theorem pushBoundary_boundary {β : Type*} [DecidableEq β] {M : α → β}
    (hs : Set.InjOn M φ.source) (ht : Set.InjOn M φ.target) :
    pushBoundary M φ.boundary =
      (fun b ↦ if b ∈ φ.target.image M then 1 else 0) -
        fun b ↦ if b ∈ φ.source.image M then 1 else 0 := by
  have h : φ.boundary =
      (fun x ↦ if x ∈ φ.target then 1 else 0) - fun x ↦ if x ∈ φ.source then 1 else 0 :=
    funext fun x ↦ boundary_apply φ x
  rw [h, map_sub, pushBoundary_indicator hs, pushBoundary_indicator ht]

end StrandDiagram

open StrandGradingGroup StrandDiagram

variable {α β : Type*} [LinearOrder α] [Fintype α] [DecidableEq β]

/-- **Grading refinement data** for a matching `M : α → β`, with base set `s₀` of pairs
(Lipshitz, Ozsváth and Thurston, (3.44)): for every set `s` of pairs with as many elements as
`s₀`, an element `ψ(s)` of `G'` whose boundary is carried by `M_*` to `s - s₀`. These are the
choices that refine the grading of the summand of the algebra of `M` whose idempotents `I(s)` have
`#s = #s₀`. The value `ψ(s)` is read through `TauCeti.MatchedGradingRefinement.shift`. -/
@[ext]
structure MatchedGradingRefinement (M : α → β) (s₀ : Finset β) where
  /-- The element `ψ(s)` for a set `s` of pairs of the size of `s₀`. -/
  shiftOf : {s : Finset β // #s = #s₀} → StrandGradingGroup α
  /-- Each `ψ(s)` lies in `G'`. -/
  shiftOf_mem_gPrime (s) : shiftOf s ∈ gPrime
  /-- `M_*(∂ψ(s)) = s - s₀`. -/
  pushBoundary_boundary_shiftOf (s) : pushBoundary M (shiftOf s).boundary =
    (fun b ↦ if b ∈ (s : Finset β) then 1 else 0) - fun b ↦ if b ∈ s₀ then 1 else 0

namespace MatchedGradingRefinement

variable {M : α → β} {s₀ : Finset β} (ψ : MatchedGradingRefinement M s₀)

/-- The element `ψ(s)` of the grading refinement data, for every set `s` of pairs: the given choice
when `#s = #s₀`, and `1` otherwise, where no choice is made. -/
def shift (s : Finset β) : StrandGradingGroup α :=
  if h : #s = #s₀ then ψ.shiftOf ⟨s, h⟩ else 1

theorem shift_of_card_eq {s : Finset β} (h : #s = #s₀) : ψ.shift s = ψ.shiftOf ⟨s, h⟩ :=
  dite_eq_left h

theorem shift_of_card_ne {s : Finset β} (h : #s ≠ #s₀) : ψ.shift s = 1 :=
  dite_eq_right h

theorem shift_mem_gPrime (s : Finset β) : ψ.shift s ∈ gPrime := by
  unfold shift
  split_ifs
  exacts [ψ.shiftOf_mem_gPrime _, one_mem _]

theorem pushBoundary_boundary_shift {s : Finset β} (h : #s = #s₀) :
    pushBoundary M (ψ.shift s).boundary =
      (fun b ↦ if b ∈ s then 1 else 0) - fun b ↦ if b ∈ s₀ then 1 else 0 := by
  rw [shift_of_card_eq ψ h]
  exact ψ.pushBoundary_boundary_shiftOf _

/-- The **refined grading** `gr(φ) = ψ(M(S)) gr'(φ) ψ(M(T))⁻¹` of a strand diagram `φ : S → T`,
for grading refinement data `ψ` (Lipshitz, Ozsváth and Thurston, (3.44)). -/
def grading (φ : StrandDiagram α) : StrandGradingGroup α :=
  ψ.shift (φ.source.image M) * φ.grading * (ψ.shift (φ.target.image M))⁻¹

theorem grading_def (φ : StrandDiagram α) :
    ψ.grading φ = ψ.shift (φ.source.image M) * φ.grading * (ψ.shift (φ.target.image M))⁻¹ :=
  (rfl)

theorem grading_mem_gPrime (φ : StrandDiagram α) : ψ.grading φ ∈ gPrime :=
  mul_mem (mul_mem (ψ.shift_mem_gPrime _) φ.grading_mem_gPrime)
    (inv_mem (ψ.shift_mem_gPrime _))

/-- **The refined grading takes values in `matchedSubgroup M`** (Lipshitz, Ozsváth and Thurston,
Lemma 3.45) on the diagrams `φ : S → T` with no two matched starting points, no two matched end
points and `#S = #s₀`: `M_*` sends the boundary of `ψ(M(S)) gr'(φ) ψ(M(T))⁻¹` to
`(M(S) - s₀) + (M(T) - M(S)) - (M(T) - s₀) = 0`. -/
theorem grading_mem_matchedSubgroup {φ : StrandDiagram α} (hs : Set.InjOn M φ.source)
    (ht : Set.InjOn M φ.target) (hcard : #φ.source = #s₀) :
    ψ.grading φ ∈ matchedSubgroup M := by
  have hS : #(φ.source.image M) = #s₀ := (card_image_of_injOn hs).trans hcard
  have hT : #(φ.target.image M) = #s₀ :=
    (card_image_of_injOn ht).trans (φ.card_target.trans hcard)
  rw [mem_matchedSubgroup, grading_def, mul_boundary, mul_boundary, inv_boundary,
    grading_boundary, map_add, map_add, map_neg, ψ.pushBoundary_boundary_shift hS,
    ψ.pushBoundary_boundary_shift hT, pushBoundary_boundary hs ht]
  abel

/-- **The refined grading takes values in `G(Z)`**: on the diagrams `φ : S → T` with no two
matched starting points, no two matched end points and `#S = #s₀`, it lies in the intersection of
`G'` with `matchedSubgroup M`, which for the matching of a pointed matched circle `Z` is the group
`G(Z)` of Lipshitz, Ozsváth and Thurston. -/
theorem grading_mem_gPrime_inf_matchedSubgroup {φ : StrandDiagram α} (hs : Set.InjOn M φ.source)
    (ht : Set.InjOn M φ.target) (hcard : #φ.source = #s₀) :
    ψ.grading φ ∈ gPrime ⊓ matchedSubgroup M :=
  ⟨ψ.grading_mem_gPrime φ, ψ.grading_mem_matchedSubgroup hs ht hcard⟩

/-- The identity diagrams have refined grading `1`. -/
@[simp]
theorem grading_idOn (S : Finset α) : ψ.grading (idOn S) = 1 := by
  simp [grading_def]

/-- **The refined grading is multiplicative**: if the product of two strand diagrams in the strands
algebra is nonzero, the refined grading of their concatenation is the product of their refined
gradings. -/
theorem grading_trans {φ χ : StrandDiagram α} (h : φ.Composable χ) :
    ψ.grading (φ.trans χ) = ψ.grading φ * ψ.grading χ := by
  simp only [grading_def]
  rw [StrandDiagram.grading_trans h, source_trans_of_target_eq h.target_eq,
    target_trans_of_target_eq h.target_eq, h.target_eq]
  group

/-- Two diagrams with the same ends differ in refined grading by `λ` raised to the difference of
their crossing numbers, since `λ` is central. In particular resolving a crossing multiplies the
refined grading by `λ⁻¹`. -/
theorem grading_eq_lambda_zpow_mul {φ χ : StrandDiagram α} (hs : χ.source = φ.source)
    (ht : χ.target = φ.target) :
    ψ.grading χ = lambda ^ ((χ.inversionCount : ℤ) - φ.inversionCount) * ψ.grading φ := by
  have hc := Subgroup.mem_center_iff.1
    (zpow_mem (lambda_mem_center (α := α)) ((χ.inversionCount : ℤ) - φ.inversionCount))
  simp only [grading_def]
  rw [hs, ht, StrandDiagram.grading_eq_lambda_zpow_mul hs ht,
    ← mul_assoc, hc, mul_assoc, mul_assoc, mul_assoc]

/-- **The differential has degree `λ⁻¹` for the refined grading**: resolving a crossing of `φ`
that lowers the number of crossings by one multiplies the refined grading by `λ⁻¹`. -/
theorem grading_resolve {φ : StrandDiagram α} {p : α × α} (h : p ∈ φ.resolvableInversions) :
    ψ.grading (φ.resolve p) = lambda⁻¹ * ψ.grading φ := by
  rw [ψ.grading_eq_lambda_zpow_mul (source_resolve φ p) (target_resolve φ p),
    ← (mem_resolvableInversions.1 h).2]
  push_cast
  rw [sub_add_cancel_left, zpow_neg_one]

/-- Moving a horizontal strand between two matched points does not change the refined grading: the
grading and the occupied pairs stay the same. -/
@[simp]
theorem grading_swapHorizontal (φ : StrandDiagram α) {a b : α} (hab : M a = M b) :
    ψ.grading (φ.swapHorizontal a b) = ψ.grading φ := by
  wlog h : φ.CanMoveHorizontal a b generalizing a b
  · by_cases h' : φ.CanMoveHorizontal b a
    · rw [swapHorizontal_comm]
      exact this hab.symm h'
    · rw [swapHorizontal_of_not h h']
  have himage {X : Finset α} (ha : a ∈ X) : (insert b (X.erase a)).image M = X.image M := by
    rw [image_insert, ← hab, ← image_insert, insert_erase ha]
  simp only [grading_def]
  rw [StrandDiagram.grading_swapHorizontal, source_swapHorizontal h,
    target_swapHorizontal h, himage (mem_source.2 ⟨a, h.mem⟩), himage (mem_target.2 ⟨a, h.mem⟩)]

/-- **The summands of a generator `a(ρ, h)` have the same refined grading.** Adding horizontal
strands at a choice `U` of one point of each pair in `h` leaves the grading of `ρ` unchanged and
adds the pairs `h` at both ends. -/
theorem grading_addHorizontal {ρ : StrandDiagram α} {h : Finset β}
    (hρ : StrandsAlgebra.IsMatchedGenerator M ρ h) {U : Finset α}
    (hU : U ∈ StrandsAlgebra.matchedChoices M h) :
    ψ.grading (ρ.addHorizontal U) =
      ψ.shift (ρ.source.image M ∪ h) * ρ.grading * (ψ.shift (ρ.target.image M ∪ h))⁻¹ := by
  have hUh : U.image M = h := (StrandsAlgebra.mem_matchedChoices.1 hU).1
  have hs := hρ.disjoint_source_of_image_subset hUh.le
  have ht := hρ.disjoint_target_of_image_subset hUh.le
  rw [grading_def, source_addHorizontal ht, target_addHorizontal hs,
    StrandDiagram.grading_addHorizontal hs ht, image_union, image_union, hUh]

/-! ### Changing the refinement data -/

/-- Two choices of grading refinement data with the same base set differ by an element of
`matchedSubgroup M` at each set of pairs. -/
theorem shift_mul_inv_shift_mem_matchedSubgroup (ψ ψ' : MatchedGradingRefinement M s₀)
    (s : Finset β) : ψ'.shift s * (ψ.shift s)⁻¹ ∈ matchedSubgroup M := by
  by_cases h : #s = #s₀
  · rw [mem_matchedSubgroup, mul_boundary, inv_boundary, map_add, map_neg,
      ψ.pushBoundary_boundary_shift h, ψ'.pushBoundary_boundary_shift h, add_neg_cancel]
  · rw [ψ.shift_of_card_ne h, ψ'.shift_of_card_ne h, inv_one, mul_one]
    exact one_mem _

/-- **Changing the grading refinement data conjugates the refined grading** (Lipshitz, Ozsváth and
Thurston, Remark 3.46): with `ξ(s) = ψ'(s) ψ(s)⁻¹`, which lies in `matchedSubgroup M`
(`shift_mul_inv_shift_mem_matchedSubgroup`), the refined gradings of `φ : S → T` satisfy
`gr_ψ'(φ) = ξ(M(S)) gr_ψ(φ) ξ(M(T))⁻¹`. -/
theorem grading_eq_mul_grading_mul_inv (ψ ψ' : MatchedGradingRefinement M s₀)
    (φ : StrandDiagram α) :
    ψ'.grading φ = ψ'.shift (φ.source.image M) * (ψ.shift (φ.source.image M))⁻¹ *
      ψ.grading φ * (ψ'.shift (φ.target.image M) * (ψ.shift (φ.target.image M))⁻¹)⁻¹ := by
  simp only [grading_def]
  group

/-! ### Existence of refinement data -/

/-- **Grading refinement data exist** when every element of `β` is the image of a point under `M`,
as for the matching of a pointed matched circle onto its pairs. Choosing one point `σ(b)` over each
`b`, the element of `G'` with boundary `δ` the indicator of `σ(s)` minus that of `σ(s₀)`, and
Maslov component a quarter of the sum of the squares of the coefficients of `δ`, serves as
`ψ(s)`. -/
theorem nonempty (hM : Function.Surjective M) (s₀ : Finset β) :
    Nonempty (MatchedGradingRefinement M s₀) := by
  classical
  set σ := Function.surjInv hM
  have hσ : Function.Injective σ := Function.injective_surjInv hM
  have hMσ (b : β) : M (σ b) = b := Function.surjInv_eq hM b
  have hinj (s : Finset β) : Set.InjOn M (s.image σ : Set α) := by
    rintro _ hx _ hy hxy
    obtain ⟨x, -, rfl⟩ := mem_image.1 (mem_coe.1 hx)
    obtain ⟨y, -, rfl⟩ := mem_image.1 (mem_coe.1 hy)
    rw [hMσ, hMσ] at hxy
    rw [hxy]
  have himage (s : Finset β) : (s.image σ).image M = s := by
    rw [image_image]
    simp [Function.comp_def, hMσ]
  let δ (s : {s : Finset β // #s = #s₀}) : α → ℤ :=
    (fun x ↦ if x ∈ (s : Finset β).image σ then 1 else 0) - fun x ↦ if x ∈ s₀.image σ then 1 else 0
  refine ⟨⟨fun s ↦ StrandGradingGroup.mk ((∑ x, (δ s x : ℚ) ^ 2) / 4) (δ s),
    fun s ↦ mem_gPrime_iff_sum_sq.2 ⟨⟨0, by simp⟩, ?_⟩, fun s ↦ ?_⟩⟩
  · simp only [δ, mk_boundary, Pi.sub_apply, sum_sub_distrib, sum_boole, filter_mem_eq_inter,
      univ_inter, card_image_of_injective _ hσ, s.2, sub_self]
  · rw [mk_boundary, map_sub, pushBoundary_indicator (hinj _), pushBoundary_indicator (hinj _),
      himage, himage]

/-! ### Homogeneous elements -/

section GradedPart

open StrandsAlgebra

variable (R : Type*) [CommSemiring R]

/-- The part of the strands algebra of refined grading `g`: the elements supported on the strand
diagrams of refined grading `g`. -/
def gradedPart (g : StrandGradingGroup α) : Submodule R (StrandsAlgebra R α) :=
  gradedPartBy R ψ.grading g

variable {R}

/-- An element has refined grading `g` exactly when every strand diagram in its support has
refined grading `g`. -/
theorem mem_gradedPart {g : StrandGradingGroup α} {x : StrandsAlgebra R α} :
    x ∈ ψ.gradedPart R g ↔ ∀ φ ∈ ((basis R α).repr x).support, ψ.grading φ = g :=
  mem_gradedPartBy

/-- The part of refined grading `g` is the span of the strand diagrams of refined grading `g`. -/
theorem gradedPart_eq_span (g : StrandGradingGroup α) :
    ψ.gradedPart R g = Submodule.span R (of '' {φ | ψ.grading φ = g}) :=
  gradedPartBy_eq_span _ g

/-- A strand diagram lies in the part of refined grading `g` exactly when its refined grading is
`g`. -/
@[simp]
theorem of_mem_gradedPart_iff [Nontrivial R] {φ : StrandDiagram α} {g : StrandGradingGroup α} :
    (of φ : StrandsAlgebra R α) ∈ ψ.gradedPart R g ↔ ψ.grading φ = g :=
  of_mem_gradedPartBy_iff

theorem of_mem_gradedPart (φ : StrandDiagram α) :
    (of φ : StrandsAlgebra R α) ∈ ψ.gradedPart R (ψ.grading φ) :=
  of_mem_gradedPartBy _ φ

/-- **The algebra is graded by the refined grading**: the product of elements of refined gradings
`g` and `h` has refined grading `g * h`. -/
theorem mul_mem_gradedPart {g h : StrandGradingGroup α} {x y : StrandsAlgebra R α}
    (hx : x ∈ ψ.gradedPart R g) (hy : y ∈ ψ.gradedPart R h) : x * y ∈ ψ.gradedPart R (g * h) :=
  mul_mem_gradedPartBy ψ.grading_trans hx hy

/-- **The differential has degree `λ⁻¹` for the refined grading.** -/
theorem differential_mem_gradedPart {g : StrandGradingGroup α} {x : StrandsAlgebra R α}
    (hx : x ∈ ψ.gradedPart R g) : differential R α x ∈ ψ.gradedPart R (lambda⁻¹ * g) :=
  differential_mem_gradedPartBy (f := (lambda⁻¹ * ·)) ψ.grading_resolve hx

/-- **The generators `a(ρ, h)` are homogeneous for the refined grading**, of grading
`ψ(M(S) ∪ h) gr'(ρ) ψ(M(T) ∪ h)⁻¹` for `ρ : S → T`. -/
theorem horizontalCompletion_mem_gradedPart {ρ : StrandDiagram α} {h : Finset β}
    (hρ : StrandsAlgebra.IsMatchedGenerator M ρ h) :
    (horizontalCompletion M ρ h : StrandsAlgebra R α) ∈
      ψ.gradedPart R
        (ψ.shift (ρ.source.image M ∪ h) * ρ.grading * (ψ.shift (ρ.target.image M ∪ h))⁻¹) := by
  rw [horizontalCompletion_def]
  refine Submodule.sum_mem _ fun U hU ↦ ?_
  rw [← ψ.grading_addHorizontal hρ hU]
  exact ψ.of_mem_gradedPart _

/-- The idempotents `I(s)` of the algebra of the matching have refined grading `1`. -/
theorem matchedIdem_mem_gradedPart (s : Finset β) :
    (matchedIdem R M s : StrandsAlgebra R α) ∈ ψ.gradedPart R 1 := by
  rw [matchedIdem_def]
  refine Submodule.sum_mem _ fun S _ ↦ ?_
  rw [idem_def, ← ψ.grading_idOn S]
  exact ψ.of_mem_gradedPart _

end GradedPart

end MatchedGradingRefinement

end TauCeti
