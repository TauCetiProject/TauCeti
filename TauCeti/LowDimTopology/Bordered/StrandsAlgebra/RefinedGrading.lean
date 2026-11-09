/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Grading
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
of pairs and, for every set `s` of pairs of the same size, an element `ψ(s)` with
`M_*(∂ψ(s)) = s - s₀` (`TauCeti.MatchedGradingRefinement.shift`). The refined grading of a diagram
`φ : S → T` is

  `gr(φ) = ψ(M(S)) gr'(φ) ψ(M(T))⁻¹`

(`TauCeti.MatchedGradingRefinement.grading`). When `M` is injective on `S` and on `T` and
`#S = #s₀`, as for the diagrams of the summand `A(Z, i)` of `A(Z)` containing `I(s₀)`, it lies in
`matchedSubgroup M` (`TauCeti.MatchedGradingRefinement.grading_mem_matchedSubgroup`). The refined
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

* `TauCeti.StrandDiagram.grading_addHorizontal`, `TauCeti.StrandDiagram.grading_swapHorizontal`:
  adding or moving horizontal strands does not change the grading.
* `TauCeti.MatchedGradingRefinement.grading_mem_matchedSubgroup`: refined gradings of the diagrams
  of `A(Z, i)` lie in `matchedSubgroup M`.
* `TauCeti.MatchedGradingRefinement.grading_trans`,
  `TauCeti.MatchedGradingRefinement.grading_idOn`,
  `TauCeti.MatchedGradingRefinement.grading_eq_lambda_zpow_mul`: the refined grading is a grading.
* `TauCeti.MatchedGradingRefinement.horizontalCompletion_mem_gradedPart`,
  `TauCeti.MatchedGradingRefinement.matchedIdem_mem_gradedPart`,
  `TauCeti.MatchedGradingRefinement.mul_mem_gradedPart`,
  `TauCeti.MatchedGradingRefinement.differential_mem_gradedPart`: the generators `a(ρ, h)` and the
  idempotents `I(s)` are homogeneous, products multiply gradings and the differential has degree
  `λ⁻¹`.
* `TauCeti.MatchedGradingRefinement.nonempty`: grading refinement data exist.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687),
  Proposition 3.40 (the unrefined grading is unchanged by adding horizontal strands) and §3.3.2
  (the group `G(Z)`, Lemma 3.43, the grading refinement data (3.44), Lemma 3.45 and Remark 3.46).
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

variable [LinearOrder α]

/-- `M_*` sends the indicator of a set on which `M` is injective to the indicator of its image. -/
theorem pushBoundary_indicator {M : α → β} {S : Finset α} (hS : Set.InjOn M S) :
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

/-! ### Horizontal strands and the grading -/

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
  have hsum : ∑ s ∈ φ'.source, pointMultiplicity s φ.boundary + pointMultiplicity a φ.boundary =
      ∑ s ∈ φ.source, pointMultiplicity s φ.boundary + pointMultiplicity b φ.boundary := by
    rw [show φ'.source = _ from source_swapHorizontal h,
      sum_insert fun hb' ↦ h.notMem_source (mem_of_mem_erase hb'), ← add_sum_erase _ _ haS]
    ring
  ext
  · rw [grading_maslov, grading_maslov, hb]
    have hinv' : ((φ'.inversionCount : ℕ) : ℚ) + φ.crossingCount a =
        φ.inversionCount + φ.crossingCount b := by exact_mod_cast hinv
    rw [hma, hmb] at hsum
    linear_combination hinv' - hsum
  · rw [grading_boundary, grading_boundary, hb]

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
`b`, the element with Maslov component `0` and boundary the indicator of `σ(s)` minus that of
`σ(s₀)` serves as `ψ(s)`. -/
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
  refine ⟨⟨fun s ↦ StrandGradingGroup.mk 0
    ((fun x ↦ if x ∈ (s : Finset β).image σ then 1 else 0) -
      fun x ↦ if x ∈ s₀.image σ then 1 else 0),
    fun s ↦ mem_gPrime.2 ⟨⟨0, by simp⟩, ?_⟩, fun s ↦ ?_⟩⟩
  · simp only [mk_boundary, Pi.sub_apply, sum_sub_distrib, sum_boole, filter_mem_eq_inter,
      univ_inter, card_image_of_injective _ hσ, s.2, sub_self]
  · rw [mk_boundary, map_sub, pushBoundary_indicator (hinj _), pushBoundary_indicator (hinj _),
      himage, himage]

/-! ### Homogeneous elements -/

section GradedPart

open StrandsAlgebra

variable (R : Type*) [CommSemiring R]

/-- The part of the strands algebra of refined grading `g`: the span of the strand diagrams of
refined grading `g`. -/
def gradedPart (g : StrandGradingGroup α) : Submodule R (StrandsAlgebra R α) :=
  Submodule.span R (of '' {φ | ψ.grading φ = g})

variable {R}

theorem of_mem_gradedPart (φ : StrandDiagram α) :
    (of φ : StrandsAlgebra R α) ∈ ψ.gradedPart R (ψ.grading φ) :=
  Submodule.subset_span ⟨φ, rfl, rfl⟩

/-- **The algebra is graded by the refined grading**: the product of elements of refined gradings
`g` and `h` has refined grading `g * h`. -/
theorem mul_mem_gradedPart {g h : StrandGradingGroup α} {x y : StrandsAlgebra R α}
    (hx : x ∈ ψ.gradedPart R g) (hy : y ∈ ψ.gradedPart R h) : x * y ∈ ψ.gradedPart R (g * h) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, hφ, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨χ, hχ, rfl⟩ := hy
      rw [of_mul_of]
      split_ifs with hφχ
      · rw [← (hφ : ψ.grading φ = g), ← (hχ : ψ.grading χ = h), ← ψ.grading_trans hφχ]
        exact ψ.of_mem_gradedPart _
      · exact zero_mem _
    | zero => rw [mul_zero]; exact zero_mem _
    | add y y' _ _ hy hy' => rw [mul_add]; exact add_mem hy hy'
    | smul r y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add x x' _ _ hx hx' => rw [add_mul]; exact add_mem hx hx'
  | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx

/-- **The differential has degree `λ⁻¹` for the refined grading.** -/
theorem differential_mem_gradedPart {g : StrandGradingGroup α} {x : StrandsAlgebra R α}
    (hx : x ∈ ψ.gradedPart R g) : differential R α x ∈ ψ.gradedPart R (lambda⁻¹ * g) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, hφ, rfl⟩ := hx
    rw [differential_of]
    refine Submodule.sum_mem _ fun q hq ↦ ?_
    obtain ⟨-, hcount⟩ := mem_resolvableInversions.1 hq
    have hgr := ψ.grading_eq_lambda_zpow_mul (source_resolve φ q) (target_resolve φ q)
    rw [show ((φ.resolve q).inversionCount : ℤ) - φ.inversionCount = -1 by omega, zpow_neg_one,
      (hφ : ψ.grading φ = g)] at hgr
    exact hgr ▸ ψ.of_mem_gradedPart _
  | zero => rw [map_zero]; exact zero_mem _
  | add x x' _ _ hx hx' => rw [map_add]; exact add_mem hx hx'
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

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
