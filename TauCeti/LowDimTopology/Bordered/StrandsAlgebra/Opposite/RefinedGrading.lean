/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Opposite.Basic
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.RefinedGrading

/-!
# The refined grading under orientation reversal

The algebra of the reversed pointed matched circle is the opposite algebra, `A(-Z) ≅ A(Z)ᵒᵖ`
(`TauCeti.StrandsAlgebra.matchedRevAlgEquiv`), and on the unrefined grading group the reversal is
the anti-isomorphism `R : G'(n) ≃ G'(n)ᵒᵖ` that keeps the Maslov component and negates the
boundary (`TauCeti.StrandGradingGroup.rev`). This file carries the reversal over to the
**refined** grading of Lipshitz, Ozsváth and Thurston, with values in the group `G(Z)`, which is
the grading compatible with gluing bordered Heegaard diagrams. It is the grading-level input for
passing between right modules over `A(Z)` and left modules over `A(-Z)`, as in the pairing of type
`A` and type `D` invariants.

Three facts make this work, for a matching `M` and the same matching `M ∘ ofDual` read on the
reversed order, and likewise for a relabelling of the points along an order isomorphism.

* The reversal carries `matchedSubgroup M` onto `matchedSubgroup (M ∘ ofDual)`, since it negates
  the boundary and `M_*` is linear
  (`TauCeti.StrandGradingGroup.unop_reverse_mem_matchedSubgroup_iff`). So it restricts to an
  anti-isomorphism `G(Z) ≃ G(-Z)ᵒᵖ` (`TauCeti.StrandGradingGroup.matchedRev`).
* Grading refinement data `ψ` for `M`, with `M_*(∂ψ(s)) = s - s₀`, give grading refinement data
  for the reversed matching with the same base set, `s ↦ R(ψ(s))⁻¹`
  (`TauCeti.MatchedGradingRefinement.reverse`): the inverse undoes the sign of the boundary.
* With these data, rotating a diagram by half a turn reverses its refined grading,
  `gr(φ.reverse) = R(gr(φ))` (`TauCeti.MatchedGradingRefinement.grading_reverse`). For `φ : S → T`
  the rotated diagram runs from `T` to `S`, and `R` reverses the order of the product
  `ψ(M(S)) gr'(φ) ψ(M(T))⁻¹`, so the inverses in the reversed data are exactly what is needed.

Consequently the isomorphism `A(Z) ≅ A(-Z)ᵒᵖ` carries the part of refined grading `g` onto the part
of refined grading `R(g)`
(`TauCeti.MatchedGradingRefinement.coe_unop_matchedRevAlgEquiv_mem_gradedPart_iff`).
Reversing twice gives back the original data up to the identification `α ≃o αᵒᵈᵒᵈ`
(`TauCeti.MatchedGradingRefinement.reverse_reverse`).

## Main definitions

* `TauCeti.StrandGradingGroup.matchedMap`, `TauCeti.StrandGradingGroup.matchedReverse`,
  `TauCeti.StrandGradingGroup.matchedRev`: the restrictions of relabelling and reversal to the
  groups `G' ⊓ matchedSubgroup M`, the last being the anti-isomorphism `G(Z) ≃ G(-Z)ᵒᵖ`. They are
  `MulEquiv.subgroupMap` followed by the identification of the image
  (`TauCeti.StrandGradingGroup.map_gPrime_inf_matchedSubgroup`,
  `TauCeti.StrandGradingGroup.map_reverse_gPrime_inf_matchedSubgroup`).
* `TauCeti.MatchedGradingRefinement.map`, `TauCeti.MatchedGradingRefinement.reverse`,
  `TauCeti.MatchedGradingRefinement.rev`: grading refinement data transported along a relabelling,
  along the reversal of the order, and to the reversed pointed matched circle.

## Main results

* `TauCeti.MatchedGradingRefinement.grading_map`,
  `TauCeti.MatchedGradingRefinement.grading_reverse`,
  `TauCeti.MatchedGradingRefinement.grading_rev`: the refined gradings of relabelled and rotated
  diagrams.
* `TauCeti.MatchedGradingRefinement.mapAlgEquiv_mem_gradedPart_iff`,
  `TauCeti.MatchedGradingRefinement.unop_reverseAlgEquiv_mem_gradedPart_iff`,
  `TauCeti.MatchedGradingRefinement.unop_revAlgEquiv_mem_gradedPart_iff`: the isomorphisms of
  strands algebras carry refined graded parts onto refined graded parts, and the corresponding
  statements for the matched subalgebras.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §3.2 (the
  orientation reversal `-Z`), §3.3.2 (the group `G(Z)` and the grading refinement data (3.44)) and
  §10.4 (the anti-homomorphism of grading groups induced by orientation reversal).
-/

public section

noncomputable section

open Finset OrderDual MulOpposite

namespace TauCeti

variable {α γ β : Type*} [LinearOrder α] [Fintype α] [LinearOrder γ] [Fintype γ] [DecidableEq β]
  {M : α → β} {M' : γ → β}

namespace StrandGradingGroup

/-! ### The subgroup `matchedSubgroup M` under relabelling and reversal -/

/-- Relabelling the points along an order isomorphism carrying `M` to `M'` does not change the sums
of the boundary over the fibres of the matching. -/
theorem pushBoundary_boundary_map (e : α ≃o γ) (hM : ∀ i, M' (e i) = M i)
    (g : StrandGradingGroup α) :
    pushBoundary M' (map e g).boundary = pushBoundary M g.boundary := by
  have hM' : M' ∘ e.toEquiv = M := funext hM
  have hb : (map e g).boundary ∘ e.toEquiv = g.boundary := by
    ext
    simp
  rw [← pushBoundary_comp_equiv e.toEquiv, hM', hb]

/-- Reversal negates the sums of the boundary over the fibres of the matching. -/
theorem pushBoundary_boundary_reverse (g : StrandGradingGroup α) :
    pushBoundary (M ∘ ofDual) (reverse g).unop.boundary = -pushBoundary M g.boundary := by
  rw [← pushBoundary_comp_equiv ofDual M, ← map_neg]
  congr 1
  ext
  simp

/-- Relabelling along an order isomorphism carrying `M` to `M'` identifies the subgroups of classes
whose boundary cancels along the matching. -/
theorem map_mem_matchedSubgroup_iff (e : α ≃o γ) (hM : ∀ i, M' (e i) = M i)
    {g : StrandGradingGroup α} : map e g ∈ matchedSubgroup M' ↔ g ∈ matchedSubgroup M := by
  rw [mem_matchedSubgroup, mem_matchedSubgroup, pushBoundary_boundary_map e hM]

/-- Reversal carries `matchedSubgroup M` onto the subgroup of the same matching on the reversed
order. -/
@[simp]
theorem unop_reverse_mem_matchedSubgroup_iff {g : StrandGradingGroup α} :
    (reverse g).unop ∈ matchedSubgroup (M ∘ ofDual) ↔ g ∈ matchedSubgroup M := by
  rw [mem_matchedSubgroup, mem_matchedSubgroup, pushBoundary_boundary_reverse, neg_eq_zero]

/-- The orientation reversal of the grading group of `{1, …, n}` carries `matchedSubgroup M` onto
`matchedSubgroup (M ∘ Fin.rev)`, the subgroup for the pairs of the reversed matched circle. -/
@[simp]
theorem unop_rev_mem_matchedSubgroup_iff {n : ℕ} {M : Fin n → β} {g : StrandGradingGroup (Fin n)} :
    (rev n g).unop ∈ matchedSubgroup (M ∘ Fin.rev) ↔ g ∈ matchedSubgroup M := by
  rw [unop_rev_apply,
    map_mem_matchedSubgroup_iff Fin.revOrderIso (M := M ∘ ofDual) (fun i ↦ by simp),
    unop_reverse_mem_matchedSubgroup_iff]

/-! ### The groups `G(Z)` under relabelling and reversal -/

/-- Relabelling along an order isomorphism carrying `M` to `M'` maps `G' ⊓ matchedSubgroup M` onto
`G' ⊓ matchedSubgroup M'`. -/
theorem map_gPrime_inf_matchedSubgroup (e : α ≃o γ) (hM : ∀ i, M' (e i) = M i) :
    (gPrime ⊓ matchedSubgroup M).map (map e : StrandGradingGroup α →* StrandGradingGroup γ) =
      gPrime ⊓ matchedSubgroup M' := by
  ext g
  obtain ⟨g, rfl⟩ := (map e).surjective g
  simp [map_mem_matchedSubgroup_iff e hM]

/-- Reversal maps `G' ⊓ matchedSubgroup M` onto the opposite of the group of the same matching on
the reversed order. -/
theorem map_reverse_gPrime_inf_matchedSubgroup :
    (gPrime ⊓ matchedSubgroup M).map (reverse (α := α)).toMonoidHom =
      (gPrime ⊓ matchedSubgroup (M ∘ ofDual)).op := by
  ext g
  obtain ⟨g, rfl⟩ := reverse.surjective g
  simp

/-- Relabelling the points along an order isomorphism carrying `M` to `M'`, as an isomorphism of
the groups `G' ⊓ matchedSubgroup M` and `G' ⊓ matchedSubgroup M'`. -/
def matchedMap (e : α ≃o γ) (hM : ∀ i, M' (e i) = M i) :
    ↥(gPrime ⊓ matchedSubgroup M) ≃* ↥(gPrime ⊓ matchedSubgroup M') :=
  ((map e).subgroupMap _).trans (MulEquiv.subgroupCongr (map_gPrime_inf_matchedSubgroup e hM))

@[simp]
theorem coe_matchedMap (e : α ≃o γ) (hM : ∀ i, M' (e i) = M i)
    (g : ↥(gPrime ⊓ matchedSubgroup M)) :
    (matchedMap e hM g : StrandGradingGroup γ) = map e g :=
  (rfl)

variable (M) in
/-- **Orientation reversal of the refined grading group.** Reversal restricts to an
anti-isomorphism from `G' ⊓ matchedSubgroup M` onto the opposite of the group of the same matching
on the reversed order. -/
def matchedReverse :
    ↥(gPrime ⊓ matchedSubgroup M) ≃* (↥(gPrime ⊓ matchedSubgroup (M ∘ ofDual)))ᵐᵒᵖ :=
  ((reverse.subgroupMap _).trans
    (MulEquiv.subgroupCongr map_reverse_gPrime_inf_matchedSubgroup)).trans
    (Subgroup.mopMulEquivOp _).symm

@[simp]
theorem coe_unop_matchedReverse (g : ↥(gPrime ⊓ matchedSubgroup M)) :
    ((matchedReverse M g).unop : StrandGradingGroup αᵒᵈ) =
      (reverse (g : StrandGradingGroup α)).unop :=
  (rfl)

variable (M) in
/-- **`G(Z) ≅ G(-Z)ᵒᵖ`.** For a matching `M` of `{1, …, n}`, the orientation reversal
`TauCeti.StrandGradingGroup.rev` restricts to an anti-isomorphism from `G' ⊓ matchedSubgroup M` onto
the opposite of `G' ⊓ matchedSubgroup (M ∘ Fin.rev)`. When `M` takes the same value exactly on the
pairs of a pointed matched circle `Z`, these are the groups `G(Z)` and `G(-Z)` of Lipshitz, Ozsváth
and Thurston, and this is the reversal matching `TauCeti.StrandsAlgebra.matchedRevAlgEquiv`. -/
def matchedRev {n : ℕ} (M : Fin n → β) :
    ↥(gPrime ⊓ matchedSubgroup M) ≃* (↥(gPrime ⊓ matchedSubgroup (M ∘ Fin.rev)))ᵐᵒᵖ :=
  (matchedReverse M).trans (MulEquiv.op (matchedMap Fin.revOrderIso fun i ↦ by simp))

@[simp]
theorem coe_unop_matchedRev {n : ℕ} (M : Fin n → β) (g : ↥(gPrime ⊓ matchedSubgroup M)) :
    ((matchedRev M g).unop : StrandGradingGroup (Fin n)) =
      (rev n (g : StrandGradingGroup (Fin n))).unop := by
  simp [matchedRev, MulEquiv.op, unop_rev_apply]

end StrandGradingGroup

namespace MatchedGradingRefinement

open StrandDiagram StrandGradingGroup

variable {s₀ : Finset β}

/-! ### Transporting grading refinement data -/

/-- Grading refinement data transported along an order isomorphism `e` carrying the matching `M` to
`M'`: the element `ψ(s)` is relabelled along `e`. -/
def map (e : α ≃o γ) (hM : ∀ i, M' (e i) = M i) (ψ : MatchedGradingRefinement M s₀) :
    MatchedGradingRefinement M' s₀ where
  shiftOf s := StrandGradingGroup.map e (ψ.shiftOf s)
  shiftOf_mem_gPrime s := (map_mem_gPrime_iff e).2 (ψ.shiftOf_mem_gPrime s)
  pushBoundary_boundary_shiftOf s := by
    rw [pushBoundary_boundary_map e hM]
    exact ψ.pushBoundary_boundary_shiftOf s

@[simp]
theorem shiftOf_map (e : α ≃o γ) (hM : ∀ i, M' (e i) = M i) (ψ : MatchedGradingRefinement M s₀)
    (s : {s : Finset β // #s = #s₀}) :
    (ψ.map e hM).shiftOf s = StrandGradingGroup.map e (ψ.shiftOf s) :=
  (rfl)

@[simp]
theorem shift_map (e : α ≃o γ) (hM : ∀ i, M' (e i) = M i) (ψ : MatchedGradingRefinement M s₀)
    (s : Finset β) : (ψ.map e hM).shift s = StrandGradingGroup.map e (ψ.shift s) := by
  by_cases h : #s = #s₀
  · rw [shift_of_card_eq _ h, shift_of_card_eq _ h, shiftOf_map]
  · rw [shift_of_card_ne _ h, shift_of_card_ne _ h, map_one]

/-- **Relabelling transports the refined grading**: for the transported refinement data, the
refined grading of a relabelled diagram is the relabelled refined grading. -/
@[simp]
theorem grading_map (e : α ≃o γ) (hM : ∀ i, M' (e i) = M i) (ψ : MatchedGradingRefinement M s₀)
    (φ : StrandDiagram α) :
    (ψ.map e hM).grading (φ.map e) = StrandGradingGroup.map e (ψ.grading φ) := by
  -- The relabelled ends occupy the same pairs.
  have himage (S : Finset α) : (S.map e.toEquiv.toEmbedding).image M' = S.image M := by
    rw [map_eq_image, image_image]
    simp [Function.comp_def, hM]
  simp only [grading_def, source_map, target_map, himage, shift_map, StrandDiagram.grading_map,
    map_mul, map_inv]

/-- Grading refinement data for the same matching on the reversed order: the element for `s` is
`R(ψ(s))⁻¹`, where `R` is the orientation reversal of the grading group. Reversal negates the
boundary, and the inverse restores `M_*(∂) = s - s₀`. -/
protected def reverse (ψ : MatchedGradingRefinement M s₀) :
    MatchedGradingRefinement (M ∘ ofDual) s₀ where
  shiftOf s := (StrandGradingGroup.reverse (ψ.shiftOf s)).unop⁻¹
  shiftOf_mem_gPrime s := inv_mem (unop_reverse_mem_gPrime_iff.2 (ψ.shiftOf_mem_gPrime s))
  pushBoundary_boundary_shiftOf s := by
    rw [inv_boundary, map_neg, pushBoundary_boundary_reverse, neg_neg]
    exact ψ.pushBoundary_boundary_shiftOf s

@[simp]
theorem shiftOf_reverse (ψ : MatchedGradingRefinement M s₀) (s : {s : Finset β // #s = #s₀}) :
    ψ.reverse.shiftOf s = (StrandGradingGroup.reverse (ψ.shiftOf s)).unop⁻¹ :=
  (rfl)

@[simp]
theorem shift_reverse (ψ : MatchedGradingRefinement M s₀) (s : Finset β) :
    ψ.reverse.shift s = (StrandGradingGroup.reverse (ψ.shift s)).unop⁻¹ := by
  by_cases h : #s = #s₀
  · rw [shift_of_card_eq _ h, shift_of_card_eq _ h, shiftOf_reverse]
  · rw [shift_of_card_ne _ h, shift_of_card_ne _ h, map_one, unop_one, inv_one]

/-- **Rotation reverses the refined grading.** For the reversed refinement data, the refined
grading of a diagram rotated by half a turn is the orientation reversal of its refined grading. -/
@[simp]
theorem grading_reverse (ψ : MatchedGradingRefinement M s₀) (φ : StrandDiagram α) :
    ψ.reverse.grading φ.reverse = (StrandGradingGroup.reverse (ψ.grading φ)).unop := by
  -- The rotated diagram runs from the end points of `φ` to its starting points, occupying the
  -- same pairs, and `R` reverses the order of the product `ψ(M(S)) gr'(φ) ψ(M(T))⁻¹`.
  have himage (S : Finset α) : (S.map toDual.toEmbedding).image (M ∘ ofDual) = S.image M := by
    rw [map_eq_image, image_image]
    simp [Function.comp_def]
  simp only [grading_def, source_reverse, target_reverse, himage, shift_reverse,
    StrandDiagram.grading_reverse, map_mul, map_inv, unop_mul, unop_inv, inv_inv, mul_assoc]

/-- Reversing twice gives back the refinement data, up to the identification `α ≃o αᵒᵈᵒᵈ`. -/
theorem reverse_reverse (ψ : MatchedGradingRefinement M s₀) :
    ψ.reverse.reverse = ψ.map (OrderIso.dualDual α) (fun _ ↦ rfl) := by
  ext s : 2
  simp only [shiftOf_reverse, map_inv, unop_inv, inv_inv, StrandGradingGroup.reverse_reverse]
  exact (shiftOf_map _ _ ψ s).symm

/-- Grading refinement data for the reversed pointed matched circle: for a matching `M` of
`{1, …, n}`, the reversed data relabelled along `i ↦ n + 1 - i` (here `Fin.rev`) are grading
refinement data for `M ∘ Fin.rev`, with the same base set. -/
def rev {n : ℕ} {M : Fin n → β} (ψ : MatchedGradingRefinement M s₀) :
    MatchedGradingRefinement (M ∘ Fin.rev) s₀ :=
  ψ.reverse.map Fin.revOrderIso fun i ↦ by simp

@[simp]
theorem shift_rev {n : ℕ} {M : Fin n → β} (ψ : MatchedGradingRefinement M s₀) (s : Finset β) :
    ψ.rev.shift s = (StrandGradingGroup.rev n (ψ.shift s)).unop⁻¹ := by
  rw [rev, shift_map, shift_reverse, map_inv, unop_rev_apply]

/-- **The refined grading of `A(-Z)`.** The anti-automorphism of the strands algebra on
`{1, …, n}`, rotating a diagram and relabelling it along `Fin.rev`, reverses the refined grading:
the refined grading for `ψ.rev` of the image of `φ` is `R(gr(φ))`. -/
@[simp]
theorem grading_rev {n : ℕ} {M : Fin n → β} (ψ : MatchedGradingRefinement M s₀)
    (φ : StrandDiagram (Fin n)) :
    ψ.rev.grading (φ.reverse.map Fin.revOrderIso) =
      (StrandGradingGroup.rev n (ψ.grading φ)).unop := by
  rw [rev, grading_map, grading_reverse, unop_rev_apply]

/-! ### Refined graded parts -/

section GradedPart

open StrandsAlgebra

variable {R : Type*} [CommSemiring R]

/-- Relabelling along an order isomorphism carrying `M` to `M'` carries the part of refined grading
`g` onto the part of the relabelled refined grading, for the transported refinement data. -/
@[simp]
theorem mapAlgEquiv_mem_gradedPart_iff (e : α ≃o γ) (hM : ∀ i, M' (e i) = M i)
    (ψ : MatchedGradingRefinement M s₀) {g : StrandGradingGroup α} {x : StrandsAlgebra R α} :
    mapAlgEquiv e x ∈ (ψ.map e hM).gradedPart R (StrandGradingGroup.map e g) ↔
      x ∈ ψ.gradedPart R g := by
  rw [gradedPart_def, gradedPart_def]
  exact mem_gradedPartBy_iff_of_basis (mapAlgEquiv e).toLinearEquiv (mapEquiv e)
    (StrandGradingGroup.map e).injective (fun φ ↦ by simp [mapAlgEquiv_of])
    (fun φ ↦ by simp)

/-- **Orientation reversal of the strands algebra is graded by the reversal of the refined grading
group**: it carries the part of refined grading `g` onto the part of refined grading `R(g)`, for
the reversed refinement data. -/
@[simp]
theorem unop_reverseAlgEquiv_mem_gradedPart_iff (ψ : MatchedGradingRefinement M s₀)
    {g : StrandGradingGroup α} {x : StrandsAlgebra R α} :
    (reverseAlgEquiv x).unop ∈ ψ.reverse.gradedPart R (StrandGradingGroup.reverse g).unop ↔
      x ∈ ψ.gradedPart R g := by
  rw [gradedPart_def, gradedPart_def]
  exact mem_gradedPartBy_iff_of_basis
    (reverseAlgEquiv.toLinearEquiv.trans (opLinearEquiv R).symm) reverseEquiv
    (unop_injective.comp StrandGradingGroup.reverse.injective) (fun φ ↦ by simp)
    (fun φ ↦ by simp)

/-- The anti-automorphism of the strands algebra on `{1, …, n}` carries the part of refined grading
`g` onto the part of refined grading `R(g)`, for the refinement data `ψ.rev`. -/
@[simp]
theorem unop_revAlgEquiv_mem_gradedPart_iff {n : ℕ} {M : Fin n → β}
    (ψ : MatchedGradingRefinement M s₀) {g : StrandGradingGroup (Fin n)}
    {x : StrandsAlgebra R (Fin n)} :
    (revAlgEquiv n x).unop ∈ ψ.rev.gradedPart R (StrandGradingGroup.rev n g).unop ↔
      x ∈ ψ.gradedPart R g := by
  rw [gradedPart_def, gradedPart_def]
  exact mem_gradedPartBy_iff_of_basis
    ((revAlgEquiv n).toLinearEquiv.trans (opLinearEquiv R).symm)
    (reverseEquiv.trans (mapEquiv Fin.revOrderIso))
    (unop_injective.comp (StrandGradingGroup.rev n).injective) (fun φ ↦ by simp)
    (fun φ ↦ by simp)

/-- The relabelling isomorphism of matched subalgebras carries the part of refined grading `g`
onto the part of the relabelled refined grading. -/
theorem coe_matchedMapAlgEquiv_mem_gradedPart_iff (e : α ≃o γ) (hM : ∀ i, M' (e i) = M i)
    (ψ : MatchedGradingRefinement M s₀) {g : StrandGradingGroup α} {x : matchedSubalgebra R M} :
    (matchedMapAlgEquiv e hM x : StrandsAlgebra R γ) ∈
        (ψ.map e hM).gradedPart R (StrandGradingGroup.map e g) ↔
      (x : StrandsAlgebra R α) ∈ ψ.gradedPart R g := by
  rw [coe_matchedMapAlgEquiv, mapAlgEquiv_mem_gradedPart_iff]

/-- The isomorphism of the matched subalgebra of `M` with the opposite of the matched subalgebra of
`M ∘ ofDual` carries the part of refined grading `g` onto the part of refined grading `R(g)`. -/
theorem coe_unop_matchedReverseAlgEquiv_mem_gradedPart_iff (ψ : MatchedGradingRefinement M s₀)
    {g : StrandGradingGroup α} {x : matchedSubalgebra R M} :
    ((unop (matchedReverseAlgEquiv R M x) : matchedSubalgebra R (M ∘ ofDual)) :
        StrandsAlgebra R αᵒᵈ) ∈ ψ.reverse.gradedPart R (StrandGradingGroup.reverse g).unop ↔
      (x : StrandsAlgebra R α) ∈ ψ.gradedPart R g := by
  rw [coe_unop_matchedReverseAlgEquiv, unop_reverseAlgEquiv_mem_gradedPart_iff]

/-- **`A(Z) ≅ A(-Z)ᵒᵖ` respects the refined gradings**: the isomorphism carries the part of
refined grading `g` onto the part of refined grading `R(g)`, for the refinement data `ψ.rev` of the
reversed pointed matched circle. -/
theorem coe_unop_matchedRevAlgEquiv_mem_gradedPart_iff {n : ℕ} {M : Fin n → β}
    (ψ : MatchedGradingRefinement M s₀) {g : StrandGradingGroup (Fin n)}
    {x : matchedSubalgebra R M} :
    ((unop (matchedRevAlgEquiv R M x) : matchedSubalgebra R (M ∘ Fin.rev)) :
        StrandsAlgebra R (Fin n)) ∈ ψ.rev.gradedPart R (StrandGradingGroup.rev n g).unop ↔
      (x : StrandsAlgebra R (Fin n)) ∈ ψ.gradedPart R g := by
  rw [coe_unop_matchedRevAlgEquiv, unop_revAlgEquiv_mem_gradedPart_iff]

end GradedPart

end MatchedGradingRefinement

end TauCeti
