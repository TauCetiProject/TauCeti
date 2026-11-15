/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Matched
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Reverse

/-!
# The algebra of the reversed matched circle is the opposite algebra

Reversing the orientation of a pointed matched circle `Z` keeps its points and its pairs and
reverses the order of the points. Lipshitz, Ozsváth and Thurston observe that the algebra of the
reversed circle is the opposite algebra, `A(-Z) ≅ A(Z)ᵒᵖ`, compatibly with the differentials; this
is what turns a left module over `A(-Z)` into a right module over `A(Z)`. This file proves the
identification for the matched subalgebra `TauCeti.StrandsAlgebra.matchedSubalgebra R M` of an
arbitrary matching `M : α → β`.

The rotation of strand diagrams by half a turn is an isomorphism of the strands algebra of `α`
with the opposite of the strands algebra of the reversed order `αᵒᵈ`
(`TauCeti.StrandsAlgebra.reverseAlgEquiv`), and it commutes with the differential
(`TauCeti.StrandsAlgebra.unop_reverseAlgEquiv_differential`). It also commutes with moving a
horizontal strand (`TauCeti.StrandDiagram.reverse_swapHorizontal`) and it reverses sources and
targets, so it identifies the matched subalgebra of `M` with that of the same matching read on
`αᵒᵈ`, `M ∘ ofDual`, and it sends the unit `∑ₛ I(s)` to the unit. The same holds for relabelling
the points along an order isomorphism (`TauCeti.StrandsAlgebra.mapAlgEquiv`).

For the points `{1, …, n}` of a pointed matched circle `Z`, the reversed order is relabelled by
`i ↦ n + 1 - i` (`Fin.rev`), and the pairs of `-Z` are the images of the pairs of `Z`
(`TauCeti.PointedMatchedCircle.reverse_matching_apply`). So if `M` takes the same value exactly on
the pairs of `Z`, then `M ∘ Fin.rev` does so on the pairs of `-Z`, and
`TauCeti.StrandsAlgebra.matchedRevAlgEquiv M` is the isomorphism `A(Z) ≅ A(-Z)ᵒᵖ`.

## Main definitions

* `TauCeti.StrandsAlgebra.matchedMapAlgEquiv e hM`: the isomorphism of matched subalgebras
  induced by an order isomorphism `e` carrying the matching `M` to `M'`.
* `TauCeti.StrandsAlgebra.matchedReverseAlgEquiv`: the isomorphism of the matched subalgebra of `M`
  with the opposite of the matched subalgebra of `M ∘ ofDual` on the reversed order.
* `TauCeti.StrandsAlgebra.matchedRevAlgEquiv M`: for a matching of `{1, …, n}`, the isomorphism
  `A(Z) ≅ A(-Z)ᵒᵖ`.

## Main results

* `TauCeti.StrandDiagram.map_swapHorizontal`, `TauCeti.StrandDiagram.reverse_swapHorizontal`:
  relabelling and rotation commute with moving a horizontal strand.
* `TauCeti.StrandsAlgebra.mapAlgEquiv_mem_matchedSubalgebra_iff`,
  `TauCeti.StrandsAlgebra.unop_reverseAlgEquiv_mem_matchedSubalgebra_iff`: relabelling and rotation
  identify the matched subalgebras.
* `TauCeti.StrandsAlgebra.matchedMapAlgEquiv_matchedDifferential`,
  `TauCeti.StrandsAlgebra.unop_matchedReverseAlgEquiv_matchedDifferential`,
  `TauCeti.StrandsAlgebra.unop_matchedRevAlgEquiv_matchedDifferential`: these isomorphisms
  commute with the differentials.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §3.2 (the
  algebra `A(Z)` and the orientation reversal `-Z`).
-/

public section

noncomputable section

open Finset OrderDual MulOpposite

namespace TauCeti

namespace StrandDiagram

variable {α γ : Type*} [LinearOrder α] [Fintype α] [LinearOrder γ] [Fintype γ]
  {φ : StrandDiagram α}

/-! ### Moving a horizontal strand of a relabelled or rotated diagram -/

/-- A horizontal strand of a relabelled diagram can be moved between relabelled points exactly
when it can be moved in the original diagram. -/
@[simp]
theorem canMoveHorizontal_map_iff (e : α ≃o γ) {a b : α} :
    (φ.map e).CanMoveHorizontal (e a) (e b) ↔ φ.CanMoveHorizontal a b := by
  rw [canMoveHorizontal_iff, canMoveHorizontal_iff, ← Option.mem_def, apply_mem_map_apply,
    Option.mem_def, source_map, target_map, mem_map_equiv, mem_map_equiv]
  simp

/-- Relabelling along an order isomorphism commutes with moving a horizontal strand. -/
theorem map_swapHorizontal (e : α ≃o γ) (φ : StrandDiagram α) (a b : α) :
    (φ.swapHorizontal a b).map e = (φ.map e).swapHorizontal (e a) (e b) := by
  wlog h : φ.CanMoveHorizontal a b generalizing a b
  · by_cases h' : φ.CanMoveHorizontal b a
    · rw [swapHorizontal_comm, this b a h', swapHorizontal_comm]
    · rw [swapHorizontal_of_not h h', swapHorizontal_of_not ((canMoveHorizontal_map_iff e).not.2 h)
        ((canMoveHorizontal_map_iff e).not.2 h')]
  ext i j
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  rw [← Option.mem_def, ← Option.mem_def, apply_mem_map_apply, mem_swapHorizontal h,
    mem_swapHorizontal ((canMoveHorizontal_map_iff e).2 h), apply_mem_map_apply]
  simp

/-- A horizontal strand of a rotated diagram can be moved between two points exactly when it can be
moved between them in the original diagram. -/
@[simp]
theorem canMoveHorizontal_reverse_iff {a b : α} :
    φ.reverse.CanMoveHorizontal (toDual a) (toDual b) ↔ φ.CanMoveHorizontal a b := by
  rw [canMoveHorizontal_iff, canMoveHorizontal_iff, ← Option.mem_def, toDual_mem_reverse_toDual,
    Option.mem_def, source_reverse, target_reverse, mem_map_equiv, mem_map_equiv]
  simp only [toDual_symm_eq, ofDual_toDual]
  exact and_congr_right fun _ ↦ and_comm

/-- Rotation by half a turn commutes with moving a horizontal strand. -/
theorem reverse_swapHorizontal (φ : StrandDiagram α) (a b : α) :
    (φ.swapHorizontal a b).reverse = φ.reverse.swapHorizontal (toDual a) (toDual b) := by
  wlog h : φ.CanMoveHorizontal a b generalizing a b
  · by_cases h' : φ.CanMoveHorizontal b a
    · rw [swapHorizontal_comm, this b a h', swapHorizontal_comm]
    · rw [swapHorizontal_of_not h h', swapHorizontal_of_not (canMoveHorizontal_reverse_iff.not.2 h)
        (canMoveHorizontal_reverse_iff.not.2 h')]
  ext i j
  obtain ⟨i, rfl⟩ := toDual.surjective i
  obtain ⟨j, rfl⟩ := toDual.surjective j
  rw [← Option.mem_def, ← Option.mem_def, toDual_mem_reverse_toDual, mem_swapHorizontal h,
    mem_swapHorizontal (canMoveHorizontal_reverse_iff.2 h), toDual_mem_reverse_toDual]
  simp only [toDual_inj, ne_eq]
  -- A strand from `j` to `i` other than the moved one avoids `a` and `b` at both of its ends.
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨hja, _, hi⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨fun hia ↦ hja (φ.eq_of_mem_of_mem (hia ▸ hi) h.mem),
        fun hib ↦ h.notMem_target (mem_target.2 ⟨j, hib ▸ hi⟩), hi⟩
  · rintro (⟨rfl, rfl⟩ | ⟨hia, _, hi⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨fun hja ↦ hia (Option.mem_unique (hja ▸ hi) h.mem),
        fun hjb ↦ h.notMem_source (mem_source.2 ⟨i, hjb ▸ hi⟩), hi⟩

end StrandDiagram

namespace StrandsAlgebra

open StrandDiagram

variable {R α β γ : Type*} [CommSemiring R] [LinearOrder α] [Fintype α] [LinearOrder γ]
  [Fintype γ] {M : α → β} {M' : γ → β}

/-! ### Relabelling the points -/

section Relabel

/-- Relabelling the points along an order isomorphism carrying the matching `M` to `M'` identifies
the matched subalgebras. -/
theorem mapAlgEquiv_mem_matchedSubalgebra_iff (e : α ≃o γ) (hM : ∀ i, M' (e i) = M i)
    {x : StrandsAlgebra R α} :
    mapAlgEquiv e x ∈ matchedSubalgebra R M' ↔ x ∈ matchedSubalgebra R M := by
  rw [mem_matchedSubalgebra, mem_matchedSubalgebra, ← (mapEquiv e).forall_congr_right,
    ← (mapEquiv e).forall_congr_right]
  refine and_congr (forall_congr' fun φ ↦ ?_) (forall_congr' fun φ ↦ ?_)
  · simp only [mapEquiv_apply, repr_mapAlgEquiv_apply_map, source_map, target_map, coe_map,
      ← e.injective.injOn.comp_iff, Equiv.coe_toEmbedding, OrderIso.coe_toEquiv, Function.comp_def,
      hM]
  · rw [← e.toEquiv.forall_congr_right]
    refine forall_congr' fun a ↦ ?_
    rw [← e.toEquiv.forall_congr_right]
    refine forall_congr' fun b ↦ ?_
    simp only [mapEquiv_apply, OrderIso.coe_toEquiv, hM, ← map_swapHorizontal,
      repr_mapAlgEquiv_apply_map]

variable [DecidableEq β]

/-- Relabelling the points along an order isomorphism carrying the matching `M` to `M'` sends the
idempotent `I(s)` of the matched subalgebra of `M` to that of `M'`. -/
theorem mapAlgEquiv_matchedIdem (e : α ≃o γ) (hM : ∀ i, M' (e i) = M i) (s : Finset β) :
    mapAlgEquiv e (matchedIdem R M s) = matchedIdem R M' s := by
  rw [matchedIdem_def, matchedIdem_def, map_sum]
  refine sum_equiv e.toEquiv.finsetCongr (fun S ↦ ?_) fun S _ ↦ ?_
  · simp only [mem_filter, mem_univ, true_and, Equiv.finsetCongr_apply, card_map]
    rw [map_eq_image, image_image]
    simp [Function.comp_def, hM]
  · rw [mapAlgEquiv_idem, Equiv.finsetCongr_apply]

/-- Relabelling the points along an order isomorphism carrying the matching `M` to `M'` sends the
unit `∑ₛ I(s)` of the matched subalgebra of `M` to that of `M'`. -/
theorem mapAlgEquiv_matchedOne (e : α ≃o γ) (hM : ∀ i, M' (e i) = M i) :
    mapAlgEquiv e (matchedOne R M) = matchedOne R M' := by
  have : univ.image M' = univ.image M := by
    rw [← image_univ_equiv e.toEquiv, image_image]
    simp [Function.comp_def, hM]
  rw [matchedOne_def, matchedOne_def, map_sum, this]
  simp [mapAlgEquiv_matchedIdem e hM]

/-- The isomorphism of matched subalgebras induced by an order isomorphism `e : α ≃o γ` carrying
the matching `M` to `M'`, relabelling the points of each strand diagram along `e`. -/
def matchedMapAlgEquiv (e : α ≃o γ) (hM : ∀ i, M' (e i) = M i) :
    matchedSubalgebra R M ≃ₐ[R] matchedSubalgebra R M' where
  toFun x := ⟨mapAlgEquiv e (x : StrandsAlgebra R α),
    (mapAlgEquiv_mem_matchedSubalgebra_iff e hM).2 x.2⟩
  invFun y := ⟨(mapAlgEquiv e).symm (y : StrandsAlgebra R γ),
    (mapAlgEquiv_mem_matchedSubalgebra_iff e hM).1 (by rw [AlgEquiv.apply_symm_apply]; exact y.2)⟩
  left_inv x := Subtype.ext ((mapAlgEquiv e).symm_apply_apply (x : StrandsAlgebra R α))
  right_inv y := Subtype.ext ((mapAlgEquiv e).apply_symm_apply (y : StrandsAlgebra R γ))
  map_mul' x y := Subtype.ext (map_mul (mapAlgEquiv e) (x : StrandsAlgebra R α) y)
  map_add' x y := Subtype.ext (map_add (mapAlgEquiv e) (x : StrandsAlgebra R α) y)
  commutes' r := Subtype.ext (by
    simp [Algebra.algebraMap_eq_smul_one, mapAlgEquiv_matchedOne e hM])

@[simp]
theorem coe_matchedMapAlgEquiv (e : α ≃o γ) (hM : ∀ i, M' (e i) = M i)
    (x : matchedSubalgebra R M) :
    (matchedMapAlgEquiv e hM x : StrandsAlgebra R γ) = mapAlgEquiv e (x : StrandsAlgebra R α) :=
  (rfl)

/-- The relabelling isomorphism of matched subalgebras commutes with the differentials. -/
theorem matchedMapAlgEquiv_matchedDifferential (e : α ≃o γ) (hM : ∀ i, M' (e i) = M i)
    (x : matchedSubalgebra R M) :
    matchedMapAlgEquiv e hM (matchedDifferential R M x) =
      matchedDifferential R M' (matchedMapAlgEquiv e hM x) :=
  Subtype.ext (by simp [mapAlgEquiv_differential])

end Relabel

/-! ### Rotation by half a turn -/

section Reverse

/-- Rotation by half a turn identifies the matched subalgebra of `M` with that of the same matching
on the reversed order. -/
theorem unop_reverseAlgEquiv_mem_matchedSubalgebra_iff {x : StrandsAlgebra R α} :
    unop (reverseAlgEquiv x) ∈ matchedSubalgebra R (M ∘ ofDual) ↔ x ∈ matchedSubalgebra R M := by
  rw [mem_matchedSubalgebra, mem_matchedSubalgebra, ← reverseEquiv.forall_congr_right,
    ← reverseEquiv.forall_congr_right]
  refine and_congr (forall_congr' fun φ ↦ ?_) (forall_congr' fun φ ↦ ?_)
  · simp only [reverseEquiv_apply, Module.Basis.repr_unop_eq_mulOpposite_repr,
      mulOpposite_repr_reverseAlgEquiv_apply_reverse, source_reverse, target_reverse, coe_map,
      ← toDual.injective.injOn.comp_iff, Equiv.coe_toEmbedding, Function.comp_def, ofDual_toDual]
    exact imp_congr_right fun _ ↦ and_comm
  · rw [← toDual.forall_congr_right]
    refine forall_congr' fun a ↦ ?_
    rw [← toDual.forall_congr_right]
    refine forall_congr' fun b ↦ ?_
    simp only [reverseEquiv_apply, Function.comp_apply, ofDual_toDual, ← reverse_swapHorizontal,
      Module.Basis.repr_unop_eq_mulOpposite_repr, mulOpposite_repr_reverseAlgEquiv_apply_reverse]

variable [DecidableEq β]

/-- Rotation by half a turn sends the idempotent `I(s)` of the matched subalgebra of `M` to that
of the same matching on the reversed order. -/
@[simp]
theorem reverseAlgEquiv_matchedIdem (s : Finset β) :
    reverseAlgEquiv (matchedIdem R M s) = op (matchedIdem R (M ∘ ofDual) s) := by
  rw [matchedIdem_def, matchedIdem_def, map_sum, op_sum]
  refine sum_equiv toDual.finsetCongr (fun S ↦ ?_) fun S _ ↦ ?_
  · simp only [mem_filter, mem_univ, true_and, Equiv.finsetCongr_apply, card_map]
    rw [map_eq_image, image_image]
    simp [Function.comp_def]
  · rw [reverseAlgEquiv_idem, Equiv.finsetCongr_apply]

/-- Rotation by half a turn sends the unit `∑ₛ I(s)` of the matched subalgebra of `M` to that of
the same matching on the reversed order. -/
@[simp]
theorem reverseAlgEquiv_matchedOne :
    reverseAlgEquiv (matchedOne R M) = op (matchedOne R (M ∘ ofDual)) := by
  have : univ.image (M ∘ ofDual) = univ.image M := by
    rw [← image_image, image_univ_equiv ofDual]
  rw [matchedOne_def, matchedOne_def, map_sum, op_sum, this]
  simp

variable (R M) in
/-- **The algebra of the reversed matched circle is the opposite algebra.** Rotating strand
diagrams by half a turn is an isomorphism of the matched subalgebra of `M` with the opposite of the
matched subalgebra of the same matching on the reversed order `αᵒᵈ`. -/
def matchedReverseAlgEquiv : matchedSubalgebra R M ≃ₐ[R] (matchedSubalgebra R (M ∘ ofDual))ᵐᵒᵖ where
  toFun x := op ⟨unop (reverseAlgEquiv (x : StrandsAlgebra R α)),
    unop_reverseAlgEquiv_mem_matchedSubalgebra_iff.2 x.2⟩
  invFun y := ⟨reverseAlgEquiv.symm
      (op ((unop y : matchedSubalgebra R (M ∘ ofDual)) : StrandsAlgebra R αᵒᵈ)),
    unop_reverseAlgEquiv_mem_matchedSubalgebra_iff.1 (by
      rw [AlgEquiv.apply_symm_apply, unop_op]; exact (unop y).2)⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := unop_injective (Subtype.ext (by simp))
  map_mul' x y := unop_injective (Subtype.ext (by simp))
  map_add' x y := unop_injective (Subtype.ext (by simp))
  commutes' r := unop_injective (Subtype.ext (by
    simp [Algebra.algebraMap_eq_smul_one]))

@[simp]
theorem coe_unop_matchedReverseAlgEquiv (x : matchedSubalgebra R M) :
    ((unop (matchedReverseAlgEquiv R M x) : matchedSubalgebra R (M ∘ ofDual)) :
      StrandsAlgebra R αᵒᵈ) =
      unop (reverseAlgEquiv (x : StrandsAlgebra R α)) :=
  (rfl)

/-- **Orientation reversal preserves the differential of the matched subalgebra.** -/
theorem unop_matchedReverseAlgEquiv_matchedDifferential (x : matchedSubalgebra R M) :
    unop (matchedReverseAlgEquiv R M (matchedDifferential R M x)) =
      matchedDifferential R (M ∘ ofDual) (unop (matchedReverseAlgEquiv R M x)) :=
  Subtype.ext (by simp [unop_reverseAlgEquiv_differential])

end Reverse

/-! ### The points `{1, …, n}` of a pointed matched circle -/

section Fin

variable [DecidableEq β] {n : ℕ}

variable (R) in
/-- **`A(-Z) ≅ A(Z)ᵒᵖ`.** For a matching `M` of `{1, …, n}`, rotating strand diagrams by half a
turn and relabelling the reversed order by `i ↦ n + 1 - i` (here `Fin.rev`) is an isomorphism of the
matched subalgebra of `M` with the opposite of the matched subalgebra of `M ∘ Fin.rev`. When `M`
takes the same value exactly on the pairs of a pointed matched circle `Z`, the matching
`M ∘ Fin.rev` does so on the pairs of `-Z`, so this is the isomorphism `A(Z) ≅ A(-Z)ᵒᵖ` of
Lipshitz, Ozsváth and Thurston. -/
def matchedRevAlgEquiv (M : Fin n → β) :
    matchedSubalgebra R M ≃ₐ[R] (matchedSubalgebra R (M ∘ Fin.rev))ᵐᵒᵖ :=
  (matchedReverseAlgEquiv R M).trans
    (AlgEquiv.op (matchedMapAlgEquiv Fin.revOrderIso fun i ↦ by simp))

@[simp]
theorem coe_unop_matchedRevAlgEquiv (M : Fin n → β) (x : matchedSubalgebra R M) :
    ((unop (matchedRevAlgEquiv R M x) : matchedSubalgebra R (M ∘ Fin.rev)) :
      StrandsAlgebra R (Fin n)) =
      unop (revAlgEquiv n (x : StrandsAlgebra R (Fin n))) := by
  simp [matchedRevAlgEquiv, unop_revAlgEquiv_apply, AlgEquiv.op]

/-- The isomorphism `A(Z) ≅ A(-Z)ᵒᵖ` commutes with the differentials. -/
theorem unop_matchedRevAlgEquiv_matchedDifferential (M : Fin n → β) (x : matchedSubalgebra R M) :
    unop (matchedRevAlgEquiv R M (matchedDifferential R M x)) =
      matchedDifferential R (M ∘ Fin.rev) (unop (matchedRevAlgEquiv R M x)) :=
  Subtype.ext (by
    simp [unop_revAlgEquiv_differential])

end Fin

end StrandsAlgebra

end TauCeti
