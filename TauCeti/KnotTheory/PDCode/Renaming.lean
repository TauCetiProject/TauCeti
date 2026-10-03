/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Basic

/-!
# Renaming PD-codes across finite index types

The basic relabelling operation on a PD-code uses permutations, so its source and target have the
same syntactic crossing count. This file supplies the corresponding operation for equivalences
between two finite crossing types. It is useful when two equal crossing counts arise from
different expressions, for example before and after rotating a list of crossings.

The equivalence on crossing names induces an equivalence on crossing-slot blocks. An independent
equivalence renames the half-edges, and `rename` transports all remaining diagram data along these
two equivalences. When both equivalences are permutations, `rename` is definitionally the existing
`relabel` operation.

## Main definitions

* `TauCeti.PDCode.crossingBlockEquiv`: the half-edge equivalence induced by an equivalence of
  crossing names.
* `TauCeti.PDCode.rename`: rename an unoriented PD-code across equivalent finite types.
* `TauCeti.OrientedPDCode.rename`: rename an oriented PD-code across equivalent finite types.
* `TauCeti.FramedOrientedPDCode.rename`: rename a framed oriented PD-code across equivalent finite
  types.

## Main results

* `TauCeti.PDCode.rename_rename`, `TauCeti.OrientedPDCode.rename_rename`, and
  `TauCeti.FramedOrientedPDCode.rename_rename`: consecutive renamings compose.
* `TauCeti.PDCode.rename_eq_relabel`, `TauCeti.OrientedPDCode.rename_eq_relabel`, and
  `TauCeti.FramedOrientedPDCode.rename_eq_relabel`: on a fixed crossing count, renaming agrees
  with relabelling.
* `TauCeti.OrientedPDCode.writhe_rename`: renaming preserves the writhe.
-/

public section

namespace TauCeti

namespace PDCode

/-- The equivalence of half-edge positions induced by an equivalence of crossing names. It changes
the crossing coordinate and preserves the slot coordinate. -/
def crossingBlockEquiv {n m : ℕ} (cross : Fin n ≃ Fin m) :
    Fin (4 * n) ≃ Fin (4 * m) :=
  (crossingSlotEquiv n).symm |>.trans
    ((cross.prodCongr (Equiv.refl (Fin 4))).trans (crossingSlotEquiv m))

/-- A crossing-block equivalence changes the crossing coordinate and preserves its slot. -/
@[simp]
theorem crossingBlockEquiv_apply_crossingSlotEquiv {n m : ℕ}
    (cross : Fin n ≃ Fin m) (i : Fin n) (slot : Fin 4) :
    crossingBlockEquiv cross (crossingSlotEquiv n (i, slot)) =
      crossingSlotEquiv m (cross i, slot) := by
  simp [crossingBlockEquiv]

/-- The inverse of a crossing-block equivalence is induced by the inverse crossing
equivalence. -/
@[simp]
theorem crossingBlockEquiv_symm {n m : ℕ} (cross : Fin n ≃ Fin m) :
    (crossingBlockEquiv cross).symm = crossingBlockEquiv cross.symm := by
  refine Equiv.ext fun h ↦ ?_
  obtain ⟨⟨i, slot⟩, rfl⟩ := (crossingSlotEquiv m).surjective h
  apply (crossingBlockEquiv cross).injective
  simp

/-- The identity equivalence of crossing names induces the identity equivalence of half-edges. -/
@[simp]
theorem crossingBlockEquiv_refl (n : ℕ) :
    crossingBlockEquiv (Equiv.refl (Fin n)) = Equiv.refl (Fin (4 * n)) := by
  ext h
  obtain ⟨⟨i, slot⟩, rfl⟩ := (crossingSlotEquiv n).surjective h
  simp

/-- Crossing-block equivalences preserve composition. -/
@[simp]
theorem crossingBlockEquiv_trans {n m r : ℕ} (cross₁ : Fin n ≃ Fin m)
    (cross₂ : Fin m ≃ Fin r) :
    crossingBlockEquiv (cross₁.trans cross₂) =
      (crossingBlockEquiv cross₁).trans (crossingBlockEquiv cross₂) := by
  ext h
  obtain ⟨⟨i, slot⟩, rfl⟩ := (crossingSlotEquiv n).surjective h
  simp

/-- On a single finite type, the crossing-block equivalence is the crossing-block permutation. -/
theorem crossingBlockEquiv_eq_crossingBlockPerm {n : ℕ} (cross : Equiv.Perm (Fin n)) :
    crossingBlockEquiv cross = crossingBlockPerm cross := by
  ext h
  obtain ⟨⟨i, slot⟩, rfl⟩ := (crossingSlotEquiv n).surjective h
  simp

/-- Rename the half-edges and crossings of a PD-code along equivalences of their finite index
types. The half-edge equivalence need not be the one induced by the crossing equivalence. -/
def rename {n m : ℕ} (D : PDCode n) (half : Fin (4 * n) ≃ Fin (4 * m))
    (cross : Fin n ≃ Fin m) : PDCode m where
  halfEdge := (crossingBlockEquiv cross).equivCongr half D.halfEdge
  edgePair := PerfectMatching.congr half D.edgePair
  crossinglessComponentCount := D.crossinglessComponentCount
  overPair := Equiv.arrowCongr cross (Equiv.refl Bool) D.overPair

/-- Renaming transports the half-edge order between the new finite types. -/
@[simp]
theorem rename_halfEdge {n m : ℕ} (D : PDCode n) (half : Fin (4 * n) ≃ Fin (4 * m))
    (cross : Fin n ≃ Fin m) :
    (D.rename half cross).halfEdge =
      (crossingBlockEquiv cross).equivCongr half D.halfEdge := by
  simp [rename]

/-- Renaming transports the perfect matching along the half-edge equivalence. -/
@[simp]
theorem rename_edgePair {n m : ℕ} (D : PDCode n) (half : Fin (4 * n) ≃ Fin (4 * m))
    (cross : Fin n ≃ Fin m) :
    (D.rename half cross).edgePair = PerfectMatching.congr half D.edgePair := by
  simp [rename]

/-- Renaming preserves the number of crossing-free components. -/
@[simp]
theorem rename_crossinglessComponentCount {n m : ℕ} (D : PDCode n)
    (half : Fin (4 * n) ≃ Fin (4 * m)) (cross : Fin n ≃ Fin m) :
    (D.rename half cross).crossinglessComponentCount = D.crossinglessComponentCount := by
  simp [rename]

/-- The over-strand choice after renaming is read at the inverse old crossing name. -/
@[simp]
theorem rename_overPair {n m : ℕ} (D : PDCode n)
    (half : Fin (4 * n) ≃ Fin (4 * m)) (cross : Fin n ≃ Fin m) (i : Fin m) :
    (D.rename half cross).overPair i = D.overPair (cross.symm i) := by
  simp [rename]

/-- Renaming transports every crossing block and all of its slots along the half-edge
equivalence. -/
theorem crossing_rename {n m : ℕ} (D : PDCode n) (half : Fin (4 * n) ≃ Fin (4 * m))
    (cross : Fin n ≃ Fin m) (i : Fin n) (slot : Fin 4) :
    (D.rename half cross).crossing (cross i) slot = half (D.crossing i slot) := by
  rw [crossing_apply, rename_halfEdge, Equiv.equivCongr_apply_apply,
    crossingBlockEquiv_symm, crossingBlockEquiv_apply_crossingSlotEquiv, crossing_apply]
  rw [Equiv.symm_apply_apply]

/-- The over/under status after renaming is read at the inverse old crossing name. -/
@[simp]
theorem isOver_rename {n m : ℕ} (D : PDCode n) (half : Fin (4 * n) ≃ Fin (4 * m))
    (cross : Fin n ≃ Fin m) (i : Fin m) (slot : Fin 4) :
    (D.rename half cross).isOver i slot = D.isOver (cross.symm i) slot := by
  obtain rfl | rfl | rfl | rfl : slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 := by omega
  all_goals simp

/-- Renaming by identity equivalences leaves a PD-code unchanged. -/
@[simp]
theorem rename_refl (D : PDCode n) :
    D.rename (Equiv.refl _) (Equiv.refl _) = D := by
  apply PDCode.ext
  · simp [rename]
  · exact PerfectMatching.congr_refl D.edgePair
  · rfl
  · rfl

/-- Consecutive renamings compose their half-edge and crossing equivalences. -/
@[simp]
theorem rename_rename {n m r : ℕ} (D : PDCode n)
    (half₁ : Fin (4 * n) ≃ Fin (4 * m)) (cross₁ : Fin n ≃ Fin m)
    (half₂ : Fin (4 * m) ≃ Fin (4 * r)) (cross₂ : Fin m ≃ Fin r) :
    (D.rename half₁ cross₁).rename half₂ cross₂ =
      D.rename (half₁.trans half₂) (cross₁.trans cross₂) := by
  apply PDCode.ext
  · simp only [rename_halfEdge, crossingBlockEquiv_trans]
    exact congrArg (fun e => e D.halfEdge)
      (Equiv.equivCongr_trans (crossingBlockEquiv cross₁) half₁
        (crossingBlockEquiv cross₂) half₂)
  · simpa only [rename_edgePair] using PerfectMatching.congr_trans half₁ half₂ D.edgePair
  · rfl
  · funext i
    simp [rename]

/-- Reflection commutes with renaming. -/
@[simp]
theorem mirror_rename {n m : ℕ} (D : PDCode n)
    (half : Fin (4 * n) ≃ Fin (4 * m)) (cross : Fin n ≃ Fin m) :
    (D.rename half cross).mirror = D.mirror.rename half cross := by
  ext <;> simp

/-- For permutations of fixed finite types, renaming is the existing relabelling operation. -/
theorem rename_eq_relabel (D : PDCode n) (half : Equiv.Perm (Fin (4 * n)))
    (cross : Equiv.Perm (Fin n)) :
    D.rename half cross = D.relabel half cross := by
  apply PDCode.ext
  · rw [rename_halfEdge, relabel_halfEdge, crossingBlockEquiv_eq_crossingBlockPerm]
  · rw [rename_edgePair, relabel_edgePair]
  · simp
  · funext i
    simp

end PDCode

namespace OrientedPDCode

/-- Rename an oriented PD-code along equivalences of its half-edge and crossing index types. -/
def rename {n m : ℕ} (D : OrientedPDCode n) (half : Fin (4 * n) ≃ Fin (4 * m))
    (cross : Fin n ≃ Fin m) : OrientedPDCode m where
  toPDCode := D.toPDCode.rename half cross
  orientation := Equiv.arrowCongr half (Equiv.refl Bool) D.orientation
  orientation_edgePair := by
    intro h
    simp [PDCode.rename, Function.comp_apply]
  orientation_oppositeCrossingSlot := by
    intro i slot
    simp [PDCode.rename, Function.comp_apply, PDCode.crossingBlockEquiv]
  crossinglessComponents := D.crossinglessComponents
  crossinglessComponents_card := by simp [PDCode.rename]

/-- Forgetting orientation after renaming gives renaming of the underlying code. -/
@[simp]
theorem rename_toPDCode {n m : ℕ} (D : OrientedPDCode n)
    (half : Fin (4 * n) ≃ Fin (4 * m)) (cross : Fin n ≃ Fin m) :
    (D.rename half cross).toPDCode = D.toPDCode.rename half cross := by
  simp [rename]

/-- The orientation after renaming is read at the inverse old half-edge name. -/
@[simp]
theorem rename_orientation {n m : ℕ} (D : OrientedPDCode n)
    (half : Fin (4 * n) ≃ Fin (4 * m)) (cross : Fin n ≃ Fin m) (h : Fin (4 * m)) :
    (D.rename half cross).orientation h = D.orientation (half.symm h) := by
  simp [rename]

/-- Renaming preserves the oriented crossing-free components. -/
@[simp]
theorem rename_crossinglessComponents {n m : ℕ} (D : OrientedPDCode n)
    (half : Fin (4 * n) ≃ Fin (4 * m)) (cross : Fin n ≃ Fin m) :
    (D.rename half cross).crossinglessComponents = D.crossinglessComponents := by
  simp [rename]

/-- The crossing sign after renaming is read at the inverse old crossing name. -/
@[simp]
theorem crossingSign_rename {n m : ℕ} (D : OrientedPDCode n)
    (half : Fin (4 * n) ≃ Fin (4 * m)) (cross : Fin n ≃ Fin m) (i : Fin m) :
    (D.rename half cross).crossingSign i = D.crossingSign (cross.symm i) := by
  obtain ⟨i, rfl⟩ := cross.surjective i
  simp only [crossingSign_def, rename_toPDCode, PDCode.crossing_rename,
    rename_orientation, PDCode.rename_overPair, Equiv.symm_apply_apply]

/-- Renaming matches the crossings bijectively, so it preserves the writhe. -/
@[simp]
theorem writhe_rename {n m : ℕ} (D : OrientedPDCode n)
    (half : Fin (4 * n) ≃ Fin (4 * m)) (cross : Fin n ≃ Fin m) :
    (D.rename half cross).writhe = D.writhe := by
  simp only [writhe_def, crossingSign_rename]
  exact Equiv.sum_comp cross.symm D.crossingSign

/-- Renaming by identity equivalences leaves an oriented PD-code unchanged. -/
@[simp]
theorem rename_refl (D : OrientedPDCode n) :
    D.rename (Equiv.refl _) (Equiv.refl _) = D := by
  apply OrientedPDCode.ext
  · exact PDCode.rename_refl D.toPDCode
  · funext h
    simp
  · rfl

/-- Consecutive renamings of an oriented code compose. -/
@[simp]
theorem rename_rename {n m r : ℕ} (D : OrientedPDCode n)
    (half₁ : Fin (4 * n) ≃ Fin (4 * m)) (cross₁ : Fin n ≃ Fin m)
    (half₂ : Fin (4 * m) ≃ Fin (4 * r)) (cross₂ : Fin m ≃ Fin r) :
    (D.rename half₁ cross₁).rename half₂ cross₂ =
      D.rename (half₁.trans half₂) (cross₁.trans cross₂) := by
  apply OrientedPDCode.ext
  · exact PDCode.rename_rename D.toPDCode half₁ cross₁ half₂ cross₂
  · funext h
    simp [rename]
  · rfl

/-- Reflection commutes with oriented renaming. -/
@[simp]
theorem mirror_rename {n m : ℕ} (D : OrientedPDCode n)
    (half : Fin (4 * n) ≃ Fin (4 * m)) (cross : Fin n ≃ Fin m) :
    (D.rename half cross).mirror = D.mirror.rename half cross := by
  ext <;> simp

/-- Orientation reversal commutes with oriented renaming. -/
@[simp]
theorem reverse_rename {n m : ℕ} (D : OrientedPDCode n)
    (half : Fin (4 * n) ≃ Fin (4 * m)) (cross : Fin n ≃ Fin m) :
    (D.rename half cross).reverse = D.reverse.rename half cross := by
  ext <;> simp

/-- For permutations of fixed finite types, oriented renaming is oriented relabelling. -/
theorem rename_eq_relabel (D : OrientedPDCode n) (half : Equiv.Perm (Fin (4 * n)))
    (cross : Equiv.Perm (Fin n)) :
    D.rename half cross = D.relabel half cross := by
  apply OrientedPDCode.ext
  · rw [rename_toPDCode, relabel_toPDCode]
    exact PDCode.rename_eq_relabel D.toPDCode half cross
  · funext h
    simp
  · simp

end OrientedPDCode

namespace FramedOrientedPDCode

/-- Rename a framed oriented PD-code along equivalences of its half-edge and crossing index
types, transporting the framing function along the half-edge equivalence. -/
def rename {n m : ℕ} (D : FramedOrientedPDCode n) (half : Fin (4 * n) ≃ Fin (4 * m))
    (cross : Fin n ≃ Fin m) : FramedOrientedPDCode m where
  toOrientedPDCode := D.toOrientedPDCode.rename half cross
  framing := Equiv.arrowCongr half (Equiv.refl ℤ) D.framing
  framing_edgePair := by
    intro h
    simp [OrientedPDCode.rename, PDCode.rename, Function.comp_apply]
  framing_oppositeCrossingSlot := by
    intro i slot
    simp [OrientedPDCode.rename, PDCode.rename, Function.comp_apply, PDCode.crossingBlockEquiv]
  crossinglessFramings := D.crossinglessFramings
  crossinglessFramings_map_fst := by simp [OrientedPDCode.rename]

/-- Forgetting framing after renaming gives renaming of the underlying oriented code. -/
@[simp]
theorem rename_toOrientedPDCode {n m : ℕ} (D : FramedOrientedPDCode n)
    (half : Fin (4 * n) ≃ Fin (4 * m)) (cross : Fin n ≃ Fin m) :
    (D.rename half cross).toOrientedPDCode = D.toOrientedPDCode.rename half cross := by
  simp [rename]

/-- The framing after renaming is read at the inverse old half-edge name. -/
@[simp]
theorem rename_framing {n m : ℕ} (D : FramedOrientedPDCode n)
    (half : Fin (4 * n) ≃ Fin (4 * m)) (cross : Fin n ≃ Fin m) (h : Fin (4 * m)) :
    (D.rename half cross).framing h = D.framing (half.symm h) := by
  simp [rename]

/-- Renaming preserves all crossing-free orientation-framing pairs. -/
@[simp]
theorem rename_crossinglessFramings {n m : ℕ} (D : FramedOrientedPDCode n)
    (half : Fin (4 * n) ≃ Fin (4 * m)) (cross : Fin n ≃ Fin m) :
    (D.rename half cross).crossinglessFramings = D.crossinglessFramings := by
  simp [rename]

/-- Renaming by identity equivalences leaves a framed oriented PD-code unchanged. -/
@[simp]
theorem rename_refl (D : FramedOrientedPDCode n) :
    D.rename (Equiv.refl _) (Equiv.refl _) = D := by
  apply FramedOrientedPDCode.ext
  · exact OrientedPDCode.rename_refl D.toOrientedPDCode
  · funext h
    simp
  · rfl

/-- Consecutive renamings of a framed oriented code compose. -/
@[simp]
theorem rename_rename {n m r : ℕ} (D : FramedOrientedPDCode n)
    (half₁ : Fin (4 * n) ≃ Fin (4 * m)) (cross₁ : Fin n ≃ Fin m)
    (half₂ : Fin (4 * m) ≃ Fin (4 * r)) (cross₂ : Fin m ≃ Fin r) :
    (D.rename half₁ cross₁).rename half₂ cross₂ =
      D.rename (half₁.trans half₂) (cross₁.trans cross₂) := by
  apply FramedOrientedPDCode.ext
  · exact OrientedPDCode.rename_rename D.toOrientedPDCode half₁ cross₁ half₂ cross₂
  · funext h
    simp [rename]
  · rfl

/-- Reflection commutes with framed oriented renaming. -/
@[simp]
theorem mirror_rename {n m : ℕ} (D : FramedOrientedPDCode n)
    (half : Fin (4 * n) ≃ Fin (4 * m)) (cross : Fin n ≃ Fin m) :
    (D.rename half cross).mirror = D.mirror.rename half cross := by
  ext <;> simp

/-- Orientation reversal commutes with framed oriented renaming. -/
@[simp]
theorem reverse_rename {n m : ℕ} (D : FramedOrientedPDCode n)
    (half : Fin (4 * n) ≃ Fin (4 * m)) (cross : Fin n ≃ Fin m) :
    (D.rename half cross).reverse = D.reverse.rename half cross := by
  ext <;> simp

/-- For permutations of fixed finite types, framed renaming is framed relabelling. -/
theorem rename_eq_relabel (D : FramedOrientedPDCode n) (half : Equiv.Perm (Fin (4 * n)))
    (cross : Equiv.Perm (Fin n)) :
    D.rename half cross = D.relabel half cross := by
  apply FramedOrientedPDCode.ext
  · rw [rename_toOrientedPDCode, relabel_toOrientedPDCode]
    exact OrientedPDCode.rename_eq_relabel D.toOrientedPDCode half cross
  · funext h
    simp
  · simp

end FramedOrientedPDCode

end TauCeti
