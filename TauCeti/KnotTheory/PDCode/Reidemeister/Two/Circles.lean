/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.DisjointUnion.Planar
public import TauCeti.KnotTheory.PDCode.Circle

/-!
# Reidemeister clasps between two crossing-free circles

The closed two-crossing clasp has two link components and four faces. Its two crossings
have complementary over-pair indicators, so one component passes over the other twice.
Its Kauffman bracket is the circle value, just as for the two-component unlink.

`PDCode.adjoinTwoCircleClasp` places this clasp beside any surrounding diagram. It is
compared with adjoining two crossing-free circles, including when the surrounding diagram
is empty. This supplies the second Reidemeister move whose two participating components
have no half-edges before the move. The matching closes the four ports of the local clasp
used by `PDCode.insertCircleClasp`.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, GTM 175 (1997), Chapter 1 and
  Chapter 3, Lemma 3.3.
* L. H. Kauffman, *State models and the Jones polynomial*, Topology 26 (1987), 395–407.
-/

public section

namespace TauCeti.PDCode

open Equiv Equiv.Perm TemperleyLieb

/-- The closed Reidemeister II clasp on two circles. The arcs pair labels `x` and `7 - x`:
slots `2`–`1` and `3`–`0` form the bigon, and slots `0`–`3` and `1`–`2` close its ports.
The bit `b` selects the over-strand at the first crossing. -/
def twoCircleClasp (b : Bool) : PDCode 2 where
  halfEdge := 1
  edgePair := PerfectMatching.congr (crossingSlotEquiv 2)
    (PerfectMatching.mk (prodCongr Fin.revPerm Fin.revPerm) (by decide) (by decide))
  crossinglessComponentCount := 0
  overPair := ![b, !b]

/-- The clasp numbers half-edges consecutively by crossing slots. -/
@[simp] theorem twoCircleClasp_halfEdge (b : Bool) : (twoCircleClasp b).halfEdge = 1 := (rfl)

/-- The arc matching reverses both the crossing index and the slot index. -/
@[simp] theorem twoCircleClasp_edgePair_val (b : Bool) :
    (twoCircleClasp b).edgePair.val =
      (crossingSlotEquiv 2).permCongr (prodCongr Fin.revPerm Fin.revPerm) := by
  simp [twoCircleClasp, PerfectMatching.congr_val]

/-- Both circles visit the crossings. -/
@[simp] theorem twoCircleClasp_crossinglessComponentCount (b : Bool) :
    (twoCircleClasp b).crossinglessComponentCount = 0 := (rfl)

/-- The over-pair indicators are complementary, keeping the same physical component over. -/
@[simp] theorem twoCircleClasp_overPair (b : Bool) (i : Fin 2) :
    (twoCircleClasp b).overPair i = ![b, !b] i := (rfl)

/-- Reflection exchanges the two choices of over-component. -/
@[simp] theorem mirror_twoCircleClasp (b : Bool) :
    (twoCircleClasp b).mirror = twoCircleClasp (!b) := by
  apply PDCode.ext
  · simp
  · apply Subtype.ext
    simp
  · simp
  · funext i
    fin_cases i <;> simp

/-- The clasp has two link components. -/
@[simp] theorem componentCount_twoCircleClasp (b : Bool) :
    (twoCircleClasp b).componentCount = 2 := by
  have hm : IsPerfectMatching
      (prodCongr (Equiv.refl (Fin 2)) oppositeCrossingSlot *
        prodCongr Fin.revPerm Fin.revPerm) := by
    rw [isPerfectMatching_iff, oppositeCrossingSlot_eq_swap_mul_swap]
    decide
  have hc := hm.two_mul_orbitCount
  rw [Nat.card_prod, Nat.card_fin, Nat.card_fin] at hc
  rw [componentCount_eq, crossingComponentCount_def, componentPerm_def, crossingTurn_def]
  simp only [twoCircleClasp_halfEdge, twoCircleClasp_edgePair_val]
  simp only [permCongr_eq_mul, one_mul, inv_one, mul_one,
    ← permCongr_mul, orbitCount_permCongr, twoCircleClasp_crossinglessComponentCount]
  omega

/-- The closed clasp has four complementary regions. -/
@[simp] theorem faceCount_twoCircleClasp (b : Bool) : (twoCircleClasp b).faceCount = 4 := by
  have hm : IsPerfectMatching
      (prodCongr Fin.revPerm Fin.revPerm * prodCongrRight fun _ : Fin 2 ↦ finRotate 4) := by
    rw [isPerfectMatching_iff]
    decide
  have hc := hm.two_mul_orbitCount
  rw [Nat.card_prod, Nat.card_fin, Nat.card_fin] at hc
  rw [faceCount_def, facePerm_def, crossingRotation_def]
  simp only [twoCircleClasp_halfEdge, twoCircleClasp_edgePair_val]
  simp only [permCongr_eq_mul, one_mul, inv_one, mul_one,
    ← permCongr_mul, orbitCount_permCongr]
  omega

/-- The crossing graph of the closed clasp is connected. -/
theorem isConnected_twoCircleClasp (b : Bool) :
    (twoCircleClasp b).toPermutationTriple.IsConnected := by
  rw [PermutationTriple.isConnected_iff]
  refine ⟨by decide, ⟨fun x y ↦ ?_⟩⟩
  let D := twoCircleClasp b
  have hrot := D.toPermutationTriple.σ0_mem_monodromyGroup
  have hedge := D.toPermutationTriple.σ1_mem_monodromyGroup
  simp only [toPermutationTriple_σ0] at hrot
  simp only [toPermutationTriple_σ1] at hedge
  have hpow (l : ℕ) :
      ((crossingSlotEquiv 2).permCongr (prodCongrRight fun _ : Fin 2 ↦ finRotate 4)) ^ l =
        (crossingSlotEquiv 2).permCongr ((prodCongrRight fun _ : Fin 2 ↦ finRotate 4) ^ l) := by
    simpa only [Equiv.permCongrHom_coe] using
      (map_pow (crossingSlotEquiv 2).permCongrHom _ l).symm
  obtain ⟨⟨i, s⟩, rfl⟩ := (crossingSlotEquiv 2).surjective x
  obtain ⟨⟨j, t⟩, rfl⟩ := (crossingSlotEquiv 2).surjective y
  let k : ℕ := if i = j then (t - s).val else (t - s.rev).val
  let g : Perm (Fin 8) := D.crossingRotation ^ k * if i = j then 1 else D.edgePair.val
  refine ⟨⟨g, mul_mem (pow_mem hrot k) (by split <;> first | exact one_mem _ | exact hedge)⟩, ?_⟩
  -- The rotation realizes the slot difference; the matching changes crossings when necessary.
  fin_cases i <;> fin_cases j <;> fin_cases s <;> fin_cases t <;>
    simp only [Subgroup.mk_smul, Perm.smul_def, g, k, D, crossingRotation_def,
      twoCircleClasp_halfEdge, twoCircleClasp_edgePair_val,
      permCongr_eq_mul, one_mul, inv_one,
      Fin.mk.injEq, Nat.zero_ne_one, Nat.one_ne_zero, ↓reduceIte, mul_one, Perm.mul_apply, hpow,
      permCongr_apply, Equiv.symm_apply_apply, Equiv.prodCongr_apply,
      EmbeddingLike.apply_eq_iff_eq] <;> decide

/-- The closed clasp is a planar diagram. -/
@[simp] theorem isPlanar_twoCircleClasp (b : Bool) : (twoCircleClasp b).IsPlanar := by
  rw [isPlanar_iff_faceCount_eq_of_isConnected (isConnected_twoCircleClasp b)]
  simp

private def claspStateForest (c₀ c₁ : Bool) : List ((Fin 2 × Fin 4) × (Fin 2 × Fin 4)) :=
  match c₀, c₁ with
  | false, false => [((0, 0), (1, 0)), ((0, 1), (1, 1)), ((0, 2), (1, 2)), ((0, 3), (1, 3))]
  | false, true =>
      [((0, 0), (1, 2)), ((0, 0), (0, 2)), ((0, 0), (1, 0)),
        ((0, 1), (1, 3)), ((0, 1), (0, 3)), ((0, 1), (1, 1))]
  | true, false =>
      [((0, 0), (1, 0)), ((0, 0), (0, 2)), ((0, 0), (1, 2)),
        ((0, 1), (1, 1)), ((0, 1), (0, 3)), ((0, 1), (1, 3))]
  | true, true => [((0, 0), (1, 2)), ((0, 1), (1, 3)), ((0, 2), (1, 0)), ((0, 3), (1, 1))]

private theorem claspStateForest_isSwapForest (c₀ c₁ : Bool) :
    (claspStateForest c₀ c₁).IsSwapForest := by
  cases c₀ <;> cases c₁ <;> simp [claspStateForest, Equiv.swap_apply_def]

private theorem smoothingTurn_mul_claspMatching (c₀ c₁ : Bool) :
    prodCongrRight ![slotSmoothing c₀, slotSmoothing c₁] *
        prodCongr Fin.revPerm Fin.revPerm =
      ((claspStateForest c₀ c₁).reverse.map (Function.uncurry Equiv.swap)).prod := by
  cases c₀ <;> cases c₁ <;>
    simp only [slotSmoothing_false, slotSmoothing_true, claspStateForest] <;> decide

/-- Equal state choices yield one smoothing circle, and unequal choices yield two. -/
@[simp] theorem stateLoopCount_twoCircleClasp (b : Bool) (s : Fin 2 → Bool) :
    (twoCircleClasp b).stateLoopCount s = if s 0 = s 1 then 1 else 2 := by
  rw [stateLoopCount_def, statePerm_def, smoothingTurn_def]
  simp only [twoCircleClasp_halfEdge, twoCircleClasp_edgePair_val,
    twoCircleClasp_crossinglessComponentCount]
  simp only [permCongr_eq_mul, one_mul, inv_one, mul_one,
    ← permCongr_mul, orbitCount_permCongr]
  obtain ⟨⟨s₀, s₁⟩, rfl⟩ := (finTwoArrowEquiv Bool).symm.surjective s
  have hchoice : (fun i ↦ slotSmoothing ((twoCircleClasp b).smoothingChoice
      ((finTwoArrowEquiv Bool).symm (s₀, s₁)) i)) =
      ![slotSmoothing (bif s₀ then b else !b), slotSmoothing (bif s₁ then !b else b)] := by
    funext i
    fin_cases i <;> cases s₀ <;> cases s₁ <;>
      simp only [finTwoArrowEquiv_symm_apply]
    all_goals first | rw [smoothingChoice_of_false _ (by rfl)] |
      rw [smoothingChoice_of_true _ (by rfl)]
    all_goals simp
  rw [hchoice, smoothingTurn_mul_claspMatching]
  have hc := (claspStateForest_isSwapForest
    (bif s₀ then b else !b) (bif s₁ then !b else b)).orbitCount_add_length
  cases b <;> cases s₀ <;> cases s₁ <;>
    norm_num [claspStateForest] at hc ⊢ <;> omega

/-- The bracket of the closed clasp equals that of the two-component unlink. -/
@[simp] theorem kauffmanBracket_twoCircleClasp {R : Type*} [CommRing R] (b : Bool) (a : Rˣ) :
    (twoCircleClasp b).kauffmanBracket a = jonesDelta a := by
  rw [kauffmanBracket_def, ← (finTwoArrowEquiv Bool).symm.sum_comp]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, stateLoopCount_twoCircleClasp,
    finTwoArrowEquiv_symm_apply, stateWeight_def, Fin.prod_univ_two]
  simp [jonesDelta_def]
  ring

/-- Adjoin a cancelling clasp between two additional circles in a disc disjoint from `D`.
It replaces the two circles of `D.adjoinCircle.adjoinCircle` by crossing-bearing circles. -/
def adjoinTwoCircleClasp {n : ℕ} (D : PDCode n) (b : Bool) : PDCode (n + 2) :=
  D.disjointUnion (twoCircleClasp b)

/-- The disjoint-union characterization of clasp adjunction. -/
theorem adjoinTwoCircleClasp_def {n : ℕ} (D : PDCode n) (b : Bool) :
    D.adjoinTwoCircleClasp b = D.disjointUnion (twoCircleClasp b) := (rfl)

/-- The old crossing-free components are retained. -/
@[simp] theorem crossinglessComponentCount_adjoinTwoCircleClasp {n : ℕ} (D : PDCode n)
    (b : Bool) : (D.adjoinTwoCircleClasp b).crossinglessComponentCount =
      D.crossinglessComponentCount := by simp [adjoinTwoCircleClasp_def]

/-- The two clasp circles contribute two link components. -/
@[simp] theorem componentCount_adjoinTwoCircleClasp {n : ℕ} (D : PDCode n) (b : Bool) :
    (D.adjoinTwoCircleClasp b).componentCount = D.componentCount + 2 := by
  simp [adjoinTwoCircleClasp_def]

/-- Reflection swaps the over-component in the adjoined clasp. -/
@[simp] theorem mirror_adjoinTwoCircleClasp {n : ℕ} (D : PDCode n) (b : Bool) :
    (D.adjoinTwoCircleClasp b).mirror = D.mirror.adjoinTwoCircleClasp (!b) := by
  simp [adjoinTwoCircleClasp_def]

/-- Adjoining the planar clasp preserves and reflects planarity of the surrounding diagram. -/
@[simp] theorem isPlanar_adjoinTwoCircleClasp {n : ℕ} (D : PDCode n) (b : Bool) :
    (D.adjoinTwoCircleClasp b).IsPlanar ↔ D.IsPlanar := by
  simp [adjoinTwoCircleClasp_def]

/-- The two-circle second move preserves the bracket in every surrounding diagram,
including the empty diagram. -/
@[simp] theorem kauffmanBracket_adjoinTwoCircleClasp {n : ℕ} {R : Type*} [CommRing R]
    (D : PDCode n) (b : Bool) (a : Rˣ) :
    (D.adjoinTwoCircleClasp b).kauffmanBracket a =
      D.adjoinCircle.adjoinCircle.kauffmanBracket a := by
  rw [adjoinTwoCircleClasp_def]
  by_cases hD : D.componentCount = 0
  · rw [kauffmanBracket_disjointUnion_of_componentCount_eq_zero_left _ _ a hD]
    have hn : n = 0 := by
      by_contra hn
      have := D.componentCount_pos hn
      omega
    subst n
    have hc : D.crossinglessComponentCount = 0 := by simpa [componentCount_eq] using hD
    simp [kauffmanBracket_eq_jonesDelta_pow, hc]
  · have hD' : 0 < D.componentCount := Nat.pos_of_ne_zero hD
    rw [kauffmanBracket_disjointUnion _ _ a hD' (by simp)]
    simp [kauffmanBracket_adjoinCircle, hD', componentCount_adjoinCircle]
    ring

end TauCeti.PDCode
