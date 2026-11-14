/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.FoxColoring.Basic
public import TauCeti.KnotTheory.PDCode.Trefoil
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Abel
import Mathlib.Data.ZMod.Basic

/-!
# The Fox colourings of the trefoil diagram

A Fox colouring of the standard trefoil diagram `TauCeti.rightHandedTrefoilPDCode` is constant on
each of its three Wirtinger arcs. With labels `a₀, a₁, a₂` on the arcs, the crossing relations
read `a₁ + a₂ = 2 a₀`, `a₀ + a₂ = 2 a₁` and `a₀ + a₁ = 2 a₂`. Writing `u = a₁ - a₀`, they say
exactly that `a₂ = a₀ - u` and `3 u = 0`. So the colourings with values in `M` are the pairs of a
label `a₀ ∈ M` and an element `u` of the `3`-torsion of `M`, and the arcs carry `a₀`, `a₀ + u`
and `a₀ - u`.

Counting gives the classical values: the trefoil has `9 = 3 · 3` three-colourings and `18`
six-colourings, although `6` does not divide its determinant `3`. The crossing-free unknot has
only `3` three-colourings (`TauCeti.OrientedPDCode.natCard_foxColorings_unknot`), so together with
the Reidemeister invariance of the number of colourings
(`TauCeti.OrientedPDCode.ReidemeisterEquiv.natCard_foxColorings_eq`) three-colourings distinguish
the trefoil from the unknot.

## Main definitions

* `TauCeti.foxColoringsRightHandedTrefoilPDCodeEquiv`: the Fox colourings of the trefoil diagram
  with values in `M` are `M × M[3]`.

## Main results

* `TauCeti.natCard_foxColorings_rightHandedTrefoilPDCode`: the trefoil diagram has
  `|M| · |M[3]|` colourings with values in `M`.
* `TauCeti.natCard_foxColorings_rightHandedTrefoilPDCode_zmod_three`: it has `9`
  three-colourings.
* `TauCeti.natCard_foxColorings_rightHandedTrefoilPDCode_zmod_six`: it has `18` six-colourings.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Graduate Texts in Mathematics 175,
  Springer (1997), Chapter 3.
* J. H. Przytycki, *3-coloring and other elementary invariants of knots*, Banach Center
  Publications 42 (1998), 275–295.
-/

public section

namespace TauCeti

open PDCode

variable {R M : Type*} [Semiring R] [AddCommGroup M] [Module R M]

/-- A Fox colouring of the trefoil diagram is constant on each Wirtinger arc. -/
private theorem apply_eq_of_mem_foxColorings_rightHandedTrefoilPDCode
    {v : Fin (4 * 3) ⊕ Fin rightHandedTrefoilPDCode.crossinglessComponentCount → M}
    (hv : v ∈ rightHandedTrefoilPDCode.foxColorings R M) (p : Fin 3 × Fin 4) :
    v (.inl (crossingSlotEquiv 3 p)) =
      v (.inl (crossingSlotEquiv 3 (rightHandedTrefoilOverArc p, 0))) :=
  apply_eq_apply_rightHandedTrefoilOverArc (fun p ↦ v (.inl (crossingSlotEquiv 3 p)))
    (fun p ↦ by
      rw [← rightHandedTrefoilPDCode_edgePair_apply]
      exact apply_edgePair_of_mem_foxColorings hv _)
    (fun i ↦ by
      simpa using
        apply_crossing_add_two_of_mem_foxColorings_of_isOver hv (i := i) (slot := 0) (by simp)) p

/-- The crossing relations of a Fox colouring of the trefoil diagram at its first two crossings,
on the labels `a₀, a₁, a₂` of the three Wirtinger arcs. -/
private theorem relations_of_mem_foxColorings_rightHandedTrefoilPDCode
    {v : Fin (4 * 3) ⊕ Fin rightHandedTrefoilPDCode.crossinglessComponentCount → M}
    (hv : v ∈ rightHandedTrefoilPDCode.foxColorings R M) :
    v (.inl (crossingSlotEquiv 3 (1, 0))) =
        2 • v (.inl (crossingSlotEquiv 3 (0, 0))) - v (.inl (crossingSlotEquiv 3 (2, 0))) ∧
      v (.inl (crossingSlotEquiv 3 (2, 0))) =
        2 • v (.inl (crossingSlotEquiv 3 (1, 0))) - v (.inl (crossingSlotEquiv 3 (0, 0))) := by
  have h (i : Fin 3) :=
    apply_crossing_add_two_of_mem_foxColorings_of_not_isOver hv (i := i) (slot := 1) (by simp)
  have h0 := h 0
  have h1 := h 1
  simp only [crossing_apply, rightHandedTrefoilPDCode_halfEdge, Equiv.Perm.one_apply,
    Fin.reduceAdd] at h0 h1
  rw [apply_eq_of_mem_foxColorings_rightHandedTrefoilPDCode hv (0, 3),
    apply_eq_of_mem_foxColorings_rightHandedTrefoilPDCode hv (0, 2),
    apply_eq_of_mem_foxColorings_rightHandedTrefoilPDCode hv (0, 1)] at h0
  rw [apply_eq_of_mem_foxColorings_rightHandedTrefoilPDCode hv (1, 3),
    apply_eq_of_mem_foxColorings_rightHandedTrefoilPDCode hv (1, 2),
    apply_eq_of_mem_foxColorings_rightHandedTrefoilPDCode hv (1, 1)] at h1
  exact ⟨by simpa [Fin.reduceSub, Fin.neg_def] using h0, by simpa using h1⟩

/-- On a Fox colouring of the trefoil diagram, the difference `a₁ - a₀` of the labels of the first
two Wirtinger arcs is `3`-torsion. -/
private theorem three_nsmul_sub_eq_zero_of_mem_foxColorings_rightHandedTrefoilPDCode
    {v : Fin (4 * 3) ⊕ Fin rightHandedTrefoilPDCode.crossinglessComponentCount → M}
    (hv : v ∈ rightHandedTrefoilPDCode.foxColorings R M) :
    3 • (v (.inl (crossingSlotEquiv 3 (1, 0))) - v (.inl (crossingSlotEquiv 3 (0, 0)))) = 0 := by
  obtain ⟨h₁, h₂⟩ := relations_of_mem_foxColorings_rightHandedTrefoilPDCode hv
  rw [h₂, ← sub_eq_zero] at h₁
  rw [← h₁]
  abel

/-- The family of labels with `a₀ = a`, `a₁ = a + u` and `a₂ = a - u` on the three Wirtinger arcs
of the trefoil diagram. -/
private def trefoilLabels (a u : M) :
    Fin (4 * 3) ⊕ Fin rightHandedTrefoilPDCode.crossinglessComponentCount → M :=
  Sum.elim (fun h ↦ ![a, a + u, a - u] (rightHandedTrefoilOverArc ((crossingSlotEquiv 3).symm h)))
    fun j ↦ absurd j.isLt (by simp)

/-- The labels `a, a + u, a - u` on the Wirtinger arcs form a Fox colouring of the trefoil diagram
when `3 • u = 0`. -/
private theorem trefoilLabels_mem_foxColorings {a u : M} (hu : 3 • u = 0) :
    trefoilLabels a u ∈ rightHandedTrefoilPDCode.foxColorings R M := by
  refine mem_foxColorings_iff.2 ⟨fun h ↦ ?_, fun i slot ↦ ?_⟩
  · obtain ⟨⟨i, slot⟩, rfl⟩ := (crossingSlotEquiv 3).surjective h
    rw [rightHandedTrefoilPDCode_edgePair_apply]
    simp [trefoilLabels]
  · have hz : (3 : ℤ) • u = 0 := by rw [← hu, ← natCast_zsmul, Nat.cast_ofNat]
    fin_cases i <;> fin_cases slot <;>
      norm_num [trefoilLabels, isOver_def, crossing_apply,
        rightHandedTrefoilPDCode_halfEdge, rightHandedTrefoilPDCode_overPair] <;>
      first
      | abel1
      | (rw [← sub_eq_zero]; abel_nf; simp [hz])

/-- The labels of `trefoilLabels a u` at slot `0` of the first two crossings. -/
private theorem trefoilLabels_apply (a u : M) :
    trefoilLabels a u (.inl (crossingSlotEquiv 3 (0, 0))) = a ∧
      trefoilLabels a u (.inl (crossingSlotEquiv 3 (1, 0))) = a + u := by
  simp [trefoilLabels]

variable (R M)

/-- **The Fox colourings of the trefoil diagram** with values in `M` are the pairs `(a, u)` of an
element of `M` and an element of its `3`-torsion: the colouring with these coordinates labels the
three Wirtinger arcs by `a`, `a + u` and `a - u`. -/
def foxColoringsRightHandedTrefoilPDCodeEquiv :
    rightHandedTrefoilPDCode.foxColorings R M ≃ₗ[R]
      M × LinearMap.ker ((3 : ℕ) • LinearMap.id : M →ₗ[R] M) where
  toFun v := (v.1 (.inl (crossingSlotEquiv 3 (0, 0))),
    ⟨v.1 (.inl (crossingSlotEquiv 3 (1, 0))) - v.1 (.inl (crossingSlotEquiv 3 (0, 0))), by
      rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
      exact three_nsmul_sub_eq_zero_of_mem_foxColorings_rightHandedTrefoilPDCode v.2⟩)
  map_add' v w := by
    refine Prod.ext rfl (Subtype.ext ?_)
    simp only [Submodule.coe_add, Pi.add_apply, Prod.snd_add]
    abel
  map_smul' c v := by
    refine Prod.ext rfl (Subtype.ext ?_)
    simp [smul_sub]
  invFun x := ⟨trefoilLabels x.1 x.2.1, trefoilLabels_mem_foxColorings (by
    rw [← LinearMap.id_apply (R := R) (x.2 : M), ← LinearMap.smul_apply]
    exact LinearMap.mem_ker.1 x.2.2)⟩
  left_inv v := by
    obtain ⟨h₁, -⟩ := relations_of_mem_foxColorings_rightHandedTrefoilPDCode v.2
    refine Subtype.ext (funext fun g ↦ ?_)
    rcases g with h | j
    · obtain ⟨p, rfl⟩ := (crossingSlotEquiv 3).surjective h
      rw [apply_eq_of_mem_foxColorings_rightHandedTrefoilPDCode v.2 p]
      simp only [trefoilLabels, Sum.elim_inl, Equiv.symm_apply_apply]
      generalize rightHandedTrefoilOverArc p = k
      fin_cases k
      · rfl
      · simp
      · simp only [Fin.reduceFinMk, Matrix.cons_val]
        rw [h₁, two_nsmul]
        abel
    · exact absurd j.isLt (by simp)
  right_inv x := by
    obtain ⟨h₀, h₁⟩ := trefoilLabels_apply x.1 x.2.1
    refine Prod.ext h₀ (Subtype.ext ?_)
    simp [h₀, h₁]

/-- The first coordinate is the label of the arc over crossing `0`. -/
@[simp↓]
theorem foxColoringsRightHandedTrefoilPDCodeEquiv_fst
    (v : rightHandedTrefoilPDCode.foxColorings R M) :
    (foxColoringsRightHandedTrefoilPDCodeEquiv R M v).1 =
      v.1 (.inl (crossingSlotEquiv 3 (0, 0))) :=
  (rfl)

/-- The torsion coordinate is the difference of the labels over crossings `1` and `0`. -/
@[simp↓]
theorem foxColoringsRightHandedTrefoilPDCodeEquiv_snd
    (v : rightHandedTrefoilPDCode.foxColorings R M) :
    ((foxColoringsRightHandedTrefoilPDCodeEquiv R M v).2 : M) =
      v.1 (.inl (crossingSlotEquiv 3 (1, 0))) - v.1 (.inl (crossingSlotEquiv 3 (0, 0))) :=
  (rfl)

/-- The inverse labels the Wirtinger arcs by `a`, `a + u` and `a - u`. -/
@[simp↓]
theorem foxColoringsRightHandedTrefoilPDCodeEquiv_symm_apply
    (x : M × LinearMap.ker ((3 : ℕ) • LinearMap.id : M →ₗ[R] M)) (h : Fin 12) :
    ((foxColoringsRightHandedTrefoilPDCodeEquiv R M).symm x).1 (.inl h) =
      ![x.1, x.1 + x.2, x.1 - x.2]
        (rightHandedTrefoilOverArc ((crossingSlotEquiv 3).symm h)) :=
  (rfl)

/-- The trefoil diagram has `|M| · |M[3]|` Fox colourings with values in `M`, where `M[3]` is the
`3`-torsion of `M`. -/
theorem natCard_foxColorings_rightHandedTrefoilPDCode :
    Nat.card (rightHandedTrefoilPDCode.foxColorings R M) =
      Nat.card M * Nat.card {x : M // 3 • x = 0} := by
  rw [Nat.card_congr (foxColoringsRightHandedTrefoilPDCodeEquiv R M).toEquiv, Nat.card_prod]
  exact congrArg _ (Nat.card_congr (Equiv.subtypeEquivRight fun x ↦ by simp))

/-- The trefoil diagram has `9` three-colourings. -/
theorem natCard_foxColorings_rightHandedTrefoilPDCode_zmod_three :
    Nat.card (rightHandedTrefoilPDCode.foxColorings (ZMod 3) (ZMod 3)) = 9 := by
  rw [natCard_foxColorings_rightHandedTrefoilPDCode, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card]
  decide

/-- The trefoil diagram has `18` six-colourings: the `3`-torsion of `ZMod 6` is `{0, 2, 4}`. -/
theorem natCard_foxColorings_rightHandedTrefoilPDCode_zmod_six :
    Nat.card (rightHandedTrefoilPDCode.foxColorings (ZMod 6) (ZMod 6)) = 18 := by
  rw [natCard_foxColorings_rightHandedTrefoilPDCode, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card]
  decide

end TauCeti
