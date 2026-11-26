/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.Height

/-!
# Torus tilings and height changes

For `n₁, n₂ ≥ 1` the torus tilings are the plane tilings invariant under the translations by
`(n₁, 0)` and `(0, n₂)`, that is under `L = n₁ℤ × n₂ℤ`. The height change `(h₁, h₂)` of a torus
tiling `M` counts the edges of `M` of direction `e₁` on the segment `[0, n₁) × {0}` and those of
direction `e₂` on the segment `{0} × [0, n₂)`.

The number of edges of direction `e₁` of a plane tiling on a horizontal segment is the increase
of its height function along the segment, and the height function of an `L`-invariant tiling
increases by `H_M(w)` between `v` and `v + w` for `w ∈ L`. So `h₁` is the number of type-1
lozenges on every horizontal segment of length `n₁`, `h₂` the number of type-2 lozenges on every
vertical segment of length `n₂`, and `H_M(v + (n₁, 0)) − H_M(v) = h₁`,
`H_M(v + (0, n₂)) − H_M(v) = h₂`, the definition of the height change by heights.

## Main definitions

* `TauCeti.IsTorusTiling n₁ n₂ M`: `M` is a plane tiling invariant under the translations by
  `(n₁, 0)` and `(0, n₂)`.
* `TauCeti.heightChange n₁ n₂ M`: the pair of counts of edges of `M` of direction `e₁` on
  `[0, n₁) × {0}` and of direction `e₂` on `{0} × [0, n₂)`.

## Main statements

* `TauCeti.IsTorusTiling.card_filter_range_eq_heightChange_fst`,
  `TauCeti.IsTorusTiling.card_filter_range_eq_heightChange_snd`: `h₁` is the number of type-1
  lozenges on any horizontal segment of length `n₁`, and `h₂` the number of type-2 lozenges on
  any vertical segment of length `n₂`.
* `TauCeti.IsTorusTiling.tilingHeight_add_sub_eq_heightChange_fst`,
  `TauCeti.IsTorusTiling.tilingHeight_add_sub_eq_heightChange_snd`:
  `H_M(v + (n₁, 0)) − H_M(v) = h₁` and `H_M(v + (0, n₂)) − H_M(v) = h₂`.

## References

* R. Kenyon, *Lectures on dimers*, IAS/Park City Math. Ser. 16 (2009).
* V. Gorin, *Lectures on random lozenge tilings*, Cambridge Stud. Adv. Math. 193 (2021),
  Section 3.3.
-/

public section

open Pointwise

namespace TauCeti

variable {M : Set TriEdge} {n₁ n₂ : ℕ}

/-- A torus tiling of the torus `ℤ² / (n₁ℤ × n₂ℤ)`: a plane tiling invariant under the
translations by `(n₁, 0)` and `(0, n₂)`. -/
def IsTorusTiling (n₁ n₂ : ℕ) (M : Set TriEdge) : Prop :=
  IsTiling Set.univ M ∧ ((n₁ : ℤ), (0 : ℤ)) +ᵥ M = M ∧ ((0 : ℤ), (n₂ : ℤ)) +ᵥ M = M

theorem isTorusTiling_def : IsTorusTiling n₁ n₂ M ↔
    IsTiling Set.univ M ∧ ((n₁ : ℤ), (0 : ℤ)) +ᵥ M = M ∧ ((0 : ℤ), (n₂ : ℤ)) +ᵥ M = M :=
  Iff.rfl

open Classical in
/-- The height change `(h₁, h₂)` of a torus tiling: the number of `x ∈ [0, n₁)` with
`((x, 0), 1) ∈ M` and the number of `y ∈ [0, n₂)` with `((0, y), 2) ∈ M`. -/
noncomputable def heightChange (n₁ n₂ : ℕ) (M : Set TriEdge) : ℕ × ℕ :=
  (((Finset.range n₁).filter fun x : ℕ => (⟨((x : ℤ), 0), 0⟩ : TriEdge) ∈ M).card,
    ((Finset.range n₂).filter fun y : ℕ => (⟨(0, (y : ℤ)), 1⟩ : TriEdge) ∈ M).card)

open Classical in
theorem heightChange_def (n₁ n₂ : ℕ) (M : Set TriEdge) : heightChange n₁ n₂ M =
    (((Finset.range n₁).filter fun x : ℕ => (⟨((x : ℤ), 0), 0⟩ : TriEdge) ∈ M).card,
      ((Finset.range n₂).filter fun y : ℕ => (⟨(0, (y : ℤ)), 1⟩ : TriEdge) ∈ M).card) :=
  (rfl)

namespace IsTiling

/-- The first component of the height change of a plane tiling is `H_M(n₁, 0)`. -/
theorem heightChange_fst_eq (h : IsTiling Set.univ M) (n₁ n₂ : ℕ) :
    ((heightChange n₁ n₂ M).1 : ℤ) = tilingHeight M (n₁, 0) := by
  classical
  have := h.card_filter_range_eq_tilingHeight_add_nsmul_sub 0 (k := 0) (by decide) n₁
  simp only [zero_add, latticeDir_zero, Prod.smul_mk, nsmul_eq_mul, mul_one, smul_zero,
    tilingHeight_zero, sub_zero] at this
  rw [heightChange_def, ← this]

/-- The second component of the height change of a plane tiling is `H_M(0, n₂)`. -/
theorem heightChange_snd_eq (h : IsTiling Set.univ M) (n₁ n₂ : ℕ) :
    ((heightChange n₁ n₂ M).2 : ℤ) = tilingHeight M (0, n₂) := by
  classical
  have := h.card_filter_range_eq_tilingHeight_add_nsmul_sub 0 (k := 1) (by decide) n₂
  simp only [zero_add, latticeDir_one, Prod.smul_mk, nsmul_eq_mul, mul_one, smul_zero,
    tilingHeight_zero, sub_zero] at this
  rw [heightChange_def, ← this]

end IsTiling

namespace IsTorusTiling

variable (h : IsTorusTiling n₁ n₂ M)
include h

theorem isTiling : IsTiling Set.univ M := h.1

theorem vadd_fst : ((n₁ : ℤ), (0 : ℤ)) +ᵥ M = M := h.2.1

theorem vadd_snd : ((0 : ℤ), (n₂ : ℤ)) +ᵥ M = M := h.2.2

/-- **The height change by heights**: `H_M(v + (n₁, 0)) − H_M(v) = h₁`. -/
theorem tilingHeight_add_sub_eq_heightChange_fst (v : ℤ × ℤ) :
    tilingHeight M (v + ((n₁ : ℤ), 0)) - tilingHeight M v = (heightChange n₁ n₂ M).1 := by
  rw [h.isTiling.heightChange_fst_eq, h.isTiling.tilingHeight_add_sub_of_vadd_eq h.vadd_fst]

/-- **The height change by heights**: `H_M(v + (0, n₂)) − H_M(v) = h₂`. -/
theorem tilingHeight_add_sub_eq_heightChange_snd (v : ℤ × ℤ) :
    tilingHeight M (v + (0, (n₂ : ℤ))) - tilingHeight M v = (heightChange n₁ n₂ M).2 := by
  rw [h.isTiling.heightChange_snd_eq, h.isTiling.tilingHeight_add_sub_of_vadd_eq h.vadd_snd]

open Classical in
/-- `h₁` is the number of type-1 lozenges on every horizontal segment of length `n₁`. -/
theorem card_filter_range_eq_heightChange_fst (a b : ℤ) :
    ((Finset.range n₁).filter fun i : ℕ => (⟨(a + i, b), 0⟩ : TriEdge) ∈ M).card =
      (heightChange n₁ n₂ M).1 := by
  have := h.isTiling.card_filter_range_eq_tilingHeight_add_nsmul_sub (a, b) (k := 0) (by decide)
    n₁
  simp only [latticeDir_zero, Prod.smul_mk, nsmul_eq_mul, mul_one, smul_zero, Prod.mk_add_mk,
    add_zero] at this
  rw [← Nat.cast_inj (R := ℤ), this, ← h.tilingHeight_add_sub_eq_heightChange_fst (a, b),
    Prod.mk_add_mk, add_zero]

open Classical in
/-- `h₂` is the number of type-2 lozenges on every vertical segment of length `n₂`. -/
theorem card_filter_range_eq_heightChange_snd (a b : ℤ) :
    ((Finset.range n₂).filter fun j : ℕ => (⟨(a, b + j), 1⟩ : TriEdge) ∈ M).card =
      (heightChange n₁ n₂ M).2 := by
  have := h.isTiling.card_filter_range_eq_tilingHeight_add_nsmul_sub (a, b) (k := 1) (by decide)
    n₂
  simp only [latticeDir_one, Prod.smul_mk, nsmul_eq_mul, mul_one, smul_zero, Prod.mk_add_mk,
    add_zero] at this
  rw [← Nat.cast_inj (R := ℤ), this, ← h.tilingHeight_add_sub_eq_heightChange_snd (a, b),
    Prod.mk_add_mk, add_zero]

end IsTorusTiling

end TauCeti
