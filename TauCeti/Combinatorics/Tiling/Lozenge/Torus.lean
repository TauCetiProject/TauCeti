/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.Height
import TauCeti.Data.Int.DivMod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

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

Summing over rows and columns, the fundamental domain `[0, n₁) × [0, n₂)` contains `n₂ h₁`
lozenges of type 1 and `n₁ h₂` of type 2; since every white face contains exactly one edge of `M`,
it contains `n₁ n₂ − n₂ h₁ − n₁ h₂` of type 3. The attainable height changes are exactly the
`(a, b) ∈ ℕ²` with `n₂ a + n₁ b ≤ n₁ n₂`: going `n₂` periods in the first direction and `n₁` in
the second raises the height by `n₂ h₁ + n₁ h₂`, which the Lipschitz bound caps at `n₁ n₂`, and
each such `(a, b)` is realised by the floor tiling `H(x, y) = ⌊(n₂ a x + n₁ b y) / (n₁ n₂)⌋`.

## Main definitions

* `TauCeti.IsTorusTiling n₁ n₂ M`: `M` is a plane tiling invariant under the translations by
  `(n₁, 0)` and `(0, n₂)`.
* `TauCeti.heightChange n₁ n₂ M`: the pair of counts of edges of `M` of direction `e₁` on
  `[0, n₁) × {0}` and of direction `e₂` on `{0} × [0, n₂)`.
* `TauCeti.floorHeight n₁ n₂ a b`: the floor height `⌊(n₂ a x + n₁ b y) / (n₁ n₂)⌋`.

## Main statements

* `TauCeti.IsTorusTiling.card_filter_range_eq_heightChange_fst`,
  `TauCeti.IsTorusTiling.card_filter_range_eq_heightChange_snd`: `h₁` is the number of type-1
  lozenges on any horizontal segment of length `n₁`, and `h₂` the number of type-2 lozenges on
  any vertical segment of length `n₂`.
* `TauCeti.IsTorusTiling.tilingHeight_add_sub_eq_heightChange_fst`,
  `TauCeti.IsTorusTiling.tilingHeight_add_sub_eq_heightChange_snd`:
  `H_M(v + (n₁, 0)) − H_M(v) = h₁` and `H_M(v + (0, n₂)) − H_M(v) = h₂`.
* `TauCeti.IsTorusTiling.card_filter_type_one`, `TauCeti.IsTorusTiling.card_filter_type_two`,
  `TauCeti.IsTorusTiling.add_card_filter_type_three`: per fundamental domain there are `n₂ h₁`
  lozenges of type 1, `n₁ h₂` of type 2 and `n₁ n₂ − n₂ h₁ − n₁ h₂` of type 3.
* `TauCeti.IsTorusTiling.heightChange_le`: `n₂ h₁ + n₁ h₂ ≤ n₁ n₂`.
* `TauCeti.isTorusTiling_tilingOfHeight_floorHeight`: the floor tiling of `(a, b)` is a torus tiling
  with height change `(a, b)`.
* `TauCeti.exists_isTorusTiling_heightChange_eq_iff`: for `n₁, n₂ ≥ 1` the attainable height
  changes are exactly the `(a, b)` with `n₂ a + n₁ b ≤ n₁ n₂`.

## References

* R. Kenyon, *Lectures on dimers*, IAS/Park City Math. Ser. 16 (2009), Lemma 4 (the lozenge
  counts, for `n₁ = n₂`) and Section 5.4 (the floor tilings and the attainable height changes
  `n₂ a + n₁ b ≤ n₁ n₂`).
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

/-- Along `m` periods in the first direction the height function rises by `m h₁`. -/
theorem tilingHeight_add_mul_sub_fst (v : ℤ × ℤ) (m : ℕ) :
    tilingHeight M (v + ((m : ℤ) * n₁, 0)) - tilingHeight M v =
      m * (heightChange n₁ n₂ M).1 := by
  induction m with
  | zero => simp [Prod.mk_zero_zero]
  | succ m ih =>
    have := h.tilingHeight_add_sub_eq_heightChange_fst (v + ((m : ℤ) * n₁, 0))
    rw [show v + (((m + 1 : ℕ) : ℤ) * n₁, 0) = v + ((m : ℤ) * n₁, 0) + ((n₁ : ℤ), 0) from
      Prod.ext (by simp only [Prod.fst_add, Nat.cast_succ]; ring) (by simp)]
    push_cast
    linarith

/-- Along `m` periods in the second direction the height function rises by `m h₂`. -/
theorem tilingHeight_add_mul_sub_snd (v : ℤ × ℤ) (m : ℕ) :
    tilingHeight M (v + (0, (m : ℤ) * n₂)) - tilingHeight M v =
      m * (heightChange n₁ n₂ M).2 := by
  induction m with
  | zero => simp [Prod.mk_zero_zero]
  | succ m ih =>
    have := h.tilingHeight_add_sub_eq_heightChange_snd (v + (0, (m : ℤ) * n₂))
    rw [show v + (0, ((m + 1 : ℕ) : ℤ) * n₂) = v + (0, (m : ℤ) * n₂) + (0, (n₂ : ℤ)) from
      Prod.ext (by simp) (by simp only [Prod.snd_add, Nat.cast_succ]; ring)]
    push_cast
    linarith

open Classical in
/-- **Type-1 lozenges per fundamental domain**: the fundamental domain `[0, n₁) × [0, n₂)` contains
`n₂ h₁` edges of `M` of direction `e₁`. -/
theorem card_filter_type_one :
    ((Finset.range n₁ ×ˢ Finset.range n₂).filter
      fun p : ℕ × ℕ => (⟨((p.1 : ℤ), (p.2 : ℤ)), 0⟩ : TriEdge) ∈ M).card =
      n₂ * (heightChange n₁ n₂ M).1 := by
  rw [Finset.card_filter, Finset.sum_product_right]
  simp_rw [← Finset.card_filter]
  have (y : ℕ) := h.card_filter_range_eq_heightChange_fst 0 y
  simp only [zero_add] at this
  simp [this]

open Classical in
/-- **Type-2 lozenges per fundamental domain**: the fundamental domain `[0, n₁) × [0, n₂)` contains
`n₁ h₂` edges of `M` of direction `e₂`. -/
theorem card_filter_type_two :
    ((Finset.range n₁ ×ˢ Finset.range n₂).filter
      fun p : ℕ × ℕ => (⟨((p.1 : ℤ), (p.2 : ℤ)), 1⟩ : TriEdge) ∈ M).card =
      n₁ * (heightChange n₁ n₂ M).2 := by
  rw [Finset.card_filter, Finset.sum_product]
  simp_rw [← Finset.card_filter]
  have (x : ℕ) := h.card_filter_range_eq_heightChange_snd x 0
  simp only [zero_add] at this
  simp [this]

omit h in
open Classical in
/-- Round the white face `W(v)` exactly one of its edges `(v, 1)`, `(v + e₁, 2)`, `(v, 3)` lies in
the plane tiling `M`. -/
private theorem ite_add_ite_add_ite (hM : IsTiling Set.univ M) (v : ℤ × ℤ) :
    ((if (⟨v, 0⟩ : TriEdge) ∈ M then 1 else 0) +
      (if (⟨v + (1, 0), 1⟩ : TriEdge) ∈ M then 1 else 0) +
      if (⟨v, 2⟩ : TriEdge) ∈ M then 1 else 0 : ℕ) = 1 := by
  obtain ⟨k, hk, hu⟩ := (TriFace.existsUnique_mem_edges_iff ⟨v, true⟩ M).1
    (hM.existsUnique (Set.mem_univ _))
  have e₀ := hu 0
  have e₁ := hu 1
  have e₂ := hu 2
  simp only [TriFace.edge_mk_true] at e₀ e₁ e₂ hk
  fin_cases k <;> simp_all

open Classical in
/-- **Type-3 lozenges per fundamental domain**: the fundamental domain `[0, n₁) × [0, n₂)` contains
`n₁ n₂ − n₂ h₁ − n₁ h₂` edges of `M` of direction `e₃`. -/
theorem add_card_filter_type_three :
    n₂ * (heightChange n₁ n₂ M).1 + n₁ * (heightChange n₁ n₂ M).2 +
      ((Finset.range n₁ ×ˢ Finset.range n₂).filter
        fun p : ℕ × ℕ => (⟨((p.1 : ℤ), (p.2 : ℤ)), 2⟩ : TriEdge) ∈ M).card = n₁ * n₂ := by
  have hB : ∑ p ∈ Finset.range n₁ ×ˢ Finset.range n₂,
      (if (⟨((p.1 : ℤ), (p.2 : ℤ)) + (1, 0), 1⟩ : TriEdge) ∈ M then 1 else 0) =
      n₁ * (heightChange n₁ n₂ M).2 := by
    rw [Finset.sum_product]
    simp_rw [← Finset.card_filter]
    have (x : ℕ) := h.card_filter_range_eq_heightChange_snd (x + 1) 0
    simp only [zero_add] at this
    simp [Prod.mk_add_mk, this]
  rw [← h.card_filter_type_one, ← hB, Finset.card_filter, Finset.card_filter,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    Finset.sum_congr rfl fun p _ => ite_add_ite_add_ite h.isTiling _]
  simp

/-- **Height changes are bounded**: `n₂ h₁ + n₁ h₂ ≤ n₁ n₂`. Going `n₂` periods in the first
direction and `n₁` in the second raises the height by `n₂ h₁ + n₁ h₂`, and by the Lipschitz bound
by at most `n₁ n₂`. -/
theorem heightChange_le : n₂ * (heightChange n₁ n₂ M).1 + n₁ * (heightChange n₁ n₂ M).2 ≤
    n₁ * n₂ := by
  have h₁ := h.tilingHeight_add_mul_sub_fst 0 n₂
  have h₂ := h.tilingHeight_add_mul_sub_snd ((n₂ : ℤ) * n₁, 0) n₁
  have h₃ := (h.isTiling.tilingHeight_sub_le_max 0 ((n₂ : ℤ) * n₁) ((n₁ : ℤ) * n₂)).trans
    (max_le (mul_comm _ _).le (max_le le_rfl (by positivity)))
  simp only [zero_add, Prod.mk_add_mk, add_zero, tilingHeight_zero, sub_zero] at h₁ h₂ h₃
  zify
  linarith

end IsTorusTiling

/-! ### Attainable height changes -/

/-- The floor height `H(x, y) = ⌊(n₂ a x + n₁ b y) / (n₁ n₂)⌋`, by integer division (so `0` when
`n₁ n₂ = 0`). For `0 < n₁, n₂` and `n₂ a + n₁ b ≤ n₁ n₂` its tiling is a torus tiling with height
change `(a, b)` (`isTorusTiling_tilingOfHeight_floorHeight`; Kenyon, *Lectures on dimers*,
Section 5.4). -/
def floorHeight (n₁ n₂ a b : ℕ) (v : ℤ × ℤ) : ℤ :=
  ((n₂ * a : ℕ) * v.1 + (n₁ * b : ℕ) * v.2) / (n₁ * n₂ : ℕ)

theorem floorHeight_def (n₁ n₂ a b : ℕ) (v : ℤ × ℤ) : floorHeight n₁ n₂ a b v =
    ((n₂ * a : ℕ) * v.1 + (n₁ * b : ℕ) * v.2) / (n₁ * n₂ : ℕ) := (rfl)

variable {a b : ℕ}

/-- **The floor height is a height function** when `n₂ a + n₁ b ≤ n₁ n₂`. -/
theorem isHeightFunction_floorHeight (hab : n₂ * a + n₁ * b ≤ n₁ * n₂) :
    IsHeightFunction (floorHeight n₁ n₂ a b) := by
  rw [isHeightFunction_def]
  rintro ⟨v, k⟩
  have hN : ((n₂ * a : ℕ) : ℤ) + ((n₁ * b : ℕ) : ℤ) ≤ ((n₁ * n₂ : ℕ) : ℤ) := by exact_mod_cast hab
  have ha : (0 : ℤ) ≤ ((n₂ * a : ℕ) : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ ((n₁ * b : ℕ) : ℤ) := by positivity
  rw [TriEdge.target_mk, floorHeight_def, floorHeight_def, Prod.fst_add, Prod.snd_add, mul_add,
    mul_add, add_add_add_comm]
  generalize ((n₂ * a : ℕ) : ℤ) = A, ((n₁ * b : ℕ) : ℤ) = B, ((n₁ * n₂ : ℕ) : ℤ) = N at *
  refine Int.ediv_add_sub_ediv ?_ ?_ <;> fin_cases k <;> simp <;> linarith

@[simp] theorem floorHeight_zero : floorHeight n₁ n₂ a b 0 = 0 := by
  simp [floorHeight_def]

/-- Translating by `(n₁, 0)` raises the floor height by `a`. -/
theorem floorHeight_add_fst (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (v : ℤ × ℤ) :
    floorHeight n₁ n₂ a b (v + ((n₁ : ℤ), 0)) = floorHeight n₁ n₂ a b v + a := by
  have hN : ((n₁ * n₂ : ℕ) : ℤ) ≠ 0 := by positivity
  rw [floorHeight_def, floorHeight_def, Prod.fst_add, Prod.snd_add, add_zero,
    show ((n₂ * a : ℕ) : ℤ) * (v.1 + n₁) + ((n₁ * b : ℕ) : ℤ) * v.2 =
      ((n₂ * a : ℕ) : ℤ) * v.1 + ((n₁ * b : ℕ) : ℤ) * v.2 + (a : ℤ) * ((n₁ * n₂ : ℕ) : ℤ) by
        push_cast; ring,
    Int.add_mul_ediv_right _ _ hN]

/-- Translating by `(0, n₂)` raises the floor height by `b`. -/
theorem floorHeight_add_snd (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (v : ℤ × ℤ) :
    floorHeight n₁ n₂ a b (v + (0, (n₂ : ℤ))) = floorHeight n₁ n₂ a b v + b := by
  have hN : ((n₁ * n₂ : ℕ) : ℤ) ≠ 0 := by positivity
  rw [floorHeight_def, floorHeight_def, Prod.fst_add, Prod.snd_add, add_zero,
    show ((n₂ * a : ℕ) : ℤ) * v.1 + ((n₁ * b : ℕ) : ℤ) * (v.2 + n₂) =
      ((n₂ * a : ℕ) : ℤ) * v.1 + ((n₁ * b : ℕ) : ℤ) * v.2 + (b : ℤ) * ((n₁ * n₂ : ℕ) : ℤ) by
        push_cast; ring,
    Int.add_mul_ediv_right _ _ hN]

/-- **The floor tiling** of `(a, b)` with `n₂ a + n₁ b ≤ n₁ n₂` is a torus tiling with height
change `(a, b)`. -/
theorem isTorusTiling_tilingOfHeight_floorHeight (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (hab : n₂ * a + n₁ * b ≤ n₁ * n₂) :
    IsTorusTiling n₁ n₂ (tilingOfHeight (floorHeight n₁ n₂ a b)) ∧
      heightChange n₁ n₂ (tilingOfHeight (floorHeight n₁ n₂ a b)) = (a, b) := by
  have hH := isHeightFunction_floorHeight hab
  have hM := hH.isTiling_tilingOfHeight
  refine ⟨⟨hM, vadd_tilingOfHeight_of_forall (floorHeight_add_fst hn₁ hn₂),
    vadd_tilingOfHeight_of_forall (floorHeight_add_snd hn₁ hn₂)⟩, ?_⟩
  have h₁ := hM.heightChange_fst_eq n₁ n₂
  have h₂ := hM.heightChange_snd_eq n₁ n₂
  have e₁ := floorHeight_add_fst (a := a) (b := b) hn₁ hn₂ 0
  have e₂ := floorHeight_add_snd (a := a) (b := b) hn₁ hn₂ 0
  simp only [hH.tilingHeight_tilingOfHeight floorHeight_zero, zero_add,
    floorHeight_zero] at h₁ h₂ e₁ e₂
  exact Prod.ext (by omega) (by omega)

/-- **Attainable height changes.** For `n₁, n₂ ≥ 1`, `(a, b)` is the height change of a torus
tiling iff `n₂ a + n₁ b ≤ n₁ n₂`; each is realised by the floor tiling (Kenyon, *Lectures on
dimers*, Section 5.4). -/
theorem exists_isTorusTiling_heightChange_eq_iff (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) :
    (∃ M, IsTorusTiling n₁ n₂ M ∧ heightChange n₁ n₂ M = (a, b)) ↔
      n₂ * a + n₁ * b ≤ n₁ * n₂ := by
  refine ⟨fun ⟨M, hM, hab⟩ => ?_,
    fun hab => ⟨_, isTorusTiling_tilingOfHeight_floorHeight hn₁ hn₂ hab⟩⟩
  have := hM.heightChange_le
  rwa [hab] at this

end TauCeti
