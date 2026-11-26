/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.Cochain
public import TauCeti.Combinatorics.Tiling.Lozenge.Tiling
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Heights of plane lozenge tilings

The height cochain of a set `M` of edges is `1 − c₀(e)` on the edges of `M` and the neutral
increment `c₀(e)` elsewhere, where `c₀` is `0` along `e₁`, `e₂` and `1` along `e₃`. It is closed
on every face meeting `M` in exactly one edge, so for a plane tiling it is exact on the plane, and
its primitive vanishing at `0` is the height function `H_M`: `H_M(v + e₁) − H_M(v) = [(v,1) ∈ M]`,
`H_M(v + e₂) − H_M(v) = [(v,2) ∈ M]` and `H_M(v + e₃) − H_M(v) = 1 − [(v,3) ∈ M]`.

A height function is a function `H : ℤ × ℤ → ℤ` whose increments along `e₁`, `e₂`, `e₃` lie in
`{0, 1}`; the edges along which its increment is not the neutral one form a plane tiling, and this
is a bijection from the height functions vanishing at `0` onto the plane tilings, inverse to
`M ↦ H_M`.

## Main definitions

* `TauCeti.heightCochain M`: the height cochain of a set of edges.
* `TauCeti.tilingHeight M`: the height function `H_M` of a plane tiling, the primitive of its
  height cochain vanishing at `0`.
* `TauCeti.IsHeightFunction H`: the increments of `H` along `e₁`, `e₂`, `e₃` lie in `{0, 1}`.
* `TauCeti.tilingOfHeight H`: the set of edges along which the increment of `H` is not neutral.

## Main statements

* `TauCeti.IsFreeTiling.isClosedCochainOn_heightCochain`: the height cochain of a free tiling of
  `R` is closed on `R`.
* `TauCeti.IsTiling.tilingHeight_target_sub_v`, `TauCeti.tilingHeight_zero`,
  `TauCeti.IsTiling.eq_tilingHeight`: `H_M` has the increments of the height cochain, vanishes at
  `0`, and is the only such function.
* `TauCeti.IsTiling.card_filter_range_eq_tilingHeight_add_nsmul_sub`: the number of edges of
  direction `e₁` (resp. `e₂`) of a plane tiling on a segment of that direction is the increase of
  `H_M` along it.
* `TauCeti.tilingOfHeight_bijOn`: `tilingOfHeight` is a bijection from the height functions
  vanishing at `0` onto the plane tilings, with inverse `tilingHeight`
  (`TauCeti.IsTiling.tilingOfHeight_tilingHeight`,
  `TauCeti.IsHeightFunction.tilingHeight_tilingOfHeight`).
* `TauCeti.IsTiling.tilingHeight_vadd`: `H_{τ_w M}(v) = H_M(v − w) − H_M(−w)`, and
  `TauCeti.IsTiling.tilingHeight_add_sub_of_vadd_eq`: if `M` is invariant under the translation
  by `w`, then `H_M(v + w) − H_M(v) = H_M(w)`.
* `TauCeti.IsHeightFunction.sub_le_max`, `TauCeti.IsTiling.tilingHeight_sub_le_max`: the Lipschitz
  bound `H(u + (a, b)) − H(u) ≤ max(a, b, 0)`.

## References

* A. Aggarwal, *Universality for lozenge tiling local statistics*, Ann. of Math. 198 (2023),
  Section 1.2.
* V. Gorin, *Lectures on random lozenge tilings*, Cambridge Stud. Adv. Math. 193 (2021),
  Lecture 1.
* R. Kenyon, *Lectures on dimers*, IAS/Park City Math. Ser. 16 (2009), Section 2.2.
-/

public section

open Pointwise

namespace TauCeti

variable {R : Set TriFace} {M : Set TriEdge} {H g : ℤ × ℤ → ℤ}

/-! ### The height cochain -/

/-- The height cochain of a set `M` of edges: `1 − c₀(e)` on the edges of `M` and the neutral
increment `c₀(e)` on the other edges. -/
noncomputable def heightCochain (M : Set TriEdge) (e : TriEdge) : ℤ :=
  open Classical in if e ∈ M then 1 - neutralIncrement e else neutralIncrement e

variable {e : TriEdge}

@[simp] theorem heightCochain_of_mem (he : e ∈ M) : heightCochain M e = 1 - neutralIncrement e := by
  simp [heightCochain, he]

@[simp] theorem heightCochain_of_notMem (he : e ∉ M) : heightCochain M e = neutralIncrement e := by
  simp [heightCochain, he]

/-- The height cochain takes the non-neutral value `1 − c₀(e)` exactly on the edges of `M`. -/
theorem heightCochain_eq_one_sub_neutralIncrement_iff :
    heightCochain M e = 1 - neutralIncrement e ↔ e ∈ M := by
  by_cases he : e ∈ M
  · simp [he]
  · rw [heightCochain_of_notMem he]
    rcases neutralIncrement_eq_zero_or_eq_one e with h | h <;> simp [h, he]

theorem heightCochain_eq_zero_or_eq_one (M : Set TriEdge) (e : TriEdge) :
    heightCochain M e = 0 ∨ heightCochain M e = 1 := by
  by_cases he : e ∈ M
  · rw [heightCochain_of_mem he]
    rcases neutralIncrement_eq_zero_or_eq_one e with h | h <;> simp [h]
  · rw [heightCochain_of_notMem he]
    exact neutralIncrement_eq_zero_or_eq_one e

/-- **The height cochain of a free tiling is closed.** On a face meeting `M` in exactly one edge,
the three values of the height cochain are `(1, 0, 1)`, `(0, 1, 1)` or `(0, 0, 0)`. -/
theorem IsFreeTiling.isClosedCochainOn_heightCochain (h : IsFreeTiling R M) :
    IsClosedCochainOn R (heightCochain M) := by
  rw [isClosedCochainOn_def]
  intro f hf
  obtain ⟨j, hj, hu⟩ := (TriFace.existsUnique_mem_edges_iff f M).1 (h.existsUnique hf)
  have hc : ∀ k, heightCochain M (f.edge k) =
      if k = j then 1 - neutralIncrement (f.edge k) else neutralIncrement (f.edge k) := fun k => by
    by_cases hk : k = j
    · subst hk
      simp only [↓reduceIte, heightCochain_of_mem hj]
    · simp only [hk, ↓reduceIte, heightCochain_of_notMem fun h' => hk (hu k h')]
  simp only [hc, f.neutralIncrement_edge]
  fin_cases j <;> simp

/-! ### The height function of a plane tiling -/

/-- The height function `H_M` of a plane tiling `M`: the primitive of its height cochain vanishing
at `0`. It is `0` when the height cochain is not exact on the plane, which does not happen for
plane tilings. -/
noncomputable def tilingHeight (M : Set TriEdge) : ℤ × ℤ → ℤ :=
  open Classical in
  if h : IsExactCochainOn Set.univ (heightCochain M) then
    fun v => (isExactCochainOn_def.1 h).choose v - (isExactCochainOn_def.1 h).choose 0
  else 0

@[simp] theorem tilingHeight_zero (M : Set TriEdge) : tilingHeight M 0 = 0 := by
  unfold tilingHeight
  split_ifs <;> simp

namespace IsTiling

/-- The height function of a plane tiling is a primitive of its height cochain. -/
theorem isCochainPrimitiveOn_tilingHeight (h : IsTiling Set.univ M) :
    IsCochainPrimitiveOn Set.univ (heightCochain M) (tilingHeight M) := by
  have hex : IsExactCochainOn Set.univ (heightCochain M) :=
    h.isFreeTiling.isClosedCochainOn_heightCochain.isExactCochainOn_univ
  unfold tilingHeight
  split_ifs
  rw [isCochainPrimitiveOn_def]
  intro e he
  rw [isCochainPrimitiveOn_def.1 (isExactCochainOn_def.1 hex).choose_spec e he]
  ring

/-- **The increments of `H_M`**: along every edge `e`, `H_M` increases by the height cochain,
`1 − c₀(e)` on the edges of `M` and `c₀(e)` on the others. -/
theorem tilingHeight_target_sub_v (h : IsTiling Set.univ M) (e : TriEdge) :
    tilingHeight M e.target - tilingHeight M e.v = heightCochain M e :=
  (isCochainPrimitiveOn_univ_iff.1 h.isCochainPrimitiveOn_tilingHeight e).symm

open Classical in
/-- Along `e₁` and `e₂`, `H_M` increases by `1` on the edges of `M` and by `0` on the others. -/
theorem tilingHeight_add_latticeDir_sub_of_ne_two (h : IsTiling Set.univ M) (v : ℤ × ℤ)
    {k : Fin 3} (hk : k ≠ 2) :
    tilingHeight M (v + latticeDir k) - tilingHeight M v =
      if (⟨v, k⟩ : TriEdge) ∈ M then 1 else 0 := by
  have hc : neutralIncrement ⟨v, k⟩ = 0 := by simp [neutralIncrement_def, hk]
  have := h.tilingHeight_target_sub_v ⟨v, k⟩
  rw [TriEdge.target_mk] at this
  split_ifs with hM <;> simp_all

open Classical in
/-- **Lozenges on a segment**: for `k` the direction `e₁` or `e₂`, the number of edges
`(v + i e_k, k)` of a plane tiling with `i < n` is `H_M(v + n e_k) − H_M(v)`. -/
theorem card_filter_range_eq_tilingHeight_add_nsmul_sub (h : IsTiling Set.univ M) (v : ℤ × ℤ)
    {k : Fin 3} (hk : k ≠ 2) (n : ℕ) :
    (((Finset.range n).filter fun i : ℕ => (⟨v + i • latticeDir k, k⟩ : TriEdge) ∈ M).card : ℤ) =
      tilingHeight M (v + n • latticeDir k) - tilingHeight M v := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep := h.tilingHeight_add_latticeDir_sub_of_ne_two (v + n • latticeDir k) hk
    rw [Finset.range_add_one, Finset.filter_insert, succ_nsmul, ← add_assoc]
    split_ifs at hstep ⊢
    · rw [Finset.card_insert_of_notMem (by simp)]
      push_cast
      omega
    · omega

/-- **Uniqueness of the height function**: a primitive of the height cochain of a plane tiling
vanishing at `0` is `H_M`. -/
theorem eq_tilingHeight (h : IsTiling Set.univ M)
    (hg : IsCochainPrimitiveOn Set.univ (heightCochain M) g) (hg0 : g 0 = 0) :
    g = tilingHeight M :=
  eq_of_isCochainPrimitiveOn_univ hg h.isCochainPrimitiveOn_tilingHeight (by simp [hg0])

end IsTiling

/-! ### Height functions -/

/-- A height function is a function `H : ℤ × ℤ → ℤ` whose increment along each of `e₁`, `e₂`,
`e₃` is `0` or `1`. -/
def IsHeightFunction (H : ℤ × ℤ → ℤ) : Prop :=
  ∀ e : TriEdge, H e.target - H e.v = 0 ∨ H e.target - H e.v = 1

/-- The tiling of a height function: the edges `(v, k)` along which the increment of `H` is not
the neutral one, `H(v + e_k) − H(v) = 1 − c₀(k)`. -/
def tilingOfHeight (H : ℤ × ℤ → ℤ) : Set TriEdge :=
  {e | H e.target - H e.v = 1 - neutralIncrement e}

theorem isHeightFunction_def :
    IsHeightFunction H ↔ ∀ e : TriEdge, H e.target - H e.v = 0 ∨ H e.target - H e.v = 1 :=
  Iff.rfl

@[simp] theorem mem_tilingOfHeight :
    e ∈ tilingOfHeight H ↔ H e.target - H e.v = 1 - neutralIncrement e :=
  Iff.rfl

/-- The height function of a plane tiling is a height function. -/
theorem IsTiling.isHeightFunction_tilingHeight (h : IsTiling Set.univ M) :
    IsHeightFunction (tilingHeight M) := fun e => by
  rw [h.tilingHeight_target_sub_v]
  exact heightCochain_eq_zero_or_eq_one M e

namespace IsHeightFunction

/-- The height cochain of the tiling of a height function is the coboundary of the height
function. -/
theorem heightCochain_tilingOfHeight (hH : IsHeightFunction H) (e : TriEdge) :
    heightCochain (tilingOfHeight H) e = H e.target - H e.v := by
  by_cases he : e ∈ tilingOfHeight H
  · rw [heightCochain_of_mem he, mem_tilingOfHeight.1 he]
  · rw [heightCochain_of_notMem he]
    rw [mem_tilingOfHeight] at he
    rcases hH e with h | h <;> rcases neutralIncrement_eq_zero_or_eq_one e with h' | h' <;>
      omega

/-- **The tiling of a height function is a plane tiling**: round every face the increments of `H`
along the edges of directions `e₁`, `e₂`, `e₃` are `(0, 0, 0)`, `(1, 0, 1)` or `(0, 1, 1)`, and
exactly one edge is selected. -/
theorem isTiling_tilingOfHeight (hH : IsHeightFunction H) :
    IsTiling Set.univ (tilingOfHeight H) := by
  rw [isTiling_univ_iff]
  intro f
  rw [TriFace.existsUnique_mem_edges_iff]
  have hcl := isClosedCochainOn_def.1 (isClosedCochainOn_coboundary Set.univ H) f (Set.mem_univ f)
  have hmem : ∀ k, f.edge k ∈ tilingOfHeight H ↔
      H (f.edge k).target - H (f.edge k).v = 1 - (if k = 2 then 1 else 0) := by
    intro k
    rw [mem_tilingOfHeight, f.neutralIncrement_edge]
  simp only [hmem]
  have h0 := hH (f.edge 0)
  have h1 := hH (f.edge 1)
  have h2 := hH (f.edge 2)
  obtain ⟨d, hd⟩ : ∃ d : Fin 3 → ℤ, ∀ k, H (f.edge k).target - H (f.edge k).v = d k :=
    ⟨_, fun _ => rfl⟩
  simp only [hd] at hcl h0 h1 h2 ⊢
  have huniq : ∀ j : Fin 3, d j = 1 - (if j = 2 then 1 else 0) →
      ∀ k : Fin 3, d k = 1 - (if k = 2 then 1 else 0) → k = j := by
    intro j hj k hk
    fin_cases j <;> fin_cases k <;> simp at hj hk ⊢ <;> omega
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · exact ⟨2, by simp; omega, fun k hk => huniq 2 (by simp; omega) k hk⟩
  · exact ⟨1, by simp; omega, fun k hk => huniq 1 (by simp; omega) k hk⟩
  · exact ⟨0, by simp; omega, fun k hk => huniq 0 (by simp; omega) k hk⟩
  · omega

/-- The height function of the tiling of a height function vanishing at `0` is the height
function itself. -/
theorem tilingHeight_tilingOfHeight (hH : IsHeightFunction H) (h0 : H 0 = 0) :
    tilingHeight (tilingOfHeight H) = H :=
  (hH.isTiling_tilingOfHeight.eq_tilingHeight
    (isCochainPrimitiveOn_univ_iff.2 hH.heightCochain_tilingOfHeight) h0).symm

end IsHeightFunction

/-- The tiling of the height function of a plane tiling is the tiling itself. -/
theorem IsTiling.tilingOfHeight_tilingHeight (h : IsTiling Set.univ M) :
    tilingOfHeight (tilingHeight M) = M := by
  ext e
  rw [mem_tilingOfHeight, h.tilingHeight_target_sub_v,
    heightCochain_eq_one_sub_neutralIncrement_iff]

/-- **Heights of plane tilings.** `tilingOfHeight` is a bijection from the height functions
vanishing at `0` onto the plane tilings; its inverse is `tilingHeight`. -/
theorem tilingOfHeight_bijOn :
    Set.BijOn tilingOfHeight {H | IsHeightFunction H ∧ H 0 = 0} {M | IsTiling Set.univ M} :=
  ⟨fun _ hH => hH.1.isTiling_tilingOfHeight,
    fun H hH H' hH' hHH' => by
      rw [← hH.1.tilingHeight_tilingOfHeight hH.2, hHH', hH'.1.tilingHeight_tilingOfHeight hH'.2],
    fun M hM => ⟨tilingHeight M, ⟨hM.isHeightFunction_tilingHeight, tilingHeight_zero M⟩,
      IsTiling.tilingOfHeight_tilingHeight hM⟩⟩

/-! ### Translations -/

@[simp] theorem heightCochain_vadd (w : ℤ × ℤ) (M : Set TriEdge) (e : TriEdge) :
    heightCochain (w +ᵥ M) e = heightCochain M (-w +ᵥ e) := by
  by_cases he : -w +ᵥ e ∈ M
  · rw [heightCochain_of_mem he, heightCochain_of_mem (Set.mem_vadd_set_iff_neg_vadd_mem.2 he),
      neutralIncrement_vadd]
  · rw [heightCochain_of_notMem he,
      heightCochain_of_notMem fun h => he (Set.mem_vadd_set_iff_neg_vadd_mem.1 h),
      neutralIncrement_vadd]

/-- **Heights of translated tilings**: `H_{τ_w M}(v) = H_M(v − w) − H_M(−w)`. -/
theorem IsTiling.tilingHeight_vadd (h : IsTiling Set.univ M) (w v : ℤ × ℤ) :
    tilingHeight (w +ᵥ M) v = tilingHeight M (v - w) - tilingHeight M (-w) := by
  have hw : IsTiling Set.univ (w +ᵥ M) := by
    have := (isTiling_vadd_iff (R := Set.univ) (M := M) w).2 h
    rwa [Set.vadd_set_univ] at this
  have hg : IsCochainPrimitiveOn Set.univ (heightCochain (w +ᵥ M))
      fun v => tilingHeight M (v - w) - tilingHeight M (-w) := by
    rw [isCochainPrimitiveOn_univ_iff]
    intro e
    rw [heightCochain_vadd, ← h.tilingHeight_target_sub_v]
    simp only [TriEdge.target_vadd, TriEdge.vadd_v]
    abel_nf
  exact congrFun (hw.eq_tilingHeight hg (by simp)).symm v

/-- **Heights of invariant tilings**: if a plane tiling is invariant under the translation by
`w`, its height function increases by `H_M(w)` between `v` and `v + w`. -/
theorem IsTiling.tilingHeight_add_sub_of_vadd_eq (h : IsTiling Set.univ M) {w : ℤ × ℤ}
    (hw : w +ᵥ M = M) (v : ℤ × ℤ) :
    tilingHeight M (v + w) - tilingHeight M v = tilingHeight M w := by
  have hv := h.tilingHeight_vadd w (v + w)
  have h0 := h.tilingHeight_vadd w w
  rw [hw, add_sub_cancel_right] at hv
  rw [hw, sub_self, tilingHeight_zero] at h0
  omega

/-! ### The Lipschitz bound -/

namespace IsHeightFunction

variable (hH : IsHeightFunction H)
include hH

theorem le_add_latticeDir (v : ℤ × ℤ) (k : Fin 3) : H v ≤ H (v + latticeDir k) := by
  rcases hH ⟨v, k⟩ with h | h <;> simp only [TriEdge.target_mk] at h <;> omega

theorem add_latticeDir_le (v : ℤ × ℤ) (k : Fin 3) : H (v + latticeDir k) ≤ H v + 1 := by
  rcases hH ⟨v, k⟩ with h | h <;> simp only [TriEdge.target_mk] at h <;> omega

theorem le_add_nsmul_latticeDir (v : ℤ × ℤ) (k : Fin 3) (n : ℕ) :
    H v ≤ H (v + n • latticeDir k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul, ← add_assoc]
    exact ih.trans (hH.le_add_latticeDir _ k)

theorem add_nsmul_latticeDir_le (v : ℤ × ℤ) (k : Fin 3) (n : ℕ) :
    H (v + n • latticeDir k) ≤ H v + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul, ← add_assoc]
    have := hH.add_latticeDir_le (v + n • latticeDir k) k
    push_cast
    omega

/-- **The Lipschitz bound** for height functions: `H(u + (a, b)) − H(u) ≤ max(a, b, 0)`. -/
theorem sub_le_max (u : ℤ × ℤ) (a b : ℤ) : H (u + (a, b)) - H u ≤ max a (max b 0) := by
  -- Going from `u + (a, b)` up along `e₁` and `e₂` to `u + m e₃`, `m = max(a, b, 0)`, does not
  -- decrease `H`, and `m` steps along `e₃` raise it by at most `m`.
  set m := max a (max b 0)
  have hma : a ≤ m := le_max_left _ _
  have hmb : b ≤ m := (le_max_left _ _).trans (le_max_right _ _)
  have hm0 : 0 ≤ m := (le_max_right _ _).trans (le_max_right _ _)
  have h1 := hH.le_add_nsmul_latticeDir (u + (a, b)) 0 (m - a).toNat
  have h2 := hH.le_add_nsmul_latticeDir (u + (a, b) + (m - a).toNat • latticeDir 0) 1
    (m - b).toNat
  have h3 := hH.add_nsmul_latticeDir_le u 2 m.toNat
  have hv : u + (a, b) + (m - a).toNat • latticeDir 0 + (m - b).toNat • latticeDir 1 =
      u + m.toNat • latticeDir 2 := by
    ext <;> simp <;> omega
  rw [hv] at h2
  omega

end IsHeightFunction

/-- **The Lipschitz bound** for heights of plane tilings:
`H_M(u + (a, b)) − H_M(u) ≤ max(a, b, 0)`. -/
theorem IsTiling.tilingHeight_sub_le_max (h : IsTiling Set.univ M) (u : ℤ × ℤ) (a b : ℤ) :
    tilingHeight M (u + (a, b)) - tilingHeight M u ≤ max a (max b 0) :=
  h.isHeightFunction_tilingHeight.sub_le_max u a b

end TauCeti
