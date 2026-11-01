/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Fin
public import TauCeti.Algebra.Order.BigOperators.Antitone
import TauCeti.GroupTheory.Perm.Basic

/-!
# Charging the moves of a permutation of `Fin L` across the gaps between points

For a permutation `σ` of `Fin L`, a point `x` with `σ x < x` crosses the gaps `c` with
`σ x < c ≤ x`, at depth `x - c`, and a point with `x < σ x` crosses the gaps `c` with
`x < c ≤ σ x`. The points with `x < σ x` are ranked by decreasing image (`Equiv.Perm.upRank`).
On every set of forward-moved points closed under passing to larger images, the ranks enumerate
an initial segment (`Equiv.Perm.image_upRank`).

At each gap as many points cross forward as backward. If `σ` moves the points below `N` forward
and the others backward, then below every threshold there are at most as many backward depths
as forward ranks at each gap (`Equiv.Perm.card_cross_backward_le`). Charging a backward move
across `j` gaps by `ρ₀, …, ρⱼ₋₁` and every gap crossed by a forward move by `ρ` at its rank, the
backward charges are therefore dominated by the forward ones for a nonnegative antitone `ρ`
(`Equiv.Perm.prod_prod_range_le_prod_pow_upRank`). This is the combinatorial core of Coleman's
coefficient bound, read off the Leibniz expansion of a Sylvester matrix.

## Main results

* `Equiv.Perm.prod_upRank`: products along the ranks of the forward-moved points are products
  over an initial segment.
* `Equiv.Perm.prod_prod_range_le_prod_pow_upRank`: the crossing estimate.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendix A3.
-/

public section

open Finset

namespace Equiv.Perm

variable {L : ℕ} (σ : Perm (Fin L))

/-- The rank of `x` among the points moved forward by `σ`, ordered by decreasing image. -/
def upRank (x : Fin L) : ℕ :=
  #{y : Fin L | (y : ℕ) < σ y ∧ (σ x : ℕ) < σ y}

/-- The rank of `x` counts the forward-moved points whose image exceeds that of `x`. -/
theorem upRank_def (x : Fin L) :
    σ.upRank x = #{y : Fin L | (y : ℕ) < σ y ∧ (σ x : ℕ) < σ y} := (rfl)

/-- Distinct forward-moved points have distinct ranks, since their images are distinct. -/
theorem upRank_injOn : Set.InjOn (upRank σ) {x : Fin L | (x : ℕ) < σ x} := by
  intro x hx y hy hxy
  by_contra hne
  have hσ : (σ x : ℕ) ≠ σ y := fun h ↦ hne (σ.injective (Fin.ext h))
  -- the point with the smaller image has the larger rank
  have key {x y : Fin L} (hy : (y : ℕ) < σ y) (h : (σ x : ℕ) < σ y) : upRank σ y < upRank σ x :=
    card_lt_card <| (ssubset_iff_of_subset fun z hz ↦ by
      simp only [mem_filter, mem_univ, true_and] at hz ⊢
      exact ⟨hz.1, h.trans hz.2⟩).2
        ⟨y, by simp only [mem_filter, mem_univ, true_and]; exact ⟨hy, h⟩,
          by simp only [mem_filter, mem_univ, lt_irrefl, and_false, not_false_eq_true]⟩
  rcases lt_or_gt_of_ne hσ with h | h
  · exact (key hy h).ne hxy.symm
  · exact (key hx h).ne hxy

/-- On a set of forward-moved points closed under passing to larger images, the ranks enumerate
`range` of its size. -/
theorem image_upRank {S : Finset (Fin L)} (hS : ∀ x ∈ S, (x : ℕ) < σ x)
    (hclosed : ∀ x ∈ S, ∀ y : Fin L, (y : ℕ) < σ y → (σ x : ℕ) < σ y → y ∈ S) :
    S.image (upRank σ) = range #S := by
  have hinj : Set.InjOn (upRank σ) S := (upRank_injOn σ).mono fun x hx ↦ hS x hx
  refine eq_of_subset_of_card_le (fun r hr ↦ ?_) (by rw [card_range, card_image_of_injOn hinj])
  obtain ⟨x, hx, rfl⟩ := mem_image.1 hr
  refine mem_range.2 ((card_le_card fun y hy ↦ ?_).trans_lt
    (card_erase_lt_of_mem hx))
  simp only [mem_filter, mem_univ, true_and] at hy
  exact mem_erase.2 ⟨fun h ↦ (h ▸ hy.2).false, hclosed x hx y hy.1 hy.2⟩

/-- On a set of forward-moved points closed under passing to larger images, exactly `t` points
have rank below `t`, for `t` at most its size. -/
theorem card_filter_upRank_lt {S : Finset (Fin L)} (hS : ∀ x ∈ S, (x : ℕ) < σ x)
    (hclosed : ∀ x ∈ S, ∀ y : Fin L, (y : ℕ) < σ y → (σ x : ℕ) < σ y → y ∈ S) {t : ℕ}
    (ht : t ≤ #S) : #{x ∈ S | upRank σ x < t} = t := by
  have himage := image_upRank σ hS hclosed
  have hfi : {x ∈ S | upRank σ x < t}.image (upRank σ) = range t := by
    ext r
    simp only [mem_image, mem_filter, mem_range]
    constructor
    · rintro ⟨x, ⟨-, hx⟩, rfl⟩
      exact hx
    · intro hr
      obtain ⟨x, hx, rfl⟩ := mem_image.1 (himage ▸ mem_range.2 (hr.trans_le ht))
      exact ⟨x, ⟨hx, hr⟩, rfl⟩
  rw [← card_image_of_injOn ((upRank_injOn σ).mono fun x hx ↦ hS x (mem_filter.1 hx).1), hfi,
    card_range]

/-- The products of a sequence along the ranks of the forward-moved points are its products over
an initial segment. -/
theorem prod_upRank {M : Type*} [CommMonoid M] (β : ℕ → M) :
    ∏ x ∈ {x : Fin L | (x : ℕ) < σ x}, β (upRank σ x) =
      ∏ t ∈ range #{x : Fin L | (x : ℕ) < σ x}, β t := by
  rw [← image_upRank σ (fun x hx ↦ (mem_filter.1 hx).2) fun x _ y hy _ ↦ by simpa using hy,
    prod_image fun x hx y hy ↦ upRank_injOn σ (by simpa using hx) (by simpa using hy)]

/-- **Charges at one gap.** If `σ` moves the points below `N` forward and the others backward,
then for every `t`, at most as many backward moves cross the gap `c` at depth below `t` as
forward moves of rank below `t`. -/
theorem card_cross_backward_le {N : ℕ} (hfwd : ∀ x : Fin L, (x : ℕ) < N → (x : ℕ) ≤ σ x)
    (hbwd : ∀ x : Fin L, N ≤ (x : ℕ) → (σ x : ℕ) ≤ x) (c t : ℕ) :
    #{x : Fin L | ((σ x : ℕ) < c ∧ c ≤ x) ∧ (x : ℕ) - c < t} ≤
      #{x : Fin L | ((x : ℕ) < c ∧ c ≤ σ x) ∧ upRank σ x < t} := by
  -- the forward-moved points landing beyond the gap
  set P : Finset (Fin L) := {y : Fin L | (y : ℕ) < σ y ∧ c ≤ σ y}
  have hPpos : ∀ x ∈ P, (x : ℕ) < σ x := fun x hx ↦ (mem_filter.1 hx).2.1
  have hPclosed : ∀ x ∈ P, ∀ y : Fin L, (y : ℕ) < σ y → (σ x : ℕ) < σ y → y ∈ P :=
    fun x hx y hy hxy ↦ by
      simp only [P, mem_filter, mem_univ, true_and] at hx ⊢
      exact ⟨hy, hx.2.trans hxy.le⟩
  have himage : P.image (upRank σ) = range #P := image_upRank σ hPpos hPclosed
  have hrank : ∀ x ∈ P, upRank σ x < #P := fun x hx ↦
    mem_range.1 (himage ▸ mem_image_of_mem _ hx)
  have hflow : #{x : Fin L | (x : ℕ) < c ∧ c ≤ σ x} = #{x : Fin L | (σ x : ℕ) < c ∧ c ≤ x} := by
    simpa only [not_le] using σ.card_filter_not_and_apply_eq fun x : Fin L ↦ c ≤ (x : ℕ)
  rcases le_or_gt #P t with hPt | htP
  · -- every forward move across the gap has rank below `t`
    calc #{x : Fin L | ((σ x : ℕ) < c ∧ c ≤ x) ∧ (x : ℕ) - c < t}
        ≤ #{x : Fin L | (σ x : ℕ) < c ∧ c ≤ x} := card_le_card fun x hx ↦ by
          simp only [mem_filter] at hx ⊢
          exact ⟨hx.1, hx.2.1⟩
      _ = #{x : Fin L | ((x : ℕ) < c ∧ c ≤ σ x) ∧ upRank σ x < t} := by
        rw [← hflow]
        congr 1
        refine filter_congr fun x _ ↦ ⟨fun hx ↦ ⟨hx, ?_⟩, And.left⟩
        refine (hrank x ?_).trans_le hPt
        simp only [P, mem_filter, mem_univ, true_and]
        exact ⟨by omega, hx.2⟩
  -- otherwise the `t` highest-landing forward moves all cross the gap, except those starting
  -- beyond it, of which there are at most `N - c`
  have hP : #{x ∈ P | upRank σ x < t} = t := card_filter_upRank_lt σ hPpos hPclosed htP.le
  have hhigh : #(P.filter fun x : Fin L ↦ c ≤ (x : ℕ)) ≤ N - c := by
    refine (card_le_card_of_injOn (fun x : Fin L ↦ (x : ℕ)) (t := Ico c N) (fun x hx ↦ ?_)
      fun x _ y _ h ↦ Fin.ext h).trans_eq (Nat.card_Ico c N)
    simp only [P, coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx
    have : (x : ℕ) < N := by
      by_contra! hN
      have := hbwd x hN
      omega
    simp [hx.2, this]
  have hlow : #{x : Fin L | ((σ x : ℕ) < c ∧ c ≤ x) ∧ (x : ℕ) - c < t} ≤ c + t - max c N := by
    refine (card_le_card_of_injOn (fun x : Fin L ↦ (x : ℕ)) (t := Ico (max c N) (c + t))
      (fun x hx ↦ ?_) fun x _ y _ h ↦ Fin.ext h).trans_eq (Nat.card_Ico _ _)
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx
    have : N ≤ (x : ℕ) := by
      by_contra! hN
      have := hfwd x hN
      omega
    simp only [coe_Ico, Set.mem_Ico, max_le_iff]
    omega
  have hsplit : #{x ∈ P | upRank σ x < t} ≤
      #{x : Fin L | ((x : ℕ) < c ∧ c ≤ σ x) ∧ upRank σ x < t} +
        #(P.filter fun x : Fin L ↦ c ≤ (x : ℕ)) := by
    refine (card_le_card fun x hx ↦ ?_).trans (card_union_le _ _)
    simp only [P, mem_filter, mem_univ, true_and, mem_union] at hx ⊢
    by_cases hxc : (x : ℕ) < c
    · exact Or.inl ⟨⟨hxc, hx.1.2⟩, hx.2⟩
    · exact Or.inr ⟨hx.1, not_lt.1 hxc⟩
  omega

/-- **Crossing estimate.** If `σ` moves the points below `N` forward and the others backward, and
`ρ` is a nonnegative antitone sequence, then the product over the backward moves of
`∏ i < x - σ x, ρ i` is at most the product over the forward moves of
`ρ (rank x) ^ (σ x - x)`. -/
theorem prod_prod_range_le_prod_pow_upRank {N : ℕ}
    (hfwd : ∀ x : Fin L, (x : ℕ) < N → (x : ℕ) ≤ σ x)
    (hbwd : ∀ x : Fin L, N ≤ (x : ℕ) → (σ x : ℕ) ≤ x) {R : Type*} [CommMonoidWithZero R]
    [Preorder R] [ZeroLEOneClass R] [PosMulMono R] {ρ : ℕ → R} (hρ₀ : ∀ i, 0 ≤ ρ i)
    (hρ : Antitone ρ) :
    ∏ x : Fin L, ∏ i ∈ range ((x : ℕ) - σ x), ρ i ≤
      ∏ x : Fin L, ρ (upRank σ x) ^ ((σ x : ℕ) - x) := by
  -- distribute both sides over the gaps crossed
  have hl (x : Fin L) : ∏ i ∈ range ((x : ℕ) - σ x), ρ i = ∏ c ∈ Ioc (σ x : ℕ) x, ρ (x - c) :=
    prod_nbij' (fun i ↦ x - i) (fun c ↦ x - c) (fun i hi ↦ by simp at hi ⊢; omega)
      (fun c hc ↦ by simp at hc ⊢; omega) (fun i hi ↦ by simp at hi; omega)
      (fun c hc ↦ by simp at hc; omega) fun i hi ↦ by simp at hi; congr 1; omega
  have hr (x : Fin L) :
      ρ (upRank σ x) ^ ((σ x : ℕ) - x) = ∏ c ∈ Ioc (x : ℕ) (σ x), ρ (upRank σ x) := by
    rw [prod_const, Nat.card_Ioc]
  simp_rw [hl, hr]
  rw [prod_comm' (t' := range (L + 1)) (s' := fun c ↦ {x : Fin L | (σ x : ℕ) < c ∧ c ≤ x})
      fun x c ↦ by simp only [mem_univ, mem_Ioc, mem_filter, mem_range, true_and]; omega,
    prod_comm' (t' := range (L + 1)) (s' := fun c ↦ {x : Fin L | (x : ℕ) < c ∧ c ≤ σ x})
      fun x c ↦ by simp only [mem_univ, mem_Ioc, mem_filter, mem_range, true_and]; omega]
  refine prod_le_prod₀ (fun c _ ↦ prod_nonneg fun x _ ↦ hρ₀ _) fun c _ ↦ ?_
  -- compare the depths and the ranks at the gap `c`
  set D : Finset (Fin L) := {x | (σ x : ℕ) < c ∧ c ≤ x}
  set U : Finset (Fin L) := {x | (x : ℕ) < c ∧ c ≤ σ x}
  have hD : Set.InjOn (fun x : Fin L ↦ (x : ℕ) - c) D := fun x hx y hy h ↦ by
    simp only [D, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx hy h
    exact Fin.ext (by omega)
  have hU : Set.InjOn (upRank σ) U := (upRank_injOn σ).mono fun x hx ↦ by
    simp only [U, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
    omega
  rw [← prod_image (f := fun i ↦ ρ i) fun x hx y hy h ↦ hD hx hy h,
    ← prod_image (f := fun i ↦ ρ i) fun x hx y hy h ↦ hU hx hy h]
  refine prod_le_prod_of_card_filter_lt_le hρ₀ hρ ?_ fun k ↦ ?_
  · rw [card_image_of_injOn hD, card_image_of_injOn hU]
    simpa only [not_le] using (σ.card_filter_not_and_apply_eq fun x : Fin L ↦ c ≤ (x : ℕ)).symm
  · rw [filter_image, filter_image, card_image_of_injOn (hD.mono (filter_subset _ _)),
      card_image_of_injOn (hU.mono (filter_subset _ _)), filter_filter, filter_filter]
    exact card_cross_backward_le σ hfwd hbwd c k

end Equiv.Perm
