/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Cube.Basic
import TauCeti.Data.Set.Function
import TauCeti.Data.Set.InjOnUnion
import TauCeti.Topology.Homeomorph.CompactQuotient
import TauCeti.Topology.Homeomorph.SetCongr

/-!
# Gluing four paths along the boundary of the unit square

Four injective paths `top : Path a b`, `bot : Path c d`, `left : Path a c`, and
`right : Path b d` in a Hausdorff topological space `X` whose opposite edges are disjoint and whose
adjacent edges meet only at their shared corners glue continuously along `TauCeti.squareBoundary`
to define a homeomorphism from `TauCeti.squareBoundary` onto the union of their ranges
(`TauCeti.exists_homeomorph_squareBoundary`).

## Main declarations

* `TauCeti.exists_homeomorph_squareBoundary`: gluing four injective paths along
  `TauCeti.squareBoundary` into a homeomorphism onto their combined range.
-/

public section

noncomputable section

open Function Set Topology unitInterval

namespace TauCeti

/-- Gluing four injective paths `top : Path a b`, `bot : Path c d`, `left : Path a c`, and
`right : Path b d` in a Hausdorff space `X` whose opposite edges are disjoint and whose adjacent
edges meet only at their shared corners defines a homeomorphism from `TauCeti.squareBoundary` onto
the union of their ranges, restricting to the four paths along the four sides. -/
theorem exists_homeomorph_squareBoundary {X : Type*} [TopologicalSpace X] [T2Space X]
    {a b c d : X} {top : Path a b} {bot : Path c d} {left : Path a c} {right : Path b d}
    (htop : Injective top) (hbot : Injective bot)
    (hleft : Injective left) (hright : Injective right)
    (htb : Disjoint (range top) (range bot)) (hlr : Disjoint (range left) (range right))
    (htl : range top ∩ range left = {a}) (htr : range top ∩ range right = {b})
    (hbl : range bot ∩ range left = {c}) (hbr : range bot ∩ range right = {d}) :
    ∃ ψ : squareBoundary ≃ₜ ↥(range top ∪ range bot ∪ range left ∪ range right),
      (∀ (s : I) (hs : (s, 0) ∈ squareBoundary), (ψ ⟨(s, 0), hs⟩ : X) = top s) ∧
      (∀ (s : I) (hs : (s, 1) ∈ squareBoundary), (ψ ⟨(s, 1), hs⟩ : X) = bot s) ∧
      (∀ (t : I) (hs : (0, t) ∈ squareBoundary), (ψ ⟨(0, t), hs⟩ : X) = left t) ∧
      (∀ (t : I) (hs : (1, t) ∈ squareBoundary), (ψ ⟨(1, t), hs⟩ : X) = right t) := by
  classical
  set C : Set X := range top ∪ range bot ∪ range left ∪ range right
  -- Piecewise parametrization of the four sides of the boundary of `I × I`.
  let f : I × I → X := fun p =>
    if p.2 = 0 then top p.1
    else if p.2 = 1 then bot p.1
    else if p.1 = 0 then left p.2
    else right p.2
  have hf_top (s : I) : f (s, 0) = top s := by simp [f]
  have hf_bot (s : I) : f (s, 1) = bot s := by simp [f]
  have hf_left (t : I) : f (0, t) = left t := by simp only [f]; split_ifs <;> simp_all
  have hf_right (t : I) : f (1, t) = right t := by simp only [f]; split_ifs <;> simp_all
  let S : Fin 4 → Set (I × I)
    | 0 => {p | p.1 = 0}
    | 1 => {p | p.1 = 1}
    | 2 => {p | p.2 = 0}
    | 3 => {p | p.2 = 1}
  have hS_closed (i : Fin 4) : IsClosed (S i) := by
    fin_cases i <;> exact isClosed_eq (by fun_prop) continuous_const
  have hS_union : squareBoundary = (S 0 ∪ S 1) ∪ (S 2 ∪ S 3) := by
    ext p; simp [S, or_assoc]
  have hS_cont (i : Fin 4) : ContinuousOn f (S i) := by
    fin_cases i
    · exact (left.continuous.comp continuous_snd).continuousOn.congr fun ⟨s, t⟩ h => by
        obtain rfl : s = 0 := h; exact hf_left t
    · exact (right.continuous.comp continuous_snd).continuousOn.congr fun ⟨s, t⟩ h => by
        obtain rfl : s = 1 := h; exact hf_right t
    · exact (top.continuous.comp continuous_fst).continuousOn.congr fun ⟨s, t⟩ h => by
        obtain rfl : t = 0 := h; exact hf_top s
    · exact (bot.continuous.comp continuous_fst).continuousOn.congr fun ⟨s, t⟩ h => by
        obtain rfl : t = 1 := h; exact hf_bot s
  have hfc : ContinuousOn f squareBoundary := by
    rw [hS_union]
    exact ((hS_cont 0).union_of_isClosed (hS_cont 1) (hS_closed 0) (hS_closed 1)).union_of_isClosed
      ((hS_cont 2).union_of_isClosed (hS_cont 3) (hS_closed 2) (hS_closed 3))
      ((hS_closed 0).union (hS_closed 1)) ((hS_closed 2).union (hS_closed 3))
  -- `f` maps `squareBoundary` bijectively onto `C`.
  have hbij : BijOn f squareBoundary C := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨s, t⟩ hst
      simp only [mem_squareBoundary_iff] at hst
      rcases hst with rfl | rfl | rfl | rfl <;> simp [C, hf_left, hf_right, hf_top, hf_bot]
    · refine injOn_of_subset_iUnion (S := S) ?_ ?_ ?_
      · rintro ⟨s, t⟩ hst
        simp only [mem_squareBoundary_iff] at hst
        rcases hst with rfl | rfl | rfl | rfl
        · exact mem_iUnion.2 ⟨0, rfl⟩
        · exact mem_iUnion.2 ⟨1, rfl⟩
        · exact mem_iUnion.2 ⟨2, rfl⟩
        · exact mem_iUnion.2 ⟨3, rfl⟩
      · intro i
        fin_cases i <;> rintro ⟨s₁, t₁⟩ h1 ⟨s₂, t₂⟩ h2 heq
        · obtain rfl : s₁ = 0 := h1; obtain rfl : s₂ = 0 := h2
          rw [hf_left, hf_left] at heq; exact Prod.ext rfl (hleft heq)
        · obtain rfl : s₁ = 1 := h1; obtain rfl : s₂ = 1 := h2
          rw [hf_right, hf_right] at heq; exact Prod.ext rfl (hright heq)
        · obtain rfl : t₁ = 0 := h1; obtain rfl : t₂ = 0 := h2
          rw [hf_top, hf_top] at heq; exact Prod.ext (htop heq) rfl
        · obtain rfl : t₁ = 1 := h1; obtain rfl : t₂ = 1 := h2
          rw [hf_bot, hf_bot] at heq; exact Prod.ext (hbot heq) rfl
      · intro i j hij ⟨s₁, t₁⟩ ⟨s₂, t₂⟩ hi hj heq
        fin_cases i <;> fin_cases j
        all_goals try exact absurd hij (by decide)
        · obtain rfl : s₁ = 0 := hi; obtain rfl : s₂ = 1 := hj
          rw [hf_left, hf_right] at heq
          exact (hlr.ne_of_mem (mem_range_self t₁) (mem_range_self t₂) heq).elim
        · obtain rfl : s₁ = 0 := hi; obtain rfl : t₂ = 0 := hj
          rw [hf_left, hf_top] at heq
          exact Or.inl (hleft.eq_of_apply_eq_of_range_inter_subset_singleton
            (inter_comm _ _ ▸ htl.subset) left.source heq)
        · obtain rfl : s₁ = 0 := hi; obtain rfl : t₂ = 1 := hj
          rw [hf_left, hf_bot] at heq
          exact Or.inl (hleft.eq_of_apply_eq_of_range_inter_subset_singleton
            (inter_comm _ _ ▸ hbl.subset) left.target heq)
        · obtain rfl : s₁ = 1 := hi; obtain rfl : t₂ = 0 := hj
          rw [hf_right, hf_top] at heq
          exact Or.inl (hright.eq_of_apply_eq_of_range_inter_subset_singleton
            (inter_comm _ _ ▸ htr.subset) right.source heq)
        · obtain rfl : s₁ = 1 := hi; obtain rfl : t₂ = 1 := hj
          rw [hf_right, hf_bot] at heq
          exact Or.inl (hright.eq_of_apply_eq_of_range_inter_subset_singleton
            (inter_comm _ _ ▸ hbr.subset) right.target heq)
        · obtain rfl : t₁ = 0 := hi; obtain rfl : t₂ = 1 := hj
          rw [hf_top, hf_bot] at heq
          exact (htb.ne_of_mem (mem_range_self s₁) (mem_range_self s₂) heq).elim
    · rintro z (((⟨s, rfl⟩ | ⟨s, rfl⟩) | ⟨t, rfl⟩) | ⟨t, rfl⟩)
      · exact ⟨(s, 0), by simp, hf_top s⟩
      · exact ⟨(s, 1), by simp, hf_bot s⟩
      · exact ⟨(0, t), by simp, hf_left t⟩
      · exact ⟨(1, t), by simp, hf_right t⟩
  let ψ : squareBoundary ≃ₜ C :=
    (isClosed_squareBoundary.isCompact.imageHomeomorph hfc hbij.injOn).trans
      (Homeomorph.setCongr hbij.image_eq)
  have hψ_coe (q : squareBoundary) : (ψ q : X) = f q := by
    simp [ψ, Homeomorph.trans_apply, Homeomorph.setCongr_apply]
  exact ⟨ψ, fun s _ => (hψ_coe _).trans (hf_top s), fun s _ => (hψ_coe _).trans (hf_bot s),
    fun t _ => (hψ_coe _).trans (hf_left t), fun t _ => (hψ_coe _).trans (hf_right t)⟩

end TauCeti
