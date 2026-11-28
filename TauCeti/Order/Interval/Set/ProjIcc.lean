/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Indicator
public import Mathlib.Order.Interval.Set.ProjIcc

/-!
# Projection to a closed interval away from its endpoints

The projection `Set.projIcc a b h` of a linear order onto `[a, b]` sends every point outside
`[a, b]` to an endpoint. So a point whose projection lies in the open interval `(a, b)` is its own
projection (`Set.eq_of_coe_projIcc_eq`), half-open intervals of projections intersect `[a, b]`
(`Set.Ioc_projIcc_eq_Ioc_inter`, `Set.indicator_Ioc_projIcc`,
`Set.indicator_Ioc_projIcc_ite_le`), and taking a minimum with an upper bound commutes with clamping
(`Set.min_coe_projIcc_eq`, `Set.sub_min_coe_projIcc_eq`, `Set.sub_min_coe_projIcc_sub`,
`Set.ite_le_sub_min_coe_projIcc`).
-/

public section

namespace Set

variable {α : Type*} [LinearOrder α] {a b s t : α} {h : a ≤ b}

/-- A point whose projection to `[a, b]` is a point `s` of the open interval `(a, b)` is `s`. -/
theorem eq_of_coe_projIcc_eq (hst : (projIcc a b h t : α) = s) (hs : s ∈ Ioo a b) : t = s := by
  have ht : t ∈ Icc a b := by
    refine ⟨not_lt.1 fun ht ↦ hs.1.ne ?_, not_lt.1 fun ht ↦ hs.2.ne' ?_⟩
    · rwa [projIcc_of_le_left _ ht.le] at hst
    · rwa [projIcc_of_right_le _ ht.le] at hst
  rwa [projIcc_of_mem _ ht] at hst

/-- Projecting the endpoints of `(l, r]` onto `[s, t]` produces `(s, t] ∩ (l, r]`. -/
theorem Ioc_projIcc_eq_Ioc_inter {l r : α} (hst : s ≤ t) :
    Ioc (projIcc s t hst l : α) (projIcc s t hst r : α) = Ioc s t ∩ Ioc l r := by
  by_cases hlt : l ≤ t
  · ext u
    simp only [mem_Ioc, mem_inter_iff, coe_projIcc, min_eq_right hlt, max_lt_iff,
      le_max_iff, le_min_iff]
    constructor
    · rintro ⟨⟨hsu, hlu⟩, h1 | ⟨hut, hur⟩⟩
      · exact absurd h1 hsu.not_ge
      · exact ⟨⟨hsu, hut⟩, ⟨hlu, hur⟩⟩
    · rintro ⟨⟨hsu, hut⟩, ⟨hlu, hur⟩⟩
      exact ⟨⟨hsu, hlu⟩, Or.inr ⟨hut, hur⟩⟩
  · have htl : t < l := lt_of_not_ge hlt
    have hpl : (projIcc s t hst l : α) = t := by simp [coe_projIcc, htl.le, hst]
    have hpr : (projIcc s t hst r : α) ≤ t := (projIcc s t hst r).property.2
    ext u
    simp only [mem_Ioc, mem_inter_iff, hpl]
    constructor
    · rintro ⟨htu, hur⟩
      exact absurd (htu.trans_le (hur.trans hpr)) (lt_irrefl t)
    · rintro ⟨⟨_, hut⟩, ⟨hlu, _⟩⟩
      exact absurd (hlu.trans_le hut) htl.not_gt

/-- Indicator of a projected half-open interval `(projIcc s t l, projIcc s t r]` factors as a
nested indicator over `(s, t]` and `(l, r]`. -/
theorem indicator_Ioc_projIcc {M : Type*} [Zero M] {l r : α} (hst : s ≤ t)
    (f : α → M) (u : α) :
    (Ioc (projIcc s t hst l : α) (projIcc s t hst r : α)).indicator f u =
      (Ioc s t).indicator (fun _ ↦ (Ioc l r).indicator f u) u := by
  rw [Ioc_projIcc_eq_Ioc_inter hst]
  by_cases hu : u ∈ Ioc s t <;> simp [hu, indicator_apply]

/-- Indicator of a projected half-open interval `(projIcc s t l, projIcc s t r]` with an `l ≤ t`
guard equals the nested indicator over `(s, t]` and `(l, r]`, because any point in
`(l, r] ∩ (s, t]` satisfies `l ≤ t`. -/
theorem indicator_Ioc_projIcc_ite_le {M : Type*} [Zero M] {l r : α} (hst : s ≤ t)
    (f : α → M) (u : α) :
    (Ioc (projIcc s t hst l : α) (projIcc s t hst r : α)).indicator
        (fun x ↦ if l ≤ t then f x else 0) u =
      (Ioc s t).indicator (fun _ ↦ (Ioc l r).indicator f u) u := by
  rw [indicator_Ioc_projIcc]
  by_cases hlt : l ≤ t
  · simp [hlt]
  · by_cases hus : u ∈ Ioc s t
    · have hul : u ∉ Ioc l r := fun h ↦ hlt (h.1.trans_le hus.2).le
      simp [hlt, hus, hul]
    · simp [hlt, hus]

/-- Truncating the projection onto `[s, t]` at `T ≥ s` equals clamping `min r (min T t)` below at
`s`. -/
theorem min_coe_projIcc_eq {T : α} (hst : s ≤ t) (hsT : s ≤ T) (r : α) :
    min (projIcc s t hst r : α) T = max s (min r (min T t)) := by
  rw [coe_projIcc, min_max_distrib_right, min_eq_left hsT]
  ac_rfl

/-- Increment of a function from `s` to `min (projIcc s t r) T` when `s ≤ T`. -/
theorem sub_min_coe_projIcc_eq {G : Type*} [AddCommGroup G] {T : α}
    (hst : s ≤ t) (hsT : s ≤ T) (r : α) (f : α → G) :
    f (min (projIcc s t hst r : α) T) - f s = f (min r (min T t)) - f (min r s) := by
  rw [min_coe_projIcc_eq hst hsT]
  have hsu : s ≤ min T t := le_min hsT hst
  rcases le_total r s with hrs | hsr
  · simp [hrs, hrs.trans hsu]
  · rw [max_eq_right (le_min hsr hsu), min_eq_right hsr]

/-- Increment of a function across the projected endpoints `projIcc s t l` and `projIcc s t r`,
truncated at `T`. -/
theorem sub_min_coe_projIcc_sub {G : Type*} [AddCommGroup G] {l r T : α}
    (hst : s ≤ t) (f : α → G) :
    f (min (projIcc s t hst r : α) T) - f (min (projIcc s t hst l : α) T) =
      (f (min r (min T t)) - f (min l (min T t))) -
        (f (min r (min T s)) - f (min l (min T s))) := by
  rcases le_total T s with hTs | hsT
  · have hpl : T ≤ (projIcc s t hst l : α) := hTs.trans (projIcc s t hst l).property.1
    have hpr : T ≤ (projIcc s t hst r : α) := hTs.trans (projIcc s t hst r).property.1
    rw [min_eq_right hpl, min_eq_right hpr, min_eq_left (hTs.trans hst), min_eq_left hTs,
      sub_self, sub_self]
  · simp only [min_eq_right hsT]
    have hr := sub_min_coe_projIcc_eq hst hsT r f
    have hl := sub_min_coe_projIcc_eq hst hsT l f
    rw [← sub_sub_sub_cancel_right (f (min (projIcc s t hst r : α) T))
      (f (min (projIcc s t hst l : α) T)) (f s), hr, hl, sub_sub_sub_comm]

/-- Clipped increment over `[s, t]` vanishes when the original nondegenerate interval `(l, r]` lies
strictly to the right of `t`. -/
theorem ite_le_sub_min_coe_projIcc {G : Type*} [AddCommGroup G] {l r T : α}
    (hst : s ≤ t) (hlr : l ≤ r) (f : α → G) :
    (if l ≤ t then f (min (projIcc s t hst r : α) T) - f (min (projIcc s t hst l : α) T)
        else 0) =
      (f (min r (min T t)) - f (min l (min T t))) -
        (f (min r (min T s)) - f (min l (min T s))) := by
  by_cases hlt : l ≤ t
  · simp only [hlt, ite_true, sub_min_coe_projIcc_sub]
  · have htl : t < l := lt_of_not_ge hlt
    have htr : t < r := htl.trans_le hlr
    have h1 : min T t ≤ l := (min_le_right T t).trans htl.le
    have h2 : min T t ≤ r := (min_le_right T t).trans htr.le
    have h3 : min T s ≤ l := (min_le_right T s).trans (hst.trans htl.le)
    have h4 : min T s ≤ r := (min_le_right T s).trans (hst.trans htr.le)
    simp only [hlt, ite_false, min_eq_right h1, min_eq_right h2, min_eq_right h3, min_eq_right h4,
      sub_self]

end Set
