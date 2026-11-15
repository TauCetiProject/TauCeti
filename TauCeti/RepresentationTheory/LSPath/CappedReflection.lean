/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.LinearMap

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import TauCeti.LinearAlgebra.Reflection

/-!
# Capped record reflection and dilation of paths

`PLPath.cappedReflection f x c` reflects the increasing records of a path up to height `c`,
keeping equal-height excursions. It is the presentation-independent version of
`PLPath.reflectRecords`. Lowering is capped reflection at the minimum height plus one,
when the lowering operator is defined.

Positive dilation multiplies all heights and caps by the same scalar, leaving the relative
cut positions unchanged (`PLPath.cappedReflection_map_smul`). For a normalized root-coroot pair
`f x = 2`, two successive capped reflections compose into a single capped reflection
(`PLPath.cappedReflection_cappedReflection`): reflecting up to `c₁` and then up to `c₂` reflects up
to the larger of `c₁` and `c₂` shifted by twice the first record increase. Iterated root operators
and root-operator similarity under dilation are deduced from these two facts in
`TauCeti.RepresentationTheory.LSPath.Similarity`.

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §§1, 5 (root operators and similarity).
-/

public section

namespace TauCeti.PLPath

open Module Relation

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] {f : Dual 𝕜 V} {x : V}

/-- Normalizing a presentation before record reflection does not change the resulting path. -/
@[simp]
theorem normalize_reflectRecords_normalize (c : 𝕜) (l : List V) :
    normalize 𝕜 (reflectRecords f x c (normalize 𝕜 l)) =
      normalize 𝕜 (reflectRecords f x c l) := by
  suffices ∀ m, ReflTransGen (Move 𝕜) l m →
      normalize 𝕜 (reflectRecords f x c m) = normalize 𝕜 (reflectRecords f x c l) from
    this _ (reflTransGen_move_normalize l)
  intro m h
  induction h with
  | refl => rfl
  | tail _ h ih => exact (h.normalize_reflectRecords c).symm.trans ih

/-- Reflect the increasing records up to the cap `c`, retaining equal-height excursions.
The operation is independent of the segment presentation. -/
noncomputable def cappedReflection (f : Dual 𝕜 V) (x : V) (c : 𝕜) (p : PLPath 𝕜 V) :
    PLPath 𝕜 V :=
  ofSegments 𝕜 (reflectRecords f x c p.segments)

/-- Compute capped reflection on any segment presentation, without normalizing it first. -/
@[simp]
theorem cappedReflection_ofSegments (c : 𝕜) (l : List V) :
    cappedReflection f x c (ofSegments 𝕜 l) = ofSegments 𝕜 (reflectRecords f x c l) := by
  apply PLPath.ext
  simp only [cappedReflection, segments_ofSegments, normalize_reflectRecords_normalize]

@[simp]
theorem cappedReflection_one (c : 𝕜) : cappedReflection f x c (1 : PLPath 𝕜 V) = 1 := by
  rw [← ofSegments_nil, cappedReflection_ofSegments, reflectRecords_nil]

/-- A cap below the minimum height reflects no part of the path. -/
@[simp]
theorem cappedReflection_eq_self {c : 𝕜} (p : PLPath 𝕜 V) (hc : c ≤ p.minHeight f) :
    cappedReflection f x c p = p := by
  rw [minHeight_def] at hc
  rw [cappedReflection, reflectRecords_of_le_listMinHeight hc, ofSegments_segments]

/-- The endpoint change is the capped increase from the minimum to the final height. -/
@[simp]
theorem endpoint_cappedReflection (c : 𝕜) (p : PLPath 𝕜 V) :
    (cappedReflection f x c p).endpoint =
      p.endpoint - (min (f p.endpoint) c - min (p.minHeight f) c) • x := by
  rw [cappedReflection, endpoint_ofSegments, sum_reflectRecords, endpoint_def, minHeight_def]

/-- For a normalized root-coroot pair, capped reflection lowers the minimum by the capped
increase from the minimum to the final height. -/
@[simp]
theorem minHeight_cappedReflection (hx : f x = 2) (c : 𝕜) (p : PLPath 𝕜 V) :
    (cappedReflection f x c p).minHeight f =
      p.minHeight f - (min (f p.endpoint) c - min (p.minHeight f) c) := by
  rw [cappedReflection, minHeight_ofSegments, listMinHeight_reflectRecords hx,
    endpoint_def, minHeight_def]

/-- Capped reflection of a concatenation uses the tail minimum for the first cap and translates
by the first factor's final height for the second cap. -/
theorem cappedReflection_mul (c : 𝕜) (p q : PLPath 𝕜 V) :
    cappedReflection f x c (p * q) =
      cappedReflection f x (min c (f p.endpoint + q.minHeight f)) p *
        cappedReflection f x (c - f p.endpoint) q := by
  obtain ⟨l, rfl⟩ := ofSegments_surjective p
  obtain ⟨m, rfl⟩ := ofSegments_surjective q
  rw [← ofSegments_append, cappedReflection_ofSegments, reflectRecords_append,
    ofSegments_append]
  simp only [cappedReflection_ofSegments, endpoint_ofSegments, minHeight_ofSegments]

/-- Capped reflection is natural for linear maps preserving the height form and carrying the
root to the target root, including maps that collapse segments. -/
theorem cappedReflection_map {W : Type*} [AddCommGroup W] [Module 𝕜 W]
    {g : V →ₗ[𝕜] W} {f' : Dual 𝕜 W} (hf : f'.comp g = f)
    (x : V) (c : 𝕜) (p : PLPath 𝕜 V) :
    cappedReflection f' (g x) c (p.map g) = (cappedReflection f x c p).map g := by
  obtain ⟨l, rfl⟩ := ofSegments_surjective p
  simp only [map_ofSegments, cappedReflection_ofSegments, reflectRecords_map hf]

/-- Lowering is capped reflection at the minimum plus one, provided the height string has
at least one step left. -/
theorem lower_eq_some_cappedReflection (p : PLPath 𝕜 V)
    (hp : 1 ≤ f p.endpoint - p.minHeight f) :
    lower f x p = some (cappedReflection f x (p.minHeight f + 1) p) := by
  obtain ⟨l, rfl⟩ := ofSegments_surjective p
  simp only [endpoint_ofSegments, minHeight_ofSegments] at hp
  rw [lower_ofSegments, listLower_def, ite_eq_left hp, Option.map_some,
    cappedReflection_ofSegments, minHeight_ofSegments]

/-! ## Positive dilation -/

/-- Dilation by a positive scalar preserves every cut fraction in capped record reflection.
This is an equality of raw segment lists, before normalization. -/
theorem reflectRecords_map_smul {a : 𝕜} (ha : 0 < a) (c : 𝕜) (l : List V) :
    reflectRecords f x (a * c) (l.map (a • ·)) = (reflectRecords f x c l).map (a • ·) := by
  induction l generalizing c with
  | nil => simp
  | cons v l ih =>
    have hcap : min (f (a • v) + listMinHeight f (l.map (a • ·))) (a * c) =
        a * min (f v + listMinHeight f l) c := by
      rw [map_smul, smul_eq_mul, listMinHeight_map_smul ha.le, ← mul_add,
        mul_min_of_nonneg _ _ ha.le]
    have hshift : a * c - f (a • v) = a * (c - f v) := by
      simp only [map_smul, smul_eq_mul, mul_sub]
    have hcut : (a * min (f v + listMinHeight f l) c) / (a * f v) =
        min (f v + listMinHeight f l) c / f v := mul_div_mul_left _ _ ha.ne'
    by_cases h : 0 < min (f v + listMinHeight f l) c
    · rw [List.map_cons, reflectRecords_cons_of_pos (by rw [hcap]; exact mul_pos ha h),
        reflectRecords_cons_of_pos h]
      simp only [hcap, hshift]
      simp only [map_smul, smul_eq_mul, hcut, ih, List.map_cons]
      congr 1
      · rw [smul_comm]
      · rw [smul_comm]
    · rw [List.map_cons, reflectRecords_cons_of_nonpos (by
          rw [hcap]; exact mul_nonpos_of_nonneg_of_nonpos ha.le (le_of_not_gt h)),
        reflectRecords_cons_of_nonpos (le_of_not_gt h), hshift, ih, List.map_cons]

/-- Positive dilation commutes with capped reflection when the cap is dilated as well.
Unlike height-preserving naturality, this keeps the root and coroot fixed. -/
theorem cappedReflection_map_smul {a : 𝕜} (ha : 0 < a) (c : 𝕜) (p : PLPath 𝕜 V) :
    cappedReflection f x (a * c) (p.map (a • LinearMap.id)) =
      (cappedReflection f x c p).map (a • LinearMap.id) := by
  obtain ⟨l, rfl⟩ := ofSegments_surjective p
  simpa only [map_ofSegments, cappedReflection_ofSegments, LinearMap.coe_smul,
    Pi.smul_def, LinearMap.id_apply] using
    congrArg (ofSegments 𝕜) (reflectRecords_map_smul (f := f) ha c l)

/-! ## Composition of capped reflections -/

/-- Any cap at or above the final height reflects the same records as the final height itself. -/
theorem reflectRecords_of_apply_sum_le {c : 𝕜} {l : List V} (hc : f l.sum ≤ c) :
    reflectRecords f x c l = reflectRecords f x (f l.sum) l := by
  induction l generalizing c with
  | nil => simp
  | cons v l ih =>
    have hle : f v + listMinHeight f l ≤ f (v :: l).sum := by
      rw [List.sum_cons, map_add]
      exact add_le_add_right (listMinHeight_le_apply_sum l) (f v)
    have hmin : min (f v + listMinHeight f l) c =
        min (f v + listMinHeight f l) (f (v :: l).sum) := by
      rw [min_eq_left (hle.trans hc), min_eq_left hle]
    have htail : f l.sum ≤ c - f v := by
      rw [List.sum_cons, map_add] at hc
      exact le_sub_iff_add_le'.mpr hc
    have hsum : f (v :: l).sum - f v = f l.sum := by
      rw [List.sum_cons, map_add, add_sub_cancel_left]
    by_cases h : 0 < min (f v + listMinHeight f l) c
    · rw [reflectRecords_cons_of_pos h, reflectRecords_cons_of_pos (hmin ▸ h), hmin, ih htail,
        hsum]
    · rw [reflectRecords_cons_of_nonpos (not_lt.mp h),
        reflectRecords_cons_of_nonpos (hmin ▸ not_lt.mp h), ih htail, hsum]

/-- Any cap at or above the endpoint height gives the same capped reflection as capping at the
endpoint height. -/
theorem cappedReflection_eq_of_apply_endpoint_le {c : 𝕜} (p : PLPath 𝕜 V)
    (hc : f p.endpoint ≤ c) :
    cappedReflection f x c p = cappedReflection f x (f p.endpoint) p := by
  rw [endpoint_def] at hc
  rw [cappedReflection, cappedReflection, endpoint_def, reflectRecords_of_apply_sum_le hc]

/-- When the minimal height equals the final height, no record strictly increases, so record
reflection leaves the segment list unchanged for every cap. -/
theorem reflectRecords_of_listMinHeight_eq_apply_sum (c : 𝕜) {l : List V}
    (hl : listMinHeight f l = f l.sum) :
    reflectRecords f x c l = l := by
  induction l generalizing c with
  | nil => exact reflectRecords_nil c
  | cons v l ih =>
    rw [listMinHeight_cons, List.sum_cons, map_add] at hl
    have hle : f v + listMinHeight f l ≤ f v + f l.sum :=
      add_le_add_right (listMinHeight_le_apply_sum l) (f v)
    have hnonpos : f v + listMinHeight f l ≤ 0 :=
      hle.trans (hl ▸ min_le_left 0 _)
    have htail : listMinHeight f l = f l.sum := by
      have hge : f v + f l.sum ≤ f v + listMinHeight f l := hl ▸ min_le_right 0 _
      exact add_left_cancel (le_antisymm hle hge)
    rw [reflectRecords_cons_of_nonpos (min_le_of_left_le hnonpos), ih (c - f v) htail]

/-- When the minimal height equals the endpoint height, capped reflection fixes the path for every
cap. -/
theorem cappedReflection_eq_self_of_minHeight_eq_apply_endpoint (c : 𝕜) (p : PLPath 𝕜 V)
    (hp : p.minHeight f = f p.endpoint) :
    cappedReflection f x c p = p := by
  rw [minHeight_def, endpoint_def] at hp
  rw [cappedReflection, reflectRecords_of_listMinHeight_eq_apply_sum c hp, ofSegments_segments]

/-- Capped reflection fixes any straight path of nonpositive height. -/
@[simp]
theorem cappedReflection_straight_of_nonpos (c : 𝕜) {v : V} (hv : f v ≤ 0) :
    cappedReflection f x c (straight 𝕜 v) = straight 𝕜 v :=
  cappedReflection_eq_self_of_minHeight_eq_apply_endpoint c (straight 𝕜 v)
    (by simp [min_eq_right hv])

/-- On a straight path of positive height, capped reflection reflects the initial fraction
`max 0 (min (f v) c) / f v` and keeps the complementary fraction. -/
theorem cappedReflection_straight_of_pos (c : 𝕜) {v : V} (hv : 0 < f v) :
    cappedReflection f x c (straight 𝕜 v) =
      straight 𝕜 (preReflection x f ((max 0 (min (f v) c) / f v) • v)) *
        straight 𝕜 ((1 - max 0 (min (f v) c) / f v) • v) := by
  by_cases hc : 0 < c
  · have hpos : 0 < min (f v + listMinHeight f ([] : List V)) c := by
      simpa using lt_min hv hc
    rw [max_eq_right (le_min hv.le hc.le), straight_def, cappedReflection_ofSegments,
      reflectRecords_cons_of_pos hpos]
    simp [ofSegments_cons]
  · have hmax : max 0 (min (f v) c) = 0 := max_eq_left (min_le_of_right_le (not_lt.mp hc))
    rw [hmax, zero_div, zero_smul, map_zero, straight_zero, one_mul, sub_zero, one_smul]
    exact cappedReflection_eq_self (straight 𝕜 v) (by simpa [min_eq_left hv.le] using not_lt.mp hc)

private theorem cappedReflection_cappedReflection_straight (hx : f x = 2) (c₁ c₂ : 𝕜) (v : V) :
    cappedReflection f x c₂ (cappedReflection f x c₁ (straight 𝕜 v)) =
      cappedReflection f x
        (max c₁ (c₂ + 2 * (min (f (straight 𝕜 v).endpoint) c₁ -
          min ((straight 𝕜 v).minHeight f) c₁)))
        (straight 𝕜 v) := by
  rcases le_or_gt (f v) 0 with hv | hv
  · simp [cappedReflection_straight_of_nonpos _ hv]
  set r₁ := max 0 (min (f v) c₁) with hr₁_def
  have hr₁_nonneg : 0 ≤ r₁ := le_max_left _ _
  have hr₁_le : r₁ ≤ f v := max_le hv.le (min_le_left _ _)
  have hΔ : min (f (straight 𝕜 v).endpoint) c₁ - min ((straight 𝕜 v).minHeight f) c₁ = r₁ := by
    simp only [endpoint_straight, minHeight_straight, min_eq_left hv.le, r₁, min_def, max_def]
    split_ifs <;> linarith
  set C := max c₁ (c₂ + 2 * r₁)
  rw [hΔ, cappedReflection_straight_of_pos c₁ hv, ← hr₁_def, cappedReflection_mul]
  have hp₁ : f (preReflection x f ((r₁ / f v) • v)) = -r₁ := by
    rw [apply_preReflection hx, map_smul, smul_eq_mul, div_mul_cancel₀ _ hv.ne']
  have hp₁_nonpos : f (preReflection x f ((r₁ / f v) • v)) ≤ 0 := by linarith
  rw [cappedReflection_straight_of_nonpos _ hp₁_nonpos, endpoint_straight, hp₁, sub_neg_eq_add]
  rcases hr₁_le.eq_or_lt with hr₁_eq | hr₁_lt
  · have hfc₁ : f v ≤ c₁ := by
      simp only [r₁, min_def, max_def] at hr₁_eq
      split_ifs at hr₁_eq <;> linarith
    have hrC : max 0 (min (f v) C) = f v := by
      rw [min_eq_left (hfc₁.trans (le_max_left _ _)), max_eq_right hv.le]
    rw [cappedReflection_straight_of_pos C hv, hrC, hr₁_eq, div_self hv.ne', sub_self, zero_smul,
      straight_zero, cappedReflection_one]
  · have hfv₂ : 0 < f v - r₁ := sub_pos.mpr hr₁_lt
    have hp₂ : f ((1 - r₁ / f v) • v) = f v - r₁ := by
      rw [map_smul, smul_eq_mul, sub_mul, one_mul, div_mul_cancel₀ _ hv.ne']
    rw [cappedReflection_straight_of_pos (c₂ + r₁) (hp₂ ▸ hfv₂),
      cappedReflection_straight_of_pos C hv, hp₂]
    set r₂ := max 0 (min (f v - r₁) (c₂ + r₁))
    have hr₂_nonneg : 0 ≤ r₂ := le_max_left _ _
    have hcut₁ : (r₂ / (f v - r₁)) • (1 - r₁ / f v) • v = (r₂ / f v) • v := by
      rw [smul_smul]
      congr 1
      have : 1 - r₁ / f v = (f v - r₁) / f v := by rw [sub_div, div_self hv.ne']
      rw [this, div_mul_div_cancel₀ hfv₂.ne']
    have hcut₂ : (1 - r₂ / (f v - r₁)) • (1 - r₁ / f v) • v = (1 - (r₁ + r₂) / f v) • v := by
      rw [smul_smul]
      congr 1
      have h1 : 1 - r₂ / (f v - r₁) = (f v - r₁ - r₂) / (f v - r₁) := by
        rw [sub_div, div_self hfv₂.ne']
      have h2 : 1 - r₁ / f v = (f v - r₁) / f v := by rw [sub_div, div_self hv.ne']
      rw [h1, h2, div_mul_div_cancel₀ hfv₂.ne', sub_sub, sub_div, div_self hv.ne']
    have hsum_r : r₁ + r₂ = max 0 (min (f v) C) := by
      have hc₁_lt : c₁ < f v := by
        by_contra hc₁_ge
        exact hr₁_lt.ne' (by
          simp only [r₁]
          rw [min_eq_left (not_lt.mp hc₁_ge), max_eq_right hv.le])
      rcases le_or_gt c₁ 0 with hc₁ | hc₁
      · have hr₁0 : r₁ = 0 := max_eq_left (min_le_of_right_le hc₁)
        have hC : min (f v) C = min (f v) (max c₁ c₂) := by simp [C, hr₁0]
        rw [hr₁0, zero_add]
        simp only [r₂, hr₁0, sub_zero, add_zero, hC, min_def, max_def]
        split_ifs <;> linarith
      · have hr₁c : r₁ = c₁ := by
          simp only [r₁]
          rw [min_eq_right hc₁_lt.le, max_eq_right hc₁.le]
        simp only [r₂, C, hr₁c, min_def, max_def]
        split_ifs <;> linarith
    rw [hcut₁, hcut₂, ← mul_assoc, map_smul, map_smul,
      straight_smul_mul_straight_smul (div_nonneg hr₁_nonneg hv.le) (div_nonneg hr₂_nonneg hv.le),
      ← add_div, ← map_smul, hsum_r]

private theorem cappedReflection_comp_cap_left {ep hp eq hq c₁ c₂ : 𝕜}
    (hq0 : hq ≤ 0) (hqe : hq ≤ eq) :
    let c₁' := min c₁ (ep + hq)
    let Δp := min ep c₁' - min hp c₁'
    let Δq := min eq (c₁ - ep) - min hq (c₁ - ep)
    let Δ := min (ep + eq) c₁ - min (min hp (ep + hq)) c₁
    max c₁' (min c₂ (ep - 2 * Δp + (hq - Δq)) + 2 * Δp) =
      min (max c₁ (c₂ + 2 * Δ)) (ep + hq) := by
  intro c₁' Δp Δq Δ
  have hΔp : Δp = c₁' - min (min hp (ep + hq)) c₁ := by
    have hc₁'_ep : min ep c₁' = c₁' := min_eq_right ((min_le_right _ _).trans (by linarith))
    have hc₁'_hp : min hp c₁' = min (min hp (ep + hq)) c₁ := by
      simp only [c₁']
      ac_rfl
    simp only [Δp]
    rw [hc₁'_ep, hc₁'_hp]
  have hΔq_nonneg : 0 ≤ Δq := by
    simp only [Δq, min_def]
    split_ifs <;> linarith
  rcases le_total c₁ (ep + hq) with hc₁ | hc₁
  · have hΔq0 : Δq = 0 := by
      have h1 : c₁ - ep ≤ hq := by linarith
      simp only [Δq]
      rw [min_eq_right (h1.trans hqe), min_eq_right h1, sub_self]
    have hc₁' : c₁' = c₁ := min_eq_left hc₁
    have hΔ_eq : Δ = Δp := by
      rw [hΔp, hc₁']
      simp only [Δ]
      rw [min_eq_right (hc₁.trans (by linarith))]
    rw [hΔq0, sub_zero, hΔ_eq, hc₁']
    simp only [min_def, max_def]
    split_ifs <;> linarith
  · have hc₁' : c₁' = ep + hq := min_eq_right hc₁
    have h1 : min c₂ (ep - 2 * Δp + (hq - Δq)) + 2 * Δp ≤ ep + hq := by
      have := min_le_right c₂ (ep - 2 * Δp + (hq - Δq))
      linarith
    rw [hc₁', max_eq_left h1, min_eq_right (hc₁.trans (le_max_left _ _))]

private theorem cappedReflection_comp_cap_right {ep hp eq hq c₁ c₂ : 𝕜} (hq0 : hq ≤ 0) :
    let c₁' := min c₁ (ep + hq)
    let Δp := min ep c₁' - min hp c₁'
    let Δq := min eq (c₁ - ep) - min hq (c₁ - ep)
    let Δ := min (ep + eq) c₁ - min (min hp (ep + hq)) c₁
    max (c₁ - ep) (c₂ - (ep - 2 * Δp) + 2 * Δq) =
      max c₁ (c₂ + 2 * Δ) - ep := by
  intro c₁' Δp Δq Δ
  have hΔp : Δp = c₁' - min (min hp (ep + hq)) c₁ := by
    have hc₁'_ep : min ep c₁' = c₁' := min_eq_right ((min_le_right _ _).trans (by linarith))
    have hc₁'_hp : min hp c₁' = min (min hp (ep + hq)) c₁ := by
      simp only [c₁']
      ac_rfl
    simp only [Δp]
    rw [hc₁'_ep, hc₁'_hp]
  have hΔq : Δq = min (ep + eq) c₁ - c₁' := by
    simp only [Δq, c₁', min_def]
    split_ifs <;> linarith
  have hsum : Δp + Δq = Δ := by
    rw [hΔp, hΔq]
    simp only [Δ]
    ring
  have hshift : c₂ - (ep - 2 * Δp) + 2 * Δq = c₂ + 2 * Δ - ep := by
    rw [← hsum]
    ring
  rw [hshift]
  simp only [max_def]
  split_ifs <;> linarith

/-- **Composition of capped record reflections**: for a normalized root-coroot pair `f x = 2`,
applying `cappedReflection` up to `c₁` and then up to `c₂` is a single `cappedReflection` whose cap
is the larger of `c₁` and `c₂` shifted up by twice the first record increase
`min (f p.endpoint) c₁ - min (p.minHeight f) c₁`. -/
theorem cappedReflection_cappedReflection (hx : f x = 2) (c₁ c₂ : 𝕜) (p : PLPath 𝕜 V) :
    cappedReflection f x c₂ (cappedReflection f x c₁ p) =
      cappedReflection f x
        (max c₁ (c₂ + 2 * (min (f p.endpoint) c₁ - min (p.minHeight f) c₁))) p := by
  obtain ⟨l, rfl⟩ := ofSegments_surjective p
  induction l generalizing c₁ c₂ with
  | nil => simp
  | cons v l ih =>
    rw [ofSegments_cons]
    set p := straight 𝕜 v
    set q := ofSegments 𝕜 l
    rw [cappedReflection_mul, cappedReflection_mul,
      cappedReflection_cappedReflection_straight hx, ih, cappedReflection_mul]
    simp only [endpoint_cappedReflection, minHeight_cappedReflection hx, endpoint_mul, map_add,
      minHeight_mul, map_sub, map_smul, smul_eq_mul, hx, mul_comm _ (2 : 𝕜)]
    rw [cappedReflection_comp_cap_left (minHeight_nonpos q) (minHeight_le_apply_endpoint q),
      cappedReflection_comp_cap_right (minHeight_nonpos q)]

/-- Raw segment-list form of `PLPath.cappedReflection_cappedReflection`: two successive record
reflections normalize to a single record reflection. -/
theorem normalize_reflectRecords_reflectRecords (hx : f x = 2) (c₁ c₂ : 𝕜) (l : List V) :
    normalize 𝕜 (reflectRecords f x c₂ (reflectRecords f x c₁ l)) =
      normalize 𝕜 (reflectRecords f x
        (max c₁ (c₂ + 2 * (min (f l.sum) c₁ - min (listMinHeight f l) c₁))) l) := by
  have h := congrArg PLPath.segments
    (cappedReflection_cappedReflection hx c₁ c₂ (ofSegments 𝕜 l))
  simpa only [cappedReflection_ofSegments, endpoint_ofSegments, minHeight_ofSegments,
    segments_ofSegments] using h

/-- Reflecting up to `p.minHeight f + a` (for `0 ≤ a ≤ f p.endpoint - p.minHeight f`) and then
reflecting up to the new minimum height plus `b` (`0 ≤ b`) equals a single capped reflection up to
`p.minHeight f + (a + b)`. -/
theorem cappedReflection_minHeight_add (hx : f x = 2) {a b : 𝕜} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (p : PLPath 𝕜 V) (hap : a ≤ f p.endpoint - p.minHeight f) :
    cappedReflection f x
        ((cappedReflection f x (p.minHeight f + a) p).minHeight f + b)
        (cappedReflection f x (p.minHeight f + a) p) =
      cappedReflection f x (p.minHeight f + (a + b)) p := by
  have hmin₁ : min (f p.endpoint) (p.minHeight f + a) = p.minHeight f + a :=
    min_eq_right (by linarith)
  have hmin₂ : min (p.minHeight f) (p.minHeight f + a) = p.minHeight f :=
    min_eq_left (by linarith)
  rw [cappedReflection_cappedReflection hx, minHeight_cappedReflection hx, hmin₁, hmin₂]
  congr 1
  have hshift : p.minHeight f - (p.minHeight f + a - p.minHeight f) + b +
      2 * (p.minHeight f + a - p.minHeight f) = p.minHeight f + (a + b) := by ring
  rw [hshift, max_eq_right (by linarith)]

end TauCeti.PLPath
