/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.Order.Interval.Set.UnorderedInterval
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Leaving a triangle along a segment

An affine function `f` on the line is determined by its values at `0` and `1`:
`f s = f 0 + s * (f 1 - f 0)` (`AffineMap.apply_eq_add_mul_sub`).

Read a segment `s ↦ σ s`, `s ∈ [0, 1]`, in the barycentric coordinates `f₀`, `f₁`, `f₂` of a
triangle `ABC`: these are affine functions of the parameter with sum `1`, and the triangle is
where all three are nonnegative. If the segment crosses the open side `AB` at `s₀ ∈ (0, 1)`, its
endpoints lie outside the triangle, and it avoids the three vertices, then it leaves the triangle
across the open side `AC` or `CB` at a single parameter `s₁ ∈ (0, 1)`, and runs inside the triangle
between `s₀` and `s₁` (`TauCeti.exists_triangle_exit`). This is how a strand of a knot diagram
crossing one side of the projected triangle of a Δ-move is seen to cross the projections of the
two new edges exactly once.

## Main results

* `AffineMap.apply_eq_add_mul_sub`: an affine function on the line is
  `s ↦ f 0 + s * (f 1 - f 0)`.
* `TauCeti.exists_triangle_exit`: a segment crossing one side of a triangle, with endpoints outside
  it and avoiding its vertices, leaves it across one of the other two sides, at a single point.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1,
  pp. 2–4, for triangle moves and their effect on link diagrams.
-/

public section

open Set AffineMap

/-- An affine function on the line is determined by its values at `0` and `1`. -/
theorem AffineMap.apply_eq_add_mul_sub {k : Type*} [CommRing k] (f : k →ᵃ[k] k) (s : k) :
    f s = f 0 + s * (f 1 - f 0) := by
  have h := f.apply_lineMap (0 : k) 1 s
  rw [lineMap_apply_ring', lineMap_apply_ring'] at h
  simp only [sub_zero, mul_one, add_zero] at h
  rw [h]
  ring

namespace TauCeti

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- The zero of an affine function `g` on the line positive at `s₀ < 1`, if it lies in
`[s₀, 1]`, and `2` otherwise. On `[s₀, 1]`, `g` is positive before this point and vanishes only
there. -/
private theorem exists_firstZero (g : 𝕜 →ᵃ[𝕜] 𝕜) {s₀ : 𝕜} (hs₀ : s₀ < 1) (hg : 0 < g s₀) :
    ∃ z, s₀ < z ∧ (z ≤ 1 ↔ g 1 ≤ 0) ∧ ∀ s ∈ Icc s₀ 1, (0 < g s ↔ s < z) ∧ (g s = 0 ↔ s = z) := by
  have hgs := g.apply_eq_add_mul_sub
  by_cases h1 : g 1 ≤ 0
  · -- `g s = m * (s - z)` with negative slope `m`.
    set m := g 1 - g 0
    have hm : m < 0 := by
      have h₀ := hgs s₀
      have h₁ := hgs 1
      nlinarith
    refine ⟨s₀ - g s₀ / m, ?_, ⟨fun _ ↦ h1, fun _ ↦ ?_⟩, fun s _ ↦ ?_⟩
    · have : g s₀ / m < 0 := div_neg_of_pos_of_neg hg hm
      linarith
    · rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff_of_neg hm]
      nlinarith [hgs s₀, hgs 1]
    · have hlin : g s = m * (s - (s₀ - g s₀ / m)) := by
        have hm0 : m ≠ 0 := hm.ne
        rw [hgs s, hgs s₀]
        field_simp
        ring
      rw [hlin]
      constructor
      · constructor
        · intro h; nlinarith
        · intro h; nlinarith
      · rw [mul_eq_zero]
        exact ⟨fun h ↦ sub_eq_zero.1 (h.resolve_left hm.ne),
          fun h ↦ Or.inr (sub_eq_zero.2 h)⟩
  · push Not at h1
    refine ⟨2, by linarith, ⟨fun h ↦ by linarith, fun h ↦ by linarith⟩, fun s hs ↦ ?_⟩
    have hpos : 0 < g s := by
      have hcomb : (1 - s₀) * g s = (1 - s) * g s₀ + (s - s₀) * g 1 := by
        rw [hgs s, hgs s₀]
        ring
      have h1s : 0 < 1 - s₀ := by linarith
      have : 0 < (1 - s) * g s₀ + (s - s₀) * g 1 := by
        rcases eq_or_lt_of_le hs.2 with rfl | hlt
        · simp only [sub_self, zero_mul, zero_add]
          exact mul_pos h1s h1
        · exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) hg)
            (mul_nonneg (by linarith [hs.1]) h1.le)
      rw [← hcomb] at this
      exact pos_of_mul_pos_right this h1s.le
    exact ⟨⟨fun _ ↦ by linarith [hs.2], fun _ ↦ hpos⟩,
      ⟨fun h ↦ (hpos.ne' h).elim, fun h ↦ by linarith [hs.2]⟩⟩

/-- A segment entering a triangle across one side, along which the barycentric coordinate `f₂`
opposite that side increases, leaves it across one of the other two sides. -/
private theorem exists_exit_of_pos {f₀ f₁ f₂ : 𝕜 →ᵃ[𝕜] 𝕜} {s₀ : 𝕜} (hs₀ : s₀ ∈ Ioo (0 : 𝕜) 1)
    (h₂ : f₂ s₀ = 0) (h₂' : 0 < f₂ 1) (h₀ : 0 < f₀ s₀) (h₁ : 0 < f₁ s₀)
    (hout : f₀ 1 < 0 ∨ f₁ 1 < 0) (hC : ∀ s ∈ Icc (0 : 𝕜) 1, ¬ (f₀ s = 0 ∧ f₁ s = 0)) :
    ∃ s₁ ∈ Ioo s₀ 1, 0 < f₂ s₁ ∧ ((f₁ s₁ = 0 ∧ 0 < f₀ s₁) ∨ (f₀ s₁ = 0 ∧ 0 < f₁ s₁)) ∧
      (∀ s ∈ Icc (0 : 𝕜) 1, 0 ≤ f₂ s → (f₁ s = 0 ∧ 0 ≤ f₀ s ∨ f₀ s = 0 ∧ 0 ≤ f₁ s) → s = s₁) ∧
      ∀ s ∈ Icc s₀ s₁, 0 ≤ f₀ s ∧ 0 ≤ f₁ s ∧ 0 ≤ f₂ s := by
  obtain ⟨z₀, hz₀, hz₀1, hz₀s⟩ := exists_firstZero f₀ hs₀.2 h₀
  obtain ⟨z₁, hz₁, hz₁1, hz₁s⟩ := exists_firstZero f₁ hs₀.2 h₁
  -- `f₂` increases, from `0` at `s₀`.
  have hf₂ := f₂.apply_eq_add_mul_sub
  have hκ : 0 < f₂ 1 - f₂ 0 := by nlinarith [hf₂ s₀, hs₀.1, hs₀.2]
  have hf₂pos (s : 𝕜) : 0 < f₂ s ↔ s₀ < s := by
    have : f₂ s = (s - s₀) * (f₂ 1 - f₂ 0) := by rw [hf₂ s]; linarith [hf₂ s₀]
    rw [this]
    exact ⟨fun h ↦ by nlinarith, fun h ↦ mul_pos (by linarith) hκ⟩
  have hf₂nn (s : 𝕜) : 0 ≤ f₂ s ↔ s₀ ≤ s := by
    have : f₂ s = (s - s₀) * (f₂ 1 - f₂ 0) := by rw [hf₂ s]; linarith [hf₂ s₀]
    rw [this]
    exact ⟨fun h ↦ by nlinarith, fun h ↦ mul_nonneg (by linarith) hκ.le⟩
  -- A nonnegative coordinate on `[s₀, 1]` has not yet passed its zero.
  have hle₀ {s} (hs : s ∈ Icc s₀ 1) (h : 0 ≤ f₀ s) : s ≤ z₀ := by
    rcases h.lt_or_eq with h | h
    exacts [((hz₀s s hs).1.1 h).le, ((hz₀s s hs).2.1 h.symm).le]
  have hle₁ {s} (hs : s ∈ Icc s₀ 1) (h : 0 ≤ f₁ s) : s ≤ z₁ := by
    rcases h.lt_or_eq with h | h
    exacts [((hz₁s s hs).1.1 h).le, ((hz₁s s hs).2.1 h.symm).le]
  have hnn₀ {s} (hs : s ∈ Icc s₀ 1) (h : s ≤ z₀) : 0 ≤ f₀ s := by
    rcases h.lt_or_eq with h | h
    exacts [((hz₀s s hs).1.2 h).le, ((hz₀s s hs).2.2 h).ge]
  have hnn₁ {s} (hs : s ∈ Icc s₀ 1) (h : s ≤ z₁) : 0 ≤ f₁ s := by
    rcases h.lt_or_eq with h | h
    exacts [((hz₁s s hs).1.2 h).le, ((hz₁s s hs).2.2 h).ge]
  -- The segment leaves at the first zero of `f₀` or `f₁`.
  set s₁ := min z₀ z₁
  have hs₁1 : s₁ < 1 := by
    rcases hout with h | h
    · refine (min_le_left _ _).trans_lt (lt_of_le_of_ne (hz₀1.2 h.le) fun he ↦ ?_)
      exact h.ne ((hz₀s 1 ⟨hs₀.2.le, le_rfl⟩).2.2 he.symm)
    · refine (min_le_right _ _).trans_lt (lt_of_le_of_ne (hz₁1.2 h.le) fun he ↦ ?_)
      exact h.ne ((hz₁s 1 ⟨hs₀.2.le, le_rfl⟩).2.2 he.symm)
  have hs₀₁ : s₀ < s₁ := lt_min hz₀ hz₁
  have hs₁I : s₁ ∈ Icc s₀ 1 := ⟨hs₀₁.le, hs₁1.le⟩
  have hs₁I' : s₁ ∈ Icc (0 : 𝕜) 1 := ⟨hs₀.1.le.trans hs₀₁.le, hs₁1.le⟩
  refine ⟨s₁, ⟨hs₀₁, hs₁1⟩, (hf₂pos s₁).2 hs₀₁, ?_, fun s hs h2 h ↦ ?_, fun s hs ↦ ?_⟩
  · rcases le_total z₀ z₁ with h | h
    · have hs₁ : s₁ = z₀ := min_eq_left h
      have hf₀ : f₀ s₁ = 0 := (hz₀s s₁ hs₁I).2.2 hs₁
      refine .inr ⟨hf₀, (hz₁s s₁ hs₁I).1.2 (lt_of_le_of_ne (hs₁ ▸ h) fun he ↦ ?_)⟩
      exact hC s₁ hs₁I' ⟨hf₀, (hz₁s s₁ hs₁I).2.2 he⟩
    · have hs₁ : s₁ = z₁ := min_eq_right h
      have hf₁ : f₁ s₁ = 0 := (hz₁s s₁ hs₁I).2.2 hs₁
      refine .inl ⟨hf₁, (hz₀s s₁ hs₁I).1.2 (lt_of_le_of_ne (hs₁ ▸ h) fun he ↦ ?_)⟩
      exact hC s₁ hs₁I' ⟨(hz₀s s₁ hs₁I).2.2 he, hf₁⟩
  · have hsI : s ∈ Icc s₀ 1 := ⟨(hf₂nn s).1 h2, hs.2⟩
    rcases h with ⟨h1, h0⟩ | ⟨h0, h1⟩
    · have hsz : s = z₁ := (hz₁s s hsI).2.1 h1
      exact hsz.trans (min_eq_right (hsz ▸ hle₀ hsI h0)).symm
    · have hsz : s = z₀ := (hz₀s s hsI).2.1 h0
      exact hsz.trans (min_eq_left (hsz ▸ hle₁ hsI h1)).symm
  · have hsI : s ∈ Icc s₀ 1 := ⟨hs.1, hs.2.trans hs₁1.le⟩
    exact ⟨hnn₀ hsI (hs.2.trans (min_le_left _ _)), hnn₁ hsI (hs.2.trans (min_le_right _ _)),
      (hf₂nn s).2 hs.1⟩

/-- **A segment crossing one side of a triangle leaves it across another.** Read a segment
`s ↦ σ s`, `s ∈ [0, 1]`, in the barycentric coordinates `f₀`, `f₁`, `f₂` of a triangle `ABC`.
Suppose that it crosses the open side `AB` at `s₀ ∈ (0, 1)`, that its endpoints lie outside the
triangle, and that it avoids the three vertices. Then it leaves the triangle at another parameter
`s₁ ∈ (0, 1)`, in the open side `AC` or `CB`; it meets those two sides only there, and it runs
inside the triangle between `s₀` and `s₁`. -/
theorem exists_triangle_exit {f₀ f₁ f₂ : 𝕜 →ᵃ[𝕜] 𝕜} (hsum : ∀ s, f₀ s + f₁ s + f₂ s = 1)
    {s₀ : 𝕜} (hs₀ : s₀ ∈ Ioo (0 : 𝕜) 1) (h₂ : f₂ s₀ = 0) (h₀ : 0 < f₀ s₀) (h₁ : 0 < f₁ s₀)
    (hout : ∀ s ∈ ({0, 1} : Set 𝕜), ¬ (0 ≤ f₀ s ∧ 0 ≤ f₁ s ∧ 0 ≤ f₂ s))
    (hA : ∀ s ∈ Icc (0 : 𝕜) 1, ¬ (f₁ s = 0 ∧ f₂ s = 0))
    (hB : ∀ s ∈ Icc (0 : 𝕜) 1, ¬ (f₀ s = 0 ∧ f₂ s = 0))
    (hC : ∀ s ∈ Icc (0 : 𝕜) 1, ¬ (f₀ s = 0 ∧ f₁ s = 0)) :
    ∃ s₁ ∈ Ioo (0 : 𝕜) 1, s₁ ≠ s₀ ∧ 0 < f₂ s₁ ∧
      ((f₁ s₁ = 0 ∧ 0 < f₀ s₁) ∨ (f₀ s₁ = 0 ∧ 0 < f₁ s₁)) ∧
      (∀ s ∈ Icc (0 : 𝕜) 1, 0 ≤ f₂ s → (f₁ s = 0 ∧ 0 ≤ f₀ s ∨ f₀ s = 0 ∧ 0 ≤ f₁ s) → s = s₁) ∧
      ∀ s ∈ uIcc s₀ s₁, 0 ≤ f₀ s ∧ 0 ≤ f₁ s ∧ 0 ≤ f₂ s := by
  have hf₀ := f₀.apply_eq_add_mul_sub
  have hf₂ := f₂.apply_eq_add_mul_sub
  have hout₀ := hout 0 (by simp)
  have hout₁ := hout 1 (by simp)
  rcases lt_trichotomy (f₂ 1 - f₂ 0) 0 with hκ | hκ | hκ
  · -- `f₂` decreases: run along the segment backwards.
    set r : 𝕜 →ᵃ[𝕜] 𝕜 := lineMap 1 0
    have hr (s : 𝕜) : r s = 1 - s := by simp [r, lineMap_apply_ring']; ring
    have hrI {s : 𝕜} (hs : s ∈ Icc (0 : 𝕜) 1) : r s ∈ Icc (0 : 𝕜) 1 := by
      rw [hr]; exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have hrr (s : 𝕜) : r (r s) = s := by rw [hr, hr]; ring
    have hrs₀ : r (r s₀) = s₀ := hrr s₀
    obtain ⟨s₁, hs₁, hpos, hside, huniq, hin⟩ := exists_exit_of_pos (f₀ := f₀.comp r)
      (f₁ := f₁.comp r) (f₂ := f₂.comp r) (s₀ := r s₀)
      (by rw [hr]; exact ⟨by linarith [hs₀.2], by linarith [hs₀.1]⟩)
      (by rwa [AffineMap.comp_apply, hrs₀])
      (by rw [AffineMap.comp_apply, hr, sub_self]; nlinarith [hf₂ s₀, hs₀.1])
      (by rwa [AffineMap.comp_apply, hrs₀]) (by rwa [AffineMap.comp_apply, hrs₀])
      (by
        simp only [AffineMap.comp_apply, hr, sub_self]
        by_contra! h
        exact hout₀ ⟨h.1, h.2, by nlinarith [hf₂ s₀, hs₀.1]⟩)
      (fun s hs ↦ hC (r s) (hrI hs))
    refine ⟨r s₁, ?_, ?_, hpos, hside, fun s hs h2 h ↦ ?_, fun s hs ↦ ?_⟩
    · rw [hr]; exact ⟨by linarith [hs₁.2], by linarith [hs₀.2, hs₁.1, hr s₀]⟩
    · rw [hr]; intro h; linarith [hs₁.1, hr s₀]
    · rw [← huniq (r s) (hrI hs) (by rwa [AffineMap.comp_apply, hrr])
        (by simpa only [AffineMap.comp_apply, hrr] using h), hrr]
    · have := hin (r s) (by
        rw [hr, hr] at *
        rcases (mem_uIcc.1 hs) with h | h <;> constructor <;> linarith [hs₁.1])
      simpa only [AffineMap.comp_apply, hrr] using this
  · -- `f₂` vanishes identically, so the segment runs along the line `AB` and meets a vertex.
    exfalso
    have hz (s : 𝕜) : f₂ s = 0 := by
      have h := hf₂ s₀
      rw [hκ, mul_zero, add_zero] at h
      rw [hf₂ s, hκ, mul_zero, add_zero, ← h, h₂]
    have hf₁ (s : 𝕜) : f₁ s = 1 - f₀ s := by linarith [hsum s, hz s]
    have h01 : f₀ s₀ < 1 := by linarith [hf₁ s₀]
    simp only [hz, le_refl, and_true, hf₁, sub_nonneg, not_and, not_le] at hout₀ hout₁
    rcases lt_or_ge (f₀ 0) 0 with h | h
    · -- `f₀` increases from below `0` to above `1`, so it takes the value `1`.
      have h1 : 1 < f₀ 1 := by
        rcases lt_or_ge (f₀ 1) 0 with h' | h'
        · nlinarith [hf₀ s₀, hs₀.1, hs₀.2]
        · exact hout₁ h'
      refine hA ((1 - f₀ 0) / (f₀ 1 - f₀ 0)) ⟨div_nonneg (by linarith) (by linarith),
        (div_le_one (by linarith)).2 (by linarith)⟩ ⟨?_, hz _⟩
      have hne : f₀ 1 - f₀ 0 ≠ 0 := (by linarith : (0 : 𝕜) < f₀ 1 - f₀ 0).ne'
      rw [hf₁, hf₀]
      field_simp
      ring
    · -- `f₀` decreases from above `1` to below `0`, so it vanishes.
      have h0 : 1 < f₀ 0 := hout₀ h
      have h1 : f₀ 1 < 0 := by
        by_contra! h'
        have := hout₁ h'
        nlinarith [hf₀ s₀, hs₀.1, hs₀.2]
      refine hB (f₀ 0 / (f₀ 0 - f₀ 1)) ⟨div_nonneg (by linarith) (by linarith),
        (div_le_one (by linarith)).2 (by linarith)⟩ ⟨?_, hz _⟩
      have hne : f₀ 0 - f₀ 1 ≠ 0 := (by linarith : (0 : 𝕜) < f₀ 0 - f₀ 1).ne'
      rw [hf₀]
      field_simp
      ring
  · obtain ⟨s₁, hs₁, hpos, hside, huniq, hin⟩ := exists_exit_of_pos hs₀ h₂
      (by nlinarith [hf₂ s₀, hs₀.2]) h₀ h₁
      (by by_contra! h; exact hout₁ ⟨h.1, h.2, by nlinarith [hf₂ s₀, hs₀.2]⟩) hC
    exact ⟨s₁, ⟨hs₀.1.trans hs₁.1, hs₁.2⟩, hs₁.1.ne', hpos, hside, huniq,
      by rwa [uIcc_of_le hs₁.1.le]⟩


end TauCeti
