/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Slope

/-!
# Gluing convex functions across points and overlapping intervals

A real function which is convex on `(-∞, a]` and on `[a, ∞)` is convex on all of `ℝ` as soon as
its left derivative at `a` is at most its right derivative there. Over any linearly ordered field,
two convex (or concave) functions on `[a, c]` and `[b, d]` with a nondegenerate overlap `b < c`
glue to `[a, d]`, and iterating across a strictly increasing subdivision glues convexity (or
concavity) along a chain of two-step intervals `[t k, t (k + 2)]`. This complements the monotone
and antitone gluing lemmas of `Mathlib.Analysis.Convex.Piecewise`.

## Main statements

* `TauCeti.convexOn_univ_of_convexOn_Iic_Ici`: a function convex on both sides of `a` whose
  one-sided derivatives at `a` satisfy `f'(a⁻) ≤ f'(a⁺)` is convex on `ℝ`.
* `TauCeti.convexOn_Icc_of_overlap`, `TauCeti.concaveOn_Icc_of_overlap`: convexity and concavity on
  `[a, c]` and `[b, d]` with `a ≤ b < c ≤ d` imply convexity and concavity on `[a, d]`.
* `TauCeti.convexOn_Icc_of_subdivision`, `TauCeti.concaveOn_Icc_of_subdivision`: convexity and
  concavity along `[t 0, t 1]` and every two-step interval `[t k, t (k + 2)]` of a strictly
  increasing subdivision imply convexity and concavity on `[t 0, t (Fin.last (m + 1))]`.
-/

public section

namespace TauCeti

open Set

/-- Gluing convex functions: if `f : ℝ → ℝ` is convex on `(-∞, a]` and on `[a, ∞)`, and its
derivative `m₁` at `a` within `(-∞, a]` is at most its derivative `m₂` at `a` within `[a, ∞)`,
then `f` is convex on `ℝ`. -/
theorem convexOn_univ_of_convexOn_Iic_Ici {f : ℝ → ℝ} {a m₁ m₂ : ℝ}
    (hl : ConvexOn ℝ (Iic a) f) (hr : ConvexOn ℝ (Ici a) f)
    (hl' : HasDerivWithinAt f m₁ (Iic a) a) (hr' : HasDerivWithinAt f m₂ (Ici a) a)
    (hm : m₁ ≤ m₂) : ConvexOn ℝ univ f := by
  -- Secants ending at `a` have slope at most `m₂`, secants starting at `a` slope at least `m₂`.
  have hla : ∀ x < a, (f a - f x) / (a - x) ≤ m₂ := fun x hx => by
    have := hl.slope_le_of_hasDerivWithinAt (mem_Iic.2 hx.le) self_mem_Iic hx hl'
    rw [slope_def_field] at this
    exact this.trans hm
  have hra : ∀ z, a < z → m₂ ≤ (f z - f a) / (z - a) := fun z hz => by
    have := hr.le_slope_of_hasDerivWithinAt self_mem_Ici (mem_Ici.2 hz.le) hz hr'
    rwa [slope_def_field] at this
  -- For `u < v < w`, the slope on `[u, w]` is a weighted average of those on `[u, v]`, `[v, w]`.
  have avg : ∀ {u v w : ℝ}, u < v → v < w →
      (f w - f u) / (w - u) * (w - u) =
        (f v - f u) / (v - u) * (v - u) + (f w - f v) / (w - v) * (w - v) := by
    intro u v w huv hvw
    rw [div_mul_cancel₀ _ (sub_pos.2 (huv.trans hvw)).ne', div_mul_cancel₀ _ (sub_pos.2 huv).ne',
      div_mul_cancel₀ _ (sub_pos.2 hvw).ne']
    ring
  refine convexOn_of_slope_mono_adjacent convex_univ fun {x y z} _ _ hxy hyz => ?_
  rcases le_or_gt z a with hza | haz
  · exact hl.slope_mono_adjacent (mem_Iic.2 ((hxy.trans hyz).le.trans hza)) (mem_Iic.2 hza)
      hxy hyz
  rcases le_or_gt a x with hax | hxa
  · exact hr.slope_mono_adjacent (mem_Ici.2 hax) (mem_Ici.2 (hax.trans (hxy.trans hyz).le))
      hxy hyz
  -- It remains to treat `x < a < z`.
  rcases lt_trichotomy y a with hya | rfl | hay
  · -- The slope on `[y, z]` is at least the slope on `[y, a]`, which bounds that on `[x, y]`.
    refine (hl.slope_mono_adjacent (mem_Iic.2 (hxy.trans hya).le) self_mem_Iic hxy hya).trans ?_
    have h₁ := hla y hya
    have h₂ := hra z haz
    have h := avg hya haz
    refine le_of_mul_le_mul_right ?_ (sub_pos.2 hyz)
    rw [h]
    linarith [mul_le_mul_of_nonneg_right (h₁.trans h₂) (sub_pos.2 haz).le]
  · exact (hla x hxa).trans (hra z haz)
  · -- The slope on `[x, y]` is at most the slope on `[a, y]`, which bounds that on `[y, z]`.
    refine le_trans ?_ (hr.slope_mono_adjacent self_mem_Ici (mem_Ici.2 (hay.trans hyz).le) hay hyz)
    have h₁ := hla x hxa
    have h₂ := hra y hay
    have h := avg hxa hay
    refine le_of_mul_le_mul_right ?_ (sub_pos.2 hxy)
    rw [h]
    linarith [mul_le_mul_of_nonneg_right (h₁.trans h₂) (sub_pos.2 hxa).le]

section Subdivision

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Gluing convex functions across a nondegenerate overlap: if `a ≤ b < c ≤ d` and `f : 𝕜 → 𝕜` is
convex on `[a, c]` and on `[b, d]`, then `f` is convex on `[a, d]`. -/
theorem convexOn_Icc_of_overlap {a b c d : 𝕜} {f : 𝕜 → 𝕜}
    (hab : a ≤ b) (hbc : b < c) (hcd : c ≤ d)
    (hl : ConvexOn 𝕜 (Icc a c) f) (hr : ConvexOn 𝕜 (Icc b d) f) :
    ConvexOn 𝕜 (Icc a d) f := by
  have avg : ∀ {u v w : 𝕜}, u < v → v < w →
      (f w - f u) / (w - u) * (w - u) =
        (f v - f u) / (v - u) * (v - u) + (f w - f v) / (w - v) * (w - v) := by
    intro u v w huv hvw
    rw [div_mul_cancel₀ _ (sub_pos.2 (huv.trans hvw)).ne', div_mul_cancel₀ _ (sub_pos.2 huv).ne',
      div_mul_cancel₀ _ (sub_pos.2 hvw).ne']
    ring
  refine convexOn_of_slope_mono_adjacent (convex_Icc a d) fun {x y z} hx hz hxy hyz => ?_
  -- If all three points lie in `[a, c]` or in `[b, d]`, apply `hl` or `hr` directly.
  rcases le_or_gt z c with hzc | hcz
  · exact hl.slope_mono_adjacent ⟨hx.1, (hxy.trans hyz).le.trans hzc⟩
      ⟨hx.1.trans (hxy.trans hyz).le, hzc⟩ hxy hyz
  rcases le_or_gt b x with hbx | hxb
  · exact hr.slope_mono_adjacent ⟨hbx, hx.2⟩ ⟨hbx.trans (hxy.trans hyz).le, hz.2⟩ hxy hyz
  -- Otherwise `x < b < c < z`; split on the position of `y` relative to `b` and `c`.
  have hx_l : x ∈ Icc a c := ⟨hx.1, (hxb.trans hbc).le⟩
  have hz_r : z ∈ Icc b d := ⟨(hbc.trans hcz).le, hz.2⟩
  rcases lt_trichotomy y b with hyb | rfl | hby
  · have h₁ : (f y - f x) / (y - x) ≤ (f c - f y) / (c - y) :=
      hl.slope_mono_adjacent hx_l ⟨hab.trans hbc.le, le_rfl⟩ hxy (hyb.trans hbc)
    have h₂ : (f c - f y) / (c - y) ≤ (f z - f c) / (z - c) :=
      (hl.secant_mono_aux3 ⟨hx.1.trans hxy.le, (hyb.trans hbc).le⟩
        ⟨hab.trans hbc.le, le_rfl⟩ hyb hbc).trans
        (hr.slope_mono_adjacent ⟨le_rfl, hbc.le.trans hcd⟩ hz_r hbc hcz)
    refine le_of_mul_le_mul_right ?_ (sub_pos.2 hyz)
    rw [avg (hyb.trans hbc) hcz]
    linarith [mul_le_mul_of_nonneg_right (h₁.trans h₂) (sub_pos.2 hcz).le,
      mul_le_mul_of_nonneg_right h₁ (sub_pos.2 (hyb.trans hbc)).le]
  · exact (hl.slope_mono_adjacent hx_l ⟨hab.trans hbc.le, le_rfl⟩ hxb hbc).trans
      (hr.secant_mono_aux2 ⟨le_rfl, hbc.le.trans hcd⟩ hz_r hbc hcz)
  · rcases lt_trichotomy y c with hyc | rfl | hcy
    · exact (hl.secant_mono_aux3 hx_l ⟨hab.trans hby.le, hyc.le⟩ hxb hby).trans
        (hr.slope_mono_adjacent ⟨le_rfl, hbc.le.trans hcd⟩ hz_r hby hyz)
    · exact (hl.secant_mono_aux3 hx_l ⟨hab.trans hbc.le, le_rfl⟩ hxb hbc).trans
        (hr.slope_mono_adjacent ⟨le_rfl, hbc.le.trans hcd⟩ hz_r hbc hcz)
    · have h₁ : (f y - f b) / (y - b) ≤ (f z - f y) / (z - y) :=
        hr.slope_mono_adjacent ⟨le_rfl, hbc.le.trans hcd⟩ hz_r hby hyz
      have h₂ : (f b - f x) / (b - x) ≤ (f y - f b) / (y - b) :=
        (hl.slope_mono_adjacent hx_l ⟨hab.trans hbc.le, le_rfl⟩ hxb hbc).trans
          (hr.secant_mono_aux2 ⟨le_rfl, hbc.le.trans hcd⟩ ⟨hby.le, hyz.le.trans hz.2⟩ hbc hcy)
      refine le_of_mul_le_mul_right ?_ (sub_pos.2 hxy)
      rw [avg hxb hby]
      linarith [mul_le_mul_of_nonneg_right (h₂.trans h₁) (sub_pos.2 hxb).le,
        mul_le_mul_of_nonneg_right h₁ (sub_pos.2 hby).le]

/-- Gluing concave functions across a nondegenerate overlap: if `a ≤ b < c ≤ d` and `f : 𝕜 → 𝕜` is
concave on `[a, c]` and on `[b, d]`, then `f` is concave on `[a, d]`. -/
theorem concaveOn_Icc_of_overlap {a b c d : 𝕜} {f : 𝕜 → 𝕜}
    (hab : a ≤ b) (hbc : b < c) (hcd : c ≤ d)
    (hl : ConcaveOn 𝕜 (Icc a c) f) (hr : ConcaveOn 𝕜 (Icc b d) f) :
    ConcaveOn 𝕜 (Icc a d) f := by
  rw [← neg_convexOn_iff]
  exact convexOn_Icc_of_overlap hab hbc hcd hl.neg hr.neg

/-- Subdivision criterion for convexity on an interval: given a strictly increasing subdivision
`t : Fin (m + 2) → 𝕜`, if `f : 𝕜 → 𝕜` is convex on `[t 0, t 1]` and on every two-step interval
`[t k, t (k + 2)]` across each interior subdivision point, then `f` is convex on
`[t 0, t (Fin.last (m + 1))]`. -/
theorem convexOn_Icc_of_subdivision {m : ℕ} {t : Fin (m + 2) → 𝕜} {f : 𝕜 → 𝕜}
    (ht : StrictMono t) (h0 : ConvexOn 𝕜 (Icc (t 0) (t 1)) f)
    (hstep : ∀ k : Fin m, ConvexOn 𝕜 (Icc (t k.castSucc.castSucc) (t k.succ.succ)) f) :
    ConvexOn 𝕜 (Icc (t 0) (t (Fin.last (m + 1)))) f := by
  induction m with
  | zero => exact h0
  | succ n ih =>
    have hleft : ConvexOn 𝕜 (Icc (t 0) (t (Fin.last (n + 1)).castSucc)) f :=
      ih (ht.comp fun _ _ h => Fin.castSucc_lt_castSucc_iff.mpr h) h0
        fun k => hstep k.castSucc
    have hright : ConvexOn 𝕜 (Icc (t (Fin.last n).castSucc.castSucc) (t (Fin.last (n + 2)))) f := by
      simpa [Fin.succ_last] using hstep (Fin.last n)
    exact convexOn_Icc_of_overlap
      (ht.monotone (Fin.zero_le _))
      (ht (by simp [Fin.lt_def]))
      (ht.monotone (Fin.le_last _))
      hleft hright

/-- Subdivision criterion for concavity on an interval: given a strictly increasing subdivision
`t : Fin (m + 2) → 𝕜`, if `f : 𝕜 → 𝕜` is concave on `[t 0, t 1]` and on every two-step interval
`[t k, t (k + 2)]` across each interior subdivision point, then `f` is concave on
`[t 0, t (Fin.last (m + 1))]`. -/
theorem concaveOn_Icc_of_subdivision {m : ℕ} {t : Fin (m + 2) → 𝕜} {f : 𝕜 → 𝕜}
    (ht : StrictMono t) (h0 : ConcaveOn 𝕜 (Icc (t 0) (t 1)) f)
    (hstep : ∀ k : Fin m, ConcaveOn 𝕜 (Icc (t k.castSucc.castSucc) (t k.succ.succ)) f) :
    ConcaveOn 𝕜 (Icc (t 0) (t (Fin.last (m + 1)))) f := by
  rw [← neg_convexOn_iff]
  exact convexOn_Icc_of_subdivision ht h0.neg fun k => (hstep k).neg

end Subdivision

end TauCeti
