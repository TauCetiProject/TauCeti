/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Slope
import Mathlib.Topology.Algebra.Affine
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Gluing convex functions across points and overlapping intervals

A real function which is convex on `(-∞, a]` and on `[a, ∞)` is convex on all of `ℝ` as soon as
its left derivative at `a` is at most its right derivative there. This is the standard way to
prove convexity of a function given by different formulas on the two sides of a point, for
instance a function of `|x|`, and complements the monotone and antitone gluing lemmas of
`Mathlib.Analysis.Convex.Piecewise`.

Over any linearly ordered field, convexity (or concavity) on `[a, c]` and `[b, d]` with `b < c`
glues to `[a, d]`, and iterating across a strictly increasing subdivision glues two-step intervals
`[t k, t (k + 2)]`. On compact real intervals and convex sets in real topological vector spaces,
this upgrades local convexity in relative neighbourhoods to global convexity.

## Main statements

* `TauCeti.convexOn_univ_of_convexOn_Iic_Ici`: a function convex on both sides of `a` whose
  one-sided derivatives at `a` satisfy `f'(a⁻) ≤ f'(a⁺)` is convex on `ℝ`.
* `TauCeti.convexOn_Icc_of_overlap`, `TauCeti.concaveOn_Icc_of_overlap`,
  `TauCeti.convexOn_Icc_of_subdivision`, `TauCeti.concaveOn_Icc_of_subdivision`.
* `TauCeti.convexOn_Icc_of_local`, `TauCeti.concaveOn_Icc_of_local`,
  `TauCeti.convexOn_of_local`, `TauCeti.concaveOn_of_local`.
-/

public section

namespace TauCeti

open Set Filter Topology

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

/-- Gluing convexity across a nondegenerate overlap: if `b < c` and `f : 𝕜 → 𝕜` is convex on
`[a, c]` and on `[b, d]`, then `f` is convex on `[a, d]`. -/
theorem convexOn_Icc_of_overlap {a b c d : 𝕜} {f : 𝕜 → 𝕜} (hbc : b < c)
    (hl : ConvexOn 𝕜 (Icc a c) f) (hr : ConvexOn 𝕜 (Icc b d) f) :
    ConvexOn 𝕜 (Icc a d) f := by
  have avg {u v w : 𝕜} (huv : u < v) (hvw : v < w) : (f w - f u) / (w - u) * (w - u) =
      (f v - f u) / (v - u) * (v - u) + (f w - f v) / (w - v) * (w - v) := by
    rw [div_mul_cancel₀ _ (sub_pos.2 (huv.trans hvw)).ne', div_mul_cancel₀ _ (sub_pos.2 huv).ne',
      div_mul_cancel₀ _ (sub_pos.2 hvw).ne']; ring
  refine convexOn_of_slope_mono_adjacent (convex_Icc a d) fun {x y z} hx hz hxy hyz => ?_
  rcases le_or_gt z c with hzc | hcz
  · exact hl.slope_mono_adjacent ⟨hx.1, (hxy.trans hyz).le.trans hzc⟩
      ⟨hx.1.trans (hxy.trans hyz).le, hzc⟩ hxy hyz
  rcases le_or_gt b x with hbx | hxb
  · exact hr.slope_mono_adjacent ⟨hbx, hx.2⟩ ⟨hbx.trans (hxy.trans hyz).le, hz.2⟩ hxy hyz
  have hxl : x ∈ Icc a c := ⟨hx.1, (hxb.trans hbc).le⟩
  have hzr : z ∈ Icc b d := ⟨(hbc.trans hcz).le, hz.2⟩
  have hcl : c ∈ Icc a c := ⟨hx.1.trans (hxb.trans hbc).le, le_rfl⟩
  have hbr : b ∈ Icc b d := ⟨le_rfl, (hbc.trans hcz).le.trans hz.2⟩
  rcases lt_trichotomy y b with hyb | rfl | hby
  · have h₁ := hl.slope_mono_adjacent hxl hcl hxy (hyb.trans hbc)
    have h₂ := (hl.secant_mono_aux3 ⟨hx.1.trans hxy.le, (hyb.trans hbc).le⟩ hcl hyb hbc).trans
      (hr.slope_mono_adjacent hbr hzr hbc hcz)
    refine le_of_mul_le_mul_right ?_ (sub_pos.2 hyz); rw [avg (hyb.trans hbc) hcz]
    linarith [mul_le_mul_of_nonneg_right (h₁.trans h₂) (sub_pos.2 hcz).le,
      mul_le_mul_of_nonneg_right h₁ (sub_pos.2 (hyb.trans hbc)).le]
  · exact (hl.slope_mono_adjacent hxl hcl hxb hbc).trans (hr.secant_mono_aux2 hbr hzr hbc hcz)
  · rcases le_or_gt y c with hyc | hcy
    · exact (hl.secant_mono_aux3 hxl ⟨hx.1.trans hxy.le, hyc⟩ hxb hby).trans
        (hr.slope_mono_adjacent hbr hzr hby hyz)
    · have h₁ := hr.slope_mono_adjacent hbr hzr hby hyz
      have h₂ := (hl.slope_mono_adjacent hxl hcl hxb hbc).trans
        (hr.secant_mono_aux2 hbr ⟨hby.le, hyz.le.trans hz.2⟩ hbc hcy)
      refine le_of_mul_le_mul_right ?_ (sub_pos.2 hxy); rw [avg hxb hby]
      linarith [mul_le_mul_of_nonneg_right (h₂.trans h₁) (sub_pos.2 hxb).le,
        mul_le_mul_of_nonneg_right h₁ (sub_pos.2 hby).le]

/-- Gluing concavity across a nondegenerate overlap: if `b < c` and `f : 𝕜 → 𝕜` is concave on
`[a, c]` and on `[b, d]`, then `f` is concave on `[a, d]`. -/
theorem concaveOn_Icc_of_overlap {a b c d : 𝕜} {f : 𝕜 → 𝕜} (hbc : b < c)
    (hl : ConcaveOn 𝕜 (Icc a c) f) (hr : ConcaveOn 𝕜 (Icc b d) f) :
    ConcaveOn 𝕜 (Icc a d) f :=
  neg_convexOn_iff.mp (convexOn_Icc_of_overlap hbc hl.neg hr.neg)

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
    exact convexOn_Icc_of_overlap (b := t (Fin.last n).castSucc.castSucc)
      (c := t (Fin.last (n + 1)).castSucc) (ht (by simp [Fin.lt_def]))
      (ih (ht.comp fun _ _ h => Fin.castSucc_lt_castSucc_iff.mpr h) h0 fun k => hstep k.castSucc)
      (by simpa [Fin.succ_last] using hstep (Fin.last n))

/-- Subdivision criterion for concavity on an interval: given a strictly increasing subdivision
`t : Fin (m + 2) → 𝕜`, if `f : 𝕜 → 𝕜` is concave on `[t 0, t 1]` and on every two-step interval
`[t k, t (k + 2)]` across each interior subdivision point, then `f` is concave on
`[t 0, t (Fin.last (m + 1))]`. -/
theorem concaveOn_Icc_of_subdivision {m : ℕ} {t : Fin (m + 2) → 𝕜} {f : 𝕜 → 𝕜}
    (ht : StrictMono t) (h0 : ConcaveOn 𝕜 (Icc (t 0) (t 1)) f)
    (hstep : ∀ k : Fin m, ConcaveOn 𝕜 (Icc (t k.castSucc.castSucc) (t k.succ.succ)) f) :
    ConcaveOn 𝕜 (Icc (t 0) (t (Fin.last (m + 1)))) f :=
  neg_convexOn_iff.mp (convexOn_Icc_of_subdivision ht h0.neg fun k => (hstep k).neg)

end Subdivision

/-- Local-to-global convexity on a compact interval: if every point `x ∈ [a, b]` admits a relative
neighbourhood `V ∈ 𝓝[[a, b]] x` on which `f : ℝ → ℝ` is convex, then `f` is convex on `[a, b]`. -/
theorem convexOn_Icc_of_local {a b : ℝ} {f : ℝ → ℝ}
    (h : ∀ x ∈ Icc a b, ∃ V ∈ 𝓝[Icc a b] x, ConvexOn ℝ V f) :
    ConvexOn ℝ (Icc a b) f := by
  rcases le_or_gt b a with hba | hab
  · refine ⟨convex_Icc a b, fun x hx y hy u v _ _ huv => ?_⟩
    obtain rfl : x = y := le_antisymm (hx.2.trans (hba.trans hy.1)) (hy.2.trans (hba.trans hx.1))
    rw [← add_smul, ← add_smul, huv, one_smul, one_smul]
  · have hL : 0 < b - a := sub_pos.mpr hab
    choose V hVnhds hVconv using fun x : Icc a b => h x.1 x.2
    choose U hUo hxU hUV using fun x : Icc a b => mem_nhdsWithin.mp (hVnhds x)
    obtain ⟨δ, hδ_pos, hball⟩ := lebesgue_number_lemma_of_metric isCompact_Icc hUo
      fun s hs => mem_iUnion.mpr ⟨⟨s, hs⟩, hxU ⟨s, hs⟩⟩
    let N : ℕ := ⌊2 * (b - a) / δ⌋₊ + 1
    have hN_pos : (0 : ℝ) < (N : ℝ) + 2 := by positivity
    have hstep_lt : 2 * (b - a) / ((N : ℝ) + 2) < δ := (div_lt_iff₀ hN_pos).mpr <| by
      linarith [(div_lt_iff₀ hδ_pos).mp (by
        dsimp [N]; push_cast; linarith [Nat.lt_floor_add_one (2 * (b - a) / δ)] :
          2 * (b - a) / δ < (N : ℝ) + 2)]
    let t (j : Fin (N + 3)) : ℝ := a + (j.val : ℝ) / ((N : ℝ) + 2) * (b - a)
    have ht_mono : StrictMono t := fun _ _ hij => add_lt_add_right
      (mul_lt_mul_of_pos_right (div_lt_div_of_pos_right (Nat.cast_lt.mpr hij) hN_pos) hL) a
    have ht0 : t 0 = a := by simp [t]
    have ht_last : t (Fin.last (N + 2)) = b := by
      simp only [t, Fin.val_last, Nat.cast_add, Nat.cast_ofNat, div_self hN_pos.ne']; ring
    have hsub {u v : ℝ} (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b)
        (hlen : v - u ≤ 2 * (b - a) / ((N : ℝ) + 2)) : ConvexOn ℝ (Icc u v) f := by
      obtain ⟨idx, hidx⟩ := hball u ⟨hau, huv.trans hvb⟩
      refine (hVconv idx).subset (fun s hs => hUV idx ⟨hidx ?_, ⟨hau.trans hs.1, hs.2.trans hvb⟩⟩)
        (convex_Icc u v)
      rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hs.1)]
      exact (sub_le_sub_right hs.2 u).trans_lt (hlen.trans_lt hstep_lt)
    rw [← ht0, ← ht_last]
    refine convexOn_Icc_of_subdivision ht_mono
      (hsub (ht0 ▸ le_rfl) (ht_mono.monotone (Fin.zero_le _))
        (ht_last ▸ ht_mono.monotone (Fin.le_last _)) ?_)
      fun k => hsub (ht0 ▸ ht_mono.monotone (Fin.zero_le _))
        (ht_mono.monotone (by simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ]; omega))
        (ht_last ▸ ht_mono.monotone (Fin.le_last _)) (le_of_eq
          (by simp only [t, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]; ring))
    simp only [t, Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one]
    exact (le_of_eq (by ring : a + 1 / ((N : ℝ) + 2) * (b - a) -
      (a + 0 / ((N : ℝ) + 2) * (b - a)) = (b - a) / ((N : ℝ) + 2))).trans
      (div_le_div_of_nonneg_right (by linarith) hN_pos.le)

/-- Local-to-global concavity on a compact interval: if every point `x ∈ [a, b]` admits a relative
neighbourhood `V ∈ 𝓝[[a, b]] x` on which `f : ℝ → ℝ` is concave, then `f` is concave on `[a, b]`. -/
theorem concaveOn_Icc_of_local {a b : ℝ} {f : ℝ → ℝ}
    (h : ∀ x ∈ Icc a b, ∃ V ∈ 𝓝[Icc a b] x, ConcaveOn ℝ V f) :
    ConcaveOn ℝ (Icc a b) f :=
  neg_convexOn_iff.mp (convexOn_Icc_of_local fun x hx =>
    let ⟨V, hV, hVc⟩ := h x hx; ⟨V, hV, hVc.neg⟩)

/-- Local-to-global convexity on a convex set: if every point `x ∈ s` admits a relative
neighbourhood `V ∈ 𝓝[s] x` on which `f : E → ℝ` is convex, then `f` is convex on `s`. -/
theorem convexOn_of_local {E : Type*} [AddCommGroup E] [TopologicalSpace E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {s : Set E} {f : E → ℝ} (hs : Convex ℝ s)
    (h : ∀ x ∈ s, ∃ V ∈ 𝓝[s] x, ConvexOn ℝ V f) : ConvexOn ℝ s f := by
  refine ⟨hs, fun x hx y hy a b ha hb hab => ?_⟩
  let γ : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y
  have hγ_mem : MapsTo γ (Icc (0 : ℝ) 1) s := fun _ ht => hs.lineMap_mem hx hy ht
  have hIcc : ConvexOn ℝ (Icc (0 : ℝ) 1) (f ∘ γ) := convexOn_Icc_of_local fun t ht =>
    let ⟨V, hV, hVc⟩ := h (γ t) (hγ_mem ht)
    ⟨γ ⁻¹' V, (AffineMap.lineMap_continuous.continuousWithinAt.tendsto_nhdsWithin hγ_mem) hV,
      hVc.comp_affineMap γ⟩
  simpa [γ, AffineMap.lineMap_apply_module, (by linarith : 1 - b = a)] using
    hIcc.2 (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one) ha hb hab

/-- Local-to-global concavity on a convex set: if every point `x ∈ s` admits a relative
neighbourhood `V ∈ 𝓝[s] x` on which `f : E → ℝ` is concave, then `f` is concave on `s`. -/
theorem concaveOn_of_local {E : Type*} [AddCommGroup E] [TopologicalSpace E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {s : Set E} {f : E → ℝ} (hs : Convex ℝ s)
    (h : ∀ x ∈ s, ∃ V ∈ 𝓝[s] x, ConcaveOn ℝ V f) : ConcaveOn ℝ s f :=
  neg_convexOn_iff.mp (convexOn_of_local hs fun x hx =>
    let ⟨V, hV, hVc⟩ := h x hx; ⟨V, hV, hVc.neg⟩)

end TauCeti
