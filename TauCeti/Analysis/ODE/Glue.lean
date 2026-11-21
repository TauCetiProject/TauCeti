/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Gluing one-sided derivatives on adjacent intervals

Two functions with derivatives `f'` and `g'` within adjacent closed intervals `[l, m]` and `[m, u]`
glue to a function with derivative `t ↦ if t ≤ m then f' t else g' t` within `[l, u]`, once the
functions and their derivatives agree at the common end `m`. For solutions of an ODE
`x' = v t (x t)`, take `f' t = v t (f t)` and `g' t = v t (g t)`: the derivatives agree at `m` as
soon as the solutions do, so two solutions agreeing at `m` glue to a solution. Similarly, an
autonomous integral curve on `[a, s]` can be concatenated with a translated integral curve on
`[0, b)` at the matching time `s`.

## Main results

* `TauCeti.hasDerivWithinAt_Icc_ite`: the glued function `t ↦ if t ≤ m then f t else g t` has the
  glued derivative within `[l, u]`.
* `TauCeti.hasDerivAt_Ioo_ite_ite`: three pieces on `[l, a]`, `[a, b]` and `[b, u]`, where `l` and
  `u` can be taken arbitrarily close to `p` and `q`, glue to a function with a two-sided
  derivative on `(p, q)`.
* `TauCeti.hasDerivWithinAt_ite_Ico`: concatenation of an integral curve on `[a, s]` with a
  translated integral curve on `[0, b)` into an integral curve on `[a, s + b)`.
-/

public section

open Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Two functions with derivatives `f'` and `g'` within adjacent closed intervals `[l, m]` and
`[m, u]`, which agree at the common end `m` together with their derivatives, glue to a function
with derivative `t ↦ if t ≤ m then f' t else g' t` within `[l, u]`. -/
theorem hasDerivWithinAt_Icc_ite {f g f' g' : ℝ → E} {l m u : ℝ} (hlm : l ≤ m) (hmu : m ≤ u)
    (hf : ∀ t ∈ Icc l m, HasDerivWithinAt f (f' t) (Icc l m) t)
    (hg : ∀ t ∈ Icc m u, HasDerivWithinAt g (g' t) (Icc m u) t) (hfg : f m = g m)
    (hfg' : f' m = g' m) :
    ∀ t ∈ Icc l u, HasDerivWithinAt (fun t ↦ if t ≤ m then f t else g t)
      (if t ≤ m then f' t else g' t) (Icc l u) t := by
  intro t ht
  have hhf : EqOn (fun t ↦ if t ≤ m then f t else g t) f (Icc l m) := fun s hs ↦ ite_eq_left hs.2
  have hhg : EqOn (fun t ↦ if t ≤ m then f t else g t) g (Icc m u) := fun s hs ↦ by
    rcases hs.1.eq_or_lt with rfl | hs'
    · exact (ite_eq_left le_rfl).trans hfg
    · exact ite_eq_right (not_le.2 hs')
  rw [← Icc_union_Icc_eq_Icc hlm hmu]
  refine HasDerivWithinAt.union ?_ ?_
  · by_cases htm : t ≤ m
    · rw [ite_eq_left htm]
      exact (hf t ⟨ht.1, htm⟩).congr hhf (hhf ⟨ht.1, htm⟩)
    · refine hasDerivWithinAt_iff_hasFDerivWithinAt.2 (HasFDerivWithinAt.of_notMem_closure ?_)
      rw [isClosed_Icc.closure_eq]
      exact fun h ↦ htm h.2
  · by_cases htm : m ≤ t
    · have hg' : (if t ≤ m then f' t else g' t) = g' t := by
        rcases htm.eq_or_lt with rfl | htm'
        · exact (ite_eq_left le_rfl).trans hfg'
        · exact ite_eq_right (not_le.2 htm')
      rw [hg']
      exact (hg t ⟨htm, ht.2⟩).congr hhg (hhg ⟨htm, ht.2⟩)
    · refine hasDerivWithinAt_iff_hasFDerivWithinAt.2 (HasFDerivWithinAt.of_notMem_closure ?_)
      rw [isClosed_Icc.closure_eq]
      exact fun h ↦ htm h.1

/-- Three functions with derivatives within `[l, a]`, `[a, b]` and `[b, u]`, for every `l ∈ (p, a)`
and `u ∈ (b, q)`, which agree at `a` and at `b` together with their derivatives, glue to a function
with a two-sided derivative at every point of `(p, q)`. -/
theorem hasDerivAt_Ioo_ite_ite {f g h f' g' h' : ℝ → E} {p q a b : ℝ} (hpa : p < a)
    (hab : a ≤ b) (hbq : b < q)
    (hf : ∀ l ∈ Ioo p a, ∀ t ∈ Icc l a, HasDerivWithinAt f (f' t) (Icc l a) t)
    (hg : ∀ t ∈ Icc a b, HasDerivWithinAt g (g' t) (Icc a b) t)
    (hh : ∀ u ∈ Ioo b q, ∀ t ∈ Icc b u, HasDerivWithinAt h (h' t) (Icc b u) t)
    (hfg : f a = g a) (hfg' : f' a = g' a) (hgh : g b = h b) (hgh' : g' b = h' b) :
    ∀ t ∈ Ioo p q, HasDerivAt (fun t ↦ if t ≤ b then (if t ≤ a then f t else g t) else h t)
      (if t ≤ b then (if t ≤ a then f' t else g' t) else h' t) t := by
  intro t ht
  set l := (p + min t a) / 2
  set u := (max t b + q) / 2
  have htl := lt_min ht.1 hpa
  have htq := max_lt ht.2 hbq
  have hl : l ∈ Ioo p a := ⟨by simp only [l]; linarith, by
    have := min_le_right t a; simp only [l]; linarith⟩
  have hlt : l < t := by have := min_le_left t a; simp only [l]; linarith
  have hu : u ∈ Ioo b q := ⟨by have := le_max_right t b; simp only [u]; linarith, by
    simp only [u]; linarith⟩
  have htu : t < u := by have := le_max_left t b; simp only [u]; linarith
  -- At `b` the first two pieces glued agree with the third, also when `a = b`.
  have hb : ∀ {F G H : ℝ → E}, F a = G a → G b = H b → (if b ≤ a then F b else G b) = H b :=
    fun hFG hGH ↦ by
      split_ifs with hba
      · obtain rfl := le_antisymm hba hab
        rw [hFG, hGH]
      · exact hGH
  exact (hasDerivWithinAt_Icc_ite (hl.2.le.trans hab) hu.1.le
    (hasDerivWithinAt_Icc_ite hl.2.le hab (hf l hl) hg hfg hfg') (hh u hu) (hb hfg hgh)
    (hb hfg' hgh') t ⟨hlt.le, htu.le⟩).hasDerivAt (Icc_mem_nhds hlt htu)

/-- Concatenating an integral curve `γ₁` of `X` on `[a, s]` with an integral curve `γ₂` of `X` on
`[0, b)` starting at `γ₂ 0 = γ₁ s` yields an integral curve of `X` on `[a, s + b)`. -/
theorem hasDerivWithinAt_ite_Ico (X : E → E) {γ₁ γ₂ : ℝ → E} {a s b u : ℝ}
    (h0₂ : γ₂ 0 = γ₁ s)
    (hγ₁' : ∀ t ∈ Icc a s, HasDerivWithinAt γ₁ (X (γ₁ t)) (Icc a s) t)
    (hγ₂' : ∀ t ∈ Ico 0 b, HasDerivWithinAt γ₂ (X (γ₂ t)) (Ico 0 b) t)
    (hu : u ∈ Ico a (s + b)) :
    HasDerivWithinAt (fun r ↦ if r ≤ s then γ₁ r else γ₂ (r - s))
      (X ((fun r ↦ if r ≤ s then γ₁ r else γ₂ (r - s)) u)) (Ico a (s + b)) u := by
  set γ : ℝ → E := fun r ↦ if r ≤ s then γ₁ r else γ₂ (r - s)
  rcases lt_trichotomy u s with hus | rfl | hsu
  · have hγu : γ u = γ₁ u := ite_eq_left hus.le
    have hd := (hγ₁' u ⟨hu.1, hus.le⟩).mono_of_mem_nhdsWithin (s := Ico a (s + b))
      (mem_nhdsWithin.mpr ⟨Iio s, isOpen_Iio, hus, fun _ hr ↦ ⟨hr.2.1, hr.1.le⟩⟩)
    exact (hγu ▸ hd).congr_of_eventuallyEq
      (Filter.mem_of_superset (nhdsWithin_le_nhds (Iio_mem_nhds hus))
        fun _ hr ↦ ite_eq_left (mem_Iio.mp hr).le) hγu
  · have hγs : γ u = γ₁ u := ite_eq_left le_rfl
    have hb : 0 < b := by linarith [hu.2]
    have hleft : HasDerivWithinAt γ (X (γ u)) (Icc a u) u :=
      (hγs ▸ hγ₁' u ⟨hu.1, le_rfl⟩).congr (fun _ hr ↦ ite_eq_left hr.2) hγs
    have hright : HasDerivWithinAt γ (X (γ u)) (Ico u (u + b)) u := by
      have hd₂ := HasDerivWithinAt.scomp_of_eq (s := Ico u (u + b)) u
        (hγ₂' 0 ⟨le_rfl, hb⟩) ((hasDerivAt_id u).sub_const u).hasDerivWithinAt
        (fun _ hr ↦ ⟨sub_nonneg.mpr hr.1, sub_lt_iff_lt_add'.mpr hr.2⟩) (sub_self u).symm
      simp only [Function.comp_def, id_eq, h0₂, one_smul, ← hγs] at hd₂
      refine hd₂.congr (fun r hr ↦ ?_) (by simp [γ, h0₂])
      rcases hr.1.eq_or_lt with rfl | hsr
      · simp [γ, h0₂]
      · exact ite_eq_right (not_le_of_gt hsr)
    have hboth : HasDerivWithinAt γ (X (γ u)) (Icc a u ∪ Ico u (u + b)) u :=
      hleft.union hright
    rwa [Icc_union_Ico_eq_Ico hu.1 hu.2] at hboth
  · have hγu : γ u = γ₂ (u - s) := ite_eq_right (not_le_of_gt hsu)
    have hd₂ := ((hγ₂' (u - s) ⟨by linarith, by linarith [hu.2]⟩).hasDerivAt
      (Ico_mem_nhds (by linarith) (by linarith [hu.2]))).comp_sub_const u s
    exact (hγu ▸ hd₂.hasDerivWithinAt).congr_of_eventuallyEq
      (Filter.mem_of_superset (nhdsWithin_le_nhds (Ioi_mem_nhds hsu))
        fun _ hr ↦ ite_eq_right (not_le_of_gt (mem_Ioi.mp hr))) hγu

end TauCeti
