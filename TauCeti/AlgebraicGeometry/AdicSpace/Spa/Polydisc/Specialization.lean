/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Classification

import TauCeti.Analysis.Normed.Field.Basic
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PowerBounded

/-!
# Closures of the points `η_{a,r}` and `η_{a,r±}` of the closed unit disc

Let `K` be an algebraically closed complete nontrivially normed nonarchimedean field and
`X = Spa (K⟨T⟩, K⟨T⟩°)` the closed unit disc. Wedhorn's Example 7.57 describes the closures of
its points: the closure of a point `η_{a,r}` of type (2) consists of `η_{a,r}` and the points of
type (5) around it, and the points of types (3) and (5) are closed. This file proves these
statements.

A point `z` lies in the closure of `η_{a,r}` exactly when it is

* `η_{a,r}` itself,
* `η_{a,r⁺}`, the point just above `η_{a,r}` on the ray towards the Gauss point, defined only
  when `r < 1`, or
* `η_{b,r⁻}` for some `b ∈ D(a, r)`, the point just below `η_{a,r}` on the ray towards `b`,

where the last two cases occur only when `r = ‖c‖` for some `c ∈ K`. So `η_{a,r}` is closed
exactly when `r` is not the norm of an element of `K`, and then `η_{a,r⁻} = η_{a,r}` and, when
`r < 1`, also `η_{a,r⁺} = η_{a,r}`. The points `η_{a,r⁺}` and `η_{a,r⁻}` are always closed. That
the classical points of type (1) are closed is
`TauCeti.ValuationSpectrum.isClosed_singleton_classicalPoint`.

The proof transfers comparisons along specializations. If `x ⤳ z`, every basic open
`{v : v(f) ≤ v(g) ≠ 0}` containing `z` contains `x`. So a strict inequality `x(g) < x(f)` gives
`z(g) < z(f)` as soon as one side is nonzero at `z`. Applied to `f` or `g` the linear polynomial
`T - a` and the other a constant, this says that `z(T - a)` keeps every strict comparison of
`x(T - a)` with the constants. Only the comparisons with the constants of norm `r` can change, and
the characterisations `TauCeti.ValuationSpectrum.eq_discPoint_iff`,
`TauCeti.ValuationSpectrum.eq_discPointAbove_iff` and
`TauCeti.ValuationSpectrum.eq_discPointBelow_iff` identify `z` in each case.

## Main results

* `TauCeti.ValuationSpectrum.discPoint_specializes_iff`: the specializations of `η_{a,r}` are
  `η_{a,r}`, and, when `r` is the norm of an element of `K`, the points `η_{b,r⁻}` with
  `‖b - a‖ ≤ r` and, when moreover `r < 1`, `η_{a,r⁺}`.
* `TauCeti.ValuationSpectrum.isClosed_singleton_discPoint_iff`: `η_{a,r}` is a closed point
  exactly when `r` is not the norm of an element of `K`, that is, exactly when it is of type (3).
* `TauCeti.ValuationSpectrum.discPointAbove_eq_discPoint_iff` and
  `TauCeti.ValuationSpectrum.discPointBelow_eq_discPoint_iff`: `η_{a,r⁺} = η_{a,r}` (for `r < 1`),
  respectively `η_{a,r⁻} = η_{a,r}`, exactly when `r` is not the norm of an element of `K`.
* `TauCeti.ValuationSpectrum.isClosed_singleton_discPointAbove` and
  `TauCeti.ValuationSpectrum.isClosed_singleton_discPointBelow`: the points `η_{a,r⁺}` (for
  `r < 1`) and `η_{a,r⁻}`, in particular the points of type (5), are closed.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Example 7.57.
* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), Example 2.20, for the points of
  type (5) and their position in the disc.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber

variable {K : Type*} [NontriviallyNormedField K] [NonarchimedeanRing K] [IsUltrametricDist K]
  {r : ℝ}

local notation "𝒯" => weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set K))
  isWeightFamily_one_weight
local notation "T" => weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0
local notation "C" => weightedC (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight

/-! ### Transferring comparisons along a specialization -/

omit [IsUltrametricDist K] in
/-- **Comparisons at a specialization hold at the generization.** If `x ⤳ z`, then
`z(f) ≤ z(g) ≠ 0` implies `x(f) ≤ x(g)`: the basic open `{v : v(f) ≤ v(g) ≠ 0}` contains `z`,
hence `x`. -/
private theorem valuation_le_of_specializes {x z : closedPolydisc 1 K} (h : x ⤳ z) {f g : 𝒯}
    (hfg : z.1.valuation f ≤ z.1.valuation g) (hg : z.1.valuation g ≠ 0) :
    x.1.valuation f ≤ x.1.valuation g := by
  have hz : z.1 ∈ basicOpen f g := (mem_basicOpen_iff _ _ _).mpr
    ⟨(valuation_le_iff _ _ _).mp hfg, fun h0 ↦ hg (by simpa using (valuation_le_iff _ _ _).mpr h0)⟩
  exact (valuation_le_iff _ _ _).mpr ((mem_basicOpen_iff _ _ _).mp
    (((subtype_specializes_iff x z).mp h).mem_open (isOpen_basicOpen f g) hz)).1

omit [IsUltrametricDist K] in
/-- **Strict comparisons at a generization hold at a specialization**, provided one side is
nonzero there: if `x ⤳ z` and `x(g) < x(f)`, then `z(g) < z(f)` unless `z(f) = z(g) = 0`. -/
private theorem valuation_lt_of_specializes {x z : closedPolydisc 1 K} (h : x ⤳ z) {f g : 𝒯}
    (hx : x.1.valuation g < x.1.valuation f)
    (hz : z.1.valuation g ≠ 0 ∨ z.1.valuation f ≠ 0) : z.1.valuation g < z.1.valuation f := by
  refine lt_of_not_ge fun hle ↦ hx.not_ge (valuation_le_of_specializes h hle ?_)
  rcases hz with hz | hz
  · exact hz
  · exact fun h0 ↦ hz (le_zero_iff.mp (h0 ▸ hle))

/-- If `x(T - a)` lies strictly above the constants `c` with `P c`, among them a nonzero one, and
strictly below the constants with `Q c`, then so does `z(T - a)` at every specialization `z` of
`x`. -/
private theorem forall_lt_and_forall_gt_of_specializes {x z : closedPolydisc 1 K} (h : x ⤳ z)
    {a : K} (P Q : K → Prop) (hP : ∃ d ≠ 0, P d)
    (hx : (∀ c : K, P c → x.1.valuation (C c) < x.1.valuation (T - C a)) ∧
      ∀ c : K, Q c → x.1.valuation (T - C a) < x.1.valuation (C c)) :
    (∀ c : K, P c → z.1.valuation (C c) < z.1.valuation (T - C a)) ∧
      ∀ c : K, Q c → z.1.valuation (T - C a) < z.1.valuation (C c) := by
  obtain ⟨d, hd, hPd⟩ := hP
  have hz₀ : z.1.valuation (T - C a) ≠ 0 :=
    (zero_le.trans_lt (valuation_lt_of_specializes h (hx.1 d hPd)
      (Or.inl ((closedPolydisc_valuation_weightedC_eq_zero_iff z d).not.mpr hd)))).ne'
  exact ⟨fun c hc ↦ valuation_lt_of_specializes h (hx.1 c hc) (Or.inr hz₀),
    fun c hc ↦ valuation_lt_of_specializes h (hx.2 c hc) (Or.inl hz₀)⟩

variable [CompleteSpace K] [IsAlgClosed K]

/-! ### The closure of `η_{a,r}` -/

/-- At a specialization `z` of `η_{a,r}`, the value `z(T - a)` lies strictly above the constants of
norm less than `r` and strictly below the constants of norm greater than `r`. -/
private theorem forall_lt_and_forall_gt_of_discPoint_specializes {a : K} (ha : ‖a‖ ≤ 1)
    (hr₀ : 0 < r) (hr₁ : r ≤ 1) {z : closedPolydisc 1 K} (h : discPoint a ha hr₀ hr₁ ⤳ z) :
    (∀ c : K, ‖c‖ < r → z.1.valuation (C c) < z.1.valuation (T - C a)) ∧
      ∀ c : K, r < ‖c‖ → z.1.valuation (T - C a) < z.1.valuation (C c) := by
  obtain ⟨-, hle, hge⟩ := (eq_discPoint_iff (discPoint a ha hr₀ hr₁) ha hr₀ hr₁).mp rfl
  obtain ⟨d, hd₀, hdr⟩ := NormedField.exists_lt_norm_lt_of_isAlgClosed K le_rfl hr₀
  refine forall_lt_and_forall_gt_of_specializes h _ _ ⟨d, norm_pos_iff.mp hd₀, hdr⟩
    ⟨fun c hc ↦ ?_, fun c hc ↦ ?_⟩
  · rw [← not_le, valuation_le_iff, hle]
    exact hc.not_ge
  · rw [← not_le, valuation_le_iff, hge]
    exact hc.not_ge

/-- A specialization `z` of `η_{a,r}` with `z(T - a)` above a constant of norm `r` is `η_{a,r⁺}`.
Then `r < 1`, since `z(T - a) ≤ 1`. -/
private theorem exists_eq_discPointAbove_of_discPoint_specializes {a : K} (ha : ‖a‖ ≤ 1)
    (hr₀ : 0 < r) (hr₁ : r ≤ 1) {z : closedPolydisc 1 K} (h : discPoint a ha hr₀ hr₁ ⤳ z)
    {c₀ : K} (hc₀ : ‖c₀‖ = r) (hlt₀ : z.1.valuation (C c₀) < z.1.valuation (T - C a)) :
    ∃ hr : r < 1, z = discPointAbove a ha hr₀ hr := by
  have hr : r < 1 := by
    refine hr₁.lt_of_ne fun hr1 ↦ ?_
    -- at radius one, `z(T - a) ≤ max (z(T), z(a)) ≤ 1 = z(c₀)`
    have hT : z.1.valuation T ≤ 1 := by
      simpa using (valuation_le_iff _ _ _).mpr (((mem_closedPolydisc_iff 1 K z.1).mp z.2).2 _
        (mem_powerBoundedSubring.mpr (isPowerBounded_weightedX_one_weight 0)))
    have hCa : z.1.valuation (C a) ≤ 1 := by
      simpa using (closedPolydisc_valuation_weightedC_le_iff z a 1).mpr (by simpa using ha)
    have hc₀1 : z.1.valuation (C c₀) = 1 :=
      (closedPolydisc_valuation_weightedC_eq_of_norm_eq z (by rw [hc₀, hr1, norm_one] :
        ‖c₀‖ = ‖(1 : K)‖)).trans (by simp)
    exact (hlt₀.trans_le ((Valuation.map_sub _ _ _).trans (max_le hT hCa))).ne hc₀1
  obtain ⟨-, hgt⟩ := forall_lt_and_forall_gt_of_discPoint_specializes ha hr₀ hr₁ h
  refine ⟨hr, (eq_discPointAbove_iff z ha hr₀ hr).mpr fun c ↦ ?_⟩
  rw [← valuation_le_iff]
  refine ⟨fun hle ↦ lt_of_not_ge fun hc ↦ ?_, fun hc ↦ (hgt c hc).le⟩
  -- `z(c₀) < z(T - a) ≤ z(c) ≤ z(c₀)`
  exact lt_irrefl _
    (hlt₀.trans_le (hle.trans
      ((closedPolydisc_valuation_weightedC_le_iff z c c₀).mpr (by rwa [hc₀]))))

/-- A specialization `z` of `η_{a,r}` with `z(T - a)` below a constant `c₀` of norm `r` is
`η_{a,r⁻}`. -/
private theorem eq_discPointBelow_of_discPoint_specializes {a : K} (ha : ‖a‖ ≤ 1)
    (hr₀ : 0 < r) (hr₁ : r ≤ 1) {z : closedPolydisc 1 K} (h : discPoint a ha hr₀ hr₁ ⤳ z)
    {c₀ : K} (hc₀ : ‖c₀‖ = r) (hgt₀ : z.1.valuation (T - C a) < z.1.valuation (C c₀)) :
    z = discPointBelow a ha hr₀ hr₁ := by
  obtain ⟨hlt, -⟩ := forall_lt_and_forall_gt_of_discPoint_specializes ha hr₀ hr₁ h
  refine (eq_discPointBelow_iff z ha hr₀ hr₁).mpr fun c ↦ ?_
  rw [← valuation_le_iff]
  refine ⟨fun hle ↦ lt_of_not_ge fun hc ↦ ?_, fun hc ↦ (hlt c hc).le⟩
  -- `z(c) ≤ z(T - a) < z(c₀) ≤ z(c)`
  exact lt_irrefl _
    (hle.trans_lt (hgt₀.trans_le
      ((closedPolydisc_valuation_weightedC_le_iff z c₀ c).mpr (by rwa [hc₀]))))

/-- A specialization `z` of `η_{a,r}` at which `z(T - a)` has the value of every constant of norm
`r` is `η_{a,r}`, or is `η_{b,r⁻}` for some `b` with `‖b - a‖ = r`. -/
private theorem eq_discPoint_or_of_discPoint_specializes {a : K} (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r)
    (hr₁ : r ≤ 1) {z : closedPolydisc 1 K} (h : discPoint a ha hr₀ hr₁ ⤳ z)
    (hA : ∀ c : K, ‖c‖ = r → z.1.valuation (T - C a) ≤ z.1.valuation (C c))
    (hB : ∀ c : K, ‖c‖ = r → z.1.valuation (C c) ≤ z.1.valuation (T - C a)) :
    z = discPoint a ha hr₀ hr₁ ∨
      ∃ (b : K) (hb : ‖b‖ ≤ 1), ‖b - a‖ = r ∧ z = discPointBelow b hb hr₀ hr₁ := by
  obtain ⟨hlt, hgt⟩ := forall_lt_and_forall_gt_of_discPoint_specializes ha hr₀ hr₁ h
  -- `z(T - a)` compares with the constants as `r` compares with their norms
  have hle (c : K) : z.1.valuation (T - C a) ≤ z.1.valuation (C c) ↔ r ≤ ‖c‖ := by
    refine ⟨fun hle ↦ le_of_not_gt fun hc ↦ (hlt c hc).not_ge hle, fun hc ↦ ?_⟩
    rcases hc.lt_or_eq with hc | hc
    · exact (hgt c hc).le
    · exact hA c hc.symm
  have hge (c : K) : z.1.valuation (C c) ≤ z.1.valuation (T - C a) ↔ ‖c‖ ≤ r := by
    refine ⟨fun hge ↦ le_of_not_gt fun hc ↦ (hgt c hc).not_ge hge, fun hc ↦ ?_⟩
    rcases hc.lt_or_eq with hc | hc
    · exact (hlt c hc).le
    · exact hB c hc
  by_cases hmin : ∀ b : K, ‖b - a‖ ≤ r → z.1.valuation (T - C a) ≤ z.1.valuation (T - C b)
  · refine Or.inl ((eq_discPoint_iff z ha hr₀ hr₁).mpr
      ⟨fun b hb ↦ (valuation_le_iff _ _ _).mp (hmin b hb), fun c ↦ ?_, fun c ↦ ?_⟩)
    · rw [← valuation_le_iff]
      exact hle c
    · rw [← valuation_le_iff]
      exact hge c
  push Not at hmin
  obtain ⟨b, hab, hb⟩ := hmin
  have hb₁ : ‖b‖ ≤ 1 := by
    have h' := IsUltrametricDist.norm_add_le_max (b - a) a
    rw [sub_add_cancel] at h'
    exact h'.trans (max_le (hab.trans hr₁) ha)
  -- `‖b - a‖ = r`: otherwise `z(b - a) < z(T - a)`, so `z(T - b) = z(T - a)`
  have hbr : ‖b - a‖ = r := by
    refine hab.antisymm (le_of_not_gt fun hlt' ↦ hb.ne ?_)
    have hsplit : T - C b = (T - C a) - C (b - a) := by
      rw [map_sub]
      ring
    rw [hsplit, Valuation.map_sub_eq_of_lt_left _ (hlt _ hlt')]
  -- `η_{a,r} = η_{b,r}`, so `z(T - b)` lies strictly above the constants of norm less than `r`
  have hη : discPoint a ha hr₀ hr₁ = discPoint b hb₁ hr₀ hr₁ :=
    (discPoint_eq_discPoint_iff ha hb₁ hr₀ hr₁ hr₀ hr₁).mpr ⟨rfl, by rwa [norm_sub_rev]⟩
  obtain ⟨hltb, -⟩ := forall_lt_and_forall_gt_of_discPoint_specializes hb₁ hr₀ hr₁ (hη ▸ h)
  refine Or.inr ⟨b, hb₁, hbr, (eq_discPointBelow_iff z hb₁ hr₀ hr₁).mpr fun c ↦ ?_⟩
  rw [← valuation_le_iff]
  refine ⟨fun hle' ↦ lt_of_not_ge fun hc ↦ ?_, fun hc ↦ (hltb c hc).le⟩
  -- `z(c) ≤ z(T - b) < z(T - a) ≤ z(c)`
  exact lt_irrefl _ (hle'.trans_lt (hb.trans_le ((hle c).mpr hc)))

/-- **The closure of `η_{a,r}`** in the closed unit disc over an algebraically closed complete
nonarchimedean field: a point `z` is a specialization of `η_{a,r}` if and only if `z` is
`η_{a,r}`, or `r` is the norm of an element of `K` and `z` is `η_{a,r⁺}` or `η_{b,r⁻}` for some
`b` with `‖b - a‖ ≤ r`. For `r ∈ |K^×|` these are the points of type (5) around the point
`η_{a,r}` of type (2) (Wedhorn, Example 7.57). -/
theorem discPoint_specializes_iff {a : K} (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    (z : closedPolydisc 1 K) :
    discPoint a ha hr₀ hr₁ ⤳ z ↔ z = discPoint a ha hr₀ hr₁ ∨ (∃ c : K, ‖c‖ = r) ∧
      ((∃ hr : r < 1, z = discPointAbove a ha hr₀ hr) ∨
        ∃ (b : K) (hb : ‖b‖ ≤ 1), ‖b - a‖ ≤ r ∧ z = discPointBelow b hb hr₀ hr₁) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · by_cases hA : ∃ c₀ : K, ‖c₀‖ = r ∧ z.1.valuation (C c₀) < z.1.valuation (T - C a)
    · obtain ⟨c₀, hc₀, hlt₀⟩ := hA
      exact Or.inr ⟨⟨c₀, hc₀⟩, Or.inl
        (exists_eq_discPointAbove_of_discPoint_specializes ha hr₀ hr₁ h hc₀ hlt₀)⟩
    by_cases hB : ∃ c₀ : K, ‖c₀‖ = r ∧ z.1.valuation (T - C a) < z.1.valuation (C c₀)
    · obtain ⟨c₀, hc₀, hgt₀⟩ := hB
      exact Or.inr ⟨⟨c₀, hc₀⟩, Or.inr ⟨a, ha, by simpa using hr₀.le,
        eq_discPointBelow_of_discPoint_specializes ha hr₀ hr₁ h hc₀ hgt₀⟩⟩
    push Not at hA hB
    rcases eq_discPoint_or_of_discPoint_specializes ha hr₀ hr₁ h hA hB with hz | ⟨b, hb, hbr, hz⟩
    · exact Or.inl hz
    · exact Or.inr ⟨⟨b - a, hbr⟩, Or.inr ⟨b, hb, hbr.le, hz⟩⟩
  · rintro (rfl | ⟨-, ⟨hr, rfl⟩ | ⟨b, hb, hab, rfl⟩⟩)
    · exact specializes_rfl
    · exact discPoint_specializes_discPointAbove a ha hr₀ hr
    · rw [(discPoint_eq_discPoint_iff ha hb hr₀ hr₁ hr₀ hr₁).mpr ⟨rfl, by rwa [norm_sub_rev]⟩]
      exact discPoint_specializes_discPointBelow b hb hr₀ hr₁

/-- **`η_{a,r}` is a closed point exactly when `r` is not the norm of an element of `K`**, over an
algebraically closed complete nonarchimedean field: the points of type (3) are closed and the
points of type (2) are not (Wedhorn, Example 7.57). -/
theorem isClosed_singleton_discPoint_iff {a : K} (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r ≤ 1) :
    IsClosed ({discPoint a ha hr₀ hr₁} : Set (closedPolydisc 1 K)) ↔ ∀ c : K, ‖c‖ ≠ r := by
  refine ⟨fun hcl c hc ↦ discPointBelow_ne_discPoint a ha hr₀ hr₁ ⟨c, hc⟩ ?_, fun hr ↦ ?_⟩
  · exact hcl.closure_subset
      (specializes_iff_mem_closure.mp (discPoint_specializes_discPointBelow a ha hr₀ hr₁))
  · refine closure_subset_iff_isClosed.mp fun z hz ↦ ?_
    rcases (discPoint_specializes_iff ha hr₀ hr₁ z).mp (specializes_iff_mem_closure.mpr hz) with
      hz | ⟨⟨c, hc⟩, -⟩
    · exact hz
    · exact absurd hc (hr c)

/-- **`η_{a,r⁺} = η_{a,r}` exactly when `r` is not the norm of an element of `K`**, over an
algebraically closed complete nonarchimedean field (Wedhorn, Example 7.57). -/
theorem discPointAbove_eq_discPoint_iff {a : K} (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r < 1) :
    discPointAbove a ha hr₀ hr₁ = discPoint a ha hr₀ hr₁.le ↔ ∀ c : K, ‖c‖ ≠ r :=
  ⟨fun h c hc ↦ discPointAbove_ne_discPoint a ha hr₀ hr₁ ⟨c, hc⟩ h, fun hr ↦
    ((isClosed_singleton_discPoint_iff ha hr₀ hr₁.le).mpr hr).closure_subset
      (specializes_iff_mem_closure.mp (discPoint_specializes_discPointAbove a ha hr₀ hr₁))⟩

/-- **`η_{a,r⁻} = η_{a,r}` exactly when `r` is not the norm of an element of `K`**, over an
algebraically closed complete nonarchimedean field (Wedhorn, Example 7.57). -/
theorem discPointBelow_eq_discPoint_iff {a : K} (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r ≤ 1) :
    discPointBelow a ha hr₀ hr₁ = discPoint a ha hr₀ hr₁ ↔ ∀ c : K, ‖c‖ ≠ r :=
  ⟨fun h c hc ↦ discPointBelow_ne_discPoint a ha hr₀ hr₁ ⟨c, hc⟩ h, fun hr ↦
    ((isClosed_singleton_discPoint_iff ha hr₀ hr₁).mpr hr).closure_subset
      (specializes_iff_mem_closure.mp (discPoint_specializes_discPointBelow a ha hr₀ hr₁))⟩

/-! ### The points `η_{a,r±}` are closed -/

/-- **`η_{a,r⁺}` is a closed point** of the closed unit disc over an algebraically closed complete
nonarchimedean field. For `r ∈ |K^×|` it is a point of type (5) (Wedhorn, Example 7.57). -/
theorem isClosed_singleton_discPointAbove {a : K} (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r < 1) :
    IsClosed ({discPointAbove a ha hr₀ hr₁} : Set (closedPolydisc 1 K)) := by
  refine closure_subset_iff_isClosed.mp fun z hz ↦ Set.mem_singleton_iff.mpr ?_
  obtain ⟨d, hd₀, hdr⟩ := NormedField.exists_lt_norm_lt_of_isAlgClosed K le_rfl hr₀
  obtain ⟨hlt, hgt⟩ := forall_lt_and_forall_gt_of_specializes (specializes_iff_mem_closure.mpr hz)
    (fun c ↦ ‖c‖ ≤ r) _ ⟨d, norm_pos_iff.mp hd₀, hdr.le⟩
    (forall_lt_and_forall_gt_of_vle_weightedC hr₀
      ((eq_discPointAbove_iff (discPointAbove a ha hr₀ hr₁) ha hr₀ hr₁).mp rfl))
  refine (eq_discPointAbove_iff z ha hr₀ hr₁).mpr fun c ↦ ?_
  rw [← valuation_le_iff]
  exact ⟨fun hle ↦ lt_of_not_ge fun hc ↦ (hlt c hc).not_ge hle, fun hc ↦ (hgt c hc.not_ge).le⟩

/-- **`η_{a,r⁻}` is a closed point** of the closed unit disc over an algebraically closed complete
nonarchimedean field. For `r ∈ |K^×|` it is a point of type (5) (Wedhorn, Example 7.57). -/
theorem isClosed_singleton_discPointBelow {a : K} (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r ≤ 1) :
    IsClosed ({discPointBelow a ha hr₀ hr₁} : Set (closedPolydisc 1 K)) := by
  refine closure_subset_iff_isClosed.mp fun z hz ↦ Set.mem_singleton_iff.mpr ?_
  obtain ⟨d, hd₀, hdr⟩ := NormedField.exists_lt_norm_lt_of_isAlgClosed K le_rfl hr₀
  obtain ⟨hlt, hgt⟩ := forall_lt_and_forall_gt_of_specializes (specializes_iff_mem_closure.mpr hz)
    (fun c ↦ ‖c‖ < r) _ ⟨d, norm_pos_iff.mp hd₀, hdr⟩ (forall_lt_and_forall_gt_of_weightedC_vle
      ((eq_discPointBelow_iff (discPointBelow a ha hr₀ hr₁) ha hr₀ hr₁).mp rfl))
  refine (eq_discPointBelow_iff z ha hr₀ hr₁).mpr fun c ↦ ?_
  rw [← valuation_le_iff]
  exact ⟨fun hle ↦ lt_of_not_ge fun hc ↦ (hgt c (not_lt.mpr hc)).not_ge hle,
    fun hc ↦ (hlt c hc).le⟩

end TauCeti.ValuationSpectrum
