/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.MongeAmpere.Engulfing
import Mathlib.MeasureTheory.Covering.Vitali

/-!
# The Vitali covering lemma for sections of Monge–Ampère solutions

Let `E` be a real inner product space of finite dimension `n ≥ 1` with an additive Haar measure
`μ`, and let `u` be convex on an open set `Ω` with `λ μ ≤ MA_u ≤ Λ μ` on `Ω`, where `MA_u` is the
Aleksandrov Monge–Ampère measure of `u` and `0 < λ`. Write
`S(x, h) = {y ∈ Ω | u y < u x + ℓ (y - x) + h}` for the section of `u` at `x` with a supporting
slope `ℓ` and height `h`, and `θ = 1 + C Λ / λ` for the engulfing constant of
`TauCeti.exists_convexSection_subset_convexSection`.

In Caffarelli's regularity theory, sections play the role of balls. This file proves the two
properties of balls that a covering argument uses.

* **Swallowing.** If two sections `S(x, h)` and `S(y, k)` meet and `h ≤ 2 k`, then
  `S(x, h) ⊆ S(y, 2 θ² k)`. Applying the engulfing property at `x`, at `y` and at a common point
  `z`, with a supporting slope at `z` given by `ConvexOn.exists_forall_add_inner_le`, gives
  `S(x, h) ⊆ S(z, θ h) ⊆ S(z, 2 θ k) ⊆ S(y, 2 θ² k)`.
* **Doubling.** For `K ≥ 1`, `μ(S(x, K h)) ≤ √(C K^n Λ / λ) μ(S(x, h))`, from the volume
  estimates `λ μ(S(x, K h))² ≤ C (K h)^n` and `hⁿ ≤ C Λ μ(S(x, h))²`.

Every application of engulfing needs a section of larger height whose closure lies inside `Ω`.
This *localization* is a hypothesis here: all sections of height `H` centred in a set `D` are
bounded with closure in `Ω`, and the sections of the family lie in `D`, with heights small
compared with `H`. This is the situation of the interior theory of strictly convex solutions,
whose sections of small height centred in a compact subset of `Ω` are compactly contained in
`Ω`; that localization property is not proved here.

With the abstract Vitali lemma `Vitali.exists_disjoint_subfamily_covering_enlargement`,
swallowing gives the **Vitali covering lemma for sections**: from every family of such sections
one can extract a countable disjoint subfamily such that each section of the family lies in the
`2 θ²`-enlargement of a section of the subfamily. With doubling, the union of the family then has
measure at most a constant multiple, depending only on `E`, `μ` and `Λ / λ`, of the measure of
the union of the disjoint subfamily.

## Main statements

* `TauCeti.exists_convexSection_subset_convexSection_of_nonempty_inter` — intersecting sections
  of comparable heights swallow each other;
* `TauCeti.exists_measure_convexSection_le_sqrt_mul` — the doubling property of sections;
* `TauCeti.exists_countable_pairwiseDisjoint_convexSection` — the Vitali covering lemma for
  sections;
* `TauCeti.exists_countable_pairwiseDisjoint_convexSection_measure_le` — its measure form.

## References

* L. A. Caffarelli, *Some regularity properties of solutions of Monge Ampère equation*, Comm.
  Pure Appl. Math. 44 (1991), 965–969.
* L. A. Caffarelli, *Interior `W^{2,p}` estimates for solutions of the Monge–Ampère equation*,
  Ann. of Math. 131 (1990), 135–150, for covering arguments with sections.
* C. E. Gutiérrez, *The Monge–Ampère Equation*, 2nd ed., Progress in Nonlinear Differential
  Equations and Their Applications 89, Birkhäuser, 2016, §3.3 (engulfing) and the covering
  lemmas for sections used in its `W^{2,p}` estimates.
* A. Figalli, *The Monge–Ampère Equation and Its Applications*, Zurich Lectures in Advanced
  Mathematics, EMS, 2017, Chapter 4.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Measure Set Module
open scoped ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **Doubling of sections.** There is a constant `C`, depending only on `E` and `μ`, with the
following property. Let `u` be convex on an open set `Ω`, with `λ μ ≤ MA_u ≤ Λ μ` on `Ω` for the
Monge–Ampère measure of `u` extended by `⊤` off `Ω` and `0 < λ`, let `ℓ` be a supporting slope of
`u` at `x ∈ Ω`, and let `K ≥ 1`. If the section `S(x, K h)` is bounded with closure inside `Ω`,
then `μ(S(x, K h)) ≤ √(C K^n Λ / λ) μ(S(x, h))`, where `n = finrank ℝ E`. -/
theorem exists_measure_convexSection_le_sqrt_mul :
    ∃ C : ℝ≥0, ∀ (Ω : Set E) [DecidablePred (· ∈ Ω)] (u : E → ℝ) (x : E) (ℓ : E →ₗ[ℝ] ℝ)
      (h : ℝ) (K lam Lam : ℝ≥0), IsOpen Ω → ConvexOn ℝ Ω u → x ∈ Ω →
      (∀ y ∈ Ω, u x + (ℓ y - ℓ x) ≤ u y) → 1 ≤ K →
      Bornology.IsBounded (convexSection Ω u x ℓ (K * h)) →
      closure (convexSection Ω u x ℓ (K * h)) ⊆ Ω → 0 < lam →
      (lam : ℝ≥0∞) • μ.restrict Ω ≤
        mongeAmpereMeasure μ (fun y => if y ∈ Ω then (u y : EReal) else ⊤) →
      mongeAmpereMeasure μ (fun y => if y ∈ Ω then (u y : EReal) else ⊤) ≤
        (Lam : ℝ≥0∞) • μ.restrict Ω →
      μ (convexSection Ω u x ℓ (K * h)) ≤
        NNReal.sqrt (C * K ^ finrank ℝ E * Lam / lam) * μ (convexSection Ω u x ℓ h) := by
  obtain ⟨C₁, hC₁⟩ := exists_mul_measure_convexSection_sq_le_mul_ofReal_pow μ (E := E)
  obtain ⟨C₂, hC₂⟩ := exists_ofReal_pow_le_mul_measure_convexSection_mul_mongeAmpereMeasure μ
    (E := E)
  refine ⟨C₁ * C₂, fun Ω _ u x ℓ h K lam Lam hΩ hu hx hℓ hK hSb hSΩ hlam hMA hMA' => ?_⟩
  set n := finrank ℝ E
  set S := convexSection Ω u x ℓ h
  set SK := convexSection Ω u x ℓ (K * h)
  rcases le_or_gt h 0 with hh | hh
  · -- Nonpositive heights give empty sections.
    rw [show SK = ∅ from (convexSection_eq_empty_iff hx hℓ).2
      (mul_nonpos_of_nonneg_of_nonpos K.coe_nonneg hh), measure_empty]
    positivity
  have hSSK : S ⊆ SK := convexSection_mono_height (le_mul_of_one_le_left hh.le hK)
  -- The two volume estimates give `λ μ(S(x, K h))² ≤ C₁ C₂ Kⁿ Λ μ(S(x, h))²`.
  have hMAS : mongeAmpereMeasure μ (fun y => if y ∈ Ω then (u y : EReal) else ⊤) S ≤
      Lam * μ S := by
    refine (Measure.le_iff'.1 hMA' S).trans ?_
    rw [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul_right (Measure.restrict_apply_le _ _) _
  have hsq : (lam : ℝ≥0∞) * μ SK ^ 2 ≤ (C₁ * C₂ * K ^ n * Lam : ℝ≥0) * μ S ^ 2 :=
    calc (lam : ℝ≥0∞) * μ SK ^ 2 ≤ C₁ * ENNReal.ofReal (K * h) ^ n :=
          hC₁ Ω u x ℓ (K * h) lam hΩ hu hℓ hSb hSΩ hMA
      _ = C₁ * K ^ n * ENNReal.ofReal h ^ n := by
          rw [ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_coe_nnreal, mul_pow, mul_assoc]
      _ ≤ C₁ * K ^ n * (C₂ * μ S *
            mongeAmpereMeasure μ (fun y => if y ∈ Ω then (u y : EReal) else ⊤) S) := by
          gcongr
          exact hC₂ Ω u x ℓ h hΩ hu hx (hSb.subset hSSK) ((closure_mono hSSK).trans hSΩ)
      _ ≤ C₁ * K ^ n * (C₂ * μ S * (Lam * μ S)) := by gcongr
      _ = (C₁ * C₂ * K ^ n * Lam : ℝ≥0) * μ S ^ 2 := by push_cast; ring
  -- Divide by `λ` and take square roots.
  set r := NNReal.sqrt (C₁ * C₂ * K ^ n * Lam / lam)
  have hr : ((r : ℝ≥0∞) * μ S) ^ 2 =
      (lam : ℝ≥0∞)⁻¹ * ((C₁ * C₂ * K ^ n * Lam : ℝ≥0) * μ S ^ 2) := by
    rw [mul_pow, ← ENNReal.coe_pow, NNReal.sq_sqrt, ENNReal.coe_div hlam.ne', div_eq_mul_inv,
      mul_comm _ (lam : ℝ≥0∞)⁻¹, mul_assoc]
  rw [← ENNReal.pow_le_pow_left_iff two_ne_zero, hr]
  · calc μ SK ^ 2 = (lam : ℝ≥0∞)⁻¹ * (lam * μ SK ^ 2) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast hlam.ne') ENNReal.coe_ne_top,
            one_mul]
      _ ≤ _ := by gcongr

/-- **Intersecting sections swallow each other.** There is a constant `C`, depending only on `E`
and `μ`, with the following property. Let `u` be convex on an open set `Ω`, with
`λ μ ≤ MA_u ≤ Λ μ` on `Ω` for the Monge–Ampère measure of `u` extended by `⊤` off `Ω` and
`0 < λ`, and write `θ = 1 + C Λ / λ`. Suppose that every section of height `H` centred at a point
of `D`, with any supporting slope, is bounded with closure inside `Ω`. Let `ℓ` and `m` be
supporting slopes of `u` at `x, y ∈ Ω`, with `S(x, h) ⊆ D` and `y ∈ D`. If `S(x, h)` meets
`S(y, k)`, `h ≤ 2 k` and `4 θ k ≤ H`, then `S(x, h) ⊆ S(y, 2 θ² k)`. -/
theorem exists_convexSection_subset_convexSection_of_nonempty_inter :
    ∃ C : ℝ≥0, ∀ (Ω : Set E) [DecidablePred (· ∈ Ω)] (u : E → ℝ) (D : Set E) (H : ℝ)
      (lam Lam : ℝ≥0) (x y : E) (ℓ m : E →ₗ[ℝ] ℝ) (h k : ℝ), IsOpen Ω → ConvexOn ℝ Ω u →
      (∀ z ∈ D, ∀ n : E →ₗ[ℝ] ℝ, (∀ w ∈ Ω, u z + (n w - n z) ≤ u w) →
        Bornology.IsBounded (convexSection Ω u z n H) ∧ closure (convexSection Ω u z n H) ⊆ Ω) →
      0 < lam →
      (lam : ℝ≥0∞) • μ.restrict Ω ≤
        mongeAmpereMeasure μ (fun y => if y ∈ Ω then (u y : EReal) else ⊤) →
      mongeAmpereMeasure μ (fun y => if y ∈ Ω then (u y : EReal) else ⊤) ≤
        (Lam : ℝ≥0∞) • μ.restrict Ω →
      x ∈ Ω → y ∈ Ω → (∀ w ∈ Ω, u x + (ℓ w - ℓ x) ≤ u w) →
      (∀ w ∈ Ω, u y + (m w - m y) ≤ u w) → convexSection Ω u x ℓ h ⊆ D → y ∈ D →
      (convexSection Ω u x ℓ h ∩ convexSection Ω u y m k).Nonempty → h ≤ 2 * k →
      4 * (1 + C * Lam / lam) * k ≤ H →
      convexSection Ω u x ℓ h ⊆ convexSection Ω u y m (2 * (1 + C * Lam / lam) ^ 2 * k) := by
  obtain ⟨C, hC⟩ := exists_convexSection_subset_convexSection μ (E := E)
  refine ⟨C, fun Ω _ u D H lam Lam x y ℓ m h k hΩ hu hD hlam hMA hMA' hx hy hℓ hm hxD hyD
    ⟨z, hzx, hzy⟩ hhk hkH => ?_⟩
  set θ : ℝ := 1 + C * Lam / lam
  have hθ : 1 ≤ θ := le_add_of_nonneg_right (by positivity)
  have hh : 0 < h := (convexSection_nonempty_iff hx hℓ).1 ⟨z, hzx⟩
  have hk : 0 < k := (convexSection_nonempty_iff hy hm).1 ⟨z, hzy⟩
  -- A supporting slope `n` of `u` at the common point `z`.
  obtain ⟨p, hp⟩ := hu.exists_forall_add_inner_le hΩ (convexSection_subset hzx)
  set n : E →ₗ[ℝ] ℝ := innerₗ E p
  have hn : ∀ w ∈ Ω, u z + (n w - n z) ≤ u w := fun w hw => by
    have := hp w hw
    rw [real_inner_comm p (w - z), inner_sub_right] at this
    simpa only [n, innerₗ_apply_apply] using this
  have hzD : z ∈ D := hxD hzx
  have hxD' : x ∈ D := hxD (mem_convexSection_iff.2 ⟨hx, by simpa using hh⟩)
  -- Engulfing at `x`: `S(x, h) ⊆ S(z, θ h)`.
  have h₁ := isBounded_convexSection_and_closure_subset_of_le (h := 2 * h)
    (by nlinarith) (hD x hxD' ℓ hℓ)
  have e₁ := hC Ω u x ℓ h lam Lam hΩ hu hℓ h₁.1 h₁.2 hlam hMA hMA' z hzx n hn
  -- Engulfing at `y`: `y ∈ S(y, k) ⊆ S(z, θ k)`.
  have h₂ := isBounded_convexSection_and_closure_subset_of_le (h := 2 * k)
    (by nlinarith) (hD y hyD m hm)
  have hyz := hC Ω u y m k lam Lam hΩ hu hm h₂.1 h₂.2 hlam hMA hMA' z hzy n hn
    (mem_convexSection_iff.2 ⟨hy, by simpa using hk⟩)
  -- Engulfing at `z` with height `2 θ k`: `S(z, 2 θ k) ⊆ S(y, 2 θ² k)`.
  have h₃ := isBounded_convexSection_and_closure_subset_of_le (h := 2 * (2 * θ * k))
    (by linarith) (hD z hzD n hn)
  have e₃ := hC Ω u z n (2 * θ * k) lam Lam hΩ hu hn h₃.1 h₃.2 hlam hMA hMA' y
    (convexSection_mono_height (by nlinarith) hyz) m hm
  rw [show θ * (2 * θ * k) = 2 * θ ^ 2 * k by ring] at e₃
  exact e₁.trans ((convexSection_mono_height (by nlinarith)).trans e₃)

/-- **The Vitali covering lemma for sections.** There is a constant `C`, depending only on `E`
and `μ`, with the following property. Let `u` be convex on an open set `Ω`, with
`λ μ ≤ MA_u ≤ Λ μ` on `Ω` for the Monge–Ampère measure of `u` extended by `⊤` off `Ω` and
`0 < λ`, and write `θ = 1 + C Λ / λ`. Suppose that every section of height `H` centred at a point
of `D`, with any supporting slope, is bounded with closure inside `Ω`. Consider a family of
sections `S i = S(c i, h i)`, `i ∈ t`, with centres `c i ∈ Ω`, supporting slopes `ℓ i`, positive
heights with `4 θ h i ≤ H`, and `S i ⊆ D`. Then there is a countable subfamily `s ⊆ t` of pairwise
disjoint sections such that every `S i` with `i ∈ t` lies in `S(c j, 2 θ² h j)` for some
`j ∈ s`. -/
theorem exists_countable_pairwiseDisjoint_convexSection :
    ∃ C : ℝ≥0, ∀ {ι : Type*} (Ω : Set E) [DecidablePred (· ∈ Ω)] (u : E → ℝ) (D : Set E) (H : ℝ)
      (lam Lam : ℝ≥0) (t : Set ι) (c : ι → E) (ℓ : ι → E →ₗ[ℝ] ℝ) (h : ι → ℝ), IsOpen Ω →
      ConvexOn ℝ Ω u →
      (∀ z ∈ D, ∀ n : E →ₗ[ℝ] ℝ, (∀ w ∈ Ω, u z + (n w - n z) ≤ u w) →
        Bornology.IsBounded (convexSection Ω u z n H) ∧ closure (convexSection Ω u z n H) ⊆ Ω) →
      0 < lam →
      (lam : ℝ≥0∞) • μ.restrict Ω ≤
        mongeAmpereMeasure μ (fun y => if y ∈ Ω then (u y : EReal) else ⊤) →
      mongeAmpereMeasure μ (fun y => if y ∈ Ω then (u y : EReal) else ⊤) ≤
        (Lam : ℝ≥0∞) • μ.restrict Ω →
      (∀ i ∈ t, c i ∈ Ω) → (∀ i ∈ t, ∀ w ∈ Ω, u (c i) + (ℓ i w - ℓ i (c i)) ≤ u w) →
      (∀ i ∈ t, convexSection Ω u (c i) (ℓ i) (h i) ⊆ D) → (∀ i ∈ t, 0 < h i) →
      (∀ i ∈ t, 4 * (1 + C * Lam / lam) * h i ≤ H) →
      ∃ s ⊆ t, s.Countable ∧ s.PairwiseDisjoint (fun i => convexSection Ω u (c i) (ℓ i) (h i)) ∧
        ∀ i ∈ t, ∃ j ∈ s, convexSection Ω u (c i) (ℓ i) (h i) ⊆
          convexSection Ω u (c j) (ℓ j) (2 * (1 + C * Lam / lam) ^ 2 * h j) := by
  obtain ⟨C, hC⟩ := exists_convexSection_subset_convexSection_of_nonempty_inter μ (E := E)
  refine ⟨C, fun Ω _ u D H lam Lam t c ℓ h hΩ hu hD hlam hMA hMA' hc hℓ hSD hh hhH => ?_⟩
  have hθ : (1 : ℝ) ≤ 1 + C * Lam / lam := le_add_of_nonneg_right (by positivity)
  have hne : ∀ i ∈ t, (convexSection Ω u (c i) (ℓ i) (h i)).Nonempty := fun i hi =>
    (convexSection_nonempty_iff (hc i hi) (hℓ i hi)).2 (hh i hi)
  obtain ⟨s, hst, hdisj, hcov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
    (fun i => convexSection Ω u (c i) (ℓ i) (h i)) t h 2 one_lt_two (fun i hi => (hh i hi).le) H
    (fun i hi => by nlinarith [hh i hi, hhH i hi]) hne
  refine ⟨s, hst, hdisj.countable_of_isOpen (fun i _ => isOpen_convexSection hΩ
    (hu.continuousOn hΩ) (ℓ i).continuous_of_finiteDimensional) fun i hi => hne i (hst hi),
    hdisj, fun i hi => ?_⟩
  obtain ⟨j, hj, hij, hhij⟩ := hcov i hi
  have hjt := hst hj
  exact ⟨j, hj, hC Ω u D H lam Lam (c i) (c j) (ℓ i) (ℓ j) (h i) (h j) hΩ hu hD hlam hMA hMA'
    (hc i hi) (hc j hjt) (hℓ i hi) (hℓ j hjt) (hSD i hi) (hSD j hjt (mem_convexSection_iff.2
      ⟨hc j hjt, by simpa using hh j hjt⟩)) hij hhij (hhH j hjt)⟩

/-- **The Vitali covering lemma for sections, measure form.** There are constants `C` and `A`,
depending only on `E` and `μ`, with the following property. Let `u` be convex on an open set `Ω`,
with `λ μ ≤ MA_u ≤ Λ μ` on `Ω` for the Monge–Ampère measure of `u` extended by `⊤` off `Ω` and
`0 < λ`, and write `θ = 1 + C Λ / λ`. Suppose that every section of height `H` centred at a point
of `D`, with any supporting slope, is bounded with closure inside `Ω`. Consider a family of
sections `S i = S(c i, h i)`, `i ∈ t`, with centres `c i ∈ Ω`, supporting slopes `ℓ i`, positive
heights with `4 θ h i ≤ H` and `2 θ² h i ≤ H`, and `S i ⊆ D`. Then there is a countable subfamily
`s ⊆ t` of pairwise disjoint sections whose union has measure at least a fixed fraction of the
measure of the union of the whole family:
`μ (⋃ i ∈ t, S i) ≤ √(A (2 θ²)ⁿ Λ / λ) μ (⋃ j ∈ s, S j)`, where `n = finrank ℝ E`. -/
theorem exists_countable_pairwiseDisjoint_convexSection_measure_le :
    ∃ C A : ℝ≥0, ∀ {ι : Type*} (Ω : Set E) [DecidablePred (· ∈ Ω)] (u : E → ℝ) (D : Set E)
      (H : ℝ) (lam Lam : ℝ≥0) (t : Set ι) (c : ι → E) (ℓ : ι → E →ₗ[ℝ] ℝ) (h : ι → ℝ),
      IsOpen Ω → ConvexOn ℝ Ω u →
      (∀ z ∈ D, ∀ n : E →ₗ[ℝ] ℝ, (∀ w ∈ Ω, u z + (n w - n z) ≤ u w) →
        Bornology.IsBounded (convexSection Ω u z n H) ∧ closure (convexSection Ω u z n H) ⊆ Ω) →
      0 < lam →
      (lam : ℝ≥0∞) • μ.restrict Ω ≤
        mongeAmpereMeasure μ (fun y => if y ∈ Ω then (u y : EReal) else ⊤) →
      mongeAmpereMeasure μ (fun y => if y ∈ Ω then (u y : EReal) else ⊤) ≤
        (Lam : ℝ≥0∞) • μ.restrict Ω →
      (∀ i ∈ t, c i ∈ Ω) → (∀ i ∈ t, ∀ w ∈ Ω, u (c i) + (ℓ i w - ℓ i (c i)) ≤ u w) →
      (∀ i ∈ t, convexSection Ω u (c i) (ℓ i) (h i) ⊆ D) → (∀ i ∈ t, 0 < h i) →
      (∀ i ∈ t, 4 * (1 + C * Lam / lam) * h i ≤ H) →
      (∀ i ∈ t, 2 * (1 + C * Lam / lam) ^ 2 * h i ≤ H) →
      ∃ s ⊆ t, s.Countable ∧ s.PairwiseDisjoint (fun i => convexSection Ω u (c i) (ℓ i) (h i)) ∧
        μ (⋃ i ∈ t, convexSection Ω u (c i) (ℓ i) (h i)) ≤
          NNReal.sqrt (A * (2 * (1 + C * Lam / lam) ^ 2) ^ finrank ℝ E * Lam / lam) *
            μ (⋃ j ∈ s, convexSection Ω u (c j) (ℓ j) (h j)) := by
  obtain ⟨C, hC⟩ := exists_countable_pairwiseDisjoint_convexSection μ (E := E)
  obtain ⟨A, hA⟩ := exists_measure_convexSection_le_sqrt_mul μ (E := E)
  refine ⟨C, A, fun Ω _ u D H lam Lam t c ℓ h hΩ hu hD hlam hMA hMA' hc hℓ hSD hh hhH hhH' => ?_⟩
  obtain ⟨s, hst, hs, hdisj, hcov⟩ :=
    hC Ω u D H lam Lam t c ℓ h hΩ hu hD hlam hMA hMA' hc hℓ hSD hh hhH
  refine ⟨s, hst, hs, hdisj, ?_⟩
  set K : ℝ≥0 := 2 * (1 + C * Lam / lam) ^ 2
  have hK : 1 ≤ K := one_le_two.trans
    (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (le_add_of_nonneg_right (by positivity))))
  have hKh : ∀ j, (K : ℝ) * h j = 2 * (1 + C * Lam / lam) ^ 2 * h j := fun j => by
    simp only [K, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_pow, NNReal.coe_add,
      NNReal.coe_one, NNReal.coe_div]
  -- Each enlarged section of the subfamily is controlled by the section itself.
  have hdbl : ∀ j ∈ s, μ (convexSection Ω u (c j) (ℓ j) (2 * (1 + C * Lam / lam) ^ 2 * h j)) ≤
      NNReal.sqrt (A * K ^ finrank ℝ E * Lam / lam) * μ (convexSection Ω u (c j) (ℓ j) (h j)) := by
    intro j hj
    have hjt := hst hj
    have hloc := isBounded_convexSection_and_closure_subset_of_le (hhH' j hjt)
      (hD (c j) (hSD j hjt (mem_convexSection_iff.2 ⟨hc j hjt, by simpa using hh j hjt⟩)) (ℓ j)
        (hℓ j hjt))
    rw [← hKh] at hloc ⊢
    exact hA Ω u (c j) (ℓ j) (h j) K lam Lam hΩ hu (hc j hjt) (hℓ j hjt) hK hloc.1 hloc.2 hlam
      hMA hMA'
  have hmeas : ∀ j ∈ s, MeasurableSet (convexSection Ω u (c j) (ℓ j) (h j)) := fun j _ =>
    (isOpen_convexSection hΩ (hu.continuousOn hΩ)
      (ℓ j).continuous_of_finiteDimensional).measurableSet
  calc μ (⋃ i ∈ t, convexSection Ω u (c i) (ℓ i) (h i))
      ≤ μ (⋃ j ∈ s, convexSection Ω u (c j) (ℓ j) (2 * (1 + C * Lam / lam) ^ 2 * h j)) := by
        refine measure_mono (iUnion₂_subset fun i hi => ?_)
        obtain ⟨j, hj, hij⟩ := hcov i hi
        exact hij.trans (subset_biUnion_of_mem (u := fun j =>
          convexSection Ω u (c j) (ℓ j) (2 * (1 + C * Lam / lam) ^ 2 * h j)) hj)
    _ ≤ ∑' j : s, μ (convexSection Ω u (c j) (ℓ j) (2 * (1 + C * Lam / lam) ^ 2 * h j)) :=
        measure_biUnion_le μ hs _
    _ ≤ ∑' j : s, (NNReal.sqrt (A * K ^ finrank ℝ E * Lam / lam) : ℝ≥0∞) *
          μ (convexSection Ω u (c j) (ℓ j) (h j)) :=
        ENNReal.tsum_le_tsum fun j => hdbl j j.2
    _ = _ := by rw [ENNReal.tsum_mul_left, measure_biUnion hs hdisj hmeas]

end TauCeti
