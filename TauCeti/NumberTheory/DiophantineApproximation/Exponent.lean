/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Codex
-/
module

public import Mathlib.NumberTheory.DiophantineApproximation.Basic
public import Mathlib.NumberTheory.Transcendental.Liouville.Measure
public import TauCeti.Data.Rat.BoundedDen

/-!
# The irrationality exponent

This file defines the irrationality exponent of a real number as the supremum of the exponents
for which it satisfies Mathlib's `LiouvilleWith` predicate.  It establishes the order-theoretic
API of this definition, identifies infinite irrationality exponent with the Liouville property,
computes the exponent of rational numbers, and records its elementary rational affine
invariances.

It then relates the exponent to approximation by reduced fractions: `irrationalityExponent ξ` is
the supremum of the `p` for which infinitely many `r : ℚ` satisfy `|ξ - r| < r.den ^ (-p)`
(`irrationalityExponent_eq_iSup_infinite`). Dirichlet's approximation theorem makes every
irrational number a Liouville number with exponent two, so the exponent is at least two exactly
on the irrational numbers (`two_le_irrationalityExponent_iff`), and Mathlib's measure estimate for
`LiouvilleWith` gives exponent two for almost every real number
(`ae_irrationalityExponent_eq_two`).

The definition follows Sondow, *Irrationality measures, irrationality bases, and a theorem of
Jarnik*, Definition 2.
-/

public section

open Filter
open scoped ENNReal

namespace TauCeti

/-- The irrationality exponent of `ξ` is the supremum of the real exponents `p` for which
`LiouvilleWith p ξ` holds. -/
noncomputable def irrationalityExponent (ξ : ℝ) : ℝ≥0∞ :=
  ⨆ (p : ℝ) (_ : LiouvilleWith p ξ), ENNReal.ofReal p

/-- The irrationality exponent is the supremum of `ENNReal.ofReal p` over the exponents `p` for
which `LiouvilleWith p ξ` holds. -/
theorem irrationalityExponent_def (ξ : ℝ) :
    irrationalityExponent ξ = ⨆ (p : ℝ) (_ : LiouvilleWith p ξ), ENNReal.ofReal p :=
  (rfl)

/-- An exponent satisfying `LiouvilleWith` is at most the irrationality exponent. -/
theorem le_irrationalityExponent_of_liouvilleWith {p ξ : ℝ} (h : LiouvilleWith p ξ) :
    ENNReal.ofReal p ≤ irrationalityExponent ξ :=
  le_iSup_of_le p <| le_iSup_of_le h le_rfl

/-- The irrationality exponent of every real number is at least one. -/
theorem one_le_irrationalityExponent (ξ : ℝ) : 1 ≤ irrationalityExponent ξ := by
  simpa using le_irrationalityExponent_of_liouvilleWith (liouvilleWith_one ξ)

/-- A real exponent strictly below the irrationality exponent satisfies `LiouvilleWith`. -/
theorem liouvilleWith_of_lt_irrationalityExponent {p ξ : ℝ}
    (h : ENNReal.ofReal p < irrationalityExponent ξ) : LiouvilleWith p ξ := by
  by_cases hp : p ≤ 0
  · exact (liouvilleWith_one ξ).mono (hp.trans zero_le_one)
  rw [irrationalityExponent, lt_iSup_iff] at h
  obtain ⟨q, hq⟩ := h
  rw [lt_iSup_iff] at hq
  obtain ⟨hqL, hpq⟩ := hq
  exact hqL.mono <| (ENNReal.ofReal_lt_ofReal_iff'.mp hpq).1.le

/-- The irrationality exponent is bounded by `a` exactly when every exponent satisfying
`LiouvilleWith` maps below `a`. -/
theorem irrationalityExponent_le_iff {ξ : ℝ} {a : ℝ≥0∞} :
    irrationalityExponent ξ ≤ a ↔ ∀ p : ℝ, LiouvilleWith p ξ → ENNReal.ofReal p ≤ a := by
  simp [irrationalityExponent]

/-- A real number has infinite irrationality exponent exactly when it is a Liouville number. -/
theorem irrationalityExponent_eq_top_iff (ξ : ℝ) :
    irrationalityExponent ξ = ⊤ ↔ Liouville ξ := by
  constructor
  · intro h
    rw [← forall_liouvilleWith_iff]
    intro p
    apply liouvilleWith_of_lt_irrationalityExponent
    rw [h]
    exact ENNReal.ofReal_lt_top
  · intro h
    apply top_unique
    rw [← ENNReal.iSup_natCast]
    refine iSup_le fun n ↦ ?_
    simpa using le_irrationalityExponent_of_liouvilleWith (h.liouvilleWith n)

/-- The irrationality exponent of a rational number is one. -/
@[simp]
theorem irrationalityExponent_ratCast (q : ℚ) : irrationalityExponent (q : ℝ) = 1 := by
  apply le_antisymm
  · rw [irrationalityExponent_le_iff]
    intro p hp
    have hp_one : p ≤ 1 := by
      by_contra hp_one
      exact q.not_irrational (hp.irrational (lt_of_not_ge hp_one))
    simpa using ENNReal.ofReal_le_ofReal hp_one
  · exact one_le_irrationalityExponent q

/-- Adding a rational number does not change the irrationality exponent. -/
@[simp]
theorem irrationalityExponent_add_ratCast (ξ : ℝ) (q : ℚ) :
    irrationalityExponent (ξ + q) = irrationalityExponent ξ := by
  simp only [irrationalityExponent, LiouvilleWith.add_rat_iff]

/-- Multiplying by a nonzero rational number does not change the irrationality exponent. -/
@[simp]
theorem irrationalityExponent_ratCast_mul (q : ℚ) (ξ : ℝ) (hq : q ≠ 0) :
    irrationalityExponent (q * ξ) = irrationalityExponent ξ := by
  simp only [irrationalityExponent, LiouvilleWith.rat_mul_iff hq]

/-- Negation does not change the irrationality exponent. -/
@[simp]
theorem irrationalityExponent_neg (ξ : ℝ) :
    irrationalityExponent (-ξ) = irrationalityExponent ξ := by
  simp only [irrationalityExponent, LiouvilleWith.neg_iff]

/-- An irrationality exponent strictly greater than one forces irrationality. -/
theorem irrational_of_one_lt_irrationalityExponent {ξ : ℝ}
    (hξ : 1 < irrationalityExponent ξ) : Irrational ξ := by
  rw [irrationalityExponent, lt_iSup_iff] at hξ
  obtain ⟨p, hp⟩ := hξ
  rw [lt_iSup_iff] at hp
  obtain ⟨hpL, hp_one⟩ := hp
  exact hpL.irrational <| (ENNReal.ofReal_lt_ofReal_iff'.mp <| by simpa using hp_one).1

/-! ### Approximation by reduced fractions -/

/-- If infinitely many rational numbers `r` satisfy `|ξ - r| < r.den ^ (-p)`, then `ξ` is a
Liouville number with exponent `p`. -/
theorem _root_.Set.Infinite.liouvilleWith_of_abs_sub_lt_rpow_neg {p ξ : ℝ}
    (h : {r : ℚ | |ξ - r| < (r.den : ℝ) ^ (-p)}.Infinite) : LiouvilleWith p ξ := by
  refine ⟨1, Nat.frequently_atTop_iff_infinite.2 fun hfin ↦ h ?_⟩
  obtain ⟨N, hN⟩ := hfin.bddAbove
  -- Every approximation `r ≠ ξ` has denominator in the finite set, hence at most `N`.
  have hden {r : ℚ} (hr : |ξ - r| < (r.den : ℝ) ^ (-p)) (hne : (r : ℝ) ≠ ξ) : r.den ≤ N := by
    refine hN ⟨r.num, ?_, ?_⟩ <;> rw [← Rat.cast_def]
    · exact hne.symm
    · rwa [one_div, ← Real.rpow_neg (Nat.cast_nonneg _)]
  -- A denominator `d ≤ N` gives `d ^ (-p) ≤ N ^ |p|`, so these approximations are bounded.
  have hbound {r : ℚ} (hr : |ξ - r| < (r.den : ℝ) ^ (-p)) (hle : r.den ≤ N) :
      (r : ℝ) ∈ Metric.ball ξ ((N : ℝ) ^ |p|) := by
    have hd : (1 : ℝ) ≤ r.den := by exact_mod_cast r.pos
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_comm]
    calc |ξ - r| < (r.den : ℝ) ^ (-p) := hr
      _ ≤ (r.den : ℝ) ^ |p| := Real.rpow_le_rpow_of_exponent_le hd (neg_le_abs p)
      _ ≤ (N : ℝ) ^ |p| := by gcongr
  have hfin' := ((Metric.isBounded_ball (x := ξ) (r := (N : ℝ) ^ |p|)).finite_setOf_rat_den_le
    N).union
    ((Set.subsingleton_singleton (a := ξ)).preimage Rat.cast_injective).finite
  refine hfin'.subset ?_
  intro r hr
  by_cases hne : (r : ℝ) = ξ
  · exact Or.inr hne
  · have hle := hden hr hne
    exact Or.inl ⟨hle, hbound hr hle⟩

/-- A Liouville number with exponent `p` has, for every `q < p`, infinitely many rational
approximations `r` with `|ξ - r| < r.den ^ (-q)`. -/
theorem _root_.LiouvilleWith.infinite_setOf_abs_sub_lt_rpow_neg {p q ξ : ℝ}
    (h : LiouvilleWith p ξ) (hq : q < p) : {r : ℚ | |ξ - r| < (r.den : ℝ) ^ (-q)}.Infinite := by
  -- The sets decrease as the exponent grows, so it suffices to treat `0 < q < p` with `0 < p`.
  have hmono {q q' : ℝ} (hqq' : q ≤ q') :
      {r : ℚ | |ξ - r| < (r.den : ℝ) ^ (-q')} ⊆ {r : ℚ | |ξ - r| < (r.den : ℝ) ^ (-q)} :=
    fun r hr ↦ lt_of_lt_of_le hr <|
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast r.pos) (neg_le_neg hqq')
  wlog hp : 0 < p generalizing p
  · exact this (liouvilleWith_one ξ) (hq.trans_le (not_lt.mp hp |>.trans zero_le_one))
      zero_lt_one
  wlog hq₀ : 0 < q generalizing q
  · exact (this (max_lt hq (half_lt_self hp)) (lt_max_of_lt_right (half_pos hp))).mono
      (hmono (le_max_left q (p / 2)))
  intro hfin
  -- The finitely many approximations distinct from `ξ` stay at distance at least `1 / M`.
  obtain ⟨M, hM⟩ := (hfin.image fun r : ℚ ↦ |ξ - r|⁻¹).bddAbove
  have hsmall : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (-q) < (max M 1)⁻¹ :=
    ((tendsto_rpow_neg_atTop hq₀).comp tendsto_natCast_atTop_atTop).eventually
      (gt_mem_nhds (by positivity))
  obtain ⟨n, ⟨hn, hnM⟩, m, hne, hlt⟩ :=
    ((eventually_ge_atTop 1).and hsmall).and_frequently (h.frequently_lt_rpow_neg hq) |>.exists
  set r : ℚ := (m : ℚ) / n
  have hr : (r : ℝ) = m / n := by simp [r]
  have hden : r.den ≤ n := by
    have := Rat.den_dvd m n
    rw [Rat.divInt_eq_div] at this
    exact Nat.le_of_dvd hn (Int.natCast_dvd_natCast.mp this)
  have hpos : 0 < |ξ - r| := abs_pos.mpr (sub_ne_zero.mpr (hr ▸ hne))
  have hmem : r ∈ {r : ℚ | |ξ - r| < (r.den : ℝ) ^ (-q)} := by
    rw [Set.mem_ofPred_eq, hr]
    exact hlt.trans_le <| Real.rpow_le_rpow_of_nonpos (by exact_mod_cast r.pos)
      (by exact_mod_cast hden) (neg_nonpos.mpr hq₀.le)
  have hle : |ξ - r|⁻¹ ≤ max M 1 := (hM ⟨r, hmem, rfl⟩).trans (le_max_left _ _)
  have : (max M 1)⁻¹ ≤ |ξ - r| := by
    rwa [inv_le_comm₀ (by positivity) hpos]
  exact (lt_irrefl _) (this.trans_lt (hr ▸ hlt |>.trans hnM))

/-- The irrationality exponent of `ξ` is the supremum of the exponents `p` for which infinitely
many rational numbers `r` satisfy `|ξ - r| < r.den ^ (-p)`. -/
theorem irrationalityExponent_eq_iSup_infinite (ξ : ℝ) :
    irrationalityExponent ξ =
      ⨆ (p : ℝ) (_ : {r : ℚ | |ξ - r| < (r.den : ℝ) ^ (-p)}.Infinite), ENNReal.ofReal p := by
  refine le_antisymm (iSup₂_le fun p hp ↦ le_of_forall_lt fun c hc ↦ ?_)
    (iSup₂_le fun p hp ↦ le_irrationalityExponent_of_liouvilleWith
      hp.liouvilleWith_of_abs_sub_lt_rpow_neg)
  have hc' : c.toReal < p := (ENNReal.lt_ofReal_iff_toReal_lt hc.ne_top).mp hc
  obtain ⟨q, hcq, hqp⟩ := exists_between hc'
  exact ((ENNReal.lt_ofReal_iff_toReal_lt hc.ne_top).mpr hcq).trans_le <|
    le_iSup₂_of_le q (hp.infinite_setOf_abs_sub_lt_rpow_neg hqp) le_rfl

/-! ### Irrational numbers and almost every real number -/

/-- Every irrational number is a Liouville number with exponent `2`, by Dirichlet's
approximation theorem. -/
theorem _root_.Irrational.liouvilleWith_two {ξ : ℝ} (hξ : Irrational ξ) : LiouvilleWith 2 ξ := by
  refine Set.Infinite.liouvilleWith_of_abs_sub_lt_rpow_neg ?_
  convert Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hξ using 4 with r
  rw [Real.rpow_neg (Nat.cast_nonneg _), one_div, Real.rpow_two]

/-- A real number has irrationality exponent at least two exactly when it is irrational. -/
@[simp]
theorem two_le_irrationalityExponent_iff (ξ : ℝ) :
    2 ≤ irrationalityExponent ξ ↔ Irrational ξ := by
  refine ⟨fun h ↦ irrational_of_one_lt_irrationalityExponent (ENNReal.one_lt_two.trans_le h),
    fun h ↦ ?_⟩
  simpa using le_irrationalityExponent_of_liouvilleWith h.liouvilleWith_two

/-- The irrationality exponent of `ξ` is at most two exactly when `ξ` is not a Liouville number
with any exponent greater than two. -/
theorem irrationalityExponent_le_two_iff (ξ : ℝ) :
    irrationalityExponent ξ ≤ 2 ↔ ∀ p > (2 : ℝ), ¬LiouvilleWith p ξ := by
  rw [irrationalityExponent_le_iff]
  refine forall_congr' fun p ↦ ⟨fun h hp hL ↦ ?_, fun h hL ↦ ?_⟩
  · exact (ENNReal.ofReal_le_ofReal_iff zero_le_two).mp (by simpa using h hL) |>.not_gt hp
  · simpa using ENNReal.ofReal_le_ofReal (not_lt.mp fun hp ↦ h hp hL)

/-- Almost every real number has irrationality exponent two. -/
theorem ae_irrationalityExponent_eq_two : ∀ᵐ ξ : ℝ, irrationalityExponent ξ = 2 := by
  have hirr : ∀ᵐ ξ : ℝ, Irrational ξ :=
    MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
      ((Set.countable_range ((↑) : ℚ → ℝ)).measure_zero _)
  filter_upwards [hirr, ae_not_liouvilleWith] with ξ hξ hL
  exact le_antisymm ((irrationalityExponent_le_two_iff ξ).mpr hL)
    ((two_le_irrationalityExponent_iff ξ).mpr hξ)

end TauCeti
