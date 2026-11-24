/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Real.Irrational
public import TauCeti.Analysis.Convex.Sequence.Asymptotic
public import TauCeti.Analysis.Convex.Sequence.Face
public import TauCeti.Analysis.Convex.Sequence.Interpolation
public import TauCeti.Analysis.Convex.Sequence.SlopeData.Basic

/-!
# Worked lower convex envelopes

Four explicit height sequences on `ℕ` exercise the degenerate and infinite behaviour of
`TauCeti.lowerConvexEnvelope`.

* **Squares.** The heights `n ↦ n ^ 2` are convex, hence their own envelope, with a finite unit
  edge at every index and unit slopes `2 * n + 1`. The piecewise-affine interpolation of these
  heights and `x ↦ x ^ 2` are two different convex functions on `[0, ∞)` taking the same values
  at the natural numbers, so a convex extension of integer heights is not unique.
* **Negative squares.** The heights `n ↦ -n ^ 2` have no real affine lower bound: the sequence is
  vertical. It has no lower convex envelope at all, its lower linear growth is `⊥`, and the total
  function `lowerConvexEnvelope` takes the all-infinite fallback, which is not an envelope of it.
* **Alternating heights.** The heights `0, 1, 0, 1, …` are not convex, and their envelope is the
  horizontal ray of height `0`. It meets the points at every even index, so a terminal ray may
  contact the points infinitely often.
* **Rounded lines.** For a real slope `m`, the integer heights `n ↦ ⌈m * n⌉` have the full line
  `n ↦ m * n` as envelope: a single straight ray with no finite face of slope `m`. For `m = √2`
  this ray has irrational slope although every point has integer height, the points touch it only
  at index `0`, and it admits no rational infinite slope presentation. This contrasts with
  `TauCeti.FiniteSlopeData.existsUnique_rat_heights_eq_iff`, which gives rational presentations
  for envelopes with finite domain and rational heights.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §3.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1.
-/

public section

open Set LinearGrowth

namespace TauCeti.LowerConvexEnvelopeExample

/-! ### Squares -/

/-- The heights `n ↦ n ^ 2`. -/
noncomputable def sqHeights (n : ℕ) : WithTop ℝ :=
  (((n : ℝ) ^ 2 : ℝ) : WithTop ℝ)

/-- The defining formula for the square heights. -/
theorem sqHeights_def (n : ℕ) : sqHeights n = (((n : ℝ) ^ 2 : ℝ) : WithTop ℝ) := (rfl)

/-- Every square height is finite. -/
@[simp] theorem sqHeights_ne_top (n : ℕ) : sqHeights n ≠ ⊤ := WithTop.coe_ne_top

/-- The real value of a square height. -/
@[simp] theorem untop₀_sqHeights (n : ℕ) : (sqHeights n).untop₀ = (n : ℝ) ^ 2 := by
  rw [sqHeights_def, WithTop.untop₀_coe]

/-- Every unit edge of the square heights is finite. -/
@[simp] theorem finiteEdges_sqHeights : finiteEdges sqHeights = univ := by
  ext n
  simp

/-- The unit slope of the square heights at `n` is `2 * n + 1`. -/
@[simp] theorem unitSlope_sqHeights (n : ℕ) : unitSlope sqHeights n = 2 * n + 1 := by
  rw [unitSlope_def, untop₀_sqHeights, untop₀_sqHeights]
  push_cast
  ring

/-- The square heights are convex. -/
theorem isConvexSeq_sqHeights : IsConvexSeq sqHeights :=
  ⟨⟨fun _ _ _ _ _ _ => sqHeights_ne_top _⟩, fun i _ j _ hij => by
    simp only [unitSlope_sqHeights]
    gcongr⟩

/-- The square heights are their own lower convex envelope. -/
@[simp] theorem lowerConvexEnvelope_sqHeights : lowerConvexEnvelope sqHeights = sqHeights :=
  isConvexSeq_sqHeights.lowerConvexEnvelope_eq

/-- The piecewise-affine interpolation of the integer squares is convex on `[0, ∞)`. -/
theorem convexOn_linearInterpolate_sq :
    ConvexOn ℝ (Ici 0) (linearInterpolate fun n : ℕ => (n : ℝ) ^ 2) := by
  have h := isConvexSeq_sqHeights.convexOn_linearInterpolate
  rwa [interpolationDomain_eq_Ici (l := 0) (by simp), Nat.cast_zero,
    funext untop₀_sqHeights] at h

/-- The piecewise-affine interpolation of the integer squares takes the value `1 / 2` at `1 / 2`,
the midpoint of the chord from `(0, 0)` to `(1, 1)`. -/
theorem linearInterpolate_sq_one_half :
    linearInterpolate (fun n : ℕ => (n : ℝ) ^ 2) (1 / 2) = 1 / 2 := by
  have hfloor : ⌊(1 / 2 : ℝ)⌋₊ = 0 := Nat.floor_eq_zero.mpr (by norm_num)
  rw [linearInterpolate_def, hfloor]
  norm_num

/-- The piecewise-affine interpolation of the integer squares and `x ↦ x ^ 2` are different
functions on `[0, ∞)`, although both are convex there (`convexOn_linearInterpolate_sq` and
`convexOn_pow`) and they agree at every natural number (`linearInterpolate_natCast`). -/
theorem not_eqOn_linearInterpolate_sq :
    ¬EqOn (linearInterpolate fun n : ℕ => (n : ℝ) ^ 2) (fun x => x ^ 2) (Ici 0) := by
  intro h
  have := h (show (1 / 2 : ℝ) ∈ Ici 0 by norm_num)
  rw [linearInterpolate_sq_one_half] at this
  norm_num at this

/-! ### Negative squares -/

/-- The heights `n ↦ -n ^ 2`. -/
noncomputable def negSqHeights (n : ℕ) : WithTop ℝ :=
  ((-(n : ℝ) ^ 2 : ℝ) : WithTop ℝ)

/-- The defining formula for the negative square heights. -/
theorem negSqHeights_def (n : ℕ) : negSqHeights n = ((-(n : ℝ) ^ 2 : ℝ) : WithTop ℝ) := (rfl)

/-- The negative square heights are vertical: no real affine line lies below all of them. -/
theorem not_isAdmissible_negSqHeights : ¬IsAdmissible negSqHeights := by
  intro h
  obtain ⟨c, m, hcm⟩ := isAdmissible_iff.mp h
  -- Beyond `|c| + |m|`, the parabola drops below the line.
  set n : ℕ := ⌈|c| + |m|⌉₊ + 1
  have hn : |c| + |m| < n := by
    simp only [n, Nat.cast_add, Nat.cast_one]
    linarith [Nat.le_ceil (|c| + |m|)]
  have hcn := hcm n
  rw [negSqHeights_def, WithTop.coe_le_coe] at hcn
  have hn1 : (1 : ℝ) ≤ n := by
    simp only [n, Nat.cast_add, Nat.cast_one]
    linarith [Nat.cast_nonneg (α := ℝ) ⌈|c| + |m|⌉₊]
  nlinarith [neg_abs_le c, neg_abs_le m, abs_nonneg c, abs_nonneg m]

/-- The negative square heights have no lower convex envelope. In particular the all-infinite
fallback `lowerConvexEnvelope negSqHeights` is not an envelope of them. -/
theorem not_isLowerConvexEnvelope_negSqHeights (h : ℕ → WithTop ℝ) :
    ¬IsLowerConvexEnvelope negSqHeights h :=
  fun hh => not_isAdmissible_negSqHeights hh.isAdmissible

/-- The total envelope of the negative square heights is the all-infinite fallback. -/
@[simp] theorem lowerConvexEnvelope_negSqHeights : lowerConvexEnvelope negSqHeights = ⊤ :=
  lowerConvexEnvelope_of_not_isAdmissible not_isAdmissible_negSqHeights

/-- The negative square heights have lower linear growth `⊥`. -/
theorem linearGrowthInf_negSqHeights :
    linearGrowthInf (fun n => (negSqHeights n).toEReal) = ⊥ := by
  rw [← not_bot_lt_iff, ← isAdmissible_iff_bot_lt_linearGrowthInf]
  exact not_isAdmissible_negSqHeights

/-! ### Alternating heights -/

/-- The heights `0, 1, 0, 1, …`: zero at even and one at odd indices. -/
noncomputable def alternatingHeights (n : ℕ) : WithTop ℝ :=
  if Even n then 0 else 1

/-- The defining formula for the alternating heights. -/
theorem alternatingHeights_def (n : ℕ) :
    alternatingHeights n = if Even n then 0 else 1 := (rfl)

/-- The alternating heights vanish exactly at the even indices. -/
@[simp] theorem alternatingHeights_eq_zero_iff {n : ℕ} : alternatingHeights n = 0 ↔ Even n := by
  by_cases hn : Even n <;> simp [alternatingHeights_def, hn]

/-- Every alternating height is nonnegative. -/
theorem alternatingHeights_nonneg (n : ℕ) : 0 ≤ alternatingHeights n := by
  rw [alternatingHeights_def]
  split_ifs <;> simp

/-- The alternating heights are not convex. -/
theorem not_isConvexSeq_alternatingHeights : ¬IsConvexSeq alternatingHeights := by
  intro h
  have h1 : (1 : WithTop ℝ) ≤ 0 := by
    simpa [alternatingHeights_def] using h.le_max (i := 0) (j := 1) (k := 2) zero_le_one one_le_two
  exact absurd h1 (not_le.mpr zero_lt_one)

/-- The lower convex envelope of the alternating heights is the horizontal ray of height `0`. -/
@[simp] theorem lowerConvexEnvelope_alternatingHeights :
    lowerConvexEnvelope alternatingHeights = 0 := by
  refine (IsLowerConvexEnvelope.eq_lowerConvexEnvelope ⟨?_, alternatingHeights_nonneg, ?_⟩).symm
  · simpa [Pi.zero_def] using isConvexSeq_affine 0 0
  · intro g hg hga n
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    · exact (hga _).trans (alternatingHeights_eq_zero_iff.mpr (even_two_mul k)).le
    -- An odd index lies between two even ones, where `g` is at most `0`.
    · have hle (j : ℕ) : g (2 * j) ≤ 0 :=
        (hga _).trans (alternatingHeights_eq_zero_iff.mpr (even_two_mul j)).le
      refine (hg.le_max (i := 2 * k) (k := 2 * (k + 1)) (by omega) (by omega)).trans ?_
      exact max_le (hle k) (hle (k + 1))

/-- The horizontal ray meets the alternating heights at exactly the even indices, infinitely
often. -/
theorem lowerConvexEnvelope_alternatingHeights_eq_iff {n : ℕ} :
    lowerConvexEnvelope alternatingHeights n = alternatingHeights n ↔ Even n := by
  rw [lowerConvexEnvelope_alternatingHeights, Pi.zero_apply, eq_comm,
    alternatingHeights_eq_zero_iff]

/-- Every unit slope of the envelope of the alternating heights is `0`. -/
theorem unitSlope_lowerConvexEnvelope_alternatingHeights (n : ℕ) :
    unitSlope (lowerConvexEnvelope alternatingHeights) n = 0 := by
  simp [unitSlope_def]

/-! ### Rounded lines and an irrational terminal ray -/

/-- The integer heights `n ↦ ⌈m * n⌉`, rounding the line of slope `m` up. -/
noncomputable def ceilHeights (m : ℝ) (n : ℕ) : WithTop ℝ :=
  (((⌈m * n⌉ : ℤ) : ℝ) : WithTop ℝ)

/-- The defining formula for the rounded heights. -/
theorem ceilHeights_def (m : ℝ) (n : ℕ) :
    ceilHeights m n = (((⌈m * n⌉ : ℤ) : ℝ) : WithTop ℝ) := (rfl)

/-- The rounded heights start at height `0`. -/
@[simp] theorem ceilHeights_zero (m : ℝ) : ceilHeights m 0 = 0 := by
  simp [ceilHeights_def]

/-- A convex minorant of the rounded heights lies below the line of slope `m` through the origin.
The chord from index `0` to a far index `k` has slope at most `m + 1 / k`. -/
private theorem le_mul_of_isConvexSeq_le_ceilHeights {m : ℝ} {g : ℕ → WithTop ℝ}
    (hg : IsConvexSeq g) (hga : g ≤ ceilHeights m) (n : ℕ) :
    g n ≤ ((m * n : ℝ) : WithTop ℝ) := by
  have hfin (k : ℕ) : g k ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (hga k)
  have hbound (k : ℕ) : (g k).untop₀ ≤ ⌈m * k⌉ := by
    have := hga k
    rwa [ceilHeights_def, ← WithTop.coe_untop₀_of_ne_top (hfin k), WithTop.coe_le_coe] at this
  rw [← WithTop.coe_untop₀_of_ne_top (hfin n), WithTop.coe_le_coe]
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  -- Choose a far index `K ≥ n` with `n < K * ε`.
  obtain ⟨k, hk⟩ := exists_nat_gt ((n : ℝ) / ε)
  set K := max k n
  have hKn : (n : ℝ) ≤ K := Nat.cast_le.mpr (le_max_right k n)
  have hKε : (n : ℝ) < K * ε := by
    have : (n : ℝ) < k * ε := (div_lt_iff₀ hε).mp hk
    nlinarith [(Nat.cast_le (α := ℝ)).mpr (le_max_left k n)]
  have hchord := hg.chord_inequality (hfin 0) (hfin K) (Nat.zero_le n) (le_max_right k n)
  have h0 : (g 0).untop₀ ≤ 0 := by simpa using hbound 0
  have hK : (g K).untop₀ < m * K + 1 := (hbound K).trans_lt (Int.ceil_lt_add_one _)
  simp only [Nat.cast_zero, sub_zero] at hchord
  nlinarith [mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr hKn),
    mul_le_mul_of_nonneg_left hK.le (Nat.cast_nonneg (α := ℝ) n)]

/-- The lower convex envelope of the rounded heights `n ↦ ⌈m * n⌉` is the line `n ↦ m * n`. -/
theorem lowerConvexEnvelope_ceilHeights (m : ℝ) :
    lowerConvexEnvelope (ceilHeights m) = fun n : ℕ => ((m * n : ℝ) : WithTop ℝ) := by
  refine (IsLowerConvexEnvelope.eq_lowerConvexEnvelope ⟨?_, fun n => ?_,
    fun g hg hga => le_mul_of_isConvexSeq_le_ceilHeights hg hga⟩).symm
  · simpa using isConvexSeq_affine 0 m
  · rw [ceilHeights_def, WithTop.coe_le_coe]
    exact Int.le_ceil _

/-- Every unit edge of the envelope of the rounded heights is finite. -/
@[simp] theorem finiteEdges_lowerConvexEnvelope_ceilHeights (m : ℝ) :
    finiteEdges (lowerConvexEnvelope (ceilHeights m)) = univ := by
  ext n
  simp only [mem_finiteEdges, lowerConvexEnvelope_ceilHeights, ne_eq, WithTop.coe_ne_top,
    not_false_eq_true, and_self, mem_univ]

/-- Every unit slope of the envelope of the rounded heights is `m`: the envelope is one straight
ray. -/
@[simp] theorem unitSlope_lowerConvexEnvelope_ceilHeights (m : ℝ) (n : ℕ) :
    unitSlope (lowerConvexEnvelope (ceilHeights m)) n = m := by
  simp only [unitSlope_def, lowerConvexEnvelope_ceilHeights, WithTop.untop₀_coe]
  push_cast
  ring

/-- The envelope of the rounded heights has no finite face of slope `m`: the line of slope `m`
through any point of the envelope contains the whole ray. -/
theorem not_isFiniteFace_lowerConvexEnvelope_ceilHeights (m : ℝ) (l u : ℕ) :
    ¬IsFiniteFace (lowerConvexEnvelope (ceilHeights m)) m l u := by
  intro hf
  obtain ⟨hlu, c, -, hface⟩ := isFiniteFace_iff.mp hf
  have hl : l ∈ supportingFace (lowerConvexEnvelope (ceilHeights m)) m c := by
    rw [hface]
    exact ⟨le_rfl, hlu⟩
  simp only [mem_supportingFace, lowerConvexEnvelope_ceilHeights, WithTop.coe_eq_coe] at hl
  have hc : c = 0 := by linarith
  have hu : u + 1 ∈ supportingFace (lowerConvexEnvelope (ceilHeights m)) m c := by
    simp [lowerConvexEnvelope_ceilHeights, hc]
  rw [hface] at hu
  exact absurd hu.2 (Nat.not_succ_le_self u)

/-- The unit slopes of the envelope of the integer heights `n ↦ ⌈√2 * n⌉` are irrational. -/
theorem irrational_unitSlope_lowerConvexEnvelope_ceilHeights_sqrt_two (n : ℕ) :
    Irrational (unitSlope (lowerConvexEnvelope (ceilHeights √2)) n) := by
  rw [unitSlope_lowerConvexEnvelope_ceilHeights]
  exact irrational_sqrt_two

/-- The integer heights `n ↦ ⌈√2 * n⌉` touch the line of slope `√2` through the origin only at
index `0`. -/
theorem supportingFace_ceilHeights_sqrt_two : supportingFace (ceilHeights √2) √2 0 = {0} := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp only [mem_supportingFace, ceilHeights_def, zero_add, WithTop.coe_eq_coe,
      mem_singleton_iff, hn, iff_false]
    exact fun h => (irrational_sqrt_two.mul_natCast hn).ne_int _ h.symm

/-- The envelope of the integer heights `n ↦ ⌈√2 * n⌉` lies on the line of slope `√2` through
the origin at every index. -/
theorem supportingFace_lowerConvexEnvelope_ceilHeights_sqrt_two :
    supportingFace (lowerConvexEnvelope (ceilHeights √2)) √2 0 = univ := by
  ext n
  simp [lowerConvexEnvelope_ceilHeights]

/-- The envelope of the integer heights `n ↦ ⌈√2 * n⌉` has no rational infinite slope
presentation. -/
theorem not_exists_rat_heights_eq_lowerConvexEnvelope_ceilHeights_sqrt_two :
    ¬∃ d : InfiniteSlopeData ℚ, (fun n => WithTop.map ((↑) : ℚ → ℝ) (d.heights n)) =
      lowerConvexEnvelope (ceilHeights √2) := by
  rintro ⟨d, hd⟩
  have h1 := congrFun hd 1
  simp only [lowerConvexEnvelope_ceilHeights, Nat.cast_one, mul_one] at h1
  cases hq : d.heights 1 with
  | top => simp [hq] at h1
  | coe q =>
    rw [hq, WithTop.map_coe, WithTop.coe_eq_coe] at h1
    exact irrational_sqrt_two.ne_rat q h1.symm

end TauCeti.LowerConvexEnvelopeExample
