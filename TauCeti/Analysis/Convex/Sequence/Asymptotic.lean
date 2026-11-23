/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.SlopeData.Basic
public import TauCeti.Analysis.Convex.Sequence.Envelope
public import TauCeti.Data.EReal.Operations
public import Mathlib.Analysis.Asymptotics.LinearGrowth

/-!
# Asymptotic slopes of convex envelopes

For an admissible height sequence whose finite domain is infinite, the lower limit of height
divided by index equals the supremum of the finite unit slopes of its lower convex envelope.
This is the geometric relation between coefficient growth and limiting Newton slopes.
The supremum is taken in `EReal`, so unbounded slopes are included. At positive indices,
missing heights remain infinite under division, and the value at index zero does not affect
the limit.

The key observation is that every slope strictly below the lower limit admits an affine
minorant: a bound on the tail can be extended over the finitely many earlier heights by
lowering the intercept. Conversely, an affine minorant bounds the lower limit from below.
The envelope therefore preserves this lower limit. For a convex sequence on a half-line,
height divided by index actually converges to its supremum of finite slopes. In particular, a
nonnegative sequence vanishing at `0` with nonpositive lower linear growth has the horizontal ray
`0` as its envelope. The growth API is Mathlib’s `LinearGrowth.linearGrowthInf`; no second growth
invariant is defined.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Chapter IV §§3–4.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1.
-/

public section

open Filter Set Finset Topology LinearGrowth

namespace TauCeti

variable {a h : ℕ → WithTop ℝ} {c σ : ℝ}

/-- An affine lower bound on a tail extends to the whole sequence with the same slope,
after possibly lowering its intercept. No admissibility assumption is needed. -/
theorem exists_affine_le_of_eventually_le
    (ha : ∀ᶠ n : ℕ in atTop, ((c + σ * n : ℝ) : WithTop ℝ) ≤ a n) :
    ∃ d : ℝ, ∀ n : ℕ, ((d + σ * n : ℝ) : WithTop ℝ) ≤ a n := by
  let u (n : ℕ) : WithTop ℝ := (a n).map (fun y => y - σ * n)
  have hb : IsBoundedUnder (· ≥ ·) atTop u := by
    refine ⟨(c : WithTop ℝ), ha.mono fun n hn => ?_⟩
    simp only [Set.mem_ofPred_eq]
    by_cases htop : a n = ⊤
    · simp [u, htop]
    · rw [← WithTop.coe_untop₀_of_ne_top htop, WithTop.coe_le_coe] at hn
      dsimp only [u]
      rw [← WithTop.coe_untop₀_of_ne_top htop, WithTop.map_coe]
      exact WithTop.coe_le_coe.mpr (by linarith)
  obtain ⟨d, hd⟩ := hb.bddBelow_range
  refine ⟨d.untopD 0, fun n => ?_⟩
  have hdn := (WithTop.coe_untopD_le d 0).trans (hd (mem_range_self n))
  by_cases htop : a n = ⊤
  · simp [htop]
  · dsimp only [u] at hdn
    rw [← WithTop.coe_untop₀_of_ne_top htop, WithTop.map_coe, WithTop.coe_le_coe] at hdn
    rw [← WithTop.coe_untop₀_of_ne_top htop, WithTop.coe_le_coe]
    linarith

/-- An affine minorant bounds the lower linear growth of the heights from below. -/
theorem le_linearGrowthInf_of_affine_le
    (ha : ∀ n : ℕ, ((c + σ * n : ℝ) : WithTop ℝ) ≤ a n) :
    (σ : EReal) ≤ linearGrowthInf (fun n => (a n).toEReal) := by
  rw [← linearGrowthInf_const_mul_self (a := (σ : EReal))]
  apply linearGrowthInf_le_of_eventually_le (b := ((-c : ℝ) : EReal)) (EReal.coe_ne_top _)
  apply Eventually.of_forall
  intro n
  have hc := add_le_add (WithTop.toEReal_le_toEReal_iff.mpr (ha n)) (le_refl ((-c : ℝ) : EReal))
  have heq : c + σ * n + -c = σ * n := by ring
  simpa only [WithTop.toEReal_coe, ← EReal.coe_add, heq, EReal.coe_mul,
    EReal.coe_natCast] using hc

/-- Every real slope strictly below the lower linear growth has an affine minorant.
The strict inequality is necessary at a convergence boundary. -/
theorem exists_affine_le_of_lt_linearGrowthInf
    (hσ : (σ : EReal) < linearGrowthInf (fun n => (a n).toEReal)) :
    ∃ c : ℝ, ∀ n : ℕ, ((c + σ * n : ℝ) : WithTop ℝ) ≤ a n := by
  apply exists_affine_le_of_eventually_le (c := 0)
  filter_upwards [eventually_mul_le hσ] with n hn
  rw [zero_add]
  apply WithTop.toEReal_le_toEReal_iff.mp
  simpa only [WithTop.toEReal_coe, EReal.coe_mul, EReal.coe_natCast] using hn

/-- A height sequence is admissible exactly when its lower linear growth is not negative
infinity. Thus a vertical sequence is precisely one with lower linear growth `⊥`. -/
theorem isAdmissible_iff_bot_lt_linearGrowthInf :
    IsAdmissible a ↔ ⊥ < linearGrowthInf (fun n => (a n).toEReal) := by
  constructor
  · intro ha
    obtain ⟨c, σ, hc⟩ := isAdmissible_iff.mp ha
    exact (EReal.bot_lt_coe σ).trans_le (le_linearGrowthInf_of_affine_le hc)
  · intro ha
    obtain ⟨σ, _, hσ⟩ := EReal.exists_between_coe_real ha
    obtain ⟨c, hc⟩ := exists_affine_le_of_lt_linearGrowthInf hσ
    exact isAdmissible_iff.mpr ⟨c, σ, hc⟩

/-- Taking a lower convex envelope preserves the lower limit of height divided by index,
including positive infinity and sequences with finite support. -/
theorem IsLowerConvexEnvelope.linearGrowthInf_eq (hh : IsLowerConvexEnvelope a h) :
    linearGrowthInf (fun n => (h n).toEReal) =
      linearGrowthInf (fun n => (a n).toEReal) := by
  apply le_antisymm
  · exact linearGrowthInf_monotone fun n => WithTop.toEReal_le_toEReal_iff.mpr (hh.le n)
  · by_contra hlt
    obtain ⟨σ, hσh, hσa⟩ := EReal.exists_between_coe_real (lt_of_not_ge hlt)
    obtain ⟨c, hc⟩ := exists_affine_le_of_lt_linearGrowthInf hσa
    have hch := hh.greatest (isConvexSeq_affine c σ) hc
    exact (not_le_of_gt hσh) (le_linearGrowthInf_of_affine_le hch)

/-- Height divided by index on an infinite convex polygon converges to the supremum of
its genuine finite unit slopes, allowing positive infinity. No endpoint sentinel participates. -/
theorem IsConvexSeq.tendsto_div_iSup_unitSlope (hh : IsConvexSeq h)
    (hinf : {n | h n ≠ ⊤}.Infinite) :
    Tendsto (fun n : ℕ => (h n).toEReal / n) atTop
      (𝓝 (⨆ i : finiteEdges h, (unitSlope h i : EReal))) := by
  obtain ⟨d, hd⟩ := InfiniteSlopeData.exists_heights_eq_iff.mpr ⟨hh, hinf⟩
  let l := d.start
  have hdom (n : ℕ) : h n ≠ ⊤ ↔ l ≤ n := by
    rw [← hd, d.heights_ne_top_iff]
  refine tendsto_of_le_liminf_of_limsup_le ?_ ?_
  · apply iSup_le
    intro i
    obtain ⟨hi, hi'⟩ := mem_finiteEdges.mp i.property
    have hline := hh.supportingLine_le hi hi'
    apply le_linearGrowthInf_of_affine_le (c := (h i).untop₀ - (i : ℝ) * unitSlope h i)
    intro n
    convert hline n using 1; congr 1; ring
  · by_contra hlt
    obtain ⟨σ, hsσ, hσlim⟩ := EReal.exists_between_coe_real (lt_of_not_ge hlt)
    have hslopes (i : ℕ) (hi : i ∈ finiteEdges h) : unitSlope h i ≤ σ := by
      apply EReal.coe_le_coe_iff.mp
      exact (le_iSup (fun j : finiteEdges h => (unitSlope h j : EReal)) ⟨i, hi⟩).trans hsσ.le
    have hupper : ∀ᶠ n : ℕ in atTop,
        (h n).toEReal ≤ (σ : EReal) * n + ((h l).untop₀ - σ * l : ℝ) := by
      filter_upwards [eventually_ge_atTop l] with n hln
      have hnf := (hdom n).mpr hln
      have hsum : ∑ i ∈ Ico l n, unitSlope h i ≤ ((n - l : ℕ) : ℝ) * σ := by
        calc
          _ ≤ ∑ _i ∈ Ico l n, σ := sum_le_sum fun i hi =>
            hslopes i (mem_finiteEdges.mpr ⟨(hdom i).mpr (mem_Ico.mp hi).1,
              (hdom (i + 1)).mpr (by have := (mem_Ico.mp hi).1; omega)⟩)
          _ = _ := by simp
      have heq := eq_coe_add_sum_unitSlope hnf hln
      have hval := congrArg WithTop.untop₀ heq
      simp only [WithTop.untop₀_coe] at hval
      rw [Nat.cast_sub hln] at hsum
      rw [← WithTop.coe_untop₀_of_ne_top hnf, WithTop.toEReal_coe,
        ← EReal.coe_natCast, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
      linarith
    have hle := linearGrowthSup_le_of_eventually_le (EReal.coe_ne_top _) hupper
    rw [linearGrowthSup_const_mul_self] at hle
    exact (not_le_of_gt hσlim) hle

/-- The asymptotic coefficient growth of an admissible, infinitely supported sequence
equals the supremum of the finite slopes of its lower convex envelope. -/
theorem linearGrowthInf_eq_iSup_unitSlope_lowerConvexEnvelope (ha : IsAdmissible a)
    (hinf : {n | a n ≠ ⊤}.Infinite) :
    linearGrowthInf (fun n => (a n).toEReal) =
      ⨆ i : finiteEdges (lowerConvexEnvelope a),
        (unitSlope (lowerConvexEnvelope a) i : EReal) := by
  have hh := isLowerConvexEnvelope_lowerConvexEnvelope ha
  rw [← hh.linearGrowthInf_eq]
  exact (hh.isConvexSeq.tendsto_div_iSup_unitSlope
    (hinf.mono fun n hn => ne_top_of_le_ne_top hn (hh.le n))).liminf_eq

/-- A nonnegative height sequence that vanishes at `0` and has nonpositive lower linear growth
has the identically zero sequence as its lower convex envelope: an infinite horizontal ray. A
convex minorant that is at most `0` at `0` and positive at `n` grows at least linearly with slope
`g n / n` beyond `n`, which the growth bound forbids. -/
theorem isLowerConvexEnvelope_zero_of_linearGrowthInf_nonpos (h0 : a 0 = 0) (hnonneg : 0 ≤ a)
    (hgrowth : linearGrowthInf (fun n => (a n).toEReal) ≤ 0) :
    IsLowerConvexEnvelope a 0 := by
  refine ⟨by simpa [Pi.zero_def] using isConvexSeq_affine 0 0, hnonneg, fun g hg hga n => ?_⟩
  rw [Pi.zero_apply]
  by_contra hlt
  rw [not_le] at hlt
  have hg0 : g 0 ≠ ⊤ := ne_top_of_le_ne_top (by rw [h0]; exact WithTop.zero_ne_top) (hga 0)
  have hg0le : (g 0).untop₀ ≤ 0 := by
    have h := hga 0
    rwa [h0, ← WithTop.coe_untop₀_of_ne_top hg0, ← WithTop.coe_zero, WithTop.coe_le_coe] at h
  have hn : (0 : ℝ) < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact absurd ((hga 0).trans_eq h0) (not_le_of_gt hlt)
    · exact_mod_cast hn
  -- Beyond `n`, the minorant lies above a line of positive slope `σ` through the origin.
  obtain ⟨σ, hσ, hσm⟩ : ∃ σ : ℝ, 0 < σ ∧ ∀ m, n ≤ m → g m ≠ ⊤ → σ * m ≤ (g m).untop₀ := by
    by_cases hgn : g n = ⊤
    · exact ⟨1, one_pos, fun m hm hgm =>
        absurd hgn (hg.ne_top_of_le_of_le hg0 hgm (Nat.zero_le n) hm)⟩
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hgn
    have htpos : 0 < t := by rwa [← ht, ← WithTop.coe_zero, WithTop.coe_lt_coe] at hlt
    refine ⟨t / n, div_pos htpos hn, fun m hm hgm => ?_⟩
    have hchord := hg.chord_inequality hg0 hgm (Nat.zero_le n) hm
    rw [← ht, WithTop.untop₀_coe] at hchord
    push_cast at hchord
    have hmn : (n : ℝ) ≤ m := by exact_mod_cast hm
    have h1 : ((m : ℝ) - n) * (g 0).untop₀ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) hg0le
    rw [div_mul_eq_mul_div, div_le_iff₀ hn]
    linarith
  have hline : ∀ᶠ m : ℕ in atTop, ((0 + σ * m : ℝ) : WithTop ℝ) ≤ a m := by
    filter_upwards [eventually_ge_atTop n] with m hm
    refine le_trans ?_ (hga m)
    by_cases hgm : g m = ⊤
    · simp [hgm]
    rw [← WithTop.coe_untop₀_of_ne_top hgm, WithTop.coe_le_coe, zero_add]
    exact hσm m hm hgm
  obtain ⟨d, hd⟩ := exists_affine_le_of_eventually_le hline
  exact (not_le_of_gt hσ) (EReal.coe_le_coe_iff.mp
    ((le_linearGrowthInf_of_affine_le hd).trans hgrowth))

end TauCeti
