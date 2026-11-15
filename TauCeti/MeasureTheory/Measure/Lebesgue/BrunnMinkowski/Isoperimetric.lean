/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.Analysis.BoundedVariation.ParallelVolume
public import TauCeti.MeasureTheory.Measure.Lebesgue.BrunnMinkowski.Parallel
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.BoundedVariation.Ball
import TauCeti.Analysis.BoundedVariation.Convex
import TauCeti.Analysis.BoundedVariation.Isoperimetric
import TauCeti.Analysis.Convex.Measure
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.Lebesgue.EssentialConvexity
import TauCeti.MeasureTheory.Measure.Lebesgue.Steiner.Equality

/-!
# The isoperimetric inequality for convex bodies and unconditional ball rigidity

Let `K` be a convex body of positive volume `V` in a Euclidean space of dimension `n ≥ 1`, and
write `ω_n = volume (ball 0 1)` and `P(K)` for the perimeter of `K` in the whole space. Then

`P(K)^n ≥ n^n ω_n V^(n-1)`

(`ConvexBody.finrank_pow_mul_volume_ball_mul_volume_pow_le_perimeter_pow`), with equality exactly
when `K` is a closed ball of positive radius
(`ConvexBody.perimeter_pow_eq_iff_exists_eq_closedBall`). Balls have equality by
`TauCeti.perimeter_ball_pow`, which fixes the constant.

The perimeter is the first variation of parallel volume: the volume of `K + t • closedBall 0 1`
has right derivative `P(K)` at `t = 0` (`Convex.hasDerivWithinAt_measureReal_add_smul_closedBall`).
Hence its `n`-th root has right derivative `P(K) / (n V^(1 - 1/n))`
(`ConvexBody.hasDerivWithinAt_volume_real_add_smul_closedBall_rpow`). By the Brunn–Minkowski
inequality this root is concave and bounded below by `V^(1/n) + t ω_n^(1/n)`, so the derivative is
at least `ω_n^(1/n)` (`ConvexBody.volume_real_rpow_le_of_hasDerivWithinAt`), which is the
inequality, in the real-valued form `n ω_n^(1/n) V^(1 - 1/n) ≤ P(K)`
(`ConvexBody.mul_volume_real_rpow_mul_le_perimeter_toReal`). The derivative equals `ω_n^(1/n)`
exactly when `K` is a closed ball
(`ConvexBody.hasDerivWithinAt_volume_real_add_smul_closedBall_rpow_iff_exists_eq_closedBall`),
which is the equality case.

For a positive finite-volume set that agrees almost everywhere with a convex set, the
compact-convex equality theorem is transported using
`MeasureTheory.Measure.exists_isCompact_convex_ae_eq` and a.e. invariance of perimeter.
The nullity of spheres converts its closed-ball conclusion into open-ball a.e. equality.
No boundedness, closedness or regularity of the supplied representative is required.
The interval-section version applies essential convexity: in each unit direction almost
every line section must agree a.e. with an interval. The exceptional transverse null set
may depend on the direction. This separates the geometric rigidity argument from the
problem of obtaining interval sections from equality in a perimeter comparison.

Combining this interval-section criterion with the sharp Euclidean isoperimetric inequality
(`MeasureTheory.NullMeasurableSet.finrank_pow_mul_volume_ball_mul_volume_pow_le_perimeter_pow`),
perimeter monotonicity under Steiner symmetrization (`TauCeti.perimeter_steinerSymmetrization_le`),
and interval-section rigidity for Steiner perimeter equality
(`TauCeti.ae_lineSection_ordConnected_of_perimeter_steinerSymmetrization_eq`) yields unconditional
isoperimetric rigidity (`MeasureTheory.NullMeasurableSet.perimeter_pow_eq_iff_exists_ae_eq_ball`):
if a null-measurable set `s` of finite positive volume in dimension `n ≥ 1` satisfies
`P(s)^n = n^n ω_n |s|^(n-1)`, then every Steiner symmetral `S_e s` has the same volume and
perimeter at most `P(s)`, hence also attains the isoperimetric lower bound, forcing
`P(S_e s) = P(s)` and therefore interval sections in every unit direction `e`, so `s` agrees almost
everywhere with an open ball of positive radius. Companion equivalences give the real-valued form
(`MeasureTheory.NullMeasurableSet.perimeter_toReal_eq_iff_exists_ae_eq_ball`), the zero-perimeter
characterization (`MeasureTheory.NullMeasurableSet.perimeter_eq_zero_iff`), and the `n ≥ 2` form
allowing sets of volume zero
(`MeasureTheory.NullMeasurableSet.perimeter_pow_eq_iff_volume_eq_zero_or_exists_ae_eq_ball`).

## References

* R. Schneider, *Convex Bodies: The Brunn–Minkowski Theory*, 2nd ed., Cambridge University
  Press, 2014, Section 7.2, for the isoperimetric inequality as a case of Minkowski's first
  inequality.
* R. J. Gardner, *The Brunn–Minkowski inequality*, Bull. Amer. Math. Soc. **39** (2002),
  355–405, Section 5.
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Cambridge
  University Press, 2012, Chapters 13 and 14.
* M. Chlebík, A. Cianchi, N. Fusco, *The perimeter inequality under Steiner symmetrization: cases
  of equality*, Ann. of Math. (2) **162** (2005), 525–555.
* F. Cagnetti, M. Colombo, G. De Philippis, F. Maggi, *Rigidity of equality cases in Steiner's
  perimeter inequality*, Anal. PDE **7** (2014), 1677–1737.
-/

public section

open MeasureTheory Metric Module Set TauCeti
open scoped ENNReal Pointwise

namespace ConvexBody

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **The first variation of the parallel volume root of a convex body.** For a convex body `K`
of positive volume `V` in dimension `n`, the function
`t ↦ volume (K + t • closedBall 0 1) ^ (1 / n)` has right derivative `P(K) / (n V ^ (1 - 1 / n))`
at zero, where `P(K)` is the perimeter of `K`. -/
theorem hasDerivWithinAt_volume_real_add_smul_closedBall_rpow (K : ConvexBody E)
    (hK : volume (K : Set E) ≠ 0) :
    HasDerivWithinAt (fun t : ℝ ↦
      volume.real ((K : Set E) + t • closedBall (0 : E) 1) ^ (finrank ℝ E : ℝ)⁻¹)
      ((perimeter volume ⊤ (K : Set E)).toReal /
        (finrank ℝ E * volume.real (K : Set E) ^ (1 - (finrank ℝ E : ℝ)⁻¹))) (Ioi 0) 0 := by
  have hKi := (K.convex.addHaar_pos_iff_interior_nonempty (μ := volume)).1 (pos_iff_ne_zero.2 hK)
  have hf := (K.convex.hasDerivWithinAt_measureReal_add_smul_closedBall (μ := volume) K.isCompact
    hKi).mono Ioi_subset_Ici_self
  have h0 : volume.real ((K : Set E) + (0 : ℝ) • closedBall (0 : E) 1) =
      volume.real (K : Set E) := by
    rw [zero_smul_set (nonempty_closedBall.2 zero_le_one), add_zero]
  have hV : 0 < volume.real (K : Set E) :=
    ENNReal.toReal_pos hK K.isCompact.measure_lt_top.ne
  convert HasDerivWithinAt.rpow_const hf (p := (finrank ℝ E : ℝ)⁻¹) (Or.inl (h0 ▸ hV.ne'))
    using 1
  rw [h0, div_eq_mul_inv, mul_inv, ← Real.rpow_neg hV.le, neg_sub]
  ring

/-- **The isoperimetric inequality for convex bodies, in real-valued form.** In dimension
`n ≥ 1`, a convex body `K` of positive volume `V` satisfies `n ω_n^(1/n) V^(1 - 1/n) ≤ P(K)`,
where `ω_n = volume (ball 0 1)`. The case `n = 0` is trivial, as the left side vanishes. -/
theorem mul_volume_real_rpow_mul_le_perimeter_toReal (K : ConvexBody E)
    (hK : volume (K : Set E) ≠ 0) :
    finrank ℝ E * volume.real (ball (0 : E) 1) ^ (finrank ℝ E : ℝ)⁻¹ *
        volume.real (K : Set E) ^ (1 - (finrank ℝ E : ℝ)⁻¹) ≤
      (perimeter volume ⊤ (K : Set E)).toReal := by
  rcases eq_or_ne (finrank ℝ E) 0 with hn | hn
  · simp [hn]
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hn)
  let B : ConvexBody E := ⟨closedBall 0 1, convex_closedBall 0 1, isCompact_closedBall 0 1,
    nonempty_closedBall.2 zero_le_one⟩
  have hB : (B : Set E) = closedBall 0 1 := ConvexBody.coe_mk _ _ _ _
  have hV : 0 < volume.real (K : Set E) :=
    ENNReal.toReal_pos hK K.isCompact.measure_lt_top.ne
  have h := K.volume_real_rpow_le_of_hasDerivWithinAt B hn
    (hB ▸ K.hasDerivWithinAt_volume_real_add_smul_closedBall_rpow hK)
  rw [hB, Measure.addHaar_real_closedBall_eq_addHaar_real_ball, le_div_iff₀ (by positivity)] at h
  linarith

/-- **The isoperimetric inequality for convex bodies.** In dimension `n ≥ 1`, a convex body `K`
of positive volume satisfies `P(K)^n ≥ n^n ω_n |K|^(n-1)`, where `ω_n = volume (ball 0 1)`. -/
theorem finrank_pow_mul_volume_ball_mul_volume_pow_le_perimeter_pow (K : ConvexBody E)
    (hn : finrank ℝ E ≠ 0) (hK : volume (K : Set E) ≠ 0) :
    (finrank ℝ E : ℝ≥0∞) ^ finrank ℝ E * volume (ball (0 : E) 1) *
        volume (K : Set E) ^ (finrank ℝ E - 1) ≤
      perimeter volume ⊤ (K : Set E) ^ finrank ℝ E := by
  have hP : perimeter volume ⊤ (K : Set E) ≠ ⊤ :=
    (K.convex.perimeter_lt_top K.isCompact.isBounded).ne
  rw [finrank_pow_mul_volume_ball_mul_volume_pow_eq_ofReal K.isCompact.measure_lt_top.ne hn,
    ← ENNReal.ofReal_toReal hP, ← ENNReal.ofReal_pow ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_le_ofReal
    (pow_le_pow_left₀ (by positivity) (K.mul_volume_real_rpow_mul_le_perimeter_toReal hK) _)

/-- **Equality in the isoperimetric inequality for convex bodies.** In dimension `n ≥ 1`, a
convex body `K` of positive volume satisfies `P(K)^n = n^n ω_n |K|^(n-1)`, where
`ω_n = volume (ball 0 1)`, exactly when it is a closed ball of positive radius. -/
theorem perimeter_pow_eq_iff_exists_eq_closedBall (K : ConvexBody E)
    (hn : finrank ℝ E ≠ 0) (hK : volume (K : Set E) ≠ 0) :
    perimeter volume ⊤ (K : Set E) ^ finrank ℝ E =
        (finrank ℝ E : ℝ≥0∞) ^ finrank ℝ E * volume (ball (0 : E) 1) *
          volume (K : Set E) ^ (finrank ℝ E - 1) ↔
      ∃ c : E, ∃ r : ℝ, 0 < r ∧ (K : Set E) = closedBall c r := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hn)
  have hP : perimeter volume ⊤ (K : Set E) ≠ ⊤ :=
    (K.convex.perimeter_lt_top K.isCompact.isBounded).ne
  have hV : 0 < volume.real (K : Set E) :=
    ENNReal.toReal_pos hK K.isCompact.measure_lt_top.ne
  have hd := K.hasDerivWithinAt_volume_real_add_smul_closedBall_rpow hK
  rw [← K.hasDerivWithinAt_volume_real_add_smul_closedBall_rpow_iff_exists_eq_closedBall hn hK,
    Measure.addHaar_real_closedBall_eq_addHaar_real_ball,
    finrank_pow_mul_volume_ball_mul_volume_pow_eq_ofReal K.isCompact.measure_lt_top.ne hn,
    ← ENNReal.ofReal_toReal hP,
    ← ENNReal.ofReal_pow ENNReal.toReal_nonneg,
    ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity),
    pow_left_inj₀ ENNReal.toReal_nonneg (by positivity) hn]
  refine ⟨fun h => hd.congr_deriv ?_, fun h => ?_⟩
  · rw [div_eq_iff (by positivity), h]
    ring
  · have := (uniqueDiffWithinAt_Ioi 0).eq_deriv _ hd h
    rw [div_eq_iff (by positivity)] at this
    rw [this]
    ring

end ConvexBody

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {s : Set E}

/-- **Isoperimetric rigidity for essentially convex sets.** In positive dimension, a set
of positive finite volume that agrees a.e. with a convex set attains the sharp perimeter
bound exactly when it agrees a.e. with an open ball of positive radius. In particular,
null modifications of convex sets need not themselves be balls. -/
theorem perimeter_pow_eq_iff_exists_ae_eq_ball_of_ae_eq_convex
    (hn : finrank ℝ E ≠ 0) (hpos : 0 < volume s) (hfin : volume s ≠ ∞)
    (hc : ∃ C : Set E, Convex ℝ C ∧ s =ᵐ[volume] C) :
    perimeter volume ⊤ s ^ finrank ℝ E =
        (finrank ℝ E : ℝ≥0∞) ^ finrank ℝ E * volume (ball (0 : E) 1) *
          volume s ^ (finrank ℝ E - 1) ↔
      ∃ c : E, ∃ r : ℝ, 0 < r ∧ s =ᵐ[volume] ball c r := by
  constructor
  · intro heq
    obtain ⟨K, hK, hKc, hKi, hsK⟩ := volume.exists_isCompact_convex_ae_eq hpos hfin hc
    let B : ConvexBody E := ⟨K, hKc, hK, hKi.mono interior_subset⟩
    have hB : (B : Set E) = K := ConvexBody.coe_mk _ _ _ _
    have hvol : volume (B : Set E) = volume s := by
      rw [hB]
      exact (measure_congr hsK).symm
    have hper : perimeter volume ⊤ (B : Set E) = perimeter volume ⊤ s := by
      rw [hB]
      exact (perimeter_congr_ae (ae_restrict_of_ae hsK)).symm
    obtain ⟨c, r, hr, hBr⟩ := (B.perimeter_pow_eq_iff_exists_eq_closedBall hn
      (hvol ▸ hpos.ne')).mp (by simpa only [hvol, hper] using heq)
    refine ⟨c, r, hr, hsK.trans ?_⟩
    rw [← hB, hBr]
    exact volume.addHaar_closedBall_ae_eq_ball_of_ne_zero c r hr.ne'
  · rintro ⟨c, r, hr, hsr⟩
    rw [perimeter_congr_ae (ae_restrict_of_ae hsr), measure_congr hsr]
    exact perimeter_ball_pow hn hr

end TauCeti

namespace MeasureTheory.NullMeasurableSet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {s : Set E}

/-- **Isoperimetric rigidity from interval sections.** For a positive finite-volume
Lebesgue-measurable set, suppose that in every unit direction almost every line section
agrees a.e. with an interval. Then equality in the sharp perimeter inequality is equivalent
to agreement a.e. with an open ball of positive radius. -/
theorem perimeter_pow_eq_iff_exists_ae_eq_ball_of_ae_lineSection_ordConnected
    (hs : NullMeasurableSet s volume) (hn : finrank ℝ E ≠ 0)
    (hpos : 0 < volume s) (hfin : volume s ≠ ∞)
    (hsections : ∀ e : E, ‖e‖ = 1 → ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume,
      ∃ I : Set ℝ, I.OrdConnected ∧ {t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I) :
    TauCeti.perimeter volume ⊤ s ^ finrank ℝ E =
        (finrank ℝ E : ℝ≥0∞) ^ finrank ℝ E * volume (ball (0 : E) 1) *
          volume s ^ (finrank ℝ E - 1) ↔
      ∃ c : E, ∃ r : ℝ, 0 < r ∧ s =ᵐ[volume] ball c r :=
  TauCeti.perimeter_pow_eq_iff_exists_ae_eq_ball_of_ae_eq_convex hn hpos hfin
    (TauCeti.exists_convex_ae_eq_of_ae_lineSection_ordConnected hs hsections)

/-- **Sets of finite volume and perimeter zero in positive dimension.** In dimension `n ≥ 1`, a
null-measurable set `s` of finite volume has perimeter zero if and only if it has volume zero. Both
hypotheses are necessary: in dimension `0` the singleton `{0}` has perimeter zero and volume one,
while in positive dimension `univ` has perimeter zero and infinite volume. -/
theorem perimeter_eq_zero_iff (hs : NullMeasurableSet s volume) (hn : finrank ℝ E ≠ 0)
    (hfin : volume s ≠ ∞) :
    perimeter volume ⊤ s = 0 ↔ volume s = 0 := by
  refine ⟨fun h0 => ?_, fun hv => ?_⟩
  · by_contra hne
    have : Nontrivial E := Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hn)
    have hle := hs.ofReal_mul_volume_real_rpow_mul_le_perimeter hfin hne
    rw [h0, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hle
    have hB : 0 < volume.real (ball (0 : E) 1) :=
      ENNReal.toReal_pos (Metric.measure_ball_pos volume (0 : E) one_pos).ne'
        measure_ball_lt_top.ne
    have hV : 0 < volume.real s := ENNReal.toReal_pos hne hfin
    have hpos' : 0 < finrank ℝ E * volume.real (ball (0 : E) 1) ^ (finrank ℝ E : ℝ)⁻¹ *
        volume.real s ^ (1 - (finrank ℝ E : ℝ)⁻¹) := by positivity
    linarith
  · rw [perimeter_congr_ae (ae_restrict_of_ae (ae_eq_empty.2 hv)), perimeter_empty]

/-- **Unconditional rigidity in the sharp Euclidean isoperimetric inequality.** In a
finite-dimensional real inner product space `E` of dimension `n ≥ 1`, a null-measurable set `s` of
finite positive volume satisfies `P(s)^n = n^n ω_n |s|^(n-1)`, where `ω_n = volume (ball 0 1)`, if
and only if `s` agrees almost everywhere with an open ball of positive radius. No boundedness,
connectedness, convexity, or boundary regularity is assumed on `s`. -/
theorem perimeter_pow_eq_iff_exists_ae_eq_ball (hs : NullMeasurableSet s volume)
    (hn : finrank ℝ E ≠ 0) (hpos : 0 < volume s) (hfin : volume s ≠ ∞) :
    perimeter volume ⊤ s ^ finrank ℝ E =
        (finrank ℝ E : ℝ≥0∞) ^ finrank ℝ E * volume (ball (0 : E) 1) *
          volume s ^ (finrank ℝ E - 1) ↔
      ∃ c : E, ∃ r : ℝ, 0 < r ∧ s =ᵐ[volume] ball c r := by
  refine ⟨fun heq => ?_, ?_⟩
  · have hP : perimeter volume ⊤ s ≠ ∞ := fun htop => by
      rw [htop, ENNReal.top_pow hn,
        finrank_pow_mul_volume_ball_mul_volume_pow_eq_ofReal hfin hn] at heq
      exact ENNReal.ofReal_ne_top heq.symm
    refine (hs.perimeter_pow_eq_iff_exists_ae_eq_ball_of_ae_lineSection_ordConnected
      hn hpos hfin fun e he => ?_).mp heq
    set S := steinerSymmetrization e he s
    have hSm : NullMeasurableSet S volume := nullMeasurableSet_steinerSymmetrization e he hs
    have hSvol : volume S = volume s := volume_steinerSymmetrization e he hs
    have hle : perimeter volume ⊤ S ≤ perimeter volume ⊤ s :=
      perimeter_steinerSymmetrization_le e he hs hfin
    have hPS : perimeter volume ⊤ S ≠ ∞ := ne_top_of_le_ne_top hP hle
    have hpow_le : perimeter volume ⊤ s ^ finrank ℝ E ≤ perimeter volume ⊤ S ^ finrank ℝ E := by
      rw [heq, ← hSvol]
      exact hSm.finrank_pow_mul_volume_ball_mul_volume_pow_le_perimeter_pow
        (hSvol.trans_ne hfin) (hSvol.trans_ne hpos.ne')
    have hge : perimeter volume ⊤ s ≤ perimeter volume ⊤ S := by
      rw [← ENNReal.toReal_le_toReal hP hPS,
        ← pow_le_pow_iff_left₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg hn,
        ← ENNReal.toReal_pow, ← ENNReal.toReal_pow]
      exact ENNReal.toReal_mono (ENNReal.pow_ne_top hPS) hpow_le
    exact ae_lineSection_ordConnected_of_perimeter_steinerSymmetrization_eq e he hs hfin hP
      (le_antisymm hle hge)
  · rintro ⟨c, r, hr, hsr⟩
    rw [perimeter_congr_ae (ae_restrict_of_ae hsr), measure_congr hsr]
    exact perimeter_ball_pow hn hr

/-- **Equality in the sharp Euclidean isoperimetric inequality in dimension `n ≥ 2`.** In dimension
`n ≥ 2`, a null-measurable set `s` of finite volume satisfies `P(s)^n = n^n ω_n |s|^(n-1)` if and
only if either `s` has volume zero or `s` agrees almost everywhere with an open ball of positive
radius. The hypothesis `2 ≤ n` is needed because for `n = 1` a null set has `P(s)^1 = 0` whereas
`1^1 ω_1 |s|^0 = 2`. -/
theorem perimeter_pow_eq_iff_volume_eq_zero_or_exists_ae_eq_ball (hs : NullMeasurableSet s volume)
    (hn : 2 ≤ finrank ℝ E) (hfin : volume s ≠ ∞) :
    perimeter volume ⊤ s ^ finrank ℝ E =
        (finrank ℝ E : ℝ≥0∞) ^ finrank ℝ E * volume (ball (0 : E) 1) *
          volume s ^ (finrank ℝ E - 1) ↔
      volume s = 0 ∨ ∃ c : E, ∃ r : ℝ, 0 < r ∧ s =ᵐ[volume] ball c r := by
  have hn0 : finrank ℝ E ≠ 0 := by omega
  have hn1 : finrank ℝ E - 1 ≠ 0 := by omega
  rcases eq_or_ne (volume s) 0 with hv | hv
  · simp [(hs.perimeter_eq_zero_iff hn0 hfin).2 hv, hv, zero_pow hn0, zero_pow hn1]
  · rw [or_iff_right hv]
    exact hs.perimeter_pow_eq_iff_exists_ae_eq_ball hn0 (pos_iff_ne_zero.2 hv) hfin

/-- **Equality in the real-valued sharp Euclidean isoperimetric inequality.** In dimension `n ≥ 1`,
a null-measurable set `s` of finite positive volume satisfies
`(perimeter volume ⊤ s).toReal = n ω_n^(1/n) |s|^(1 - 1/n)` if and only if `s` agrees almost
everywhere with an open ball of positive radius (when `perimeter volume ⊤ s = ∞`, `.toReal` is `0`
while the right-hand side is strictly positive, so no finiteness hypothesis on perimeter is
needed). -/
theorem perimeter_toReal_eq_iff_exists_ae_eq_ball (hs : NullMeasurableSet s volume)
    (hn : finrank ℝ E ≠ 0) (hpos : 0 < volume s) (hfin : volume s ≠ ∞) :
    (perimeter volume ⊤ s).toReal =
        finrank ℝ E * volume.real (ball (0 : E) 1) ^ (finrank ℝ E : ℝ)⁻¹ *
          volume.real s ^ (1 - (finrank ℝ E : ℝ)⁻¹) ↔
      ∃ c : E, ∃ r : ℝ, 0 < r ∧ s =ᵐ[volume] ball c r := by
  rcases eq_or_ne (perimeter volume ⊤ s) ∞ with htop | hP
  · have : Nontrivial E := Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hn)
    have hB : 0 < volume.real (ball (0 : E) 1) :=
      ENNReal.toReal_pos (Metric.measure_ball_pos volume (0 : E) one_pos).ne'
        measure_ball_lt_top.ne
    have hV : 0 < volume.real s := ENNReal.toReal_pos hpos.ne' hfin
    have hrhs : 0 < finrank ℝ E * volume.real (ball (0 : E) 1) ^ (finrank ℝ E : ℝ)⁻¹ *
        volume.real s ^ (1 - (finrank ℝ E : ℝ)⁻¹) := by positivity
    refine ⟨fun h => ?_, fun hball => ?_⟩
    · rw [htop, ENNReal.toReal_top] at h
      linarith
    · have hpow := (hs.perimeter_pow_eq_iff_exists_ae_eq_ball hn hpos hfin).2 hball
      rw [htop, ENNReal.top_pow hn,
        finrank_pow_mul_volume_ball_mul_volume_pow_eq_ofReal hfin hn] at hpow
      exact absurd hpow.symm ENNReal.ofReal_ne_top
  · rw [← hs.perimeter_pow_eq_iff_exists_ae_eq_ball hn hpos hfin,
      finrank_pow_mul_volume_ball_mul_volume_pow_eq_ofReal hfin hn,
      ← ENNReal.ofReal_toReal hP,
      ← ENNReal.ofReal_pow ENNReal.toReal_nonneg,
      ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity),
      pow_left_inj₀ ENNReal.toReal_nonneg (by positivity) hn,
      ENNReal.toReal_ofReal ENNReal.toReal_nonneg]

end MeasureTheory.NullMeasurableSet
