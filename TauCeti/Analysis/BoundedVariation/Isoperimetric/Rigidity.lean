/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
public import TauCeti.MeasureTheory.Measure.Lebesgue.Steiner.Basic
import TauCeti.Analysis.BoundedVariation.Ball
import TauCeti.Analysis.BoundedVariation.Isoperimetric.Basic
import TauCeti.MeasureTheory.Measure.Lebesgue.BrunnMinkowski.Isoperimetric
import TauCeti.MeasureTheory.Measure.Lebesgue.Steiner.Perimeter
import TauCeti.MeasureTheory.Measure.Lebesgue.Steiner.Rigidity

/-!
# Rigidity of equality in the sharp Euclidean isoperimetric inequality

Among null-measurable subsets of a finite-dimensional real inner product space `E` of dimension
`n` with finite positive volume, open Euclidean balls (up to Lebesgue-null modification) are the
unique sets attaining equality in the sharp De Giorgi perimeter inequality

`P(s)^n = n^n ω_n |s|^(n - 1)`

(`MeasureTheory.NullMeasurableSet.perimeter_pow_eq_iff_exists_ae_eq_ball`), as well as in its
extended-real and real-valued fractional-power formulations
(`MeasureTheory.NullMeasurableSet.ofReal_mul_volume_real_rpow_mul_eq_perimeter_iff`,
`MeasureTheory.NullMeasurableSet.mul_volume_real_rpow_mul_eq_perimeter_toReal_iff`). In dimension
`n ≥ 2`, dropping the positive-volume hypothesis adds only the null sets
(`MeasureTheory.NullMeasurableSet.perimeter_pow_eq_iff_of_two_le`); in dimension `n = 1` the
exponent `n - 1 = 0` makes `1^1 ω_1 |s|^0 = 2` nonzero for null sets while `P(s) = 0`, and in any
positive dimension `P(s) = 0 ↔ |s| = 0` for finite-volume null-measurable sets
(`MeasureTheory.NullMeasurableSet.perimeter_eq_zero_iff`).

## Proof strategy

Suppose `s` has finite positive volume and `P(s)^n = n^n ω_n |s|^(n - 1)` in positive dimension
`n`. First, the right-hand side is finite, forcing `P(s) < ∞`
(`TauCeti.perimeter_ne_top_of_perimeter_pow_eq`). For every unit vector `e`, the Steiner symmetral
`S_e s` has the same volume as `s` and perimeter at most `P(s)`
(`TauCeti.perimeter_steinerSymmetrization_le`), while the sharp isoperimetric inequality applied to
`S_e s` bounds `P(S_e s)^n` from below by `n^n ω_n |S_e s|^(n - 1) = P(s)^n`. Strict monotonicity
of `t ↦ t^n` forces `P(S_e s) = P(s)`
(`MeasureTheory.NullMeasurableSet.perimeter_steinerSymmetrization_eq_of_perimeter_pow_eq`). By
Steiner perimeter rigidity
(`TauCeti.ae_exists_ordConnected_lineSection_of_perimeter_steinerSymmetrization_eq`), almost every
line section of `s` in every unit direction agrees almost everywhere with an interval. Essential
convexity (`TauCeti.exists_convex_ae_eq_of_ae_lineSection_ordConnected`) and Brunn–Minkowski
equality rigidity (`TauCeti.perimeter_pow_eq_iff_exists_ae_eq_ball_of_ae_eq_convex`) then show that
`s` agrees almost everywhere with an open ball of positive radius.

## References

* E. De Giorgi, *Sulla proprietà isoperimetrica dell'ipersfera, nella classe degli insiemi aventi
  frontiera orientata di misura finita*, Atti Accad. Naz. Lincei Mem. Cl. Sci. Fis. Mat. Natur.
  Sez. Ia (8) **5** (1958), 33–44.
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Cambridge University
  Press, 2012, Theorem 14.1.
* F. Cagnetti, M. Colombo, G. De Philippis, F. Maggi, *Rigidity of equality cases in Steiner's
  perimeter inequality*, Anal. PDE **7** (2014), 1535–1593.
-/

public noncomputable section

open MeasureTheory Metric Module Set TopologicalSpace
open scoped ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E]

/-- A null set has perimeter zero in every open set. -/
private theorem perimeter_eq_zero_of_measure_eq_zero {μ : Measure E} {Ω : Opens E} {s : Set E}
    (h : μ s = 0) :
    perimeter μ Ω s = 0 := by
  have h0 : μ.restrict Ω s = 0 := le_antisymm ((Measure.restrict_apply_le _ _).trans_eq h) zero_le
  rw [perimeter_congr_ae (ae_eq_empty.2 h0), perimeter_empty]

/-- Attaining equality in `P(s)^n = n^n ω_n |s|^(n - 1)` for a finite-volume set in positive
dimension forces `P(s) < ∞`. -/
theorem perimeter_ne_top_of_perimeter_pow_eq [BorelSpace E] {s : Set E}
    (hn : finrank ℝ E ≠ 0) (hμs : volume s ≠ ⊤)
    (heq : perimeter volume ⊤ s ^ finrank ℝ E =
      (finrank ℝ E : ℝ≥0∞) ^ finrank ℝ E * volume (ball (0 : E) 1) *
        volume s ^ (finrank ℝ E - 1)) :
    perimeter volume ⊤ s ≠ ⊤ := by
  intro htop
  rw [htop, ENNReal.top_pow hn] at heq
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)) measure_ball_lt_top.ne)
    (ENNReal.pow_ne_top hμs) heq.symm

end TauCeti

namespace MeasureTheory.NullMeasurableSet

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- In positive dimension, a finite-volume null-measurable set has zero perimeter in the whole
space if and only if it has zero volume. -/
theorem perimeter_eq_zero_iff {s : Set E} (hs : NullMeasurableSet s volume)
    (hn : finrank ℝ E ≠ 0) (hμs : volume s ≠ ⊤) :
    perimeter volume ⊤ s = 0 ↔ volume s = 0 := by
  refine ⟨fun hP => ?_, perimeter_eq_zero_of_measure_eq_zero⟩
  by_contra hs0
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hn)
  have hball : 0 < volume.real (ball (0 : E) 1) :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  have hvol : 0 < volume.real s := ENNReal.toReal_pos hs0 hμs
  have hpos : 0 < ENNReal.ofReal (finrank ℝ E * volume.real (ball (0 : E) 1) ^ (finrank ℝ E : ℝ)⁻¹ *
      volume.real s ^ (1 - (finrank ℝ E : ℝ)⁻¹)) :=
    ENNReal.ofReal_pos.2 (by positivity)
  exact (hpos.trans_le (hs.ofReal_mul_volume_real_rpow_mul_le_perimeter hμs hs0)).ne' hP

/-- Any set of finite positive volume attaining equality in the sharp isoperimetric inequality has
Steiner perimeter equality `P(S_e s) = P(s)` in every unit direction `e`. -/
theorem perimeter_steinerSymmetrization_eq_of_perimeter_pow_eq
    {s : Set E} (hs : NullMeasurableSet s volume) (hn : finrank ℝ E ≠ 0)
    (hμs : volume s ≠ ⊤) (hs0 : volume s ≠ 0) (e : E) (he : ‖e‖ = 1)
    (heq : perimeter volume ⊤ s ^ finrank ℝ E =
      (finrank ℝ E : ℝ≥0∞) ^ finrank ℝ E * volume (ball (0 : E) 1) *
        volume s ^ (finrank ℝ E - 1)) :
    perimeter volume ⊤ (steinerSymmetrization e he s) = perimeter volume ⊤ s := by
  refine le_antisymm (perimeter_steinerSymmetrization_le e he hs hμs) ?_
  have hSm := nullMeasurableSet_steinerSymmetrization e he hs
  have hSvol := volume_steinerSymmetrization e he hs
  have hle := hSm.finrank_pow_mul_volume_ball_mul_volume_pow_le_perimeter_pow
    (hSvol ▸ hμs) (hSvol ▸ hs0)
  rwa [hSvol, ← heq, (ENNReal.pow_right_strictMono hn).le_iff_le] at hle

/-- In dimension zero, any nonempty set agrees with `ball 0 1` and `volume (ball 0 1) = 1`. -/
private theorem eq_ball_and_volume_ball_eq_one_of_finrank_eq_zero {s : Set E} (hs0 : volume s ≠ 0)
    (hn : finrank ℝ E = 0) :
    s = ball (0 : E) 1 ∧ volume (ball (0 : E) 1) = 1 := by
  have : Subsingleton E := Module.finrank_zero_iff.mp hn
  have hs_ne : s.Nonempty := nonempty_iff_ne_empty.2 fun h => hs0 (by simp [h])
  let b := stdOrthonormalBasis ℝ E
  have hb : ball (0 : E) 1 = parallelepiped b := by
    rw [Subsingleton.eq_univ_of_nonempty (nonempty_ball.2 one_pos)]
    exact (eq_univ_of_forall fun x => (mem_parallelepiped_iff _ _).2
      ⟨0, ⟨le_rfl, fun _ => zero_le_one⟩, Subsingleton.elim _ _⟩).symm
  refine ⟨?_, by rw [hb, b.volume_parallelepiped]⟩
  rw [Subsingleton.eq_univ_of_nonempty hs_ne,
    Subsingleton.eq_univ_of_nonempty (nonempty_ball.2 one_pos)]

/-- **Euclidean ball rigidity in the sharp isoperimetric inequality.** Let `s` be a null-measurable
subset of a finite-dimensional real inner product space `E` of dimension `n` with finite positive
volume. Then `P(s)^n = n^n ω_n |s|^(n - 1)` if and only if `s` agrees almost everywhere with an
open Euclidean ball of positive radius. -/
theorem perimeter_pow_eq_iff_exists_ae_eq_ball
    {s : Set E} (hs : NullMeasurableSet s volume) (hμs : volume s ≠ ⊤) (hs0 : volume s ≠ 0) :
    perimeter volume ⊤ s ^ finrank ℝ E =
        (finrank ℝ E : ℝ≥0∞) ^ finrank ℝ E * volume (ball (0 : E) 1) *
          volume s ^ (finrank ℝ E - 1) ↔
      ∃ c : E, ∃ r : ℝ, 0 < r ∧ s =ᵐ[volume] ball c r := by
  rcases eq_or_ne (finrank ℝ E) 0 with hn | hn
  · obtain ⟨hsb, hvol⟩ := eq_ball_and_volume_ball_eq_one_of_finrank_eq_zero hs0 hn
    exact iff_of_true (by simp [hn, hvol]) ⟨0, 1, one_pos, hsb ▸ .rfl⟩
  refine ⟨fun heq => ?_, ?_⟩
  · have hPfin := perimeter_ne_top_of_perimeter_pow_eq hn hμs heq
    have hsec (e : E) (he : ‖e‖ = 1) :=
      ae_exists_ordConnected_lineSection_of_perimeter_steinerSymmetrization_eq e he hs hμs hPfin
        (hs.perimeter_steinerSymmetrization_eq_of_perimeter_pow_eq hn hμs hs0 e he heq)
    exact (hs.perimeter_pow_eq_iff_exists_ae_eq_ball_of_ae_lineSection_ordConnected hn
      (pos_iff_ne_zero.2 hs0) hμs hsec).mp heq
  · rintro ⟨c, r, hr, hsr⟩
    rw [perimeter_congr_ae (ae_restrict_of_ae hsr), measure_congr hsr]
    exact perimeter_ball_pow hn hr

/-- **Equality cases of the sharp isoperimetric inequality in dimension `n ≥ 2`.** For a
finite-volume null-measurable set `s` in a space of dimension `n ≥ 2`, equality holds in
`P(s)^n ≥ n^n ω_n |s|^(n - 1)` if and only if `s` is either null or almost everywhere equal to an
open ball of positive radius. The bound `2 ≤ n` is sharp: in dimension `1`, null sets satisfy
`P(s)^1 = 0 ≠ 2 = 1^1 ω_1 |s|^0`. -/
theorem perimeter_pow_eq_iff_of_two_le
    {s : Set E} (hs : NullMeasurableSet s volume) (hμs : volume s ≠ ⊤)
    (hn : 2 ≤ finrank ℝ E) :
    perimeter volume ⊤ s ^ finrank ℝ E =
        (finrank ℝ E : ℝ≥0∞) ^ finrank ℝ E * volume (ball (0 : E) 1) *
          volume s ^ (finrank ℝ E - 1) ↔
      volume s = 0 ∨ ∃ c : E, ∃ r : ℝ, 0 < r ∧ s =ᵐ[volume] ball c r := by
  rcases eq_or_ne (volume s) 0 with hs0 | hs0
  · exact iff_of_true (by rw [perimeter_eq_zero_of_measure_eq_zero hs0, hs0,
      zero_pow (by omega), zero_pow (by omega), mul_zero]) (Or.inl hs0)
  · simpa only [hs0, false_or] using hs.perimeter_pow_eq_iff_exists_ae_eq_ball hμs hs0

/-- **Euclidean ball rigidity, extended-real fractional-power form.** For a null-measurable set `s`
of finite positive volume, `n ω_n ^ (1 / n) |s| ^ (1 - 1 / n) = P(s)` in `ℝ≥0∞` if and only if `s`
agrees almost everywhere with an open ball of positive radius. -/
theorem ofReal_mul_volume_real_rpow_mul_eq_perimeter_iff
    {s : Set E} (hs : NullMeasurableSet s volume) (hμs : volume s ≠ ⊤) (hs0 : volume s ≠ 0) :
    ENNReal.ofReal (finrank ℝ E * volume.real (ball (0 : E) 1) ^ (finrank ℝ E : ℝ)⁻¹ *
        volume.real s ^ (1 - (finrank ℝ E : ℝ)⁻¹)) = perimeter volume ⊤ s ↔
      ∃ c : E, ∃ r : ℝ, 0 < r ∧ s =ᵐ[volume] ball c r := by
  rcases eq_or_ne (finrank ℝ E) 0 with hn | hn
  · obtain ⟨hsb, -⟩ := eq_ball_and_volume_ball_eq_one_of_finrank_eq_zero hs0 hn
    have : Subsingleton E := Module.finrank_zero_iff.mp hn
    have hsu : s = univ := hsb.trans (Subsingleton.eq_univ_of_nonempty (nonempty_ball.2 one_pos))
    exact iff_of_true (by simp [hn, hsu]) ⟨0, 1, one_pos, hsb ▸ .rfl⟩
  rw [← hs.perimeter_pow_eq_iff_exists_ae_eq_ball hμs hs0,
    finrank_pow_mul_volume_ball_mul_volume_pow_eq_ofReal hμs hn,
    ENNReal.ofReal_pow (by positivity), eq_comm,
    (ENNReal.pow_right_strictMono hn).injective.eq_iff]

/-- **Euclidean ball rigidity, real-valued fractional-power form.** For a null-measurable set `s`
of finite positive volume, `n ω_n ^ (1 / n) |s| ^ (1 - 1 / n) = P(s).toReal` if and only if `s`
agrees almost everywhere with an open ball of positive radius. No separate finiteness hypothesis on
`P(s)` is needed: in positive dimension the left-hand side is strictly positive whereas
`⊤.toReal = 0`. -/
theorem mul_volume_real_rpow_mul_eq_perimeter_toReal_iff
    {s : Set E} (hs : NullMeasurableSet s volume) (hμs : volume s ≠ ⊤) (hs0 : volume s ≠ 0) :
    finrank ℝ E * volume.real (ball (0 : E) 1) ^ (finrank ℝ E : ℝ)⁻¹ *
        volume.real s ^ (1 - (finrank ℝ E : ℝ)⁻¹) = (perimeter volume ⊤ s).toReal ↔
      ∃ c : E, ∃ r : ℝ, 0 < r ∧ s =ᵐ[volume] ball c r := by
  rcases eq_or_ne (finrank ℝ E) 0 with hn | hn
  · obtain ⟨hsb, -⟩ := eq_ball_and_volume_ball_eq_one_of_finrank_eq_zero hs0 hn
    have : Subsingleton E := Module.finrank_zero_iff.mp hn
    have hsu : s = univ := hsb.trans (Subsingleton.eq_univ_of_nonempty (nonempty_ball.2 one_pos))
    exact iff_of_true (by simp [hn, hsu]) ⟨0, 1, one_pos, hsb ▸ .rfl⟩
  rw [← hs.ofReal_mul_volume_real_rpow_mul_eq_perimeter_iff hμs hs0]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have : Nontrivial E := Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hn)
    have hball : 0 < volume.real (ball (0 : E) 1) :=
      ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
    have hvol : 0 < volume.real s := ENNReal.toReal_pos hs0 hμs
    have hpos : 0 < (perimeter volume ⊤ s).toReal := h ▸ by positivity
    have hPfin : perimeter volume ⊤ s ≠ ⊤ := fun htop => by simp [htop] at hpos
    rw [h, ENNReal.ofReal_toReal hPfin]
  · rw [← h, ENNReal.toReal_ofReal (by positivity)]

end MeasureTheory.NullMeasurableSet
