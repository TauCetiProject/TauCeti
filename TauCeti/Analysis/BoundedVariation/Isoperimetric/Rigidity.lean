/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.Analysis.BoundedVariation.Perimeter
import Mathlib.Analysis.Normed.Module.RCLike.Real
import TauCeti.Analysis.BoundedVariation.Ball
import TauCeti.Analysis.BoundedVariation.Isoperimetric.Basic
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.Lebesgue.BrunnMinkowski.Isoperimetric
import TauCeti.MeasureTheory.Measure.Lebesgue.Steiner.Equality
import TauCeti.MeasureTheory.Measure.Lebesgue.Steiner.Perimeter
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# Equality cases in the Euclidean isoperimetric inequality

Let `E` be a finite-dimensional real inner product space of dimension `n` with its Lebesgue volume,
and write `ω_n = volume (ball 0 1)` and `P(s)` for the distributional perimeter of `s` in the whole
space. A null-measurable set `s` of finite positive volume attains equality in the sharp
isoperimetric inequality

`P(s)^n = n^n ω_n |s|^(n-1)`

if and only if `s` agrees almost everywhere with an open ball of positive radius
(`MeasureTheory.NullMeasurableSet.perimeter_pow_eq_iff_exists_ae_eq_ball`), with no boundedness,
connectedness, convexity, or regularity assumption on `s`, and no prior finiteness assumption on
`P(s)`. The same characterization holds in the extended-real form
`P(s) = ENNReal.ofReal (n ω_n^(1/n) |s|^(1 - 1/n))`
(`MeasureTheory.NullMeasurableSet.perimeter_eq_ofReal_iff_exists_ae_eq_ball`) and in the real-valued
form `P(s).toReal = n ω_n^(1/n) |s|^(1 - 1/n)`
(`MeasureTheory.NullMeasurableSet.perimeter_toReal_eq_iff_exists_ae_eq_ball`), again without
assuming `P(s) < ∞` (since `∞.toReal = 0` while the right-hand side is strictly positive in
positive dimension). In dimension `n ≥ 2`, dropping positivity of the volume allows radius `r = 0`
(`MeasureTheory.NullMeasurableSet.perimeter_pow_eq_iff_exists_ae_eq_ball_of_two_le`), whereas in
dimension `n = 1` the empty set does not attain `P(∅) = 2`.

For regular open sets (`interior (closure s) = s`) and regular closed sets
(`closure (interior s) = s`), almost-everywhere agreement upgrades to exact equality with an open
or closed ball of positive radius
(`TauCeti.perimeter_pow_eq_iff_exists_eq_ball_of_interior_closure_eq` and
`TauCeti.perimeter_pow_eq_iff_exists_eq_closedBall_of_closure_interior_eq`). Ordinary openness or
closedness does not suffice, as removing a point from an open ball or adding a point to a closed
ball preserves both volume and perimeter.

## Strategy

In positive dimension, suppose `s` has finite positive volume and satisfies
`P(s)^n = n^n ω_n |s|^(n-1)`. Then `P(s)` is finite, and for every unit vector `e`, the Steiner
symmetral `S_e s` preserves volume (`TauCeti.volume_steinerSymmetrization`) and does not increase
perimeter (`TauCeti.perimeter_steinerSymmetrization_le`). Applying the sharp isoperimetric
inequality (`NullMeasurableSet.finrank_pow_mul_volume_ball_mul_volume_pow_le_perimeter_pow`)
to `S_e s` squeezes `P(S_e s)^n = P(s)^n`, hence `P(S_e s) = P(s)`. By equality in Steiner's
perimeter inequality
(`NullMeasurableSet.ae_exists_ordConnected_lineSection_of_perimeter_steinerSymmetrization_eq`),
almost every line section of `s` along `e` agrees a.e. with an interval. Since this holds in every
unit direction, the interval-section rigidity theorem
(`NullMeasurableSet.perimeter_pow_eq_iff_exists_ae_eq_ball_of_ae_lineSection_ordConnected`)
yields an open ball of positive radius agreeing a.e. with `s`.

## Main results

* `MeasureTheory.NullMeasurableSet.perimeter_pow_eq_iff_exists_ae_eq_ball`: unconditional a.e.
  ball rigidity for `P(s)^n = n^n ω_n |s|^(n-1)`.
* `MeasureTheory.NullMeasurableSet.perimeter_eq_ofReal_iff_exists_ae_eq_ball`: the equivalent
  characterization for `P(s) = ENNReal.ofReal (n ω_n^(1/n) |s|^(1 - 1/n))`.
* `MeasureTheory.NullMeasurableSet.perimeter_toReal_eq_iff_exists_ae_eq_ball`: the real-valued
  characterization for `P(s).toReal = n ω_n^(1/n) |s|^(1 - 1/n)`.
* `MeasureTheory.NullMeasurableSet.perimeter_pow_eq_iff_exists_ae_eq_ball_of_two_le`: the `n ≥ 2`
  version allowing zero volume (`0 ≤ r`).
* `TauCeti.perimeter_pow_eq_iff_exists_eq_ball_of_interior_closure_eq`: exact open-ball rigidity
  for regular open sets.
* `TauCeti.perimeter_pow_eq_iff_exists_eq_closedBall_of_closure_interior_eq`: exact closed-ball
  rigidity for regular closed sets.

## References

* E. De Giorgi, *Sulla proprietà isoperimetrica dell'ipersfera, nella classe degli insiemi aventi
  frontiera orientata di misura finita*, Atti Accad. Naz. Lincei Mem. Cl. Sci. Fis. Mat. Natur.
  Sez. I **5** (1958), 33–44.
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Cambridge University
  Press, 2012, Chapter 14.
* F. Cagnetti, M. Colombo, G. De Philippis, F. Maggi, *Rigidity of equality cases in Steiner's
  perimeter inequality*, Anal. PDE **7** (2014), 1535–1593.
-/

public section

noncomputable section

open MeasureTheory Metric Module Set
open scoped ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- In a zero-dimensional inner product space, every set of nonzero volume equals `univ` and
`ball 0 1`, and the unit ball has volume `1`. -/
private theorem eq_univ_and_ball_of_finrank_zero {s : Set E} (hn : finrank ℝ E = 0)
    (hs0 : volume s ≠ 0) :
    s = univ ∧ ball (0 : E) 1 = univ ∧ volume (ball (0 : E) 1) = 1 := by
  have _ : Subsingleton E := Module.finrank_zero_iff.mp hn
  obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hs0
  have hsuniv : s = univ := eq_univ_of_forall fun y ↦ Subsingleton.elim y x ▸ hx
  have hball : ball (0 : E) 1 = univ :=
    eq_univ_of_forall fun y ↦ by simp [Subsingleton.elim y 0]
  let b := stdOrthonormalBasis ℝ E
  have hb : parallelepiped b = univ := eq_univ_of_forall fun y ↦
    (mem_parallelepiped_iff _ _).2 ⟨0, ⟨le_rfl, fun _ ↦ zero_le_one⟩, Subsingleton.elim _ _⟩
  exact ⟨hsuniv, hball, by rw [hball, ← hb, b.volume_parallelepiped]⟩

end TauCeti

namespace MeasureTheory.NullMeasurableSet

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Unconditional isoperimetric rigidity.** In a finite-dimensional real inner product space of
dimension `n`, a null-measurable set `s` of finite positive volume satisfies
`P(s)^n = n^n ω_n |s|^(n-1)`, where `ω_n = volume (ball 0 1)` and `P(s)` is the perimeter of `s`
in the whole space, if and only if `s` agrees almost everywhere with an open ball of positive
radius. No boundedness, convexity, regularity, or finite-perimeter hypothesis is assumed. -/
theorem perimeter_pow_eq_iff_exists_ae_eq_ball
    {s : Set E} (hs : NullMeasurableSet s volume) (hμs : volume s ≠ ⊤) (hs0 : volume s ≠ 0) :
    perimeter volume ⊤ s ^ finrank ℝ E =
        (finrank ℝ E : ℝ≥0∞) ^ finrank ℝ E * volume (ball (0 : E) 1) *
          volume s ^ (finrank ℝ E - 1) ↔
      ∃ c : E, ∃ r : ℝ, 0 < r ∧ s =ᵐ[volume] ball c r := by
  rcases eq_or_ne (finrank ℝ E) 0 with hn | hn
  · obtain ⟨hsuniv, hball, hvol⟩ := eq_univ_and_ball_of_finrank_zero hn hs0
    refine ⟨fun _ ↦ ⟨0, 1, one_pos, by rw [hsuniv, hball]⟩, fun _ ↦ ?_⟩
    simp [hn, hvol]
  constructor
  · intro heq
    have hrhs_ne_top : (finrank ℝ E : ℝ≥0∞) ^ finrank ℝ E * volume (ball (0 : E) 1) *
        volume s ^ (finrank ℝ E - 1) ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))
        measure_ball_lt_top.ne) (ENNReal.pow_ne_top hμs)
    have hP : perimeter volume ⊤ s ≠ ⊤ := fun htop ↦
      hrhs_ne_top (heq.symm.trans (by rw [htop, ENNReal.top_pow hn]))
    -- Equality forces every Steiner symmetral to have the same perimeter, hence interval sections.
    have hsections : ∀ e : E, ‖e‖ = 1 → ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume,
        ∃ I : Set ℝ, I.OrdConnected ∧ {t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I := by
      intro e he
      set S := steinerSymmetrization e he s
      have hSm : NullMeasurableSet S volume := nullMeasurableSet_steinerSymmetrization e he hs
      have hSvol : volume S = volume s := volume_steinerSymmetrization e he hs
      have hSle : perimeter volume ⊤ S ≤ perimeter volume ⊤ s :=
        perimeter_steinerSymmetrization_le e he hs hμs
      have hSpow : perimeter volume ⊤ S ^ finrank ℝ E = perimeter volume ⊤ s ^ finrank ℝ E :=
        le_antisymm (pow_le_pow_left₀ zero_le hSle _) <| heq.trans_le <| by
          simpa only [hSvol] using
            hSm.finrank_pow_mul_volume_ball_mul_volume_pow_le_perimeter_pow
              (hSvol.symm ▸ hμs) (hSvol.symm ▸ hs0)
      exact hs.ae_exists_ordConnected_lineSection_of_perimeter_steinerSymmetrization_eq hμs hP e he
        ((ENNReal.pow_right_strictMono hn).injective hSpow)
    exact (hs.perimeter_pow_eq_iff_exists_ae_eq_ball_of_ae_lineSection_ordConnected
      hn (pos_iff_ne_zero.2 hs0) hμs hsections).1 heq
  · rintro ⟨c, r, hr, hsr⟩
    rw [perimeter_congr_ae (ae_restrict_of_ae hsr), measure_congr hsr]
    exact perimeter_ball_pow hn hr

/-- **Unconditional isoperimetric rigidity, extended-real form.** A null-measurable set `s` of
finite positive volume satisfies `P(s) = ENNReal.ofReal (n ω_n^(1/n) |s|^(1 - 1/n))` if and only
if `s` agrees almost everywhere with an open ball of positive radius. -/
theorem perimeter_eq_ofReal_iff_exists_ae_eq_ball
    {s : Set E} (hs : NullMeasurableSet s volume) (hμs : volume s ≠ ⊤) (hs0 : volume s ≠ 0) :
    perimeter volume ⊤ s =
        ENNReal.ofReal (finrank ℝ E * volume.real (ball (0 : E) 1) ^ (finrank ℝ E : ℝ)⁻¹ *
          volume.real s ^ (1 - (finrank ℝ E : ℝ)⁻¹)) ↔
      ∃ c : E, ∃ r : ℝ, 0 < r ∧ s =ᵐ[volume] ball c r := by
  rcases eq_or_ne (finrank ℝ E) 0 with hn | hn
  · obtain ⟨hsuniv, hball, -⟩ := eq_univ_and_ball_of_finrank_zero hn hs0
    refine ⟨fun _ ↦ ⟨0, 1, one_pos, by rw [hsuniv, hball]⟩, fun _ ↦ ?_⟩
    simp [hn, hsuniv, perimeter_univ]
  rw [← hs.perimeter_pow_eq_iff_exists_ae_eq_ball hμs hs0,
    finrank_pow_mul_volume_ball_mul_volume_pow_eq_ofReal hμs hn,
    ENNReal.ofReal_pow (by positivity)]
  exact (ENNReal.pow_right_strictMono hn).injective.eq_iff.symm

/-- **Unconditional isoperimetric rigidity, real-valued form.** A null-measurable set `s` of finite
positive volume satisfies `P(s).toReal = n ω_n^(1/n) |s|^(1 - 1/n)` if and only if `s` agrees almost
everywhere with an open ball of positive radius. No finite-perimeter assumption is needed: in
positive dimension the right-hand side is strictly positive, whereas `∞.toReal = 0`. -/
theorem perimeter_toReal_eq_iff_exists_ae_eq_ball
    {s : Set E} (hs : NullMeasurableSet s volume) (hμs : volume s ≠ ⊤) (hs0 : volume s ≠ 0) :
    (perimeter volume ⊤ s).toReal =
        finrank ℝ E * volume.real (ball (0 : E) 1) ^ (finrank ℝ E : ℝ)⁻¹ *
          volume.real s ^ (1 - (finrank ℝ E : ℝ)⁻¹) ↔
      ∃ c : E, ∃ r : ℝ, 0 < r ∧ s =ᵐ[volume] ball c r := by
  rcases eq_or_ne (finrank ℝ E) 0 with hn | hn
  · obtain ⟨hsuniv, hball, -⟩ := eq_univ_and_ball_of_finrank_zero hn hs0
    refine ⟨fun _ ↦ ⟨0, 1, one_pos, by rw [hsuniv, hball]⟩, fun _ ↦ ?_⟩
    simp [hn, hsuniv, perimeter_univ]
  rw [← hs.perimeter_eq_ofReal_iff_exists_ae_eq_ball hμs hs0]
  have hω : 0 < volume.real (ball (0 : E) 1) := Metric.measureReal_ball_pos volume 0 one_pos
  have hV : 0 < volume.real s := ENNReal.toReal_pos hs0 hμs
  have hRpos : 0 < (finrank ℝ E : ℝ) * volume.real (ball (0 : E) 1) ^ (finrank ℝ E : ℝ)⁻¹ *
      volume.real s ^ (1 - (finrank ℝ E : ℝ)⁻¹) := by
    have : (0 : ℝ) < finrank ℝ E := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
    positivity
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, ENNReal.toReal_ofReal hRpos.le]⟩
  have hP : perimeter volume ⊤ s ≠ ⊤ := fun htop ↦ hRpos.ne' (by simpa [htop] using h.symm)
  rw [← h, ENNReal.ofReal_toReal hP]

/-- **Unconditional isoperimetric rigidity in dimension `n ≥ 2`.** In dimension `n ≥ 2`, a
null-measurable set `s` of finite volume (possibly zero) satisfies `P(s)^n = n^n ω_n |s|^(n-1)` if
and only if `s` agrees almost everywhere with an open ball of nonnegative radius. -/
theorem perimeter_pow_eq_iff_exists_ae_eq_ball_of_two_le
    {s : Set E} (hs : NullMeasurableSet s volume) (hμs : volume s ≠ ⊤) (hn : 2 ≤ finrank ℝ E) :
    perimeter volume ⊤ s ^ finrank ℝ E =
        (finrank ℝ E : ℝ≥0∞) ^ finrank ℝ E * volume (ball (0 : E) 1) *
          volume s ^ (finrank ℝ E - 1) ↔
      ∃ c : E, ∃ r : ℝ, 0 ≤ r ∧ s =ᵐ[volume] ball c r := by
  rcases eq_or_ne (volume s) 0 with hs0 | hs0
  · refine ⟨fun _ ↦ ⟨0, 0, le_rfl, by rw [ball_zero]; exact ae_eq_empty.2 hs0⟩, fun _ ↦ ?_⟩
    rw [perimeter_congr_ae (ae_restrict_of_ae (ae_eq_empty.2 hs0)), perimeter_empty, hs0,
      zero_pow (by omega), zero_pow (by omega), mul_zero]
  rw [hs.perimeter_pow_eq_iff_exists_ae_eq_ball hμs hs0]
  refine ⟨fun ⟨c, r, hr, hsr⟩ ↦ ⟨c, r, hr.le, hsr⟩, fun ⟨c, r, hr, hsr⟩ ↦ ⟨c, r, ?_, hsr⟩⟩
  refine lt_of_le_of_ne hr fun hr0 ↦ hs0 ?_
  rw [measure_congr hsr, ← hr0, ball_zero, measure_empty]

end MeasureTheory.NullMeasurableSet

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Exact open-ball isoperimetric rigidity for regular open sets.** A regular open set
(`interior (closure s) = s`) of finite positive volume attains equality in the sharp isoperimetric
inequality `P(s)^n = n^n ω_n |s|^(n-1)` if and only if `s` is literally an open ball of positive
radius. -/
theorem perimeter_pow_eq_iff_exists_eq_ball_of_interior_closure_eq
    {s : Set E} (hs : interior (closure s) = s) (hμs : volume s ≠ ⊤) (hs0 : volume s ≠ 0) :
    perimeter volume ⊤ s ^ finrank ℝ E =
        (finrank ℝ E : ℝ≥0∞) ^ finrank ℝ E * volume (ball (0 : E) 1) *
          volume s ^ (finrank ℝ E - 1) ↔
      ∃ c : E, ∃ r : ℝ, 0 < r ∧ s = ball c r := by
  have hnm : NullMeasurableSet s volume := (hs ▸ isOpen_interior).measurableSet.nullMeasurableSet
  rw [hnm.perimeter_pow_eq_iff_exists_ae_eq_ball hμs hs0]
  refine ⟨fun ⟨c, r, hr, hsr⟩ ↦ ⟨c, r, hr, ?_⟩, fun ⟨c, r, hr, hsr⟩ ↦ ⟨c, r, hr, hsr ▸ .rfl⟩⟩
  exact eq_of_ae_eq_of_interior_closure_eq hs
    (by rw [closure_ball c hr.ne', interior_closedBall c hr.ne']) hsr

/-- **Exact closed-ball isoperimetric rigidity for regular closed sets.** A regular closed set
(`closure (interior s) = s`) of finite positive volume attains equality in the sharp isoperimetric
inequality `P(s)^n = n^n ω_n |s|^(n-1)` if and only if `s` is literally a closed ball of positive
radius. -/
theorem perimeter_pow_eq_iff_exists_eq_closedBall_of_closure_interior_eq
    {s : Set E} (hs : closure (interior s) = s) (hμs : volume s ≠ ⊤) (hs0 : volume s ≠ 0) :
    perimeter volume ⊤ s ^ finrank ℝ E =
        (finrank ℝ E : ℝ≥0∞) ^ finrank ℝ E * volume (ball (0 : E) 1) *
          volume s ^ (finrank ℝ E - 1) ↔
      ∃ c : E, ∃ r : ℝ, 0 < r ∧ s = closedBall c r := by
  have hclosed : IsClosed s := hs ▸ isClosed_closure
  have hnm : NullMeasurableSet s volume := hclosed.measurableSet.nullMeasurableSet
  rw [hnm.perimeter_pow_eq_iff_exists_ae_eq_ball hμs hs0]
  refine ⟨fun ⟨c, r, hr, hsr⟩ ↦ ⟨c, r, hr, ?_⟩, fun ⟨c, r, hr, hsr⟩ ↦
    ⟨c, r, hr, hsr ▸ volume.addHaar_closedBall_ae_eq_ball_of_ne_zero c r hr.ne'⟩⟩
  have hsub1 : ball c r ⊆ interior s :=
    interior_maximal ((isOpen_ball.subset_closure_of_ae_le (hsr.mono fun _ h ↦ h.2)).trans_eq
      hclosed.closure_eq) isOpen_ball
  have hsub2 : interior s ⊆ ball c r := by
    rw [← interior_closedBall c hr.ne']
    refine interior_maximal ?_ isOpen_interior
    rw [← closure_ball c hr.ne']
    exact isOpen_interior.subset_closure_of_ae_le (hsr.mono fun _ h hx ↦ h.1 (interior_subset hx))
  rw [← hs, Subset.antisymm hsub2 hsub1, closure_ball c hr.ne']

end TauCeti

end
