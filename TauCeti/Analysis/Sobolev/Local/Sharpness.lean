/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.Sobolev.WeakDeriv.NormRpow
import TauCeti.MeasureTheory.Integral.NormRpow

/-!
# Subcritical sharpness of local Sobolev products and compositions

For the planar local classes `TauCeti.MemLpLoc` and `TauCeti.MemWkpLoc`, this file computes
exactly when a norm power `z ↦ ‖z‖ ^ s` belongs to them near the origin, and uses these powers to
show that the mixed-exponent product and the composition results for `W^{1,p}_loc` fail at the
subcritical exponent `p = 4 / 3`, below the critical exponent `p = 2`.

For `0 < p < ∞`, `‖z‖ ^ s` is in `Lᵖ_loc` near the origin exactly when `s p > -2`. For
`1 ≤ p < ∞` and `s ≠ 0`, it is in `W^{1,p}_loc` near the origin exactly when `(s - 1) p > -2`:
its weak derivative is the classical derivative, of norm `|s| ‖z‖ ^ (s - 1)`. Membership holds on
every set when the exponent condition holds; failure holds on every neighbourhood of the origin.

At `p = 4 / 3`:

* `f = ‖z‖ ^ (-6 / 5)` is in `L^{4/3}_loc` and `g = ‖z‖ ^ (-2 / 5)` is in `W^{1,4/3}_loc`, but
  `f g = ‖z‖ ^ (-8 / 5)` is not in `L^{4/3}_loc`. So the mixed-exponent product
  `Lᵖ_loc × W^{1,q}_loc → L^q_loc` fails at `p = q = 4 / 3`, and its hypothesis `p ≥ 2` cannot be
  dropped altogether.
* `u = ‖z‖ ^ (-2 / 5)` is in `W^{1,4/3}_loc`, but `u ^ 2 = ‖z‖ ^ (-4 / 5)` is not, since its
  derivative has size `‖z‖ ^ (-9 / 5)` and `(9 / 5) (4 / 3) > 2`. So composition with the smooth
  map `x ↦ x ^ 2` does not preserve `W^{1,4/3}_loc`, and the supercritical hypothesis `p > 2` of
  the composition results cannot be dropped altogether.

## Main declarations

* `TauCeti.memLpLoc_norm_rpow_iff`: local `Lᵖ` membership of a norm power near the origin.
* `TauCeti.memWkpLoc_one_norm_rpow_iff`: local `W^{1,p}` membership of a norm power near the
  origin.
* `TauCeti.memLpLoc_memWkpLoc_not_memLpLoc_mul_norm_rpow`: the mixed-exponent product fails at
  `p = q = 4 / 3`.
* `TauCeti.memWkpLoc_not_memWkpLoc_sq_norm_rpow`: squaring does not preserve `W^{1,4/3}_loc`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (Proposition B.1.19 and the composition results it is compared with).
-/

public section

noncomputable section

namespace TauCeti

open Filter _root_.MeasureTheory Metric Set Topology TopologicalSpace

open scoped ENNReal

variable {p : ENNReal} {U : Set ℂ} {s : ℝ}

/-- For `0 < p < ∞`, the norm power `z ↦ ‖z‖ ^ s` is locally `Lᵖ` on every subset of the plane
when `s p > -2`. -/
theorem memLpLoc_norm_rpow (hp0 : p ≠ 0) (hp : p ≠ ∞) (hs : -2 < s * p.toReal) :
    MemLpLoc p U (fun z : ℂ => ‖z‖ ^ s) := by
  refine memLpLoc_iff.2 fun K _ hc => ?_
  rw [← integrable_norm_rpow_iff (measurable_norm.pow_const s).aestronglyMeasurable hp0 hp]
  simp only [Real.norm_eq_abs, Real.abs_rpow_of_nonneg (norm_nonneg _), abs_norm,
    ← Real.rpow_mul (norm_nonneg _)]
  refine (?_ : LocallyIntegrable _ volume).integrableOn_isCompact hc
  simpa only [zero_sub, norm_neg] using
    locallyIntegrable_norm_sub_rpow (mu := (volume : Measure ℂ)) (s := s * p.toReal)
      (by rw [Complex.finrank_real_complex]; push_cast; linarith) (0 : ℂ)

/-- For `0 < p < ∞`, if `s p ≤ -2` then `z ↦ ‖z‖ ^ s` is not locally `Lᵖ` on any neighbourhood
of the origin. -/
theorem not_memLpLoc_norm_rpow (hp0 : p ≠ 0) (hp : p ≠ ∞) (hU : U ∈ 𝓝 (0 : ℂ))
    (hs : s * p.toReal ≤ -2) : ¬ MemLpLoc p U (fun z : ℂ => ‖z‖ ^ s) := by
  intro h
  obtain ⟨r, hr, hrU⟩ := nhds_basis_closedBall.mem_iff.1 hU
  have hint := (memLpLoc_iff.1 h _ hrU (isCompact_closedBall 0 r)).integrable_norm_rpow hp0 hp
  simp only [Real.norm_eq_abs, Real.abs_rpow_of_nonneg (norm_nonneg _), abs_norm,
    ← Real.rpow_mul (norm_nonneg _)] at hint
  have hball : IntegrableOn (fun z : ℂ => ‖z‖ ^ (s * p.toReal)) (ball 0 r) volume :=
    IntegrableOn.mono_set hint ball_subset_closedBall
  rw [integrableOn_norm_rpow_ball_iff hr, Complex.finrank_real_complex] at hball
  push_cast at hball
  linarith

/-- **Local `Lᵖ` membership of a norm power.** For `0 < p < ∞` and a neighbourhood `U` of the
origin, `z ↦ ‖z‖ ^ s` is locally `Lᵖ` on `U` exactly when `s p > -2`. -/
theorem memLpLoc_norm_rpow_iff (hp0 : p ≠ 0) (hp : p ≠ ∞) (hU : U ∈ 𝓝 (0 : ℂ)) :
    MemLpLoc p U (fun z : ℂ => ‖z‖ ^ s) ↔ -2 < s * p.toReal :=
  ⟨fun h => not_le.1 fun hs => not_memLpLoc_norm_rpow hp0 hp hU hs h,
    memLpLoc_norm_rpow hp0 hp⟩

/-- For `1 ≤ p < ∞`, the norm power `z ↦ ‖z‖ ^ s` is in `W^{1,p}_loc` on every subset of the
plane when `(s - 1) p > -2`. Its weak derivative is `s ‖z‖ ^ (s - 2) ⟪z, ·⟫`. -/
theorem memWkpLoc_one_norm_rpow (hp1 : 1 ≤ p) (hp : p ≠ ∞) (hs : -2 < (s - 1) * p.toReal) :
    MemWkpLoc p U 1 (fun z : ℂ => ‖z‖ ^ s) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hpr : 1 ≤ p.toReal := by
    simpa using ENNReal.toReal_mono hp hp1
  have hs1 : 1 - (Module.finrank ℝ ℂ : ℝ) < s := by
    rw [Complex.finrank_real_complex]
    push_cast
    nlinarith
  refine memWkpLoc_succ_iff.2 ⟨memLpLoc_norm_rpow hp0 hp (by nlinarith),
    fun z => (s * ‖z‖ ^ (s - 2)) • innerSL ℝ z, hasWeakFDerivOn_norm_rpow hs1 _,
    memWkpLoc_zero_iff.2 (memLpLoc_iff.2 fun K hK hc => ?_)⟩
  refine ((memLpLoc_iff.1 (memLpLoc_norm_rpow hp0 hp hs) K hK hc).const_mul |s|).of_le
    (locallyIntegrable_norm_rpow_smul_innerSL hs1).aestronglyMeasurable.restrict
    (ae_of_all _ fun z => ?_)
  refine (norm_rpow_smul_innerSL_le s z).trans (le_of_eq ?_)
  rw [Real.norm_of_nonneg (by positivity)]

/-- For `0 < p < ∞` and `s ≠ 0`, if `(s - 1) p ≤ -2` then `z ↦ ‖z‖ ^ s` is not in
`W^{1,p}_loc` on any neighbourhood of the origin: away from the origin a weak derivative agrees
with the classical one, whose norm `|s| ‖z‖ ^ (s - 1)` is not `p`-integrable near the origin. -/
theorem not_memWkpLoc_one_norm_rpow (hp0 : p ≠ 0) (hp : p ≠ ∞) (hU : U ∈ 𝓝 (0 : ℂ))
    (hs0 : s ≠ 0) (hs : (s - 1) * p.toReal ≤ -2) :
    ¬ MemWkpLoc p U 1 (fun z : ℂ => ‖z‖ ^ s) := by
  intro h
  obtain ⟨-, D, hD, hDp⟩ := memWkpLoc_succ_iff.1 h
  obtain ⟨r, hr, hrU⟩ := nhds_basis_closedBall.mem_iff.1 (interior_mem_nhds.2 hU)
  -- On the punctured interior, `D` is the classical derivative.
  let W : Opens ℂ := Opens.interior U ⊓ ⟨{0}ᶜ, isOpen_compl_singleton⟩
  have hdiff : ∀ z ∈ (W : Set ℂ), HasFDerivAt (fun z : ℂ => ‖z‖ ^ s)
      ((s * ‖z‖ ^ (s - 2)) • innerSL ℝ z) z := fun z hz => hasFDerivAt_norm_rpow_of_ne s hz.2
  have hcont : ContinuousOn (fderiv ℝ fun z : ℂ => ‖z‖ ^ s) W := by
    have hc : ContinuousOn (fun z : ℂ => (s * ‖z‖ ^ (s - 2)) • innerSL ℝ z) W :=
      fun z hz => ((continuousAt_const.mul ((continuous_norm.continuousAt).rpow_const
        (Or.inl (norm_ne_zero_iff.2 hz.2)))).smul
          (innerSL ℝ).continuous.continuousAt).continuousWithinAt
    exact hc.congr fun z hz => (hdiff z hz).fderiv
  have hae := (hD.mono (inf_le_left : W ≤ Opens.interior U)).ae_eq_fderiv
    (hcont.locallyIntegrableOn W.isOpen.measurableSet)
    fun z hz => (hdiff z hz).differentiableAt
  have hae' := (ae_restrict_iff' W.isOpen.measurableSet).1 hae
  -- So `|s| ‖z‖ ^ (s - 1)` would be `p`-integrable on a ball about the origin.
  have hint := (memLpLoc_iff.1 (memWkpLoc_zero_iff.1 hDp) _ (hrU.trans interior_subset)
    (isCompact_closedBall 0 r)).integrable_norm_rpow hp0 hp
  have hball : IntegrableOn (fun z : ℂ => |s| ^ p.toReal * ‖z‖ ^ ((s - 1) * p.toReal))
      (ball 0 r) volume := by
    refine (IntegrableOn.mono_set hint ball_subset_closedBall).congr ?_
    filter_upwards [ae_restrict_of_ae hae', ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (Measure.ae_ne volume (0 : ℂ))] with z hz hzb hz0
    have hzW : z ∈ (W : Set ℂ) :=
      ⟨by simpa using hrU (ball_subset_closedBall hzb), hz0⟩
    rw [hz hzW, norm_fderiv_norm_rpow_of_ne s hz0,
      Real.mul_rpow (abs_nonneg s) (Real.rpow_nonneg (norm_nonneg z) _),
      ← Real.rpow_mul (norm_nonneg z)]
  have hpos : (0 : ℝ) < |s| ^ p.toReal := Real.rpow_pos_of_pos (abs_pos.2 hs0) _
  rw [IntegrableOn, integrable_const_mul_iff hpos.ne'.isUnit, ← IntegrableOn,
    integrableOn_norm_rpow_ball_iff hr, Complex.finrank_real_complex] at hball
  push_cast at hball
  linarith

/-- **Local `W^{1,p}` membership of a norm power.** For `1 ≤ p < ∞`, `s ≠ 0` and a neighbourhood
`U` of the origin, `z ↦ ‖z‖ ^ s` is in `W^{1,p}_loc` on `U` exactly when `(s - 1) p > -2`. -/
theorem memWkpLoc_one_norm_rpow_iff (hp1 : 1 ≤ p) (hp : p ≠ ∞) (hU : U ∈ 𝓝 (0 : ℂ))
    (hs0 : s ≠ 0) :
    MemWkpLoc p U 1 (fun z : ℂ => ‖z‖ ^ s) ↔ -2 < (s - 1) * p.toReal :=
  ⟨fun h => not_le.1 fun hs =>
      not_memWkpLoc_one_norm_rpow (zero_lt_one.trans_le hp1).ne' hp hU hs0 hs h,
    memWkpLoc_one_norm_rpow hp1 hp⟩

private lemma toReal_four_thirds : (4 / 3 : ENNReal).toReal = 4 / 3 := by
  rw [ENNReal.toReal_div]
  norm_num

private lemma one_le_four_thirds : (1 : ENNReal) ≤ 4 / 3 := by
  rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]
  norm_num

private lemma four_thirds_ne_top : (4 / 3 : ENNReal) ≠ ∞ :=
  ENNReal.div_ne_top (by norm_num) (by norm_num)

/-- `‖z‖ ^ (-2 / 5)` is in `W^{1,4/3}_loc` on the unit disc: its derivative has size
`‖z‖ ^ (-7 / 5)`, and `(7 / 5) (4 / 3) = 28 / 15 < 2`. -/
private lemma memWkpLoc_norm_rpow_neg_two_fifths :
    MemWkpLoc (4 / 3) (ball (0 : ℂ) 1) 1 (fun z => ‖z‖ ^ (-2 / 5 : ℝ)) :=
  memWkpLoc_one_norm_rpow one_le_four_thirds four_thirds_ne_top
    (by rw [toReal_four_thirds]; norm_num)

/-- **Mixed exponents at order zero fail at `p = 4 / 3`.** For `p = q = 4 / 3` on the unit disc,
`f = ‖z‖ ^ (-6 / 5)` is in `L^{4/3}_loc` and `g = ‖z‖ ^ (-2 / 5)` is in `W^{1,4/3}_loc`, but
`f g = ‖z‖ ^ (-8 / 5)` is not in `L^{4/3}_loc`, since `(8 / 5) (4 / 3) = 32 / 15 > 2`. -/
theorem memLpLoc_memWkpLoc_not_memLpLoc_mul_norm_rpow :
    MemLpLoc (4 / 3) (ball (0 : ℂ) 1) (fun z => ‖z‖ ^ (-6 / 5 : ℝ)) ∧
      MemWkpLoc (4 / 3) (ball (0 : ℂ) 1) 1 (fun z => ‖z‖ ^ (-2 / 5 : ℝ)) ∧
      ¬ MemLpLoc (4 / 3) (ball (0 : ℂ) 1) (fun z => ‖z‖ ^ (-6 / 5 : ℝ) * ‖z‖ ^ (-2 / 5 : ℝ)) := by
  have hp0 : (4 / 3 : ENNReal) ≠ 0 := by simp
  refine ⟨memLpLoc_norm_rpow hp0 four_thirds_ne_top (by rw [toReal_four_thirds]; norm_num),
    memWkpLoc_norm_rpow_neg_two_fifths, ?_⟩
  have hmul : (fun z : ℂ => ‖z‖ ^ (-6 / 5 : ℝ) * ‖z‖ ^ (-2 / 5 : ℝ)) =
      fun z => ‖z‖ ^ (-8 / 5 : ℝ) := by
    funext z
    rw [← Real.rpow_add' (norm_nonneg z) (by norm_num)]
    norm_num
  rw [hmul]
  exact not_memLpLoc_norm_rpow hp0 four_thirds_ne_top (ball_mem_nhds 0 one_pos)
    (by rw [toReal_four_thirds]; norm_num)

/-- **Composition at order one fails at `p = 4 / 3`.** On the unit disc,
`u = ‖z‖ ^ (-2 / 5)` is in `W^{1,4/3}_loc`, but `u ^ 2 = ‖z‖ ^ (-4 / 5)` is not: its derivative
has size `‖z‖ ^ (-9 / 5)`, and `(9 / 5) (4 / 3) = 12 / 5 > 2`. -/
theorem memWkpLoc_not_memWkpLoc_sq_norm_rpow :
    MemWkpLoc (4 / 3) (ball (0 : ℂ) 1) 1 (fun z => ‖z‖ ^ (-2 / 5 : ℝ)) ∧
      ¬ MemWkpLoc (4 / 3) (ball (0 : ℂ) 1) 1 (fun z => (‖z‖ ^ (-2 / 5 : ℝ)) ^ 2) := by
  refine ⟨memWkpLoc_norm_rpow_neg_two_fifths, ?_⟩
  have hsq : (fun z : ℂ => (‖z‖ ^ (-2 / 5 : ℝ)) ^ 2) = fun z => ‖z‖ ^ (-4 / 5 : ℝ) := by
    funext z
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg z)]
    norm_num
  rw [hsq]
  exact not_memWkpLoc_one_norm_rpow (by simp) four_thirds_ne_top (ball_mem_nhds 0 one_pos)
    (by norm_num) (by rw [toReal_four_thirds]; norm_num)

end TauCeti
