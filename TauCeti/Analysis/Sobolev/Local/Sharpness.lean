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
# Norm-power thresholds and subcritical sharpness for local Sobolev classes

For the local classes `TauCeti.MemLpLoc` and `TauCeti.MemWkpLoc` on a finite-dimensional real
space `E` of dimension `n = Module.finrank ℝ E`, this file computes the exact integrability and
Sobolev thresholds of radial norm powers `x ↦ ‖x‖ ^ s` and `x ↦ ‖x‖⁻¹` near the origin, and uses
them in dimension `2` to show that the mixed-exponent product and composition results for
`W^{1,p}_loc` fail at the subcritical exponent `p = 4 / 3`.

* On any nontrivial finite-dimensional real normed space `E` with additive Haar `volume`:
  - for `0 < p < ∞`, `x ↦ ‖x‖ ^ s` lies in `Lᵖ_loc(U)` (`0 ∈ interior U`) iff `-n < s * p.toReal`
    (`TauCeti.memLpLoc_norm_rpow_iff`);
  - for all `p : ℝ≥0∞` (including `p = 0` and `p = ∞`), `x ↦ ‖x‖⁻¹` lies in `Lᵖ_loc(U)`
    (`0 ∈ interior U`) iff `p < n` (`TauCeti.memLpLoc_norm_inv_iff`).
* On any nontrivial finite-dimensional real inner product space `E` with additive Haar `volume`,
  for `1 ≤ p < ∞` and `s ≠ 0`, `x ↦ ‖x‖ ^ s` lies in `W^{1,p}_loc(U)` (`0 ∈ interior U`) iff
  `-n < (s - 1) * p.toReal` (`TauCeti.memWkpLoc_one_norm_rpow_iff`).

At `p = 4 / 3` on the unit disc in `ℂ`:

* `f = ‖z‖ ^ (-6 / 5)` is in `L^{4/3}_loc` and `g = ‖z‖ ^ (-2 / 5)` is in `W^{1,4/3}_loc`, but
  `f g = ‖z‖ ^ (-8 / 5)` is not in `L^{4/3}_loc`.
* `u = ‖z‖ ^ (-2 / 5)` is in `W^{1,4/3}_loc`, but `u ^ 2 = ‖z‖ ^ (-4 / 5)` is not.

## Main declarations

* `TauCeti.memLpLoc_norm_rpow_iff`: local `Lᵖ` membership of `x ↦ ‖x‖ ^ s` near the origin.
* `TauCeti.memLpLoc_norm_inv_iff`: local `Lᵖ` membership of `x ↦ ‖x‖⁻¹` near the origin for all
  `p : ℝ≥0∞`.
* `TauCeti.memWkpLoc_one_norm_rpow_iff`: local `W^{1,p}` membership of `x ↦ ‖x‖ ^ s` near the
  origin.
* `TauCeti.memLpLoc_memWkpLoc_not_memLpLoc_mul_norm_rpow`: the mixed-exponent product fails at
  `p = q = 4 / 3` in dimension `2`.
* `TauCeti.memWkpLoc_not_memWkpLoc_sq_norm_rpow`: squaring does not preserve `W^{1,4/3}_loc` in
  dimension `2`.

## References

* L. C. Evans, *Partial Differential Equations*, second edition, §5.2.2, Example 3.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (Proposition B.1.19 and the composition results it is compared with).
-/

public section

noncomputable section

namespace TauCeti

open Filter _root_.MeasureTheory Metric Set Topology TopologicalSpace

open scoped ENNReal

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
  {p : ENNReal} {U : Set E} {s : ℝ}

/-- For `0 < p < ∞`, the norm power `x ↦ ‖x‖ ^ s` is locally `Lᵖ` on every subset of `E`
when `-(Module.finrank ℝ E : ℝ) < s * p.toReal`. -/
theorem memLpLoc_norm_rpow (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (hs : -(Module.finrank ℝ E : ℝ) < s * p.toReal) :
    MemLpLoc p U (fun x : E => ‖x‖ ^ s) := by
  refine memLpLoc_iff.2 fun K _ hc => ?_
  rw [← integrable_norm_rpow_iff (measurable_norm.pow_const s).aestronglyMeasurable hp0 hp]
  simp only [Real.norm_eq_abs, Real.abs_rpow_of_nonneg (norm_nonneg _), abs_norm,
    ← Real.rpow_mul (norm_nonneg _)]
  refine (?_ : LocallyIntegrable _ volume).integrableOn_isCompact hc
  simpa only [zero_sub, norm_neg] using
    locallyIntegrable_norm_sub_rpow (mu := (volume : Measure E)) (s := s * p.toReal) hs (0 : E)

/-- For `0 < p < ∞` on a nontrivial space `E`, if `s * p.toReal ≤ -Module.finrank ℝ E` then
`x ↦ ‖x‖ ^ s` is not locally `Lᵖ` on any neighbourhood of the origin. -/
theorem not_memLpLoc_norm_rpow [Nontrivial E] (hp0 : p ≠ 0) (hp : p ≠ ∞) (hU : U ∈ 𝓝 (0 : E))
    (hs : s * p.toReal ≤ -(Module.finrank ℝ E : ℝ)) : ¬ MemLpLoc p U (fun x : E => ‖x‖ ^ s) := by
  intro h
  obtain ⟨r, hr, hrU⟩ := nhds_basis_closedBall.mem_iff.1 hU
  have hint := (memLpLoc_iff.1 h _ hrU (isCompact_closedBall 0 r)).integrable_norm_rpow hp0 hp
  simp only [Real.norm_eq_abs, Real.abs_rpow_of_nonneg (norm_nonneg _), abs_norm,
    ← Real.rpow_mul (norm_nonneg _)] at hint
  have hball : IntegrableOn (fun x : E => ‖x‖ ^ (s * p.toReal)) (ball 0 r) volume :=
    IntegrableOn.mono_set hint ball_subset_closedBall
  rw [integrableOn_norm_rpow_ball_iff hr] at hball
  linarith

/-- **Local `Lᵖ` membership of a norm power.** On a nontrivial space `E`, for `0 < p < ∞` and a
neighbourhood `U` of the origin, `x ↦ ‖x‖ ^ s` is locally `Lᵖ` on `U` iff
`-Module.finrank ℝ E < s * p.toReal`. -/
theorem memLpLoc_norm_rpow_iff [Nontrivial E] (hp0 : p ≠ 0) (hp : p ≠ ∞) (hU : U ∈ 𝓝 (0 : E)) :
    MemLpLoc p U (fun x : E => ‖x‖ ^ s) ↔ -(Module.finrank ℝ E : ℝ) < s * p.toReal :=
  ⟨fun h => not_le.1 fun hs => not_memLpLoc_norm_rpow hp0 hp hU hs h,
    memLpLoc_norm_rpow hp0 hp⟩

/-- The inverse norm `x ↦ ‖x‖⁻¹` is locally `Lᵖ` on every subset of `E` whenever
`p < Module.finrank ℝ E`. -/
theorem memLpLoc_norm_inv (hp : p < Module.finrank ℝ E) :
    MemLpLoc p U (fun x : E => ‖x‖⁻¹) :=
  memLpLoc_iff.2 fun _ _ hc => hc.memLp_norm_inv_restrict hp

/-- On a nontrivial space `E`, `x ↦ ‖x‖⁻¹` is not locally `Lᵖ` on any neighbourhood of the origin
when `Module.finrank ℝ E ≤ p` (including `p = ∞`). -/
theorem not_memLpLoc_norm_inv [Nontrivial E] (hU : U ∈ 𝓝 (0 : E))
    (hp : (Module.finrank ℝ E : ENNReal) ≤ p) :
    ¬ MemLpLoc p U (fun x : E => ‖x‖⁻¹) := by
  intro h
  obtain ⟨r, hr, hrU⟩ := nhds_basis_closedBall.mem_iff.1 hU
  exact not_memLp_norm_inv_closedBall hr hp (memLpLoc_iff.1 h _ hrU (isCompact_closedBall 0 r))

/-- **Local `Lᵖ` membership of `x ↦ ‖x‖⁻¹` for all `p : ℝ≥0∞`.** On a nontrivial space `E` and any
neighbourhood `U` of `0`, `‖x‖⁻¹ ∈ MemLpLoc p U` iff `p < Module.finrank ℝ E`. -/
theorem memLpLoc_norm_inv_iff [Nontrivial E] (hU : U ∈ 𝓝 (0 : E)) :
    MemLpLoc p U (fun x : E => ‖x‖⁻¹) ↔ p < Module.finrank ℝ E :=
  ⟨fun h => not_le.1 fun hp => not_memLpLoc_norm_inv hU hp h, memLpLoc_norm_inv⟩

end Normed

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
  {p : ENNReal} {U : Set E} {s : ℝ}

/-- For `1 ≤ p < ∞`, the norm power `x ↦ ‖x‖ ^ s` is in `W^{1,p}_loc` on every subset of `E` when
`-Module.finrank ℝ E < (s - 1) * p.toReal`. Its weak derivative is `s ‖x‖ ^ (s - 2) ⟪x, ·⟫`. -/
theorem memWkpLoc_one_norm_rpow (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    (hs : -(Module.finrank ℝ E : ℝ) < (s - 1) * p.toReal) :
    MemWkpLoc p U 1 (fun x : E => ‖x‖ ^ s) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hpr : 1 ≤ p.toReal := by
    simpa using ENNReal.toReal_mono hp hp1
  have hs1 : 1 - (Module.finrank ℝ E : ℝ) < s := by
    by_contra! hle
    have : (s - 1) * p.toReal ≤ (-(Module.finrank ℝ E : ℝ)) * 1 := by
      have : s - 1 ≤ -(Module.finrank ℝ E : ℝ) := by linarith
      nlinarith
    linarith
  refine memWkpLoc_succ_iff.2 ⟨memLpLoc_norm_rpow hp0 hp (by linarith),
    fun x => (s * ‖x‖ ^ (s - 2)) • innerSL ℝ x, hasWeakFDerivOn_norm_rpow hs1 _,
    memWkpLoc_zero_iff.2 (memLpLoc_iff.2 fun K hK hc => ?_)⟩
  refine ((memLpLoc_iff.1 (memLpLoc_norm_rpow hp0 hp hs) K hK hc).const_mul |s|).of_le
    (locallyIntegrable_norm_rpow_smul_innerSL hs1).aestronglyMeasurable.restrict
    (ae_of_all _ fun x => ?_)
  refine (norm_rpow_smul_innerSL_le s x).trans (le_of_eq ?_)
  rw [Real.norm_of_nonneg (by positivity)]

/-- On a nontrivial inner product space `E`, for `0 < p < ∞` and `s ≠ 0`, if
`(s - 1) * p.toReal ≤ -Module.finrank ℝ E` then `x ↦ ‖x‖ ^ s` is not in `W^{1,p}_loc` on any
neighbourhood of the origin: away from `0` a weak derivative agrees with the classical one, whose
norm `|s| ‖x‖ ^ (s - 1)` is not `p`-integrable near `0`. -/
theorem not_memWkpLoc_one_norm_rpow [Nontrivial E] (hp0 : p ≠ 0) (hp : p ≠ ∞) (hU : U ∈ 𝓝 (0 : E))
    (hs0 : s ≠ 0) (hs : (s - 1) * p.toReal ≤ -(Module.finrank ℝ E : ℝ)) :
    ¬ MemWkpLoc p U 1 (fun x : E => ‖x‖ ^ s) := by
  intro h
  obtain ⟨-, D, hD, hDp⟩ := memWkpLoc_succ_iff.1 h
  obtain ⟨r, hr, hrU⟩ := nhds_basis_closedBall.mem_iff.1 (interior_mem_nhds.2 hU)
  -- On the punctured interior, `D` is the classical derivative.
  let W : Opens E := Opens.interior U ⊓ ⟨{0}ᶜ, isOpen_compl_singleton⟩
  have hdiff : ∀ x ∈ (W : Set E), HasFDerivAt (fun x : E => ‖x‖ ^ s)
      ((s * ‖x‖ ^ (s - 2)) • innerSL ℝ x) x := fun x hx => hasFDerivAt_norm_rpow_of_ne s hx.2
  have hcont : ContinuousOn (fderiv ℝ fun x : E => ‖x‖ ^ s) W := by
    have hc : ContinuousOn (fun x : E => (s * ‖x‖ ^ (s - 2)) • innerSL ℝ x) W :=
      fun x hx => ((continuousAt_const.mul ((continuous_norm.continuousAt).rpow_const
        (Or.inl (norm_ne_zero_iff.2 hx.2)))).smul
          (innerSL ℝ).continuous.continuousAt).continuousWithinAt
    exact hc.congr fun x hx => (hdiff x hx).fderiv
  have hae := (hD.mono (inf_le_left : W ≤ Opens.interior U)).ae_eq_fderiv
    (hcont.locallyIntegrableOn W.isOpen.measurableSet)
    fun x hx => (hdiff x hx).differentiableAt
  have hae' := (ae_restrict_iff' W.isOpen.measurableSet).1 hae
  -- So `|s| ‖x‖ ^ (s - 1)` would be `p`-integrable on a ball about the origin.
  have hint := (memLpLoc_iff.1 (memWkpLoc_zero_iff.1 hDp) _ (hrU.trans interior_subset)
    (isCompact_closedBall 0 r)).integrable_norm_rpow hp0 hp
  have hball : IntegrableOn (fun x : E => |s| ^ p.toReal * ‖x‖ ^ ((s - 1) * p.toReal))
      (ball 0 r) volume := by
    refine (IntegrableOn.mono_set hint ball_subset_closedBall).congr ?_
    filter_upwards [ae_restrict_of_ae hae', ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (Measure.ae_ne volume (0 : E))] with x hx hxb hx0
    have hxW : x ∈ (W : Set E) :=
      ⟨by simpa using hrU (ball_subset_closedBall hxb), hx0⟩
    rw [hx hxW, norm_fderiv_norm_rpow_of_ne s hx0,
      Real.mul_rpow (abs_nonneg s) (Real.rpow_nonneg (norm_nonneg x) _),
      ← Real.rpow_mul (norm_nonneg x)]
  have hpos : (0 : ℝ) < |s| ^ p.toReal := Real.rpow_pos_of_pos (abs_pos.2 hs0) _
  rw [IntegrableOn, integrable_const_mul_iff hpos.ne'.isUnit, ← IntegrableOn,
    integrableOn_norm_rpow_ball_iff hr] at hball
  linarith

/-- **Local `W^{1,p}` membership of a norm power.** On a nontrivial inner product space `E`, for
`1 ≤ p < ∞`, `s ≠ 0`, and a neighbourhood `U` of the origin, `x ↦ ‖x‖ ^ s` lies in `W^{1,p}_loc(U)`
iff `-Module.finrank ℝ E < (s - 1) * p.toReal`. -/
theorem memWkpLoc_one_norm_rpow_iff [Nontrivial E] (hp1 : 1 ≤ p) (hp : p ≠ ∞) (hU : U ∈ 𝓝 (0 : E))
    (hs0 : s ≠ 0) :
    MemWkpLoc p U 1 (fun x : E => ‖x‖ ^ s) ↔ -(Module.finrank ℝ E : ℝ) < (s - 1) * p.toReal :=
  ⟨fun h => not_le.1 fun hs =>
      not_memWkpLoc_one_norm_rpow (zero_lt_one.trans_le hp1).ne' hp hU hs0 hs h,
    memWkpLoc_one_norm_rpow hp1 hp⟩

end InnerProduct

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
    (by rw [Complex.finrank_real_complex, toReal_four_thirds]; norm_num)

/-- **Mixed exponents at order zero fail at `p = 4 / 3`.** For `p = q = 4 / 3` on the unit disc,
`f = ‖z‖ ^ (-6 / 5)` is in `L^{4/3}_loc` and `g = ‖z‖ ^ (-2 / 5)` is in `W^{1,4/3}_loc`, but
`f g = ‖z‖ ^ (-8 / 5)` is not in `L^{4/3}_loc`, since `(8 / 5) (4 / 3) = 32 / 15 > 2`. -/
theorem memLpLoc_memWkpLoc_not_memLpLoc_mul_norm_rpow :
    MemLpLoc (4 / 3) (ball (0 : ℂ) 1) (fun z => ‖z‖ ^ (-6 / 5 : ℝ)) ∧
      MemWkpLoc (4 / 3) (ball (0 : ℂ) 1) 1 (fun z => ‖z‖ ^ (-2 / 5 : ℝ)) ∧
      ¬ MemLpLoc (4 / 3) (ball (0 : ℂ) 1) (fun z => ‖z‖ ^ (-6 / 5 : ℝ) * ‖z‖ ^ (-2 / 5 : ℝ)) := by
  have hp0 : (4 / 3 : ENNReal) ≠ 0 := by simp
  refine ⟨memLpLoc_norm_rpow hp0 four_thirds_ne_top
      (by rw [Complex.finrank_real_complex, toReal_four_thirds]; norm_num),
    memWkpLoc_norm_rpow_neg_two_fifths, ?_⟩
  have hmul : (fun z : ℂ => ‖z‖ ^ (-6 / 5 : ℝ) * ‖z‖ ^ (-2 / 5 : ℝ)) =
      fun z => ‖z‖ ^ (-8 / 5 : ℝ) := by
    funext z
    rw [← Real.rpow_add' (norm_nonneg z) (by norm_num)]
    norm_num
  rw [hmul]
  exact not_memLpLoc_norm_rpow hp0 four_thirds_ne_top (ball_mem_nhds 0 one_pos)
    (by rw [Complex.finrank_real_complex, toReal_four_thirds]; norm_num)

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
    (by norm_num) (by rw [Complex.finrank_real_complex, toReal_four_thirds]; norm_num)

end TauCeti
