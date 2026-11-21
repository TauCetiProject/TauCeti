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

For `p < ∞`, `‖z‖ ^ s` is in `Lᵖ_loc` near the origin exactly when `s p > -2`. For
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

/-- For `p < ∞`, the norm power `z ↦ ‖z‖ ^ s` is locally `Lᵖ` on every subset of the plane
when `s p > -2`. -/
theorem memLpLoc_norm_rpow (hp : p ≠ ∞) (hs : -2 < s * p.toReal) :
    MemLpLoc p U (fun z : ℂ => ‖z‖ ^ s) :=
  memLpLoc_iff.2 fun K _ hc => hc.isBounded.memLp_norm_rpow_restrict hp
    (by rw [Complex.finrank_real_complex]; push_cast; linarith)

/-- If `s p ≤ -2` then `z ↦ ‖z‖ ^ s` is not locally `Lᵖ` on any neighbourhood of the origin.
The hypothesis forces `p < ∞`. -/
theorem not_memLpLoc_norm_rpow (hU : U ∈ 𝓝 (0 : ℂ))
    (hs : s * p.toReal ≤ -2) : ¬ MemLpLoc p U (fun z : ℂ => ‖z‖ ^ s) := by
  intro h
  have hp : p ≠ ∞ := by
    rintro rfl
    simp only [ENNReal.toReal_top, mul_zero] at hs
    linarith
  obtain ⟨r, hr, hrU⟩ := nhds_basis_closedBall.mem_iff.1 hU
  have h2 := (isBounded_closedBall.memLp_norm_rpow_restrict_iff (closedBall_mem_nhds 0 hr) hp).1
    (memLpLoc_iff.1 h _ hrU (isCompact_closedBall 0 r))
  rw [Complex.finrank_real_complex] at h2
  push_cast at h2
  linarith

/-- **Local `Lᵖ` membership of a norm power.** For `p < ∞` and a neighbourhood `U` of the
origin, `z ↦ ‖z‖ ^ s` is locally `Lᵖ` on `U` exactly when `s p > -2`. -/
theorem memLpLoc_norm_rpow_iff (hp : p ≠ ∞) (hU : U ∈ 𝓝 (0 : ℂ)) :
    MemLpLoc p U (fun z : ℂ => ‖z‖ ^ s) ↔ -2 < s * p.toReal :=
  ⟨fun h => not_le.1 fun hs => not_memLpLoc_norm_rpow hU hs h,
    memLpLoc_norm_rpow hp⟩

/-- For `1 ≤ p < ∞`, the norm power `z ↦ ‖z‖ ^ s` is in `W^{1,p}_loc` on every subset of the
plane when `(s - 1) p > -2`. Its weak derivative is `s ‖z‖ ^ (s - 2) ⟪z, ·⟫`. -/
theorem memWkpLoc_one_norm_rpow (hp1 : 1 ≤ p) (hp : p ≠ ∞) (hs : -2 < (s - 1) * p.toReal) :
    MemWkpLoc p U 1 (fun z : ℂ => ‖z‖ ^ s) := by
  have hpr : 1 ≤ p.toReal := by
    simpa using ENNReal.toReal_mono hp hp1
  have hs1 : 1 - (Module.finrank ℝ ℂ : ℝ) < s := by
    rw [Complex.finrank_real_complex]
    push_cast
    linarith [neg_lt_of_neg_lt_mul (by norm_num) hpr hs]
  refine memWkpLoc_succ_iff.2 ⟨memLpLoc_norm_rpow hp (by nlinarith),
    fun z => (s * ‖z‖ ^ (s - 2)) • innerSL ℝ z, hasWeakFDerivOn_norm_rpow hs1 _,
    memWkpLoc_zero_iff.2 (memLpLoc_iff.2 fun K hK hc => ?_)⟩
  refine ((memLpLoc_iff.1 (memLpLoc_norm_rpow hp hs) K hK hc).const_mul |s|).of_le
    (locallyIntegrable_norm_rpow_smul_innerSL hs1).aestronglyMeasurable.restrict
    (ae_of_all _ fun z => ?_)
  refine (norm_rpow_smul_innerSL_le s z).trans (le_of_eq ?_)
  rw [Real.norm_of_nonneg (by positivity)]

/-- For `s ≠ 0`, if `(s - 1) p ≤ -2` then `z ↦ ‖z‖ ^ s` is not in `W^{1,p}_loc` on any
neighbourhood of the origin. The hypothesis forces `0 < p < ∞`. -/
theorem not_memWkpLoc_one_norm_rpow (hU : U ∈ 𝓝 (0 : ℂ))
    (hs0 : s ≠ 0) (hs : (s - 1) * p.toReal ≤ -2) :
    ¬ MemWkpLoc p U 1 (fun z : ℂ => ‖z‖ ^ s) := by
  intro h
  have hp0 : p ≠ 0 := by
    rintro rfl
    simp only [ENNReal.toReal_zero, mul_zero] at hs
    linarith
  have hp : p ≠ ∞ := by
    rintro rfl
    simp only [ENNReal.toReal_top, mul_zero] at hs
    linarith
  obtain ⟨-, D, hD, hDp⟩ := memWkpLoc_succ_iff.1 h
  obtain ⟨r, hr, hrU⟩ := nhds_basis_closedBall.mem_iff.1 (interior_mem_nhds.2 hU)
  -- The weak derivative `D` is `p`-integrable on a ball about the origin.
  have hint := (memLpLoc_iff.1 (memWkpLoc_zero_iff.1 hDp) _ (hrU.trans interior_subset)
    (isCompact_closedBall 0 r)).integrable_norm_rpow hp0 hp
  have h2 := hD.neg_finrank_lt_sub_one_mul_of_integrableOn hs0 hr
    (ball_subset_closedBall.trans hrU) (IntegrableOn.mono_set hint ball_subset_closedBall)
  rw [Complex.finrank_real_complex] at h2
  push_cast at h2
  linarith

/-- **Local `W^{1,p}` membership of a norm power.** For `1 ≤ p < ∞`, `s ≠ 0` and a neighbourhood
`U` of the origin, `z ↦ ‖z‖ ^ s` is in `W^{1,p}_loc` on `U` exactly when `(s - 1) p > -2`. -/
theorem memWkpLoc_one_norm_rpow_iff (hp1 : 1 ≤ p) (hp : p ≠ ∞) (hU : U ∈ 𝓝 (0 : ℂ))
    (hs0 : s ≠ 0) :
    MemWkpLoc p U 1 (fun z : ℂ => ‖z‖ ^ s) ↔ -2 < (s - 1) * p.toReal :=
  ⟨fun h => not_le.1 fun hs =>
      not_memWkpLoc_one_norm_rpow hU hs0 hs h,
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
  refine ⟨memLpLoc_norm_rpow four_thirds_ne_top (by rw [toReal_four_thirds]; norm_num),
    memWkpLoc_norm_rpow_neg_two_fifths, ?_⟩
  have hmul : (fun z : ℂ => ‖z‖ ^ (-6 / 5 : ℝ) * ‖z‖ ^ (-2 / 5 : ℝ)) =
      fun z => ‖z‖ ^ (-8 / 5 : ℝ) := by
    funext z
    rw [← Real.rpow_add' (norm_nonneg z) (by norm_num)]
    norm_num
  rw [hmul]
  exact not_memLpLoc_norm_rpow (ball_mem_nhds 0 one_pos) (by rw [toReal_four_thirds]; norm_num)

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
  exact not_memWkpLoc_one_norm_rpow (ball_mem_nhds 0 one_pos) (by norm_num)
    (by rw [toReal_four_thirds]; norm_num)

end TauCeti
