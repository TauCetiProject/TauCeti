/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs

/-!
# Star projections from the continuous functional calculus

If a real function `f` takes only the values `0` and `1` on the spectrum of `a`, then `cfc f a` is
a star projection. When `f` is continuous on the spectrum and `a` is self-adjoint this follows
from multiplicativity of the functional calculus; otherwise `cfc f a` is the junk value `0`. In
particular the spectral projector `cfc (Ω.indicator 1) a` is a star projection for every set
`Ω ⊆ ℝ` and every `a`.

When `a` is self-adjoint and invertible, `0` is not in its spectrum, so the spectral projectors
`P₊ = cfc ((Ioi 0).indicator 1) a` and `P₋ = cfc ((Iio 0).indicator 1) a` onto the positive and
negative parts of the spectrum are complementary, `P₊ + P₋ = 1`. They are given by the sign
`a |a|⁻¹` of `a`, where `|a| = CFC.abs a = √(a⋆ a)`: `2 P₊ = 1 + a |a|⁻¹` and
`2 P₋ = 1 - a |a|⁻¹`. These formulas express the two projectors through multiplication, inversion
and the square root alone, without any choice of eigenvectors; for operators on a
finite-dimensional real space they give the smooth dependence of the projectors on `a`
(`ContinuousLinearMap.contDiffOn_cfc_indicator_Ioi`).

## Main results

* `TauCeti.isStarProjection_cfc` — `cfc f a` is a star projection when `f` is idempotent-valued on
  the spectrum of `a`;
* `TauCeti.isStarProjection_cfc_indicator` — the spectral projector `cfc (Ω.indicator 1) a` is a
  star projection;
* `TauCeti.cfc_indicator_Ioi_add_cfc_indicator_Iio` — for invertible self-adjoint `a`, the
  positive and negative spectral projectors add up to `1`;
* `TauCeti.two_smul_cfc_indicator_Ioi` and `TauCeti.two_smul_cfc_indicator_Iio` — for invertible
  self-adjoint `a`, `2 P₊ = 1 + a |a|⁻¹` and `2 P₋ = 1 - a |a|⁻¹`.

## References

* N. J. Higham, *Functions of Matrices: Theory and Computation*, SIAM, 2008, Chapter 5 (the
  matrix sign function and its spectral projectors).
-/

public section

namespace TauCeti

variable {A : Type*} [Ring A] [StarRing A] [TopologicalSpace A] [Algebra ℝ A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

/-- If `f t` is idempotent (that is, `0` or `1`) at every point `t` of the spectrum of `a`, then
`cfc f a` is a star projection. -/
theorem isStarProjection_cfc {f : ℝ → ℝ} {a : A}
    (hf : ∀ t ∈ spectrum ℝ a, IsIdempotentElem (f t)) : IsStarProjection (cfc f a) := by
  by_cases h : IsSelfAdjoint a ∧ ContinuousOn f (spectrum ℝ a)
  · obtain ⟨ha, hcont⟩ := h
    refine ⟨?_, cfc_predicate f a⟩
    rw [IsIdempotentElem, ← cfc_mul f f a]
    exact cfc_congr hf
  · rcases not_and_or.1 h with ha | hcont
    · rw [cfc_apply_of_not_predicate a ha]
      exact .zero _
    · rw [cfc_apply_of_not_continuousOn a hcont]
      exact .zero _

/-- The spectral projector `cfc (Ω.indicator 1) a` is a star projection for every `Ω ⊆ ℝ`. (When
`a` is not self-adjoint, or the indicator is not continuous on its spectrum, it is the junk value
`0`.) -/
theorem isStarProjection_cfc_indicator (a : A) (Ω : Set ℝ) :
    IsStarProjection (cfc (Ω.indicator (1 : ℝ → ℝ)) a) :=
  isStarProjection_cfc fun t _ ↦ by by_cases ht : t ∈ Ω <;> simp [ht, IsIdempotentElem]

open Set

omit [StarRing A] [TopologicalSpace A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] in
/-- At an invertible element, the indicator of a set whose frontier is `{0}`, such as a half-line
ending at `0`, is continuous on the spectrum, since the spectrum avoids `0`. -/
private theorem continuousOn_indicator_spectrum {Ω : Set ℝ} (hΩ : frontier Ω = {0}) {a : A}
    (ha : IsUnit a) : ContinuousOn (Ω.indicator (1 : ℝ → ℝ)) (spectrum ℝ a) := by
  classical
  rw [← piecewise_eq_indicator]
  refine ContinuousOn.piecewise (fun x hx ↦ ?_) continuousOn_const continuousOn_const
  rw [hΩ, mem_inter_iff, mem_singleton_iff] at hx
  exact absurd (hx.2 ▸ hx.1) (spectrum.zero_notMem ℝ ha)

omit [StarRing A] [TopologicalSpace A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] in
/-- At an invertible element, the scalar sign `x ‖x‖⁻¹` is continuous on the spectrum. -/
private theorem continuousOn_mul_norm_inv_spectrum {a : A} (ha : IsUnit a) :
    ContinuousOn (fun x : ℝ ↦ x * ‖x‖⁻¹) (spectrum ℝ a) :=
  continuousOn_id.mul <| continuous_norm.continuousOn.inv₀ fun _ hx ↦
    norm_ne_zero_iff.mpr (ne_of_mem_of_not_mem hx (spectrum.zero_notMem ℝ ha))

/-- For an invertible self-adjoint `a`, the spectral projectors onto the positive and the negative
parts of the spectrum add up to `1`. -/
theorem cfc_indicator_Ioi_add_cfc_indicator_Iio {a : A} (ha : IsUnit a)
    (ha' : IsSelfAdjoint a := by cfc_tac) :
    cfc ((Ioi (0 : ℝ)).indicator 1) a + cfc ((Iio (0 : ℝ)).indicator 1) a = 1 := by
  rw [← cfc_add (hf := continuousOn_indicator_spectrum frontier_Ioi ha)
    (hg := continuousOn_indicator_spectrum frontier_Iio ha), ← cfc_const_one ℝ a]
  refine cfc_congr fun x hx ↦ ?_
  rcases lt_or_gt_of_ne (ne_of_mem_of_not_mem hx (spectrum.zero_notMem ℝ ha)) with hx | hx
  · simp [indicator_of_notMem, indicator_of_mem, hx, hx.not_gt]
  · simp [indicator_of_notMem, indicator_of_mem, hx, hx.not_gt]

section Abs

variable [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A] [IsTopologicalRing A]
  [T2Space A]

/-- The sign `a |a|⁻¹` of an invertible self-adjoint `a` is the functional calculus of the
scalar sign `x ‖x‖⁻¹`. -/
private theorem mul_ringInverse_abs_eq_cfc {a : A} (ha : IsUnit a)
    (ha' : IsSelfAdjoint a := by cfc_tac) :
    a * Ring.inverse (CFC.abs a) = cfc (fun x : ℝ ↦ x * ‖x‖⁻¹) a := by
  have hnorm : ∀ x ∈ spectrum ℝ a, ‖x‖ ≠ 0 := fun x hx ↦
    norm_ne_zero_iff.mpr (ne_of_mem_of_not_mem hx (spectrum.zero_notMem ℝ ha))
  rw [cfc_mul (fun x : ℝ ↦ x) (fun x : ℝ ↦ ‖x‖⁻¹) a
      (hg := continuous_norm.continuousOn.inv₀ hnorm),
    cfc_id' ℝ a, cfc_inv (‖·‖) a hnorm, CFC.abs_eq_cfc_norm a]

/-- **The positive spectral projector through the sign.** For an invertible self-adjoint `a`, the
spectral projector `P₊` onto the positive part of the spectrum satisfies `2 P₊ = 1 + a |a|⁻¹`. -/
theorem two_smul_cfc_indicator_Ioi {a : A} (ha : IsUnit a)
    (ha' : IsSelfAdjoint a := by cfc_tac) :
    (2 : ℝ) • cfc ((Ioi (0 : ℝ)).indicator 1) a = 1 + a * Ring.inverse (CFC.abs a) := by
  rw [mul_ringInverse_abs_eq_cfc ha,
    ← cfc_smul (hf := continuousOn_indicator_spectrum frontier_Ioi ha), ← cfc_const_one ℝ a,
    ← cfc_add (a := a) (fun _ ↦ (1 : ℝ)) _ (hg := continuousOn_mul_norm_inv_spectrum ha)]
  refine cfc_congr fun x hx ↦ ?_
  rcases lt_or_gt_of_ne (ne_of_mem_of_not_mem hx (spectrum.zero_notMem ℝ ha)) with hx | hx
  · simp [indicator_of_notMem, hx.not_gt, abs_of_neg hx, hx.ne]
  · simp [indicator_of_mem, hx, abs_of_pos hx, hx.ne']
    norm_num

/-- **The negative spectral projector through the sign.** For an invertible self-adjoint `a`, the
spectral projector `P₋` onto the negative part of the spectrum satisfies `2 P₋ = 1 - a |a|⁻¹`. -/
theorem two_smul_cfc_indicator_Iio {a : A} (ha : IsUnit a)
    (ha' : IsSelfAdjoint a := by cfc_tac) :
    (2 : ℝ) • cfc ((Iio (0 : ℝ)).indicator 1) a = 1 - a * Ring.inverse (CFC.abs a) := by
  rw [mul_ringInverse_abs_eq_cfc ha,
    ← cfc_smul (hf := continuousOn_indicator_spectrum frontier_Iio ha), ← cfc_const_one ℝ a,
    ← cfc_sub (fun _ ↦ (1 : ℝ)) _ a (hg := continuousOn_mul_norm_inv_spectrum ha)]
  refine cfc_congr fun x hx ↦ ?_
  rcases lt_or_gt_of_ne (ne_of_mem_of_not_mem hx (spectrum.zero_notMem ℝ ha)) with hx | hx
  · simp [indicator_of_mem, hx, abs_of_neg hx, hx.ne]
    norm_num
  · simp [indicator_of_notMem, hx.not_gt, abs_of_pos hx, hx.ne']

end Abs

end TauCeti
