/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital

/-!
# Star projections from the continuous functional calculus

If a function `f` takes star projections as values on the spectrum of `a`, for instance a real
function taking only the values `0` and `1` there, then `cfc f a` is a star projection, for any
scalar semiring and predicate carrying a continuous functional calculus. When `f` is continuous on
the spectrum and `a` satisfies the predicate this follows from multiplicativity of the functional
calculus; otherwise `cfc f a` is the junk value `0`. In particular the spectral projector
`cfc (Ω.indicator 1) a` is a star projection for every set `Ω` of scalars and every `a`.

When `a` is self-adjoint and invertible, `0` is not in its spectrum, so the spectral projectors
`P₊ = cfc ((Ioi 0).indicator 1) a` and `P₋ = cfc ((Iio 0).indicator 1) a` onto the positive and
negative parts of the spectrum are complementary, `P₊ + P₋ = 1`.

## Main results

* `TauCeti.isStarProjection_cfc` — `cfc f a` is a star projection when the values of `f` on the
  spectrum of `a` are star projections;
* `TauCeti.isStarProjection_cfc_indicator` — the spectral projector `cfc (Ω.indicator 1) a` is a
  star projection;
* `IsUnit.continuousOn_indicator_spectrum` — at an invertible element, the indicator of a set
  whose frontier is contained in `{0}` is continuous on the spectrum;
* `TauCeti.cfc_indicator_Ioi_add_cfc_indicator_Iio` — for invertible self-adjoint `a`, the
  positive and negative spectral projectors add up to `1`.
-/

public section

namespace TauCeti

section Semiring

variable {R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R] [MetricSpace R]
  [IsTopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A] [TopologicalSpace A]
  [Algebra R A] [ContinuousFunctionalCalculus R A p]

/-- If `f t` is a star projection at every point `t` of the spectrum of `a`, then `cfc f a` is a
star projection. Over `ℝ` the hypothesis says that `f t` is idempotent, that is, `0` or `1`. -/
theorem isStarProjection_cfc {f : R → R} {a : A}
    (hf : ∀ t ∈ spectrum R a, IsStarProjection (f t)) : IsStarProjection (cfc f a) := by
  refine ⟨?_, (cfc_star f a).symm.trans (cfc_congr fun t ht ↦ (hf t ht).isSelfAdjoint)⟩
  by_cases h : p a ∧ ContinuousOn f (spectrum R a)
  · rw [IsIdempotentElem, ← cfc_mul f f a h.2 h.2]
    exact cfc_congr fun t ht ↦ (hf t ht).isIdempotentElem
  · rw [cfc_apply_of_not_and a h]
    exact .zero

/-- The spectral projector `cfc (Ω.indicator 1) a` is a star projection for every set `Ω` of
scalars. (When `a` does not satisfy the predicate of the functional calculus, or the indicator is
not continuous on its spectrum, it is the junk value `0`.) -/
theorem isStarProjection_cfc_indicator (a : A) (Ω : Set R) :
    IsStarProjection (cfc (Ω.indicator (1 : R → R)) a) :=
  isStarProjection_cfc fun t _ ↦ by
    by_cases ht : t ∈ Ω <;> simp [ht, IsStarProjection.zero, IsStarProjection.one]

end Semiring

variable {A : Type*} [Ring A] [StarRing A] [TopologicalSpace A] [Algebra ℝ A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

open Set

omit [StarRing A] [TopologicalSpace A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] in
/-- At an invertible element, the indicator of a set whose frontier is contained in `{0}`, such as
a half-line ending at `0`, is continuous on the spectrum, since the spectrum avoids `0`. -/
theorem _root_.IsUnit.continuousOn_indicator_spectrum {a : A} (ha : IsUnit a) {Ω : Set ℝ}
    (hΩ : frontier Ω ⊆ {0}) : ContinuousOn (Ω.indicator (1 : ℝ → ℝ)) (spectrum ℝ a) := by
  classical
  rw [← piecewise_eq_indicator]
  refine ContinuousOn.piecewise (fun x hx ↦ ?_) continuousOn_const continuousOn_const
  exact absurd (mem_singleton_iff.mp (hΩ hx.2) ▸ hx.1) (spectrum.zero_notMem ℝ ha)

/-- For an invertible self-adjoint `a`, the spectral projectors onto the positive and the negative
parts of the spectrum add up to `1`. -/
theorem cfc_indicator_Ioi_add_cfc_indicator_Iio {a : A} (ha : IsUnit a)
    (ha' : IsSelfAdjoint a := by cfc_tac) :
    cfc ((Ioi (0 : ℝ)).indicator 1) a + cfc ((Iio (0 : ℝ)).indicator 1) a = 1 := by
  rw [← cfc_add (hf := ha.continuousOn_indicator_spectrum frontier_Ioi.subset)
    (hg := ha.continuousOn_indicator_spectrum frontier_Iio.subset), ← cfc_const_one ℝ a]
  refine cfc_congr fun x hx ↦ ?_
  rcases lt_or_gt_of_ne (ne_of_mem_of_not_mem hx (spectrum.zero_notMem ℝ ha)) with hx | hx <;>
    simp [hx, hx.not_gt]

end TauCeti
