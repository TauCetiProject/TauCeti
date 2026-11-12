/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import TauCeti.Analysis.Normed.Algebra.Spectrum
import TauCeti.Topology.Algebra.Indicator

/-!
# Star projections from the continuous functional calculus

If a real function `f` takes only the values `0` and `1` on the spectrum of `a`, then `cfc f a` is
a star projection. When `f` is continuous on the spectrum and `a` is self-adjoint this follows
from multiplicativity of the functional calculus; otherwise `cfc f a` is the junk value `0`. In
particular the spectral projector `cfc (Ω.indicator 1) a` is a star projection for every set
`Ω ⊆ ℝ` and every `a`.

When `a` is self-adjoint and invertible, `0` is not in its spectrum, so the spectral projectors
`P₊ = cfc ((Ioi 0).indicator 1) a` and `P₋ = cfc ((Iio 0).indicator 1) a` onto the positive and
negative parts of the spectrum are complementary, `P₊ + P₋ = 1`.

In a complete normed algebra with an isometric functional calculus, such as a C⋆-algebra, the
spectral projector `cfc (Ω.indicator 1) a` depends continuously on the self-adjoint element `a`
wherever the spectrum of `a` avoids the frontier of `Ω`.

## Main results

* `TauCeti.isStarProjection_cfc` — `cfc f a` is a star projection when `f` is idempotent-valued on
  the spectrum of `a`;
* `TauCeti.isStarProjection_cfc_indicator` — the spectral projector `cfc (Ω.indicator 1) a` is a
  star projection;
* `IsUnit.continuousOn_indicator_spectrum` — at an invertible element, the indicator of a set
  whose frontier is contained in `{0}` is continuous on the spectrum;
* `TauCeti.cfc_indicator_Ioi_add_cfc_indicator_Iio` — for invertible self-adjoint `a`, the
  positive and negative spectral projectors add up to `1`;
* `IsSelfAdjoint.continuousWithinAt_cfc_indicator` — the spectral projector depends continuously
  on the self-adjoint element when the frontier of the set avoids the spectrum.
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
  · obtain ⟨_, hcont⟩ := h
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
  rcases lt_or_gt_of_ne (ne_of_mem_of_not_mem hx (spectrum.zero_notMem ℝ ha)) with hx | hx
  · simp [indicator_of_notMem, indicator_of_mem, hx, hx.not_gt]
  · simp [indicator_of_notMem, indicator_of_mem, hx, hx.not_gt]

end TauCeti

section Continuity

open Filter Set Topology

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
  [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [ContinuousStar A] [CompleteSpace A]

/-- The spectral projector for a set `Ω` depends continuously on the self-adjoint element at an
element whose spectrum avoids the frontier of `Ω`. -/
theorem IsSelfAdjoint.continuousWithinAt_cfc_indicator {a : A} (ha : IsSelfAdjoint a)
    {Ω : Set ℝ} (hΩ : Disjoint (frontier Ω) (spectrum ℝ a)) :
    ContinuousWithinAt (cfc (Ω.indicator (1 : ℝ → ℝ))) {b | IsSelfAdjoint b} a := by
  set t := {b : A | IsSelfAdjoint b ∧ spectrum ℝ b ⊆ (frontier Ω)ᶜ}
  have hcont : ContinuousOn (cfc (Ω.indicator (1 : ℝ → ℝ))) t :=
    ContinuousOn.cfc_of_mem_nhdsSet (a := id) _
      (isClosed_frontier.isOpen_compl.mem_nhdsSet.2 (iUnion₂_subset fun b hb ↦ hb.2))
      continuousOn_id (fun b hb ↦ hb.1)
      (continuousOn_const.continuousOn_indicator_of_disjoint_frontier disjoint_compl_right)
  refine (hcont.continuousWithinAt ⟨ha, hΩ.subset_compl_left⟩).mono_of_mem_nhdsWithin ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (spectrum.eventually_disjoint_of_isClosed isClosed_frontier hΩ)]
    with b hb hb'
  exact ⟨hb, hb'.subset_compl_left⟩

end Continuity
