/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Topology.Semicontinuity.Hemicontinuity
import TauCeti.Topology.Frontier

/-!
# Star projections from the continuous functional calculus

If a real function `f` takes only the values `0` and `1` on the spectrum of `a`, then `cfc f a` is
a star projection. When `f` is continuous on the spectrum and `a` is self-adjoint this follows
from multiplicativity of the functional calculus; otherwise `cfc f a` is the junk value `0`. In
particular the spectral projector `cfc (Ω.indicator 1) a` is a star projection for every set
`Ω ⊆ ℝ` and every `a`.

The spectral projector of `s` depends continuously on a self-adjoint element `a` as long as the
frontier of `s` misses the spectrum of `a`: the spectrum is upper hemicontinuous, so nearby
spectra stay in a compact set on which the indicator is continuous.

When `a` is self-adjoint and invertible, `0` is not in its spectrum, so the spectral projectors
`P₊ = cfc ((Ioi 0).indicator 1) a` and `P₋ = cfc ((Iio 0).indicator 1) a` onto the positive and
negative parts of the spectrum are complementary, `P₊ + P₋ = 1`.

## Main results

* `TauCeti.isStarProjection_cfc` — `cfc f a` is a star projection when `f` is idempotent-valued on
  the spectrum of `a`;
* `TauCeti.isStarProjection_cfc_indicator` — the spectral projector `cfc (Ω.indicator 1) a` is a
  star projection;
* `IsUnit.continuousOn_indicator_spectrum` — at an invertible element, the indicator of a set
  whose frontier is contained in `{0}` is continuous on the spectrum;
* `TauCeti.cfc_indicator_Ioi_add_cfc_indicator_Iio` — for invertible self-adjoint `a`, the
  positive and negative spectral projectors add up to `1`.
* `Filter.Tendsto.eventually_disjoint_spectrum` — a closed set missing the spectrum of `a₀`
  misses the spectra of all elements near `a₀`.
* `Filter.Tendsto.cfc_indicator` — the spectral projector `cfc (s.indicator 1) a` is continuous
  in a self-adjoint `a` whose spectrum misses the frontier of `s`.
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

open Filter Topology

variable {ι : Type*} {l : Filter ι}

/-- A closed set disjoint from the spectrum of `a₀` is disjoint from the spectra of all elements
near `a₀`, by upper hemicontinuity of the spectrum. -/
theorem Filter.Tendsto.eventually_disjoint_spectrum {𝕜 B : Type*} [NormedField 𝕜] [ProperSpace 𝕜]
    [NormedRing B] [NormedAlgebra 𝕜 B] [CompleteSpace B] {a : ι → B} {a₀ : B} {K : Set 𝕜}
    (ha : Tendsto a l (𝓝 a₀)) (hK : IsClosed K) (hKa : Disjoint K (spectrum 𝕜 a₀)) :
    ∀ᶠ i in l, Disjoint K (spectrum 𝕜 (a i)) :=
  ha.eventually ((upperHemicontinuous_spectrum 𝕜 B).forall_isOpen a₀ _ hK.isOpen_compl
    hKa.subset_compl_left) |>.mono fun _ h ↦ disjoint_compl_right.mono_right h

/-- **Continuity of spectral projectors.** If self-adjoint elements `a i` converge to a
self-adjoint `a₀` whose spectrum misses the frontier of `s`, then their spectral projectors onto
`s` converge to that of `a₀`. -/
theorem Filter.Tendsto.cfc_indicator {B : Type*} [CStarAlgebra B] {a : ι → B} {a₀ : B}
    {s : Set ℝ} (ha : Tendsto a l (𝓝 a₀)) (hsa : ∀ᶠ i in l, IsSelfAdjoint (a i))
    (ha₀ : IsSelfAdjoint a₀) (hs : Disjoint (frontier s) (spectrum ℝ a₀)) :
    Tendsto (fun i ↦ cfc (s.indicator (1 : ℝ → ℝ)) (a i)) l
      (𝓝 (cfc (s.indicator (1 : ℝ → ℝ)) a₀)) := by
  -- Nearby spectra lie in a compact neighbourhood of the spectrum of `a₀` missing `frontier s`.
  obtain ⟨L, hL, hspec, hLU⟩ := exists_compact_between (spectrum.isCompact a₀)
    isClosed_frontier.isOpen_compl hs.subset_compl_left
  have hev : ∀ᶠ i in l, spectrum ℝ (a i) ⊆ L :=
    ha.eventually ((upperHemicontinuous_spectrum ℝ B).forall_isOpen a₀ _ isOpen_interior hspec)
      |>.mono fun _ h ↦ h.trans interior_subset
  exact ha.cfc hL _ hev hsa (hspec.trans interior_subset) ha₀
    (TauCeti.continuousOn_indicator_of_disjoint_frontier continuousOn_const
      (disjoint_compl_right.mono_right hLU))

end Continuity
