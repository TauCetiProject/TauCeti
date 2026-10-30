/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.SimpleFuncDense

/-!
# Uniform approximation by simple functions

Mathlib's `MeasureTheory.SimpleFunc.approxOn f hf s y₀ h₀` is a sequence of simple functions with
values in `s` converging pointwise to a measurable function `f` whose values lie in the closure of
the separable set `s` (`MeasureTheory.SimpleFunc.tendsto_approxOn`). When `s` is totally bounded
the convergence is uniform: finitely many points of the dense sequence underlying `approxOn`
already form an `ε`-net of `closure s`, and from then on every approximant is within `ε` of `f`.

Thus a measurable function with totally bounded range, such as a bounded measurable function into
a finite-dimensional normed space, is a uniform limit of measurable finite-range functions whose
values stay in any prescribed totally bounded set containing its range. This is the
approximation behind integration of bounded measurable functions against projection-valued
measures, where uniform rather than pointwise control is needed.

## Main statements

* `MeasureTheory.SimpleFunc.tendstoUniformlyOn_nearestPt` — nearest-point projections onto the
  initial segments of a sequence converge uniformly to the identity on every totally bounded set
  in the closure of the sequence.
* `MeasureTheory.SimpleFunc.tendstoUniformly_approxOn` — for totally bounded `s`, the simple
  approximants `approxOn f hf s y₀ h₀ n` converge to `f` uniformly.
-/

public section

open Filter Set TopologicalSpace
open scoped ENNReal

namespace MeasureTheory.SimpleFunc

variable {α β : Type*} [MeasurableSpace α] [PseudoEMetricSpace α] [OpensMeasurableSpace α]

/-- The nearest-point projections `nearestPt e N` onto `{e 0, …, e N}` converge to the identity
uniformly on every totally bounded set contained in the closure of the range of `e`. -/
theorem tendstoUniformlyOn_nearestPt {e : ℕ → α} {S : Set α} (hS : TotallyBounded S)
    (hSe : S ⊆ closure (range e)) :
    TendstoUniformlyOn (fun N ↦ ⇑(nearestPt e N)) id atTop S := by
  refine EMetric.tendstoUniformlyOn_iff.2 fun ε hε ↦ ?_
  obtain ⟨t, htS, ht, hSt⟩ := EMetric.totallyBounded_iff'.1 hS (ε / 2) (ENNReal.half_pos hε.ne')
  -- each point `z` of the finite `ε / 2`-net is within `ε / 2` of some `e k`; once `N ≥ k`, the
  -- nearest point to any `y` within `ε / 2` of `z` is at least as close to `y` as `e k` is
  have hnet : ∀ z ∈ t, ∀ᶠ N in atTop, ∀ y ∈ Metric.eball z (ε / 2),
      edist y (nearestPt e N y) < ε := by
    intro z hz
    obtain ⟨-, ⟨k, rfl⟩, hk⟩ :=
      EMetric.mem_closure_iff.1 (hSe (htS hz)) (ε / 2) (ENNReal.half_pos hε.ne')
    filter_upwards [eventually_ge_atTop k] with N hN y hy
    calc edist y (nearestPt e N y) = edist (nearestPt e N y) y := edist_comm _ _
      _ ≤ edist (e k) y := edist_nearestPt_le e y hN
      _ ≤ edist (e k) z + edist z y := edist_triangle _ _ _
      _ < ε / 2 + ε / 2 := by
        gcongr
        · rwa [edist_comm]
        · rwa [edist_comm, ← Metric.mem_eball]
      _ = ε := ENNReal.add_halves ε
  filter_upwards [(eventually_all_finite ht).2 hnet] with N hN y hy
  obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.1 (hSt hy)
  exact hN z hz y hyz

variable [MeasurableSpace β]

/-- If `s` is totally bounded, the simple approximants `approxOn f hf s y₀ h₀ n` of a measurable
function `f` with values in the closure of `s` converge to `f` uniformly. -/
theorem tendstoUniformly_approxOn {f : β → α} (hf : Measurable f) {s : Set α} {y₀ : α}
    (h₀ : y₀ ∈ s) [SeparableSpace s] (hs : TotallyBounded s) (hfs : ∀ x, f x ∈ closure s) :
    TendstoUniformly (fun n ↦ ⇑(approxOn f hf s y₀ h₀ n)) f atTop := by
  have : Nonempty s := ⟨⟨y₀, h₀⟩⟩
  -- the points used by `approxOn` are `y₀` followed by the dense sequence of `s`
  have hsub : closure s ⊆ closure (range fun k ↦ (Nat.casesOn k y₀ ((↑) ∘ denseSeq s) : α)) := by
    refine closure_minimal (fun y hy ↦ closure_mono (s := range ((↑) ∘ denseSeq s)) ?_ ?_)
      isClosed_closure
    · rintro _ ⟨k, rfl⟩
      exact ⟨k + 1, rfl⟩
    · rw [range_comp]
      exact image_closure_subset_closure_image continuous_subtype_val
        ⟨⟨y, hy⟩, (denseRange_denseSeq s).closure_range ▸ mem_univ _, rfl⟩
  rw [← tendstoUniformlyOn_univ]
  simpa only [approxOn, coe_comp, Function.id_comp] using
    ((tendstoUniformlyOn_nearestPt hs.closure hsub).comp f).mono fun x _ ↦ hfs x

end MeasureTheory.SimpleFunc
