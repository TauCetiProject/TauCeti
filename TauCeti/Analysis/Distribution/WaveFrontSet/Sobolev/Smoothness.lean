/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Tempered
import TauCeti.Analysis.Distribution.Sobolev
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding

/-!
# Distributions of every Sobolev order are smooth

Let `T` be a complex distribution on an open subset `Ω` of a finite-dimensional real inner product
space `E`. A smooth function is `H^s` near every point for every real `s`, so the `H^s` singular
supports `Distribution.sobolevSingularSupport s T` lie in the singular support
`Distribution.singularSupport T`. This file proves the converse: `T` is a smooth function near
`x` exactly when, for every `s`, `T` is `H^s` near every point of a neighbourhood of `x` that does
not depend on `s` (`Distribution.notMem_singularSupport_iff_eventually_forall_isLocallySobolevAt`).
This is the step from elliptic regularity on the Sobolev scale, `P T ∈ H^s` near `x` ⟹
`T ∈ H^(s + m)` near `x`, to `C^∞` regularity: if `P T` is smooth near `x`, such a statement makes
`T` `H^s` near every point close to `x`, for every `s`, and this file then makes `T` smooth there.

The argument has two steps.

* **One cutoff for all orders.** If `T` is `H^s` near every point of the support of a test
  function `φ`, a partition of unity splits `φ` into finitely many test functions, each supported
  in a neighbourhood on which every cut-off distribution lies in `H^s`; so `φ T ∈ H^s`. If this
  holds for every `s`, then `φ T` lies in every Bessel-potential space `H^s`, and so it is a
  smooth function (`Distribution.exists_contDiff_cutoffTempered_eq_integral`), by the Sobolev
  embedding `TemperedDistribution.exists_contDiff_eq_integral_of_forall_memSobolev`.
* **Localization.** Where `φ = 1`, the distribution `T` agrees with `φ T`.

The neighbourhood in this characterization cannot be dropped: `T` may be `H^s` near `x` for every
`s` while singularities of ever higher regularity accumulate at `x`. Accordingly the singular
support is the closure in `Ω` of the union of the `H^s` singular supports, rather than the union
itself (`Distribution.singularSupport_eq_inter_closure_iUnion_sobolevSingularSupport`). In
particular `T` is smooth on all of `Ω` exactly when every `H^s` singular support is empty
(`Distribution.singularSupport_eq_empty_iff_forall_sobolevSingularSupport_eq_empty`).

## Main results

* `Distribution.exists_contDiff_cutoffTempered_eq_integral`: if `T` is `H^s` near every point of
  the support of `φ` for every `s`, then `φ T` is a smooth function.
* `Distribution.notMem_singularSupport_iff_eventually_forall_isLocallySobolevAt`: `T` is smooth
  near `x` exactly when it is `H^s` near every point close to `x`, for every `s`.
* `Distribution.singularSupport_eq_inter_closure_iUnion_sobolevSingularSupport`: the singular
  support is the closure in `Ω` of the union of the `H^s` singular supports.
* `Distribution.singularSupport_eq_empty_iff_forall_sobolevSingularSupport_eq_empty`: `T` is
  smooth on `Ω` exactly when it is `H^s` near every point of `Ω` for every `s`.

## References

* L. Hörmander, *Lectures on Nonlinear Hyperbolic Differential Equations*, Springer, 1997,
  §11.1 (the `H^s` wave front set).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, 2008, Lecture I, (4.6)–(4.11)
  (elliptic regularity, from `H^s_loc` to `C^∞`).
-/

public section

noncomputable section

open Complex Filter Set TopologicalSpace TestFunction MeasureTheory TemperedDistribution
open scoped Distributions Topology ContDiff SchwartzMap

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E} {T : 𝓓'(Ω, ℂ)}

/-- **Cut-off distributions of every Sobolev order are smooth.** If `T` is `H^s` near every point
of the support of a test function `φ`, for every real `s`, then the tempered distribution `φ T`
is a smooth function `g`: it pairs with every Schwartz function `ψ` as `∫ ψ • g`. -/
theorem exists_contDiff_cutoffTempered_eq_integral {φ : 𝓓(Ω, ℂ)}
    (h : ∀ s, ∀ x ∈ tsupport φ, T.IsLocallySobolevAt s x) :
    ∃ g : E → ℂ, ContDiff ℝ ∞ g ∧ ∀ ψ : 𝓢(E, ℂ), T.cutoffTempered φ ψ = ∫ x, ψ x • g x := by
  refine exists_contDiff_eq_integral_of_forall_memSobolev fun s ↦ ?_
  -- Each point of `tsupport φ` has a neighbourhood on which every cutoff gives an `H^s` product.
  choose U hU hUs using fun x : tsupport φ ↦
    (h s x x.property).exists_nhds_forall_memSobolev_cutoffTempered
  -- Split `φ` into finitely many test functions supported in these neighbourhoods.
  obtain ⟨t, ψ, hψU, hψφ, -⟩ := φ.exists_sum_subordinate (fun x ↦ interior (U x))
    (fun _ ↦ isOpen_interior) fun x hx ↦
      mem_iUnion.2 ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.2 (hU ⟨x, hx⟩)⟩
  rw [← hψφ, cutoffTempered_sum_cutoff]
  exact MemSobolev.sum fun i _ ↦ hUs i _ ((hψU i).trans interior_subset)

/-- **Smoothness from every Sobolev order.** A complex distribution is a smooth function near a
point `x ∈ Ω` exactly when, for every real `s`, it is `H^s` near every point of a neighbourhood
of `x` independent of `s`. -/
theorem notMem_singularSupport_iff_eventually_forall_isLocallySobolevAt {x : E} (hx : x ∈ Ω) :
    x ∉ T.singularSupport ↔ ∀ᶠ y in 𝓝 x, ∀ s, T.IsLocallySobolevAt s y := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · filter_upwards [T.isOpen_diff_singularSupport.mem_nhds ⟨hx, h⟩] with y hy s
    exact (notMem_sobolevSingularSupport_iff hy.1).1 fun hs ↦
      hy.2 (sobolevSingularSupport_subset_singularSupport s T hs)
  -- A cutoff equal to one near `x` and supported where `T` has every Sobolev order.
  obtain ⟨χc, V, hV, hxV, hV1, hχcs⟩ := exists_eqOn_one_tsupport_subset (n := ⊤) (𝕜 := ℂ) h hx
  obtain ⟨g, hg, hTg⟩ := exists_contDiff_cutoffTempered_eq_integral fun s y hy ↦ hχcs hy s
  -- On `V` the cutoff is one, so `T` is the function representing `χ T`.
  exact (notMem_singularSupport_iff hx).2 ⟨V, hV, hxV, g, hg.contDiffOn, fun φ hφ ↦
    T.apply_eq_integral_of_cutoffTempered_apply_eq_integral hTg (fun y hy ↦ hV1 hy) hφ⟩

/-- **The singular support is the closure of the `H^s` singular supports.** The singular support
of a complex distribution is the closure in `Ω` of the union over all real `s` of its `H^s`
singular supports. -/
theorem singularSupport_eq_inter_closure_iUnion_sobolevSingularSupport (T : 𝓓'(Ω, ℂ)) :
    T.singularSupport = (Ω : Set E) ∩ closure (⋃ s, T.sobolevSingularSupport s) := by
  ext x
  refine ⟨fun hx ↦ ?_, fun ⟨hxΩ, hx⟩ ↦ by_contra fun h ↦ ?_⟩
  · have hxΩ := T.singularSupport_subset hx
    have hfreq : ∃ᶠ y in 𝓝 x, ¬ ∀ s, T.IsLocallySobolevAt s y := by
      rw [← not_eventually]
      exact mt (notMem_singularSupport_iff_eventually_forall_isLocallySobolevAt hxΩ).2
        (not_not.2 hx)
    refine ⟨hxΩ, mem_closure_iff_frequently.2 ?_⟩
    refine (hfreq.and_eventually (Ω.isOpen.mem_nhds hxΩ)).mono fun y ⟨hy, hyΩ⟩ ↦ ?_
    obtain ⟨s, hs⟩ := not_forall.1 hy
    exact mem_iUnion.2 ⟨s, mem_sobolevSingularSupport_iff.2 ⟨hyΩ, hs⟩⟩
  · obtain ⟨y, ⟨-, hy⟩, hy'⟩ :=
      mem_closure_iff_nhds.1 hx _ (T.isOpen_diff_singularSupport.mem_nhds ⟨hxΩ, h⟩)
    obtain ⟨s, hs⟩ := mem_iUnion.1 hy'
    exact hy (sobolevSingularSupport_subset_singularSupport s T hs)

/-- A complex distribution is smooth near every point of `Ω` exactly when it is `H^s` near every
point of `Ω`, for every real `s`. -/
theorem singularSupport_eq_empty_iff_forall_sobolevSingularSupport_eq_empty :
    T.singularSupport = ∅ ↔ ∀ s, T.sobolevSingularSupport s = ∅ := by
  refine ⟨fun h s ↦ subset_empty_iff.1 (h ▸ sobolevSingularSupport_subset_singularSupport s T),
    fun h ↦ ?_⟩
  simp [singularSupport_eq_inter_closure_iUnion_sobolevSingularSupport, h]

end Distribution
