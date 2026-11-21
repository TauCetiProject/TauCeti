/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Tempered
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding

/-!
# Smoothness from local Sobolev regularity of every order

Let `T` be a complex distribution on an open subset `Ω` of a finite-dimensional real inner product
space `E`. This file proves that `T` is a smooth function near a point `x ∈ Ω` exactly when it is
`H^s` near every point of some neighbourhood of `x`, for every real order `s`
(`Distribution.notMem_singularSupport_iff_eventually_forall_isLocallySobolevAt`). Equivalently,
the singular support of `T` is the closure in `Ω` of the union of its `H^s` singular supports
(`Distribution.singularSupport_eq_inter_closure_iUnion_sobolevSingularSupport`), and an open set
avoids the singular support exactly when it avoids every `H^s` singular support
(`Distribution.disjoint_singularSupport_iff_forall_disjoint_sobolevSingularSupport`).

This is the step from the Sobolev scale to smoothness in distributional elliptic regularity: an
elliptic estimate `P T ∈ H^(s - m)_loc ⇒ T ∈ H^s_loc`, applied at every order `s` on an open set
where `P T` is smooth, shows that `T` is smooth there.

The neighbourhood in the statement cannot be dropped. A distribution can be `H^s` near `x` for
every `s` without being smooth near `x`, when the regularity of its singularities improves as they
accumulate at `x`: the neighbourhood on which `T` is `H^s` may shrink as `s` grows. Accordingly the
singular support is the closure of the union of the `H^s` singular supports, not the union itself.

## Proof

If `T` is `H^s` near every point of the support of a cutoff `φ`, then `φ T ∈ H^s`
(`Distribution.memSobolev_cutoffTempered_of_forall_isLocallySobolevAt`): split `φ` by a finite
partition of unity into pieces supported in neighbourhoods on which every cutoff gives `H^s`
(`Distribution.IsLocallySobolevAt.exists_nhds`). Take `φ` equal to one near `x` and supported in
the neighbourhood of the hypothesis. Then `φ T` lies in every Bessel-potential space `H^s`, so it
is a smooth function (`TemperedDistribution.exists_contDiff_eq_integral_of_forall_memSobolev`), and
`T` agrees with it where `φ = 1`.

## Main results

* `Distribution.notMem_singularSupport_iff_eventually_forall_isLocallySobolevAt`: `T` is smooth
  near `x` exactly when it is `H^s` near every point close to `x`, for every `s`.
* `Distribution.singularSupport_eq_inter_closure_iUnion_sobolevSingularSupport`: the singular
  support is the closure in `Ω` of the union of the `H^s` singular supports.
* `Distribution.disjoint_singularSupport_iff_forall_disjoint_sobolevSingularSupport`,
  `Distribution.singularSupport_eq_empty_iff_forall_sobolevSingularSupport_eq_empty`: `T` is
  smooth on an open set, or on all of `Ω`, exactly when it is `H^s` there for every `s`.

## References

* L. Hörmander, *Lectures on Nonlinear Hyperbolic Differential Equations*, Springer, 1997,
  §11.1 (the `H^s` wave front set and its relation to the wave front set).
* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, 2008, Lecture I,
  (4.6)–(4.11) (elliptic regularity, from all Sobolev orders to smoothness).
-/

public section

noncomputable section

open Complex Filter Set TopologicalSpace TestFunction MeasureTheory TemperedDistribution
open scoped Distributions Topology SchwartzMap ContDiff

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E}

/-- **Smoothness from Sobolev regularity of every order.** A complex distribution is a smooth
function near a point `x ∈ Ω` exactly when, for every real `s`, it is `H^s` near every point of
some neighbourhood of `x` independent of `s`. -/
theorem notMem_singularSupport_iff_eventually_forall_isLocallySobolevAt {T : 𝓓'(Ω, ℂ)} {x : E}
    (hx : x ∈ Ω) :
    x ∉ T.singularSupport ↔ ∀ᶠ y in 𝓝 x, ∀ s, T.IsLocallySobolevAt s y := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · filter_upwards [T.isOpen_diff_singularSupport.mem_nhds ⟨hx, h⟩] with y ⟨hyΩ, hy⟩ s
    exact (notMem_sobolevSingularSupport_iff hyΩ).1 fun hs ↦
      hy (sobolevSingularSupport_subset_singularSupport s T hs)
  obtain ⟨U, hU, hUo, hxU⟩ := _root_.eventually_nhds_iff.1 h
  -- A cutoff equal to one near `x` and supported in `U ∩ Ω`.
  obtain ⟨χ, -, hχ1, hχs⟩ := exists_cutoff_tsupport_subset (n := ⊤) (isCompact_singleton (x := x))
    (hUo.inter Ω.isOpen) (singleton_subset_iff.2 ⟨hxU, hx⟩) inter_subset_right
  rw [nhdsSet_singleton] at hχ1
  obtain ⟨V, hV1, hV, hxV⟩ := _root_.eventually_nhds_iff.1 hχ1
  let χc : 𝓓(Ω, ℂ) := postcompCLM (𝕜 := ℝ) ofRealCLM χ
  have hχc (y : E) : χc y = χ y := by simp [χc]
  have hχcs : tsupport χc ⊆ U :=
    (tsupport_comp_subset (g := ofRealCLM) (by simp) χ).trans (hχs.trans inter_subset_left)
  -- The tempered distribution `χ T` lies in every `H^s`, so it is a smooth function `f`.
  obtain ⟨f, hf, hTf⟩ := exists_contDiff_eq_integral_of_forall_memSobolev fun s ↦
    memSobolev_cutoffTempered_of_forall_isLocallySobolevAt (T := T) (φ := χc) fun y hy ↦
      hU y (hχcs hy) s
  -- Where `χ = 1`, `T` agrees with `χ T`.
  refine (notMem_singularSupport_iff hx).2 ⟨V, hV, hxV, f, hf.contDiffOn, fun φ hφ ↦ ?_⟩
  have hφc : HasCompactSupport fun y ↦ (φ y : ℂ) := φ.hasCompactSupport.comp_left ofReal_zero
  let ψ : 𝓢(E, ℂ) := hφc.toSchwartzMap (ofRealCLM.contDiff.comp φ.contDiff)
  -- Mathlib has no evaluation lemma for `HasCompactSupport.toSchwartzMap`; by definition it
  -- evaluates to the underlying function.
  have hψ (y : E) : ψ y = φ y := (rfl)
  have hTψ : T.cutoffTempered χc ψ = T φ := by
    rw [cutoffTempered_apply T χc (χ := postcompCLM (𝕜 := ℝ) ofRealCLM φ) fun y ↦ ?_,
      complexPairing_postcompCLM_ofRealCLM]
    by_cases hy : φ y = 0
    · simp [hψ, hy]
    · simp [hψ, hχc, hV1 y (hφ (subset_tsupport _ hy))]
  rw [← hTψ, hTf ψ]
  simp [hψ, Complex.real_smul]

/-- **The singular support is the closure of the `H^s` singular supports.** The singular support of
a complex distribution is the closure in `Ω` of the union over all real `s` of its `H^s` singular
supports. -/
theorem singularSupport_eq_inter_closure_iUnion_sobolevSingularSupport (T : 𝓓'(Ω, ℂ)) :
    T.singularSupport = (Ω : Set E) ∩ closure (⋃ s, T.sobolevSingularSupport s) := by
  ext x
  by_cases hx : x ∈ Ω
  · rw [← not_iff_not, notMem_singularSupport_iff_eventually_forall_isLocallySobolevAt hx,
      mem_inter_iff, mem_closure_iff_frequently, not_and, not_frequently]
    simp only [SetLike.mem_coe, hx, forall_const, mem_iUnion, not_exists,
      mem_sobolevSingularSupport_iff, not_and, not_not]
    refine ⟨fun h ↦ h.mono fun y hy s _ ↦ hy s, fun h ↦ ?_⟩
    filter_upwards [h, Ω.isOpen.mem_nhds hx] with y hy hyΩ s using hy s hyΩ
  · exact iff_of_false (fun h ↦ hx (T.singularSupport_subset h)) fun h ↦ hx h.1

/-- **Smoothness on an open set from Sobolev regularity of every order.** An open set `U` avoids the
singular support of a complex distribution exactly when it avoids its `H^s` singular support for
every real `s`. -/
theorem disjoint_singularSupport_iff_forall_disjoint_sobolevSingularSupport {T : 𝓓'(Ω, ℂ)}
    {U : Set E} (hU : IsOpen U) :
    Disjoint U T.singularSupport ↔ ∀ s, Disjoint U (T.sobolevSingularSupport s) := by
  refine ⟨fun h s ↦ h.mono_right (sobolevSingularSupport_subset_singularSupport s T), fun h ↦ ?_⟩
  refine disjoint_left.2 fun x hxU hx ↦
    (notMem_singularSupport_iff_eventually_forall_isLocallySobolevAt
      (T.singularSupport_subset hx)).2 ?_ hx
  filter_upwards [hU.mem_nhds hxU, Ω.isOpen.mem_nhds (T.singularSupport_subset hx)]
    with y hyU hyΩ s
  exact (notMem_sobolevSingularSupport_iff hyΩ).1 (disjoint_left.1 (h s) hyU)

/-- A complex distribution is a smooth function on all of `Ω` exactly when it is `H^s` near every
point of `Ω` for every real `s`. -/
theorem singularSupport_eq_empty_iff_forall_sobolevSingularSupport_eq_empty {T : 𝓓'(Ω, ℂ)} :
    T.singularSupport = ∅ ↔ ∀ s, T.sobolevSingularSupport s = ∅ := by
  simpa only [univ_disjoint] using
    disjoint_singularSupport_iff_forall_disjoint_sobolevSingularSupport (T := T) isOpen_univ

end Distribution
