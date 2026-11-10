/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Support
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# The fundamental lemma for bundle-valued variations

A continuous field of real covectors on a smooth vector bundle is determined on an
open set by its integrals against smooth sections compactly supported in that set.
The measure must be locally finite and charge every nonempty open set. In particular,
this applies after choosing a positive smooth density to represent a density-valued
source by an ordinary covector field. No metric or trivialization of the vector
bundle is chosen.

Continuity of a covector field is expressed as continuity of its fibrewise evaluation
on the total space, over the specified open set. The fibre may be infinite-dimensional.
The statements concern continuous sources along fields, not functions on jet spaces:
turning uniqueness along every field into a jet identity additionally needs local
realization of jets.

The proof uses Mathlib's scalar distribution theorem
`IsOpen.ae_eq_zero_of_integral_contMDiff_smul_eq_zero`, the full-support upgrade
`Measure.eqOn_open_of_ae_eq`, and `FiberBundle.exists_contMDiff_section_eq` to test
every fibre vector. Compact support is the native `ContMDiffSection.tsupport`, not
the support of the map into the total space.

## References

* Ian M. Anderson, *The Variational Bicomplex*, Chapter 2, §B, for uniqueness of
  Euler source coefficients from arbitrary supported variations.
-/

public section

open Bundle MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace ContMDiffSection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] {n : ℕ∞ω}

/-- Pairing a continuous covector field with a smooth section supported in its
continuity domain gives a continuous scalar function on the whole base. -/
theorem continuous_covector_apply (s : Cₛ^n⟮I; F, V⟯)
    {η : ∀ x, V x →L[ℝ] ℝ} {U : Set M} (hU : IsOpen U)
    (hη : ContinuousOn (fun p : TotalSpace F V ↦ η p.proj p.snd) ((π F V) ⁻¹' U))
    (hsU : s.tsupport ⊆ U) : Continuous (fun x ↦ η x (s x)) := by
  have hc : ContinuousOn (fun x ↦ η x (s x)) U :=
    hη.comp s.contMDiff.continuous.continuousOn (fun _ hx ↦ hx)
  have ht : _root_.tsupport (fun x ↦ η x (s x)) ⊆ s.tsupport := by
    apply closure_minimal _ s.isClosed_tsupport
    intro x hx
    by_contra hxs
    exact hx (by simp [s.eq_zero_of_notMem_tsupport hxs])
  exact continuous_of_tsupport fun x hx ↦ hc.continuousAt (hU.mem_nhds (hsU (ht hx)))

/-- A continuous covector field pairs integrably with every smooth section compactly
supported inside its continuity domain, for any locally finite Borel measure. -/
theorem integrable_covector_apply [R1Space M] [MeasurableSpace M] [BorelSpace M]
    {μ : Measure M} [IsLocallyFiniteMeasure μ] (s : Cₛ^n⟮I; F, V⟯)
    {η : ∀ x, V x →L[ℝ] ℝ} {U : Set M} (hU : IsOpen U)
    (hη : ContinuousOn (fun p : TotalSpace F V ↦ η p.proj p.snd) ((π F V) ⁻¹' U))
    (hsc : IsCompact s.tsupport) (hsU : s.tsupport ⊆ U) :
    Integrable (fun x ↦ η x (s x)) μ := by
  apply (s.continuous_covector_apply hU hη hsU).integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact hsc
  intro x hx
  by_contra hxs
  exact hx (by simp [s.eq_zero_of_notMem_tsupport hxs])

end ContMDiffSection

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  {μ : Measure M} [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure]

/-- **The bundle fundamental lemma.** A continuous covector field whose integral
pairing with every smooth compactly supported variation in an open set is zero
vanishes pointwise there. Full support of the measure is essential to the
pointwise conclusion. The bundle and its fibres need not be trivial or nonzero. -/
theorem covector_eq_zero_of_integral_section_eq_zero {η : ∀ x, V x →L[ℝ] ℝ}
    {U : Set M} (hU : IsOpen U)
    (hη : ContinuousOn (fun p : TotalSpace F V ↦ η p.proj p.snd) ((π F V) ⁻¹' U))
    (h : ∀ s : Cₛ^∞⟮I; F, V⟯, IsCompact s.tsupport → s.tsupport ⊆ U →
      ∫ x, η x (s x) ∂μ = 0) : ∀ x ∈ U, η x = 0 := by
  have hs (s : Cₛ^∞⟮I; F, V⟯) : EqOn (fun x ↦ η x (s x)) 0 U := by
    have hc : ContinuousOn (fun x ↦ η x (s x)) U :=
      hη.comp s.contMDiff.continuous.continuousOn (fun _ hx ↦ hx)
    have hae := hU.ae_eq_zero_of_integral_contMDiff_smul_eq_zero I
      (hc.locallyIntegrableOn (μ := μ) hU.measurableSet) (fun g hg hgc hgU ↦ ?_)
    · exact Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' hU.measurableSet).2 hae)
        hU hc continuousOn_const
    · let g' : C^∞⟮I, M; ℝ⟯ := ⟨g, hg⟩
      have ht := ContMDiffSection.tsupport_smul_function_subset g' s
      have hg' : ⇑g' = g := ContMDiffMap.coeFn_mk g hg
      simpa only [ContMDiffSection.smul_apply, map_smul, smul_eq_mul, hg'] using
        h (g' • s)
          (ContMDiffSection.mem_compactlySupported.mp
            (ContMDiffSection.smul_function_mem_compactlySupported_of_hasCompactSupport g' hgc s))
          (ht.trans (inter_subset_left.trans hgU))
  intro x hx
  ext v
  obtain ⟨s, hsmooth, hsv⟩ := FiberBundle.exists_contMDiff_section_eq I F ∞ v
  simpa only [ContMDiffSection.coeFn_mk, hsv, Pi.zero_apply, zero_apply] using
    hs ⟨s, hsmooth⟩ hx

/-- Two continuous covector fields with equal integral pairings against all smooth
variations compactly supported in an open set coincide there. Integrability of the
two pairings follows from continuity and compact support, rather than being an
extra premise about formal integral values. -/
theorem covector_eq_of_integral_section_eq {η ζ : ∀ x, V x →L[ℝ] ℝ}
    {U : Set M} (hU : IsOpen U)
    (hη : ContinuousOn (fun p : TotalSpace F V ↦ η p.proj p.snd) ((π F V) ⁻¹' U))
    (hζ : ContinuousOn (fun p : TotalSpace F V ↦ ζ p.proj p.snd) ((π F V) ⁻¹' U))
    (h : ∀ s : Cₛ^∞⟮I; F, V⟯, IsCompact s.tsupport → s.tsupport ⊆ U →
      ∫ x, η x (s x) ∂μ = ∫ x, ζ x (s x) ∂μ) : ∀ x ∈ U, η x = ζ x := by
  have hz := covector_eq_zero_of_integral_section_eq_zero (I := I) (μ := μ)
    (η := fun x ↦ η x - ζ x) hU (hη.sub hζ) (fun s hsc hsU ↦ ?_)
  · intro x hx
    exact sub_eq_zero.mp (hz x hx)
  · simp only [sub_apply]
    rw [integral_sub (s.integrable_covector_apply hU hη hsc hsU)
      (s.integrable_covector_apply hU hζ hsc hsU), h s hsc hsU, sub_self]

end TauCeti
