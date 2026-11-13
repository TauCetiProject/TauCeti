/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Support
public import Mathlib.Geometry.Manifold.BumpFunction
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.OpenPos

import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The fundamental lemma for bundle-valued variations

A continuous field of continuous linear maps into a real Banach space on a `C^n`
real vector bundle, `n ≤ ∞`, over a finite-dimensional Hausdorff smooth manifold is
determined on an open set by its integrals against `C^n` sections compactly
supported in that set. The measure must make open sets measurable, be finite on
compact sets, and charge every nonempty open set. No σ-compactness assumption is
needed. In particular, after choosing a positive smooth density, this applies to
real-valued covector fields representing density-valued sources. No metric or
trivialization of the vector bundle is chosen.

Continuity of the field is expressed as continuity of its fibrewise evaluation
on the total space, over the specified open set. The fibre may be infinite-dimensional.
The statements concern continuous sources along fields, not functions on jet spaces:
turning uniqueness along every field into a jet identity additionally needs local
realization of jets.

The proof uses Mathlib's
`Continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero` and smooth bump
functions, together with `ContMDiffSection.evalLinearMap_surjective` to test every
fibre vector and the separating dual to detect Banach-valued pairings. Compact
support is the native `ContMDiffSection.tsupport`, not the support of the map into
the total space.

## References

* Ian M. Anderson, *The Variational Bicomplex*, Chapter 2, §B, for uniqueness of
  Euler source coefficients from arbitrary supported variations.
-/

public section

open Bundle Filter MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace ContMDiffSection

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] {n : ℕ∞ω}
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- A field of continuous linear maps evaluates integrably on every `C^n` section compactly
supported inside an open continuity domain, for any measure finite on compact sets
that makes open sets measurable. -/
theorem integrable_clm_apply_of_tsupport_subset [MeasurableSpace M] [OpensMeasurableSpace M]
    {μ : Measure M} [IsFiniteMeasureOnCompacts μ] (s : Cₛ^n⟮I; F, V⟯)
    {η : ∀ x, V x →L[𝕜] G} {U : Set M} (hU : IsOpen U)
    (hη : ContinuousOn (fun p : TotalSpace F V ↦ η p.proj p.snd) ((π F V) ⁻¹' U))
    (hsc : IsCompact s.tsupport) (hsU : s.tsupport ⊆ U) :
    Integrable (fun x ↦ η x (s x)) μ := by
  apply (s.continuous_clm_apply_of_tsupport_subset hU hη hsU).integrable_of_hasCompactSupport
  exact hsc.of_isClosed_subset (_root_.isClosed_tsupport _) (s.tsupport_clm_apply_subset η)

end ContMDiffSection

namespace IsOpen

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M] [MeasurableSpace M] [OpensMeasurableSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞ω} [ENat.LEInfty n] [ContMDiffVectorBundle n F V I]
  {μ : Measure M} [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- **The bundle fundamental lemma.** A continuous field of continuous linear maps
into a real Banach space whose integral pairing with every `C^n` compactly supported
variation in an open set is zero vanishes pointwise there. Full support of the measure
is essential to the pointwise conclusion. The bundle and its fibres need not be
trivial or nonzero. -/
theorem eq_zero_of_integral_clm_apply_contMDiffSection_eq_zero {η : ∀ x, V x →L[ℝ] G}
    {U : Set M} (hU : IsOpen U)
    (hη : ContinuousOn (fun p : TotalSpace F V ↦ η p.proj p.snd) ((π F V) ⁻¹' U))
    (h : ∀ s : Cₛ^n⟮I; F, V⟯, IsCompact s.tsupport → s.tsupport ⊆ U →
      ∫ x, η x (s x) ∂μ = 0) : ∀ x ∈ U, η x = 0 := by
  have hs (ℓ : G →L[ℝ] ℝ) (s : Cₛ^n⟮I; F, V⟯) {x : M} (hx : x ∈ U) :
      ℓ (η x (s x)) ≤ 0 := by
    by_contra! hpos
    have hηℓ := ℓ.continuous.comp_continuousOn hη
    have hc := s.continuousOn_clm_apply (η := fun y ↦ ℓ.comp (η y)) hηℓ
    obtain ⟨ρ, -, hρ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
      (inter_mem (hU.mem_nhds hx)
        ((hc.continuousAt (hU.mem_nhds hx)).preimage_mem_nhds (Ioi_mem_nhds hpos)))
    let g : C^n⟮I, M; ℝ⟯ := ⟨ρ, ρ.contMDiff.of_le ENat.LEInfty.out⟩
    have ht := ContMDiffSection.tsupport_smul_function_subset g s
    have hsc := ContMDiffSection.mem_compactlySupported.mp
      (ContMDiffSection.smul_function_mem_compactlySupported_of_hasCompactSupport
        g ρ.hasCompactSupport s)
    have hsU : (g • s).tsupport ⊆ U := ht.trans (inter_subset_left.trans
      (hρ.trans inter_subset_left))
    have hgs (y : M) : (g • s) y = ρ y • s y := ContMDiffSection.smul_apply g s y
    have hcont := (g • s).continuous_clm_apply_of_tsupport_subset
      (η := fun y ↦ ℓ.comp (η y)) hU hηℓ hsU
    have hp := hcont.integral_pos_of_hasCompactSupport_nonneg_ne_zero (μ := μ)
        (hsc.of_isClosed_subset (_root_.isClosed_tsupport _)
          ((g • s).tsupport_clm_apply_subset (fun y ↦ ℓ.comp (η y))))
        (fun y ↦ ?_) (x := x) (by
          simpa only [ContinuousLinearMap.comp_apply, hgs, ρ.eq_one, one_smul] using hpos.ne')
    · simp only [ContinuousLinearMap.comp_apply] at hp
      rw [ℓ.integral_comp_comm
        ((g • s).integrable_clm_apply_of_tsupport_subset hU hη hsc hsU),
        h (g • s) hsc hsU, map_zero] at hp
      exact hp.false
    · by_cases hy : y ∈ tsupport ρ
      · simpa only [Pi.zero_apply, ContinuousLinearMap.comp_apply, hgs, map_smul,
          smul_eq_mul] using
          mul_nonneg (ρ.nonneg (x := y)) (hρ hy).2.le
      · simp only [Pi.zero_apply, hgs, image_eq_zero_of_notMem_tsupport hy,
          zero_smul, map_zero, le_refl]
  intro x hx
  ext v
  obtain ⟨s, rfl⟩ := ContMDiffSection.evalLinearMap_surjective (I := I) (F := F) (V := V) n x v
  simp only [ContMDiffSection.evalLinearMap_apply, zero_apply]
  apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ)
  intro ℓ
  apply le_antisymm (hs ℓ s hx)
  simpa using hs ℓ (-s) hx

/-- Two continuous fields of continuous linear maps into a real Banach space with equal
integral pairings against all `C^n` variations compactly supported in an open set coincide there.
Integrability of the two pairings follows from continuity and compact support, rather than being an
extra premise about formal integral values. -/
theorem eq_of_integral_clm_apply_contMDiffSection_eq {η ζ : ∀ x, V x →L[ℝ] G}
    {U : Set M} (hU : IsOpen U)
    (hη : ContinuousOn (fun p : TotalSpace F V ↦ η p.proj p.snd) ((π F V) ⁻¹' U))
    (hζ : ContinuousOn (fun p : TotalSpace F V ↦ ζ p.proj p.snd) ((π F V) ⁻¹' U))
    (h : ∀ s : Cₛ^n⟮I; F, V⟯, IsCompact s.tsupport → s.tsupport ⊆ U →
      ∫ x, η x (s x) ∂μ = ∫ x, ζ x (s x) ∂μ) : ∀ x ∈ U, η x = ζ x := by
  have hz := hU.eq_zero_of_integral_clm_apply_contMDiffSection_eq_zero (I := I) (n := n) (μ := μ)
    (η := fun x ↦ η x - ζ x) (hη.sub hζ) (fun s hsc hsU ↦ ?_)
  · intro x hx
    exact sub_eq_zero.mp (hz x hx)
  · simp only [sub_apply]
    rw [integral_sub (s.integrable_clm_apply_of_tsupport_subset hU hη hsc hsU)
      (s.integrable_clm_apply_of_tsupport_subset hU hζ hsc hsU), h s hsc hsU, sub_self]

end IsOpen
