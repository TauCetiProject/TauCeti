/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.Geometry.Manifold.ContMDiff.Subtype
public import TauCeti.Geometry.Manifold.MFDeriv.Opens
public import TauCeti.Geometry.Manifold.RegularValue.Immersion
public import TauCeti.Geometry.Manifold.RegularValue.Open

/-!
# Local defining functions and genuine regular boundary arcs

A genuine smooth regular curve lying in the zero set of a scalar function regular at one actual
curve point parametrizes every nearby zero. Smoothness is needed only on an actual open target
neighborhood. The construction internally chooses a smaller regular target and an actual open
source interval, and uses the native regular-level manifold. No extra zero-set parametrization
or global defining function is supplied by the caller.
-/

public noncomputable section

open Bundle Filter Function Manifold Set TopologicalSpace Topology TauCeti.Manifold
open scoped ContDiff Manifold Topology
namespace TauCeti
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
/-- A smooth actual regular curve fills a scalar zero level near its image when the
actual defining function is smooth and regular on an open target neighborhood. -/
theorem exists_isOpen_zero_locus_subset_curve_image_of_open
    {ρ : M → ℝ} (U : Opens M) (hρ : ContMDiffOn I 𝓘(ℝ) ∞ ρ U)
    (hreg : ∀ p ∈ U, IsRegularPoint I 𝓘(ℝ) ρ p) (hdim : Module.finrank ℝ E = 2)
    (δ : ℝ → M) (S : Opens ℝ) (hδ : ContMDiffOn 𝓘(ℝ) I ∞ δ S)
    (hδU : MapsTo δ (S : Set ℝ) U) (hzero : ∀ s ∈ S, ρ (δ s) = 0)
    (hne : ∀ s ∈ S, Manifold.curveVelocity I δ s ≠ 0)
    {s₀ : ℝ} (hs₀ : s₀ ∈ S) :
    ∃ W : Set M, IsOpen W ∧ δ s₀ ∈ W ∧ W ⊆ U ∧
      ∀ p ∈ W, ρ p = 0 → ∃ s ∈ S, δ s = p := by
  let fρ : U → ℝ := ρ ∘ Subtype.val
  have hfρ : ContMDiff I 𝓘(ℝ) ∞ fρ :=
    hρ.comp_contMDiff contMDiff_subtype_val (fun p ↦ p.property)
  have hregU : IsRegularValue I 𝓘(ℝ) fρ 0 := by
    rw [isRegularValue_iff]
    intro p _
    rw [isRegularPoint_iff]
    change Surjective (mfderiv I 𝓘(ℝ) (ρ ∘ (Subtype.val : U → M)) p)
    rw [mfderiv_comp p
      ((hρ.contMDiffAt (U.isOpen.mem_nhds p.property)).mdifferentiableAt (by simp))
      (contMDiff_subtype_val.mdifferentiableAt (n := 1) one_ne_zero), Manifold.mfderiv_subtype_val]
    exact (isRegularPoint_iff.mp (hreg p p.property)).comp
      (tangentSpaceOpenEquiv (I := I) p).surjective
  let f : S → U := fun q ↦ ⟨δ q.val, hδU q.property⟩
  have hδS : ContMDiff 𝓘(ℝ) I ∞ (fun q : S ↦ δ q.val) :=
    hδ.comp_contMDiff contMDiff_subtype_val (fun q ↦ q.property)
  have hf : ContMDiff 𝓘(ℝ) I ∞ f :=
    (TauCeti.ContMDiff.subtypeVal_comp_iff U f).mp hδS
  let q₀ : S := ⟨s₀, hs₀⟩
  have hδmd : MDifferentiableAt 𝓘(ℝ) I δ s₀ :=
    (hδ.contMDiffAt (S.isOpen.mem_nhds hs₀)).mdifferentiableAt (by simp)
  have hδinj : Injective (mfderiv 𝓘(ℝ) I (δ ∘ (Subtype.val : S → ℝ)) q₀) := by
    intro v w hvw
    rw [Manifold.mfderiv_comp_subtype_val_apply, Manifold.mfderiv_comp_subtype_val_apply,
      (Manifold.hasMFDerivAt_curveVelocity hδmd).mfderiv] at hvw
    exact smul_left_injective ℝ (hne s₀ hs₀) hvw
  have hfinj : Injective (mfderiv 𝓘(ℝ) I f q₀) := by
    intro v w hvw
    apply hδinj
    change mfderiv 𝓘(ℝ) I ((Subtype.val : U → M) ∘ f) q₀ v =
      mfderiv 𝓘(ℝ) I ((Subtype.val : U → M) ∘ f) q₀ w
    rw [mfderiv_comp q₀ (contMDiff_subtype_val.mdifferentiableAt (n := 1) one_ne_zero)
      (hf.mdifferentiableAt (by simp))]
    exact congrArg (mfderiv I I (Subtype.val : U → M) (f q₀)) hvw
  have hparam := hregU.eventually_mem_range
    (fun p _ ↦ (hfρ p).of_le (by simp))
    (by simp [hdim] : Module.finrank ℝ ℝ + Module.finrank ℝ ℝ = Module.finrank ℝ E)
    (hf.of_le (by simp)) (fun q ↦ hzero q.val q.property) hfinj
    BoundarylessManifold.isInteriorPoint
  obtain ⟨V, hVsub, hVopen, hVmem⟩ := mem_nhds_iff.mp hparam
  refine ⟨Subtype.val '' V, U.isOpen.isOpenMap_subtype_val _ hVopen,
    ⟨f q₀, hVmem, rfl⟩, ?_, ?_⟩
  · rintro p ⟨q, _, rfl⟩
    exact q.property
  · rintro p ⟨q, hq, rfl⟩ hz
    obtain ⟨s, hs⟩ := hVsub hq hz
    exact ⟨s.val, s.property, congrArg Subtype.val hs⟩
/-- A scalar defining function regular at one actual point of a smooth regular curve
has no additional zero branch nearby. The actual source and target neighborhoods are
chosen internally, preserving the requested parameter interval. -/
theorem exists_isOpen_zero_locus_subset_curve_image_of_regularPoint
    {ρ : M → ℝ} (U : Opens M) (hρ : ContMDiffOn I 𝓘(ℝ) ∞ ρ U)
    (hdim : Module.finrank ℝ E = 2)
    (δ : ℝ → M) (S : Opens ℝ) (hδ : ContMDiffOn 𝓘(ℝ) I ∞ δ S)
    (hzero : ∀ s ∈ S, ρ (δ s) = 0)
    (hne : ∀ s ∈ S, Manifold.curveVelocity I δ s ≠ 0)
    {s₀ : ℝ} (hs₀ : s₀ ∈ S) (hδU : δ s₀ ∈ U)
    (hreg : IsRegularPoint I 𝓘(ℝ) ρ (δ s₀)) :
    ∃ W : Set M, IsOpen W ∧ δ s₀ ∈ W ∧ W ⊆ U ∧
      ∀ p ∈ W, ρ p = 0 → ∃ s ∈ S, δ s = p := by
  have hregular : ∀ᶠ p in 𝓝 (δ s₀), IsRegularPoint I 𝓘(ℝ) ρ p :=
    hreg.eventually_isRegularPoint (hρ.contMDiffAt (U.isOpen.mem_nhds hδU)) (by simp)
  have hnear : (U : Set M) ∩ {p | IsRegularPoint I 𝓘(ℝ) ρ p} ∈ 𝓝 (δ s₀) :=
    inter_mem (U.isOpen.mem_nhds hδU) hregular
  obtain ⟨V, hVsub, hVopen, hVmem⟩ := mem_nhds_iff.mp hnear
  let V' : Opens M := ⟨V, hVopen⟩
  have hδcont : ContinuousAt δ s₀ :=
    (hδ.contMDiffAt (S.isOpen.mem_nhds hs₀)).continuousAt
  have hparam : (S : Set ℝ) ∩ δ ⁻¹' V ∈ 𝓝 s₀ :=
    inter_mem (S.isOpen.mem_nhds hs₀) (hδcont.preimage_mem_nhds (hVopen.mem_nhds hVmem))
  obtain ⟨T, hTsub, hTopen, hTmem⟩ := mem_nhds_iff.mp hparam
  let T' : Opens ℝ := ⟨T, hTopen⟩
  obtain ⟨W, hW, hmem, hWV, hzeroW⟩ :=
    exists_isOpen_zero_locus_subset_curve_image_of_open V'
      (hρ.mono (fun p hp ↦ (hVsub hp).1))
      (fun p hp ↦ (hVsub hp).2) hdim δ T'
      (hδ.mono (fun t ht ↦ (hTsub ht).1))
      (fun t ht ↦ (hTsub ht).2) (fun t ht ↦ hzero t (hTsub ht).1)
      (fun t ht ↦ hne t (hTsub ht).1) hTmem
  refine ⟨W, hW, hmem, fun p hp ↦ (hVsub (hWV hp)).1, ?_⟩
  intro p hp hz
  obtain ⟨t, ht, htp⟩ := hzeroW p hp hz
  exact ⟨t, (hTsub ht).1, htp⟩
end TauCeti
