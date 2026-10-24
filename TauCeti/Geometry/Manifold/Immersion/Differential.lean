/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Immersion.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.Prod
public import TauCeti.Geometry.Manifold.ContMDiff.Atlas
public import TauCeti.Analysis.Calculus.InverseFunctionTheorem
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Immersion normal forms from split differentials

A map between real or complex Banach spaces with a continuous left inverse to its
derivative has the local normal form of an immersion. The map need only be `C^n` on
an open neighbourhood, with `1 ≤ n`. This turns a differential splitting into
actual slice charts, as needed to extend data from the image of an embedded map.

The construction adds a closed complement to the source and applies the inverse
function theorem to the resulting map. It uses Mathlib's
`ContinuousLinearMap.HasLeftInverse.complement` and
`ContinuousLinearMap.coprodSubtypeLEquivOfIsCompl`, and Tau Ceti's smooth inverse
function theorem on an open neighbourhood.

The same criterion holds for maps between manifolds without boundary. A normal form of a map read
in the preferred extended charts is carried back to the manifolds by composing its charts with the
preferred charts (`Manifold.IsImmersionAtOfComplement.of_writtenInExtChartAt`); on a boundaryless
model the manifold derivative is the derivative of the map read in these charts. A
parameter-preserving map `(p, x) ↦ (p, G (p, x))` is then an immersion at every point where its
slice `x ↦ G (p, x)` is one in the sense of differentials, as for the space-time track of a moving
embedded submanifold.

Reference: M. Hirsch, *Differential Topology*, Chapter 1, §3 (the local immersion
theorem), and Chapter 8, §1 (its use in isotopy extension).
-/

public section

noncomputable section

open Set Function Topology Manifold
open scoped ContDiff Manifold

section Euclidean

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {n : ℕ∞ω} {f : E → F} {s : Set E} {x : E}

/-- A `C^n` map on an open set has an immersion normal form at any point where its
derivative admits a continuous linear left inverse. Both spaces may be infinite dimensional. -/
theorem ContDiffOn.isImmersionAt_of_hasLeftInverse
    (hf : ContDiffOn 𝕜 n f s) (hs : IsOpen s) (hx : x ∈ s) (hn : 1 ≤ n)
    (hdf : (fderiv 𝕜 f x).HasLeftInverse) :
    IsImmersionAt 𝓘(𝕜, E) 𝓘(𝕜, F) n f x := by
  -- Adjoin the closed complement so that the augmented derivative is invertible.
  let G := hdf.complement
  have : CompleteSpace G := hdf.isClosed_complement.completeSpace_coe
  let e : (E × G) ≃L[𝕜] F :=
    (fderiv 𝕜 f x).coprodSubtypeLEquivOfIsCompl hdf.isCompl_complement
      (LinearMap.ker_eq_bot.mpr hdf.injective)
  let g : E × G → F := fun p => f p.1 + (p.2 : F)
  let t : Set (E × G) := Prod.fst ⁻¹' s
  have ht : IsOpen t := hs.preimage continuous_fst
  have hg : ContDiffOn 𝕜 n g t :=
    (hf.comp contDiffOn_fst (fun _ hp => hp)).add
      (G.subtypeL.contDiff.comp contDiff_snd).contDiffOn
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hderiv : HasFDerivAt g (e : (E × G) →L[𝕜] F) (x, 0) := by
    convert (((hf.contDiffAt (hs.mem_nhds hx)).differentiableAt hn0).hasFDerivAt.comp
      (x, (0 : G)) (hasFDerivAt_fst)).add
      (G.subtypeL.hasFDerivAt.comp (x, 0) (hasFDerivAt_snd)) using 1
    · rfl
    · apply ContinuousLinearMap.ext
      intro p
      rfl
  obtain ⟨Θ, hΘ, hxΘ, hsub, hinv⟩ :=
    TauCeti.ContDiffOn.exists_openPartialHomeomorph hg ht hx hn hderiv.fderiv.symm
  have hforward : ContDiffOn 𝕜 n Θ Θ.source := hΘ ▸ hg.mono hsub
  -- The inverse chart straightens the image; the source chart restricts the identity.
  let ψ := Θ.symm.transHomeomorph e.toHomeomorph
  let u : Set E := (fun y => (y, (0 : G))) ⁻¹' Θ.source
  have hu : IsOpen u := Θ.open_source.preimage (continuous_id.prodMk continuous_const)
  let φ := (OpenPartialHomeomorph.refl E).restrOpen u hu
  have hφsource : φ.source = u := by simp [φ]
  have hφtarget : (φ.extend 𝓘(𝕜, E)).target = u := by simp [φ, mfld_simps]
  have hψ : ψ ∈ IsManifold.maximalAtlas 𝓘(𝕜, F) n F := by
    apply ψ.mem_maximalAtlas_of_contMDiffOn
    · exact contMDiffOn_iff_contDiffOn.mpr (e.contDiff.comp_contDiffOn hinv)
    · exact contMDiffOn_iff_contDiffOn.mpr
        (hforward.comp e.symm.contDiff.contDiffOn (fun _ hy => hy))
  refine IsImmersionAt.mk_of_charts e φ ψ (hφsource.symm ▸ hxΘ) ?_
    (φ.mem_maximalAtlas_of_contMDiffOn contMDiffOn_id contMDiffOn_id) hψ ?_ ?_
  · have h := Θ.map_source hxΘ
    simpa [ψ, hΘ, g] using h
  · intro y hy
    have h := Θ.map_source (hφsource ▸ hy)
    simpa [φ, ψ, hΘ, g] using h
  · intro y hy
    have h := Θ.left_inv (hφtarget ▸ hy)
    simpa [φ, ψ, hΘ, g, mfld_simps] using congrArg e h

/-- For a `C^n` map on an open subset of a Banach space, the immersion normal form
is equivalent to the derivative having a continuous linear left inverse. -/
theorem ContDiffOn.isImmersionAt_iff_hasLeftInverse
    (hf : ContDiffOn 𝕜 n f s) (hs : IsOpen s) (hx : x ∈ s) (hn : 1 ≤ n) :
    IsImmersionAt 𝓘(𝕜, E) 𝓘(𝕜, F) n f x ↔ (fderiv 𝕜 f x).HasLeftInverse := by
  refine ⟨fun h => ?_, hf.isImmersionAt_of_hasLeftInverse hs hx hn⟩
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  obtain ⟨L, hL⟩ := isDiffImmersionAt_iff.mp (h.isDiffImmersionAt hn0)
  -- Transport the left inverse through the canonical tangent-space identifications.
  refine ⟨(NormedSpace.fromTangentSpace (𝕜 := 𝕜) x).toContinuousLinearMap.comp
    (L.comp
      (NormedSpace.fromTangentSpace (𝕜 := 𝕜) (f x)).symm.toContinuousLinearMap), ?_⟩
  intro v
  have hleft := hL ((NormedSpace.fromTangentSpace (𝕜 := 𝕜) x).symm v)
  simp only [mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] at hleft
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply] using
    congrArg (NormedSpace.fromTangentSpace (𝕜 := 𝕜) x) hleft

omit [CompleteSpace E] [CompleteSpace F] in
/-- For a finite-dimensional target, a `C^n` map on an open set has the immersion
normal form exactly when its derivative is injective. -/
theorem ContDiffOn.isImmersionAt_iff_injective_fderiv [FiniteDimensional 𝕜 F]
    (hf : ContDiffOn 𝕜 n f s) (hs : IsOpen s) (hx : x ∈ s) (hn : 1 ≤ n) :
    IsImmersionAt 𝓘(𝕜, E) 𝓘(𝕜, F) n f x ↔ Injective (fderiv 𝕜 f x) := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  refine ⟨fun h => ?_, fun hdf => ?_⟩
  · intro u v huv
    have h' := h.mfderiv_injective hn0 (a₁ := (NormedSpace.fromTangentSpace x).symm u)
      (a₂ := (NormedSpace.fromTangentSpace x).symm v) (by
      simp only [mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply, huv])
    exact (NormedSpace.fromTangentSpace (𝕜 := 𝕜) x).symm.injective h'
  · have : FiniteDimensional 𝕜 E :=
      FiniteDimensional.of_injective (fderiv 𝕜 f x).toLinearMap hdf
    have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
    have : CompleteSpace F := FiniteDimensional.complete 𝕜 F
    exact hf.isImmersionAt_of_hasLeftInverse hs hx hn
      (ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hdf)

end Euclidean

namespace Manifold.IsImmersionAtOfComplement

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} {f : M → N} {x : M}

/-- An immersion normal form of a map between boundaryless manifolds, read in the preferred
extended charts, is an immersion normal form of the map itself, with the same complement. -/
theorem of_writtenInExtChartAt [I.Boundaryless] [J.Boundaryless]
    [IsManifold I n M] [IsManifold J n N] (hf : ContinuousAt f x)
    (h : IsImmersionAtOfComplement F 𝓘(𝕜, E) 𝓘(𝕜, E') n (writtenInExtChartAt I J x f)
      (extChartAt I x x)) :
    IsImmersionAtOfComplement F I J n f x := by
  -- The charts of the normal form in the model spaces, read through the preferred charts.
  let φ : OpenPartialHomeomorph M H :=
    (((chartAt H x).transHomeomorph I.toHomeomorph).trans h.domChart).transHomeomorph
      I.toHomeomorph.symm
  let ψ : OpenPartialHomeomorph N G :=
    (((chartAt G (f x)).transHomeomorph J.toHomeomorph).trans h.codChart).transHomeomorph
      J.toHomeomorph.symm
  refine mk_of_continuousAt hf h.equiv φ ψ ?_ ?_ ?_ ?_ ?_
  · simpa [φ] using h.mem_domChart_source
  · simpa [ψ, writtenInExtChartAt] using h.mem_codChart_source
  · exact TauCeti.conj_chartAt_mem_maximalAtlas x h.domChart_mem_maximalAtlas
  · exact TauCeti.conj_chartAt_mem_maximalAtlas (f x) h.codChart_mem_maximalAtlas
  · intro u hu
    have hI : ∀ u, I (I.symm u) = u := fun u => I.right_inv (by simp [I.range_eq_univ])
    have hJ : ∀ u, J (J.symm u) = u := fun u => J.right_inv (by simp [J.range_eq_univ])
    have k1 : (φ.extend I).symm u = (chartAt H x).symm (I.symm (h.domChart.symm u)) := by
      simp [φ, hI, OpenPartialHomeomorph.extend]
    have k2 : ∀ z, ψ.extend J z = h.codChart (J (chartAt G (f x) z)) := by
      intro z
      simp [ψ, hJ, OpenPartialHomeomorph.extend]
    have hu' : (∃ y, I y = u) ∧ u ∈ h.domChart.target ∧
        I.symm (h.domChart.symm u) ∈ (chartAt H x).target := by
      simpa [φ, hI, OpenPartialHomeomorph.extend] using hu
    have := h.writtenInCharts (by simpa [OpenPartialHomeomorph.extend] using hu'.2.1)
    simp only [Function.comp_apply, k1, k2] at this ⊢
    simpa [OpenPartialHomeomorph.extend, writtenInExtChartAt, extChartAt] using this

end Manifold.IsImmersionAtOfComplement

section Manifold

variable {𝕜 : Type*} [RCLike 𝕜]
  {E E' H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [CompleteSpace E']
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} [I.Boundaryless] [J.Boundaryless] [IsManifold I n M] [IsManifold J n N]
  {f : M → N} {s : Set M} {x : M}

/-- A `C^n` map on an open subset of a boundaryless manifold, with values in a boundaryless
manifold, is an immersion at any point where its manifold derivative admits a continuous linear
left inverse. -/
theorem ContMDiffOn.isImmersionAt_of_hasLeftInverse_mfderiv
    (hf : ContMDiffOn I J n f s) (hs : IsOpen s) (hx : x ∈ s) (hn : 1 ≤ n)
    (hdf : (mfderiv I J f x).HasLeftInverse) :
    IsImmersionAt I J n f x := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hfx : ContMDiffAt I J n f x := hf.contMDiffAt (hs.mem_nhds hx)
  -- Read `f` in the preferred extended charts, on an open set around the chart image of `x`.
  let t := (extChartAt I x).target ∩
    (extChartAt I x).symm ⁻¹' (s ∩ f ⁻¹' (extChartAt J (f x)).source)
  have ht : IsOpen t :=
    (continuousOn_extChartAt_symm x).isOpen_inter_preimage (isOpen_extChartAt_target x)
      (hf.continuousOn.isOpen_inter_preimage hs (isOpen_extChartAt_source (f x)))
  have hxt : extChartAt I x x ∈ t := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    simp [hx]
  have hft : ContDiffOn 𝕜 n (writtenInExtChartAt I J x f) t :=
    (contMDiffOn_iff.mp hf).2 x (f x)
  -- On a boundaryless model the manifold derivative is literally the derivative in charts.
  have hderiv : fderiv 𝕜 (writtenInExtChartAt I J x f) (extChartAt I x x) =
      mfderiv I J f x := by
    rw [(hfx.mdifferentiableAt hn0).mfderiv_abuse, I.range_eq_univ, fderivWithin_univ]
  have h := hft.isImmersionAt_of_hasLeftInverse ht hxt hn (hderiv ▸ hdf)
  exact (IsImmersionAtOfComplement.of_writtenInExtChartAt hfx.continuousAt
    h.isImmersionAtOfComplement_complement).isImmersionAt

/-- For a `C^n` map on an open subset of a boundaryless manifold, with values in a boundaryless
manifold, the immersion normal form is equivalent to the manifold derivative having a continuous
linear left inverse. -/
theorem ContMDiffOn.isImmersionAt_iff_hasLeftInverse_mfderiv
    (hf : ContMDiffOn I J n f s) (hs : IsOpen s) (hx : x ∈ s) (hn : 1 ≤ n) :
    IsImmersionAt I J n f x ↔ (mfderiv I J f x).HasLeftInverse := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  exact ⟨fun h => isDiffImmersionAt_iff.mp (h.isDiffImmersionAt hn0),
    hf.isImmersionAt_of_hasLeftInverse_mfderiv hs hx hn⟩

omit [CompleteSpace E] [CompleteSpace E'] in
/-- For a finite-dimensional target model, a `C^n` map on an open subset of a boundaryless
manifold, with values in a boundaryless manifold, has the immersion normal form exactly when its
manifold derivative is injective. -/
theorem ContMDiffOn.isImmersionAt_iff_injective_mfderiv [FiniteDimensional 𝕜 E']
    (hf : ContMDiffOn I J n f s) (hs : IsOpen s) (hx : x ∈ s) (hn : 1 ≤ n) :
    IsImmersionAt I J n f x ↔ Injective (mfderiv I J f x) := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  refine ⟨fun h => h.mfderiv_injective hn0, fun hdf => ?_⟩
  have : FiniteDimensional 𝕜 E :=
    FiniteDimensional.of_injective (mfderiv I J f x).toLinearMap hdf
  have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  have : CompleteSpace E' := FiniteDimensional.complete 𝕜 E'
  exact hf.isImmersionAt_of_hasLeftInverse_mfderiv hs hx hn
    (ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hdf)

variable {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP] [CompleteSpace EP]
  [TopologicalSpace HP] {IP : ModelWithCorners 𝕜 EP HP} [TopologicalSpace P] [ChartedSpace HP P]
  [IP.Boundaryless] [IsManifold IP n P]

/-- A `C^n` parameter-preserving map `(p, x) ↦ (p, G (p, x))` between boundaryless manifolds is an
immersion at every point where its slice at the fixed parameter is an immersion in the sense of
differentials. -/
theorem ContMDiff.isImmersionAt_fst_prod {G : P × M → N} (hG : ContMDiff (IP.prod I) J n G)
    (hn : 1 ≤ n) {q : P × M} (hq : IsDiffImmersionAt I J (fun x => G (q.1, x)) q.2) :
    IsImmersionAt (IP.prod I) (IP.prod J) n (fun q => (q.1, G q)) q := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  refine (contMDiff_fst.prodMk hG).contMDiffOn.isImmersionAt_of_hasLeftInverse_mfderiv
    isOpen_univ (mem_univ q) hn ?_
  exact ((hG q).mdifferentiableAt hn0).hasLeftInverse_mfderiv_fst_prod_iff.mpr
    (isDiffImmersionAt_iff.mp hq)

end Manifold

end
