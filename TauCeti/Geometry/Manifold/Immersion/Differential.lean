/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Immersion.Basic
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

Reference: M. Hirsch, *Differential Topology*, Chapter 1, §3 (the local immersion
theorem), and Chapter 8, §1 (its use in isotopy extension).
-/

public section

noncomputable section

open Set Function Topology Manifold
open scoped ContDiff

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

end
