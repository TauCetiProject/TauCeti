/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Diffeomorph
public import TauCeti.Geometry.Manifold.TubularNeighborhood.WholeBundle.Smooth

/-!
# Tubular maps on intrinsic Euclidean normal bundles

A smooth Euclidean embedding admits a smooth open embedding of its whole intrinsic normal
bundle into any prescribed open neighbourhood of its image. This map agrees with the original
embedding on the zero section. The source consists of normal classes in the ambient tangent
spaces, with their quotient topology and transported smooth atlas.

The construction transports `exists_contMDiff_isOpenEmbedding_wholeNormalBundle_subset`
through `SmoothEmbedding.normalBundleDiffeomorphOrthogonal`. It establishes regularity of the
forward map; smoothness of the tubular inverse requires the local normal inverse theorem.

Reference: J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24.
-/

public section

open Set Function Bundle Topology
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {E V F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The entire intrinsic normal bundle of a smooth Euclidean embedding embeds smoothly
and openly inside any prescribed open neighbourhood of the embedded image, fixing the core.
This asserts smoothness of the forward map, without asserting smoothness of its inverse. -/
theorem exists_contMDiff_isOpenEmbedding_normalBundle_subset
    (f : SmoothEmbedding I 𝓘(ℝ, V) ∞ M V)
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E)
    {O : Set V} (hO : IsOpen O) (hfO : range f ⊆ O) :
    let hn : (∞ : ℕ∞ω) ≠ 0 := by simp
    letI := f.normalSpaceFiberBundle (F := F) hn hdim
    ∃ Φ : TotalSpace F (fun x => f.NormalSpace x hn) → V,
      ContMDiff (I.prod 𝓘(ℝ, F)) 𝓘(ℝ, V) ∞ Φ ∧ IsOpenEmbedding Φ ∧
      (∀ x, Φ (zeroSection F (fun x => f.NormalSpace x hn) x) = f x) ∧
      range Φ ⊆ O := by
  let hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  let := f.normalSpaceFiberBundle (F := F) hn hdim
  let := normalFiberBundle (f.contMDiff.of_le (by simp))
    (f.isImmersion.mfderiv_injective (by simp)) hdim
  let h := f.normalBundleDiffeomorphOrthogonal (by simp) hdim ∞
  obtain ⟨Φ, hΦ, hemb, hzero, hΦO⟩ :=
    exists_contMDiff_isOpenEmbedding_wholeNormalBundle_subset f.contMDiff
      (f.isImmersion.mfderiv_injective (by simp)) f.isEmbedding.isInducing hdim hO hfO
  refine ⟨Φ ∘ h, hΦ.comp h.contMDiff, hemb.comp h.toHomeomorph.isOpenEmbedding, ?_, ?_⟩
  · intro x
    simpa only [Function.comp_apply, h, normalBundleDiffeomorphOrthogonal_apply,
      zeroSection, map_zero] using hzero x
  · rintro _ ⟨p, rfl⟩
    exact hΦO ⟨h p, rfl⟩

end TauCeti.SmoothEmbedding
