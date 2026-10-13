/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle
public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Smooth identification of intrinsic and orthogonal normal bundles

Taking orthogonal representatives identifies the intrinsic quotient normal bundle of a
Euclidean embedding with its orthogonal normal bundle by a diffeomorphism. This permits
smooth tubular coordinates constructed with orthogonal vectors to act on intrinsic normal
classes instead. The identification preserves the projection and the zero section.

The comparison is smooth at every order because the intrinsic atlas is transported from
the orthogonal atlas. The regularity of either bundle as a manifold is separately supplied
by the regularity of the embedding and its normal vector-bundle atlas.

The construction upgrades `normalBundleHomeomorphOrthogonal`, using
`normalSpaceTrivialization_apply` and Mathlib's bundle-valued smoothness criterion.

Reference: J. M. Lee, *Introduction to Smooth Manifolds*, second edition, the normal-bundle
construction preceding Theorem 6.24.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {E V F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {n : ℕ∞ω}

/-- Orthogonal representatives identify intrinsic and orthogonal normal bundles smoothly.
Both charted structures use the same fixed model fibre `F`. -/
def normalBundleDiffeomorphOrthogonal (f : SmoothEmbedding I 𝓘(ℝ, V) n M V)
    (hn : n ≠ 0)
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E) (m : ℕ∞ω) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := normalFiberBundle
      (f.contMDiff.of_le (ENat.one_le_iff_ne_zero_withTop.mpr hn))
      (f.isImmersion.mfderiv_injective hn) hdim
    TotalSpace F (fun x => f.NormalSpace x hn) ≃ₘ^m⟮I.prod 𝓘(ℝ, F), I.prod 𝓘(ℝ, F)⟯
      TotalSpace F (fun x => normalSubspace I f x) := by
  let := f.normalSpaceFiberBundle hn hdim
  let := normalFiberBundle
    (f.contMDiff.of_le (ENat.one_le_iff_ne_zero_withTop.mpr hn))
    (f.isImmersion.mfderiv_injective hn) hdim
  let h := f.normalBundleHomeomorphOrthogonal (F := F) hn
  refine { h.toEquiv with contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · intro p
    obtain ⟨hb, hv⟩ := Bundle.contMDiffAt_totalSpace.mp
      (contMDiffAt_id (I := I.prod 𝓘(ℝ, F)) (n := m) (x := p))
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨?_, ?_⟩
    · simpa only [id_eq, h, Homeomorph.coe_toEquiv, normalBundleHomeomorphOrthogonal_apply] using hb
    · simpa only [id_eq, h, normalSpaceFiberBundle_trivializationAt,
        normalSpaceTrivialization_apply, normalFiberBundle_trivializationAt, Homeomorph.coe_toEquiv,
        normalBundleHomeomorphOrthogonal_apply] using hv
  · intro p
    obtain ⟨hb, hv⟩ := Bundle.contMDiffAt_totalSpace.mp
      (contMDiffAt_id (I := I.prod 𝓘(ℝ, F)) (n := m) (x := p))
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨?_, ?_⟩
    · simpa only [id_eq, h, Homeomorph.coe_symm_toEquiv,
        normalBundleHomeomorphOrthogonal_symm_apply] using hb
    · have hp : ((f.normalBundleHomeomorphOrthogonal hn).symm p).proj = p.proj := by
        rw [normalBundleHomeomorphOrthogonal_symm_apply]
      simpa only [id_eq, normalSpaceFiberBundle_trivializationAt,
        normalSpaceTrivialization_apply, h, Homeomorph.coe_symm_toEquiv, hp,
        Homeomorph.apply_symm_apply, normalFiberBundle_trivializationAt] using hv

variable (f : SmoothEmbedding I 𝓘(ℝ, V) n M V) (hn : n ≠ 0)
  (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E) (m : ℕ∞ω)

/-- The smooth identification retains the existing quotient-to-orthogonal homeomorphism. -/
@[simp] theorem normalBundleDiffeomorphOrthogonal_toHomeomorph :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := normalFiberBundle
      (f.contMDiff.of_le (ENat.one_le_iff_ne_zero_withTop.mpr hn))
      (f.isImmersion.mfderiv_injective hn) hdim
    (f.normalBundleDiffeomorphOrthogonal hn hdim m).toHomeomorph =
      f.normalBundleHomeomorphOrthogonal hn := by
  exact Homeomorph.ext fun _ => rfl

/-- The smooth identification takes the orthogonal representative of each normal class. -/
@[simp] theorem normalBundleDiffeomorphOrthogonal_apply
    (p : TotalSpace F (fun x => f.NormalSpace x hn)) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := normalFiberBundle
      (f.contMDiff.of_le (ENat.one_le_iff_ne_zero_withTop.mpr hn))
      (f.isImmersion.mfderiv_injective hn) hdim
    f.normalBundleDiffeomorphOrthogonal hn hdim m p =
      ⟨p.proj, f.normalSpaceOrthogonalEquiv p.proj hn p.2⟩ := by
  simpa only [← Diffeomorph.coe_toHomeomorph, normalBundleDiffeomorphOrthogonal_toHomeomorph]
    using f.normalBundleHomeomorphOrthogonal_apply hn p

/-- The inverse smooth identification takes the intrinsic class of an orthogonal vector. -/
@[simp] theorem normalBundleDiffeomorphOrthogonal_symm_apply
    (p : TotalSpace F (fun x => normalSubspace I f x)) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := normalFiberBundle
      (f.contMDiff.of_le (ENat.one_le_iff_ne_zero_withTop.mpr hn))
      (f.isImmersion.mfderiv_injective hn) hdim
    (f.normalBundleDiffeomorphOrthogonal hn hdim m).symm p =
      ⟨p.proj, f.normalClass p.proj hn
        ((NormedSpace.fromTangentSpace (f p.proj)).symm p.2)⟩ := by
  simpa only [← Diffeomorph.coe_toHomeomorph_symm,
    normalBundleDiffeomorphOrthogonal_toHomeomorph]
    using f.normalBundleHomeomorphOrthogonal_symm_apply hn p

end TauCeti.SmoothEmbedding
