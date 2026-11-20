/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.VectorBundle
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.SubbundleOrthogonal

/-!
# Orthogonal complements of distributions

On a manifold modelled on a finite-dimensional real space `E`, with a `C^n` Riemannian metric, the
orthogonal complement `x ↦ (D x)ᗮ` of a `C^n` distribution `D` of rank `k` is a `C^n` distribution
of rank `dim E - k` (`TauCeti.IsContMDiffDistribution.orthogonal`). This is the orthogonal
complement of a smooth subbundle of the tangent bundle
(`TauCeti.HasLocalContMDiffSubbundleFrames.orthogonal`), read through the local frame description
of distributions (`TauCeti.isContMDiffDistribution_iff_hasLocalContMDiffSubbundleFrames`).

For instance, the orthogonal complement of the kernel distribution of a submersion is its
horizontal distribution, an Ehresmann connection.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Lemma 10.32
  (the local frame criterion for smooth subbundles) and Chapter 19 (distributions).
-/

public section

open Bundle Module
open scoped Manifold ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {n : ℕ∞ω} {k : ℕ} {D : Π x : M, Submodule ℝ (TangentSpace I x)}

/-- **The orthogonal complement of a distribution.** On a `C^(n+1)` manifold modelled on a
finite-dimensional real space `E`, with a `C^n` Riemannian metric, the orthogonal complement of a
`C^n` distribution of rank `k` is a `C^n` distribution of rank `dim E - k`. -/
theorem IsContMDiffDistribution.orthogonal [IsManifold I (n + 1) M]
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]
    (hD : IsContMDiffDistribution I n k D) :
    IsContMDiffDistribution I n (finrank ℝ E - k) fun x ↦ (D x)ᗮ := by
  have := TangentBundle.contMDiffVectorBundle (n := n) (I := I) (M := M)
  -- The fibres are named explicitly so that the metric's fibre instances are the ones used.
  exact isContMDiffDistribution_iff_hasLocalContMDiffSubbundleFrames.mpr
    (HasLocalContMDiffSubbundleFrames.orthogonal (V := fun x : M ↦ TangentSpace I x)
      (isContMDiffDistribution_iff_hasLocalContMDiffSubbundleFrames.mp hD))

end TauCeti
