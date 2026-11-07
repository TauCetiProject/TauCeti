/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Immersion.Differential
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.SmoothEmbedding

/-!
# Transporting smooth embeddings through partial diffeomorphisms

A smooth embedding whose image lies in the source of a partial diffeomorphism
remains a smooth embedding after composition. The target may have a different
finite-dimensional model. This applies to embedded submanifolds contained in
normal-exponential coordinate neighbourhoods, such as normal sphere bundles.

The differential criterion for immersions and Mathlib's
`PartialDiffeomorph.isLocalDiffeomorphAt` supply the smooth part; the restriction
of the underlying partial homeomorphism supplies the topological embedding.

## References

* M. W. Hirsch, *Differential Topology*, Chapter 1, for immersions and embeddings.
-/

public section

open Manifold Set
open scoped Manifold ContDiff

namespace PartialDiffeomorph

variable {𝕜 : Type*} [RCLike 𝕜]
  {E E' E'' H H' H'' M N P : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [FiniteDimensional 𝕜 E'']
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' H'}
  {K : ModelWithCorners 𝕜 E'' H''} [I.Boundaryless] [K.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
  [TopologicalSpace P] [ChartedSpace H'' P]
  {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N] [IsManifold K n P]

/-- A partial diffeomorphism carries a smooth embedding whose image lies in its source
to a smooth embedding. The target may have a different finite-dimensional model. -/
theorem isSmoothEmbedding_comp
    (Φ : PartialDiffeomorph J K N P n) (hn : 1 ≤ n)
    {f : M → N} (hf : IsSmoothEmbedding I J n f) (hs : ∀ x, f x ∈ Φ.source) :
    IsSmoothEmbedding I K n (Φ ∘ f) := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hsm := Φ.contMDiffOn.comp_contMDiff hf.contMDiff hs
  refine ⟨TauCeti.isImmersion_iff_forall_isImmersionAt.mpr fun x => ?_,
    Φ.toOpenPartialHomeomorph.isEmbedding_restrict.comp
      (hf.isEmbedding.codRestrict Φ.source hs)⟩
  refine (hsm.contMDiffOn.isImmersionAt_iff_injective_mfderiv
    isOpen_univ (mem_univ x) hn).mpr ?_
  have hlocal := Φ.isLocalDiffeomorphAt J K n (hs x)
  rw [mfderiv_comp x (hlocal.mdifferentiableAt hn0)
    (hf.contMDiff.mdifferentiableAt hn0), ContinuousLinearMap.coe_comp]
  exact (hlocal.isInvertible_mfderiv hn0).injective.comp (hf.isImmersion.mfderiv_injective hn0 x)

end PartialDiffeomorph
