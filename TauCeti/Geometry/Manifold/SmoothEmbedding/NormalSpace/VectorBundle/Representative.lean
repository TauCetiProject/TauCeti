/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Quotient
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.Pullback

/-!
# Smooth descent of representatives to the normal bundle

Let `f : M → N` be an embedding. A family of maps `r x` from the normal spaces of `f` to the
ambient tangent spaces is `C^m` on the intrinsic normal bundle as soon as its values on the normal
classes of ambient tangent vectors are `C^m` on the pulled-back ambient tangent bundle
(`TauCeti.SmoothEmbedding.contMDiff_normalBundle_of_contMDiff_normalClass`). Orthogonal and
symplectic representatives are obtained this way from smooth tangential corrections
(`TauCeti.contMDiff_of_eq_sub_mfderiv_inverse`).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24.
-/

public noncomputable section

open Bundle Manifold Function
open scoped ContDiff Manifold

namespace TauCeti.SmoothEmbedding

variable {E V P H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  {n m : ℕ∞ω} [IsManifold I (m + 1) M] [IsManifold J (m + 1) N]

variable [IsManifold I 1 M] [IsManifold J 1 N]

/-- **Smooth descent of representatives.** A family of maps `r x` from the normal spaces to the
ambient tangent spaces is `C^m` on the intrinsic normal bundle as soon as its values on normal
classes of ambient tangent vectors are `C^m` on the pulled-back ambient tangent bundle. -/
theorem contMDiff_normalBundle_of_contMDiff_normalClass (f : SmoothEmbedding I J n M N)
    (hn : n ≠ 0) (hm : m + 1 ≤ n)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E)
    (r : (x : M) → f.NormalSpace x hn → TangentSpace J (f x))
    (hr : ContMDiff (I.prod 𝓘(ℝ, V)) (J.prod 𝓘(ℝ, V)) m
      (fun p : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) ↦
        (⟨f p.proj, r p.proj (f.normalClass p.proj hn p.2)⟩ : TangentBundle J N))) :
    letI := f.normalSpaceFiberBundle hn hdim
    ContMDiff (I.prod 𝓘(ℝ, P)) (J.prod 𝓘(ℝ, V)) m
      (fun p : TotalSpace P (fun x ↦ f.NormalSpace x hn) ↦
        (⟨f p.proj, r p.proj p.2⟩ : TangentBundle J N)) := by
  let := f.normalSpaceFiberBundle hn hdim
  rw [f.contMDiff_normalBundle_iff hn hm hdim]
  convert hr using 1
  funext p
  rw [Function.comp_apply, normalQuotientMap_apply]

end TauCeti.SmoothEmbedding
