/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.IsManifold.Basic
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Map
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Quotient
public import TauCeti.Geometry.Manifold.VectorBundle.Pullback
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Smooth maps between intrinsic normal bundles

A smooth commuting square between smooth embeddings induces a smooth map between their
intrinsic normal bundles. The construction loses one derivative: its fibre map is the ambient
differential, descended to the quotient by the tangent spaces of the embedded submanifolds.

The proof uses the smooth quotient presentation of the intrinsic normal bundle. On ambient
tangent representatives, the induced map is the tangent map of the ambient map, with its base
point identified by the commuting square.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, the normal-bundle construction
  preceding Theorem 6.24.
-/

public noncomputable section

open Bundle Function
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {𝕜 E V P E' V' P' H G H' G' M N M' N' : Type*}
  [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P] [FiniteDimensional 𝕜 P]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [FiniteDimensional 𝕜 E']
  [NormedAddCommGroup V'] [NormedSpace 𝕜 V'] [FiniteDimensional 𝕜 V']
  [NormedAddCommGroup P'] [NormedSpace 𝕜 P'] [FiniteDimensional 𝕜 P']
  [TopologicalSpace H] [TopologicalSpace G]
  [TopologicalSpace H'] [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 V G}
  {I' : ModelWithCorners 𝕜 E' H'} {J' : ModelWithCorners 𝕜 V' G'}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  [TopologicalSpace M'] [ChartedSpace H' M']
  [TopologicalSpace N'] [ChartedSpace G' N']
  {n n' r : ℕ∞ω}

private def pullbackTangentMap
    (f : M → N) (g : M' → N') (u : M → M') (v : N → N')
    (_h : v ∘ f = g ∘ u)
    (p : TotalSpace V (f *ᵖ (TangentSpace J))) :
    TotalSpace V' (g *ᵖ (TangentSpace J')) :=
  ⟨u p.proj, tangentSpaceCast J' (v (f p.proj)) (g (u p.proj))
    (mfderiv J J' v (f p.proj) p.2)⟩

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 V]
  [FiniteDimensional 𝕜 E'] [FiniteDimensional 𝕜 V'] [TopologicalSpace M]
  [TopologicalSpace M'] in
/-- Lifting `pullbackTangentMap` to the ambient tangent bundle gives the ambient tangent map at
the lifted point. The base points agree by the commuting square, and over these equal base
points `tangentSpaceCast` identifies the two tangent spaces, by `heq_tangentSpaceCast`. -/
private theorem lift_pullbackTangentMap
    (f : M → N) (g : M' → N') (u : M → M') (v : N → N')
    (h : v ∘ f = g ∘ u) (p : TotalSpace V (f *ᵖ (TangentSpace J))) :
    Pullback.lift g (pullbackTangentMap (J := J) (J' := J') f g u v h p) =
      tangentMap J J' v (Pullback.lift f p) :=
  TotalSpace.ext (congrFun h p.proj).symm (heq_tangentSpaceCast (congrFun h p.proj) _)

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 V]
  [FiniteDimensional 𝕜 E'] [FiniteDimensional 𝕜 V'] in
private theorem contMDiff_pullbackTangentMap
    [IsManifold J (r + 1) N] [IsManifold J' (r + 1) N']
    (f : SmoothEmbedding I J n M N) (g : SmoothEmbedding I' J' n' M' N')
    (hfn : r ≤ n) (hgn : r ≤ n')
    (u : M → M') (v : N → N')
    (hu : ContMDiff I I' r u) (hv : ContMDiff J J' (r + 1) v)
    (h : v ∘ f = g ∘ u) :
    haveI : IsManifold J 1 N := .of_le (n := r + 1) le_add_self
    haveI : IsManifold J' 1 N' := .of_le (n := r + 1) le_add_self
    ContMDiff (I.prod 𝓘(𝕜, V)) (I'.prod 𝓘(𝕜, V')) r
      (pullbackTangentMap (J := J) (J' := J') f g u v h) := by
  have : IsManifold J 1 N := .of_le (n := r + 1) le_add_self
  have : IsManifold J' 1 N' := .of_le (n := r + 1) le_add_self
  rw [Bundle.Pullback.contMDiff_iff g (g.contMDiff.of_le hgn)]
  constructor
  · exact hu.comp (Bundle.contMDiff_proj (f *ᵖ (TangentSpace J)))
  · have hlift : ContMDiff (I.prod 𝓘(𝕜, V)) (J.prod 𝓘(𝕜, V)) r
        (fun p : TotalSpace V (f *ᵖ (TangentSpace J)) => Pullback.lift f p) :=
      ((Bundle.Pullback.contMDiff_iff f (f.contMDiff.of_le hfn)).mp contMDiff_id).2
    have htangent := (hv.contMDiff_tangentMap le_rfl).comp hlift
    exact htangent.congr (lift_pullbackTangentMap f g u v h)

/-- A commuting square between smooth embeddings induces a `C^r` map of their intrinsic normal
bundles when its map of ambient manifolds is `C^(r + 1)` and its map of embedded manifolds is
differentiable and `C^r`. Thus the normal-bundle construction is functorial with the expected
one-derivative loss in the ambient map. -/
theorem contMDiff_normalBundleMap
    [IsManifold I (r + 1) M] [IsManifold J (r + 1) N]
    [IsManifold I' (r + 1) M'] [IsManifold J' (r + 1) N']
    (f : SmoothEmbedding I J n M N) (g : SmoothEmbedding I' J' n' M' N')
    (hn : n ≠ 0) (hn' : n' ≠ 0) (hfn : r + 1 ≤ n) (hgn : r + 1 ≤ n')
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    (hdim' : Module.finrank 𝕜 P' = Module.finrank 𝕜 V' - Module.finrank 𝕜 E')
    {u : M → M'} {v : N → N'}
    (hu : ContMDiff I I' r u) (hdu : MDifferentiable I I' u)
    (hv : ContMDiff J J' (r + 1) v)
    (h : v ∘ f = g ∘ u) :
    haveI : IsManifold I 1 M := .of_le (n := r + 1) le_add_self
    haveI : IsManifold J 1 N := .of_le (n := r + 1) le_add_self
    haveI : IsManifold I' 1 M' := .of_le (n := r + 1) le_add_self
    haveI : IsManifold J' 1 N' := .of_le (n := r + 1) le_add_self
    letI := f.normalSpaceFiberBundle hn hdim
    letI := g.normalSpaceFiberBundle hn' hdim'
    ContMDiff (I.prod 𝓘(𝕜, P)) (I'.prod 𝓘(𝕜, P')) r
      (f.normalBundleMap (K := P) (K' := P') g hn hn'
        hdu (hv.mdifferentiable (by simp)) h) := by
  have : IsManifold I 1 M := .of_le (n := r + 1) le_add_self
  have : IsManifold J 1 N := .of_le (n := r + 1) le_add_self
  have : IsManifold I' 1 M' := .of_le (n := r + 1) le_add_self
  have : IsManifold J' 1 N' := .of_le (n := r + 1) le_add_self
  let := f.normalSpaceFiberBundle hn hdim
  let := g.normalSpaceFiberBundle hn' hdim'
  rw [f.contMDiff_normalBundle_iff hn hfn hdim]
  have hT := contMDiff_pullbackTangentMap f g
    ((le_add_right le_rfl).trans hfn) ((le_add_right le_rfl).trans hgn) u v hu hv h
  have hq := (g.contMDiff_normalQuotientMap hn' hgn hdim').comp hT
  convert hq using 1
  funext p
  exact f.normalBundleMap_normalQuotientMap g hn hn'
    hdu (hv.mdifferentiable (by simp)) h p

end TauCeti.SmoothEmbedding
