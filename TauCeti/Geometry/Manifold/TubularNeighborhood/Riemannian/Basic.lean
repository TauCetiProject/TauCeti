/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Basic
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Riemannian
import TauCeti.Geometry.Manifold.TubularNeighborhood.Riemannian.Lift

/-!
# The normal exponential of a smooth embedding

For a smooth embedding into a finite-dimensional Riemannian manifold, every intrinsic normal
class has a unique representative orthogonal to the tangent space of the embedded submanifold.
The **normal exponential** sends that representative through the ambient Riemannian exponential.
Its natural domain consists of the classes whose representatives lie in the domain of the
ambient exponential map; this domain contains the zero section and is star-convex in each fibre.

This is the local map used to construct tubular neighbourhoods in a general ambient manifold.
The tubular-neighbourhood theorem additionally shrinks its domain so that the normal exponential
is injective and a diffeomorphism onto an ambient neighbourhood.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24.
* M. W. Hirsch, *Differential Topology*, Chapter 4, Theorem 6.3.
-/

public section

noncomputable section

open Bundle Manifold Set
open scoped ContDiff InnerProductSpace Manifold

namespace TauCeti.SmoothEmbedding

variable {E V H G M N P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω}

variable [RiemannianBundle (fun y : N ↦ TangentSpace J y)]

section Exponential

variable [IsManifold J ∞ N] [J.Boundaryless] [T2Space N]
  [IsContMDiffRiemannianBundle J ∞ V (fun y : N ↦ TangentSpace J y)]

/-- The natural domain of the normal exponential: the intrinsic normal classes whose orthogonal
representatives lie in the domain of the ambient Riemannian exponential. -/
def normalExpDomain (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) :
    Set (TotalSpace P (fun x ↦ f.NormalSpace x hn)) :=
  TauCeti.Bundle.liftExpDomain f (fun x ↦ f.normalRepresentative x hn)

omit [J.Boundaryless] [T2Space N] in
/-- Membership in the natural normal-exponential domain means that the orthogonal representative
lies in the natural domain of the ambient exponential at its base point. -/
@[simp]
theorem mem_normalExpDomain
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (p : TotalSpace P (fun x ↦ f.NormalSpace x hn)) :
    p ∈ f.normalExpDomain (P := P) hn ↔
      f.normalRepresentative p.proj hn p.2 ∈ Manifold.expDomain J N (f p.proj) :=
  TauCeti.Bundle.mem_liftExpDomain f (fun x ↦ f.normalRepresentative x hn) p

omit [J.Boundaryless] [T2Space N] in
/-- On an orthogonal normal fibre, the normal-exponential domain is the preimage of the
ambient exponential domain under the inclusion into the tangent space. -/
theorem normalExpDomain_fiber_eq_preimage
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (x : M) :
    {v : (f.tangentRange x hn)ᗮ |
      (⟨x, f.normalClass x hn v⟩ : TotalSpace P (fun y ↦ f.NormalSpace y hn)) ∈
        f.normalExpDomain hn} =
      Subtype.val ⁻¹' Manifold.expDomain J N (f x) := by
  ext v
  simp only [mem_ofPred_eq, mem_normalExpDomain, normalRepresentative_normalClass,
    Submodule.starProjection_mem_subspace_eq_self, mem_preimage]

omit [J.Boundaryless] [T2Space N] in
/-- The zero normal class at every point lies in the natural domain of the normal exponential. -/
theorem zeroSection_mem_normalExpDomain
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (x : M) :
    zeroSection P (fun x ↦ f.NormalSpace x hn) x ∈ f.normalExpDomain (P := P) hn :=
  TauCeti.Bundle.zeroSection_mem_liftExpDomain f (fun x ↦ f.normalRepresentative x hn) x

omit [J.Boundaryless] [T2Space N] in
/-- Every fibre slice of the natural normal-exponential domain is star-convex at zero. -/
theorem starConvex_normalExpDomain_fiber
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (x : M) :
    StarConvex ℝ 0
      {v : f.NormalSpace x hn |
        (⟨x, v⟩ : TotalSpace P (fun x ↦ f.NormalSpace x hn)) ∈
          f.normalExpDomain (P := P) hn} :=
  TauCeti.Bundle.starConvex_liftExpDomain_fiber f (fun x ↦ f.normalRepresentative x hn) x

/-- The normal exponential sends an intrinsic normal class to the ambient exponential of its
orthogonal representative. It takes the base point as a junk value outside its natural domain,
following `Manifold.riemannianExp`. -/
def normalExp (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (p : TotalSpace P (fun x ↦ f.NormalSpace x hn)) : N :=
  TauCeti.Bundle.liftExp f (fun x ↦ f.normalRepresentative x hn) p

omit [J.Boundaryless] [T2Space N] in
/-- The normal exponential is the ambient Riemannian exponential of the orthogonal
representative. -/
theorem normalExp_apply
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (p : TotalSpace P (fun x ↦ f.NormalSpace x hn)) :
    f.normalExp (P := P) hn p =
      Manifold.riemannianExp J N (f p.proj) (f.normalRepresentative p.proj hn p.2) :=
  TauCeti.Bundle.liftExp_apply f (fun x ↦ f.normalRepresentative x hn) p

/-- The normal exponential sends the zero section to the original embedding. -/
@[simp]
theorem normalExp_zeroSection
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (x : M) :
    f.normalExp (P := P) hn (zeroSection P (fun x ↦ f.NormalSpace x hn) x) = f x :=
  TauCeti.Bundle.liftExp_zeroSection f (fun x ↦ f.normalRepresentative x hn) x

omit [T2Space N] in
/-- Outside its natural domain, the normal exponential takes its base point as a junk value. -/
@[simp]
theorem normalExp_of_notMem_normalExpDomain
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    {p : TotalSpace P (fun x ↦ f.NormalSpace x hn)}
    (hp : p ∉ f.normalExpDomain (P := P) hn) :
    f.normalExp (P := P) hn p = f p.proj :=
  TauCeti.Bundle.liftExp_of_notMem_liftExpDomain f (fun x ↦ f.normalRepresentative x hn) hp

omit [J.Boundaryless] [T2Space N] in
/-- On the class of an ambient tangent vector, the normal exponential uses its orthogonal
projection to the normal directions. -/
@[simp]
theorem normalExp_normalClass
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (x : M)
    (v : TangentSpace J (f x)) :
    f.normalExp (P := P) hn ⟨x, f.normalClass x hn v⟩ =
      Manifold.riemannianExp J N (f x)
        ((Submodule.orthogonal (f.tangentRange x hn)).starProjection v) := by
  simp [normalExp_apply]

omit [J.Boundaryless] [T2Space N] in
/-- On an orthogonal normal vector, the normal exponential agrees with the ambient
Riemannian exponential without an additional projection. -/
-- The general normal-class and orthogonal-projection simp lemmas already normalize this.
theorem normalExp_normalClass_orthogonal
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (x : M)
    (v : (f.tangentRange x hn)ᗮ) :
    f.normalExp (P := P) hn ⟨x, f.normalClass x hn v⟩ =
      Manifold.riemannianExp J N (f x) v := by
  simp only [normalExp_normalClass, Submodule.starProjection_mem_subspace_eq_self]

end Exponential

end TauCeti.SmoothEmbedding
