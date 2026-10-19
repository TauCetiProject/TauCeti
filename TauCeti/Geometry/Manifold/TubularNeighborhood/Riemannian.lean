/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Basic

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

private theorem isTopCompl_tangentRange_orthogonal
    (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0) :
    Submodule.IsTopCompl (f.tangentRange x hn)
      (Submodule.orthogonal (f.tangentRange x hn)) := by
  have hclosed : IsClosed
      (f.tangentRange x hn : Set (TangentSpace J (f x))) :=
    f.isClosed_tangentRange x hn
  let : CompleteSpace (f.tangentRange x hn) := hclosed.completeSpace_coe
  exact (f.tangentRange x hn).isTopCompl_orthogonal

/-- Orthogonal representatives identify an intrinsic normal space with the orthogonal complement
of the embedded tangent space in the ambient tangent space. -/
def normalSpaceOrthogonalComplementEquiv
    (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0) :
    f.NormalSpace x hn ≃L[ℝ] Submodule.orthogonal (f.tangentRange x hn) :=
  (f.tangentRange x hn).quotientEquivOfIsTopCompl _
    (isTopCompl_tangentRange_orthogonal f x hn)

/-- The inverse orthogonal-representative equivalence takes the normal class of the given
orthogonal vector. -/
@[simp]
theorem normalSpaceOrthogonalComplementEquiv_symm_apply
    (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0)
    (v : Submodule.orthogonal (f.tangentRange x hn)) :
    (f.normalSpaceOrthogonalComplementEquiv x hn).symm v =
      f.normalClass x hn v := by
  rw [normalClass_def]
  exact Submodule.quotientEquivOfIsTopCompl_symm_apply
    (isTopCompl_tangentRange_orthogonal f x hn) v

/-- The orthogonal representative of the class of an ambient tangent vector is its projection
onto the orthogonal complement of the embedded tangent space. -/
@[simp]
theorem normalSpaceOrthogonalComplementEquiv_normalClass
    (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0)
    (v : TangentSpace J (f x)) :
    f.normalSpaceOrthogonalComplementEquiv x hn (f.normalClass x hn v) =
      (Submodule.orthogonal (f.tangentRange x hn)).orthogonalProjectionOnto v := by
  apply (f.normalSpaceOrthogonalComplementEquiv x hn).symm.injective
  rw [ContinuousLinearEquiv.symm_apply_apply,
    normalSpaceOrthogonalComplementEquiv_symm_apply]
  apply (f.normalClass_eq_iff x hn _ _).mpr
  change v - (Submodule.orthogonal (f.tangentRange x hn)).starProjection v ∈
    f.tangentRange x hn
  simpa only [Submodule.starProjection_orthogonal_val, sub_sub_cancel]
    using (f.tangentRange x hn).starProjection_apply_mem v

/-- The unique tangent vector orthogonal to the embedded tangent space which represents an
intrinsic normal class. -/
def normalRepresentative (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0) :
    f.NormalSpace x hn →L[ℝ] TangentSpace J (f x) :=
  (Submodule.orthogonal (f.tangentRange x hn)).subtypeL.comp
    (f.normalSpaceOrthogonalComplementEquiv x hn).toContinuousLinearMap

/-- The representative of an ambient tangent class is its orthogonal projection to the normal
directions. -/
@[simp]
theorem normalRepresentative_normalClass
    (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0)
    (v : TangentSpace J (f x)) :
    f.normalRepresentative x hn (f.normalClass x hn v) =
      (Submodule.orthogonal (f.tangentRange x hn)).starProjection v := by
  rw [normalRepresentative]
  simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
  simpa only [ContinuousLinearEquiv.coe_coe,
    Submodule.coe_orthogonalProjectionOnto_apply] using congrArg Subtype.val
      (f.normalSpaceOrthogonalComplementEquiv_normalClass x hn v)

/-- Taking the normal class of its orthogonal representative recovers the original class. -/
@[simp]
theorem normalClass_normalRepresentative
    (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0)
    (v : f.NormalSpace x hn) :
    f.normalClass x hn (f.normalRepresentative x hn v) = v := by
  change f.normalClass x hn (↑(f.normalSpaceOrthogonalComplementEquiv x hn v)) = v
  rw [← normalSpaceOrthogonalComplementEquiv_symm_apply,
    ContinuousLinearEquiv.symm_apply_apply]

/-- Normal representatives are orthogonal to every tangent vector of the embedded
submanifold. -/
theorem normalRepresentative_mem_orthogonal
    (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0)
    (v : f.NormalSpace x hn) :
    f.normalRepresentative x hn v ∈ Submodule.orthogonal (f.tangentRange x hn) :=
  (f.normalSpaceOrthogonalComplementEquiv x hn v).property

/-- The normal representative is the unique orthogonal ambient tangent vector in its normal
class. -/
theorem normalRepresentative_eq_iff
    (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0)
    (v : f.NormalSpace x hn) (w : TangentSpace J (f x)) :
    f.normalRepresentative x hn v = w ↔
      w ∈ Submodule.orthogonal (f.tangentRange x hn) ∧ f.normalClass x hn w = v := by
  constructor
  · rintro rfl
    exact ⟨f.normalRepresentative_mem_orthogonal x hn v,
      f.normalClass_normalRepresentative x hn v⟩
  · rintro ⟨hw, hv⟩
    rw [← hv, normalRepresentative_normalClass,
      Submodule.starProjection_eq_self_iff.mpr hw]

/-- The normal representative is perpendicular to the differential of every tangent vector. -/
theorem inner_normalRepresentative_mfderiv
    (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0)
    (v : f.NormalSpace x hn) (w : TangentSpace I x) :
    inner ℝ (f.normalRepresentative x hn v) (mfderiv I J f x w) = 0 := by
  exact Submodule.inner_left_of_mem_orthogonal
    ((f.mem_tangentRange_iff x hn _).2 ⟨w, rfl⟩)
    (f.normalRepresentative_mem_orthogonal x hn v)

section Exponential

variable [IsManifold J ∞ N] [J.Boundaryless] [T2Space N]
  [IsContMDiffRiemannianBundle J ∞ V (fun y : N ↦ TangentSpace J y)]

/-- The natural domain of the normal exponential: the intrinsic normal classes whose orthogonal
representatives lie in the domain of the ambient Riemannian exponential. -/
def normalExpDomain (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) :
    Set (TotalSpace P (fun x ↦ f.NormalSpace x hn)) :=
  {p | f.normalRepresentative p.proj hn p.2 ∈ Manifold.expDomain J N (f p.proj)}

omit [J.Boundaryless] [T2Space N] in
/-- Membership in the natural normal-exponential domain means that the orthogonal representative
lies in the natural domain of the ambient exponential at its base point. -/
@[simp]
theorem mem_normalExpDomain
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (p : TotalSpace P (fun x ↦ f.NormalSpace x hn)) :
    p ∈ f.normalExpDomain (P := P) hn ↔
      f.normalRepresentative p.proj hn p.2 ∈ Manifold.expDomain J N (f p.proj) :=
  Iff.rfl

omit [J.Boundaryless] [T2Space N] in
/-- The zero normal class at every point lies in the natural domain of the normal exponential. -/
theorem zeroSection_mem_normalExpDomain
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (x : M) :
    zeroSection P (fun x ↦ f.NormalSpace x hn) x ∈ f.normalExpDomain (P := P) hn := by
  change f.normalRepresentative x hn 0 ∈ Manifold.expDomain J N (f x)
  rw [map_zero]
  exact Manifold.zero_mem_expDomain (I := J) (M := N) (f x)

omit [T2Space N] in
/-- Every fibre slice of the natural normal-exponential domain is star-convex at zero. -/
theorem starConvex_normalExpDomain_fiber
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (x : M) :
    StarConvex ℝ 0
      {v : f.NormalSpace x hn |
        (⟨x, v⟩ : TotalSpace P (fun x ↦ f.NormalSpace x hn)) ∈
          f.normalExpDomain (P := P) hn} := by
  intro v hv a b _ha hb _hab
  change f.normalRepresentative x hn (a • (0 : f.NormalSpace x hn) + b • v) ∈
    Manifold.expDomain J N (f x)
  rw [smul_zero, zero_add, map_smul]
  exact (Manifold.starConvex_expDomain (I := J) (M := N) (f x)).smul_mem hv hb
    (by linarith)

/-- The normal exponential sends an intrinsic normal class to the ambient exponential of its
orthogonal representative. It takes the base point as a junk value outside its natural domain,
following `Manifold.riemannianExp`. -/
def normalExp (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (p : TotalSpace P (fun x ↦ f.NormalSpace x hn)) : N :=
  Manifold.riemannianExp J N (f p.proj) (f.normalRepresentative p.proj hn p.2)

omit [J.Boundaryless] [T2Space N] in
/-- The normal exponential is the ambient Riemannian exponential of the orthogonal
representative. -/
theorem normalExp_apply
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (p : TotalSpace P (fun x ↦ f.NormalSpace x hn)) :
    f.normalExp (P := P) hn p =
      Manifold.riemannianExp J N (f p.proj) (f.normalRepresentative p.proj hn p.2) :=
  (rfl)

/-- The normal exponential sends the zero section to the original embedding. -/
@[simp]
theorem normalExp_zeroSection
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (x : M) :
    f.normalExp (P := P) hn (zeroSection P (fun x ↦ f.NormalSpace x hn) x) = f x := by
  rw [normalExp]
  change Manifold.riemannianExp J N (f x) (f.normalRepresentative x hn 0) = f x
  rw [map_zero, Manifold.riemannianExp_zero]

omit [T2Space N] in
/-- Outside its natural domain, the normal exponential takes its base point as a junk value. -/
@[simp]
theorem normalExp_of_notMem_normalExpDomain
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    {p : TotalSpace P (fun x ↦ f.NormalSpace x hn)}
    (hp : p ∉ f.normalExpDomain (P := P) hn) :
    f.normalExp (P := P) hn p = f p.proj := by
  exact Manifold.riemannianExp_of_notMem_expDomain (mt (f.mem_normalExpDomain hn p).2 hp)

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
  simp [normalExp]

end Exponential

end TauCeti.SmoothEmbedding
