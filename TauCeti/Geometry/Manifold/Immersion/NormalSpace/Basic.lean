/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Immersion
public import TauCeti.Topology.Algebra.Module.Quotient

/-!
# Quotient normal spaces of immersions

For an immersion `f : M → N` and `x : M`, the normal space is the ambient tangent space
`T_{f x} N` modulo the range of the differential `mfderiv I J f x`
(`Manifold.IsImmersion.NormalSpace`). This quotient is intrinsic: it needs no metric or choice of
complementary subspace. The normal spaces are indexed by the source point, so two sheets of an
immersion through one image point keep separate normal spaces. They are the fibres of the
quotient normal bundle `f*TN / df(TM)`.

The differential of an immersion of positive smoothness has a continuous left inverse, so its
range is closed and the normal space is Hausdorff. In finite dimensions it has the expected
codimension. The quotient map `Manifold.IsImmersion.normalClass` characterizes exactly which
ambient tangent vectors represent zero normal vectors.

The normal spaces of a bundled smooth embedding, `TauCeti.SmoothEmbedding.NormalSpace`, are these
normal spaces of its underlying immersion.

Reference: J. M. Lee, *Introduction to Smooth Manifolds*, second edition, the normal-bundle
construction preceding Theorem 6.24.
-/

public section

open scoped Manifold ContDiff

namespace Manifold.IsImmersion

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} {f : M → N}

/-- The tangent subspace of the ambient manifold determined by a positive-regularity immersion
at `x`: the range of the differential, regarded as a linear map of tangent spaces. -/
@[expose] noncomputable def tangentRange (_hf : IsImmersion I J n f) (x : M) (_hn : n ≠ 0) :
    Submodule 𝕜 (TangentSpace J (f x)) :=
  (mfderiv I J f x).toLinearMap.range

/-- An ambient tangent vector is tangent to the immersion precisely when it is a differential
image. -/
@[simp]
theorem mem_tangentRange_iff (hf : IsImmersion I J n f) (x : M) (hn : n ≠ 0)
    (v : TangentSpace J (f x)) :
    v ∈ hf.tangentRange x hn ↔ ∃ u : TangentSpace I x, mfderiv I J f x u = v :=
  Iff.rfl

/-- The normal space of an immersion at `x`: ambient tangent vectors modulo the image of the
differential at `x`. -/
@[expose]
noncomputable def NormalSpace (hf : IsImmersion I J n f) (x : M) (hn : n ≠ 0) : Type _ :=
  TangentSpace J (f x) ⧸ hf.tangentRange x hn

/-- The tangent range is closed because the differential of an immersion has a continuous
left inverse. -/
theorem isClosed_tangentRange (hf : IsImmersion I J n f) (x : M) (hn : n ≠ 0) :
    IsClosed (hf.tangentRange x hn : Set (TangentSpace J (f x))) := by
  -- `tangentRange` is the linear range, whose carrier is the set range of `mfderiv`.
  change IsClosed (Set.range (mfderiv I J f x))
  exact ContinuousLinearMap.HasLeftInverse.isClosed_range
    (isDiffImmersionAt_iff.mp (hf.isDiffImmersionAt hn x))

noncomputable instance instAddCommGroupNormalSpace (hf : IsImmersion I J n f) (x : M)
    (hn : n ≠ 0) : AddCommGroup (hf.NormalSpace x hn) :=
  inferInstanceAs (AddCommGroup (TangentSpace J (f x) ⧸ hf.tangentRange x hn))

noncomputable instance instModuleNormalSpace (hf : IsImmersion I J n f) (x : M) (hn : n ≠ 0) :
    Module 𝕜 (hf.NormalSpace x hn) :=
  inferInstanceAs (Module 𝕜 (TangentSpace J (f x) ⧸ hf.tangentRange x hn))

noncomputable instance instTopologicalSpaceNormalSpace (hf : IsImmersion I J n f) (x : M)
    (hn : n ≠ 0) : TopologicalSpace (hf.NormalSpace x hn) :=
  inferInstanceAs (TopologicalSpace (TangentSpace J (f x) ⧸ hf.tangentRange x hn))

instance instT3SpaceNormalSpace (hf : IsImmersion I J n f) (x : M) (hn : n ≠ 0) :
    T3Space (hf.NormalSpace x hn) :=
  @Submodule.t3_quotient_of_isClosed 𝕜 (TangentSpace J (f x))
    _ _ _ _ (hf.tangentRange x hn) _ (hf.isClosed_tangentRange x hn)

instance instIsTopologicalAddGroupNormalSpace (hf : IsImmersion I J n f) (x : M) (hn : n ≠ 0) :
    IsTopologicalAddGroup (hf.NormalSpace x hn) :=
  inferInstanceAs (IsTopologicalAddGroup (TangentSpace J (f x) ⧸ hf.tangentRange x hn))

instance instContinuousSMulNormalSpace (hf : IsImmersion I J n f) (x : M) (hn : n ≠ 0) :
    ContinuousSMul 𝕜 (hf.NormalSpace x hn) :=
  inferInstanceAs (ContinuousSMul 𝕜 (TangentSpace J (f x) ⧸ hf.tangentRange x hn))

/-- A normal space into a finite-dimensional model is finite-dimensional. -/
instance instFiniteDimensionalNormalSpace [FiniteDimensional 𝕜 F] (hf : IsImmersion I J n f)
    (x : M) (hn : n ≠ 0) : FiniteDimensional 𝕜 (hf.NormalSpace x hn) :=
  -- Tangent spaces are their model spaces.
  haveI : FiniteDimensional 𝕜 (TangentSpace J (f x)) := inferInstanceAs (FiniteDimensional 𝕜 F)
  inferInstanceAs (FiniteDimensional 𝕜 (TangentSpace J (f x) ⧸ hf.tangentRange x hn))

/-- Project an ambient tangent vector to its normal class. -/
@[expose] noncomputable def normalClass (hf : IsImmersion I J n f) (x : M) (hn : n ≠ 0) :
    TangentSpace J (f x) →ₗ[𝕜] hf.NormalSpace x hn :=
  (hf.tangentRange x hn).mkQ

/-- The normal-class map is the linear quotient map by the tangent range. -/
theorem normalClass_def (hf : IsImmersion I J n f) (x : M) (hn : n ≠ 0) :
    hf.normalClass x hn = (hf.tangentRange x hn).mkQ := (rfl)

/-- The kernel of the normal-class map is exactly the tangent range. -/
@[simp]
theorem normalClass_ker (hf : IsImmersion I J n f) (x : M) (hn : n ≠ 0) :
    (hf.normalClass x hn).ker = hf.tangentRange x hn :=
  (hf.tangentRange x hn).ker_mkQ

/-- Every normal vector has an ambient tangent representative. -/
theorem normalClass_surjective (hf : IsImmersion I J n f) (x : M) (hn : n ≠ 0) :
    Function.Surjective (hf.normalClass x hn) :=
  (hf.tangentRange x hn).mkQ_surjective

/-- An ambient tangent vector has zero normal class precisely when it is tangent to the image. -/
@[simp]
theorem normalClass_eq_zero_iff (hf : IsImmersion I J n f) (x : M) (hn : n ≠ 0)
    (v : TangentSpace J (f x)) :
    hf.normalClass x hn v = 0 ↔ v ∈ hf.tangentRange x hn :=
  Submodule.Quotient.mk_eq_zero (hf.tangentRange x hn)

/-- The differential of the immersion has zero normal class. -/
@[simp]
theorem normalClass_mfderiv (hf : IsImmersion I J n f) (x : M) (hn : n ≠ 0)
    (v : TangentSpace I x) :
    hf.normalClass x hn (mfderiv I J f x v) = 0 :=
  (hf.normalClass_eq_zero_iff x hn _).2 ⟨v, rfl⟩

/-- Two ambient tangent vectors represent the same normal vector exactly when their difference
is tangent to the immersion. -/
@[simp]
theorem normalClass_eq_iff (hf : IsImmersion I J n f) (x : M) (hn : n ≠ 0)
    (v w : TangentSpace J (f x)) :
    hf.normalClass x hn v = hf.normalClass x hn w ↔ v - w ∈ hf.tangentRange x hn :=
  Submodule.Quotient.eq (hf.tangentRange x hn)

/-- The normal dimension plus the tangent dimension equals the ambient dimension for a
positive-regularity immersion into a manifold with finite-dimensional model. -/
theorem finrank_normalSpace_add_finrank (hf : IsImmersion I J n f) (x : M) (hn : n ≠ 0)
    [FiniteDimensional 𝕜 F] :
    Module.finrank 𝕜 (hf.NormalSpace x hn) + Module.finrank 𝕜 (TangentSpace I x) =
      Module.finrank 𝕜 (TangentSpace J (f x)) := by
  rw [← LinearMap.finrank_range_of_inj (hf.mfderiv_injective hn x)]
  exact (hf.tangentRange x hn).finrank_quotient_add_finrank

/-- The dimension of the normal space is the codimension of the immersion. -/
theorem finrank_normalSpace (hf : IsImmersion I J n f) (x : M) (hn : n ≠ 0)
    [FiniteDimensional 𝕜 F] :
    Module.finrank 𝕜 (hf.NormalSpace x hn) =
      Module.finrank 𝕜 (TangentSpace J (f x)) - Module.finrank 𝕜 (TangentSpace I x) := by
  have h := hf.finrank_normalSpace_add_finrank x hn
  omega

end Manifold.IsImmersion
