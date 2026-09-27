/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# Normal spaces of smooth embeddings

At a point of a smoothly embedded submanifold, the normal space is the ambient tangent space
modulo the image of the differential of the embedding. This quotient is intrinsic: it needs no
metric or choice of complementary subspace. It is the fibrewise linear object from which a normal
bundle, and eventually a tubular neighbourhood, must be constructed.

The differential is injective for an immersion of positive smoothness. Consequently the normal
space has the expected codimension in finite dimensions. The quotient map also characterizes
exactly which ambient tangent vectors represent zero normal vectors.

For the tubular-neighbourhood application of normal bundles, see M. Hirsch,
*Differential Topology*, Theorem 6.3.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω}

/-- The tangent subspace of the ambient manifold determined by a smooth embedding at `x`.
It is the range of the differential, regarded as a linear map of tangent spaces. -/
noncomputable def tangentRange (f : SmoothEmbedding I J n M N) (x : M) :
    Submodule 𝕜 (TangentSpace J (f x)) :=
  (mfderiv I J (f : M → N) x).toLinearMap.range

/-- An ambient tangent vector is tangent to the embedding precisely when it is a differential
image. -/
@[simp]
theorem mem_tangentRange_iff (f : SmoothEmbedding I J n M N) (x : M)
    (v : TangentSpace J (f x)) :
    v ∈ f.tangentRange x ↔ ∃ u : TangentSpace I x, mfderiv I J (f : M → N) x u = v :=
  Iff.rfl

/-- The normal space of a smooth embedding at `x`: ambient tangent vectors modulo vectors
tangent to the embedded submanifold. -/
noncomputable def NormalSpace (f : SmoothEmbedding I J n M N) (x : M) : Type _ :=
  TangentSpace J (f x) ⧸ f.tangentRange x

noncomputable instance (f : SmoothEmbedding I J n M N) (x : M) :
    AddCommGroup (f.NormalSpace x) :=
  inferInstanceAs (AddCommGroup (TangentSpace J (f x) ⧸ f.tangentRange x))

noncomputable instance (f : SmoothEmbedding I J n M N) (x : M) :
    Module 𝕜 (f.NormalSpace x) :=
  inferInstanceAs (Module 𝕜 (TangentSpace J (f x) ⧸ f.tangentRange x))

/-- Project an ambient tangent vector to its normal class. -/
noncomputable def normalClass (f : SmoothEmbedding I J n M N) (x : M) :
    TangentSpace J (f x) →ₗ[𝕜] f.NormalSpace x :=
  (f.tangentRange x).mkQ

/-- Every normal vector has an ambient tangent representative. -/
theorem normalClass_surjective (f : SmoothEmbedding I J n M N) (x : M) :
    Function.Surjective (f.normalClass x) :=
  (f.tangentRange x).mkQ_surjective

/-- An ambient tangent vector has zero normal class precisely when it is tangent to the image. -/
@[simp]
theorem normalClass_eq_zero_iff (f : SmoothEmbedding I J n M N) (x : M)
    (v : TangentSpace J (f x)) :
    f.normalClass x v = 0 ↔ v ∈ f.tangentRange x :=
  by
    -- Expose the quotient hidden by `NormalSpace` so the standard quotient criterion applies.
    change (Submodule.Quotient.mk v : TangentSpace J (f x) ⧸ f.tangentRange x) = 0 ↔ _
    exact Submodule.Quotient.mk_eq_zero (p := f.tangentRange x) (x := v)

/-- The differential of the embedding has zero normal class. -/
@[simp]
theorem normalClass_mfderiv (f : SmoothEmbedding I J n M N) (x : M)
    (v : TangentSpace I x) :
    f.normalClass x (mfderiv I J (f : M → N) x v) = 0 :=
  (f.normalClass_eq_zero_iff x _).2 ⟨v, rfl⟩

/-- Two ambient tangent vectors represent the same normal vector exactly when their difference
is tangent to the embedded submanifold. -/
theorem normalClass_eq_iff (f : SmoothEmbedding I J n M N) (x : M)
    (v w : TangentSpace J (f x)) :
    f.normalClass x v = f.normalClass x w ↔ v - w ∈ f.tangentRange x := by
  -- Expose the quotient hidden by `NormalSpace` to use the standard equivalence relation.
  change (Submodule.Quotient.mk v : TangentSpace J (f x) ⧸ f.tangentRange x) =
    Submodule.Quotient.mk w ↔ _
  exact Submodule.Quotient.eq (f.tangentRange x)

/-- A linear map vanishing on tangent vectors descends to the normal space. -/
noncomputable def normalLift (f : SmoothEmbedding I J n M N) (x : M)
    {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    (g : TangentSpace J (f x) →ₗ[𝕜] V)
    (hg : ∀ v ∈ f.tangentRange x, g v = 0) : f.NormalSpace x →ₗ[𝕜] V :=
  (f.tangentRange x).liftQ g (by
    intro v hv
    exact (LinearMap.mem_ker).2 (hg v hv))

@[simp]
theorem normalLift_comp_normalClass (f : SmoothEmbedding I J n M N) (x : M)
    {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    (g : TangentSpace J (f x) →ₗ[𝕜] V)
    (hg : ∀ v ∈ f.tangentRange x, g v = 0) :
    (f.normalLift x g hg).comp (f.normalClass x) = g :=
  (f.tangentRange x).liftQ_mkQ g _

/-- A map out of the normal space is determined by its values on ambient tangent classes. -/
theorem normalLift_unique (f : SmoothEmbedding I J n M N) (x : M)
    {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    (g : TangentSpace J (f x) →ₗ[𝕜] V)
    (hg : ∀ v ∈ f.tangentRange x, g v = 0)
    (h : f.NormalSpace x →ₗ[𝕜] V) (hh : h.comp (f.normalClass x) = g) :
    h = f.normalLift x g hg := by
  apply LinearMap.ext
  intro z
  obtain ⟨v, rfl⟩ := f.normalClass_surjective x z
  change (h.comp (f.normalClass x)) v =
    ((f.normalLift x g hg).comp (f.normalClass x)) v
  rw [hh, f.normalLift_comp_normalClass]

/-- The normal dimension plus the tangent dimension equals the ambient dimension for a
finite-dimensional smooth embedding. -/
theorem finrank_normalSpace_add_finrank (f : SmoothEmbedding I J n M N) (x : M)
    (hn : n ≠ 0) [FiniteDimensional 𝕜 F] :
    Module.finrank 𝕜 (f.NormalSpace x) + Module.finrank 𝕜 (TangentSpace I x) =
      Module.finrank 𝕜 (TangentSpace J (f x)) := by
  have hi := f.isImmersion.mfderiv_injective hn x
  have hr : Module.finrank 𝕜 (f.tangentRange x) =
      Module.finrank 𝕜 (TangentSpace I x) :=
    LinearMap.finrank_range_of_inj hi
  rw [← hr]
  exact (f.tangentRange x).finrank_quotient_add_finrank

/-- The dimension of the normal space is the codimension of the embedded manifold. -/
theorem finrank_normalSpace (f : SmoothEmbedding I J n M N) (x : M)
    (hn : n ≠ 0) [FiniteDimensional 𝕜 F] :
    Module.finrank 𝕜 (f.NormalSpace x) =
      Module.finrank 𝕜 (TangentSpace J (f x)) - Module.finrank 𝕜 (TangentSpace I x) := by
  have h := f.finrank_normalSpace_add_finrank x hn
  omega

end TauCeti.SmoothEmbedding
