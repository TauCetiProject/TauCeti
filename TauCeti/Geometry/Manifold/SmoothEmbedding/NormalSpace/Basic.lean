/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import TauCeti.Topology.Algebra.Module.Quotient

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

/-- The tangent subspace of the ambient manifold determined by a positive-regularity embedding
at `x`. It is the range of the differential, regarded as a linear map of tangent spaces. -/
@[expose] noncomputable def tangentRange (f : SmoothEmbedding I J n M N) (x : M) (_hn : n ≠ 0) :
    Submodule 𝕜 (TangentSpace J (f x)) :=
  (mfderiv I J (f : M → N) x).toLinearMap.range

/-- An ambient tangent vector is tangent to the embedding precisely when it is a differential
image. -/
@[simp]
theorem mem_tangentRange_iff (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0)
    (v : TangentSpace J (f x)) :
    v ∈ f.tangentRange x hn ↔ ∃ u : TangentSpace I x, mfderiv I J (f : M → N) x u = v :=
  Iff.rfl

/-- The normal space of a smooth embedding at `x`: ambient tangent vectors modulo vectors
tangent to the embedded submanifold. -/
@[expose]
noncomputable def NormalSpace
    (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0) : Type _ :=
  TangentSpace J (f x) ⧸ f.tangentRange x hn

/-- The tangent range is closed because the differential of an immersion has a continuous
left inverse. -/
theorem isClosed_tangentRange (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0) :
    IsClosed (f.tangentRange x hn : Set (TangentSpace J (f x))) := by
  -- `tangentRange` is the linear range, whose carrier is the set range of `mfderiv`.
  change IsClosed (Set.range (mfderiv I J (f : M → N) x))
  exact ContinuousLinearMap.HasLeftInverse.isClosed_range
    (isDiffImmersionAt_iff.mp (f.isImmersion.isDiffImmersionAt hn x))

noncomputable instance (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0) :
    AddCommGroup (f.NormalSpace x hn) :=
  inferInstanceAs (AddCommGroup (TangentSpace J (f x) ⧸ f.tangentRange x hn))

noncomputable instance (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0) :
    Module 𝕜 (f.NormalSpace x hn) :=
  inferInstanceAs (Module 𝕜 (TangentSpace J (f x) ⧸ f.tangentRange x hn))

noncomputable instance (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0) :
    TopologicalSpace (f.NormalSpace x hn) :=
  inferInstanceAs (TopologicalSpace (TangentSpace J (f x) ⧸ f.tangentRange x hn))

instance (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0) :
    T3Space (f.NormalSpace x hn) := by
  have hclosed : IsClosed (f.tangentRange x hn : Set (TangentSpace J (f x))) :=
    f.isClosed_tangentRange x hn
  exact @Submodule.t3_quotient_of_isClosed 𝕜 (TangentSpace J (f x))
    _ _ _ _ (f.tangentRange x hn) _ hclosed

instance (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0) :
    IsTopologicalAddGroup (f.NormalSpace x hn) :=
  inferInstanceAs (IsTopologicalAddGroup (TangentSpace J (f x) ⧸ f.tangentRange x hn))

instance (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0) :
    ContinuousSMul 𝕜 (f.NormalSpace x hn) :=
  inferInstanceAs (ContinuousSMul 𝕜 (TangentSpace J (f x) ⧸ f.tangentRange x hn))

/-- Project an ambient tangent vector to its normal class. -/
noncomputable def normalClass (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0) :
    TangentSpace J (f x) →ₗ[𝕜] f.NormalSpace x hn :=
  (f.tangentRange x hn).mkQ

/-- The normal-class map is the linear quotient map by the tangent range. -/
theorem normalClass_def (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0) :
    f.normalClass x hn = (f.tangentRange x hn).mkQ := (rfl)

/-- The kernel of the normal-class map is exactly the tangent range. -/
@[simp]
theorem normalClass_ker (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0) :
    (f.normalClass x hn).ker = f.tangentRange x hn :=
  (f.tangentRange x hn).ker_mkQ

/-- The continuous quotient map from ambient tangent vectors to normal classes. -/
noncomputable def normalClassL (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0) :
    TangentSpace J (f x) →L[𝕜] f.NormalSpace x hn :=
  (f.tangentRange x hn).mkQL

/-- The continuous normal-class map gives the normal space its quotient topology. -/
theorem isQuotientMap_normalClassL (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0) :
    Topology.IsQuotientMap (f.normalClassL x hn) :=
  (f.tangentRange x hn).isQuotientMap_mkQL

/-- The continuous normal-class map is an open quotient map. -/
theorem isOpenQuotientMap_normalClassL (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0) :
    IsOpenQuotientMap (f.normalClassL x hn) :=
  (f.tangentRange x hn).isOpenQuotientMap_mkQL

/-- The continuous normal-class map has `normalClass` as its underlying linear map. -/
@[simp]
theorem normalClassL_toLinearMap (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0) :
    (f.normalClassL x hn).toLinearMap = f.normalClass x hn := by
  simp only [normalClassL, normalClass, Submodule.toLinearMap_mkQL]
  rfl

/-- The continuous normal-class map agrees pointwise with the linear normal-class map. -/
@[simp]
theorem normalClassL_apply (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0)
    (v : TangentSpace J (f x)) :
    f.normalClassL x hn v = f.normalClass x hn v := by
  exact congrArg (fun h : TangentSpace J (f x) →ₗ[𝕜] f.NormalSpace x hn => h v)
    (f.normalClassL_toLinearMap x hn)

/-- A continuous linear map vanishing on tangent vectors descends continuously to normal
classes. -/
noncomputable def normalLiftL (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0)
    {V : Type*} [TopologicalSpace V] [AddCommGroup V] [Module 𝕜 V]
    (g : TangentSpace J (f x) →L[𝕜] V)
    (hg : ∀ v ∈ f.tangentRange x hn, g v = 0) : f.NormalSpace x hn →L[𝕜] V :=
  (f.tangentRange x hn).liftQL g (by
    intro v hv
    -- Membership in the continuous linear map's kernel means that its value is zero.
    change g v = 0
    exact hg v hv)

/-- The continuous quotient lift recovers the original map after composition with the
continuous normal-class map. -/
@[simp]
theorem normalLiftL_comp_normalClassL (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0)
    {V : Type*} [TopologicalSpace V] [AddCommGroup V] [Module 𝕜 V]
    (g : TangentSpace J (f x) →L[𝕜] V)
    (hg : ∀ v ∈ f.tangentRange x hn, g v = 0) :
    (f.normalLiftL x hn g hg).comp (f.normalClassL x hn) = g := by
  apply ContinuousLinearMap.coe_injective
  rw [ContinuousLinearMap.toLinearMap_comp]
  simp only [normalLiftL, normalClassL, Submodule.toLinearMap_liftQL,
    Submodule.toLinearMap_mkQL]
  exact (f.tangentRange x hn).liftQ_mkQ g.toLinearMap _

/-- Every normal vector has an ambient tangent representative. -/
theorem normalClass_surjective (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0) :
    Function.Surjective (f.normalClass x hn) :=
  (f.tangentRange x hn).mkQ_surjective

section Equiv

variable {E' F' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {H' G' : Type*} [TopologicalSpace H'] [TopologicalSpace G']
  {I' : ModelWithCorners 𝕜 E' H'} {J' : ModelWithCorners 𝕜 F' G'}
  {M' N' : Type*}
  [TopologicalSpace M'] [ChartedSpace H' M']
  [TopologicalSpace N'] [ChartedSpace G' N']
  {m : ℕ∞ω}
  (f : SmoothEmbedding I J n M N) (g : SmoothEmbedding I' J' m M' N')
  (x : M) (y : M') (hn : n ≠ 0) (hm : m ≠ 0)

/-- An ambient tangent equivalence carrying one embedding's tangent range onto the other's
induces an equivalence of their intrinsic normal spaces. -/
noncomputable def normalSpaceEquivOfMapTangentRange
    (e : TangentSpace J (f x) ≃L[𝕜] TangentSpace J' (g y))
    (h : (f.tangentRange x hn).map e.toLinearMap = g.tangentRange y hm) :
    f.NormalSpace x hn ≃L[𝕜] g.NormalSpace y hm :=
  e.quotientEquiv (f.tangentRange x hn) (g.tangentRange y hm) h

/-- The normal-space equivalence induced by an ambient tangent equivalence applies it to
representatives. -/
@[simp]
theorem normalSpaceEquivOfMapTangentRange_normalClass
    (e : TangentSpace J (f x) ≃L[𝕜] TangentSpace J' (g y))
    (h : (f.tangentRange x hn).map e.toLinearMap = g.tangentRange y hm)
    (w : TangentSpace J (f x)) :
    f.normalSpaceEquivOfMapTangentRange g x y hn hm e h (f.normalClass x hn w) =
      g.normalClass y hm (e w) := by
  exact e.quotientEquiv_mk (f.tangentRange x hn) (g.tangentRange y hm) h w

end Equiv

/-- An ambient tangent vector has zero normal class precisely when it is tangent to the image. -/
@[simp]
theorem normalClass_eq_zero_iff (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0)
    (v : TangentSpace J (f x)) :
    f.normalClass x hn v = 0 ↔ v ∈ f.tangentRange x hn :=
  by
    -- Expose the quotient hidden by `NormalSpace` so the standard quotient criterion applies.
    change (Submodule.Quotient.mk v : TangentSpace J (f x) ⧸ f.tangentRange x hn) = 0 ↔ _
    exact Submodule.Quotient.mk_eq_zero (p := f.tangentRange x hn) (x := v)

/-- The differential of the embedding has zero normal class. -/
@[simp]
theorem normalClass_mfderiv (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0)
    (v : TangentSpace I x) :
    f.normalClass x hn (mfderiv I J (f : M → N) x v) = 0 :=
  (f.normalClass_eq_zero_iff x hn _).2 ⟨v, rfl⟩

/-- Two ambient tangent vectors represent the same normal vector exactly when their difference
is tangent to the embedded submanifold. -/
@[simp]
theorem normalClass_eq_iff (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0)
    (v w : TangentSpace J (f x)) :
    f.normalClass x hn v = f.normalClass x hn w ↔ v - w ∈ f.tangentRange x hn := by
  -- Expose the quotient hidden by `NormalSpace` to use the standard equivalence relation.
  change (Submodule.Quotient.mk v : TangentSpace J (f x) ⧸ f.tangentRange x hn) =
    Submodule.Quotient.mk w ↔ _
  exact Submodule.Quotient.eq (f.tangentRange x hn)

/-- A linear map vanishing on tangent vectors descends to the normal space. -/
noncomputable def normalLift (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0)
    {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    (g : TangentSpace J (f x) →ₗ[𝕜] V)
    (hg : ∀ v ∈ f.tangentRange x hn, g v = 0) : f.NormalSpace x hn →ₗ[𝕜] V :=
  (f.tangentRange x hn).liftQ g (by
    intro v hv
    exact (LinearMap.mem_ker).2 (hg v hv))

/-- The underlying linear map of the continuous normal lift is the linear normal lift. -/
@[simp]
theorem normalLiftL_toLinearMap (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0)
    {V : Type*} [TopologicalSpace V] [AddCommGroup V] [Module 𝕜 V]
    (g : TangentSpace J (f x) →L[𝕜] V)
    (hg : ∀ v ∈ f.tangentRange x hn, g v = 0) :
    (f.normalLiftL x hn g hg).toLinearMap =
      f.normalLift x hn g.toLinearMap (fun v hv => hg v hv) := by
  simp only [normalLiftL, normalLift, Submodule.toLinearMap_liftQL]
  rfl

/-- The continuous normal lift agrees pointwise with the linear normal lift. -/
@[simp]
theorem normalLiftL_apply (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0)
    {V : Type*} [TopologicalSpace V] [AddCommGroup V] [Module 𝕜 V]
    (g : TangentSpace J (f x) →L[𝕜] V)
    (hg : ∀ v ∈ f.tangentRange x hn, g v = 0) (v : f.NormalSpace x hn) :
    f.normalLiftL x hn g hg v =
      f.normalLift x hn g.toLinearMap (fun w hw => hg w hw) v := by
  exact congrArg (fun h : f.NormalSpace x hn →ₗ[𝕜] V => h v)
    (f.normalLiftL_toLinearMap x hn g hg)

/-- Composing the quotient lift with the normal-class map recovers the original linear map. -/
@[simp]
theorem normalLift_comp_normalClass (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0)
    {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    (g : TangentSpace J (f x) →ₗ[𝕜] V)
    (hg : ∀ v ∈ f.tangentRange x hn, g v = 0) :
    (f.normalLift x hn g hg).comp (f.normalClass x hn) = g :=
  (f.tangentRange x hn).liftQ_mkQ g _

/-- A map out of the normal space is determined by its values on ambient tangent classes. -/
theorem normalLift_unique (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0)
    {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    (g : TangentSpace J (f x) →ₗ[𝕜] V)
    (hg : ∀ v ∈ f.tangentRange x hn, g v = 0)
    (h : f.NormalSpace x hn →ₗ[𝕜] V) (hh : h.comp (f.normalClass x hn) = g) :
    h = f.normalLift x hn g hg := by
  apply Submodule.linearMap_qext
  exact hh.trans (f.normalLift_comp_normalClass x hn g hg).symm

/-- A continuous linear map out of the normal space is determined by its composition with
the continuous normal-class map. -/
theorem normalLiftL_unique (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0)
    {V : Type*} [TopologicalSpace V] [AddCommGroup V] [Module 𝕜 V]
    (g : TangentSpace J (f x) →L[𝕜] V)
    (hg : ∀ v ∈ f.tangentRange x hn, g v = 0)
    (h : f.NormalSpace x hn →L[𝕜] V) (hh : h.comp (f.normalClassL x hn) = g) :
    h = f.normalLiftL x hn g hg := by
  apply ContinuousLinearMap.coe_injective
  rw [normalLiftL_toLinearMap]
  apply f.normalLift_unique x hn g.toLinearMap (fun v hv => hg v hv)
  simpa only [← normalClassL_toLinearMap, ← ContinuousLinearMap.toLinearMap_comp] using
    congrArg ContinuousLinearMap.toLinearMap hh

/-- The normal dimension plus the tangent dimension equals the ambient dimension for a
finite-dimensional smooth embedding. -/
theorem finrank_normalSpace_add_finrank (f : SmoothEmbedding I J n M N) (x : M)
    (hn : n ≠ 0) [FiniteDimensional 𝕜 F] :
    Module.finrank 𝕜 (f.NormalSpace x hn) + Module.finrank 𝕜 (TangentSpace I x) =
      Module.finrank 𝕜 (TangentSpace J (f x)) := by
  have hi := f.isImmersion.mfderiv_injective hn x
  have hr : Module.finrank 𝕜 (f.tangentRange x hn) =
      Module.finrank 𝕜 (TangentSpace I x) :=
    LinearMap.finrank_range_of_inj hi
  rw [← hr]
  exact (f.tangentRange x hn).finrank_quotient_add_finrank

/-- The dimension of the normal space is the codimension of the embedded manifold. -/
theorem finrank_normalSpace (f : SmoothEmbedding I J n M N) (x : M)
    (hn : n ≠ 0) [FiniteDimensional 𝕜 F] :
    Module.finrank 𝕜 (f.NormalSpace x hn) =
      Module.finrank 𝕜 (TangentSpace J (f x)) - Module.finrank 𝕜 (TangentSpace I x) := by
  have h := f.finrank_normalSpace_add_finrank x hn
  omega

end TauCeti.SmoothEmbedding
