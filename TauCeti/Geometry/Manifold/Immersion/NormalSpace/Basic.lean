/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Immersion
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Topology.Algebra.Module.Quotient
import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# Quotient normal spaces of immersions

For an immersion `f : M → N` and `x : M`, the normal space is the ambient tangent space
`T_{f x} N` modulo the range of the differential `mfderiv I J f x`
(`Manifold.IsImmersion.NormalSpace`). This quotient is intrinsic: it needs no metric or choice of
complementary subspace. The normal spaces are indexed by the source point, so two sheets of an
immersion through one image point keep separate normal spaces. They are the fibres of the
quotient normal bundle `f*TN / df(TM)`.

The differential of an immersion of positive smoothness has a continuous left inverse, so it
restricts to a continuous linear equivalence onto `Manifold.IsImmersion.tangentRange`
(`Manifold.IsImmersion.tangentSpaceEquivTangentRange`), its range is closed, and the normal space
is Hausdorff. In finite dimensions it has the expected codimension
(`Manifold.IsImmersion.finrank_normalSpace`, `Manifold.IsImmersion.finrank_normalSpace_eq_one`).
The quotient map `Manifold.IsImmersion.normalClass` characterizes exactly which
ambient tangent vectors represent zero normal vectors, so `0 → T_x M → T_{f x} N → N_x → 0` is
exact (`Manifold.IsImmersion.exact_mfderiv_normalClass`), and linear and continuous linear maps
vanishing on the tangent range descend to the normal space (`Manifold.IsImmersion.normalLift`,
`Manifold.IsImmersion.normalLiftL`), uniquely.

An ambient tangent equivalence carrying one tangent range onto another induces an equivalence of
normal spaces (`Manifold.IsImmersion.normalSpaceEquivOfMapTangentRange`). A continuous linear
map out of the ambient tangent space whose kernel is exactly the tangent range identifies the
normal space with any target of the same dimension
(`Manifold.IsImmersion.normalSpaceEquivOfKer`).

The normal spaces of a bundled smooth embedding `f` are those of its underlying immersion,
`f.isImmersion.NormalSpace`.

For comparison, J. M. Lee, *Introduction to Smooth Manifolds*, second edition, defines the normal
bundle of an embedded submanifold of `ℝⁿ` by orthogonal complements, before Theorem 6.24. The
quotient here is the metric-free analogue of that construction, defined for any immersion.
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

/-- The tangent range is the range of the differential. -/
theorem tangentRange_def (hf : IsImmersion I J n f) (x : M) (hn : n ≠ 0) :
    hf.tangentRange x hn = (mfderiv I J f x).toLinearMap.range := (rfl)

/-- An ambient tangent vector is tangent to the immersion precisely when it is a differential
image. -/
@[simp]
theorem mem_tangentRange_iff (hf : IsImmersion I J n f) (x : M) (hn : n ≠ 0)
    (v : TangentSpace J (f x)) :
    v ∈ hf.tangentRange x hn ↔ ∃ u : TangentSpace I x, mfderiv I J f x u = v :=
  Iff.rfl

/-- At each point `x : M`, the differential `mfderiv I J f x` of a positive-regularity immersion
restricts to a continuous linear equivalence onto `hf.tangentRange x hn`. Neither
finite-dimensionality nor completeness of `𝕜` is required. -/
noncomputable def tangentSpaceEquivTangentRange (hf : IsImmersion I J n f) (x : M)
    (hn : n ≠ 0) : TangentSpace I x ≃L[𝕜] hf.tangentRange x hn :=
  let heq := LinearEquiv.ofInjective (mfderiv I J f x).toLinearMap (hf.mfderiv_injective hn x)
  ContinuousLinearEquiv.mk heq
    ((mfderiv I J f x).continuous.subtype_mk _)
    (by
      obtain ⟨L, hL⟩ := isDiffImmersionAt_iff.mp (hf.isDiffImmersionAt hn x)
      exact (L.continuous.comp continuous_subtypeVal).congr fun ⟨_, u, rfl⟩ ↦
        (hL u).trans (heq.symm_apply_apply u).symm)

/-- `hf.tangentSpaceEquivTangentRange x hn` sends `u` to `mfderiv I J f x u` in the ambient
tangent space. -/
@[simp]
theorem coe_tangentSpaceEquivTangentRange_apply (hf : IsImmersion I J n f) (x : M)
    (hn : n ≠ 0) (u : TangentSpace I x) :
    (hf.tangentSpaceEquivTangentRange x hn u : TangentSpace J (f x)) = mfderiv I J f x u :=
  LinearEquiv.ofInjective_apply (mfderiv I J f x).toLinearMap (h := hf.mfderiv_injective hn x) u

/-- The inverse of `hf.tangentSpaceEquivTangentRange x hn` sends `⟨mfderiv I J f x u, _⟩` back
to `u`. -/
@[simp]
theorem tangentSpaceEquivTangentRange_symm_mfderiv (hf : IsImmersion I J n f) (x : M)
    (hn : n ≠ 0) (u : TangentSpace I x) :
    (hf.tangentSpaceEquivTangentRange x hn).symm ⟨mfderiv I J f x u, ⟨u, rfl⟩⟩ = u :=
  (hf.tangentSpaceEquivTangentRange x hn).symm_apply_apply u

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
noncomputable def normalClass (hf : IsImmersion I J n f) (x : M) (hn : n ≠ 0) :
    TangentSpace J (f x) →ₗ[𝕜] hf.NormalSpace x hn :=
  (hf.tangentRange x hn).mkQ

/-- The normal-class map is the linear quotient map by the tangent range. -/
theorem normalClass_def (hf : IsImmersion I J n f) (x : M) (hn : n ≠ 0) :
    hf.normalClass x hn = (hf.tangentRange x hn).mkQ := (rfl)

/-- The normal class of an ambient tangent vector is its class in the quotient by the tangent
range. -/
theorem normalClass_apply (hf : IsImmersion I J n f) (x : M) (hn : n ≠ 0)
    (v : TangentSpace J (f x)) :
    hf.normalClass x hn v = (Submodule.Quotient.mk v : hf.NormalSpace x hn) := (rfl)

/-- The kernel of the normal-class map is exactly the tangent range. -/
@[simp]
theorem normalClass_ker (hf : IsImmersion I J n f) (x : M) (hn : n ≠ 0) :
    (hf.normalClass x hn).ker = hf.tangentRange x hn :=
  (hf.tangentRange x hn).ker_mkQ

/-- Every normal vector has an ambient tangent representative. -/
theorem normalClass_surjective (hf : IsImmersion I J n f) (x : M) (hn : n ≠ 0) :
    Function.Surjective (hf.normalClass x hn) :=
  (hf.tangentRange x hn).mkQ_surjective

/-- The differential of an immersion followed by the normal projection is a short exact sequence
`0 → T_x M → T_{f x} N → N_x → 0`. -/
theorem exact_mfderiv_normalClass (hf : IsImmersion I J n f) (x : M) (hn : n ≠ 0) :
    Function.Exact (mfderiv I J f x).toLinearMap (hf.normalClass x hn) := by
  rw [LinearMap.exact_iff, normalClass_ker]
  rfl

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

/-- The continuous quotient map from ambient tangent vectors to normal classes. -/
noncomputable def normalClassL (hf : IsImmersion I J n f) (x : M) (hn : n ≠ 0) :
    TangentSpace J (f x) →L[𝕜] hf.NormalSpace x hn :=
  (hf.tangentRange x hn).mkQL

/-- The continuous normal-class map gives the normal space its quotient topology. -/
theorem isQuotientMap_normalClassL (hf : IsImmersion I J n f) (x : M) (hn : n ≠ 0) :
    Topology.IsQuotientMap (hf.normalClassL x hn) :=
  (hf.tangentRange x hn).isQuotientMap_mkQL

/-- The continuous normal-class map is an open quotient map. -/
theorem isOpenQuotientMap_normalClassL (hf : IsImmersion I J n f) (x : M) (hn : n ≠ 0) :
    IsOpenQuotientMap (hf.normalClassL x hn) :=
  (hf.tangentRange x hn).isOpenQuotientMap_mkQL

/-- The continuous normal-class map has `normalClass` as its underlying linear map. -/
@[simp]
theorem normalClassL_toLinearMap (hf : IsImmersion I J n f) (x : M) (hn : n ≠ 0) :
    (hf.normalClassL x hn).toLinearMap = hf.normalClass x hn := by
  simp only [normalClassL, normalClass, Submodule.toLinearMap_mkQL]
  rfl

/-- The continuous normal-class map agrees pointwise with the linear normal-class map. -/
@[simp]
theorem normalClassL_apply (hf : IsImmersion I J n f) (x : M) (hn : n ≠ 0)
    (v : TangentSpace J (f x)) :
    hf.normalClassL x hn v = hf.normalClass x hn v := by
  exact congrArg (fun h : TangentSpace J (f x) →ₗ[𝕜] hf.NormalSpace x hn => h v)
    (hf.normalClassL_toLinearMap x hn)

/-- A continuous linear map vanishing on tangent vectors descends continuously to normal
classes. -/
noncomputable def normalLiftL (hf : IsImmersion I J n f) (x : M) (hn : n ≠ 0)
    {V : Type*} [TopologicalSpace V] [AddCommGroup V] [Module 𝕜 V]
    (g : TangentSpace J (f x) →L[𝕜] V)
    (hg : ∀ v ∈ hf.tangentRange x hn, g v = 0) : hf.NormalSpace x hn →L[𝕜] V :=
  (hf.tangentRange x hn).liftQL g (by
    intro v hv
    -- Membership in the continuous linear map's kernel means that its value is zero.
    change g v = 0
    exact hg v hv)

/-- The continuous quotient lift recovers the original map after composition with the
continuous normal-class map. -/
@[simp]
theorem normalLiftL_comp_normalClassL (hf : IsImmersion I J n f) (x : M) (hn : n ≠ 0)
    {V : Type*} [TopologicalSpace V] [AddCommGroup V] [Module 𝕜 V]
    (g : TangentSpace J (f x) →L[𝕜] V)
    (hg : ∀ v ∈ hf.tangentRange x hn, g v = 0) :
    (hf.normalLiftL x hn g hg).comp (hf.normalClassL x hn) = g := by
  apply ContinuousLinearMap.coe_injective
  rw [ContinuousLinearMap.toLinearMap_comp]
  simp only [normalLiftL, normalClassL, Submodule.toLinearMap_liftQL,
    Submodule.toLinearMap_mkQL]
  exact (hf.tangentRange x hn).liftQ_mkQ g.toLinearMap _

/-- The continuous quotient lift sends the normal class of an ambient tangent vector to the
value of the original map on that vector. -/
theorem normalLiftL_normalClass (hf : IsImmersion I J n f) (x : M) (hn : n ≠ 0)
    {V : Type*} [TopologicalSpace V] [AddCommGroup V] [Module 𝕜 V]
    (g : TangentSpace J (f x) →L[𝕜] V)
    (hg : ∀ v ∈ hf.tangentRange x hn, g v = 0) (v : TangentSpace J (f x)) :
    hf.normalLiftL x hn g hg (hf.normalClass x hn v) = g v := by
  rw [← normalClassL_apply, ← ContinuousLinearMap.comp_apply, normalLiftL_comp_normalClassL]

/-- A linear map vanishing on tangent vectors descends to the normal space. -/
noncomputable def normalLift (hf : IsImmersion I J n f) (x : M) (hn : n ≠ 0)
    {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    (g : TangentSpace J (f x) →ₗ[𝕜] V)
    (hg : ∀ v ∈ hf.tangentRange x hn, g v = 0) : hf.NormalSpace x hn →ₗ[𝕜] V :=
  (hf.tangentRange x hn).liftQ g (by
    intro v hv
    exact (LinearMap.mem_ker).2 (hg v hv))

/-- The underlying linear map of the continuous normal lift is the linear normal lift. -/
@[simp]
theorem normalLiftL_toLinearMap (hf : IsImmersion I J n f) (x : M) (hn : n ≠ 0)
    {V : Type*} [TopologicalSpace V] [AddCommGroup V] [Module 𝕜 V]
    (g : TangentSpace J (f x) →L[𝕜] V)
    (hg : ∀ v ∈ hf.tangentRange x hn, g v = 0) :
    (hf.normalLiftL x hn g hg).toLinearMap =
      hf.normalLift x hn g.toLinearMap (fun v hv => hg v hv) := by
  simp only [normalLiftL, normalLift, Submodule.toLinearMap_liftQL]
  rfl

/-- The continuous normal lift agrees pointwise with the linear normal lift. -/
@[simp]
theorem normalLiftL_apply (hf : IsImmersion I J n f) (x : M) (hn : n ≠ 0)
    {V : Type*} [TopologicalSpace V] [AddCommGroup V] [Module 𝕜 V]
    (g : TangentSpace J (f x) →L[𝕜] V)
    (hg : ∀ v ∈ hf.tangentRange x hn, g v = 0) (v : hf.NormalSpace x hn) :
    hf.normalLiftL x hn g hg v =
      hf.normalLift x hn g.toLinearMap (fun w hw => hg w hw) v := by
  exact congrArg (fun h : hf.NormalSpace x hn →ₗ[𝕜] V => h v)
    (hf.normalLiftL_toLinearMap x hn g hg)

/-- Composing the quotient lift with the normal-class map recovers the original linear map. -/
@[simp]
theorem normalLift_comp_normalClass (hf : IsImmersion I J n f) (x : M) (hn : n ≠ 0)
    {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    (g : TangentSpace J (f x) →ₗ[𝕜] V)
    (hg : ∀ v ∈ hf.tangentRange x hn, g v = 0) :
    (hf.normalLift x hn g hg).comp (hf.normalClass x hn) = g :=
  (hf.tangentRange x hn).liftQ_mkQ g _

/-- The quotient lift sends the normal class of an ambient tangent vector to the value of the
original linear map on that vector. -/
@[simp]
theorem normalLift_normalClass (hf : IsImmersion I J n f) (x : M) (hn : n ≠ 0)
    {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    (g : TangentSpace J (f x) →ₗ[𝕜] V)
    (hg : ∀ v ∈ hf.tangentRange x hn, g v = 0) (v : TangentSpace J (f x)) :
    hf.normalLift x hn g hg (hf.normalClass x hn v) = g v :=
  LinearMap.congr_fun (hf.normalLift_comp_normalClass x hn g hg) v

/-- A map out of the normal space is determined by its values on ambient tangent classes. -/
theorem normalLift_unique (hf : IsImmersion I J n f) (x : M) (hn : n ≠ 0)
    {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    (g : TangentSpace J (f x) →ₗ[𝕜] V)
    (hg : ∀ v ∈ hf.tangentRange x hn, g v = 0)
    (h : hf.NormalSpace x hn →ₗ[𝕜] V) (hh : h.comp (hf.normalClass x hn) = g) :
    h = hf.normalLift x hn g hg := by
  apply Submodule.linearMap_qext
  exact hh.trans (hf.normalLift_comp_normalClass x hn g hg).symm

/-- A continuous linear map out of the normal space is determined by its composition with
the continuous normal-class map. -/
theorem normalLiftL_unique (hf : IsImmersion I J n f) (x : M) (hn : n ≠ 0)
    {V : Type*} [TopologicalSpace V] [AddCommGroup V] [Module 𝕜 V]
    (g : TangentSpace J (f x) →L[𝕜] V)
    (hg : ∀ v ∈ hf.tangentRange x hn, g v = 0)
    (h : hf.NormalSpace x hn →L[𝕜] V) (hh : h.comp (hf.normalClassL x hn) = g) :
    h = hf.normalLiftL x hn g hg := by
  apply ContinuousLinearMap.coe_injective
  rw [normalLiftL_toLinearMap]
  apply hf.normalLift_unique x hn g.toLinearMap (fun v hv => hg v hv)
  simpa only [← normalClassL_toLinearMap, ← ContinuousLinearMap.toLinearMap_comp] using
    congrArg ContinuousLinearMap.toLinearMap hh

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

/-- In codimension one (`finrank 𝕜 E + 1 = finrank 𝕜 F`), every normal fibre has `𝕜`-rank `1`. -/
theorem finrank_normalSpace_eq_one (hf : IsImmersion I J n f) (hn : n ≠ 0)
    (hcodim : Module.finrank 𝕜 E + 1 = Module.finrank 𝕜 F) (x : M) :
    Module.finrank 𝕜 (hf.NormalSpace x hn) = 1 := by
  have : FiniteDimensional 𝕜 F := Module.finite_of_finrank_eq_succ hcodim.symm
  have h := hf.finrank_normalSpace x hn
  rw [TauCeti.finrank_tangentSpace, TauCeti.finrank_tangentSpace] at h
  omega

section Equiv

variable {E' F' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {H' G' : Type*} [TopologicalSpace H'] [TopologicalSpace G']
  {I' : ModelWithCorners 𝕜 E' H'} {J' : ModelWithCorners 𝕜 F' G'}
  {M' N' : Type*}
  [TopologicalSpace M'] [ChartedSpace H' M']
  [TopologicalSpace N'] [ChartedSpace G' N']
  {m : ℕ∞ω} {f' : M' → N'}

/-- An ambient tangent equivalence carrying one immersion's tangent range onto the other's
induces an equivalence of their intrinsic normal spaces. -/
noncomputable def normalSpaceEquivOfMapTangentRange (hf : IsImmersion I J n f)
    (hf' : IsImmersion I' J' m f') (x : M) (y : M') (hn : n ≠ 0) (hm : m ≠ 0)
    (e : TangentSpace J (f x) ≃L[𝕜] TangentSpace J' (f' y))
    (h : (hf.tangentRange x hn).map e.toLinearMap = hf'.tangentRange y hm) :
    hf.NormalSpace x hn ≃L[𝕜] hf'.NormalSpace y hm :=
  e.quotientEquiv (hf.tangentRange x hn) (hf'.tangentRange y hm) h

/-- The normal-space equivalence induced by an ambient tangent equivalence applies it to
representatives. -/
@[simp]
theorem normalSpaceEquivOfMapTangentRange_normalClass (hf : IsImmersion I J n f)
    (hf' : IsImmersion I' J' m f') (x : M) (y : M') (hn : n ≠ 0) (hm : m ≠ 0)
    (e : TangentSpace J (f x) ≃L[𝕜] TangentSpace J' (f' y))
    (h : (hf.tangentRange x hn).map e.toLinearMap = hf'.tangentRange y hm)
    (w : TangentSpace J (f x)) :
    hf.normalSpaceEquivOfMapTangentRange hf' x y hn hm e h (hf.normalClass x hn w) =
      hf'.normalClass y hm (e w) := by
  rw [normalClass_apply, normalClass_apply]
  exact e.quotientEquiv_mk (hf.tangentRange x hn) (hf'.tangentRange y hm) h w

end Equiv

section KerEquiv

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] {V : Type*} [AddCommGroup V] [Module 𝕜 V]
  [FiniteDimensional 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul 𝕜 V]
  [T2Space V]

/-- A continuous linear map out of the ambient tangent space whose kernel is exactly the tangent
range, into a space of the dimension of the normal space, descends to a continuous linear
equivalence from the normal space: the normal class `[v]` corresponds to `g v`. -/
noncomputable def normalSpaceEquivOfKer (hf : IsImmersion I J n f) (x : M) (hn : n ≠ 0)
    (g : TangentSpace J (f x) →L[𝕜] V) (hg : ∀ v, g v = 0 ↔ v ∈ hf.tangentRange x hn)
    (hdim : Module.finrank 𝕜 (hf.NormalSpace x hn) = Module.finrank 𝕜 V) :
    hf.NormalSpace x hn ≃L[𝕜] V :=
  let φ := hf.normalLiftL x hn g fun v ↦ (hg v).2
  have hinj : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun w hw ↦ ?_
    obtain ⟨v, rfl⟩ := hf.normalClass_surjective x hn w
    rw [normalLiftL_normalClass, hg] at hw
    exact (hf.normalClass_eq_zero_iff x hn v).2 hw
  (φ.toLinearMap.linearEquivOfInjective hinj hdim).toContinuousLinearEquiv

/-- The normal class `[v]` corresponds to `g v`. -/
@[simp]
theorem normalSpaceEquivOfKer_normalClass (hf : IsImmersion I J n f) (x : M) (hn : n ≠ 0)
    (g : TangentSpace J (f x) →L[𝕜] V) (hg : ∀ v, g v = 0 ↔ v ∈ hf.tangentRange x hn)
    (hdim : Module.finrank 𝕜 (hf.NormalSpace x hn) = Module.finrank 𝕜 V)
    (v : TangentSpace J (f x)) :
    hf.normalSpaceEquivOfKer x hn g hg hdim (hf.normalClass x hn v) = g v := by
  rw [normalSpaceEquivOfKer, LinearEquiv.coe_toContinuousLinearEquiv',
    LinearMap.linearEquivOfInjective_apply, ContinuousLinearMap.coe_coe, normalLiftL_normalClass]

/-- The value `g v` corresponds to the normal class `[v]`. -/
@[simp]
theorem normalSpaceEquivOfKer_symm_apply (hf : IsImmersion I J n f) (x : M) (hn : n ≠ 0)
    (g : TangentSpace J (f x) →L[𝕜] V) (hg : ∀ v, g v = 0 ↔ v ∈ hf.tangentRange x hn)
    (hdim : Module.finrank 𝕜 (hf.NormalSpace x hn) = Module.finrank 𝕜 V)
    (v : TangentSpace J (f x)) :
    (hf.normalSpaceEquivOfKer x hn g hg hdim).symm (g v) = hf.normalClass x hn v :=
  (ContinuousLinearEquiv.symm_apply_eq _).2
    (hf.normalSpaceEquivOfKer_normalClass x hn g hg hdim v).symm

end KerEquiv

end Manifold.IsImmersion
