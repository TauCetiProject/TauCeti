/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import TauCeti.Geometry.Manifold.VectorBundle.CurveInTotalSpace

/-!
# Tangent spaces along the zero section

The tangent space of a vector bundle at its zero vector splits canonically into the tangent
space of the base and the fibre. The horizontal summand is the differential of the zero
section; the vertical summand is the velocity of scalar multiplication through zero.
Neither a connection nor a norm on the individual fibres is needed.

This decomposition lets one compute the total differential of a map out of a vector bundle
from its restriction to the zero section and its derivatives along the fibres. In particular,
these are the two parts of the differential of the normal exponential in the tubular
neighbourhood theorem.

The horizontal computation generalizes Mathlib's
`TangentBundle.tangentMap_tangentBundle_pure`, by Sébastien Gouëzel and Floris van Doorn,
from tangent bundles to vector bundles. The vertical computation uses the scalar-curve case
`Bundle.TotalSpace.hasMFDerivAt_smul_curve` of the total-space curve criterion.

The chart of the total space at a point `0_{b₀}` of the zero section reads a vector as its base
point in the chart at `b₀` and its fibre coordinate in the trivialization at `b₀`
(`TauCeti.Bundle.extChartAt_zeroSection_apply`); its inverse and source are described by
`TauCeti.Bundle.extChartAt_zeroSection_symm_apply` and
`TauCeti.Bundle.mem_extChartAt_zeroSection_source`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24.
-/

public noncomputable section

open Bundle Filter Set
open scoped Manifold Topology

namespace TauCeti.Bundle

variable {𝕜 B E H F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace B] [ChartedSpace H B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : B → Type*} [∀ b, AddCommMonoid (V b)] [∀ b, Module 𝕜 (V b)]
  [∀ b, TopologicalSpace (V b)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- The tangent space at a zero vector, identified with the base tangent space times the fibre.
The intrinsic characterization is given by `zeroSectionTangentEquiv_mfderiv_zeroSection` and
`zeroSectionTangentEquiv_symm_inr`. -/
def zeroSectionTangentEquiv (b : B) :
    TangentSpace (I.prod 𝓘(𝕜, F)) (zeroSection F V b) ≃L[𝕜] TangentSpace I b × V b :=
  -- Tangent spaces use the model spaces in the preferred charts. The first factor is thus
  -- already the preferred tangent coordinate at `b`; convert only the fibre coordinate.
  (ContinuousLinearEquiv.refl 𝕜 (TangentSpace I b)).prodCongr
    ((trivializationAt F V b).continuousLinearEquivAt 𝕜 b
      (mem_baseSet_trivializationAt F V b)).symm

/-- The splitting retains the base tangent coordinate and converts the preferred fibre
coordinate back to an intrinsic fibre vector. -/
theorem zeroSectionTangentEquiv_apply (b : B)
    (w : TangentSpace (I.prod 𝓘(𝕜, F)) (zeroSection F V b)) :
    zeroSectionTangentEquiv (I := I) b w =
      (w.1, (trivializationAt F V b).symmL 𝕜 b w.2) := by
  -- The product equivalence acts on the model underlying the dependent tangent space.
  change (w.1, ((trivializationAt F V b).continuousLinearEquivAt 𝕜 b
    (mem_baseSet_trivializationAt F V b)).symm w.2) = _
  rw [Trivialization.symm_continuousLinearEquivAt_eq]

/-- The inverse splitting reads the fibre vector in the preferred trivialization. -/
theorem zeroSectionTangentEquiv_symm_apply (b : B) (w : TangentSpace I b × V b) :
    (zeroSectionTangentEquiv (I := I) b).symm w =
      (w.1, (trivializationAt F V b).continuousLinearMapAt 𝕜 b w.2) := by
  -- The inverse product equivalence acts on the model underlying the dependent tangent space.
  change (w.1, (trivializationAt F V b).continuousLinearEquivAt 𝕜 b
    (mem_baseSet_trivializationAt F V b) w.2) = _
  rw [Trivialization.coe_continuousLinearEquivAt_eq]

/-- A fibre vector gives the vertical tangent vector via the velocity of its scalar line
through zero. -/
theorem zeroSectionTangentEquiv_symm_inr (b : B) (v : V b) :
    (zeroSectionTangentEquiv (I := I) b).symm (0, v) =
      mfderiv 𝓘(𝕜) (I.prod 𝓘(𝕜, F))
        (fun t : 𝕜 ↦ (⟨b, t • v⟩ : TotalSpace F V)) 0 (1 : 𝕜) := by
  -- The scalar line through `v` has velocity `(0, ξ)` at `0`, with `ξ` the fibre
  -- coordinate of `v`.
  have hd : HasMFDerivAt 𝓘(𝕜) (I.prod 𝓘(𝕜, F))
      (fun t : 𝕜 ↦ (⟨b, t • v⟩ : TotalSpace F V)) 0
      ((1 : 𝕜 →L[𝕜] 𝕜).smulRight
        ((0 : E), (trivializationAt F V b (⟨b, v⟩ : TotalSpace F V)).2)) := by
    simpa only [one_smul] using TotalSpace.hasMFDerivAt_smul_curve
      (⟨b, v⟩ : TotalSpace F V) (hasDerivAt_id' (0 : 𝕜))
  rw [hd.mfderiv, zeroSectionTangentEquiv_symm_apply,
    Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 _
      (mem_baseSet_trivializationAt F V b)]
  exact (one_smul 𝕜 _).symm

variable [IsManifold I 1 B] [ContMDiffVectorBundle 1 F V I]

/-- In preferred tangent coordinates, the differential of the zero section is the first
summand inclusion. -/
theorem mfderiv_zeroSection (b : B) :
    mfderiv I (I.prod 𝓘(𝕜, F)) (zeroSection F V) b =
      ContinuousLinearMap.inl 𝕜 (TangentSpace I b) F := by
  have hcoord : (extChartAt (I.prod 𝓘(𝕜, F)) (zeroSection F V b)) ∘ zeroSection F V
      =ᶠ[𝓝 b] fun y ↦ (extChartAt I b y, (0 : F)) := by
    filter_upwards [(trivializationAt F V b).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt F V b)] with y hy
    simp only [Function.comp_apply, FiberBundle.extChartAt, zeroSection,
      PartialEquiv.trans_apply, PartialEquiv.prod_coe,
      PartialEquiv.refl_coe, id_eq]
    -- The partial equivalence and the trivialization have the same underlying function.
    exact congrArg (fun q : B × F ↦ (extChartAt I b q.1, q.2))
      ((trivializationAt F V b).zeroSection 𝕜 hy)
  have hchain := mfderiv_comp b
    (mdifferentiableAt_extChartAt (I := I.prod 𝓘(𝕜, F)) (mem_chart_source _ _))
    (mdifferentiableAt_zeroSection 𝕜 V (IB := I))
  -- The chart and bundle tangent spaces use the same model with different dependent types.
  -- `erw` lets the chain rule identify those model spaces when cancelling the chart derivative.
  erw [mfderiv_extChartAt_self, ContinuousLinearMap.id_comp] at hchain
  have hpair : mfderiv I 𝓘(𝕜, E × F) (fun y ↦ (extChartAt I b y, (0 : F))) b =
      ContinuousLinearMap.inl 𝕜 (TangentSpace I b) F := by
    have hp := mfderiv_comp (I := I) (I' := 𝓘(𝕜, E)) (I'' := 𝓘(𝕜, E × F)) b
      (f := extChartAt I b) (g := ContinuousLinearMap.inl 𝕜 E F)
      (ContinuousLinearMap.inl 𝕜 E F).mdifferentiableAt
      (mdifferentiableAt_extChartAt (x := b) (mem_chart_source _ _))
    erw [ContinuousLinearMap.mfderiv_eq, mfderiv_extChartAt_self,
      ContinuousLinearMap.comp_id] at hp
    exact hp
  erw [hcoord.mfderiv_eq, hpair] at hchain
  -- The congruence rule inserts the identity transport between the two vector-space
  -- tangent types. It acts identically on the preferred coordinates.
  exact hchain.symm

/-- The differential of the zero section is the horizontal summand of the canonical
splitting. -/
@[simp]
theorem zeroSectionTangentEquiv_mfderiv_zeroSection (b : B) (u : TangentSpace I b) :
    zeroSectionTangentEquiv (I := I) b
      (mfderiv I (I.prod 𝓘(𝕜, F)) (zeroSection F V) b u) = (u, 0) := by
  rw [zeroSectionTangentEquiv_apply]
  -- The differential lands in a dependent tangent space represented by the model product.
  erw [mfderiv_zeroSection]
  exact Prod.ext rfl (map_zero _)

/-- The inverse splitting is the sum of the differential of the zero section and the
velocity of the scalar line through the given fibre vector. This characterizes the splitting
without reference to a trivialization. -/
theorem zeroSectionTangentEquiv_symm_eq (b : B) (u : TangentSpace I b) (v : V b) :
    (zeroSectionTangentEquiv (I := I) b).symm (u, v) =
      mfderiv I (I.prod 𝓘(𝕜, F)) (zeroSection F V) b u +
        (zeroSectionTangentEquiv (I := I) b).symm (0, v) := by
  apply (zeroSectionTangentEquiv (I := I) b).injective
  simp

end TauCeti.Bundle

/-! ### The chart of the total space at a point of the zero section -/

namespace TauCeti.Bundle

variable {𝕜 B EB HB F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : B → Type*} [∀ b, Zero (V b)] [∀ b, TopologicalSpace (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V]

/-- The chart of the total space at a point `0_{b₀}` of the zero section reads a vector over the
base set of the trivialization at `b₀` as its base point in the chart at `b₀` and its fibre
coordinate in the trivialization at `b₀`. -/
theorem extChartAt_zeroSection_apply (b₀ : B) {v : TotalSpace F V}
    (hv : v.proj ∈ (trivializationAt F V b₀).baseSet) :
    extChartAt (IB.prod 𝓘(𝕜, F)) (zeroSection F V b₀) v =
      (extChartAt IB b₀ v.proj, (trivializationAt F V b₀ v).2) := by
  rw [FiberBundle.extChartAt]
  simp [(trivializationAt F V b₀).coe_fst' hv]

/-- The inverse of the chart of the total space at a point `0_{b₀}` of the zero section. -/
theorem extChartAt_zeroSection_symm_apply (b₀ : B) {x : EB}
    (hx : (extChartAt IB b₀).symm x ∈ (trivializationAt F V b₀).baseSet) (w : F) :
    (extChartAt (IB.prod 𝓘(𝕜, F)) (zeroSection F V b₀)).symm (x, w) =
      ⟨(extChartAt IB b₀).symm x,
        (trivializationAt F V b₀).symm ((extChartAt IB b₀).symm x) w⟩ := by
  rw [FiberBundle.extChartAt]
  exact ((trivializationAt F V b₀).mk_symm hx w).symm

/-- A vector lies in the source of the chart of the total space at a point `0_{b₀}` of the zero
section exactly when its base point lies in the source of the chart at `b₀` and in the base set
of the trivialization at `b₀`. -/
theorem mem_extChartAt_zeroSection_source (b₀ : B) (v : TotalSpace F V) :
    v ∈ (extChartAt (IB.prod 𝓘(𝕜, F)) (zeroSection F V b₀)).source ↔
      v.proj ∈ (extChartAt IB b₀).source ∩ (trivializationAt F V b₀).baseSet := by
  rw [FiberBundle.extChartAt]
  simp only [PartialEquiv.trans_source, mem_inter_iff,
    Trivialization.mem_source, mem_preimage, PartialEquiv.prod_source, PartialEquiv.refl_source,
    mem_prod, mem_univ, and_true, zeroSection_proj]
  exact ⟨fun h ↦ ⟨(trivializationAt F V b₀).coe_fst' h.1 ▸ h.2, h.1⟩,
    fun h ↦ ⟨h.2, ((trivializationAt F V b₀).coe_fst' h.2).symm ▸ h.1⟩⟩

/-- The inverse of the chart of the total space at a point `0_{b₀}` of the zero section, at a
point `(φ b, w)` of the image of the fibre over `b`, where `φ` is the chart at `b₀`, is the
vector of fibre coordinate `w` over `b` in the trivialization at `b₀`. -/
theorem extChartAt_zeroSection_symm_apply_extChartAt (b₀ : B) {b : B}
    (hb : b ∈ (extChartAt IB b₀).source ∩ (trivializationAt F V b₀).baseSet) (w : F) :
    (extChartAt (IB.prod 𝓘(𝕜, F)) (zeroSection F V b₀)).symm (extChartAt IB b₀ b, w) =
      ⟨b, (trivializationAt F V b₀).symm b w⟩ := by
  have h := (extChartAt IB b₀).left_inv hb.1
  rw [extChartAt_zeroSection_symm_apply b₀ (by rw [h]; exact hb.2) w, h]

end TauCeti.Bundle
