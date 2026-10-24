/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import TauCeti.Geometry.Manifold.VectorBundle.CurveInTotalSpace
import Mathlib.Analysis.Calculus.Deriv.Mul

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
from tangent bundles to vector bundles. The vertical computation uses the total-space
curve criterion in `TauCeti.Manifold.hasMFDerivAt_totalSpace_curve_iff`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24.
-/

public noncomputable section

open Bundle Filter Set
open scoped Manifold Topology

namespace Bundle

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
  have hd : HasMFDerivAt 𝓘(𝕜) (I.prod 𝓘(𝕜, F))
      (fun t : 𝕜 ↦ (⟨b, t • v⟩ : TotalSpace F V)) 0
      ((1 : 𝕜 →L[𝕜] 𝕜).smulRight
        ((0 : E), (trivializationAt F V b).continuousLinearMapAt 𝕜 b v)) := by
    rw [TauCeti.Manifold.hasMFDerivAt_totalSpace_curve_iff]
    have hcoord (t : 𝕜) :
        (trivializationAt F V b (⟨b, t • v⟩ : TotalSpace F V)).2 =
          t • (trivializationAt F V b).continuousLinearMapAt 𝕜 b v := by
      rw [Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 _
        (mem_baseSet_trivializationAt F V b)]
      exact ((trivializationAt F V b).linear 𝕜
        (mem_baseSet_trivializationAt F V b)).map_smul t v
    refine ⟨(FiberBundle.continuousAt_totalSpace F _).2 ⟨continuousAt_const, ?_⟩,
      ?_, ?_⟩
    · simp_rw [hcoord]
      exact (continuous_id.smul continuous_const).continuousAt
    · simpa only using hasDerivAt_const (0 : 𝕜) (extChartAt I b b)
    · simpa only [hcoord, one_smul] using
        (hasDerivAt_id' (0 : 𝕜)).smul_const
          ((trivializationAt F V b).continuousLinearMapAt 𝕜 b v)
  rw [hd.mfderiv, zeroSectionTangentEquiv_symm_apply]
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

end Bundle
