/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Geometry.Manifold.SmoothEmbedding.LeftInverse
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
neighbourhood theorem. A map of vector bundles over the identity of the base which is linear on
the fibres acts on these splittings by the identity on the base part and by its fibre maps on
the fibre part (`TauCeti.Bundle.mfderiv_zeroSection_zeroSectionTangentEquiv_symm`).

Over a boundaryless base with finite-dimensional model and fibre, the zero section is a smooth
embedding (`TauCeti.Bundle.isSmoothEmbedding_zeroSection`), since the bundle projection is a smooth
left inverse.

The horizontal computation generalizes Mathlib's
`TangentBundle.tangentMap_tangentBundle_pure`, by Sébastien Gouëzel and Floris van Doorn,
from tangent bundles to vector bundles. The vertical computation uses the scalar-curve case
`Bundle.TotalSpace.hasMFDerivAt_smul_curve` of the total-space curve criterion.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24.
-/

public noncomputable section

open Bundle Filter Set
open scoped Manifold Topology ContDiff

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

/-- In preferred tangent coordinates, the differential of the zero section is the first
summand inclusion. -/
theorem mfderiv_zeroSection (b : B) :
    mfderiv I (I.prod 𝓘(𝕜, F)) (zeroSection F V) b =
      ContinuousLinearMap.inl 𝕜 (TangentSpace I b) F := by
  -- In the preferred charts the zero section is the first summand inclusion.
  have key : ∀ y ∈ (extChartAt I b).target,
      (extChartAt I b).symm y ∈ (trivializationAt F V b).baseSet →
      writtenInExtChartAt I (I.prod 𝓘(𝕜, F)) b (zeroSection F V) y =
        ContinuousLinearMap.inl 𝕜 E F y := by
    intro y hy hs
    have h0 := (trivializationAt F V b).zeroSection 𝕜 hs
    simp only [writtenInExtChartAt, Function.comp_apply, FiberBundle.extChartAt,
      PartialEquiv.trans_apply, PartialEquiv.prod_coe, PartialEquiv.refl_coe, id_eq]
    -- The partial equivalence and the trivialization have the same underlying function.
    change (extChartAt I b ((trivializationAt F V b) (zeroSection F V _)).1,
      ((trivializationAt F V b) (zeroSection F V _)).2) = _
    rw [h0]
    exact Prod.ext ((extChartAt I b).right_inv hy) rfl
  have hb : (extChartAt I b).symm (extChartAt I b b) ∈ (trivializationAt F V b).baseSet := by
    rw [extChartAt_to_inv]
    exact mem_baseSet_trivializationAt F V b
  refine HasMFDerivAt.mfderiv ⟨(Trivialization.continuous_zeroSection 𝕜 (E := V)).continuousAt, ?_⟩
  refine (ContinuousLinearMap.inl 𝕜 E F).hasFDerivAt.hasFDerivWithinAt.congr_of_eventuallyEq
    ?_ (key _ (mem_extChartAt_target b) hb)
  filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem (I := I) (mem_extChartAt_target b),
    nhdsWithin_le_nhds ((continuousAt_extChartAt_symm b).eventually
      ((trivializationAt F V b).open_baseSet.mem_nhds hb))] with y hy hs using key y hy hs

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

section FibrewiseLinear

variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {V' : B → Type*} [∀ b, AddCommMonoid (V' b)] [∀ b, Module 𝕜 (V' b)]
  [∀ b, TopologicalSpace (V' b)] [TopologicalSpace (TotalSpace F' V')]
  [FiberBundle F' V'] [VectorBundle 𝕜 F' V']

/-- A map of vector bundles over the identity of the base which is linear on each fibre,
`⟨b, v⟩ ↦ ⟨b, φ_b v⟩`, has differential `(u, v) ↦ (u, φ_b v)` at a zero vector, in the canonical
splittings of the tangent spaces along the zero sections into base and fibre parts. -/
theorem mfderiv_zeroSection_zeroSectionTangentEquiv_symm {g : TotalSpace F V → TotalSpace F' V'}
    (φ : ∀ b, V b →ₗ[𝕜] V' b) (hg : ∀ b v, g ⟨b, v⟩ = ⟨b, φ b v⟩) (b : B)
    (hgd : MDifferentiableAt (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, F')) g (zeroSection F V b))
    (u : TangentSpace I b) (v : V b) :
    mfderiv (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, F')) g (zeroSection F V b)
        ((zeroSectionTangentEquiv (I := I) b).symm (u, v)) =
      (zeroSectionTangentEquiv (I := I) (F := F') (V := V') b).symm (u, φ b v) := by
  have hz : g ∘ zeroSection F V = zeroSection F' V' := funext fun b ↦ by
    simp only [Function.comp_apply, zeroSection, hg, map_zero]
  -- The scalar line through `v` is carried to the scalar line through `φ_b v`.
  have hl : g ∘ (fun t : 𝕜 ↦ (⟨b, t • v⟩ : TotalSpace F V)) =
      fun t : 𝕜 ↦ (⟨b, t • φ b v⟩ : TotalSpace F' V') := funext fun t ↦ by
    simp only [Function.comp_apply, hg, map_smul]
  have hline : MDifferentiableAt 𝓘(𝕜) (I.prod 𝓘(𝕜, F))
      (fun t : 𝕜 ↦ (⟨b, t • v⟩ : TotalSpace F V)) 0 :=
    (TotalSpace.hasMFDerivAt_smul_curve (⟨b, v⟩ : TotalSpace F V)
      (hasDerivAt_id' (0 : 𝕜))).mdifferentiableAt
  have hhor : mfderiv (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, F')) g (zeroSection F V b)
      (mfderiv I (I.prod 𝓘(𝕜, F)) (zeroSection F V) b u) =
      mfderiv I (I.prod 𝓘(𝕜, F')) (zeroSection F' V') b u := by
    rw [← mfderiv_comp_apply b hgd (mdifferentiableAt_zeroSection 𝕜 V), hz]
  have hver : mfderiv (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, F')) g (zeroSection F V b)
      ((zeroSectionTangentEquiv (I := I) b).symm (0, v)) =
      (zeroSectionTangentEquiv (I := I) (F := F') (V := V') b).symm (0, φ b v) := by
    have h := mfderiv_comp_apply_of_eq (0 : 𝕜) hgd hline (by simp [zeroSection]) (1 : 𝕜)
    rw [zeroSectionTangentEquiv_symm_inr, zeroSectionTangentEquiv_symm_inr, ← h, hl]
  rw [zeroSectionTangentEquiv_symm_eq, map_add, hhor, hver]
  exact (zeroSectionTangentEquiv_symm_eq b u (φ b v)).symm

end FibrewiseLinear

section Embedding

variable {𝕂 : Type*} [RCLike 𝕂] [NormedSpace 𝕂 E] [NormedSpace 𝕂 F]
  {J : ModelWithCorners 𝕂 E H} [J.Boundaryless] [FiniteDimensional 𝕂 E] [FiniteDimensional 𝕂 F]
  {W : B → Type*} [∀ b, AddCommMonoid (W b)] [∀ b, Module 𝕂 (W b)]
  [∀ b, TopologicalSpace (W b)] [TopologicalSpace (TotalSpace F W)]
  [FiberBundle F W] [VectorBundle 𝕂 F W] {n : ℕ∞ω} [IsManifold J n B]
  [ContMDiffVectorBundle n F W J]

/-- The zero section of a `C^n` vector bundle with finite-dimensional fibres, over a boundaryless
manifold with finite-dimensional model, is a `C^n` smooth embedding for `1 ≤ n`: the bundle
projection is a smooth left inverse. -/
theorem isSmoothEmbedding_zeroSection (hn : 1 ≤ n) :
    Manifold.IsSmoothEmbedding J (J.prod 𝓘(𝕂, F)) n (zeroSection F W) :=
  (contMDiff_zeroSection 𝕂 W).isSmoothEmbedding_of_leftInverse hn
    ((contMDiff_proj (n := n) W).of_le hn) fun _ ↦ rfl

end Embedding

end TauCeti.Bundle
