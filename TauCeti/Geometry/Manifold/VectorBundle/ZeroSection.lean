/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import TauCeti.Geometry.Manifold.VectorBundle.CurveInTotalSpace
public import TauCeti.Topology.VectorBundle.ZeroSection

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

In the preferred charts the zero section has derivative the first summand inclusion
(`TauCeti.Bundle.hasMFDerivAt_zeroSection`), and the fibre over `b`, parametrized by the model
fibre through the trivialization at `b`, has derivative the second summand inclusion
(`TauCeti.Bundle.hasMFDerivAt_mk_trivializationAt_symm`,
`TauCeti.Bundle.mfderiv_mk_trivializationAt_symm`); it is `C^n`
(`TauCeti.Bundle.contMDiff_mk_trivializationAt_symm`). These two statements about the
parametrized fibre hold in any fibre bundle. So a map out of the total space which is `C^n` at
`0_b` is `C^n` at `0` along the fibre (`ContMDiffAt.comp_mk_trivializationAt_symm`), and if it is
differentiable at `0_b` its derivative at `0` along the fibre is its derivative on vertical
vectors (`TauCeti.Bundle.mfderiv_comp_mk_trivializationAt_symm_zero_apply`).

The horizontal computation generalizes Mathlib's
`TangentBundle.tangentMap_tangentBundle_pure`, by Sébastien Gouëzel and Floris van Doorn,
from tangent bundles to vector bundles. The vertical computation uses the scalar-curve case
`Bundle.TotalSpace.hasMFDerivAt_smul_curve` of the total-space curve criterion.

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
  {V : B → Type*} [∀ b, TopologicalSpace (V b)] [TopologicalSpace (TotalSpace F V)]

section FiberBundle

variable [∀ b, Nonempty (V b)] [FiberBundle F V]

/-- The fibre over `b`, parametrized by the model fibre through the trivialization at `b`, is
`C^n`: in that trivialization it is the identity of the model fibre. -/
theorem contMDiff_mk_trivializationAt_symm {n : WithTop ℕ∞} (b : B) :
    ContMDiff 𝓘(𝕜, F) (I.prod 𝓘(𝕜, F)) n
      (fun w : F ↦ (⟨b, (trivializationAt F V b).symm b w⟩ : TotalSpace F V)) := fun _ ↦
  contMDiffAt_totalSpace_iff.mpr ⟨contMDiffAt_const, contMDiffAt_id.congr_of_eventuallyEq
    (Eventually.of_forall fun w ↦ congrArg Prod.snd
      ((trivializationAt F V b).apply_mk_symm (mem_baseSet_trivializationAt F V b) w))⟩

/-- The fibre over `b`, parametrized by the model fibre through the trivialization at `b`, has
derivative the second summand inclusion at every point: in the preferred charts it is
`w ↦ (φ b, w)`. -/
theorem hasMFDerivAt_mk_trivializationAt_symm (b : B) (w₀ : F) :
    HasMFDerivAt 𝓘(𝕜, F) (I.prod 𝓘(𝕜, F))
      (fun w : F ↦ (⟨b, (trivializationAt F V b).symm b w⟩ : TotalSpace F V)) w₀
      (ContinuousLinearMap.inr 𝕜 (TangentSpace I b) F) := by
  -- In the preferred charts the parametrized fibre is the second summand inclusion, shifted by
  -- the chart image of `b`.
  have key : writtenInExtChartAt 𝓘(𝕜, F) (I.prod 𝓘(𝕜, F)) w₀
      (fun w : F ↦ (⟨b, (trivializationAt F V b).symm b w⟩ : TotalSpace F V)) =
        fun w ↦ (extChartAt I b b, w) := by
    funext w
    simp only [writtenInExtChartAt, Function.comp_apply, FiberBundle.extChartAt,
      extChartAt_model_space_eq_id, PartialEquiv.refl_symm, PartialEquiv.refl_coe, id_eq,
      PartialEquiv.trans_apply, PartialEquiv.prod_coe, OpenPartialHomeomorph.coe_toPartialEquiv,
      Trivialization.coe_coe,
      (trivializationAt F V b).apply_mk_symm (mem_baseSet_trivializationAt F V b)]
  refine ⟨(contMDiff_mk_trivializationAt_symm (I := I) (n := 0) b w₀).continuousAt, ?_⟩
  rw [key]
  exact ((hasFDerivAt_const _ _).prodMk (hasFDerivAt_id _)).hasFDerivWithinAt

/-- The fibre over `b`, parametrized by the model fibre through the trivialization at `b`, has
derivative the second summand inclusion at every point. -/
theorem mfderiv_mk_trivializationAt_symm (b : B) (w₀ : F) :
    mfderiv 𝓘(𝕜, F) (I.prod 𝓘(𝕜, F))
      (fun w : F ↦ (⟨b, (trivializationAt F V b).symm b w⟩ : TotalSpace F V)) w₀ =
      ContinuousLinearMap.inr 𝕜 (TangentSpace I b) F :=
  (hasMFDerivAt_mk_trivializationAt_symm b w₀).mfderiv

end FiberBundle

variable [∀ b, AddCommMonoid (V b)] [∀ b, Module 𝕜 (V b)] [FiberBundle F V] [VectorBundle 𝕜 F V]

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

/-- In preferred tangent coordinates, the zero section has derivative the first summand
inclusion. -/
theorem hasMFDerivAt_zeroSection (b : B) :
    HasMFDerivAt I (I.prod 𝓘(𝕜, F)) (zeroSection F V) b
      (ContinuousLinearMap.inl 𝕜 (TangentSpace I b) F) := by
  -- In the preferred charts the zero section is the first summand inclusion.
  have key : ∀ y ∈ (extChartAt I b).target,
      (extChartAt I b).symm y ∈ (trivializationAt F V b).baseSet →
      writtenInExtChartAt I (I.prod 𝓘(𝕜, F)) b (zeroSection F V) y =
        ContinuousLinearMap.inl 𝕜 E F y := by
    intro y hy hs
    have h0 := (trivializationAt F V b).zeroSection 𝕜 hs
    simp only [writtenInExtChartAt, Function.comp_apply, FiberBundle.extChartAt,
      PartialEquiv.trans_apply, PartialEquiv.prod_coe, PartialEquiv.refl_coe, id_eq,
      OpenPartialHomeomorph.coe_toPartialEquiv, Trivialization.coe_coe, zeroSection_proj, h0]
    exact Prod.ext ((extChartAt I b).right_inv hy) rfl
  have hb : (extChartAt I b).symm (extChartAt I b b) ∈ (trivializationAt F V b).baseSet := by
    rw [extChartAt_to_inv]
    exact mem_baseSet_trivializationAt F V b
  refine ⟨(Trivialization.continuous_zeroSection 𝕜 (E := V)).continuousAt, ?_⟩
  refine (ContinuousLinearMap.inl 𝕜 E F).hasFDerivAt.hasFDerivWithinAt.congr_of_eventuallyEq
    ?_ (key _ (mem_extChartAt_target b) hb)
  filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem (I := I) (mem_extChartAt_target b),
    nhdsWithin_le_nhds ((continuousAt_extChartAt_symm b).eventually
      ((trivializationAt F V b).open_baseSet.mem_nhds hb))] with y hy hs using key y hy hs

/-- In preferred tangent coordinates, the differential of the zero section is the first
summand inclusion. -/
theorem mfderiv_zeroSection (b : B) :
    mfderiv I (I.prod 𝓘(𝕜, F)) (zeroSection F V) b =
      ContinuousLinearMap.inl 𝕜 (TangentSpace I b) F :=
  (hasMFDerivAt_zeroSection b).mfderiv

/-- A map out of the total space which is `C^n` at the zero vector over `b` is `C^n` at `0` along
the fibre over `b`, parametrized by the model fibre through the trivialization at `b`. -/
theorem _root_.ContMDiffAt.comp_mk_trivializationAt_symm {E' H' M : Type*}
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    [TopologicalSpace M] [ChartedSpace H' M] {n : WithTop ℕ∞} {Φ : TotalSpace F V → M} {b : B}
    (hΦ : ContMDiffAt (I.prod 𝓘(𝕜, F)) I' n Φ (zeroSection F V b)) :
    ContMDiffAt 𝓘(𝕜, F) I' n (fun w : F ↦ Φ ⟨b, (trivializationAt F V b).symm b w⟩) 0 :=
  ((mk_trivializationAt_symm_zero (F := F) (E := V) 𝕜 b).symm ▸ hΦ).comp 0
    (contMDiff_mk_trivializationAt_symm b 0)

/-- Along the fibre over `b`, parametrized by the model fibre through the trivialization at `b`, a
map out of the total space which is differentiable at the zero vector over `b` has derivative at
`0` the derivative of the map on vertical vectors. -/
theorem mfderiv_comp_mk_trivializationAt_symm_zero_apply {E' H' M : Type*}
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    [TopologicalSpace M] [ChartedSpace H' M] {Φ : TotalSpace F V → M} {b : B}
    (hΦ : MDifferentiableAt (I.prod 𝓘(𝕜, F)) I' Φ (zeroSection F V b)) (w : F) :
    mfderiv 𝓘(𝕜, F) I' (fun w : F ↦ Φ ⟨b, (trivializationAt F V b).symm b w⟩) 0 w =
      mfderiv (I.prod 𝓘(𝕜, F)) I' Φ (zeroSection F V b) (0, w) := by
  have h0 := mk_trivializationAt_symm_zero (F := F) (E := V) 𝕜 b
  have hd := hasMFDerivAt_mk_trivializationAt_symm (I := I) (F := F) (V := V) b 0
  rw [← h0] at hΦ ⊢
  exact congrArg (· w) ((hΦ.hasMFDerivAt.comp 0 hd).mfderiv)

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
