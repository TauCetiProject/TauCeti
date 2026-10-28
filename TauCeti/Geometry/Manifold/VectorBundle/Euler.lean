/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CurveInTotalSpace
public import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The Euler vector field of a vector bundle

The fibres of a vector bundle `V → B` are vector spaces, so every vector `z` in the total space
lies on the line `t ↦ t • z` through the origin of its fibre. The velocity of that line at
`t = 1` is the **Euler vector field** (or radial vector field) of the bundle
(`TauCeti.vectorBundleEulerField`). In a bundle chart with coordinates `(x, ξ)` it is
`ξ ∂_ξ`: at `z` its coordinates are `(0, ξ)`, where `ξ` is the fibre coordinate of `z`
(`TauCeti.vectorBundleEulerField_eq_trivializationAt`). It is vertical, that is, killed by the
derivative of the projection (`TauCeti.mfderiv_proj_vectorBundleEulerField`), it vanishes along
the zero section (`TauCeti.vectorBundleEulerField_zero`), and it is smooth
(`TauCeti.contMDiff_vectorBundleEulerField`).

It is the infinitesimal generator of the fibre dilations `z ↦ c • z`
(`TauCeti.vectorBundleScalarDiffeomorph`): on a real vector bundle, the curve `t ↦ e^t • z` is an
integral curve of the Euler vector field (`TauCeti.isMIntegralCurve_vectorBundleEulerField`). On
a cotangent bundle it is the field `p ∂_p`, the Liouville vector field of the canonical symplectic
structure.

## Main declarations

* `TauCeti.vectorBundleEulerField`: the Euler vector field.
* `TauCeti.hasMFDerivAt_vectorBundleEulerField`: it is the velocity at `t = 1` of `t ↦ t • z`.
* `TauCeti.vectorBundleEulerField_eq_trivializationAt`: its coordinates in the chart at `z`.
* `TauCeti.mfderiv_proj_vectorBundleEulerField`: it is vertical.
* `TauCeti.contMDiff_vectorBundleEulerField`: it is a smooth section of the tangent bundle of the
  total space.
* `TauCeti.isMIntegralCurve_vectorBundleEulerField`: on a real vector bundle, the curves
  `t ↦ e^t • z` are integral curves of it.

## References

* S. Lang, *Fundamentals of Differential Geometry*, Graduate Texts in Mathematics 191, Springer,
  1999, Chapter IV (sprays, and the dilations of the fibres of a vector bundle).
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

section General

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {B : Type*} [TopologicalSpace B] [ChartedSpace H B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : B → Type*} [∀ b, AddCommMonoid (V b)] [∀ b, Module 𝕜 (V b)]
  [∀ b, TopologicalSpace (V b)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

variable (I) in
/-- The **Euler vector field** of a vector bundle: at a vector `z` of the total space, the velocity
at `t = 1` of the line `t ↦ t • z` in the fibre of `z`. In a bundle chart with coordinates `(x, ξ)`
it is `ξ ∂_ξ` (`TauCeti.vectorBundleEulerField_eq_trivializationAt`). -/
def vectorBundleEulerField (z : TotalSpace F V) : TangentSpace (I.prod 𝓘(𝕜, F)) z :=
  mfderiv 𝓘(𝕜) (I.prod 𝓘(𝕜, F)) (fun t : 𝕜 ↦ (⟨z.proj, t • z.2⟩ : TotalSpace F V)) 1 (1 : 𝕜)

/-- The fibre coordinate of `c • z` is `c` times that of `z`, by linearity of the trivialization
at the base point of `z`. -/
private theorem trivializationAt_smul_snd (z : TotalSpace F V) (c : 𝕜) :
    (trivializationAt F V z.proj (⟨z.proj, c • z.2⟩ : TotalSpace F V)).2 =
      c • (trivializationAt F V z.proj z).2 :=
  ((trivializationAt F V z.proj).linear 𝕜
    (FiberBundle.mem_baseSet_trivializationAt F V z.proj)).map_smul c z.2

/-- If `f` has derivative `f'` at `t`, then the curve `r ↦ f r • z` in the fibre of `z` has
velocity `(0, f' • ξ)` at `t`, read in the chart at `z`, where `ξ` is the fibre coordinate of
`z`. -/
private theorem hasMFDerivAt_smul_curve (z : TotalSpace F V) {f : 𝕜 → 𝕜} {f' t : 𝕜}
    (hf : HasDerivAt f f' t) :
    HasMFDerivAt 𝓘(𝕜) (I.prod 𝓘(𝕜, F)) (fun r : 𝕜 ↦ (⟨z.proj, f r • z.2⟩ : TotalSpace F V)) t
      ((1 : 𝕜 →L[𝕜] 𝕜).smulRight ((0 : E), f' • (trivializationAt F V z.proj z).2)) := by
  rw [Manifold.hasMFDerivAt_totalSpace_curve_iff]
  -- Both the continuity and the derivative of the fibre coordinate reduce to those of
  -- `r ↦ f r • ξ`.
  refine ⟨(FiberBundle.continuousAt_totalSpace F _).2 ⟨continuousAt_const, ?_⟩,
    hasDerivAt_const t (extChartAt I z.proj z.proj), ?_⟩ <;>
    rw [funext fun r ↦ trivializationAt_smul_snd z (f r)]
  exacts [hf.continuousAt.smul continuousAt_const, hf.smul_const _]

/-- The line `t ↦ t • z` has velocity `(0, ξ)` at `t = 1`, read in the chart at `z`, where `ξ` is
the fibre coordinate of `z`. -/
private theorem hasMFDerivAt_smul_aux (z : TotalSpace F V) :
    HasMFDerivAt 𝓘(𝕜) (I.prod 𝓘(𝕜, F)) (fun t : 𝕜 ↦ (⟨z.proj, t • z.2⟩ : TotalSpace F V)) 1
      ((1 : 𝕜 →L[𝕜] 𝕜).smulRight ((0 : E), (trivializationAt F V z.proj z).2)) := by
  simpa only [one_smul] using hasMFDerivAt_smul_curve (I := I) z (hasDerivAt_id' (1 : 𝕜))

/-- **Chart formula for the Euler vector field.** Read in the chart at `z`, where tangent vectors
at `z` are their own coordinates, the Euler vector field at `z` is `(0, ξ)`, with `ξ` the fibre
coordinate of `z` in the trivialization at its base point. -/
theorem vectorBundleEulerField_eq_trivializationAt (z : TotalSpace F V) :
    vectorBundleEulerField I z = ((0 : E), (trivializationAt F V z.proj z).2) := by
  rw [vectorBundleEulerField, (hasMFDerivAt_smul_aux z).mfderiv]
  -- `smulRight 1 v` sends `1` to `1 • v`.
  exact one_smul 𝕜 _

/-- The Euler vector field at `z` is the velocity at `t = 1` of the line `t ↦ t • z`. -/
theorem hasMFDerivAt_vectorBundleEulerField (z : TotalSpace F V) :
    HasMFDerivAt 𝓘(𝕜) (I.prod 𝓘(𝕜, F)) (fun t : 𝕜 ↦ (⟨z.proj, t • z.2⟩ : TotalSpace F V)) 1
      ((1 : 𝕜 →L[𝕜] 𝕜).smulRight (vectorBundleEulerField I z)) := by
  rw [vectorBundleEulerField_eq_trivializationAt]
  exact hasMFDerivAt_smul_aux z

/-- The Euler vector field vanishes along the zero section. -/
@[simp]
theorem vectorBundleEulerField_zero (b : B) :
    vectorBundleEulerField I (⟨b, 0⟩ : TotalSpace F V) = 0 := by
  rw [vectorBundleEulerField_eq_trivializationAt]
  exact Prod.ext rfl (((trivializationAt F V b).linear 𝕜
    (FiberBundle.mem_baseSet_trivializationAt F V b)).map_zero)

/-- The Euler vector field is **vertical**: the derivative of the bundle projection kills it. -/
@[simp]
theorem mfderiv_proj_vectorBundleEulerField (z : TotalSpace F V) :
    mfderiv (I.prod 𝓘(𝕜, F)) I (π F V) z (vectorBundleEulerField I z) = 0 := by
  -- The projection of the line `t ↦ t • z` is the constant curve at the base point of `z`.
  have h := mfderiv_comp_apply_of_eq (1 : 𝕜) (y := z)
    ((contMDiff_proj V).mdifferentiableAt (n := 1) one_ne_zero)
    (hasMFDerivAt_vectorBundleEulerField (I := I) z).mdifferentiableAt (by simp) (1 : 𝕜)
  rw [show (π F V ∘ fun t : 𝕜 ↦ (⟨z.proj, t • z.2⟩ : TotalSpace F V)) = fun _ ↦ z.proj from rfl,
    mfderiv_const] at h
  exact h.symm

/-- **Smoothness of the Euler vector field.** The Euler vector field is a `C^m` section of the
tangent bundle of the total space, for every `m`. -/
theorem contMDiff_vectorBundleEulerField {m : ℕ∞ω}
    [IsManifold (I.prod 𝓘(𝕜, F)) 1 (TotalSpace F V)] :
    ContMDiff (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, F)).tangent m
      (fun z ↦ (⟨z, vectorBundleEulerField I z⟩ :
        TangentBundle (I.prod 𝓘(𝕜, F)) (TotalSpace F V))) := by
  -- The fibre dilation `(t, z) ↦ t • z` as a single map on `𝕜 × V`.
  let Φ : 𝕜 × TotalSpace F V → TotalSpace F V := fun p ↦ ⟨p.2.proj, p.1 • p.2.2⟩
  have hΦ : ContMDiff (𝓘(𝕜).prod (I.prod 𝓘(𝕜, F))) (I.prod 𝓘(𝕜, F)) ω Φ :=
    contMDiff_fst.smul_totalSpace contMDiff_snd
  -- The unit vector along the scalar factor, at the point `(1, z)`.
  let σ : TotalSpace F V → TangentBundle (𝓘(𝕜).prod (I.prod 𝓘(𝕜, F))) (𝕜 × TotalSpace F V) :=
    fun z ↦ (equivTangentBundleProd 𝓘(𝕜) 𝕜 (I.prod 𝓘(𝕜, F)) (TotalSpace F V)).symm
      (⟨1, (1 : 𝕜)⟩, ⟨z, 0⟩)
  have hσ : ContMDiff (I.prod 𝓘(𝕜, F)) (𝓘(𝕜).prod (I.prod 𝓘(𝕜, F))).tangent m σ :=
    contMDiff_equivTangentBundleProd_symm.comp
      (contMDiff_const.prodMk (contMDiff_zeroSection 𝕜 (TangentSpace (I.prod 𝓘(𝕜, F)))))
  refine ((hΦ.contMDiff_tangentMap le_top).comp hσ).congr fun z ↦ ?_
  simp only [Function.comp_apply, σ, tangentMap, equivTangentBundleProd_symm_apply_snd]
  rw [equivTangentBundleProd_symm_apply_proj]
  dsimp only
  -- The tangent map of the dilation sends the unit vector at `(1, z)` to the Euler field at `z`,
  -- by the chain rule along the line `t ↦ (t, z)`.
  have hline : HasMFDerivAt 𝓘(𝕜) (𝓘(𝕜).prod (I.prod 𝓘(𝕜, F))) (fun t : 𝕜 ↦ (t, z)) 1
      (ContinuousLinearMap.inl 𝕜 𝕜 (E × F)) :=
    (hasMFDerivAt_id 1).prodMk (hasMFDerivAt_const z 1)
  have hv := mfderiv_comp_apply_of_eq (1 : 𝕜) ((hΦ (1, z)).mdifferentiableAt (by simp))
    hline.mdifferentiableAt rfl (1 : 𝕜)
  rw [hline.mfderiv] at hv
  -- By definition of `Φ`, its composite with the line `t ↦ (t, z)` is the line `t ↦ t • z`,
  -- whose velocity at `t = 1` is the Euler field by definition; and `inl 1 = (1, 0)` by
  -- definition of `ContinuousLinearMap.inl`. (`rw` cannot perform these steps, because the
  -- tangent spaces involved are only definitionally equal to their model vector spaces.)
  have hE : vectorBundleEulerField I z =
      mfderiv (𝓘(𝕜).prod (I.prod 𝓘(𝕜, F))) (I.prod 𝓘(𝕜, F)) Φ (1, z) (1, 0) :=
    hv
  exact TotalSpace.ext (by simp [Φ]) (heq_of_eq hE)

end General

/-! ### The flow of the Euler vector field -/

section Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {B : Type*} [TopologicalSpace B] [ChartedSpace H B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [∀ b, AddCommMonoid (V b)] [∀ b, Module ℝ (V b)]
  [∀ b, TopologicalSpace (V b)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- **The flow of the Euler vector field is fibre dilation.** For every vector `z` of a real vector
bundle, the curve `t ↦ e^t • z` is an integral curve of the Euler vector field. -/
theorem isMIntegralCurve_vectorBundleEulerField (z : TotalSpace F V) :
    IsMIntegralCurve (fun t : ℝ ↦ (⟨z.proj, Real.exp t • z.2⟩ : TotalSpace F V))
      (vectorBundleEulerField I) := by
  intro t
  rw [vectorBundleEulerField_eq_trivializationAt]
  have h := hasMFDerivAt_smul_curve (I := I) z (Real.hasDerivAt_exp t)
  rwa [← trivializationAt_smul_snd] at h

end Real

end TauCeti
