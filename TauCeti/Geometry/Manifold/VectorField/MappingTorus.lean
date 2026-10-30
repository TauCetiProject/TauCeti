/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Interior
public import TauCeti.Geometry.Manifold.DifferentialForm.MappingTorus

/-!
# The suspension vector field of a smooth mapping torus

Let `φ : M ≃ₘ⟮I, I⟯ M` be a diffeomorphism of a locally compact Hausdorff smooth manifold and
`Y_φ = (ℝ × M) / ((t, x) ∼ (t + 1, φ⁻¹ x))` its smooth mapping torus
(`TauCeti.SmoothMappingTorus φ`), with projection `p : Y_φ → ℝ / ℤ`, `[t, x] ↦ [t]`, and
suspension flow `[t, x] ↦ [t + s, x]`. This file constructs the vector field `T = ∂_t` of `Y_φ`,
the descent of the coordinate field `∂_t` of `ℝ × M`, and splits each tangent space of `Y_φ` as
`T Y_φ = ℝ T ⊕ V` into the line spanned by `T` and the vertical tangent space `V = ker dp`.

The field `T` (`TauCeti.SmoothMappingTorus.timeVectorField φ`) is defined as the velocity at time
zero of the suspension flow. So it is intrinsic to `Y_φ`, and no choice of representative `(t, x)`
enters its definition. Through the local diffeomorphism `(t, x) ↦ [t, x]` it is the image of the
unit vector `(1, 0)` of `ℝ × M` (`TauCeti.SmoothMappingTorus.timeVectorField_mk`). It is a smooth
section of the tangent bundle, and the orbits of the suspension flow are integral curves of `T`
defined for all time.

The time form `dt` is the differential of the projection `p`, read in the real tangent lines of
the circle (`TauCeti.SmoothMappingTorus.timeForm_apply`), and the field `T` is dual to it:
`dt(T) = dp(T) = 1`. At `[t, x]` the vertical tangent space `ker dp` is the tangent space of the
fiber, the image of the differential of the inclusion `x ↦ [t, x]`
(`TauCeti.SmoothMappingTorus.range_mfderiv_mk`). Finally, `T` is in the kernel of every fiber
form: `ι_T σ_v = 0` for every form `σ` on `M` preserved by `φ`.

## Main definitions

* `TauCeti.SmoothMappingTorus.timeVectorField φ`: the vector field `T = ∂_t` of the mapping torus.

## Main results

* `TauCeti.SmoothMappingTorus.timeVectorField_mk`: at `[t, x]`, `T` is the image of the unit
  vector `(1, 0)` of `ℝ × M` under the differential of `(t, x) ↦ [t, x]`.
* `TauCeti.SmoothMappingTorus.contMDiff_timeVectorField`: `T` is a smooth vector field.
* `TauCeti.SmoothMappingTorus.isMIntegralCurve_flow`: the orbits of the suspension flow are
  integral curves of `T`.
* `TauCeti.SmoothMappingTorus.timeForm_timeVectorField`,
  `TauCeti.SmoothMappingTorus.mfderiv_proj_timeVectorField`: `dt(T) = 1` and `dp(T) = 1`.
* `TauCeti.SmoothMappingTorus.isCompl_span_timeVectorField_ker_mfderiv_proj`: the splitting
  `T Y_φ = ℝ T ⊕ ker dp`.
* `TauCeti.SmoothMappingTorus.mfderiv_map_timeVectorField`: the map `[t, x] ↦ [t, g x]` induced
  by a smooth map `g` intertwining `φ` and `ψ` sends the field `T` of `Y_φ` to that of `Y_ψ`.
* `TauCeti.SmoothMappingTorus.interior_timeVectorField_fiberForm`,
  `TauCeti.SmoothMappingTorus.fiberForm_apply_vecCons_timeVectorField`,
  `TauCeti.SmoothMappingTorus.eval₂_fiberForm_timeVectorField_left`: `ι_T σ_v = 0`.

## References

* Michael Hutchings and Michael Sullivan, *The periodic Floer homology of a Dehn twist*, Algebraic
  & Geometric Topology 5 (2005), 301–354 (the vector field `∂_t` of a mapping torus and the
  kernel of its fiber form).
-/

public section

noncomputable section

open Bundle Set Function
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothMappingTorus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M]
  (φ : M ≃ₘ⟮I, I⟯ M)

/-- The vector field `T = ∂_t` of the mapping torus `Y_φ`: its value at `y` is the velocity at
time zero of the orbit `s ↦ [t + s, x]` of the suspension flow through `y = [t, x]`. At `[t, x]`
it is the image of the unit vector `(1, 0)` of `ℝ × M` under the differential of
`(t, x) ↦ [t, x]` (`TauCeti.SmoothMappingTorus.timeVectorField_mk`). -/
def timeVectorField (y : SmoothMappingTorus φ) : TangentSpace (𝓘(ℝ).prod I) y :=
  mfderiv 𝓘(ℝ) (𝓘(ℝ).prod I) (fun s : ℝ ↦ flow φ s y) 0 (1 : ℝ)

omit [IsManifold I ∞ M] in
/-- The field `T` at `y` is the velocity at time zero of the suspension flow through `y`. -/
theorem timeVectorField_def (y : SmoothMappingTorus φ) :
    timeVectorField φ y = mfderiv 𝓘(ℝ) (𝓘(ℝ).prod I) (fun s : ℝ ↦ flow φ s y) 0 (1 : ℝ) :=
  (rfl)

/-- The orbit `r ↦ [t + r, x]` of the suspension flow through `[t, x]` has velocity at `s` the
image of the unit vector `(1, 0)` at `(t + s, x)` under the differential of `(t, x) ↦ [t, x]`. -/
private theorem hasMFDerivAt_flow_mk (t : ℝ) (x : M) (s : ℝ) :
    HasMFDerivAt 𝓘(ℝ) (𝓘(ℝ).prod I) (fun r : ℝ ↦ flow φ r (mk φ t x)) s
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t + s, x)
          ((Manifold.tangentSpaceProdEquiv (t + s, x)).symm (1, 0)))) := by
  -- The curve `r ↦ (t + r, x)` of `ℝ × M` has velocity `(1, 0)`.
  have hadd : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ) (fun r : ℝ ↦ t + r) s (ContinuousLinearMap.id ℝ ℝ) :=
    hasMFDerivAt_iff_hasFDerivAt.2 ((hasFDerivAt_id s).const_add t)
  have hline : HasMFDerivAt 𝓘(ℝ) (𝓘(ℝ).prod I) (fun r : ℝ ↦ (t + r, x)) s
      ((ContinuousLinearMap.id ℝ ℝ).prod 0) :=
    hadd.prodMk (hasMFDerivAt_const (I := 𝓘(ℝ)) x s)
  have h := ((contMDiff_uncurry_mk φ (t + s, x)).mdifferentiableAt (by simp)).hasMFDerivAt.comp
    s hline
  refine (h.congr_of_eventuallyEq_abuse
    (Filter.Eventually.of_forall fun r ↦ flow_mk φ r t x)).congr_mfderiv ?_
  refine ContinuousLinearMap.ext_ring ?_
  rw [Manifold.tangentSpaceProdEquiv_symm_apply]
  -- Both sides send `1` to the differential of `(t, x) ↦ [t, x]` applied to `(1, 0)`.
  exact (one_smul ℝ _).symm

/-- At `[t, x]`, the field `T` is the image of the unit vector `(1, 0)` of `ℝ × M` under the
differential of `(t, x) ↦ [t, x]`. -/
theorem timeVectorField_mk (t : ℝ) (x : M) :
    timeVectorField φ (mk φ t x) =
      mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
        ((Manifold.tangentSpaceProdEquiv (t, x)).symm (1, 0)) := by
  rw [timeVectorField_def, (hasMFDerivAt_flow_mk φ t x 0).mfderiv]
  -- `smulRight 1 v` sends `1` to `1 • v`.
  refine (one_smul ℝ _).trans ?_
  rw [add_zero]

/-- The orbits of the suspension flow are integral curves of the field `T`, defined for all
time. -/
theorem isMIntegralCurve_flow (y : SmoothMappingTorus φ) :
    IsMIntegralCurve (fun s ↦ flow φ s y) (timeVectorField φ) := by
  obtain ⟨⟨t, x⟩, rfl⟩ := uncurry_mk_surjective φ y
  intro s
  have hT : timeVectorField φ (flow φ s (mk φ t x)) =
      mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t + s, x)
        ((Manifold.tangentSpaceProdEquiv (t + s, x)).symm (1, 0)) := by
    rw [flow_mk, timeVectorField_mk]
  rw [uncurry_apply_pair, hT]
  exact hasMFDerivAt_flow_mk φ t x s

/-- The field `T` is a smooth section of the tangent bundle of the mapping torus. -/
theorem contMDiff_timeVectorField :
    ContMDiff (𝓘(ℝ).prod I) (𝓘(ℝ).prod I).tangent ∞
      (fun y ↦
        (⟨y, timeVectorField φ y⟩ : TangentBundle (𝓘(ℝ).prod I) (SmoothMappingTorus φ))) := by
  -- This argument follows the proof of `TauCeti.contMDiff_vectorBundleEulerField` in
  -- `TauCeti/Geometry/Manifold/VectorBundle/Euler.lean`, with the suspension flow in place of the
  -- fibre dilation.
  -- The unit vector along the time factor, at the point `(0, y)` of `ℝ × Y_φ`.
  let σ : SmoothMappingTorus φ →
      TangentBundle (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (ℝ × SmoothMappingTorus φ) :=
    fun y ↦ (equivTangentBundleProd 𝓘(ℝ) ℝ (𝓘(ℝ).prod I) (SmoothMappingTorus φ)).symm
      (⟨0, (1 : ℝ)⟩, ⟨y, 0⟩)
  have hσ : ContMDiff (𝓘(ℝ).prod I) (𝓘(ℝ).prod (𝓘(ℝ).prod I)).tangent ∞ σ :=
    contMDiff_equivTangentBundleProd_symm.comp
      (contMDiff_const.prodMk (contMDiff_zeroSection ℝ (TangentSpace (𝓘(ℝ).prod I))))
  refine (((contMDiff_uncurry_flow φ).contMDiff_tangentMap le_rfl).comp hσ).congr fun y ↦ ?_
  simp only [Function.comp_apply, σ, tangentMap, equivTangentBundleProd_symm_apply_snd]
  rw [equivTangentBundleProd_symm_apply_proj]
  dsimp only
  -- The tangent map of the flow sends the unit vector at `(0, y)` to `T y`, by the chain rule
  -- along the line `s ↦ (s, y)`.
  have hline : HasMFDerivAt 𝓘(ℝ) (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (fun s : ℝ ↦ (s, y)) 0
      (ContinuousLinearMap.inl ℝ ℝ (ℝ × E)) :=
    (hasMFDerivAt_id 0).prodMk (hasMFDerivAt_const y 0)
  have hv := mfderiv_comp_apply_of_eq (0 : ℝ)
    (((contMDiff_uncurry_flow φ) (0, y)).mdifferentiableAt (by simp)) hline.mdifferentiableAt rfl
    (1 : ℝ)
  rw [hline.mfderiv] at hv
  -- By definition, the flow composed with `s ↦ (s, y)` is the orbit `s ↦ flow φ s y`, and
  -- `inl 1 = (1, 0)`. (`rw` cannot perform these steps, because the tangent spaces involved are
  -- only definitionally equal to their model vector spaces.)
  have hT : timeVectorField φ y =
      mfderiv (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (𝓘(ℝ).prod I) (uncurry (flow φ)) (0, y) (1, 0) :=
    hv
  exact TotalSpace.ext (by simp) (heq_of_eq hT)

/-! ### The time form and the vertical bundle -/

/-- The field `T` is dual to the time form: `dt(T) = 1`. -/
@[simp]
theorem timeForm_timeVectorField (y : SmoothMappingTorus φ) :
    (timeForm φ).1 y ![timeVectorField φ y] = 1 := by
  obtain ⟨⟨t, x⟩, rfl⟩ := uncurry_mk_surjective φ y
  rw [uncurry_apply_pair, timeVectorField_mk, timeForm_apply_mfderiv_uncurry_mk,
    ContinuousLinearEquiv.apply_symm_apply]
  -- The real component of `(1, 0)` is `1`.
  rfl

/-- The projection to the circle has derivative `1` along the field `T`: `dp(T) = 1`. -/
@[simp]
theorem mfderiv_proj_timeVectorField (y : SmoothMappingTorus φ) :
    mfderiv (𝓘(ℝ).prod I) 𝓘(ℝ) (proj φ) y (timeVectorField φ y) = (1 : ℝ) := by
  have h := timeForm_apply φ y ![timeVectorField φ y]
  rw [timeForm_timeVectorField] at h
  -- `![T y] 0` is `T y`.
  exact h.symm

/-- The splitting `T Y_φ = ℝ T ⊕ V` of the tangent space of the mapping torus into the line
spanned by the field `T` and the vertical tangent space `V = ker dp`. -/
theorem isCompl_span_timeVectorField_ker_mfderiv_proj (y : SmoothMappingTorus φ) :
    IsCompl (ℝ ∙ timeVectorField φ y)
      (mfderiv (𝓘(ℝ).prod I) 𝓘(ℝ) (proj φ) y).ker := by
  -- The differential of the projection, read as a real linear form: tangent vectors of the
  -- circle are real numbers.
  let f : TangentSpace (𝓘(ℝ).prod I) y →L[ℝ] ℝ := mfderiv (𝓘(ℝ).prod I) 𝓘(ℝ) (proj φ) y
  have hT : f (timeVectorField φ y) = 1 := mfderiv_proj_timeVectorField φ y
  suffices h : IsCompl (ℝ ∙ timeVectorField φ y) f.ker from h
  refine ⟨Submodule.disjoint_def.2 fun w hw hw' ↦ ?_, codisjoint_iff.2 ?_⟩
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_smul, hT, smul_eq_mul,
      mul_one] at hw'
    rw [hw', zero_smul]
  · exact LinearMap.span_singleton_sup_ker_eq_top f.toLinearMap
      (by rw [f.coe_coe, hT]; exact one_ne_zero)

/-! ### Maps of mapping tori -/

/-- The map `[t, x] ↦ [t, g x]` induced by a smooth map `g` intertwining `φ` and `ψ` sends the
field `T` of `Y_φ` to the field `T` of `Y_ψ`, because it intertwines the suspension flows. -/
@[simp]
theorem mfderiv_map_timeVectorField {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} {N : Type*}
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]
    [LocallyCompactSpace N] (ψ : N ≃ₘ⟮J, J⟯ N) {g : M → N} (h : Function.Semiconj g φ ψ)
    (hg : ContMDiff I J ∞ g) (y : SmoothMappingTorus φ) :
    mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod J) (map φ ψ g h) y (timeVectorField φ y) =
      timeVectorField ψ (map φ ψ g h y) := by
  have hcurve : (fun s : ℝ ↦ flow ψ s (map φ ψ g h y)) = map φ ψ g h ∘ fun s ↦ flow φ s y :=
    funext fun s ↦ (map_flow φ ψ g h s y).symm
  have hflow : ContMDiff 𝓘(ℝ) (𝓘(ℝ).prod I) ∞ fun s : ℝ ↦ flow φ s y :=
    (contMDiff_uncurry_flow φ).comp (contMDiff_id.prodMk contMDiff_const)
  rw [timeVectorField_def, timeVectorField_def, hcurve]
  -- The chain rule along the orbit `s ↦ flow φ s y`, which passes through `y` at time zero.
  exact (mfderiv_comp_apply_of_eq (0 : ℝ)
    ((contMDiff_map φ ψ g h hg _).mdifferentiableAt (by simp))
    ((hflow 0).mdifferentiableAt (by simp)) ((flow φ).map_zero_apply y) (1 : ℝ)).symm

/-! ### Fiber forms -/

/-- The field `T` lies in the kernel of every fiber form: `ι_T σ_v = 0` for every form `σ` on
`M` preserved by `φ`. -/
@[simp]
theorem interior_timeVectorField_fiberForm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ} {σ : SmoothForm I M F (k + 1)} {hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ} :
    (fiberForm φ σ hσ).1.interior (timeVectorField φ) = 0 := by
  -- The unit vector field `(1, 0)` of `ℝ × M`, related to `T` by `(t, x) ↦ [t, x]` and to the zero
  -- field of `M` by the second projection.
  let X : (p : ℝ × M) → TangentSpace (𝓘(ℝ).prod I) p :=
    fun p ↦ (Manifold.tangentSpaceProdEquiv p).symm (1, 0)
  refine (isLocalDiffeomorph_uncurry_mk φ).mpullback_injective (by simp)
    (uncurry_mk_surjective φ) ?_
  rw [mpullback_interior _ X _ _ fun p ↦ (timeVectorField_mk φ p.1 p.2).symm,
    ← SmoothForm.coe_mpullback _ (contMDiff_uncurry_mk φ), mpullback_uncurry_mk_fiberForm,
    SmoothForm.coe_mpullback, ← mpullback_interior _ X 0 _ fun p ↦ by
      rw [mfderiv_snd]
      exact congrArg Prod.snd
        (Manifold.tangentSpaceProdEquiv_symm_apply p ((1 : ℝ), (0 : TangentSpace I p.2))),
    RoughForm.interior_zero_field, mpullback_zero, mpullback_zero]

/-- A fiber form vanishes whenever `T` fills its first slot:
`σ_v(T, v₁, …, v_k) = 0` for every form `σ` on `M` preserved by `φ`. -/
@[simp]
theorem fiberForm_apply_vecCons_timeVectorField {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {k : ℕ} {σ : SmoothForm I M F (k + 1)}
    {hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ} (y : SmoothMappingTorus φ)
    (v : Fin k → TangentSpace (𝓘(ℝ).prod I) y) :
    (fiberForm φ σ hσ).1 y (Matrix.vecCons (timeVectorField φ y) v) = 0 := by
  rw [← RoughForm.interior_apply, interior_timeVectorField_fiberForm]
  rfl

/-- The field `T` lies in the kernel of the fiber form of every two-form `σ` preserved by `φ`:
`σ_v(T, w) = 0`. -/
theorem eval₂_fiberForm_timeVectorField_left {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {σ : SmoothForm I M F 2} {hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ}
    (y : SmoothMappingTorus φ) (w : TangentSpace (𝓘(ℝ).prod I) y) :
    (fiberForm φ σ hσ).eval₂ y (timeVectorField φ y) w = 0 := by
  simp

end SmoothMappingTorus

end TauCeti
