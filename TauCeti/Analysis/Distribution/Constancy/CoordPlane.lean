/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.CubicalGrid
public import TauCeti.Analysis.Distribution.TestFunction.IntegrationCurrent
public import TauCeti.Analysis.Distribution.Mass.Basic
import TauCeti.Analysis.Distribution.Constancy.Basic
import TauCeti.Analysis.Distribution.Mass.IntegrationCurrent
import TauCeti.Analysis.Distribution.Mass.SmulLeft
import TauCeti.Analysis.Distribution.Mass.Support
import TauCeti.Analysis.Distribution.Pushforward
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Distribution.TestFunction.TopDegree
import TauCeti.Analysis.Normed.Module.Alternating.TopDegree

/-!
# The constancy theorem for normal currents in a coordinate plane

For an injection `I : Fin k ↪ Fin n` and a point `x ∈ ℝⁿ`, the coordinate `k`-plane through `x`
spanned by `e_{I 0}, …, e_{I (k-1)}` is parametrized by the isometric embedding
`TauCeti.coordPlaneMap I x : ℝᵏ → ℝⁿ`. On an open set `U ⊆ ℝⁿ` its oriented current
`TauCeti.coordPlaneCurrent I x U` integrates the coefficient `ω y (e_{I 0}, …, e_{I (k-1)})` of a
test `k`-form over the part of the plane in `U`. It has locally finite mass, no boundary in `U`,
and support in the plane.

This file proves the **constancy theorem for currents supported in a plane**: a `(k + 1)`-current
`T` on `U` of locally finite mass, with zero boundary in `U` and supported in `U` in the coordinate
plane, is a unique real multiple of the current of the plane, provided the part of the plane in
`U` is connected. Unlike the constancy theorem for top-degree currents
(`Orientation.existsUnique_eq_smul_integrationCurrent_of_comp_extDerivCLM_eq_zero`), this needs the
locally finite mass: in `ℝ²` the current `f dx + g dy ↦ ∫ ∂_y f (t, 0) dt` has zero boundary and is
supported on the first axis, but it is not a multiple of the current of the axis.

The proof has two steps.

* **Tangency.** If `T` and `∂T` have locally finite mass and `T` is supported in the plane, then
  `T ω` only depends on the coefficients `ω y (e_{I 0}, …, e_{I k})` at the points `y` of the
  support of `T` (`Distribution.HasLocallyFiniteMass.map_eq_map_of_forall_apply_single_eq`). For
  each coordinate `m` normal to the plane, `T` is supported in the hyperplane `{y_m = x_m}`, so it
  does not change when its test forms are pulled back by the projection killing `e_m`
  (`Distribution.HasLocallyFiniteMass.map_postcompCLM_compContinuousLinearMapCLM_id_sub_smulRight`).
  Once all normal coordinates are killed, a `(k + 1)`-form is its coefficient times the coordinate
  form `dx^I`, and a current of locally finite mass only sees the values of a test form on its
  support (`Distribution.HasLocallyFiniteMass.map_eq_map_of_eqOn_dsupport`).
* **Constancy.** The scalar distribution `g ↦ T (g dx^I)` is supported in the plane, so it can be
  pushed forward to the plane along the affine projection onto the coordinates indexed by `I`
  (`Distribution.pushforward`). For a direction `y` of the plane, Cartan's formula
  `∂_y g dx^I = d (g ι_y dx^I) + ι_y d (g dx^I)`
  (`TestFunction.extDerivCLM_postcompCLM_toSpanSingleton_curryLeft_add`), the boundary condition
  and tangency show that the pushforward has vanishing derivatives. On the connected part of the
  plane in `U` it is therefore integration against a constant `c`
  (`Distribution.existsUnique_eq_ofFun_const_of_forall_lineDerivOp_eq_zero`), and tangency gives
  `T = c • TauCeti.coordPlaneCurrent I x U`.

In the deformation theorem of Federer and Fleming, this identifies a normal current supported in
the `k`-skeleton of a cubical grid, with boundary in the `(k - 1)`-skeleton, near the interior of
each `k`-face, as a real multiple of that face.

## Main declarations

* `TauCeti.coordPlaneCurrent I x U`: the oriented current of a coordinate plane, with its value
  `TauCeti.coordPlaneCurrent_apply`, restriction `TauCeti.coordPlaneCurrent_monoCLM`, zero
  boundary `TauCeti.coordPlaneCurrent_comp_extDerivCLM`,
  support `TauCeti.dsupport_coordPlaneCurrent_subset`, locally finite mass
  `TauCeti.hasLocallyFiniteMass_coordPlaneCurrent` and nonvanishing
  `TauCeti.coordPlaneCurrent_ne_zero`.
* `Distribution.HasLocallyFiniteMass.map_eq_map_of_forall_apply_single_eq`: normal currents in a
  coordinate plane are tangent to it.
* `TauCeti.existsUnique_eq_smul_coordPlaneCurrent_of_comp_extDerivCLM_eq_zero`: the constancy
  theorem.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.31 (the constancy theorem for currents supported in
  an affine subspace).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §2 (the constancy theorem) and
  §4 (the deformation theorem).
-/

public section

open MeasureTheory Set TopologicalSpace TestFunction Distribution WithLp LineDeriv Filter
open scoped Distributions Topology

namespace TauCeti

variable {k n : ℕ}

section CoordPlaneCurrent

/-- The **oriented current of a coordinate plane** in an open set `U ⊆ ℝⁿ`: the `k`-current on
test `k`-forms on `U` integrating the coefficient of a form on `e_{I 0}, …, e_{I (k-1)}` over the
plane `s ↦ x + ∑ⱼ sⱼ e_{I j}` (`TauCeti.coordPlaneCurrent_apply`). It is the pushforward along
`TauCeti.coordPlaneMap I x` of the integration current of `ℝᵏ` with its standard orientation, so it
is the integration current of the part of the plane in `U`, oriented by `e_{I 0}, …, e_{I (k-1)}`.
-/
noncomputable def coordPlaneCurrent (I : Fin k ↪ Fin n) (x : EuclideanSpace ℝ (Fin n))
    (U : Opens (EuclideanSpace ℝ (Fin n))) :
    𝓓(U, EuclideanSpace ℝ (Fin n) [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ :=
  (EuclideanSpace.basisFun (Fin k) ℝ).toBasis.orientation.integrationCurrent ⊤ ∘L
    pullbackCLM (coordPlaneMap I x) (coordPlaneMap I x).contDiff.contDiffOn
      (fun _ hK _ ↦ isCompact_inter_preimage_coordPlaneMap I x hK)

/-- The current of a coordinate plane is the pushforward of the integration current of `ℝᵏ`
along `TauCeti.coordPlaneMap I x`. -/
theorem coordPlaneCurrent_def (I : Fin k ↪ Fin n) (x : EuclideanSpace ℝ (Fin n))
    (U : Opens (EuclideanSpace ℝ (Fin n))) :
    coordPlaneCurrent I x U =
      (EuclideanSpace.basisFun (Fin k) ℝ).toBasis.orientation.integrationCurrent ⊤ ∘L
        pullbackCLM (coordPlaneMap I x) (coordPlaneMap I x).contDiff.contDiffOn
          (fun _ hK _ ↦ isCompact_inter_preimage_coordPlaneMap I x hK) :=
  (rfl)

/-- The current of a coordinate plane integrates the coefficient of a test form on
`e_{I 0}, …, e_{I (k-1)}` over the plane. -/
theorem coordPlaneCurrent_apply (I : Fin k ↪ Fin n) (x : EuclideanSpace ℝ (Fin n))
    (U : Opens (EuclideanSpace ℝ (Fin n))) (ω : 𝓓(U, EuclideanSpace ℝ (Fin n) [⋀^Fin k]→L[ℝ] ℝ)) :
    coordPlaneCurrent I x U ω =
      ∫ s, ω (coordPlaneMap I x s) fun j ↦ EuclideanSpace.single (I j) 1 := by
  rw [coordPlaneCurrent, ContinuousLinearMap.comp_apply,
    Orientation.integrationCurrent_apply_eq_integral_volume _ (EuclideanSpace.basisFun (Fin k) ℝ)
      rfl]
  congr 1
  funext s
  rw [pullbackCLM_apply_of_mem _ (Opens.mem_top _), ContinuousAffineMap.fderiv,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  simp only [Function.comp_def, EuclideanSpace.basisFun_apply, contLinear_coordPlaneMap_single]

/-- The current of a coordinate plane is compatible with restriction: on a test form extended by
zero from a smaller open set `U'`, the current of the plane in `U` is the current of the plane in
`U'`. -/
@[simp]
theorem coordPlaneCurrent_monoCLM (I : Fin k ↪ Fin n) (x : EuclideanSpace ℝ (Fin n))
    {U U' : Opens (EuclideanSpace ℝ (Fin n))} (h : U' ≤ U)
    (ω : 𝓓(U', EuclideanSpace ℝ (Fin n) [⋀^Fin k]→L[ℝ] ℝ)) :
    coordPlaneCurrent I x U (monoCLM ℝ ω : 𝓓(U, EuclideanSpace ℝ (Fin n) [⋀^Fin k]→L[ℝ] ℝ)) =
      coordPlaneCurrent I x U' ω := by
  simp [coordPlaneCurrent_apply, monoCLM_apply, h]

/-- **The current of a coordinate plane has no boundary** in `U`. -/
@[simp]
theorem coordPlaneCurrent_comp_extDerivCLM (I : Fin (k + 1) ↪ Fin n)
    (x : EuclideanSpace ℝ (Fin n)) (U : Opens (EuclideanSpace ℝ (Fin n))) :
    coordPlaneCurrent I x U ∘L extDerivCLM = 0 := by
  rw [coordPlaneCurrent, ContinuousLinearMap.comp_pullbackCLM_comp_extDerivCLM,
    Orientation.integrationCurrent_comp_extDerivCLM, ContinuousLinearMap.zero_comp]

/-- The current of a coordinate plane is supported in the plane. -/
theorem dsupport_coordPlaneCurrent_subset (I : Fin k ↪ Fin n) (x : EuclideanSpace ℝ (Fin n))
    (U : Opens (EuclideanSpace ℝ (Fin n))) :
    dsupport (coordPlaneCurrent I x U :
        𝓓(U, EuclideanSpace ℝ (Fin n) [⋀^Fin k]→L[ℝ] ℝ) → ℝ) ⊆ range (coordPlaneMap I x) := by
  rw [coordPlaneCurrent, ContinuousLinearMap.coe_comp]
  refine (dsupport_comp_pullbackCLM_subset _).trans ?_
  rw [(isometry_coordPlaneMap I x).isClosedEmbedding.isClosed_range.closure_subset_iff]
  exact image_subset_range _ _

/-- The current of a coordinate plane has locally finite mass. -/
theorem hasLocallyFiniteMass_coordPlaneCurrent (I : Fin k ↪ Fin n)
    (x : EuclideanSpace ℝ (Fin n)) (U : Opens (EuclideanSpace ℝ (Fin n))) :
    HasLocallyFiniteMass (coordPlaneCurrent I x U) :=
  (Orientation.hasLocallyFiniteMass_integrationCurrent _ ⊤).comp_pullbackCLM

end CoordPlaneCurrent

section Tangency

/-- The coordinate projection `v ↦ (v (I j))ⱼ`, a left inverse of the linear part of
`TauCeti.coordPlaneMap I x`. -/
private noncomputable def coordProj (I : Fin k ↪ Fin n) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
  (EuclideanSpace.equiv (Fin k) ℝ).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun j ↦ EuclideanSpace.proj (I j)

private theorem coordProj_apply (I : Fin k ↪ Fin n) (v : EuclideanSpace ℝ (Fin n)) (j : Fin k) :
    coordProj I v j = v (I j) := by
  simp [coordProj]

private theorem coordProj_contLinear_coordPlaneMap (I : Fin k ↪ Fin n)
    (x : EuclideanSpace ℝ (Fin n)) (s : EuclideanSpace ℝ (Fin k)) :
    coordProj I ((coordPlaneMap I x).contLinear s) = s := by
  ext j
  simp [coordProj_apply, contLinear_coordPlaneMap, I.injective.extend_apply]

/-- The coordinate `k`-form `dx^I`: the determinant of the coordinates indexed by `I`. -/
private noncomputable def coordForm (I : Fin k ↪ Fin n) :
    EuclideanSpace ℝ (Fin n) [⋀^Fin k]→L[ℝ] ℝ :=
  (EuclideanSpace.basisFun (Fin k) ℝ).toBasis.continuousDet.compContinuousLinearMap (coordProj I)

private theorem coordForm_apply_single (I : Fin k ↪ Fin n) :
    coordForm I (fun j ↦ EuclideanSpace.single (I j) 1) = 1 := by
  have h : (coordProj I ∘ fun j ↦ EuclideanSpace.single (I j) (1 : ℝ)) =
      (EuclideanSpace.basisFun (Fin k) ℝ).toBasis := by
    funext j
    ext i
    simp [coordProj_apply, I.injective.eq_iff, eq_comm]
  rw [coordForm, ContinuousAlternatingMap.compContinuousLinearMap_apply, h,
    Module.Basis.continuousDet_apply, Module.Basis.det_self]

/-- The linear map zeroing the coordinates indexed by `S`. -/
private noncomputable def zeroCoords (S : Finset (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  .id ℝ _ - ∑ m ∈ S, (EuclideanSpace.proj m).smulRight (EuclideanSpace.single m (1 : ℝ))

private theorem zeroCoords_apply (S : Finset (Fin n)) (v : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    zeroCoords S v i = if i ∈ S then 0 else v i := by
  by_cases hi : i ∈ S <;>
    simp [zeroCoords, hi, Pi.single_apply, Finset.sum_apply]

private theorem zeroCoords_insert {m : Fin n} {S : Finset (Fin n)} (hm : m ∉ S) :
    zeroCoords (insert m S) = zeroCoords S ∘L
      (.id ℝ _ - (EuclideanSpace.proj m).smulRight (EuclideanSpace.single m (1 : ℝ))) := by
  ext v i
  by_cases him : i = m
  · subst him
    simp [zeroCoords_apply, hm]
  · simp [zeroCoords_apply, him]

private theorem contLinear_coordPlaneMap_comp_coordProj (I : Fin k ↪ Fin n)
    (x : EuclideanSpace ℝ (Fin n)) :
    (coordPlaneMap I x).contLinear ∘L coordProj I =
      zeroCoords (Finset.univ.filter (· ∉ range I)) := by
  ext v i
  by_cases hi : i ∈ range I
  · obtain ⟨j, rfl⟩ := hi
    simp [zeroCoords_apply, contLinear_coordPlaneMap, I.injective.extend_apply, coordProj_apply]
  · simp only [zeroCoords_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
      contLinear_coordPlaneMap, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometry.piLpExtendByZero_apply_eq_zero hi, Finset.mem_filter, Finset.mem_univ,
      hi, not_false_eq_true, and_self, ite_true]

/-- Zeroing the coordinates normal to the plane spanned by `e_{I 0}, …, e_{I (k-1)}` turns a
`k`-form into the multiple of `dx^I` by its coefficient on `e_{I 0}, …, e_{I (k-1)}`. -/
private theorem compContinuousLinearMap_zeroCoords (I : Fin k ↪ Fin n)
    (α : EuclideanSpace ℝ (Fin n) [⋀^Fin k]→L[ℝ] ℝ) :
    α.compContinuousLinearMap (zeroCoords (Finset.univ.filter (· ∉ range I))) =
      α (fun j ↦ EuclideanSpace.single (I j) 1) • coordForm I := by
  rw [← contLinear_coordPlaneMap_comp_coordProj I 0]
  ext v
  set b := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  have h := (α.compContinuousLinearMap (coordPlaneMap I 0).contLinear).apply_eq_det_mul b
    (coordProj I ∘ v)
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply] at h
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, ContinuousLinearMap.coe_comp,
    ContinuousAlternatingMap.smul_apply, coordForm, smul_eq_mul]
  have hb : (coordPlaneMap I 0).contLinear ∘ b = fun j ↦ EuclideanSpace.single (I j) 1 := by
    funext j
    simp only [Function.comp_apply, b, OrthonormalBasis.coe_toBasis,
      EuclideanSpace.basisFun_apply, contLinear_coordPlaneMap_single]
  rw [Function.comp_assoc, h, hb, mul_comm, Module.Basis.continuousDet_apply]

variable {I : Fin (k + 1) ↪ Fin n} {x : EuclideanSpace ℝ (Fin n)}
  {U : Opens (EuclideanSpace ℝ (Fin n))}
  {T : 𝓓(U, EuclideanSpace ℝ (Fin n) [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ}

/-- A normal current supported in the coordinate plane is unchanged when its test forms are
pulled back by the map zeroing some coordinates normal to the plane. -/
private theorem map_postcompCLM_zeroCoords (hT : HasLocallyFiniteMass T)
    (hdT : HasLocallyFiniteMass (T ∘L extDerivCLM))
    (hTI : (U : Set (EuclideanSpace ℝ (Fin n))) ∩ dsupport T ⊆ range (coordPlaneMap I x))
    (S : Finset (Fin n)) (hS : ∀ m ∈ S, m ∉ range I)
    (ω : 𝓓(U, EuclideanSpace ℝ (Fin n) [⋀^Fin (k + 1)]→L[ℝ] ℝ)) :
    T (postcompCLM (ContinuousAlternatingMap.compContinuousLinearMapCLM (zeroCoords S)) ω) =
      T ω := by
  induction S using Finset.induction_on generalizing ω with
  | empty =>
    congr 1
    ext y v
    simp [zeroCoords]
  | insert m S hm ih =>
    have hmI : m ∉ range I := hS m (Finset.mem_insert_self m S)
    -- The support of `T` lies in the hyperplane `{y | y m = x m}`.
    have hTm : (U : Set (EuclideanSpace ℝ (Fin n))) ∩ dsupport T ⊆
        {y | EuclideanSpace.proj m y = x m} := by
      intro y hy
      obtain ⟨s, rfl⟩ := hTI hy
      simp [coordPlaneMap_apply, Function.extend_apply' _ _ _ hmI]
    have hcomp : postcompCLM (ContinuousAlternatingMap.compContinuousLinearMapCLM
        (zeroCoords (insert m S))) ω =
        postcompCLM (ContinuousAlternatingMap.compContinuousLinearMapCLM
          (.id ℝ _ - (EuclideanSpace.proj m).smulRight (EuclideanSpace.single m (1 : ℝ))))
          (postcompCLM (ContinuousAlternatingMap.compContinuousLinearMapCLM (zeroCoords S)) ω) := by
      ext y v
      simp only [postcompCLM_apply, Function.comp_apply,
        ContinuousAlternatingMap.compContinuousLinearMapCLM_apply,
        ContinuousAlternatingMap.compContinuousLinearMap_apply, zeroCoords_insert hm,
        ContinuousLinearMap.coe_comp, Function.comp_assoc]
    rw [hcomp, hT.map_postcompCLM_compContinuousLinearMapCLM_id_sub_smulRight hdT hTm,
      ih (fun m' hm' ↦ hS m' (Finset.mem_insert_of_mem hm'))]

/-- **Normal currents in a coordinate plane are tangent to it.** Let `T` be a `(k + 1)`-current on
`U ⊆ ℝⁿ` such that `T` and `∂T` have locally finite mass, supported in `U` in the coordinate plane
through `x` spanned by `e_{I 0}, …, e_{I k}`. Then `T ω` only depends on the coefficients
`ω y (e_{I 0}, …, e_{I k})` of `ω` at the points `y` of the support of `T` in `U`. -/
theorem _root_.Distribution.HasLocallyFiniteMass.map_eq_map_of_forall_apply_single_eq
    (hT : HasLocallyFiniteMass T)
    (hdT : HasLocallyFiniteMass (T ∘L extDerivCLM))
    (hTI : (U : Set (EuclideanSpace ℝ (Fin n))) ∩ dsupport T ⊆ range (coordPlaneMap I x))
    {ω ω' : 𝓓(U, EuclideanSpace ℝ (Fin n) [⋀^Fin (k + 1)]→L[ℝ] ℝ)}
    (h : ∀ y ∈ (U : Set (EuclideanSpace ℝ (Fin n))) ∩ dsupport T,
      ω y (fun j ↦ EuclideanSpace.single (I j) 1) = ω' y (fun j ↦ EuclideanSpace.single (I j) 1)) :
    T ω = T ω' := by
  have hS : ∀ m ∈ Finset.univ.filter (· ∉ range I), m ∉ range I := fun m hm ↦
    (Finset.mem_filter.1 hm).2
  rw [← map_postcompCLM_zeroCoords hT hdT hTI _ hS ω,
    ← map_postcompCLM_zeroCoords hT hdT hTI _ hS ω']
  refine hT.map_eq_map_of_eqOn_dsupport fun y hy ↦ ?_
  simp only [postcompCLM_apply, Function.comp_apply,
    ContinuousAlternatingMap.compContinuousLinearMapCLM_apply, compContinuousLinearMap_zeroCoords,
    h y hy]

end Tangency

section Constancy

/-- The current of a coordinate plane meeting `U` is nonzero. -/
theorem coordPlaneCurrent_ne_zero {I : Fin k ↪ Fin n} {x : EuclideanSpace ℝ (Fin n)}
    {U : Opens (EuclideanSpace ℝ (Fin n))} (hU : (coordPlaneMap I x ⁻¹' U).Nonempty) :
    coordPlaneCurrent I x U ≠ 0 := by
  obtain ⟨s₀, hs₀⟩ := hU
  obtain ⟨ρ, hρ, hρ01⟩ := TestFunction.exists_eventually_eq_one (n := ⊤) (Ω := U)
    isCompact_singleton (singleton_subset_iff.2 hs₀)
  have hρ₀ : ρ (coordPlaneMap I x s₀) = 1 := hρ.self_of_nhdsSet _ rfl
  intro h
  have hzero := DFunLike.congr_fun h (postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ
    (coordForm I)) ρ)
  rw [coordPlaneCurrent_apply, zero_apply] at hzero
  simp only [postcompCLM_apply, Function.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    ContinuousAlternatingMap.smul_apply, coordForm_apply_single, smul_eq_mul, mul_one] at hzero
  refine (Continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero (x := s₀)
    (ρ.continuous.comp (coordPlaneMap I x).continuous)
    (ρ.hasCompactSupport.comp_isClosedEmbedding (isometry_coordPlaneMap I x).isClosedEmbedding)
    (fun s ↦ (hρ01 _).1) (by simp [hρ₀])).ne' hzero

variable {I : Fin (k + 1) ↪ Fin n} {x : EuclideanSpace ℝ (Fin n)}
  {U : Opens (EuclideanSpace ℝ (Fin n))}
  {T : 𝓓(U, EuclideanSpace ℝ (Fin n) [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ}

/-- The directions of a coordinate plane lie in the span of `e_{I 0}, …, e_{I (k-1)}`. -/
private theorem contLinear_coordPlaneMap_mem_span {k : ℕ} (I : Fin k ↪ Fin n)
    (x : EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin k)) :
    (coordPlaneMap I x).contLinear v ∈
      Submodule.span ℝ (range fun j ↦ EuclideanSpace.single (I j) (1 : ℝ)) := by
  refine (Submodule.mem_span_range_iff_exists_fun ℝ).2 ⟨fun j ↦ v j, ?_⟩
  conv_rhs => rw [← (EuclideanSpace.basisFun (Fin k) ℝ).toBasis.sum_repr v]
  simp [map_sum, map_smul, contLinear_coordPlaneMap_single]

/-- If `∂T = 0`, the coefficient distribution `g ↦ T (g dx^I)` of a current `T` of locally finite
mass supported in the coordinate plane has vanishing derivatives along the plane. -/
private theorem map_postcompCLM_coordForm_lineDerivOp_eq_zero (hT : HasLocallyFiniteMass T)
    (hTI : (U : Set (EuclideanSpace ℝ (Fin n))) ∩ dsupport T ⊆ range (coordPlaneMap I x))
    (hb : T ∘L extDerivCLM = 0) (v : EuclideanSpace ℝ (Fin (k + 1))) (g : 𝓓(U, ℝ)) :
    T (postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ (coordForm I))
      (∂_{(coordPlaneMap I x).contLinear v} g)) = 0 := by
  have hdT : HasLocallyFiniteMass (T ∘L extDerivCLM) := by
    simpa [hb] using hasLocallyFiniteMass_zero
  -- By Cartan's formula, `∂_y g dx^I = d (g ι_y dx^I) + ι_y d (g dx^I)`.
  rw [← extDerivCLM_postcompCLM_toSpanSingleton_curryLeft_add, map_add,
    ← ContinuousLinearMap.comp_apply T extDerivCLM, hb, zero_apply, zero_add,
    hT.map_eq_map_of_forall_apply_single_eq hdT hTI (ω' := 0) fun y _ ↦ ?_, map_zero]
  -- `ι_y d (g dx^I)` vanishes on `e_{I 0}, …, e_{I k}`, since `y` lies in their span.
  simp only [postcompCLM_apply, Function.comp_apply,
    ContinuousAlternatingMap.curryLeftFlipL_apply_apply,
    ContinuousAlternatingMap.curryLeft_apply_apply]
  refine ((extDerivCLM _ y).toAlternatingMap.map_linearDependent _ ?_).trans (by simp)
  rw [Matrix.vecCons, linearIndependent_finCons, not_and_or, not_not]
  exact .inr (contLinear_coordPlaneMap_mem_span I x v)

/-! ### The coefficient distribution and its pushforward to the plane -/

/-- The affine projection `y ↦ (y - x)_I` onto the coordinates of the plane, a left inverse of
`TauCeti.coordPlaneMap I x`. -/
private noncomputable def planeProj {k : ℕ} (I : Fin k ↪ Fin n) (x : EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin k) :=
  coordProj I (y - x)

private theorem hasFDerivAt_planeProj {k : ℕ} (I : Fin k ↪ Fin n) (x y : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (planeProj I x) (coordProj I) y := by
  have h := (coordProj I).hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const x)
  rwa [ContinuousLinearMap.comp_id] at h

private theorem contDiff_planeProj {k : ℕ} (I : Fin k ↪ Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ (⊤ : ℕ∞) (planeProj I x) :=
  (coordProj I).contDiff.comp (contDiff_id.sub contDiff_const)

@[simp]
private theorem planeProj_coordPlaneMap {k : ℕ} (I : Fin k ↪ Fin n)
    (x : EuclideanSpace ℝ (Fin n)) (s : EuclideanSpace ℝ (Fin k)) :
    planeProj I x (coordPlaneMap I x s) = s := by
  ext j
  simp [planeProj, coordPlaneMap_apply, coordProj_apply, I.injective.extend_apply]

/-- The part of the coordinate plane in `U`, in the coordinates of the plane. -/
private noncomputable def planeOpens {k : ℕ} (I : Fin k ↪ Fin n) (x : EuclideanSpace ℝ (Fin n))
    (U : Opens (EuclideanSpace ℝ (Fin n))) : Opens (EuclideanSpace ℝ (Fin k)) :=
  ⟨coordPlaneMap I x ⁻¹' U, U.isOpen.preimage (coordPlaneMap I x).continuous⟩

/-- The scalar coefficient distribution `g ↦ T (g dx^I)` of a current `T`. -/
private noncomputable def coeffDistribution
    (T : 𝓓(U, EuclideanSpace ℝ (Fin n) [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ) (I : Fin (k + 1) ↪ Fin n) :
    𝓓'(U, ℝ) :=
  ContinuousLinearMap.toUniformConvergenceCLM _ ℝ _
    (T ∘L postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ (coordForm I)))

private theorem coeffDistribution_apply (g : 𝓓(U, ℝ)) :
    coeffDistribution T I g =
      T (postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ (coordForm I)) g) :=
  (rfl)

private theorem dsupport_coeffDistribution_subset : dsupport (coeffDistribution T I) ⊆ dsupport T :=
  dsupport_comp_subset_of_tsupport_subset (T : 𝓓(U, _) → ℝ)
    (P := postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ (coordForm I))) fun g ↦ by
      rw [postcompCLM_apply]
      exact tsupport_comp_subset (map_zero _) _

/-- Over a set `K` of the plane, the support of `T` in `U` lies in the image of `K`. -/
private theorem inter_dsupport_inter_preimage_planeProj_subset
    (hTI : (U : Set (EuclideanSpace ℝ (Fin n))) ∩ dsupport T ⊆ range (coordPlaneMap I x))
    (K : Set (EuclideanSpace ℝ (Fin (k + 1)))) :
    (U : Set (EuclideanSpace ℝ (Fin n))) ∩ dsupport T ∩ planeProj I x ⁻¹' K ⊆
      coordPlaneMap I x '' K := by
  rintro y ⟨hyT, hyK⟩
  obtain ⟨s, rfl⟩ := hTI hyT
  exact ⟨_, hyK, by rw [planeProj_coordPlaneMap]⟩

private theorem isProperOnSupport_coeffDistribution
    (hTI : (U : Set (EuclideanSpace ℝ (Fin n))) ∩ dsupport T ⊆ range (coordPlaneMap I x)) :
    IsProperOnSupport (coeffDistribution T I) (planeProj I x) (planeOpens I x U) :=
  IsProperOnSupport.of_forall_subset fun K hK hKW ↦ ⟨coordPlaneMap I x '' K,
    hK.image (coordPlaneMap I x).continuous, fun _ ⟨⟨hyU, hyD⟩, hyK⟩ ↦
      inter_dsupport_inter_preimage_planeProj_subset hTI K
        ⟨⟨hyU, dsupport_coeffDistribution_subset hyD⟩, hyK⟩,
    by rintro _ ⟨s, hs, rfl⟩; exact ⟨hKW hs, by simpa using hs⟩⟩

/-- Every test function `φ` on the plane has an extension `g` to `U` agreeing with `φ` composed
with the projection to the plane near the support of `T` in `U`. -/
private theorem exists_eventuallyEq_comp_planeProj
    (hTI : (U : Set (EuclideanSpace ℝ (Fin n))) ∩ dsupport T ⊆ range (coordPlaneMap I x))
    (φ : 𝓓(planeOpens I x U, ℝ)) :
    ∃ g : 𝓓(U, ℝ), ∀ y ∈ (U : Set (EuclideanSpace ℝ (Fin n))) ∩ dsupport T,
      (g : EuclideanSpace ℝ (Fin n) → ℝ) =ᶠ[𝓝 y] fun z ↦ φ (planeProj I x z) := by
  -- The relevant part of the support is `P '' tsupport φ ∩ dsupport T`, which is compact.
  have heq : (U : Set (EuclideanSpace ℝ (Fin n))) ∩ dsupport T ∩ planeProj I x ⁻¹' tsupport φ =
      coordPlaneMap I x '' tsupport φ ∩ dsupport T := by
    ext y
    constructor
    · rintro ⟨⟨hyU, hyT⟩, hyK⟩
      exact ⟨inter_dsupport_inter_preimage_planeProj_subset hTI _ ⟨⟨hyU, hyT⟩, hyK⟩, hyT⟩
    · rintro ⟨⟨s, hs, rfl⟩, hyT⟩
      exact ⟨⟨φ.tsupport_subset hs, hyT⟩, by simpa using hs⟩
  have hK : IsCompact
      ((U : Set (EuclideanSpace ℝ (Fin n))) ∩ dsupport T ∩ planeProj I x ⁻¹' tsupport φ) := by
    rw [heq]
    exact (φ.hasCompactSupport.image (coordPlaneMap I x).continuous).inter_right
      isClosed_dsupport
  obtain ⟨χ, hχ, -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤) hK
    (inter_subset_left.trans inter_subset_left)
  exact ⟨cutoffCompCLM χ _ (contDiff_planeProj I x).contDiffOn φ,
    fun y hy ↦ cutoffCompCLM_eventuallyEq hχ hy.1 hy⟩

/-- If `∂T = 0`, the pushforward of the coefficient distribution of `T` to the plane has vanishing
derivatives. -/
private theorem lineDerivOp_pushforward_coeffDistribution_eq_zero (hT : HasLocallyFiniteMass T)
    (hTI : (U : Set (EuclideanSpace ℝ (Fin n))) ∩ dsupport T ⊆ range (coordPlaneMap I x))
    (hb : T ∘L extDerivCLM = 0) (v : EuclideanSpace ℝ (Fin (k + 1))) :
    ∂_{v} (pushforward (coeffDistribution T I) (planeProj I x)
      (contDiff_planeProj I x).contDiffOn (isProperOnSupport_coeffDistribution hTI)) = 0 := by
  ext φ
  obtain ⟨g, hg⟩ := exists_eventuallyEq_comp_planeProj hTI φ
  -- The derivative of `g` along the plane agrees with `∂_v φ ∘ q` near the support of `T`.
  have hg' : ∀ y ∈ (U : Set (EuclideanSpace ℝ (Fin n))) ∩ dsupport (coeffDistribution T I),
      ⇑(∂_{(coordPlaneMap I x).contLinear v} g : 𝓓(U, ℝ)) =ᶠ[𝓝 y]
        fun z ↦ ∂_{v} φ (planeProj I x z) := fun y hy ↦ by
    filter_upwards [(hg y ⟨hy.1, dsupport_coeffDistribution_subset hy.2⟩).eventuallyEq_nhds]
      with z hz
    have hφq : HasFDerivAt (fun z ↦ φ (planeProj I x z))
        (fderiv ℝ φ (planeProj I x z) ∘L coordProj I) z :=
      (φ.contDiff.differentiable (by simp) _).hasFDerivAt.comp z (hasFDerivAt_planeProj I x z)
    rw [lineDerivOp_apply, hz.lineDeriv_eq, (hφq.hasLineDerivAt _).lineDeriv,
      lineDerivOp_apply_eq_fderiv, ContinuousLinearMap.comp_apply,
      coordProj_contLinear_coordPlaneMap]
  rw [lineDerivOp_apply_apply, map_neg, pushforward_apply_of_eventuallyEq _ hg',
    coeffDistribution_apply, map_postcompCLM_coordForm_lineDerivOp_eq_zero hT hTI hb]
  simp

/-- If the pushforward of the coefficient distribution of `T` to the plane is integration against
the constant `c`, then `T = c • [[x; I]]`. -/
private theorem eq_smul_coordPlaneCurrent_of_pushforward_eq (hT : HasLocallyFiniteMass T)
    (hdT : HasLocallyFiniteMass (T ∘L extDerivCLM))
    (hTI : (U : Set (EuclideanSpace ℝ (Fin n))) ∩ dsupport T ⊆ range (coordPlaneMap I x)) {c : ℝ}
    (hc : pushforward (coeffDistribution T I) (planeProj I x) (contDiff_planeProj I x).contDiffOn
      (isProperOnSupport_coeffDistribution hTI) = ofFun (planeOpens I x U) (fun _ ↦ c) volume ⊤) :
    T = c • coordPlaneCurrent I x U := by
  ext ω
  -- The coefficient `s ↦ ω (P s) e_I` of `ω` along the plane, as a test function on the plane.
  have hPp (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hKU : K ⊆ U) :
      IsCompact ((planeOpens I x U : Set (EuclideanSpace ℝ (Fin (k + 1)))) ∩
        coordPlaneMap I x ⁻¹' K) := by
    rw [show (planeOpens I x U : Set (EuclideanSpace ℝ (Fin (k + 1)))) ∩ coordPlaneMap I x ⁻¹' K =
      coordPlaneMap I x ⁻¹' K from inter_eq_right.2 (preimage_mono hKU)]
    exact (isometry_coordPlaneMap I x).isClosedEmbedding.isCompact_preimage hK
  let φ : 𝓓(planeOpens I x U, ℝ) :=
    (EuclideanSpace.basisFun (Fin (k + 1)) ℝ).toBasis.testTopFormEquiv
      (pullbackCLM (coordPlaneMap I x) (coordPlaneMap I x).contDiff.contDiffOn hPp ω)
  have hφ (s : EuclideanSpace ℝ (Fin (k + 1))) :
      φ s = ω (coordPlaneMap I x s) fun j ↦ EuclideanSpace.single (I j) 1 := by
    by_cases hs : s ∈ planeOpens I x U
    · simp only [φ, Module.Basis.testTopFormEquiv_apply, pullbackCLM_apply_of_mem _ hs,
        ContinuousAffineMap.fderiv, ContinuousAlternatingMap.compContinuousLinearMap_apply,
        Function.comp_def, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
        contLinear_coordPlaneMap_single]
    · have hω : ω (coordPlaneMap I x s) = 0 :=
        image_eq_zero_of_notMem_tsupport fun h ↦ hs (ω.tsupport_subset h)
      simp [φ, pullbackCLM_apply_of_notMem _ hs, hω]
  obtain ⟨g, hg⟩ := exists_eventuallyEq_comp_planeProj hTI φ
  -- By tangency, `T ω = T (g dx^I)`, which is the pushforward evaluated on `φ`.
  have hgT : T ω = T (postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ (coordForm I)) g) :=
    hT.map_eq_map_of_forall_apply_single_eq hdT hTI fun y hy ↦ by
      obtain ⟨s, rfl⟩ := hTI hy
      simp [coordForm_apply_single, (hg _ hy).eq_of_nhds, hφ]
  rw [hgT, ← coeffDistribution_apply, ← pushforward_apply_of_eventuallyEq
      (hΦ := (contDiff_planeProj I x).contDiffOn) (hT := isProperOnSupport_coeffDistribution hTI) φ
      fun y hy ↦ hg y ⟨hy.1, dsupport_coeffDistribution_subset hy.2⟩, hc,
    ofFun_apply (locallyIntegrableOn_const c), smul_apply, coordPlaneCurrent_apply]
  simp only [hφ, smul_eq_mul, mul_comm _ c, integral_const_mul]

/-! ### The constancy theorem -/

/-- **The constancy theorem for normal currents in a coordinate plane.** Let `T` be a
`(k + 1)`-current of locally finite mass on an open set `U ⊆ ℝⁿ` with zero boundary, `T ∘ d = 0`,
supported in `U` in the coordinate plane through `x` spanned by `e_{I 0}, …, e_{I k}`. If the part
of the plane in `U` is connected, then `T` is a unique real multiple of the current of the plane.
-/
theorem existsUnique_eq_smul_coordPlaneCurrent_of_comp_extDerivCLM_eq_zero
    (hU : IsConnected (coordPlaneMap I x ⁻¹' U)) (hT : HasLocallyFiniteMass T)
    (hTI : (U : Set (EuclideanSpace ℝ (Fin n))) ∩ dsupport T ⊆ range (coordPlaneMap I x))
    (hb : T ∘L extDerivCLM = 0) :
    ∃! c : ℝ, T = c • coordPlaneCurrent I x U := by
  have hdT : HasLocallyFiniteMass (T ∘L extDerivCLM) := by
    simpa [hb] using hasLocallyFiniteMass_zero
  -- The pushforward of the coefficient distribution has vanishing derivatives on the connected
  -- part of the plane in `U`, so it is integration against a constant `c`.
  obtain ⟨c, hc, -⟩ := Distribution.existsUnique_eq_ofFun_const_of_forall_lineDerivOp_eq_zero
    (pushforward (coeffDistribution T I) (planeProj I x) (contDiff_planeProj I x).contDiffOn
      (isProperOnSupport_coeffDistribution hTI))
    volume hU (lineDerivOp_pushforward_coeffDistribution_eq_zero hT hTI hb)
  have hTc := eq_smul_coordPlaneCurrent_of_pushforward_eq hT hdT hTI hc
  refine ⟨c, hTc, fun c' hc' ↦ ?_⟩
  obtain ⟨ω, hω⟩ := DFunLike.ne_iff.1 (coordPlaneCurrent_ne_zero hU.nonempty)
  have h := DFunLike.congr_fun (hc'.symm.trans hTc) ω
  simp only [smul_apply, smul_eq_mul] at h
  exact mul_right_cancel₀ hω h

end Constancy

end TauCeti
