/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Diffeomorph.Cotangent
public import TauCeti.Geometry.Manifold.Instances.AddCircle.Torus

import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod.Basic

/-!
# The cotangent bundle of a torus

For a finite family of positive periods `p : ι → ℝ`, let `Tⁿ = ∀ i, AddCircle (p i)` be the torus,
modelled on `I_T = ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)`. Since the tangent-bundle trivializations
of `Tⁿ` are the identity of `ι → ℝ` on their chart domains (`AddCircle.symmL_trivializationAt_pi`),
the preferred charts of the cotangent bundle `T*Tⁿ` act trivially on the fibre coordinate
(`TauCeti.CotangentBundle.extChartAt_torus_apply`,
`TauCeti.CotangentBundle.extChartAt_torus_symm_apply`).

Consequently, `T*Tⁿ` is globally trivialized by the analytic diffeomorphism

`z ↦ (z.proj, z.2) : T*Tⁿ ≃ Tⁿ × ((ι → ℝ) →L[ℝ] ℝ)`

(`TauCeti.CotangentBundle.torusTrivDiffeomorph`), whose differential at every point is the identity
of `(ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)`. Identifying the dual `(ι → ℝ) →L[ℝ] ℝ` with `ι → ℝ` via
evaluation on the standard basis `eᵢ = Pi.single i 1` yields the **action–angle trivialization**

`z ↦ (z.proj, fun i ↦ z.2 (Pi.single i 1)) : T*Tⁿ ≃ Tⁿ × (ι → ℝ)`

(`TauCeti.CotangentBundle.torusActionAngleDiffeomorph`). In particular, the action coordinate map
`z ↦ fun i ↦ z.2 (Pi.single i 1)` is analytic with differential `(a, η) ↦ fun i ↦ η (Pi.single i 1)`
(`TauCeti.CotangentBundle.hasMFDerivAt_torusActionCoord`).

Precomposing the inverse action–angle trivialization with the universal covering map of `Tⁿ` gives
the covering map `(ι → ℝ) × (ι → ℝ) → T*Tⁿ` sending `(θ, I)` to the covector `∑ i, I i • dθᵢ` over
`([θᵢ])ᵢ` (`TauCeti.CotangentBundle.torusCoverMap`). It is a surjective analytic local
diffeomorphism (`TauCeti.CotangentBundle.isLocalDiffeomorph_torusCoverMap`) with differential
`(a, b) ↦ (a, ∑ i, b i • proj i)` (`TauCeti.CotangentBundle.mfderiv_torusCoverMap_apply`), and two
pairs `(θ, I)` and `(θ', I')` have the same image exactly when `I' = I` and `θ' - θ ∈ ∏ i, p i · ℤ`
(`TauCeti.CotangentBundle.torusCoverMap_eq_iff`).

Finally, the cotangent lift of the coordinatewise period rescaling
`AddCircle.piDiffeomorphAddCircle` rescales the `i`-th action coordinate by `(q i)⁻¹ * p i`
(`TauCeti.CotangentBundle.piDiffeomorphAddCircle_cotangent_snd_apply_single`).

## Main definitions

* `TauCeti.CotangentBundle.torusTrivDiffeomorph`: the global trivialization
  `T*Tⁿ ≃ₘ^n Tⁿ × ((ι → ℝ) →L[ℝ] ℝ)`.
* `TauCeti.CotangentBundle.torusActionAngleDiffeomorph`: the action–angle trivialization
  `T*Tⁿ ≃ₘ^n Tⁿ × (ι → ℝ)`.
* `TauCeti.CotangentBundle.torusCoverMap`: the universal covering map `(ι → ℝ) × (ι → ℝ) → T*Tⁿ`.

## Main results

* `TauCeti.CotangentBundle.extChartAt_torus_apply`,
  `TauCeti.CotangentBundle.extChartAt_torus_symm_apply`: preferred charts of `T*Tⁿ` are trivial on
  the covector fibre.
* `TauCeti.CotangentBundle.hasMFDerivAt_torusTrivDiffeomorph`,
  `TauCeti.CotangentBundle.hasMFDerivAt_torusTrivDiffeomorph_symm`: the trivialization and its
  inverse have identity differentials.
* `TauCeti.CotangentBundle.hasMFDerivAt_torusActionCoord`,
  `TauCeti.CotangentBundle.mfderiv_torusActionCoord_apply`: smoothness and differential of the
  action coordinates `z ↦ fun i ↦ z.2 (Pi.single i 1)`.
* `TauCeti.CotangentBundle.isLocalDiffeomorph_torusCoverMap`,
  `TauCeti.CotangentBundle.torusCoverMap_eq_iff`,
  `TauCeti.CotangentBundle.mfderiv_torusCoverMap_apply`: the covering map of `T*Tⁿ` is a surjective
  analytic local diffeomorphism identifying points modulo the period lattice in the angles.
* `TauCeti.CotangentBundle.piDiffeomorphAddCircle_cotangent_snd_apply_single`: effect of period
  rescaling on the action coordinates.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Sections 49–50.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 18.4.
-/

public section

noncomputable section

open Bundle Function Set
open scoped Manifold ContDiff Topology

namespace TauCeti

namespace CotangentBundle

variable {ι : Type*} [Fintype ι] (p : ι → ℝ) [∀ i, Fact (0 < p i)]

/-! ### Preferred charts of `T*Tⁿ` -/

section Charts

variable {p}

/-- On the base chart domain around `z₀.proj`, the preferred chart of the cotangent bundle of a
torus keeps the covector coordinate unchanged. -/
theorem extChartAt_torus_apply
    {z₀ z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))}
    (hz : z.proj ∈ (chartAt (ModelPi fun _ : ι ↦ ℝ) z₀.proj).source) :
    extChartAt ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) z₀ z =
      (extChartAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) z₀.proj z.proj, z.2) := by
  rw [extChartAt_apply]
  refine Prod.ext rfl (ContinuousLinearMap.ext fun v ↦ ?_)
  rw [ContinuousLinearMap.comp_apply, AddCircle.symmL_trivializationAt_pi hz]
  rfl

/-- On the target of the base chart at `z₀.proj`, the inverse of the preferred chart of the
cotangent bundle of a torus keeps the covector coordinate unchanged. -/
theorem extChartAt_torus_symm_apply
    (z₀ : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)))
    {q : ι → ℝ} (η : (ι → ℝ) →L[ℝ] ℝ)
    (hq : q ∈ (extChartAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) z₀.proj).target) :
    (extChartAt ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) z₀).symm
        (q, η) =
      TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ)
        ((extChartAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) z₀.proj).symm q) η := by
  have hx : (extChartAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) z₀.proj).symm q ∈
      (chartAt (ModelPi fun _ : ι ↦ ℝ) z₀.proj).source := by
    simpa only [extChartAt_source] using
      (extChartAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) z₀.proj).map_target hq
  rw [extChartAt_symm_apply z₀ η hq]
  refine CotangentBundle.ext rfl fun v ↦ ?_
  rw [ContinuousLinearMap.comp_apply, AddCircle.continuousLinearMapAt_trivializationAt_pi hx]
  rfl

end Charts

/-! ### Global trivialization of `T*Tⁿ` -/

section Trivialization

private theorem continuousAt_torusTriv
    (z₀ : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) :
    ContinuousAt
      ((fun z ↦ (z.proj, z.2)) :
        CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) →
          (∀ i, AddCircle (p i)) × ((ι → ℝ) →L[ℝ] ℝ)) z₀ := by
  let I_T := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)
  let f : CotangentBundle I_T (∀ i, AddCircle (p i)) → (ι → ℝ) →L[ℝ] ℝ := fun z ↦ z.2
  change ContinuousAt (fun z ↦ (z.proj, f z)) z₀
  let e := trivializationAt ((ι → ℝ) →L[ℝ] ℝ)
    (fun x : ∀ i, AddCircle (p i) ↦ TangentSpace I_T x →L[ℝ] ℝ) z₀.proj
  have hproj : ContinuousAt (fun z : CotangentBundle I_T (∀ i, AddCircle (p i)) ↦ z.proj) z₀ :=
    (FiberBundle.continuous_proj ((ι → ℝ) →L[ℝ] ℝ) _).continuousAt
  refine hproj.prodMk ?_
  have hz₀ : z₀ ∈ e.source :=
    e.mem_source.2 (FiberBundle.mem_baseSet_trivializationAt _ _ z₀.proj)
  have htriv : ContinuousAt (fun z ↦ (e z).2) z₀ :=
    continuous_snd.continuousAt.comp (e.continuousOn.continuousAt (e.open_source.mem_nhds hz₀))
  refine htriv.congr ?_
  filter_upwards [hproj.preimage_mem_nhds
    ((chartAt (ModelPi fun _ : ι ↦ ℝ) z₀.proj).open_source.mem_nhds
      (mem_chart_source _ z₀.proj))] with z hz
  refine (trivializationAt_mk_snd (I := I_T) z₀.proj z.proj z.2).trans ?_
  refine ContinuousLinearMap.ext fun v ↦ ?_
  rw [ContinuousLinearMap.comp_apply, AddCircle.symmL_trivializationAt_pi hz]
  rfl

private theorem continuousAt_torusTriv_symm
    (w₀ : (∀ i, AddCircle (p i)) × ((ι → ℝ) →L[ℝ] ℝ)) :
    ContinuousAt
      (fun w : (∀ i, AddCircle (p i)) × ((ι → ℝ) →L[ℝ] ℝ) ↦
        (TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ) w.1 w.2 :
          CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)))) w₀ := by
  refine (FiberBundle.continuousAt_totalSpace _ _).2 ⟨continuousAt_fst, ?_⟩
  refine continuousAt_snd.congr ?_
  filter_upwards [continuousAt_fst.preimage_mem_nhds
    ((chartAt (ModelPi fun _ : ι ↦ ℝ) w₀.1).open_source.mem_nhds
      (mem_chart_source _ w₀.1))] with w hw
  symm
  let η : TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) w.1 →L[ℝ] ℝ := w.2
  refine (trivializationAt_mk_snd (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) w₀.1 w.1 η).trans ?_
  refine ContinuousLinearMap.ext fun v ↦ ?_
  rw [ContinuousLinearMap.comp_apply, AddCircle.symmL_trivializationAt_pi hw]
  rfl

private theorem writtenInExtChartAt_torusTriv_eventuallyEq
    (z₀ : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) :
    writtenInExtChartAt
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
        z₀ ((fun z ↦ (z.proj, z.2)) :
          CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) →
            (∀ i, AddCircle (p i)) × ((ι → ℝ) →L[ℝ] ℝ)) =ᶠ[𝓝 (extChartAt
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) z₀ z₀)] id := by
  let I_T := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)
  let I_C := I_T.prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)
  have hz₀ : extChartAt I_C z₀ z₀ ∈
      (extChartAt I_T z₀.proj).target ×ˢ (univ : Set ((ι → ℝ) →L[ℝ] ℝ)) :=
    ⟨by rw [extChartAt_apply]; exact mem_extChartAt_target z₀.proj, trivial⟩
  filter_upwards [((isOpen_extChartAt_target (I := I_T) z₀.proj).prod isOpen_univ).mem_nhds hz₀]
    with w hw
  rcases w with ⟨q, η⟩
  have hq : q ∈ (extChartAt I_T z₀.proj).target := hw.1
  have hsymm := extChartAt_torus_symm_apply z₀ η hq
  simp only [writtenInExtChartAt, comp_apply, id_eq]
  rw [hsymm]
  change (extChartAt I_T z₀.proj ((extChartAt I_T z₀.proj).symm q), η) = (q, η)
  rw [(extChartAt I_T z₀.proj).right_inv hq]

private theorem writtenInExtChartAt_torusTriv_symm_eventuallyEq
    (w₀ : (∀ i, AddCircle (p i)) × ((ι → ℝ) →L[ℝ] ℝ)) :
    writtenInExtChartAt
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
        w₀ (fun w ↦ (TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ) w.1 w.2 :
          CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))))
      =ᶠ[𝓝 (extChartAt ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
        w₀ w₀)] id := by
  set I_T := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)
  set I_C := I_T.prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)
  filter_upwards [(isOpen_extChartAt_target (I := I_C) w₀).mem_nhds (mem_extChartAt_target w₀)]
    with w hw
  have hq : w.1 ∈ (extChartAt I_T w₀.1).target := by
    simpa only [I_C, extChartAt_prod, PartialEquiv.prod_target, extChartAt_model_space_eq_id,
      PartialEquiv.refl_target, mem_prod, mem_univ, and_true] using hw
  have hx : (extChartAt I_T w₀.1).symm w.1 ∈ (chartAt (ModelPi fun _ : ι ↦ ℝ) w₀.1).source := by
    simpa only [extChartAt_source] using (extChartAt I_T w₀.1).map_target hq
  simp only [writtenInExtChartAt, comp_apply, id_eq, I_C, extChartAt_prod, PartialEquiv.prod_symm,
    PartialEquiv.prod_coe, extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
    PartialEquiv.refl_coe]
  rw [extChartAt_torus_apply (z₀ := TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ) w₀.1 w₀.2) hx,
    (extChartAt I_T w₀.1).right_inv hq]
  rfl

/-- **Global trivialization of the cotangent bundle of a torus.** The map `z ↦ (z.proj, z.2)` is an
analytic diffeomorphism `T*Tⁿ ≃ Tⁿ × ((ι → ℝ) →L[ℝ] ℝ)`, reducing to the identity in preferred
charts at every point. -/
def torusTrivDiffeomorph (n : ℕ∞ω) :
    CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) ≃ₘ^n⟮
      (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ),
      (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)⟯
    (∀ i, AddCircle (p i)) × ((ι → ℝ) →L[ℝ] ℝ) where
  toFun z := (z.proj, (z.2 : (ι → ℝ) →L[ℝ] ℝ))
  invFun w := TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ) w.1 w.2
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun z₀ := contMDiffAt_iff.2 ⟨continuousAt_torusTriv p z₀,
    contDiffAt_id.contDiffWithinAt.congr_of_eventuallyEq
      ((writtenInExtChartAt_torusTriv_eventuallyEq p z₀).filter_mono nhdsWithin_le_nhds)
      (writtenInExtChartAt_torusTriv_eventuallyEq p z₀).self_of_nhds⟩
  contMDiff_invFun w₀ := contMDiffAt_iff.2 ⟨continuousAt_torusTriv_symm p w₀,
    contDiffAt_id.contDiffWithinAt.congr_of_eventuallyEq
      ((writtenInExtChartAt_torusTriv_symm_eventuallyEq p w₀).filter_mono nhdsWithin_le_nhds)
      (writtenInExtChartAt_torusTriv_symm_eventuallyEq p w₀).self_of_nhds⟩

/-- The global trivialization sends a covector to the pair of its base point and functional. -/
@[simp]
theorem torusTrivDiffeomorph_apply (n : ℕ∞ω)
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) :
    torusTrivDiffeomorph p n z = (z.proj, (z.2 : (ι → ℝ) →L[ℝ] ℝ)) :=
  (rfl)

/-- The inverse of the global trivialization packs a base point and a functional into `T*Tⁿ`. -/
@[simp]
theorem torusTrivDiffeomorph_symm_apply (n : ℕ∞ω)
    (w : (∀ i, AddCircle (p i)) × ((ι → ℝ) →L[ℝ] ℝ)) :
    (torusTrivDiffeomorph p n).symm w = TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ) w.1 w.2 :=
  (rfl)

/-- The global trivialization `T*Tⁿ ≃ Tⁿ × ((ι → ℝ) →L[ℝ] ℝ)` has derivative the identity at every
point. -/
theorem hasMFDerivAt_torusTrivDiffeomorph (n : ℕ∞ω)
    (z₀ : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) :
    HasMFDerivAt
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      (torusTrivDiffeomorph p n) z₀
      (ContinuousLinearMap.id ℝ ((ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ))) := by
  refine ⟨continuousAt_torusTriv p z₀, ?_⟩
  exact (hasFDerivAt_id _).hasFDerivWithinAt.congr_of_eventuallyEq
    ((writtenInExtChartAt_torusTriv_eventuallyEq p z₀).filter_mono nhdsWithin_le_nhds)
    (writtenInExtChartAt_torusTriv_eventuallyEq p z₀).self_of_nhds

/-- The derivative of the global trivialization `T*Tⁿ ≃ Tⁿ × ((ι → ℝ) →L[ℝ] ℝ)` is the identity. -/
@[simp]
theorem mfderiv_torusTrivDiffeomorph (n : ℕ∞ω)
    (z₀ : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) :
    mfderiv
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
        (torusTrivDiffeomorph p n) z₀ =
      ContinuousLinearMap.id ℝ ((ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) :=
  (hasMFDerivAt_torusTrivDiffeomorph p n z₀).mfderiv

/-- The inverse global trivialization `Tⁿ × ((ι → ℝ) →L[ℝ] ℝ) ≃ T*Tⁿ` has derivative the identity at
every point. -/
theorem hasMFDerivAt_torusTrivDiffeomorph_symm (n : ℕ∞ω)
    (w₀ : (∀ i, AddCircle (p i)) × ((ι → ℝ) →L[ℝ] ℝ)) :
    HasMFDerivAt
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      (torusTrivDiffeomorph p n).symm w₀
      (ContinuousLinearMap.id ℝ ((ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ))) := by
  refine ⟨continuousAt_torusTriv_symm p w₀, ?_⟩
  exact (hasFDerivAt_id _).hasFDerivWithinAt.congr_of_eventuallyEq
    ((writtenInExtChartAt_torusTriv_symm_eventuallyEq p w₀).filter_mono nhdsWithin_le_nhds)
    (writtenInExtChartAt_torusTriv_symm_eventuallyEq p w₀).self_of_nhds

/-- The derivative of the inverse global trivialization is the identity. -/
@[simp]
theorem mfderiv_torusTrivDiffeomorph_symm (n : ℕ∞ω)
    (w₀ : (∀ i, AddCircle (p i)) × ((ι → ℝ) →L[ℝ] ℝ)) :
    mfderiv
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
        (torusTrivDiffeomorph p n).symm w₀ =
      ContinuousLinearMap.id ℝ ((ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) :=
  (hasMFDerivAt_torusTrivDiffeomorph_symm p n w₀).mfderiv

end Trivialization

/-! ### Action–angle coordinates and universal cover of `T*Tⁿ` -/

section ActionAngle

/-- Evaluation on the standard basis `Pi.single i 1` identifies `((ι → ℝ) →L[ℝ] ℝ)` with `ι → ℝ`,
with inverse `I ↦ ∑ i, I i • proj i`. -/
private def dualPiEquiv : ((ι → ℝ) →L[ℝ] ℝ) ≃L[ℝ] (ι → ℝ) :=
  letI := Classical.decEq ι
  ContinuousLinearEquiv.equivOfInverse
    (ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1))
    (∑ i, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).smulRight
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i))
    (fun ξ ↦ ContinuousLinearMap.ext fun v ↦ by
      simp only [sum_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.pi_apply, ContinuousLinearMap.apply_apply,
        ContinuousLinearMap.proj_apply, smul_apply, smul_eq_mul]
      conv_rhs => rw [← Finset.univ_sum_single v]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hsingle : Pi.single (M := fun _ : ι ↦ ℝ) i (v i) = v i • Pi.single i 1 := by
        funext j
        by_cases hji : j = i <;> simp [hji]
      rw [hsingle, map_smul, smul_eq_mul, mul_comm])
    (fun I ↦ funext fun j ↦ by
      simp [Pi.single_apply])

/-- **Action–angle trivialization of `T*Tⁿ`.** The analytic diffeomorphism
`T*Tⁿ ≃ Tⁿ × (ι → ℝ)` sending a covector `ξ` over `θ` to `(θ, (ξ(eᵢ))ᵢ)`. -/
def torusActionAngleDiffeomorph (n : ℕ∞ω) :
    CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) ≃ₘ^n⟮
      (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ),
      (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ)⟯
    (∀ i, AddCircle (p i)) × (ι → ℝ) :=
  (torusTrivDiffeomorph p n).trans
    { toEquiv := (Equiv.refl _).prodCongr (dualPiEquiv (ι := ι)).toEquiv
      contMDiff_toFun := contMDiff_fst.prodMk
        ((dualPiEquiv (ι := ι)).contDiff.contMDiff.comp contMDiff_snd)
      contMDiff_invFun := contMDiff_fst.prodMk
        ((dualPiEquiv (ι := ι)).symm.contDiff.contMDiff.comp contMDiff_snd) }

/-- The action–angle trivialization sends `z` to `(z.proj, fun i ↦ z.2 (Pi.single i 1))`. -/
@[simp]
theorem torusActionAngleDiffeomorph_apply [DecidableEq ι] (n : ℕ∞ω)
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) :
    torusActionAngleDiffeomorph p n z = (z.proj, fun i ↦ z.2 (Pi.single i 1)) := by
  refine Prod.ext rfl (funext fun i ↦ ?_)
  change z.2 (letI := Classical.decEq ι; Pi.single i 1) = z.2 (Pi.single i 1)
  congr 1
  funext j
  simp [Pi.single_apply]

/-- The inverse of the action–angle trivialization sends `(θ, I)` to the covector
`∑ i, I i • proj i` over `θ`. -/
@[simp]
theorem torusActionAngleDiffeomorph_symm_apply (n : ℕ∞ω)
    (w : (∀ i, AddCircle (p i)) × (ι → ℝ)) :
    (torusActionAngleDiffeomorph p n).symm w =
      TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ) w.1
        (∑ i, w.2 i • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i)) := by
  refine CotangentBundle.ext rfl fun v ↦ ?_
  change (∑ i, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).smulRight
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i)) w.2 v =
    (∑ i, w.2 i • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i)) v
  simp [sum_apply]

/-- The action coordinate map `z ↦ fun i ↦ z.2 (Pi.single i 1)` on `T*Tⁿ` is analytic. -/
theorem contMDiff_torusActionCoord [DecidableEq ι] (n : ℕ∞ω) :
    ContMDiff ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) 𝓘(ℝ, ι → ℝ) n
      (fun z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) ↦
        fun i ↦ z.2 (Pi.single i 1)) :=
  (contMDiff_snd.comp (torusActionAngleDiffeomorph p n).contMDiff).congr fun z ↦
    (congrArg Prod.snd (torusActionAngleDiffeomorph_apply p n z)).symm

/-- The action coordinate map `z ↦ fun i ↦ z.2 (Pi.single i 1)` on `T*Tⁿ` has derivative
`(a, η) ↦ fun i ↦ η (Pi.single i 1)`. -/
theorem hasMFDerivAt_torusActionCoord [DecidableEq ι]
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) :
    HasMFDerivAt ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      𝓘(ℝ, ι → ℝ)
      (fun z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) ↦
        fun i ↦ z.2 (Pi.single i 1)) z
      ((ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1)).comp
        (ContinuousLinearMap.snd ℝ (ι → ℝ) ((ι → ℝ) →L[ℝ] ℝ))) := by
  let L : ((ι → ℝ) →L[ℝ] ℝ) →L[ℝ] (ι → ℝ) :=
    ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1)
  have hcomp :
      (fun z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) ↦
          fun i ↦ z.2 (Pi.single i 1)) =
        (L ∘ Prod.snd) ∘ torusTrivDiffeomorph p 1 := rfl
  rw [hcomp]
  have hsnd : HasMFDerivAt
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) 𝓘(ℝ, ι → ℝ)
      (L ∘ Prod.snd) (torusTrivDiffeomorph p 1 z)
      (L.comp (ContinuousLinearMap.snd ℝ (ι → ℝ) ((ι → ℝ) →L[ℝ] ℝ))) :=
    L.hasMFDerivAt.comp (torusTrivDiffeomorph p 1 z)
      (hasMFDerivAt_snd (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
        (I' := 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) (torusTrivDiffeomorph p 1 z))
  exact (hsnd.comp z (hasMFDerivAt_torusTrivDiffeomorph p 1 z)).congr_mfderiv
    (ContinuousLinearMap.comp_id _)

/-- The derivative of the action coordinate map `z ↦ fun i ↦ z.2 (Pi.single i 1)` sends a tangent
vector `v` of `T*Tⁿ` to `fun i ↦ v.2 (Pi.single i 1)`. -/
@[simp]
theorem mfderiv_torusActionCoord_apply [DecidableEq ι]
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)))
    (v : TangentSpace ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) z)
    (i : ι) :
    mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) 𝓘(ℝ, ι → ℝ)
        (fun z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) ↦
          fun i ↦ z.2 (Pi.single i 1)) z v i =
      v.2 (Pi.single i 1) := by
  rw [(hasMFDerivAt_torusActionCoord p z).mfderiv]
  rfl

/-- **Universal covering map of `T*Tⁿ`.** Sends `(θ, I) : (ι → ℝ) × (ι → ℝ)` to the covector
`∑ i, I i • proj i` over `fun i ↦ (θ i : AddCircle (p i))`. -/
def torusCoverMap (w : (ι → ℝ) × (ι → ℝ)) :
    CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) :=
  TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ) (fun i ↦ (w.1 i : AddCircle (p i)))
    (∑ i, w.2 i • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i))

/-- The base point of `torusCoverMap p (θ, I)` is `fun i ↦ (θ i : AddCircle (p i))`. -/
@[simp]
theorem torusCoverMap_proj (w : (ι → ℝ) × (ι → ℝ)) :
    (torusCoverMap p w).proj = fun i ↦ (w.1 i : AddCircle (p i)) :=
  (rfl)

/-- The covector `torusCoverMap p (θ, I)` evaluates a tangent vector `v` to `∑ i, I i * v i`. -/
theorem torusCoverMap_snd_apply (w : (ι → ℝ) × (ι → ℝ)) (v : ι → ℝ) :
    (torusCoverMap p w).2 v = ∑ i, w.2 i * v i := by
  change (∑ i, w.2 i • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i)) v = _
  simp [sum_apply, smul_apply]

/-- The `i`-th action coordinate of `torusCoverMap p (θ, I)` is `I i`. -/
@[simp]
theorem torusCoverMap_snd_apply_single [DecidableEq ι] (w : (ι → ℝ) × (ι → ℝ)) (i : ι) :
    (torusCoverMap p w).2 (Pi.single i 1) = w.2 i := by
  rw [torusCoverMap_snd_apply]
  simp [Pi.single_apply]

/-- The covering map `(ι → ℝ) × (ι → ℝ) → T*Tⁿ` is surjective. -/
theorem torusCoverMap_surjective : Surjective (torusCoverMap p) := fun z ↦ by
  classical
  refine ⟨(fun i ↦ (Quotient.exists_rep (z.proj i)).choose,
    fun i ↦ z.2 (Pi.single i 1)),
    CotangentBundle.ext
      (funext fun i ↦ (Quotient.exists_rep (z.proj i)).choose_spec) fun v ↦ ?_⟩
  let u : ι → ℝ := v
  let ξ : (ι → ℝ) →L[ℝ] ℝ := z.2
  refine (torusCoverMap_snd_apply p _ u).trans ?_
  change ∑ i, ξ (Pi.single i 1) * u i = ξ u
  conv_rhs => rw [← Finset.univ_sum_single u]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hsingle : Pi.single (M := fun _ : ι ↦ ℝ) i (u i) = u i • Pi.single i 1 := by
    funext j
    by_cases hji : j = i <;> simp [hji]
  rw [hsingle, map_smul, smul_eq_mul, mul_comm]

/-- Two points `(θ, I)` and `(θ', I')` have the same image under `torusCoverMap p` exactly when
`I' = I` and `θ' - θ` lies in the period lattice `∏ i, p i · ℤ`. -/
theorem torusCoverMap_eq_iff (θ θ' c c' : ι → ℝ) :
    torusCoverMap p (θ, c) = torusCoverMap p (θ', c') ↔
      c' = c ∧ ∃ m : ι → ℤ, θ' = θ + fun i ↦ p i * m i := by
  classical
  constructor
  · intro h
    have hc : c' = c := funext fun i ↦ by
      have hi := congrArg (fun z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
          (∀ i, AddCircle (p i)) ↦ z.2 (Pi.single i 1)) h
      simpa using hi.symm
    have hθ : ∀ i, ∃ m : ℤ, θ' i = θ i + p i * m := fun i ↦ by
      have hi : (θ i : AddCircle (p i)) = (θ' i : AddCircle (p i)) :=
        congrFun (congrArg TotalSpace.proj h) i
      obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.1 (QuotientAddGroup.eq.1 hi)
      exact ⟨m, by rw [zsmul_eq_mul, mul_comm] at hm; linarith⟩
    choose m hm using hθ
    exact ⟨hc, m, funext hm⟩
  · rintro ⟨rfl, m, rfl⟩
    refine CotangentBundle.ext (funext fun i ↦ ?_) fun _ ↦ rfl
    simp only [torusCoverMap_proj, Pi.add_apply, AddCircle.coe_add]
    have hzero : ((p i * (m i : ℝ) : ℝ) : AddCircle (p i)) = 0 := by
      rw [mul_comm, ← zsmul_eq_mul, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero]
    rw [hzero, add_zero]

/-- The covering map `(ι → ℝ) × (ι → ℝ) → T*Tⁿ` is an analytic local diffeomorphism. -/
theorem isLocalDiffeomorph_torusCoverMap (n : ℕ∞ω) :
    IsLocalDiffeomorph 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) n
      (torusCoverMap p) := by
  have hcomp : torusCoverMap p =
      (torusActionAngleDiffeomorph p n).symm ∘
        Prod.map (fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle (p i))) (id : (ι → ℝ) → (ι → ℝ)) :=
    funext fun w ↦ (torusActionAngleDiffeomorph_symm_apply p n
      (fun i ↦ (w.1 i : AddCircle (p i)), w.2)).symm
  rw [hcomp]
  intro w
  have hprod : IsLocalDiffeomorphAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ)) n
      (Prod.map (fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle (p i))) (id : (ι → ℝ) → (ι → ℝ))) w := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact (AddCircle.isLocalDiffeomorph_pi_coe p n w.1).prodMap
      ((Diffeomorph.refl 𝓘(ℝ, ι → ℝ) (ι → ℝ) n).isLocalDiffeomorph w.2)
  exact hprod.comp (hg := (torusActionAngleDiffeomorph p n).symm.isLocalDiffeomorph _)

/-- The covering map `(ι → ℝ) × (ι → ℝ) → T*Tⁿ` has derivative
`(a, b) ↦ (a, ∑ i, b i • proj i)` at every point. -/
theorem hasMFDerivAt_torusCoverMap (w : (ι → ℝ) × (ι → ℝ)) :
    HasMFDerivAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      (torusCoverMap p) w
      ((ContinuousLinearMap.id ℝ (ι → ℝ)).prodMap
        (∑ i, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).smulRight
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i))) := by
  let R : (ι → ℝ) →L[ℝ] ((ι → ℝ) →L[ℝ] ℝ) :=
    ∑ i, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).smulRight
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i)
  have hcomp : torusCoverMap p =
      (torusTrivDiffeomorph p 1).symm ∘
        Prod.map (fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle (p i))) R := by
    funext u
    refine CotangentBundle.ext rfl fun v ↦ ?_
    change (∑ i, u.2 i • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i)) (v : ι → ℝ) =
      R u.2 (v : ι → ℝ)
    simp [R, sum_apply]
  rw [hcomp]
  have hprod : HasMFDerivAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      (Prod.map (fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle (p i))) R) w
      ((ContinuousLinearMap.id ℝ (ι → ℝ)).prodMap R) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    refine ((AddCircle.hasMFDerivAt_pi_coe p w.1).prodMap R.hasMFDerivAt).congr_mfderiv ?_
    rw [AddCircle.mfderiv_pi_coe, R.hasMFDerivAt.mfderiv]
    rfl
  exact ((hasMFDerivAt_torusTrivDiffeomorph_symm p 1 _).comp w hprod).congr_mfderiv
    (ContinuousLinearMap.id_comp _)

/-- The derivative of `torusCoverMap p` sends `(a, b)` to `(a, ∑ i, b i • proj i)`. -/
@[simp]
theorem mfderiv_torusCoverMap_apply (w v : (ι → ℝ) × (ι → ℝ)) :
    mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
        (torusCoverMap p) w v =
      (v.1, ∑ i, v.2 i • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i)) := by
  rw [(hasMFDerivAt_torusCoverMap p w).mfderiv]
  refine Prod.ext rfl (ContinuousLinearMap.ext fun u ↦ ?_)
  change (∑ i, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).smulRight
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i)) v.2 u =
    (∑ i, v.2 i • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i)) u
  simp [sum_apply]

end ActionAngle

/-! ### Cotangent lift of period rescaling -/

section Rescale

variable (p₁ p₂ : ι → ℝ) [∀ i, Fact (0 < p₁ i)] [∀ i, Fact (0 < p₂ i)]

/-- The cotangent lift of the coordinatewise period rescaling `AddCircle.piDiffeomorphAddCircle`
sends a covector `z` to `v ↦ z.2 (fun i ↦ (p₂ i)⁻¹ * p₁ i * v i)`. -/
theorem piDiffeomorphAddCircle_cotangent_snd_apply
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p₁ i)))
    (v : ι → ℝ) :
    ((AddCircle.piDiffeomorphAddCircle p₁ p₂ ∞).cotangent z).2 v =
      z.2 (fun i ↦ (p₂ i)⁻¹ * p₁ i * v i) := by
  refine (Diffeomorph.cotangent_snd_apply _ z v).trans (congrArg z.2 (funext fun i ↦ ?_))
  rw [AddCircle.piDiffeomorphAddCircle_symm, AddCircle.mfderiv_piDiffeomorphAddCircle_apply]

/-- The cotangent lift of the coordinatewise period rescaling rescales the `i`-th action coordinate
by `(p₂ i)⁻¹ * p₁ i`. -/
@[simp]
theorem piDiffeomorphAddCircle_cotangent_snd_apply_single [DecidableEq ι]
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p₁ i)))
    (i : ι) :
    ((AddCircle.piDiffeomorphAddCircle p₁ p₂ ∞).cotangent z).2 (Pi.single i 1) =
      (p₂ i)⁻¹ * p₁ i * z.2 (Pi.single i 1) := by
  let ξ : (ι → ℝ) →L[ℝ] ℝ := z.2
  have hvec : (fun j ↦ (p₂ j)⁻¹ * p₁ j * Pi.single (M := fun _ : ι ↦ ℝ) i (1 : ℝ) j) =
      ((p₂ i)⁻¹ * p₁ i) • Pi.single (M := fun _ : ι ↦ ℝ) i (1 : ℝ) := by
    funext j
    by_cases hji : j = i <;> simp [hji]
  refine (piDiffeomorphAddCircle_cotangent_snd_apply p₁ p₂ z (Pi.single i 1)).trans ?_
  change ξ (fun j ↦ (p₂ j)⁻¹ * p₁ j * Pi.single (M := fun _ : ι ↦ ℝ) i (1 : ℝ) j) =
    (p₂ i)⁻¹ * p₁ i * ξ (Pi.single i 1)
  rw [hvec, map_smul, smul_eq_mul]

end Rescale

end CotangentBundle

end TauCeti
