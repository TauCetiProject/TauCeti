/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.SemiboundedForm
public import TauCeti.LinearAlgebra.LinearPMap.Conj

/-!
# Restriction and unitary transport of semibounded forms

Let `q` be a semibounded form on an inner product space `H` (`TauCeti.SemiboundedForm 𝕜 H`). This
file transports `q` along two operations.

* **Restriction.** For a subspace `W` of the form domain, `q.restrict W hW` is `q` on `W`. It keeps
  every lower bound of `q` (`TauCeti.SemiboundedForm.IsLowerBound.restrict`), and its form spaces
  embed isometrically into those of `q` (`TauCeti.SemiboundedForm.restrictFormSpaceIsometry`), with
  image the vectors whose underlying vector lies in `W`. So when `q` is closed, `q.restrict W hW` is
  closed exactly when `W` is closed in the form norm of `q`
  (`TauCeti.SemiboundedForm.isClosed_restrict_iff`). When `W` is dense in `H`, the operator
  represented by the restriction has graph `{(u, h) | u ∈ W, ∀ v ∈ W, q u v = ⟪h, v⟫_𝕜}`
  (`TauCeti.SemiboundedForm.mem_graph_operator_restrict_iff`).
* **Unitary transport.** For a linear isometric equivalence `U : H ≃ₗᵢ[𝕜] H'`, `q.map U` is the
  form `(u, v) ↦ q (U⁻¹ u) (U⁻¹ v)` on `U D`. It is functorial in `U`
  (`TauCeti.SemiboundedForm.map_refl`, `TauCeti.SemiboundedForm.map_trans`). It has the same lower
  bounds, isometric form spaces (`TauCeti.SemiboundedForm.mapFormSpaceEquiv`), is closed exactly
  when `q` is, and represents the unitary conjugate `U A U⁻¹` of the operator `A` represented by
  `q` (`TauCeti.SemiboundedForm.operator_map`).

## Main declarations

* `TauCeti.SemiboundedForm.restrict`: the restriction to a subspace of the form domain.
* `TauCeti.SemiboundedForm.isClosed_restrict_iff`: closedness of a restriction of a closed form.
* `TauCeti.SemiboundedForm.mem_graph_operator_restrict_iff`: the operator of a restriction.
* `TauCeti.SemiboundedForm.map`: unitary transport of a form.
* `TauCeti.SemiboundedForm.isClosed_map_iff`, `TauCeti.SemiboundedForm.operator_map`.

## References

* G. Teschl, *Mathematical Methods in Quantum Mechanics*, 2nd ed., AMS (2014), §2.3,
  Theorem 2.13, for the operator represented by a closed form.
-/

public section

noncomputable section

open RCLike
open scoped InnerProductSpace

namespace TauCeti

namespace SemiboundedForm

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  (q : SemiboundedForm 𝕜 H)

/-! ### Restriction to a subspace of the form domain -/

section Restrict

variable (W : Submodule 𝕜 H) (hW : W ≤ q.domain)

/-- The **restriction** of a semibounded form `q` to a subspace `W` of its form domain. -/
def restrict : SemiboundedForm 𝕜 H where
  domain := W
  form := (q.form.comp (Submodule.inclusion hW)).compl₂ (Submodule.inclusion hW)
  form_apply_eq_star u v := q.form_apply_eq_star _ _
  exists_lowerBound := by
    obtain ⟨γ, hγ⟩ := q.exists_lowerBound
    exact ⟨γ, fun u ↦ hγ (Submodule.inclusion hW u)⟩

/-- The form domain of the restriction to `W` is `W`. -/
@[simp]
theorem restrict_domain : (q.restrict W hW).domain = W :=
  (rfl)

/-- The inclusion of the form domain of a restriction into the form domain of `q`. -/
def restrictInclusion : (q.restrict W hW).domain →ₗ[𝕜] q.domain :=
  Submodule.inclusion ((q.restrict_domain W hW).le.trans hW)

/-- The inclusion of the form domain of a restriction does not change the underlying vector. -/
@[simp]
theorem coe_restrictInclusion (u : (q.restrict W hW).domain) :
    (q.restrictInclusion W hW u : H) = u :=
  Submodule.coe_inclusion _ u

/-- The restriction to `W` is `q` on the vectors of `W`. -/
@[simp]
theorem restrict_form_apply (u v : (q.restrict W hW).domain) :
    (q.restrict W hW).form u v = q.form (q.restrictInclusion W hW u) (q.restrictInclusion W hW v) :=
  (rfl)

variable {q W}

/-- **A restriction keeps every lower bound.** -/
theorem IsLowerBound.restrict {γ : ℝ} (hγ : q.IsLowerBound γ) :
    (q.restrict W hW).IsLowerBound γ :=
  (isLowerBound_iff _).mpr fun u ↦ by
    simpa using (isLowerBound_iff q).mp hγ (q.restrictInclusion W hW u)

/-- An admissible shift of `q` is admissible for every restriction of `q`. -/
theorem IsAdmissibleShift.restrict {α : ℝ} (hα : q.IsAdmissibleShift α) :
    (q.restrict W hW).IsAdmissibleShift α :=
  let ⟨γ, hγ, hγα⟩ := (isAdmissibleShift_iff q).mp hα
  (isAdmissibleShift_iff _).mpr ⟨γ, hγ.restrict hW, hγα⟩

variable {α : ℝ} (hα : q.IsAdmissibleShift α)

/-- The form space of a restriction embeds isometrically into the form space of `q`: the form norm
of the restriction is the form norm of `q`. -/
def restrictFormSpaceIsometry :
    (q.restrict W hW).FormSpace α (hα.restrict hW) →ₗᵢ[𝕜] q.FormSpace α hα :=
  LinearMap.isometryOfInner
    ((q.toFormSpace hα).toLinearMap ∘ₗ q.restrictInclusion W hW ∘ₗ
      ((q.restrict W hW).toFormSpace (hα.restrict hW)).symm.toLinearMap)
    fun x y ↦ by
      obtain ⟨u, rfl⟩ := ((q.restrict W hW).toFormSpace (hα.restrict hW)).surjective x
      obtain ⟨v, rfl⟩ := ((q.restrict W hW).toFormSpace (hα.restrict hW)).surjective y
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply, inner_toFormSpace, shiftedInner_def, restrict_form_apply,
        coe_restrictInclusion]

@[simp]
theorem restrictFormSpaceIsometry_toFormSpace (u : (q.restrict W hW).domain) :
    q.restrictFormSpaceIsometry hW hα ((q.restrict W hW).toFormSpace (hα.restrict hW) u) =
      q.toFormSpace hα (q.restrictInclusion W hW u) := by
  simp only [restrictFormSpaceIsometry, LinearMap.coe_isometryOfInner, LinearMap.coe_comp,
    Function.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

/-- The isometry of form spaces does not change the underlying vector of the form domain. -/
@[simp]
theorem toFormSpace_symm_restrictFormSpaceIsometry
    (x : (q.restrict W hW).FormSpace α (hα.restrict hW)) :
    (q.toFormSpace hα).symm (q.restrictFormSpaceIsometry hW hα x) =
      q.restrictInclusion W hW (((q.restrict W hW).toFormSpace (hα.restrict hW)).symm x) := by
  obtain ⟨u, rfl⟩ := ((q.restrict W hW).toFormSpace (hα.restrict hW)).surjective x
  rw [restrictFormSpaceIsometry_toFormSpace, LinearEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply]

/-- The isometry of form spaces commutes with the inclusions into `H`. -/
theorem inclusion_restrictFormSpaceIsometry (x : (q.restrict W hW).FormSpace α (hα.restrict hW)) :
    q.inclusion hα (q.restrictFormSpaceIsometry hW hα x) =
      (q.restrict W hW).inclusion (hα.restrict hW) x := by
  obtain ⟨u, rfl⟩ := ((q.restrict W hW).toFormSpace (hα.restrict hW)).surjective x
  rw [restrictFormSpaceIsometry_toFormSpace, inclusion_toFormSpace, inclusion_toFormSpace,
    coe_restrictInclusion]

/-- The image of the form space of a restriction to `W` consists of the vectors of the form space
of `q` whose underlying vector lies in `W`. -/
theorem range_restrictFormSpaceIsometry :
    Set.range (q.restrictFormSpaceIsometry hW hα) = {x | q.inclusion hα x ∈ W} := by
  ext x
  refine ⟨?_, fun hx ↦ ?_⟩
  · rintro ⟨y, rfl⟩
    rw [Set.mem_ofPred_eq, inclusion_restrictFormSpaceIsometry, inclusion_apply]
    exact (q.restrict_domain W hW).le
      (((q.restrict W hW).toFormSpace (hα.restrict hW)).symm y).property
  · refine ⟨(q.restrict W hW).toFormSpace (hα.restrict hW) ⟨_, hx⟩, ?_⟩
    rw [restrictFormSpaceIsometry_toFormSpace]
    convert (q.toFormSpace hα).apply_symm_apply x
    exact Subtype.ext ((q.coe_restrictInclusion W hW _).trans (q.inclusion_apply hα x))

/-- If a restriction of `q` to `W` is closed, then `W` is closed in the form norm of `q`. -/
theorem isClosed_setOf_inclusion_mem_of_isClosed_restrict (h : (q.restrict W hW).IsClosed) :
    _root_.IsClosed {x : q.FormSpace α hα | q.inclusion hα x ∈ W} := by
  have := ((q.restrict W hW).isClosed_iff_completeSpace (hα.restrict hW)).mp h
  rw [← range_restrictFormSpaceIsometry hW hα]
  exact ((completeSpace_iff_isComplete_range
    (q.restrictFormSpaceIsometry hW hα).isometry.isUniformInducing).mp this).isClosed

/-- **Closed restrictions of a closed form.** The restriction of a closed form `q` to a subspace
`W` of its form domain is closed exactly when `W` is closed in the form norm of `q`. -/
theorem isClosed_restrict_iff (hq : q.IsClosed) :
    (q.restrict W hW).IsClosed ↔ _root_.IsClosed {x : q.FormSpace α hα | q.inclusion hα x ∈ W} := by
  refine ⟨q.isClosed_setOf_inclusion_mem_of_isClosed_restrict hW hα, fun h ↦ ?_⟩
  have := (q.isClosed_iff_completeSpace hα).mp hq
  rw [← range_restrictFormSpaceIsometry hW hα] at h
  rw [isClosed_iff_completeSpace _ (hα.restrict hW), completeSpace_iff_isComplete_range
    (q.restrictFormSpaceIsometry hW hα).isometry.isUniformInducing]
  exact h.isComplete

variable (q) {hW} in
/-- **The operator represented by a restriction.** For a subspace `W` of the form domain which is
dense in `H`, the graph of the operator represented by `q.restrict W hW` consists of the pairs
`(x, h)` with `x ∈ W` and `q x v = ⟪h, v⟫_𝕜` for every `v ∈ W`. -/
theorem mem_graph_operator_restrict_iff (hd : Dense ((q.restrict W hW).domain : Set H)) {x h : H} :
    (x, h) ∈ ((q.restrict W hW).operator hd).graph ↔
      ∃ hx : x ∈ W, ∀ v (hv : v ∈ W), q.form ⟨x, hW hx⟩ ⟨v, hW hv⟩ = ⟪h, v⟫_𝕜 := by
  simp only [mem_graph_operator_iff, restrict_form_apply, restrictInclusion,
    Submodule.inclusion_apply, Subtype.forall, Subtype.exists, restrict_domain]
  constructor
  · rintro ⟨u, hu, rfl, hv⟩
    exact ⟨hu, hv⟩
  · rintro ⟨hx, hv⟩
    exact ⟨x, hx, rfl, hv⟩

variable {hW} in
/-- The operator represented by the restriction of `q` to a dense subspace `W` of the form domain
which is closed in the form norm is self-adjoint, when `q` is closed and `H` is complete. -/
theorem isSelfAdjoint_operator_restrict [CompleteSpace H] (hq : q.IsClosed)
    (hd : Dense ((q.restrict W hW).domain : Set H))
    (hWc : _root_.IsClosed {x : q.FormSpace α hα | q.inclusion hα x ∈ W}) :
    IsSelfAdjoint ((q.restrict W hW).operator hd) :=
  (q.restrict W hW).isSelfAdjoint_operator hd ((q.isClosed_restrict_iff hW hα hq).mpr hWc)

end Restrict

/-! ### Unitary transport -/

section Map

variable {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace 𝕜 H'] (U : H ≃ₗᵢ[𝕜] H')

/-- The **unitary transport** of a semibounded form `q` along `U : H ≃ₗᵢ[𝕜] H'`: the form
`(u, v) ↦ q (U⁻¹ u) (U⁻¹ v)` on the image `U D` of the form domain `D`. -/
def map : SemiboundedForm 𝕜 H' where
  domain := q.domain.map (U.toLinearEquiv : H →ₗ[𝕜] H')
  form := (q.form.comp (U.toLinearEquiv.submoduleMap q.domain).symm.toLinearMap).compl₂
    (U.toLinearEquiv.submoduleMap q.domain).symm.toLinearMap
  form_apply_eq_star u v := q.form_apply_eq_star _ _
  exists_lowerBound := by
    obtain ⟨γ, hγ⟩ := q.exists_lowerBound
    refine ⟨γ, fun u ↦ ?_⟩
    simpa using hγ ((U.toLinearEquiv.submoduleMap q.domain).symm u)

/-- The form domain of `q.map U` is the image of the form domain under `U`. -/
@[simp]
theorem map_domain : (q.map U).domain = q.domain.map (U.toLinearEquiv : H →ₗ[𝕜] H') :=
  (rfl)

/-- The identification `u ↦ U u` of the form domain of `q` with that of `q.map U`. -/
def mapDomainEquiv : q.domain ≃ₗ[𝕜] (q.map U).domain :=
  U.toLinearEquiv.submoduleMap q.domain

/-- The underlying vector of `q.mapDomainEquiv U u` is `U u`. -/
@[simp]
theorem coe_mapDomainEquiv (u : q.domain) : (q.mapDomainEquiv U u : H') = U u :=
  U.toLinearEquiv.submoduleMap_apply q.domain u

/-- The underlying vector of `(q.mapDomainEquiv U).symm u` is `U⁻¹ u`. -/
@[simp]
theorem coe_mapDomainEquiv_symm (u : (q.map U).domain) :
    ((q.mapDomainEquiv U).symm u : H) = U.symm u :=
  U.toLinearEquiv.submoduleMap_symm_apply q.domain u

/-- `q.map U` is `(u, v) ↦ q (U⁻¹ u) (U⁻¹ v)`. -/
theorem map_form_apply (u v : (q.map U).domain) :
    (q.map U).form u v = q.form ((q.mapDomainEquiv U).symm u) ((q.mapDomainEquiv U).symm v) :=
  (rfl)

/-- `q.map U` on `U u` and `U v` is `q u v`. -/
@[simp]
theorem map_form_mapDomainEquiv (u v : q.domain) :
    (q.map U).form (q.mapDomainEquiv U u) (q.mapDomainEquiv U v) = q.form u v := by
  rw [map_form_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

/-- Transport along the identity does nothing. -/
@[simp]
theorem map_refl : q.map (LinearIsometryEquiv.refl 𝕜 H) = q :=
  ext_of_form_eq (by ext; simp) fun u v u' v' hu hv ↦ by
    rw [map_form_apply]
    exact congrArg₂ (fun a b ↦ q.form a b)
      (Subtype.ext (by simp [hu, LinearIsometryEquiv.symm_apply_eq]))
      (Subtype.ext (by simp [hv, LinearIsometryEquiv.symm_apply_eq]))

variable {H'' : Type*} [NormedAddCommGroup H''] [InnerProductSpace 𝕜 H''] in
/-- Transport along a composite is transport along each factor in turn. -/
theorem map_trans (V : H' ≃ₗᵢ[𝕜] H'') : q.map (U.trans V) = (q.map U).map V :=
  ext_of_form_eq (by ext; simp) fun u v u' v' hu hv ↦ by
    rw [map_form_apply, map_form_apply, map_form_apply]
    exact congrArg₂ (fun a b ↦ q.form a b) (Subtype.ext (by simp [hu]))
      (Subtype.ext (by simp [hv]))

/-- Transporting along `U` and then along `U⁻¹` recovers the original form. -/
@[simp]
theorem map_symm_map : (q.map U).map U.symm = q := by
  rw [← map_trans, LinearIsometryEquiv.self_trans_symm, map_refl]

/-- Transporting along `U⁻¹` and then along `U` recovers the original form. -/
@[simp]
theorem map_map_symm (q' : SemiboundedForm 𝕜 H') : (q'.map U.symm).map U = q' := by
  simpa using q'.map_symm_map U.symm

/-- **Unitary transport keeps the lower bounds.** -/
@[simp]
theorem isLowerBound_map_iff {γ : ℝ} : (q.map U).IsLowerBound γ ↔ q.IsLowerBound γ := by
  rw [isLowerBound_iff, isLowerBound_iff, ← (q.mapDomainEquiv U).forall_congr_right]
  simp

/-- **Unitary transport keeps the admissible shifts.** -/
@[simp]
theorem isAdmissibleShift_map_iff {α : ℝ} :
    (q.map U).IsAdmissibleShift α ↔ q.IsAdmissibleShift α := by
  simp [isAdmissibleShift_iff]

variable {α : ℝ} (hα : q.IsAdmissibleShift α)

/-- The form spaces of `q` and of its unitary transport are isometric. -/
def mapFormSpaceEquiv :
    q.FormSpace α hα ≃ₗᵢ[𝕜] (q.map U).FormSpace α ((q.isAdmissibleShift_map_iff U).mpr hα) :=
  LinearEquiv.isometryOfInner
    ((q.toFormSpace hα).symm ≪≫ₗ q.mapDomainEquiv U ≪≫ₗ
      (q.map U).toFormSpace ((q.isAdmissibleShift_map_iff U).mpr hα))
    fun x y ↦ by
      obtain ⟨u, rfl⟩ := (q.toFormSpace hα).surjective x
      obtain ⟨v, rfl⟩ := (q.toFormSpace hα).surjective y
      simp [shiftedInner_def, U.inner_map_map]

/-- The isometry of form spaces sends the class of `u` to the class of `U u`. -/
@[simp]
theorem mapFormSpaceEquiv_toFormSpace (u : q.domain) :
    q.mapFormSpaceEquiv U hα (q.toFormSpace hα u) =
      (q.map U).toFormSpace ((q.isAdmissibleShift_map_iff U).mpr hα) (q.mapDomainEquiv U u) := by
  simp [mapFormSpaceEquiv]

/-- The inverse of the isometry of form spaces sends the class of `u` to the class of `U⁻¹ u`. -/
@[simp]
theorem mapFormSpaceEquiv_symm_toFormSpace (u : (q.map U).domain) :
    (q.mapFormSpaceEquiv U hα).symm
        ((q.map U).toFormSpace ((q.isAdmissibleShift_map_iff U).mpr hα) u) =
      q.toFormSpace hα ((q.mapDomainEquiv U).symm u) := by
  rw [LinearIsometryEquiv.symm_apply_eq, mapFormSpaceEquiv_toFormSpace,
    LinearEquiv.apply_symm_apply]

/-- The isometry of form spaces sends the underlying vector `u` of the form domain to `U u`. -/
@[simp]
theorem toFormSpace_symm_mapFormSpaceEquiv (x : q.FormSpace α hα) :
    ((q.map U).toFormSpace ((q.isAdmissibleShift_map_iff U).mpr hα)).symm
        (q.mapFormSpaceEquiv U hα x) =
      q.mapDomainEquiv U ((q.toFormSpace hα).symm x) := by
  obtain ⟨u, rfl⟩ := (q.toFormSpace hα).surjective x
  rw [mapFormSpaceEquiv_toFormSpace, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

/-- The isometry of form spaces commutes with the inclusions into `H` and `H'`. -/
theorem inclusion_mapFormSpaceEquiv (x : q.FormSpace α hα) :
    (q.map U).inclusion ((q.isAdmissibleShift_map_iff U).mpr hα) (q.mapFormSpaceEquiv U hα x) =
      U (q.inclusion hα x) := by
  obtain ⟨u, rfl⟩ := (q.toFormSpace hα).surjective x
  rw [mapFormSpaceEquiv_toFormSpace, inclusion_toFormSpace, inclusion_toFormSpace,
    coe_mapDomainEquiv]

/-- **Unitary transport keeps closedness.** -/
@[simp]
theorem isClosed_map_iff : (q.map U).IsClosed ↔ q.IsClosed := by
  obtain ⟨α, hα⟩ := q.exists_isAdmissibleShift
  rw [isClosed_iff_completeSpace _ hα,
    isClosed_iff_completeSpace _ ((q.isAdmissibleShift_map_iff U).mpr hα)]
  exact (completeSpace_congr (e := (q.mapFormSpaceEquiv U hα).toLinearEquiv.toEquiv)
    (q.mapFormSpaceEquiv U hα).isometry.isUniformEmbedding).symm

/-- The form domain of the unitary transport is dense exactly when the form domain is. -/
theorem dense_map_domain_iff :
    Dense ((q.map U).domain : Set H') ↔ Dense (q.domain : Set H) := by
  rw [map_domain, Submodule.map_coe]
  exact U.toHomeomorph.isDenseEmbedding.dense_image

/-- **The operator of a unitary transport.** The unitary transport `q.map U` represents the unitary
conjugate `U A U⁻¹` of the operator `A` represented by `q`. -/
theorem operator_map (hd : Dense (q.domain : Set H)) :
    (q.map U).operator ((q.dense_map_domain_iff U).mpr hd) =
      (q.operator hd).conj U.toLinearEquiv := by
  refine LinearPMap.eq_of_eq_graph (Submodule.ext fun ⟨x, h⟩ ↦ ?_)
  rw [LinearPMap.mem_graph_conj_iff, mem_graph_operator_iff, mem_graph_operator_iff,
    ← (q.mapDomainEquiv U).exists_congr_right]
  refine exists_congr fun u ↦ and_congr ?_ ?_
  · simp [U.eq_symm_apply]
  · rw [← (q.mapDomainEquiv U).forall_congr_right]
    refine forall_congr' fun v ↦ ?_
    simp [← U.inner_map_map]

end Map

end SemiboundedForm

end TauCeti
