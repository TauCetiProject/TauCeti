/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FixedPointIndex.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import TauCeti.Analysis.Calculus.Sard.EqualDimension
import TauCeti.LinearAlgebra.Determinant.Basic

/-!
# Commutativity of the fixed-point index

Let `E₁` and `E₂` be finite-dimensional real normed spaces, `U ⊆ E₁` and `V ⊆ E₂` open sets, and
`φ : E₁ → E₂`, `ψ : E₂ → E₁` maps differentiable on `U` and on `V`. The composite `ψ ∘ φ` is a
self-map of the open set `U ∩ φ⁻¹(V)` of `E₁` and `φ ∘ ψ` a self-map of the open set
`V ∩ ψ⁻¹(U)` of `E₂`, and this file proves that they have the same fixed-point index
(`ContinuousMap.fixedPointIndex_comp_comm`):

`i(ψ ∘ φ) = i(φ ∘ ψ)`.

Neither composite is assumed to map its domain into itself, and the two spaces may have different
dimensions. The maps `φ` and `ψ` are inverse bijections between the two fixed sets, so one is
compact exactly when the other is; when they are not compact both indices vanish.

This is the commutativity property of the classical fixed-point index. Applied with `φ = h ∘ f`
and `ψ = h⁻¹` for a diffeomorphism `h` of open sets, it gives `i(h ∘ f ∘ h⁻¹) = i(f)`: the index
of a self-map of a manifold does not depend on the chart in which it is computed.

The proof perturbs `ψ` to `ψ + v` for a small vector `v`. Let `C ⊆ V ∩ ψ⁻¹(U)` be a compact
neighbourhood of the fixed points of `φ ∘ ψ`. For `v` small, the homotopies `ψ ∘ φ + t v` and
`φ ∘ (ψ + t v)`, `t ∈ [0, 1]`, have no fixed points over the boundary of `C`, so their fixed sets
are compact and the indices do not change (`ContinuousMap.fixedPointIndex_eq_of_homotopy`). By
Sard's theorem (`TauCeti.dense_setOf_forall_surjective_fderiv`) `v` can be chosen to be a regular
value of `z ↦ z - ψ (φ z)`; then every fixed point of `ψ ∘ φ + v` is nondegenerate. The fixed
points of the two perturbed composites correspond under `φ` and `ψ + v`, and at corresponding
points the derivatives are `B A` and `A B` for `A = dφ` and `B = dψ`, which have
`det (1 - B A) = det (1 - A B)` (`LinearMap.det_one_sub_comp_comm`). So both indices are the same
sum of signs (`ContinuousMap.fixedPointIndex_eq_sum_sign_det`).

## Main results

* `ContinuousMap.fixedPointIndex_comp_comm`: the fixed-point indices of `ψ ∘ φ` and `φ ∘ ψ` on
  their natural domains agree.

## References

* A. Dold, *Lectures on Algebraic Topology*, Springer, 1972, Chapter VII, §5 (the commutativity
  property of the fixed-point index).
* A. Dold, *Fixed point index and fixed point theorem for Euclidean neighborhood retracts*,
  Topology 4 (1965), 1–8.
-/

public section

noncomputable section

open Function Metric Module Set Topology TopologicalSpace

namespace ContinuousMap

variable {E₁ E₂ : Type} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  {φ : E₁ → E₂} {ψ : E₂ → E₁} {U U' : Opens E₁} {V V' : Opens E₂}

/-! ### The fixed points of the two composites -/

omit [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂] in
/-- The fixed points of `φ ∘ ψ` on `V ∩ ψ⁻¹(U)` are the images under `φ` of the fixed points of
`ψ ∘ φ` on `U ∩ φ⁻¹(V)`. -/
private theorem image_val_setOf_apply_eq (hU' : (U' : Set E₁) = (U : Set E₁) ∩ φ ⁻¹' V)
    (hV' : (V' : Set E₂) = (V : Set E₂) ∩ ψ ⁻¹' U) {k : C(U', E₁)}
    (hk : ∀ z : U', k z = ψ (φ z)) {l : C(V', E₂)} (hl : ∀ w : V', l w = φ (ψ w)) :
    Subtype.val '' {w | l w = w} = φ '' (Subtype.val '' {z | k z = z}) := by
  have hU'm (z : E₁) : z ∈ U' ↔ z ∈ U ∧ φ z ∈ V := by
    rw [← SetLike.mem_coe, hU']
    rfl
  have hV'm (w : E₂) : w ∈ V' ↔ w ∈ V ∧ ψ w ∈ U := by
    rw [← SetLike.mem_coe, hV']
    rfl
  ext w
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [mem_ofPred_eq, hl] at hw
    have hz : ψ w ∈ U' := (hU'm _).2 ⟨((hV'm w).1 w.2).2, by rw [hw]; exact ((hV'm w).1 w.2).1⟩
    refine ⟨ψ w, ⟨⟨ψ w, hz⟩, ?_, rfl⟩, hw⟩
    rw [mem_ofPred_eq, hk, hw]
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    rw [mem_ofPred_eq, hk] at hz
    have hw : φ z ∈ V' := (hV'm _).2 ⟨((hU'm z).1 z.2).2, by rw [hz]; exact ((hU'm z).1 z.2).1⟩
    refine ⟨⟨φ z, hw⟩, ?_, rfl⟩
    rw [mem_ofPred_eq, hl, hz]

omit [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂] in
/-- If `ψ ∘ φ` has a compact fixed set on `U ∩ φ⁻¹(V)`, so does `φ ∘ ψ` on `V ∩ ψ⁻¹(U)`. -/
private theorem isCompact_setOf_apply_eq (hφ : ContinuousOn φ U)
    (hU' : (U' : Set E₁) = (U : Set E₁) ∩ φ ⁻¹' V)
    (hV' : (V' : Set E₂) = (V : Set E₂) ∩ ψ ⁻¹' U) {k : C(U', E₁)}
    (hk : ∀ z : U', k z = ψ (φ z)) {l : C(V', E₂)} (hl : ∀ w : V', l w = φ (ψ w))
    (h : IsCompact {z | k z = z}) : IsCompact {w | l w = w} := by
  rw [Subtype.isCompact_iff, image_val_setOf_apply_eq hU' hV' hk hl]
  refine (Subtype.isCompact_iff.1 h).image_of_continuousOn (hφ.mono ?_)
  rintro _ ⟨z, -, rfl⟩
  have hz : (z : E₁) ∈ (U' : Set E₁) := z.2
  rw [hU'] at hz
  exact hz.1

/-! ### Nondegenerate fixed points -/

/-- **Sylvester's determinant identity** `det (1 - X Y) = det (1 - Y X)` for continuous linear
maps between two spaces, from the Weinstein–Aronszajn identity `LinearMap.det_one_add_comp_comm`
applied to `-X` and `Y`. -/
private theorem det_one_sub_comp_comm (X : E₂ →L[ℝ] E₁) (Y : E₁ →L[ℝ] E₂) :
    (1 - X.comp Y).det = (1 - Y.comp X).det := by
  have h := LinearMap.det_one_add_comp_comm (-(X : E₂ →ₗ[ℝ] E₁)) (Y : E₁ →ₗ[ℝ] E₂)
  simp only [LinearMap.neg_comp, LinearMap.comp_neg, ← sub_eq_add_neg] at h
  simpa [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_sub,
    ContinuousLinearMap.toLinearMap_one, ContinuousLinearMap.coe_comp] using h

/-- Commutativity of the fixed-point index when `ψ ∘ φ` has a compact set of nondegenerate fixed
points: both indices are then the same finite sum of signs. -/
private theorem fixedPointIndex_comp_comm_of_det_ne_zero (hφ : DifferentiableOn ℝ φ U)
    (hψ : DifferentiableOn ℝ ψ V) (hU' : (U' : Set E₁) = (U : Set E₁) ∩ φ ⁻¹' V)
    (hV' : (V' : Set E₂) = (V : Set E₂) ∩ ψ ⁻¹' U) (k : C(U', E₁))
    (hk : ∀ z : U', k z = ψ (φ z)) (l : C(V', E₂)) (hl : ∀ w : V', l w = φ (ψ w))
    (hK : IsCompact {z | k z = z})
    (hdet : ∀ z : U', k z = z → (1 - (fderiv ℝ ψ (φ z)).comp (fderiv ℝ φ z)).det ≠ 0) :
    k.fixedPointIndex = l.fixedPointIndex := by
  have hU'm (z : U') : (z : E₁) ∈ U ∧ φ z ∈ V := by
    have hz : (z : E₁) ∈ (U' : Set E₁) := z.2
    rwa [hU'] at hz
  have hV'm (w : V') : (w : E₂) ∈ V ∧ ψ w ∈ U := by
    have hw : (w : E₂) ∈ (V' : Set E₂) := w.2
    rwa [hV'] at hw
  have hdk (z : U') : HasFDerivAt (fun x ↦ ψ (φ x)) ((fderiv ℝ ψ (φ z)).comp (fderiv ℝ φ z)) z :=
    (hψ.differentiableAt (V.isOpen.mem_nhds (hU'm z).2)).hasFDerivAt.comp (z : E₁)
      (hφ.differentiableAt (U.isOpen.mem_nhds (hU'm z).1)).hasFDerivAt
  have hdl (w : V') : HasFDerivAt (fun y ↦ φ (ψ y)) ((fderiv ℝ φ (ψ w)).comp (fderiv ℝ ψ w)) w :=
    (hφ.differentiableAt (U.isOpen.mem_nhds (hV'm w).2)).hasFDerivAt.comp (w : E₂)
      (hψ.differentiableAt (V.isOpen.mem_nhds (hV'm w).1)).hasFDerivAt
  -- A fixed point `w` of `l` comes from the fixed point `ψ w` of `k`, where `φ (ψ w) = w`.
  have hψU' (w : V') (hw : l w = w) : ψ w ∈ U' := by
    rw [← SetLike.mem_coe, hU']
    exact ⟨(hV'm w).2, by rw [mem_preimage, ← hl, hw]; exact (hV'm w).1⟩
  have hdet' (w : V') (hw : l w = w) :
      (1 - (fderiv ℝ φ (ψ w)).comp (fderiv ℝ ψ w)).det ≠ 0 := by
    have h := hdet ⟨ψ w, hψU' w hw⟩ (by rw [hk, ← hl, hw])
    rw [show φ (ψ w) = w by rw [← hl, hw]] at h
    rwa [det_one_sub_comp_comm] at h
  have hK' := isCompact_setOf_apply_eq hφ.continuousOn hU' hV' hk hl hK
  have hfin := k.finite_setOf_apply_eq hK (fun z ↦ (hk z).symm)
    (f' := fun x ↦ (fderiv ℝ ψ (φ x)).comp (fderiv ℝ φ x)) (fun z _ ↦ hdk z) hdet
  have hfin' := l.finite_setOf_apply_eq hK' (fun w ↦ (hl w).symm)
    (f' := fun y ↦ (fderiv ℝ φ (ψ y)).comp (fderiv ℝ ψ y)) (fun w _ ↦ hdl w) hdet'
  rw [k.fixedPointIndex_eq_sum_sign_det hfin (fun z ↦ (hk z).symm)
      (f' := fun x ↦ (fderiv ℝ ψ (φ x)).comp (fderiv ℝ φ x)) (fun z _ ↦ hdk z) hdet,
    l.fixedPointIndex_eq_sum_sign_det hfin' (fun w ↦ (hl w).symm)
      (f' := fun y ↦ (fderiv ℝ φ (ψ y)).comp (fderiv ℝ ψ y)) (fun w _ ↦ hdl w) hdet']
  -- The fixed points of `k` and `l` correspond under `φ` and `ψ`.
  have hφV' (z : U') (hz : k z = z) : φ z ∈ V' := by
    rw [← SetLike.mem_coe, hV']
    exact ⟨(hU'm z).2, by rw [mem_preimage, ← hk, hz]; exact (hU'm z).1⟩
  refine Finset.sum_bij' (fun z hz ↦ ⟨φ z, hφV' z (hfin.mem_toFinset.1 hz)⟩)
    (fun w hw ↦ ⟨ψ w, hψU' w (hfin'.mem_toFinset.1 hw)⟩) (fun z hz ↦ ?_) (fun w hw ↦ ?_)
    (fun z hz ↦ ?_) (fun w hw ↦ ?_) (fun z hz ↦ ?_)
  · rw [hfin'.mem_toFinset, mem_ofPred_eq]
    exact (hl _).trans (congrArg φ ((hk z).symm.trans (hfin.mem_toFinset.1 hz)))
  · rw [hfin.mem_toFinset, mem_ofPred_eq]
    exact (hk _).trans (congrArg ψ ((hl w).symm.trans (hfin'.mem_toFinset.1 hw)))
  · exact Subtype.ext ((hk z).symm.trans (hfin.mem_toFinset.1 hz))
  · exact Subtype.ext ((hl w).symm.trans (hfin'.mem_toFinset.1 hw))
  · have hz' : ψ (φ z) = z := by rw [← hk, hfin.mem_toFinset.1 hz]
    dsimp only
    rw [hz', det_one_sub_comp_comm]

/-! ### Perturbation -/

omit [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂] in
/-- Choice of the size of the perturbation. Let `C` be a compact set with `C ⊆ V` and
`ψ(C) ⊆ U`, such that the fixed points of `φ ∘ ψ` in `C` lie in its interior. For vectors `u`
smaller than some `η > 0`, the translates `ψ w + u`, `w ∈ C`, stay in `U`, and the fixed points
in `C` of `φ ∘ (ψ + u)` still lie in the interior of `C`. -/
private theorem exists_pos_forall_norm_lt (hφ : ContinuousOn φ U) (hψ : ContinuousOn ψ V)
    {C : Set E₂} (hC : IsCompact C) (hCV : ∀ w ∈ C, w ∈ V ∧ ψ w ∈ U)
    (hfix : ∀ w ∈ C, φ (ψ w) = w → w ∈ interior C) :
    ∃ η > 0, ∀ w ∈ C, ∀ u : E₁, ‖u‖ < η →
      ψ w + u ∈ U ∧ (φ (ψ w + u) = w → w ∈ interior C) := by
  have hT : IsCompact (ψ '' C) := hC.image_of_continuousOn (hψ.mono fun w hw ↦ (hCV w hw).1)
  obtain ⟨ε, hε, hεU⟩ := hT.exists_cthickening_subset_open U.isOpen
    (image_subset_iff.2 fun w hw ↦ (hCV w hw).2)
  -- The displacement `w ↦ ‖w - φ (ψ w)‖` is bounded below by some `δ > 0` on `C \ interior C`,
  -- which contains no fixed point of `φ ∘ ψ`.
  have hcont : ContinuousOn (fun w ↦ ‖w - φ (ψ w)‖) (C \ interior C) :=
    (continuousOn_id.sub (hφ.comp (hψ.mono fun w (hw : w ∈ C \ interior C) ↦ (hCV w hw.1).1)
      fun w (hw : w ∈ C \ interior C) ↦ (hCV w hw.1).2)).norm
  obtain ⟨δ, hδ, hδC⟩ := (hC.diff isOpen_interior).exists_forall_le' hcont
    (a := 0) fun w hw ↦ norm_pos_iff.2 (sub_ne_zero.2 fun h ↦ hw.2 (hfix w hw.1 h.symm))
  obtain ⟨η, hη, hηφ⟩ := Metric.uniformContinuousOn_iff.1
    (hT.cthickening.uniformContinuousOn_of_continuous (hφ.mono hεU)) δ hδ
  refine ⟨min η ε, lt_min hη hε, fun w hw u hu ↦ ?_⟩
  have hdist : dist (ψ w + u) (ψ w) = ‖u‖ := by rw [dist_eq_norm, add_sub_cancel_left]
  have hmem : ψ w + u ∈ cthickening ε (ψ '' C) :=
    mem_cthickening_of_dist_le _ (ψ w) ε _ (mem_image_of_mem ψ hw)
      (hdist ▸ hu.le.trans (min_le_right _ _))
  refine ⟨hεU hmem, fun hfw ↦ by_contra fun hint ↦ ?_⟩
  have h := hηφ _ hmem _ (self_subset_cthickening _ (mem_image_of_mem ψ hw))
    (hdist ▸ hu.trans_le (min_le_left _ _))
  rw [hfw, dist_eq_norm] at h
  exact (hδC w ⟨hw, hint⟩).not_gt h

omit [FiniteDimensional ℝ E₁] in
/-- Multiples `t v` with `t ∈ [0, 1]` of a vector `v` of norm less than `η` have norm less
than `η`. -/
private theorem norm_smul_lt {η : ℝ} {v : E₁} (hv : ‖v‖ < η) (t : unitInterval) :
    ‖(t : ℝ) • v‖ < η := by
  rw [norm_smul, Real.norm_of_nonneg t.2.1]
  exact (mul_le_of_le_one_left (norm_nonneg v) t.2.2).trans_lt hv

omit [FiniteDimensional ℝ E₁] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂] in
/-- The fixed points of the homotopy `φ ∘ (ψ + t v)`, `t ∈ [0, 1]`, over a compact set `C` as in
`exists_pos_forall_norm_lt`, for `v` smaller than the `η` chosen there: they form a compact set,
and they lie over the interior of `C`. -/
private theorem isCompact_setOf_comp_add_smul_eq {C : Set E₂} (hφ : ContinuousOn φ U)
    (hψ : ContinuousOn ψ V) (hC : IsCompact C) (hCV : ∀ w ∈ C, w ∈ V ∧ ψ w ∈ U) {η : ℝ}
    (hηC : ∀ w ∈ C, ∀ u : E₁, ‖u‖ < η → ψ w + u ∈ U ∧ (φ (ψ w + u) = w → w ∈ interior C))
    {v : E₁} (hv : ‖v‖ < η) :
    IsCompact {p : unitInterval × E₂ | p.2 ∈ C ∧ φ (ψ p.2 + (p.1 : ℝ) • v) = p.2} ∧
      ∀ p : unitInterval × E₂, p.2 ∈ C → φ (ψ p.2 + (p.1 : ℝ) • v) = p.2 → p.2 ∈ interior C := by
  have hsmall := norm_smul_lt hv
  refine ⟨?_, fun p hp h ↦ (hηC p.2 hp _ (hsmall p.1)).2 h⟩
  have hcont : ContinuousOn (fun p : unitInterval × E₂ ↦ φ (ψ p.2 + (p.1 : ℝ) • v) - p.2)
      (univ ×ˢ C) :=
    (hφ.comp ((hψ.comp continuousOn_snd
      fun p (hp : p ∈ (univ : Set unitInterval) ×ˢ C) ↦ (hCV p.2 hp.2).1).add
      ((continuous_subtype_val.comp continuous_fst).smul continuous_const).continuousOn)
      fun p (hp : p ∈ (univ : Set unitInterval) ×ˢ C) ↦ (hηC p.2 hp.2 _ (hsmall p.1)).1).sub
      continuousOn_snd
  have hclosed := hcont.preimage_isClosed_of_isClosed (isClosed_univ.prod hC.isClosed)
    (isClosed_singleton (x := (0 : E₂)))
  have heq : {p : unitInterval × E₂ | p.2 ∈ C ∧ φ (ψ p.2 + (p.1 : ℝ) • v) = p.2} =
      univ ×ˢ C ∩ (fun p : unitInterval × E₂ ↦ φ (ψ p.2 + (p.1 : ℝ) • v) - p.2) ⁻¹' {0} := by
    ext p
    simp [sub_eq_zero]
  rw [heq]
  exact (isCompact_univ.prod hC).of_isClosed_subset hclosed inter_subset_left

/-- The end map `f₁` of a homotopy `H` of self-maps of an open set whose fixed set
`{(t, z) | H (t, z) = z}` is compact has a compact fixed set. -/
private theorem isCompact_setOf_apply_eq_of_homotopy {X : Type*} [TopologicalSpace X]
    {W : Opens X} {f₀ f₁ : C(W, X)} (H : f₀.Homotopy f₁)
    (hH : IsCompact {p : unitInterval × W | H p = p.2}) : IsCompact {z | f₁ z = z} := by
  have h := (hH.inter_right ((isClosed_singleton (x := (1 : unitInterval))).prod
    isClosed_univ)).image continuous_snd
  convert h using 1
  ext z
  constructor
  · intro hz
    exact ⟨(1, z), ⟨by simpa using hz, by simp⟩, rfl⟩
  · rintro ⟨⟨t, z⟩, ⟨hp, ht, -⟩, rfl⟩
    rw [mem_singleton_iff] at ht
    subst ht
    simpa using hp

omit [FiniteDimensional ℝ E₁] in
/-- The homotopy `φ ∘ (ψ + t v)`, `t ∈ [0, 1]`, on the interior `W₂` of a compact set `C` as in
`exists_pos_forall_norm_lt`, for `v` smaller than the `η` chosen there: `φ ∘ ψ` and
`φ ∘ (ψ + v)` have the same fixed-point index on `W₂`, and the fixed set of `φ ∘ (ψ + v)` is
compact. -/
private theorem fixedPointIndex_eq_comp_add (hφ : ContinuousOn φ U) (hψ : ContinuousOn ψ V)
    {C : Set E₂} (hC : IsCompact C) (hCV : ∀ w ∈ C, w ∈ V ∧ ψ w ∈ U) {η : ℝ}
    (hηC : ∀ w ∈ C, ∀ u : E₁, ‖u‖ < η → ψ w + u ∈ U ∧ (φ (ψ w + u) = w → w ∈ interior C))
    {v : E₁} (hv : ‖v‖ < η) {W₂ : Opens E₂} (hW₂ : (W₂ : Set E₂) = interior C) (l : C(W₂, E₂))
    (hl : ∀ w : W₂, l w = φ (ψ w)) (lv : C(W₂, E₂)) (hlv : ∀ w : W₂, lv w = φ (ψ w + v)) :
    l.fixedPointIndex = lv.fixedPointIndex ∧ IsCompact {w | lv w = w} := by
  obtain ⟨hF, hFC⟩ := isCompact_setOf_comp_add_smul_eq hφ hψ hC hCV hηC hv
  have hWC (w : W₂) : (w : E₂) ∈ C := interior_subset (hW₂ ▸ w.2)
  let H : l.Homotopy lv :=
    { toFun := fun p ↦ φ (ψ p.2 + (p.1 : ℝ) • v)
      continuous_toFun := hφ.comp_continuous ((hψ.comp_continuous
          (continuous_subtype_val.comp continuous_snd) fun p ↦ (hCV _ (hWC p.2)).1).add
          ((continuous_subtype_val.comp continuous_fst).smul continuous_const))
        fun p ↦ (hηC _ (hWC p.2) _ (norm_smul_lt hv p.1)).1
      map_zero_left := fun w ↦ by simp [hl]
      map_one_left := fun w ↦ by simp [hlv] }
  -- The fixed set of `H`, read in `[0, 1] × E₂`, is the compact set of
  -- `isCompact_setOf_comp_add_smul_eq`.
  have hH : IsCompact {p : unitInterval × W₂ | H p = p.2} := by
    rw [(IsEmbedding.id.prodMap IsEmbedding.subtypeVal).isCompact_iff]
    convert hF using 1
    ext ⟨t, w⟩
    constructor
    · rintro ⟨⟨t', w'⟩, hp, he⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact ⟨hWC w', hp⟩
    · rintro ⟨hwC, hp⟩
      have hw : w ∈ (W₂ : Set E₂) := hW₂ ▸ hFC (t, w) hwC hp
      exact ⟨(t, ⟨w, hw⟩), hp, rfl⟩
  exact ⟨fixedPointIndex_eq_of_homotopy H hH, isCompact_setOf_apply_eq_of_homotopy H hH⟩

omit [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂] in
/-- The homotopy `ψ ∘ φ + t v`, `t ∈ [0, 1]`, on `W₁ = U ∩ φ⁻¹(W₂)`, where `W₂` is the interior
of a compact set `C` as in `exists_pos_forall_norm_lt`, for `v` smaller than the `η` chosen
there: `ψ ∘ φ` and `ψ ∘ φ + v` have the same fixed-point index on `W₁`, and the fixed set of
`ψ ∘ φ + v` is compact. Its fixed points are the images under `ψ + t v` of those of
`φ ∘ (ψ + t v)`. -/
private theorem fixedPointIndex_eq_comp_add_const (hφ : ContinuousOn φ U)
    (hψ : ContinuousOn ψ V) {C : Set E₂} (hC : IsCompact C) (hCV : ∀ w ∈ C, w ∈ V ∧ ψ w ∈ U)
    {η : ℝ}
    (hηC : ∀ w ∈ C, ∀ u : E₁, ‖u‖ < η → ψ w + u ∈ U ∧ (φ (ψ w + u) = w → w ∈ interior C))
    {v : E₁} (hv : ‖v‖ < η) {W₂ : Opens E₂} (hW₂ : (W₂ : Set E₂) = interior C) {W₁ : Opens E₁}
    (hW₁ : (W₁ : Set E₁) = (U : Set E₁) ∩ φ ⁻¹' W₂) (k : C(W₁, E₁))
    (hk : ∀ z : W₁, k z = ψ (φ z)) (kv : C(W₁, E₁)) (hkv : ∀ z : W₁, kv z = ψ (φ z) + v) :
    k.fixedPointIndex = kv.fixedPointIndex ∧ IsCompact {z | kv z = z} := by
  obtain ⟨hF, hFC⟩ := isCompact_setOf_comp_add_smul_eq hφ hψ hC hCV hηC hv
  have hW₁m (z : W₁) : (z : E₁) ∈ U ∧ φ z ∈ C := by
    have hz : (z : E₁) ∈ (W₁ : Set E₁) := z.2
    rw [hW₁] at hz
    exact ⟨hz.1, interior_subset (hW₂ ▸ hz.2)⟩
  let H : k.Homotopy kv :=
    { toFun := fun p ↦ ψ (φ p.2) + (p.1 : ℝ) • v
      continuous_toFun := (hψ.comp_continuous (hφ.comp_continuous
          (continuous_subtype_val.comp continuous_snd) fun p ↦ (hW₁m p.2).1)
          fun p ↦ (hCV _ (hW₁m p.2).2).1).add
        ((continuous_subtype_val.comp continuous_fst).smul continuous_const)
      map_zero_left := fun z ↦ by simp [hk]
      map_one_left := fun z ↦ by simp [hkv] }
  -- The fixed set of `H`, read in `[0, 1] × E₁`, is the image of that of `φ ∘ (ψ + t v)` under
  -- `(t, w) ↦ (t, ψ w + t v)`.
  have hG : IsCompact ((fun p : unitInterval × E₂ ↦ (p.1, ψ p.2 + (p.1 : ℝ) • v)) ''
      {p : unitInterval × E₂ | p.2 ∈ C ∧ φ (ψ p.2 + (p.1 : ℝ) • v) = p.2}) :=
    hF.image_of_continuousOn (continuous_fst.continuousOn.prodMk
      ((hψ.comp continuousOn_snd fun p (hp : p ∈ {p : unitInterval × E₂ |
        p.2 ∈ C ∧ φ (ψ p.2 + (p.1 : ℝ) • v) = p.2}) ↦ (hCV _ hp.1).1).add
        ((continuous_subtype_val.comp continuous_fst).smul continuous_const).continuousOn))
  have hH : IsCompact {p : unitInterval × W₁ | H p = p.2} := by
    rw [(IsEmbedding.id.prodMap IsEmbedding.subtypeVal).isCompact_iff]
    convert hG using 1
    ext ⟨t, z⟩
    constructor
    · rintro ⟨⟨t', z'⟩, hp, he⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      -- `H (t, z)` is `ψ (φ z) + t v` by construction.
      have hp' : ψ (φ z') + (t' : ℝ) • v = z' := hp
      refine ⟨(t', φ z'), ⟨(hW₁m z').2, by rw [hp']⟩, ?_⟩
      simp only [id_eq, hp']
    · rintro ⟨⟨t', w⟩, ⟨hwC, hp⟩, he⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      have hw : w ∈ (W₂ : Set E₂) := hW₂ ▸ hFC (t', w) hwC hp
      have hz : ψ w + (t' : ℝ) • v ∈ (W₁ : Set E₁) := by
        rw [hW₁]
        exact ⟨(hηC w hwC _ (norm_smul_lt hv t')).1, by rw [mem_preimage, hp]; exact hw⟩
      refine ⟨(t', ⟨_, hz⟩), ?_, rfl⟩
      -- `H (t, z)` is `ψ (φ z) + t v` by construction.
      change ψ (φ (ψ w + (t' : ℝ) • v)) + (t' : ℝ) • v = ψ w + (t' : ℝ) • v
      rw [hp]
  exact ⟨fixedPointIndex_eq_of_homotopy H hH, isCompact_setOf_apply_eq_of_homotopy H hH⟩

/-- **Regular values exist near `0`**: for a map `g` differentiable on a set `W`, with derivative
`g' z` at `z`, there are vectors `v` of arbitrarily small norm such that `1 - g' z` is invertible
at every `z ∈ W` with `z - g z = v`. This is Sard's theorem for `z ↦ z - g z`. -/
private theorem exists_norm_lt_forall_det_ne_zero {W : Set E₁} {g : E₁ → E₁}
    {g' : E₁ → E₁ →L[ℝ] E₁} (hg : ∀ z ∈ W, HasFDerivAt g (g' z) z) {η : ℝ} (hη : 0 < η) :
    ∃ v : E₁, ‖v‖ < η ∧ ∀ z ∈ W, z - g z = v → (1 - g' z).det ≠ 0 := by
  let _ : MeasurableSpace E₁ := borel E₁
  have _ : BorelSpace E₁ := ⟨rfl⟩
  have hD (z : E₁) (hz : z ∈ W) : HasFDerivAt (fun x ↦ x - g x) (1 - g' z) z :=
    (hasFDerivAt_id z).sub (hg z hz)
  obtain ⟨v, hv, hvη⟩ := (TauCeti.dense_setOf_forall_surjective_fderiv (f := fun x ↦ x - g x)
    (s := W) (fun z hz ↦ (hD z hz).differentiableAt) rfl).exists_mem_open isOpen_ball
    ⟨0, mem_ball_self hη⟩
  refine ⟨v, mem_ball_zero_iff.1 hvη, fun z hz hzv ↦ ?_⟩
  have hs : Surjective ⇑(1 - g' z) := (hD z hz).fderiv ▸ hv z hz hzv
  exact (LinearMap.isUnit_det _ ((Module.End.isUnit_iff _).2
    ⟨LinearMap.injective_iff_surjective.2 hs, hs⟩)).ne_zero

/-- Commutativity of the fixed-point index, given a compact neighbourhood `C ⊆ V ∩ ψ⁻¹(U)` of the
fixed points of `φ ∘ ψ` and a size `η` of perturbations of `ψ` as in
`exists_pos_forall_norm_lt`. -/
private theorem fixedPointIndex_comp_comm_of_isCompact (hφ : DifferentiableOn ℝ φ U)
    (hψ : DifferentiableOn ℝ ψ V) (hU' : (U' : Set E₁) = (U : Set E₁) ∩ φ ⁻¹' V)
    (hV' : (V' : Set E₂) = (V : Set E₂) ∩ ψ ⁻¹' U) (k : C(U', E₁))
    (hk : ∀ z : U', k z = ψ (φ z)) (l : C(V', E₂)) (hl : ∀ w : V', l w = φ (ψ w))
    {C : Set E₂} (hC : IsCompact C) (hCV : ∀ w ∈ C, w ∈ V ∧ ψ w ∈ U) (hCV' : C ⊆ V')
    (hKC : Subtype.val '' {w | l w = w} ⊆ interior C) {η : ℝ} (hη : 0 < η)
    (hηC : ∀ w ∈ C, ∀ u : E₁, ‖u‖ < η → ψ w + u ∈ U ∧ (φ (ψ w + u) = w → w ∈ interior C)) :
    k.fixedPointIndex = l.fixedPointIndex := by
  -- The open sets `W₂ = interior C ⊆ V'` and `W₁ = U ∩ φ⁻¹(W₂) ⊆ U'` contain the fixed points.
  obtain ⟨W₂, hW₂⟩ : ∃ W : Opens E₂, (W : Set E₂) = interior C := ⟨⟨_, isOpen_interior⟩, rfl⟩
  obtain ⟨W₁, hW₁⟩ : ∃ W : Opens E₁, (W : Set E₁) = (U : Set E₁) ∩ φ ⁻¹' W₂ :=
    ⟨⟨_, hφ.continuousOn.isOpen_inter_preimage U.isOpen W₂.isOpen⟩, rfl⟩
  have hW₂C (w : W₂) : (w : E₂) ∈ C := interior_subset (hW₂ ▸ w.2)
  have hW₁m (z : W₁) : (z : E₁) ∈ U ∧ φ z ∈ W₂ := by
    have hz : (z : E₁) ∈ (W₁ : Set E₁) := z.2
    rwa [hW₁] at hz
  have hW₂V' : W₂ ≤ V' := fun w hw ↦ hCV' (hW₂C ⟨w, hw⟩)
  have hW₁U' : W₁ ≤ U' := fun z hz ↦ by
    rw [← SetLike.mem_coe, hU']
    exact ⟨(hW₁m ⟨z, hz⟩).1, (hCV _ (hW₂C ⟨_, (hW₁m ⟨z, hz⟩).2⟩)).1⟩
  have hkW (z : U') (hz : k z = z) : (z : E₁) ∈ W₁ := by
    rw [← SetLike.mem_coe, hW₁, hW₂]
    refine ⟨(hU' ▸ z.2 : (z : E₁) ∈ (U : Set E₁) ∩ φ ⁻¹' V).1, hKC ?_⟩
    rw [image_val_setOf_apply_eq hU' hV' hk hl]
    exact mem_image_of_mem φ ⟨z, hz, rfl⟩
  have hlW (w : V') (hw : l w = w) : (w : E₂) ∈ W₂ := by
    rw [← SetLike.mem_coe, hW₂]
    exact hKC ⟨w, hw, rfl⟩
  -- A regular value `v` of `z ↦ z - ψ (φ z)` on `W₁`, of norm less than `η`.
  have hψφV (z : W₁) : φ z ∈ V := (hCV _ (hW₂C ⟨_, (hW₁m z).2⟩)).1
  obtain ⟨v, hv, hreg⟩ := exists_norm_lt_forall_det_ne_zero (W := W₁)
    (g' := fun z ↦ (fderiv ℝ ψ (φ z)).comp (fderiv ℝ φ z)) (fun z hz ↦
      (hψ.differentiableAt (V.isOpen.mem_nhds (hψφV ⟨z, hz⟩))).hasFDerivAt.comp z
        (hφ.differentiableAt (U.isOpen.mem_nhds (hW₁m ⟨z, hz⟩).1)).hasFDerivAt) hη
  have hψv (w : W₂) : ψ w + v ∈ U := (hηC _ (hW₂C w) v hv).1
  let kv : C(W₁, E₁) := ⟨fun z ↦ ψ (φ z) + v, (hψ.continuousOn.comp_continuous
    (hφ.continuousOn.comp_continuous continuous_subtype_val fun z ↦ (hW₁m z).1) hψφV).add
    continuous_const⟩
  let lv : C(W₂, E₂) := ⟨fun w ↦ φ (ψ w + v), hφ.continuousOn.comp_continuous
    ((hψ.continuousOn.comp_continuous continuous_subtype_val fun w ↦ (hCV _ (hW₂C w)).1).add
      continuous_const) hψv⟩
  obtain ⟨hkv, hKv⟩ := fixedPointIndex_eq_comp_add_const hφ.continuousOn hψ.continuousOn hC hCV
    hηC hv hW₂ hW₁ (k.comp (inclusion hW₁U')) (fun z ↦ hk _) kv (fun _ ↦ rfl)
  obtain ⟨hlv, -⟩ := fixedPointIndex_eq_comp_add hφ.continuousOn hψ.continuousOn hC hCV hηC hv
    hW₂ (l.comp (inclusion hW₂V')) (fun w ↦ hl _) lv (fun _ ↦ rfl)
  rw [← k.fixedPointIndex_comp_inclusion hW₁U' hkW, ← l.fixedPointIndex_comp_inclusion hW₂V' hlW,
    hkv, hlv]
  -- The perturbed composites have nondegenerate fixed points.
  refine fixedPointIndex_comp_comm_of_det_ne_zero (ψ := fun w ↦ ψ w + v) hφ
    ((hψ.mono fun w hw ↦ (hCV _ (hW₂C ⟨w, hw⟩)).1).add_const v) hW₁ ?_ kv (fun _ ↦ rfl) lv
    (fun _ ↦ rfl) hKv fun z hz ↦ ?_
  · ext w
    exact ⟨fun hw ↦ ⟨hw, hψv ⟨w, hw⟩⟩, And.left⟩
  · rw [fderiv_add_const]
    exact hreg z z.2 (sub_eq_iff_eq_add'.2 hz.symm)

/-- **Commutativity of the fixed-point index.** Let `φ : E₁ → E₂` and `ψ : E₂ → E₁` be
differentiable on open sets `U ⊆ E₁` and `V ⊆ E₂`. The composite `ψ ∘ φ` is a self-map `k` of
`U' = U ∩ φ⁻¹(V)` and `φ ∘ ψ` a self-map `l` of `V' = V ∩ ψ⁻¹(U)`, and they have the same
fixed-point index: `i(ψ ∘ φ) = i(φ ∘ ψ)`. -/
theorem fixedPointIndex_comp_comm (hφ : DifferentiableOn ℝ φ U) (hψ : DifferentiableOn ℝ ψ V)
    (hU' : (U' : Set E₁) = (U : Set E₁) ∩ φ ⁻¹' V)
    (hV' : (V' : Set E₂) = (V : Set E₂) ∩ ψ ⁻¹' U) (k : C(U', E₁))
    (hk : ∀ z : U', k z = ψ (φ z)) (l : C(V', E₂)) (hl : ∀ w : V', l w = φ (ψ w)) :
    k.fixedPointIndex = l.fixedPointIndex := by
  by_cases hK : IsCompact {w | l w = w}
  swap
  · have hK' : ¬IsCompact {z | k z = z} := fun h ↦
      hK (isCompact_setOf_apply_eq hφ.continuousOn hU' hV' hk hl h)
    rw [k.fixedPointIndex_of_not_isCompact hK', l.fixedPointIndex_of_not_isCompact hK]
  -- A compact neighbourhood `C ⊆ V'` of the fixed points of `l`, and a size `η` of perturbations
  -- of `ψ` which create no fixed point of `φ ∘ ψ` over the boundary of `C`.
  obtain ⟨C, hC, hKC, hCV'⟩ := exists_compact_between (Subtype.isCompact_iff.1 hK) V'.isOpen
    (image_subset_iff.2 fun w _ ↦ w.2)
  have hCV (w : E₂) (hw : w ∈ C) : w ∈ V ∧ ψ w ∈ U := by
    have h : w ∈ (V' : Set E₂) := hCV' hw
    rwa [hV'] at h
  obtain ⟨η, hη, hηC⟩ := exists_pos_forall_norm_lt hφ.continuousOn hψ.continuousOn hC hCV
    fun w hw h ↦ hKC ⟨⟨w, hCV' hw⟩, (hl _).trans h, rfl⟩
  exact fixedPointIndex_comp_comm_of_isCompact hφ hψ hU' hV' k hk l hl hC hCV hCV' hKC hη hηC

end ContinuousMap
