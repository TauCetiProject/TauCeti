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
import TauCeti.Topology.Algebra.Module.Determinant

/-!
# Commutativity of the fixed-point index

Let `E₁` and `E₂` be finite-dimensional real normed spaces, `U ⊆ E₁` and `V ⊆ E₂` open sets, and
`φ : E₁ → E₂`, `ψ : E₂ → E₁` maps differentiable on `U` and on `V`. The composite `ψ ∘ φ`
restricts to a map from the open set `U ∩ φ⁻¹(V)` to `E₁` and `φ ∘ ψ` to a map from the open set
`V ∩ ψ⁻¹(U)` to `E₂`, and this file proves that they have the same fixed-point index
(`ContinuousMap.fixedPointIndex_comp_comm`):

`i(ψ ∘ φ) = i(φ ∘ ψ)`.

Neither composite is assumed to map its domain into itself, and the two spaces may have different
dimensions. The maps `φ` and `ψ` are inverse bijections between the two fixed sets, so one is
compact exactly when the other is; when they are not compact both indices vanish.

This is the commutativity property of the classical fixed-point index, here for differentiable
maps. Applied with `φ = h ∘ f` and `ψ = h⁻¹` for a diffeomorphism `h` of open sets and a map `f`
differentiable on its domain that maps its domain into the domain of `h`, it gives
`i(h ∘ f ∘ h⁻¹) = i(f)`. Its intended use is to show that an index of self-maps of a manifold,
computed in charts, does not depend on the chart.

The proof perturbs `ψ` to `ψ + v` for a small vector `v`. Let `C ⊆ V ∩ ψ⁻¹(U)` be a compact
neighbourhood of the fixed points of `φ ∘ ψ`. For `v` small, the homotopies `ψ ∘ φ + t v` and
`φ ∘ (ψ + t v)`, `t ∈ [0, 1]`, have no fixed points over the boundary of `C`, so their fixed sets
are compact and the indices do not change (`ContinuousMap.fixedPointIndex_eq_of_homotopy`). By
Sard's theorem (`TauCeti.dense_setOf_forall_surjective_fderiv`) `v` can be chosen to be a regular
value of `z ↦ z - ψ (φ z)`; then every fixed point of `ψ ∘ φ + v` is nondegenerate. The fixed
points of the two perturbed composites correspond under `φ` and `ψ + v`, and at corresponding
points the derivatives are `B A` and `A B` for `A = dφ` and `B = dψ`, which have
`det (1 - B A) = det (1 - A B)` (`ContinuousLinearMap.det_one_sub_comp_comm`). Sard's theorem
enters through `TauCeti.exists_norm_lt_forall_det_one_sub_ne_zero`. So both indices are the same
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
/-- A fixed point `w` of `φ ∘ ψ` in `V ∩ ψ⁻¹(U)` gives the point `ψ w` of `U ∩ φ⁻¹(V)`. With the
roles of `φ` and `ψ` exchanged, a fixed point `z` of `ψ ∘ φ` in `U ∩ φ⁻¹(V)` gives the point
`φ z` of `V ∩ ψ⁻¹(U)`. -/
private theorem apply_mem_of_apply_apply_eq (hU' : (U' : Set E₁) = (U : Set E₁) ∩ φ ⁻¹' V)
    (hV' : (V' : Set E₂) = (V : Set E₂) ∩ ψ ⁻¹' U) {w : E₂} (hw : w ∈ V') (hfix : φ (ψ w) = w) :
    ψ w ∈ U' :=
  hU'.superset ⟨(hV'.subset hw).2, by rw [mem_preimage, hfix]; exact (hV'.subset hw).1⟩

omit [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂] in
/-- The fixed points of `φ ∘ ψ` on `V ∩ ψ⁻¹(U)` are the images under `φ` of the fixed points of
`ψ ∘ φ` on `U ∩ φ⁻¹(V)`. -/
private theorem image_val_setOf_apply_eq (hU' : (U' : Set E₁) = (U : Set E₁) ∩ φ ⁻¹' V)
    (hV' : (V' : Set E₂) = (V : Set E₂) ∩ ψ ⁻¹' U) {k : C(U', E₁)}
    (hk : ∀ z : U', k z = ψ (φ z)) {l : C(V', E₂)} (hl : ∀ w : V', l w = φ (ψ w)) :
    Subtype.val '' {w | l w = w} = φ '' (Subtype.val '' {z | k z = z}) := by
  ext w
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [mem_ofPred_eq, hl] at hw
    refine ⟨ψ w, ⟨⟨ψ w, apply_mem_of_apply_apply_eq hU' hV' w.property hw⟩, ?_, rfl⟩, hw⟩
    rw [mem_ofPred_eq, hk, hw]
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    rw [mem_ofPred_eq, hk] at hz
    refine ⟨⟨φ z, apply_mem_of_apply_apply_eq hV' hU' z.property hz⟩, ?_, rfl⟩
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
  exact (hU'.subset z.property).1

/-! ### Nondegenerate fixed points -/

omit [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂] in
/-- The derivative of `ψ ∘ φ` at a point `z ∈ U` with `φ z ∈ V` is `dψ (φ z) ∘ dφ z`. -/
private theorem hasFDerivAt_comp_of_mem (hφ : DifferentiableOn ℝ φ U)
    (hψ : DifferentiableOn ℝ ψ V) {z : E₁} (hz : z ∈ U) (hφz : φ z ∈ V) :
    HasFDerivAt (fun x ↦ ψ (φ x)) ((fderiv ℝ ψ (φ z)).comp (fderiv ℝ φ z)) z :=
  (hψ.differentiableAt (V.isOpen.mem_nhds hφz)).hasFDerivAt.comp z
    (hφ.differentiableAt (U.isOpen.mem_nhds hz)).hasFDerivAt

omit [FiniteDimensional ℝ E₂] in
/-- If `ψ ∘ φ` has a compact set of nondegenerate fixed points on `U' = U ∩ φ⁻¹(V)`, this set is
finite and the fixed-point index is the sum over it of the signs of `det (1 - dψ dφ)`. -/
private theorem exists_finite_fixedPointIndex_eq_sum (hφ : DifferentiableOn ℝ φ U)
    (hψ : DifferentiableOn ℝ ψ V) (hU' : (U' : Set E₁) = (U : Set E₁) ∩ φ ⁻¹' V) (k : C(U', E₁))
    (hk : ∀ z : U', k z = ψ (φ z)) (hK : IsCompact {z | k z = z})
    (hdet : ∀ z : U', k z = z → (1 - (fderiv ℝ ψ (φ z)).comp (fderiv ℝ φ z)).det ≠ 0) :
    ∃ hfin : {z | k z = z}.Finite, k.fixedPointIndex = ∑ z ∈ hfin.toFinset,
      (SignType.sign (1 - (fderiv ℝ ψ (φ z)).comp (fderiv ℝ φ z)).det : ℤ) := by
  have hd (z : U') (_ : k z = z) :
      HasFDerivAt (fun x ↦ ψ (φ x)) ((fderiv ℝ ψ (φ z)).comp (fderiv ℝ φ z)) z :=
    hasFDerivAt_comp_of_mem hφ hψ (hU'.subset z.property).1 (hU'.subset z.property).2
  have hfin := k.finite_setOf_apply_eq hK (fun z ↦ (hk z).symm)
    (f' := fun x ↦ (fderiv ℝ ψ (φ x)).comp (fderiv ℝ φ x)) hd hdet
  exact ⟨hfin, k.fixedPointIndex_eq_sum_sign_det hfin (fun z ↦ (hk z).symm)
    (f' := fun x ↦ (fderiv ℝ ψ (φ x)).comp (fderiv ℝ φ x)) hd hdet⟩

/-- Commutativity of the fixed-point index when `ψ ∘ φ` has a compact set of nondegenerate fixed
points: both indices are then the same finite sum of signs. -/
private theorem fixedPointIndex_comp_comm_of_det_ne_zero (hφ : DifferentiableOn ℝ φ U)
    (hψ : DifferentiableOn ℝ ψ V) (hU' : (U' : Set E₁) = (U : Set E₁) ∩ φ ⁻¹' V)
    (hV' : (V' : Set E₂) = (V : Set E₂) ∩ ψ ⁻¹' U) (k : C(U', E₁))
    (hk : ∀ z : U', k z = ψ (φ z)) (l : C(V', E₂)) (hl : ∀ w : V', l w = φ (ψ w))
    (hK : IsCompact {z | k z = z})
    (hdet : ∀ z : U', k z = z → (1 - (fderiv ℝ ψ (φ z)).comp (fderiv ℝ φ z)).det ≠ 0) :
    k.fixedPointIndex = l.fixedPointIndex := by
  -- A fixed point `w` of `l` comes from the fixed point `ψ w` of `k`, where `φ (ψ w) = w`.
  have hψU' (w : V') (hw : l w = w) : ψ w ∈ U' :=
    apply_mem_of_apply_apply_eq hU' hV' w.property (by rw [← hl, hw])
  have hdet' (w : V') (hw : l w = w) :
      (1 - (fderiv ℝ φ (ψ w)).comp (fderiv ℝ ψ w)).det ≠ 0 := by
    have h := hdet ⟨ψ w, hψU' w hw⟩ (by rw [hk, ← hl, hw])
    rw [show φ (ψ w) = w by rw [← hl, hw]] at h
    rwa [ContinuousLinearMap.det_one_sub_comp_comm] at h
  obtain ⟨hfin, hkS⟩ := exists_finite_fixedPointIndex_eq_sum hφ hψ hU' k hk hK hdet
  obtain ⟨hfin', hlS⟩ := exists_finite_fixedPointIndex_eq_sum hψ hφ hV' l hl
    (isCompact_setOf_apply_eq hφ.continuousOn hU' hV' hk hl hK) hdet'
  rw [hkS, hlS]
  -- The fixed points of `k` and `l` correspond under `φ` and `ψ`.
  have hφV' (z : U') (hz : k z = z) : φ z ∈ V' :=
    apply_mem_of_apply_apply_eq hV' hU' z.property (by rw [← hk, hz])
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
    rw [hz', ContinuousLinearMap.det_one_sub_comp_comm]

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
  rw [norm_smul, Real.norm_of_nonneg t.property.1]
  exact (mul_le_of_le_one_left (norm_nonneg v) t.property.2).trans_lt hv

omit [FiniteDimensional ℝ E₁] in
/-- If `g` is continuous on `s`, then `(t, x) ↦ g x + t v` is continuous on `[0, 1] × s`. -/
private theorem continuousOn_add_smul {X : Type*} [TopologicalSpace X] {g : X → E₁} {s : Set X}
    (hg : ContinuousOn g s) (v : E₁) :
    ContinuousOn (fun p : unitInterval × X ↦ g p.2 + (p.1 : ℝ) • v) (univ ×ˢ s) :=
  (hg.comp continuousOn_snd mapsTo_snd_prod).add
    ((continuous_subtypeVal.comp continuous_fst).smul continuous_const).continuousOn

omit [FiniteDimensional ℝ E₁] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂] in
/-- For a compact set `C` as in `exists_pos_forall_norm_lt` and `v` smaller than the `η` chosen
there, the homotopy `(t, w) ↦ φ (ψ w + t v)` is continuous on `[0, 1] × C`. -/
private theorem continuousOn_comp_add_smul (hφ : ContinuousOn φ U) (hψ : ContinuousOn ψ V)
    {C : Set E₂} (hCV : ∀ w ∈ C, w ∈ V ∧ ψ w ∈ U) {η : ℝ}
    (hηC : ∀ w ∈ C, ∀ u : E₁, ‖u‖ < η → ψ w + u ∈ U ∧ (φ (ψ w + u) = w → w ∈ interior C))
    {v : E₁} (hv : ‖v‖ < η) :
    ContinuousOn (fun p : unitInterval × E₂ ↦ φ (ψ p.2 + (p.1 : ℝ) • v)) (univ ×ˢ C) :=
  hφ.comp (continuousOn_add_smul (hψ.mono fun w hw ↦ (hCV w hw).1) v)
    fun p hp ↦ (hηC p.2 hp.2 _ (norm_smul_lt hv p.1)).1

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
  refine ⟨?_, fun p hp h ↦ (hηC p.2 hp _ (norm_smul_lt hv p.1)).2 h⟩
  have hclosed := ((continuousOn_comp_add_smul hφ hψ hCV hηC hv).sub
    continuousOn_snd).preimage_isClosed_of_isClosed (isClosed_univ.prod hC.isClosed)
    (isClosed_singleton (x := (0 : E₂)))
  have heq : {p : unitInterval × E₂ | p.2 ∈ C ∧ φ (ψ p.2 + (p.1 : ℝ) • v) = p.2} =
      univ ×ˢ C ∩ (fun p : unitInterval × E₂ ↦ φ (ψ p.2 + (p.1 : ℝ) • v) - p.2) ⁻¹' {0} := by
    ext p
    simp [sub_eq_zero]
  rw [heq]
  exact (isCompact_univ.prod hC).of_isClosed_subset hclosed inter_subset_left

omit [FiniteDimensional ℝ E₁] in
/-- The homotopy `φ ∘ (ψ + t v)`, `t ∈ [0, 1]`, on the interior `W₂` of a compact set `C` as in
`exists_pos_forall_norm_lt`, for `v` smaller than the `η` chosen there: `φ ∘ ψ` and
`φ ∘ (ψ + v)` have the same fixed-point index on `W₂`, and the fixed set of `φ ∘ (ψ + v)` is
compact. -/
private theorem exists_fixedPointIndex_eq_comp_add (hφ : ContinuousOn φ U)
    (hψ : ContinuousOn ψ V) {C : Set E₂} (hC : IsCompact C) (hCV : ∀ w ∈ C, w ∈ V ∧ ψ w ∈ U)
    {η : ℝ}
    (hηC : ∀ w ∈ C, ∀ u : E₁, ‖u‖ < η → ψ w + u ∈ U ∧ (φ (ψ w + u) = w → w ∈ interior C))
    {v : E₁} (hv : ‖v‖ < η) {W₂ : Opens E₂} (hW₂ : (W₂ : Set E₂) = interior C) (l : C(W₂, E₂))
    (hl : ∀ w : W₂, l w = φ (ψ w)) :
    ∃ lv : C(W₂, E₂), (∀ w : W₂, lv w = φ (ψ w + v)) ∧
      l.fixedPointIndex = lv.fixedPointIndex ∧ IsCompact {w | lv w = w} := by
  obtain ⟨hF, hFC⟩ := isCompact_setOf_comp_add_smul_eq hφ hψ hC hCV hηC hv
  have hWC (w : W₂) : (w : E₂) ∈ C := interior_subset (hW₂ ▸ w.property)
  have hcont : Continuous fun p : unitInterval × W₂ ↦ φ (ψ p.2 + (p.1 : ℝ) • v) :=
    (continuousOn_comp_add_smul hφ hψ hCV hηC hv).comp_continuous
      (continuous_fst.prodMk (continuous_subtypeVal.comp continuous_snd))
      fun p ↦ ⟨trivial, hWC p.2⟩
  let lv : C(W₂, E₂) :=
    ⟨fun w ↦ φ (ψ w + v), (hcont.comp (Continuous.prodMk_right 1)).congr fun w ↦ by simp⟩
  have hlv (w : W₂) : lv w = φ (ψ w + v) := rfl
  let H : l.Homotopy lv :=
    { toFun := fun p ↦ φ (ψ p.2 + (p.1 : ℝ) • v)
      continuous_toFun := hcont
      map_zero_left := fun w ↦ by simp [hl]
      map_one_left := fun w ↦ by simp [hlv] }
  have hHp (p : unitInterval × W₂) : H p = φ (ψ p.2 + (p.1 : ℝ) • v) := rfl
  -- The fixed set of `H`, read in `[0, 1] × E₂`, is the compact set of
  -- `isCompact_setOf_comp_add_smul_eq`.
  have hH : IsCompact {p : unitInterval × W₂ | H p = p.2} :=
    H.isCompact_setOf_apply_eq_of_isCompact hF (fun p hp ↦ hW₂ ▸ hFC p hp.1 hp.2)
      fun t w ↦ by rw [hHp, mem_ofPred_eq, and_iff_right (hWC w)]
  exact ⟨lv, hlv, fixedPointIndex_eq_of_homotopy H hH, H.isCompact_setOf_apply_one_eq hH⟩

omit [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂] in
/-- The homotopy `ψ ∘ φ + t v`, `t ∈ [0, 1]`, on `W₁ = U ∩ φ⁻¹(W₂)`, where `W₂` is the interior
of a compact set `C` as in `exists_pos_forall_norm_lt`, for `v` smaller than the `η` chosen
there: `ψ ∘ φ` and `ψ ∘ φ + v` have the same fixed-point index on `W₁`, and the fixed set of
`ψ ∘ φ + v` is compact. Its fixed points are the images under `ψ + t v` of those of
`φ ∘ (ψ + t v)`. -/
private theorem exists_fixedPointIndex_eq_comp_add_const (hφ : ContinuousOn φ U)
    (hψ : ContinuousOn ψ V) {C : Set E₂} (hC : IsCompact C) (hCV : ∀ w ∈ C, w ∈ V ∧ ψ w ∈ U)
    {η : ℝ}
    (hηC : ∀ w ∈ C, ∀ u : E₁, ‖u‖ < η → ψ w + u ∈ U ∧ (φ (ψ w + u) = w → w ∈ interior C))
    {v : E₁} (hv : ‖v‖ < η) {W₂ : Opens E₂} (hW₂ : (W₂ : Set E₂) = interior C) {W₁ : Opens E₁}
    (hW₁ : (W₁ : Set E₁) = (U : Set E₁) ∩ φ ⁻¹' W₂) (k : C(W₁, E₁))
    (hk : ∀ z : W₁, k z = ψ (φ z)) :
    ∃ kv : C(W₁, E₁), (∀ z : W₁, kv z = ψ (φ z) + v) ∧
      k.fixedPointIndex = kv.fixedPointIndex ∧ IsCompact {z | kv z = z} := by
  obtain ⟨hF, hFC⟩ := isCompact_setOf_comp_add_smul_eq hφ hψ hC hCV hηC hv
  have hW₁m (z : E₁) (hz : z ∈ (W₁ : Set E₁)) : z ∈ U ∧ φ z ∈ C :=
    ⟨(hW₁.subset hz).1, interior_subset (hW₂ ▸ (hW₁.subset hz).2)⟩
  have hcont : Continuous fun p : unitInterval × W₁ ↦ ψ (φ p.2) + (p.1 : ℝ) • v :=
    (continuousOn_add_smul (hψ.comp (hφ.mono fun z hz ↦ (hW₁m z hz).1)
      fun z hz ↦ (hCV _ (hW₁m z hz).2).1) v).comp_continuous
      (continuous_fst.prodMk (continuous_subtypeVal.comp continuous_snd))
      fun p ↦ ⟨trivial, p.2.property⟩
  let kv : C(W₁, E₁) :=
    ⟨fun z ↦ ψ (φ z) + v, (hcont.comp (Continuous.prodMk_right 1)).congr fun z ↦ by simp⟩
  have hkv (z : W₁) : kv z = ψ (φ z) + v := rfl
  let H : k.Homotopy kv :=
    { toFun := fun p ↦ ψ (φ p.2) + (p.1 : ℝ) • v
      continuous_toFun := hcont
      map_zero_left := fun z ↦ by simp [hk]
      map_one_left := fun z ↦ by simp [hkv] }
  have hHp (p : unitInterval × W₁) : H p = ψ (φ p.2) + (p.1 : ℝ) • v := rfl
  -- The fixed set of `H`, read in `[0, 1] × E₁`, is the image of that of `φ ∘ (ψ + t v)` under
  -- `(t, w) ↦ (t, ψ w + t v)`.
  have hG : IsCompact ((fun p : unitInterval × E₂ ↦ (p.1, ψ p.2 + (p.1 : ℝ) • v)) ''
      {p : unitInterval × E₂ | p.2 ∈ C ∧ φ (ψ p.2 + (p.1 : ℝ) • v) = p.2}) :=
    hF.image_of_continuousOn (continuous_fst.continuousOn.prodMk
      ((continuousOn_add_smul (hψ.mono fun w hw ↦ (hCV w hw).1) v).mono
        fun _ hp ↦ ⟨trivial, hp.1⟩))
  have hH : IsCompact {p : unitInterval × W₁ | H p = p.2} := by
    refine H.isCompact_setOf_apply_eq_of_isCompact hG ?_ fun t z ↦ ⟨fun hp ↦ ?_, ?_⟩
    · rintro _ ⟨⟨t, w⟩, ⟨hwC, hp⟩, rfl⟩
      have hw : φ (ψ w + (t : ℝ) • v) ∈ (W₂ : Set E₂) := by
        rw [hp, hW₂]
        exact hFC (t, w) hwC hp
      rw [hW₁]
      exact ⟨(hηC w hwC _ (norm_smul_lt hv t)).1, hw⟩
    · rw [hHp] at hp
      refine ⟨(t, φ z), ⟨(hW₁m z z.property).2, by rw [hp]⟩, Prod.ext rfl hp⟩
    · rintro ⟨⟨t', w⟩, ⟨-, hp⟩, he⟩
      obtain ⟨rfl, hz⟩ := Prod.mk.inj he
      rw [hHp, ← hz, hp]
  exact ⟨kv, hkv, fixedPointIndex_eq_of_homotopy H hH, H.isCompact_setOf_apply_one_eq hH⟩

/-- Commutativity of the fixed-point index, given a compact neighbourhood `C ⊆ V ∩ ψ⁻¹(U)` of the
fixed points of `φ ∘ ψ` and a size `η` of perturbations of `ψ` as in
`exists_pos_forall_norm_lt`. -/
private theorem fixedPointIndex_comp_comm_of_isCompact (hφ : DifferentiableOn ℝ φ U)
    (hψ : DifferentiableOn ℝ ψ V) (hU' : (U' : Set E₁) = (U : Set E₁) ∩ φ ⁻¹' V)
    (hV' : (V' : Set E₂) = (V : Set E₂) ∩ ψ ⁻¹' U) (k : C(U', E₁))
    (hk : ∀ z : U', k z = ψ (φ z)) (l : C(V', E₂)) (hl : ∀ w : V', l w = φ (ψ w))
    {C : Set E₂} (hC : IsCompact C) (hCV' : C ⊆ V')
    (hKC : Subtype.val '' {w | l w = w} ⊆ interior C) {η : ℝ} (hη : 0 < η)
    (hηC : ∀ w ∈ C, ∀ u : E₁, ‖u‖ < η → ψ w + u ∈ U ∧ (φ (ψ w + u) = w → w ∈ interior C)) :
    k.fixedPointIndex = l.fixedPointIndex := by
  have hCV (w : E₂) (hw : w ∈ C) : w ∈ V ∧ ψ w ∈ U := hV'.subset (hCV' hw)
  -- The open sets `W₂ = interior C ⊆ V'` and `W₁ = U ∩ φ⁻¹(W₂) ⊆ U'` contain the fixed points.
  obtain ⟨W₂, hW₂⟩ : ∃ W : Opens E₂, (W : Set E₂) = interior C := ⟨⟨_, isOpen_interior⟩, rfl⟩
  obtain ⟨W₁, hW₁⟩ : ∃ W : Opens E₁, (W : Set E₁) = (U : Set E₁) ∩ φ ⁻¹' W₂ :=
    ⟨⟨_, hφ.continuousOn.isOpen_inter_preimage U.isOpen W₂.isOpen⟩, rfl⟩
  have hW₂C (w : W₂) : (w : E₂) ∈ C := interior_subset (hW₂ ▸ w.property)
  have hW₁m (z : W₁) : (z : E₁) ∈ U ∧ φ z ∈ W₂ := hW₁.subset z.property
  have hW₂V' : W₂ ≤ V' := fun w hw ↦ hCV' (hW₂C ⟨w, hw⟩)
  have hW₁U' : W₁ ≤ U' := fun z hz ↦
    hU'.superset ⟨(hW₁m ⟨z, hz⟩).1, (hCV _ (hW₂C ⟨_, (hW₁m ⟨z, hz⟩).2⟩)).1⟩
  have hkW (z : U') (hz : k z = z) : (z : E₁) ∈ W₁ := by
    rw [← SetLike.mem_coe, hW₁, hW₂]
    refine ⟨(hU'.subset z.property).1, hKC ?_⟩
    rw [image_val_setOf_apply_eq hU' hV' hk hl]
    exact mem_image_of_mem φ ⟨z, hz, rfl⟩
  have hlW (w : V') (hw : l w = w) : (w : E₂) ∈ W₂ := by
    rw [← SetLike.mem_coe, hW₂]
    exact hKC ⟨w, hw, rfl⟩
  -- A regular value `v` of `z ↦ z - ψ (φ z)` on `W₁`, of norm less than `η`.
  obtain ⟨v, hv, hreg⟩ := TauCeti.exists_norm_lt_forall_det_one_sub_ne_zero (s := W₁)
    (g' := fun z ↦ (fderiv ℝ ψ (φ z)).comp (fderiv ℝ φ z)) (fun z hz ↦
      hasFDerivAt_comp_of_mem hφ hψ (hW₁m ⟨z, hz⟩).1 (hCV _ (hW₂C ⟨_, (hW₁m ⟨z, hz⟩).2⟩)).1) hη
  obtain ⟨kv, hkv, hkeq, hKv⟩ := exists_fixedPointIndex_eq_comp_add_const hφ.continuousOn
    hψ.continuousOn hC hCV hηC hv hW₂ hW₁ (k.comp (inclusion hW₁U')) (fun z ↦ hk _)
  obtain ⟨lv, hlv, hleq, -⟩ := exists_fixedPointIndex_eq_comp_add hφ.continuousOn hψ.continuousOn
    hC hCV hηC hv hW₂ (l.comp (inclusion hW₂V')) (fun w ↦ hl _)
  rw [← k.fixedPointIndex_comp_inclusion hW₁U' hkW, ← l.fixedPointIndex_comp_inclusion hW₂V' hlW,
    hkeq, hleq]
  -- The perturbed composites have nondegenerate fixed points.
  refine fixedPointIndex_comp_comm_of_det_ne_zero (ψ := fun w ↦ ψ w + v) hφ
    ((hψ.mono fun w hw ↦ (hCV _ (hW₂C ⟨w, hw⟩)).1).add_const v) hW₁ ?_ kv hkv lv hlv hKv
    fun z hz ↦ ?_
  · ext w
    exact ⟨fun hw ↦ ⟨hw, (hηC _ (hW₂C ⟨w, hw⟩) v hv).1⟩, And.left⟩
  · rw [fderiv_add_const]
    exact hreg z z.property (sub_eq_iff_eq_add'.2 ((hkv z).symm.trans hz).symm)

/-- **Commutativity of the fixed-point index.** Let `φ : E₁ → E₂` and `ψ : E₂ → E₁` be
differentiable on open sets `U ⊆ E₁` and `V ⊆ E₂`. The composite `ψ ∘ φ` restricts to a map
`k : U' → E₁` on `U' = U ∩ φ⁻¹(V)` and `φ ∘ ψ` to a map `l : V' → E₂` on `V' = V ∩ ψ⁻¹(U)`
(neither need map its domain into itself), and they have the same fixed-point index:
`i(ψ ∘ φ) = i(φ ∘ ψ)`. -/
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
    (image_subset_iff.2 fun w _ ↦ w.property)
  have hCV (w : E₂) (hw : w ∈ C) : w ∈ V ∧ ψ w ∈ U := hV'.subset (hCV' hw)
  obtain ⟨η, hη, hηC⟩ := exists_pos_forall_norm_lt hφ.continuousOn hψ.continuousOn hC hCV
    fun w hw h ↦ hKC ⟨⟨w, hCV' hw⟩, (hl _).trans h, rfl⟩
  exact fixedPointIndex_comp_comm_of_isCompact hφ hψ hU' hV' k hk l hl hC hCV' hKC hη hηC

end ContinuousMap
