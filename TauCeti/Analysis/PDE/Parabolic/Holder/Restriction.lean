/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Two
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Restriction and time reversal of order-two parabolic Hölder maps

Localisation in time and backward parabolic problems move order-two parabolic Hölder maps
between slabs. This file supplies the two basic moves on `ParabolicC2HolderSpace`.

* **Restriction.** For `a ≤ a' < b' ≤ b`, restricting a map on `E × [a, b]` to `E × [a', b']`
  restricts each of its four fields. In particular the time derivative within `[a', b']` is the
  restriction of the one within `[a, b]`, also at the endpoints `a'` and `b'`. Restriction is a
  continuous linear map of operator norm at most one.
* **Time reversal.** With `R (x, s) = (x, T - s)`, which maps `E × [T - b, T - a]` isometrically
  onto `E × [a, b]`, the map `u ↦ u ∘ R` keeps the spatial fields and negates the time
  derivative. It is a linear isometric equivalence. Negating the time derivative is what turns a
  terminal-value problem for a backward equation into an initial-value problem for a forward one.

Restriction and time reversal commute: restricting `u ∘ R` to `E × [T - d, T - c]` is the time
reversal of the restriction of `u` to `E × [c, d]`.

## Main declarations

* `TauCeti.ParabolicC2HolderSpace.restrictL`: restriction to a smaller slab.
* `TauCeti.ParabolicC2HolderSpace.timeReverseLIE`: time reversal about `T`.
* `TauCeti.ParabolicC2HolderSpace.restrictL_timeReverseLIE`: the two commute.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, lecture notes, Cortona, 2004.
-/

public section
noncomputable section

namespace TauCeti

open Set ParabolicSpaceTime
open scoped NNReal BoundedContinuousFunction

variable {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ} {hab : a < b}

namespace ParabolicC2HolderSpace

/-! ### Restriction to a smaller slab -/

section Restriction

variable {a' b' : ℝ} (ha : a ≤ a') (hb : b' ≤ b)

omit [NormedSpace ℝ E] in
private theorem lipschitzWith_inclusion :
    LipschitzWith 1 (inclusion (slab_subset_slab (E := E) ha hb)) :=
  LipschitzWith.of_dist_le_mul fun _ _ ↦ by simp [Subtype.dist_eq]

/-- The restriction of an order-two parabolic Hölder map to a smaller slab. -/
private def restrict (hab' : a' < b') (f : ParabolicC2HolderSpace α E F hab) :
    ParabolicC2HolderSpace α E F hab' :=
  mk ((valueL f).compContinuous (ContinuousMap.inclusion (slab_subset_slab ha hb)))
    ((spatialFDerivL f).compContinuous (ContinuousMap.inclusion (slab_subset_slab ha hb)))
    (HolderSpace.compLipschitzL _ (lipschitzWith_inclusion ha hb) (spatialSecondFDerivL f))
    (HolderSpace.compLipschitzL _ (lipschitzWith_inclusion ha hb) (timeDerivL f))
    (fun t x ↦ by
      simpa [ContinuousMap.inclusion] using
        f.hasSpatialFDerivAt (inclusion (Icc_subset_Icc ha hb) t) x)
    (fun t x ↦ by
      simpa [ContinuousMap.inclusion] using
        f.hasSpatialSecondFDerivAt (inclusion (Icc_subset_Icc ha hb) t) x)
    (fun x t ↦ by
      have h := (f.hasTimeDerivWithinAt x (inclusion (Icc_subset_Icc ha hb) t)).mono
        (Icc_subset_Icc ha hb)
      rw [HolderSpace.compLipschitzL_apply, inclusion_slabMk]
      refine h.congr_of_mem (fun s hs ↦ ?_) t.2
      simp [ContinuousMap.inclusion, timeExtension_def, projIcc_of_mem hab'.le hs,
        projIcc_of_mem hab.le (Icc_subset_Icc ha hb hs)])

private theorem restrict_apply (hab' : a' < b') (f : ParabolicC2HolderSpace α E F hab)
    (p : slab (E := E) a' b') :
    restrict ha hb hab' f p = f (inclusion (slab_subset_slab ha hb) p) := by
  simp [restrict, ContinuousMap.inclusion]

private theorem norm_restrict_le (hab' : a' < b') (f : ParabolicC2HolderSpace α E F hab) :
    ‖restrict ha hb hab' f‖ ≤ ‖f‖ := by
  have hH := HolderSpace.norm_compLipschitzL_le_one (α := α) (Y := E →L[ℝ] E →L[ℝ] F)
    (X := slab (E := E) a b) (X' := slab (E := E) a' b') (lipschitzWith_inclusion ha hb)
  have hT := HolderSpace.norm_compLipschitzL_le_one (α := α) (Y := F)
    (X := slab (E := E) a b) (X' := slab (E := E) a' b') (lipschitzWith_inclusion ha hb)
  rw [norm_eq, norm_eq f, restrict, valueL_mk, spatialFDerivL_mk, spatialSecondFDerivL_mk,
    timeDerivL_mk]
  gcongr
  · exact BoundedContinuousFunction.norm_compContinuous_le _ _
  · exact BoundedContinuousFunction.norm_compContinuous_le _ _
  · simpa using (HolderSpace.compLipschitzL _ _).le_of_opNorm_le hH (spatialSecondFDerivL f)
  · simpa using (HolderSpace.compLipschitzL _ _).le_of_opNorm_le hT (timeDerivL f)

/-- Restriction of an order-two parabolic Hölder map on `E × [a, b]` to the smaller slab
`E × [a', b']`, as a continuous linear map. -/
def restrictL (hab' : a' < b') :
    ParabolicC2HolderSpace α E F hab →L[ℝ] ParabolicC2HolderSpace α E F hab' :=
  LinearMap.mkContinuous
    { toFun := restrict ha hb hab'
      map_add' f g := by ext p; simp only [restrict_apply, add_apply]
      map_smul' c f := by ext p; simp only [restrict_apply, smul_apply, RingHom.id_apply] }
    1 fun f ↦ by
      rw [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      exact norm_restrict_le ha hb hab' f

private theorem restrictL_eq_restrict (hab' : a' < b') (f : ParabolicC2HolderSpace α E F hab) :
    restrictL ha hb hab' f = restrict ha hb hab' f :=
  (rfl)

variable {ha hb} {hab' : a' < b'}

@[simp]
theorem restrictL_apply (f : ParabolicC2HolderSpace α E F hab) (p : slab (E := E) a' b') :
    restrictL ha hb hab' f p = f (inclusion (slab_subset_slab ha hb) p) := by
  rw [restrictL_eq_restrict, restrict_apply]

@[simp]
theorem spatialFDerivL_restrictL (f : ParabolicC2HolderSpace α E F hab)
    (p : slab (E := E) a' b') : spatialFDerivL (restrictL ha hb hab' f) p =
      spatialFDerivL f (inclusion (slab_subset_slab ha hb) p) := by
  rw [restrictL_eq_restrict, restrict, spatialFDerivL_mk]
  simp [ContinuousMap.inclusion]

@[simp]
theorem spatialSecondFDerivL_restrictL (f : ParabolicC2HolderSpace α E F hab)
    (p : slab (E := E) a' b') : spatialSecondFDerivL (restrictL ha hb hab' f) p =
      spatialSecondFDerivL f (inclusion (slab_subset_slab ha hb) p) := by
  rw [restrictL_eq_restrict, restrict, spatialSecondFDerivL_mk, HolderSpace.compLipschitzL_apply]

/-- The time derivative of the restriction is the restriction of the time derivative, also at
the endpoints of the smaller slab. -/
@[simp]
theorem timeDerivL_restrictL (f : ParabolicC2HolderSpace α E F hab)
    (p : slab (E := E) a' b') : timeDerivL (restrictL ha hb hab' f) p =
      timeDerivL f (inclusion (slab_subset_slab ha hb) p) := by
  rw [restrictL_eq_restrict, restrict, timeDerivL_mk, HolderSpace.compLipschitzL_apply]

variable (ha hb hab') in
/-- Restriction to a smaller slab does not increase the norm. -/
theorem norm_restrictL_le :
    ‖restrictL (α := α) (E := E) (F := F) (hab := hab) ha hb hab'‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f ↦ by
    rw [restrictL_eq_restrict, one_mul]
    exact norm_restrict_le ha hb hab' f

/-- Restricting to the whole slab does nothing. -/
@[simp]
theorem restrictL_self (f : ParabolicC2HolderSpace α E F hab) :
    restrictL le_rfl le_rfl hab f = f := by
  ext p
  simp

/-- Successive restrictions compose. -/
@[simp]
theorem restrictL_restrictL {a'' b'' : ℝ} {ha' : a' ≤ a''} {hb' : b'' ≤ b'}
    {hab'' : a'' < b''} (f : ParabolicC2HolderSpace α E F hab) :
    restrictL ha' hb' hab'' (restrictL ha hb hab' f) =
      restrictL (ha.trans ha') (hb'.trans hb) hab'' f := by
  ext p
  simp

end Restriction

/-! ### Time reversal -/

section TimeReversal

variable {a' b' : ℝ} (T : ℝ) (ha : a' = T - b) (hb : b' = T - a)

private theorem sub_mem_Icc_of_eq_sub {a' b' : ℝ} (T : ℝ) (ha : a' = T - b) (hb : b' = T - a)
    {s : ℝ} (hs : s ∈ Icc a' b') : T - s ∈ Icc a b := by
  subst ha hb
  constructor <;> linarith [hs.1, hs.2]

/-- The time reversal `u ∘ R` of an order-two parabolic Hölder map, with negated time
derivative. -/
private def reverse (f : ParabolicC2HolderSpace α E F hab) :
    ParabolicC2HolderSpace α E F (ha ▸ hb ▸ sub_lt_sub_left hab T) :=
  mk ((valueL f).compContinuous ⟨_, (slabTimeReverse T ha hb).continuous⟩)
    ((spatialFDerivL f).compContinuous ⟨_, (slabTimeReverse T ha hb).continuous⟩)
    (HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith
      (spatialSecondFDerivL f))
    (-HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith (timeDerivL f))
    (fun t x ↦ by
      simpa using f.hasSpatialFDerivAt ⟨T - t, sub_mem_Icc_of_eq_sub T ha hb t.2⟩ x)
    (fun t x ↦ by
      simpa using f.hasSpatialSecondFDerivAt ⟨T - t, sub_mem_Icc_of_eq_sub T ha hb t.2⟩ x)
    (fun x t ↦ by
      have h := HasDerivWithinAt.scomp (t : ℝ)
        (f.hasTimeDerivWithinAt x ⟨T - t, sub_mem_Icc_of_eq_sub T ha hb t.2⟩)
        ((hasDerivWithinAt_id (t : ℝ) (Icc a' b')).const_sub T)
        (fun s hs ↦ sub_mem_Icc_of_eq_sub T ha hb hs)
      rw [neg_one_smul] at h
      rw [HolderSpace.neg_apply, HolderSpace.compLipschitzL_apply, slabTimeReverse_slabMk]
      refine h.congr_of_mem (fun s hs ↦ ?_) t.2
      simp [timeExtension_def, projIcc_of_mem (ha ▸ hb ▸ sub_lt_sub_left hab T).le hs,
        projIcc_of_mem hab.le (sub_mem_Icc_of_eq_sub T ha hb hs)])

private theorem reverse_apply (f : ParabolicC2HolderSpace α E F hab)
    (p : slab (E := E) a' b') : reverse T ha hb f p = f (slabTimeReverse T ha hb p) := by
  simp [reverse]

private theorem norm_reverse_le (f : ParabolicC2HolderSpace α E F hab) :
    ‖reverse T ha hb f‖ ≤ ‖f‖ := by
  have hH := HolderSpace.norm_compLipschitzL_le_one (α := α) (Y := E →L[ℝ] E →L[ℝ] F)
    (X := slab (E := E) a b) (X' := slab (E := E) a' b')
    (slabTimeReverse T ha hb).isometry.lipschitzWith
  have hT := HolderSpace.norm_compLipschitzL_le_one (α := α) (Y := F)
    (X := slab (E := E) a b) (X' := slab (E := E) a' b')
    (slabTimeReverse T ha hb).isometry.lipschitzWith
  rw [norm_eq, norm_eq f, reverse, valueL_mk, spatialFDerivL_mk, spatialSecondFDerivL_mk,
    timeDerivL_mk, norm_neg]
  gcongr
  · exact BoundedContinuousFunction.norm_compContinuous_le _ _
  · exact BoundedContinuousFunction.norm_compContinuous_le _ _
  · simpa using (HolderSpace.compLipschitzL _ _).le_of_opNorm_le hH (spatialSecondFDerivL f)
  · simpa using (HolderSpace.compLipschitzL _ _).le_of_opNorm_le hT (timeDerivL f)

/-- Time reversal about `T`: the map `u ↦ u ∘ R` with `R (x, s) = (x, T - s)`, from order-two
parabolic Hölder maps on `E × [a, b]` to those on `E × [a', b']`, where `a' = T - b` and
`b' = T - a`. It is a linear isometric equivalence, whose inverse is time reversal about `T` in
the opposite direction. -/
def timeReverseLIE : ParabolicC2HolderSpace α E F hab ≃ₗᵢ[ℝ]
    ParabolicC2HolderSpace α E F (ha ▸ hb ▸ sub_lt_sub_left hab T) :=
  LinearIsometryEquiv.ofBounds
    { toFun := reverse T ha hb
      invFun := reverse T (by rw [hb, sub_sub_cancel]) (by rw [ha, sub_sub_cancel])
      map_add' f g := by ext p; simp only [reverse_apply, add_apply]
      map_smul' c f := by ext p; simp only [reverse_apply, smul_apply, RingHom.id_apply]
      left_inv f := by
        ext p
        have h := (slabTimeReverse T ha hb).apply_symm_apply p
        rw [slabTimeReverse_symm] at h
        rw [reverse_apply, reverse_apply, h]
      right_inv g := by
        ext p
        have h := (slabTimeReverse T ha hb).symm_apply_apply p
        rw [slabTimeReverse_symm] at h
        rw [reverse_apply, reverse_apply, h] }
    (norm_reverse_le T ha hb) (norm_reverse_le T _ _)

private theorem timeReverseLIE_eq_reverse (f : ParabolicC2HolderSpace α E F hab) :
    timeReverseLIE T ha hb f = reverse T ha hb f :=
  (rfl)

variable {T ha hb}

@[simp]
theorem timeReverseLIE_apply (f : ParabolicC2HolderSpace α E F hab) (p : slab (E := E) a' b') :
    timeReverseLIE T ha hb f p = f (slabTimeReverse T ha hb p) := by
  rw [timeReverseLIE_eq_reverse, reverse_apply]

@[simp]
theorem spatialFDerivL_timeReverseLIE (f : ParabolicC2HolderSpace α E F hab)
    (p : slab (E := E) a' b') : spatialFDerivL (timeReverseLIE T ha hb f) p =
      spatialFDerivL f (slabTimeReverse T ha hb p) := by
  rw [timeReverseLIE_eq_reverse, reverse, spatialFDerivL_mk]
  simp

@[simp]
theorem spatialSecondFDerivL_timeReverseLIE (f : ParabolicC2HolderSpace α E F hab)
    (p : slab (E := E) a' b') : spatialSecondFDerivL (timeReverseLIE T ha hb f) p =
      spatialSecondFDerivL f (slabTimeReverse T ha hb p) := by
  rw [timeReverseLIE_eq_reverse, reverse, spatialSecondFDerivL_mk,
    HolderSpace.compLipschitzL_apply]

/-- Time reversal negates the time derivative. -/
@[simp]
theorem timeDerivL_timeReverseLIE (f : ParabolicC2HolderSpace α E F hab)
    (p : slab (E := E) a' b') : timeDerivL (timeReverseLIE T ha hb f) p =
      -timeDerivL f (slabTimeReverse T ha hb p) := by
  rw [timeReverseLIE_eq_reverse, reverse, timeDerivL_mk, HolderSpace.neg_apply,
    HolderSpace.compLipschitzL_apply]

/-- The inverse of time reversal is time reversal in the opposite direction. -/
@[simp]
theorem timeReverseLIE_symm :
    (timeReverseLIE T ha hb (α := α) (E := E) (F := F) (hab := hab)).symm =
      timeReverseLIE T (by rw [hb, sub_sub_cancel]) (by rw [ha, sub_sub_cancel]) := by
  ext f p
  rfl

/-- Restriction commutes with time reversal: restricting the reversal of `f` to
`E × [c', d']` is the reversal of the restriction of `f` to `E × [c, d]`, where `c' = T - d` and
`d' = T - c`. -/
theorem restrictL_timeReverseLIE {c d c' d' : ℝ} {hcd : c < d} (hc : a ≤ c) (hd : d ≤ b)
    (hc' : c' = T - d) (hd' : d' = T - c) (f : ParabolicC2HolderSpace α E F hab) :
    restrictL (by rw [ha, hc']; linarith) (by rw [hb, hd']; linarith)
        (hc' ▸ hd' ▸ sub_lt_sub_left hcd T) (timeReverseLIE T ha hb f) =
      timeReverseLIE T hc' hd' (restrictL hc hd hcd f) := by
  ext p
  simp only [restrictL_apply, timeReverseLIE_apply]
  congr 1
  ext <;> simp

end TimeReversal

end ParabolicC2HolderSpace

end TauCeti
