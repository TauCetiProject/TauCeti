/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import TauCeti.Analysis.Normed.Module.Basic
import TauCeti.Topology.MetricSpace.Holder

/-!
# Time reversal of bounded parabolic Hölder maps of every order

Let `R (x, s) = (x, T - s)`, which maps the slab `E × [a', b']`, where `a' = T - b` and
`b' = T - a`, isometrically onto `E × [a, b]`. For a map `u` in the bounded parabolic Hölder space
`C_{par,b}^{k+α}` on `E × [a, b]` (`TauCeti.ParabolicCkHolderSpace`), the reversed map `u ∘ R`
lies in the same space on `E × [a', b']`, and its mixed derivatives are

`D_t^r D_x^m (u ∘ R) = (-1)^r (D_t^r D_x^m u) ∘ R`:

spatial derivatives commute with `R`, and each time derivative, including the one-sided ones at
the endpoints of the slab, changes sign. The top-order Hölder fields and the time slices one
order below are reversed in the same way. Since `R` is an isometry, and so is the reversal
`t ↦ T - t` of the time interval, and the signs do not change norms, `u ↦ u ∘ R` is a linear
isometric equivalence (`TauCeti.ParabolicCkHolderSpace.timeReverseLIE`), whose inverse is time
reversal about `T` in the opposite direction.

Time reversal turns a backward parabolic equation `∂ₜu + L u = f` with data at the terminal time
`b` into a forward equation with data at the initial time `a'`, so it transfers the theory of
the initial-value problem in every order to terminal-value problems. On the order-two carrier
`TauCeti.ParabolicC2HolderSpace` the same map is `TauCeti.ParabolicC2HolderSpace.timeReverseLIE`.

## Main declarations

* `TauCeti.ParabolicCkHolderSpace.timeReverseLIE`: time reversal about `T`, with
  `TauCeti.ParabolicCkHolderSpace.timeReverseLIE_apply` and the inverse
  `TauCeti.ParabolicCkHolderSpace.timeReverseLIE_symm`.
* `TauCeti.ParabolicCkHolderSpace.mixedDerivL_timeReverseLIE`: its mixed derivatives.
* `TauCeti.ParabolicCkHolderSpace.timeSliceL_timeReverseLIE` and
  `TauCeti.ParabolicCkHolderSpace.mixedDerivHolderL_timeReverseLIE`: its time slices and its
  top-order Hölder fields.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 3.
-/

public section
noncomputable section

namespace TauCeti

open Set ParabolicSpaceTime
open scoped NNReal BoundedContinuousFunction

variable {k : ℕ} {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ} {hab : a < b}

namespace ParabolicCkHolderSpace

variable {a' b' : ℝ} (T : ℝ) (ha : a' = T - b) (hb : b' = T - a)

/-- The fields `(-1) ^ r (D_t^r D_x^m u) ∘ R` of the time reversal of `u`. -/
private def reverseField (f : ParabolicCkHolderSpace k α E F hab) (r m : ℕ) :
    slab (E := E) a' b' →ᵇ (E [×m]→L[ℝ] F) :=
  (-1 : ℝ) ^ r • (mixedDerivL r m f).compContinuous ⟨_, (slabTimeReverse T ha hb).continuous⟩

private theorem reverseField_apply (f : ParabolicCkHolderSpace k α E F hab) (r m : ℕ)
    (p : slab (E := E) a' b') :
    reverseField T ha hb f r m p = (-1 : ℝ) ^ r • mixedDerivL r m f (slabTimeReverse T ha hb p) :=
  (rfl)

/-- The spatial derivative identities of the reversed fields: `R` keeps the spatial variable. -/
private theorem hasFDerivAt_reverseField (f : ParabolicCkHolderSpace k α E F hab) {r m : ℕ}
    (h : 2 * r + m + 1 ≤ k) (t : Icc a' b') (x : E) :
    HasFDerivAt (fun y ↦ reverseField T ha hb f r m (slabMk y t))
      (reverseField T ha hb f r (m + 1) (slabMk x t)).curryLeft x := by
  have hd := (f.hasFDerivAt_mixedDerivL h (iccTimeReverse T ha hb t) x).const_smul
    ((-1 : ℝ) ^ r)
  simp only [reverseField_apply, slabTimeReverse_slabMk, iccTimeReverse_apply] at hd ⊢
  convert hd using 1
  ext v w
  simp [ContinuousMultilinearMap.curryLeft_apply]

/-- The time derivative identities of the reversed fields: each time derivative changes sign,
also at the endpoints of the slab. -/
private theorem hasDerivWithinAt_reverseField (f : ParabolicCkHolderSpace k α E F hab) {r m : ℕ}
    (h : 2 * r + m + 2 ≤ k) (x : E) (t : Icc a' b') :
    HasDerivWithinAt (ParabolicC2HolderSpace.timeExtension
        (ha ▸ hb ▸ sub_lt_sub_left hab T).le (reverseField T ha hb f r m) x)
      (reverseField T ha hb f (r + 1) m (slabMk x t)) (Icc a' b') t := by
  have hd := (HasDerivWithinAt.scomp (t : ℝ)
    (f.hasDerivWithinAt_mixedDerivL h x ⟨T - t, sub_mem_Icc_of_eq_sub T ha hb t.property⟩)
    ((hasDerivWithinAt_id (t : ℝ) (Icc a' b')).const_sub T)
    fun s hs ↦ sub_mem_Icc_of_eq_sub T ha hb hs).const_smul ((-1 : ℝ) ^ r)
  refine (hd.congr_of_mem (fun s hs ↦ ?_) t.property).congr_deriv ?_
  · simp [ParabolicC2HolderSpace.timeExtension_def, reverseField_apply, iccTimeReverse_apply,
      projIcc_of_mem (ha ▸ hb ▸ sub_lt_sub_left hab T).le hs,
      projIcc_of_mem hab.le (sub_mem_Icc_of_eq_sub T ha hb hs)]
  · rw [reverseField_apply, slabTimeReverse_slabMk, iccTimeReverse_apply, smul_smul, ← pow_succ]

/-- The reversed fields of order `k - 1` have uniformly Hölder time slices, because the time
reversal of the interval is an isometry. -/
private theorem exists_holderWith_reverseField (f : ParabolicCkHolderSpace k α E F hab)
    {r m : ℕ} (h : 2 * r + m + 1 = k) :
    ∃ C, ∀ x : E,
      HolderWith C ((1 + α) / 2) fun t : Icc a' b' ↦ reverseField T ha hb f r m (slabMk x t) := by
  refine ⟨‖timeSliceL r m f‖₊ * ‖(-1 : ℝ) ^ r‖₊, fun x ↦ ?_⟩
  have hx : ‖timeSliceL r m f x‖₊ ≤ ‖timeSliceL r m f‖₊ := by
    exact_mod_cast lp.norm_apply_le_norm ENNReal.top_ne_zero _ x
  convert (((timeSliceL r m f x).holderWith_nnnorm.mono hx).comp_lipschitzWith_one
    (iccTimeReverse T ha hb).isometry.lipschitzWith).smul ((-1 : ℝ) ^ r) using 2 with t
  simp [reverseField_apply, timeSliceL_apply f h, iccTimeReverse_apply]

/-- The reversed fields of order `k` are parabolically `α`-Hölder, because `R` is an isometry. -/
private theorem memHolder_reverseField (f : ParabolicCkHolderSpace k α E F hab) {r m : ℕ}
    (h : 2 * r + m = k) :
    MemHolder α (reverseField T ha hb f r m : slab (E := E) a' b' → E [×m]→L[ℝ] F) := by
  refine ⟨‖mixedDerivHolderL r m f‖₊ * ‖(-1 : ℝ) ^ r‖₊, ?_⟩
  convert ((mixedDerivHolderL r m f).holderWith_nnnorm.comp_lipschitzWith_one
    (slabTimeReverse T ha hb).isometry.lipschitzWith).smul ((-1 : ℝ) ^ r) using 1
  funext p
  rw [reverseField_apply, Pi.smul_apply, Function.comp_apply,
    ← HolderSpace.toBoundedContinuousFunction_apply,
    toBoundedContinuousFunction_mixedDerivHolderL f h]

/-- The time reversal `u ∘ R` of a parabolic Hölder map of order `k`. -/
private def reverse (f : ParabolicCkHolderSpace k α E F hab) :
    ParabolicCkHolderSpace k α E F (ha ▸ hb ▸ sub_lt_sub_left hab T) :=
  mk (reverseField T ha hb f) (fun _ _ h t x ↦ hasFDerivAt_reverseField T ha hb f h t x)
    (fun _ _ h x t ↦ hasDerivWithinAt_reverseField T ha hb f h x t)
    (fun _ _ h ↦ exists_holderWith_reverseField T ha hb f h)
    (fun _ _ h ↦ memHolder_reverseField T ha hb f h)

private theorem reverse_apply (f : ParabolicCkHolderSpace k α E F hab)
    (p : slab (E := E) a' b') : reverse T ha hb f p = f (slabTimeReverse T ha hb p) := by
  rw [reverse, mk_apply, reverseField_apply, pow_zero, one_smul,
    ContinuousMultilinearMap.curry0_apply, mixedDerivL_zero_zero_apply]

private theorem mixedDerivL_reverse (f : ParabolicCkHolderSpace k α E F hab) (r m : ℕ)
    (p : slab (E := E) a' b') : mixedDerivL r m (reverse T ha hb f) p =
      (-1 : ℝ) ^ r • mixedDerivL r m f (slabTimeReverse T ha hb p) := by
  by_cases h : 2 * r + m ≤ k
  · rw [reverse, mixedDerivL_mk _ _ _ _ h, reverseField_apply]
  · simp [mixedDerivL_of_lt (not_le.1 h)]

private theorem timeSliceL_reverse (f : ParabolicCkHolderSpace k α E F hab) (r m : ℕ) (x : E) :
    timeSliceL r m (reverse T ha hb f) x = (-1 : ℝ) ^ r •
      HolderSpace.compLipschitzL _ (iccTimeReverse T ha hb).isometry.lipschitzWith
        (timeSliceL r m f x) := by
  by_cases h : 2 * r + m + 1 = k
  · refine HolderSpace.ext fun t ↦ ?_
    rw [timeSliceL_apply _ h, HolderSpace.smul_apply, HolderSpace.compLipschitzL_apply,
      timeSliceL_apply _ h, mixedDerivL_reverse, slabTimeReverse_slabMk, iccTimeReverse_apply]
  · simp [timeSliceL_of_ne h]

private theorem mixedDerivHolderL_reverse (f : ParabolicCkHolderSpace k α E F hab) (r m : ℕ) :
    mixedDerivHolderL r m (reverse T ha hb f) = (-1 : ℝ) ^ r •
      HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith
        (mixedDerivHolderL r m f) := by
  by_cases h : 2 * r + m = k
  · refine HolderSpace.ext fun p ↦ ?_
    rw [HolderSpace.smul_apply, HolderSpace.compLipschitzL_apply,
      ← HolderSpace.toBoundedContinuousFunction_apply,
      ← HolderSpace.toBoundedContinuousFunction_apply,
      toBoundedContinuousFunction_mixedDerivHolderL _ h,
      toBoundedContinuousFunction_mixedDerivHolderL _ h, mixedDerivL_reverse]
  · simp [mixedDerivHolderL_of_ne h]

private theorem norm_reverse_le (f : ParabolicCkHolderSpace k α E F hab) :
    ‖reverse T ha hb f‖ ≤ ‖f‖ := by
  rw [norm_eq, norm_eq f]
  refine Finset.sum_le_sum fun p _ ↦ ?_
  have hT := HolderSpace.norm_compLipschitzL_le_one (α := (1 + α) / 2) (Y := E [×p.2]→L[ℝ] F)
    (iccTimeReverse T ha hb).isometry.lipschitzWith
  have hH := HolderSpace.norm_compLipschitzL_le_one (α := α) (Y := E [×p.2]→L[ℝ] F)
    (X := slab (E := E) a b) (X' := slab (E := E) a' b')
    (slabTimeReverse T ha hb).isometry.lipschitzWith
  refine add_le_add ?_ (add_le_add ?_ ?_)
  · refine (BoundedContinuousFunction.norm_le (norm_nonneg (mixedDerivL p.1 p.2 f))).2 fun q ↦ ?_
    rw [mixedDerivL_reverse, norm_neg_one_pow_smul]
    exact (mixedDerivL p.1 p.2 f).norm_coe_le_norm _
  · refine lp.norm_le_of_forall_le (norm_nonneg _) fun x ↦ ?_
    rw [timeSliceL_reverse, norm_neg_one_pow_smul]
    exact ((HolderSpace.compLipschitzL _ _).le_of_opNorm_le hT _).trans
      ((one_mul _).trans_le (lp.norm_apply_le_norm ENNReal.top_ne_zero _ x))
  · rw [mixedDerivHolderL_reverse, norm_neg_one_pow_smul]
    exact ((HolderSpace.compLipschitzL _ _).le_of_opNorm_le hH _).trans (one_mul _).le

/-- Time reversal about `T`: the map `u ↦ u ∘ R` with `R (x, s) = (x, T - s)`, from bounded
parabolic Hölder maps of order `k` on `E × [a, b]` to those on `E × [a', b']`, where `a' = T - b`
and `b' = T - a`. It is a linear isometric equivalence, whose inverse is time reversal about `T`
in the opposite direction. -/
def timeReverseLIE : ParabolicCkHolderSpace k α E F hab ≃ₗᵢ[ℝ]
    ParabolicCkHolderSpace k α E F (ha ▸ hb ▸ sub_lt_sub_left hab T) :=
  LinearIsometryEquiv.ofBounds
    { toFun := reverse T ha hb
      invFun := reverse T (by rw [hb, sub_sub_cancel]) (by rw [ha, sub_sub_cancel])
      map_add' f g := by ext p; simp only [reverse_apply, coe_add, Pi.add_apply]
      map_smul' c f := by
        ext p
        simp only [reverse_apply, coe_smul, Pi.smul_apply, RingHom.id_apply]
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

private theorem timeReverseLIE_eq_reverse (f : ParabolicCkHolderSpace k α E F hab) :
    timeReverseLIE T ha hb f = reverse T ha hb f :=
  (rfl)

variable {T ha hb}

@[simp]
theorem timeReverseLIE_apply (f : ParabolicCkHolderSpace k α E F hab)
    (p : slab (E := E) a' b') : timeReverseLIE T ha hb f p = f (slabTimeReverse T ha hb p) := by
  rw [timeReverseLIE_eq_reverse, reverse_apply]

/-- The mixed derivatives of the time reversal: `D_t^r D_x^m (u ∘ R) = (-1)^r (D_t^r D_x^m u) ∘ R`.
-/
@[simp]
theorem mixedDerivL_timeReverseLIE (f : ParabolicCkHolderSpace k α E F hab) (r m : ℕ)
    (p : slab (E := E) a' b') : mixedDerivL r m (timeReverseLIE T ha hb f) p =
      (-1 : ℝ) ^ r • mixedDerivL r m f (slabTimeReverse T ha hb p) := by
  rw [timeReverseLIE_eq_reverse, mixedDerivL_reverse]

/-- The time slices of the time reversal are the reversed time slices, with the sign `(-1) ^ r`.
-/
@[simp]
theorem timeSliceL_timeReverseLIE (f : ParabolicCkHolderSpace k α E F hab) (r m : ℕ) (x : E) :
    timeSliceL r m (timeReverseLIE T ha hb f) x = (-1 : ℝ) ^ r •
      HolderSpace.compLipschitzL _ (iccTimeReverse T ha hb).isometry.lipschitzWith
        (timeSliceL r m f x) := by
  rw [timeReverseLIE_eq_reverse, timeSliceL_reverse]

/-- The top-order Hölder fields of the time reversal are the reversed Hölder fields, with the
sign `(-1) ^ r`. -/
@[simp]
theorem mixedDerivHolderL_timeReverseLIE (f : ParabolicCkHolderSpace k α E F hab) (r m : ℕ) :
    mixedDerivHolderL r m (timeReverseLIE T ha hb f) = (-1 : ℝ) ^ r •
      HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith
        (mixedDerivHolderL r m f) := by
  rw [timeReverseLIE_eq_reverse, mixedDerivHolderL_reverse]

/-- The inverse of time reversal is time reversal in the opposite direction. -/
@[simp]
theorem timeReverseLIE_symm :
    (timeReverseLIE T ha hb (k := k) (α := α) (E := E) (F := F) (hab := hab)).symm =
      timeReverseLIE T (by rw [hb, sub_sub_cancel]) (by rw [ha, sub_sub_cancel]) := by
  ext f : 1
  rw [LinearIsometryEquiv.symm_apply_eq]
  ext p
  rw [timeReverseLIE_apply, timeReverseLIE_apply, ← slabTimeReverse_symm T ha hb,
    IsometryEquiv.symm_apply_apply]

end ParabolicCkHolderSpace

end TauCeti
