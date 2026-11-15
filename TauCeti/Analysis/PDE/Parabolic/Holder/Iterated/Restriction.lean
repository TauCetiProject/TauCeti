/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Basic
public import TauCeti.Topology.EMetricSpace.Lipschitz

/-!
# Restriction of parabolic Hölder maps of every order to smaller slabs

For `a ≤ a' < b' ≤ b`, a bounded parabolic Hölder map of order `k` on the slab `E × [a, b]`
restricts to one on the smaller slab `E × [a', b']`
(`TauCeti.ParabolicCkHolderSpace.restrictL`). Every field of the restriction is the restriction of
the corresponding field:

* the mixed derivatives `D_t^r D_x^m u`, `2 r + m ≤ k`
  (`TauCeti.ParabolicCkHolderSpace.mixedDerivL_restrictL`), so in particular the iterated time
  derivatives within `[a', b']` are the restrictions of those within `[a, b]`, also at the
  endpoints `a'` and `b'`, where they are one-sided;
* the top-order fields as bounded Hölder maps
  (`TauCeti.ParabolicCkHolderSpace.mixedDerivHolderL_restrictL`);
* the time slices one order below the top
  (`TauCeti.ParabolicCkHolderSpace.timeSliceL_restrictL`).

Restriction is a continuous linear map of operator norm at most one
(`TauCeti.ParabolicCkHolderSpace.norm_restrictL_le`): the norms of `C_{par,b}^{k+α}` are monotone
in the slab. Restricting to the whole slab does nothing, and successive restrictions compose.
Localising the Schauder theory in time, and estimates on later slabs `[δ, T]`, pass through this
map. It is the every-order counterpart of the restriction
`TauCeti.ParabolicC2HolderSpace.restrictL` of the order-two carrier.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 3.
-/

public section
noncomputable section

namespace TauCeti

open Set ParabolicSpaceTime
open scoped NNReal ENNReal BoundedContinuousFunction

variable {k : ℕ} {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {a b a' b' : ℝ} {hab : a < b}

namespace ParabolicCkHolderSpace

variable (ha : a ≤ a') (hb : b' ≤ b)

/-- The restriction of the field `D_t^r D_x^m u` to the smaller slab. -/
private def restrictField (f : ParabolicCkHolderSpace k α E F hab) (r m : ℕ) :
    slab (E := E) a' b' →ᵇ (E [×m]→L[ℝ] F) :=
  (mixedDerivL r m f).compContinuous (ContinuousMap.inclusion (slab_subset_slab ha hb))

private theorem restrictField_apply (f : ParabolicCkHolderSpace k α E F hab) (r m : ℕ)
    (p : slab (E := E) a' b') :
    restrictField ha hb f r m p = mixedDerivL r m f (inclusion (slab_subset_slab ha hb) p) :=
  (rfl)

/-- A restricted time slice is bounded by the norm of the whole family of time slices. -/
private theorem norm_compLipschitzL_timeSliceL_le (f : ParabolicCkHolderSpace k α E F hab)
    (r m : ℕ) (x : E) :
    ‖HolderSpace.compLipschitzL _ (LipschitzWith.inclusion (Icc_subset_Icc ha hb))
      (timeSliceL r m f x)‖ ≤ ‖timeSliceL r m f‖ :=
  (HolderSpace.norm_compLipschitzL_apply_le _ _).trans
    (lp.norm_apply_le_norm ENNReal.top_ne_zero _ x)

/-- The restricted time slices of order `k - 1` are uniformly `(1 + α) / 2`-Hölder, with the
norm of the family of time slices of `u` as a common constant. -/
private theorem holderWith_restrictField_slabMk (f : ParabolicCkHolderSpace k α E F hab)
    {r m : ℕ} (h : 2 * r + m + 1 = k) (x : E) :
    HolderWith ‖timeSliceL r m f‖₊ ((1 + α) / 2)
      fun t : Icc a' b' ↦ restrictField ha hb f r m (slabMk x t) := by
  set g := HolderSpace.compLipschitzL _ (LipschitzWith.inclusion (Icc_subset_Icc ha hb))
    (timeSliceL r m f x)
  have hg : (g.toBoundedContinuousFunction : Icc a' b' → E [×m]→L[ℝ] F) =
      fun t ↦ restrictField ha hb f r m (slabMk x t) := funext fun t ↦ by
    rw [HolderSpace.coe_toBoundedContinuousFunction, HolderSpace.compLipschitzL_apply,
      timeSliceL_apply f h, restrictField_apply, inclusion_slabMk]
  have hnorm : (nnHolderNorm ((1 + α) / 2) (g.toBoundedContinuousFunction :
      Icc a' b' → E [×m]→L[ℝ] F) : ℝ) ≤ ‖timeSliceL r m f‖ :=
    g.nnHolderNorm_le.trans (norm_compLipschitzL_timeSliceL_le ha hb f r m x)
  rw [← hg]
  exact g.memHolder.holderWith.mono (by exact_mod_cast hnorm)

/-- The restricted fields of top order are parabolically `α`-Hölder. -/
private theorem memHolder_restrictField (f : ParabolicCkHolderSpace k α E F hab) {r m : ℕ}
    (h : 2 * r + m = k) :
    MemHolder α (restrictField ha hb f r m : slab (E := E) a' b' → E [×m]→L[ℝ] F) := by
  have h' := (memHolder_mixedDerivL f h).holderWith.comp
    (holderWith_one.2 (LipschitzWith.inclusion (slab_subset_slab ha hb)))
  rw [mul_one] at h'
  exact h'.memHolder

/-- The restriction of a parabolic Hölder map of order `k` to a smaller slab. -/
private def restrict (hab' : a' < b') (f : ParabolicCkHolderSpace k α E F hab) :
    ParabolicCkHolderSpace k α E F hab' :=
  mk (restrictField ha hb f)
    (fun r m h t x ↦ by
      simpa [restrictField_apply, inclusion_slabMk] using
        f.hasFDerivAt_mixedDerivL h (inclusion (Icc_subset_Icc ha hb) t) x)
    (fun r m h x t ↦ by
      have h' := (f.hasDerivWithinAt_mixedDerivL h x (inclusion (Icc_subset_Icc ha hb) t)).mono
        (Icc_subset_Icc ha hb)
      rw [restrictField_apply, inclusion_slabMk]
      refine h'.congr_of_mem (fun s hs ↦ ?_) t.property
      simp [restrictField_apply, inclusion_slabMk, ParabolicC2HolderSpace.timeExtension_def,
        projIcc_of_mem hab'.le hs, projIcc_of_mem hab.le (Icc_subset_Icc ha hb hs)])
    (fun _ _ h ↦ ⟨_, holderWith_restrictField_slabMk ha hb f h⟩)
    (fun _ _ h ↦ memHolder_restrictField ha hb f h)

private theorem mixedDerivL_restrict (hab' : a' < b') (f : ParabolicCkHolderSpace k α E F hab)
    (r m : ℕ) (p : slab (E := E) a' b') :
    mixedDerivL r m (restrict ha hb hab' f) p =
      mixedDerivL r m f (inclusion (slab_subset_slab ha hb) p) := by
  by_cases h : 2 * r + m ≤ k
  · rw [restrict, mixedDerivL_mk _ _ _ _ h, restrictField_apply]
  · rw [mixedDerivL_of_lt (by omega), mixedDerivL_of_lt (by omega)]
    simp

private theorem restrict_apply (hab' : a' < b') (f : ParabolicCkHolderSpace k α E F hab)
    (p : slab (E := E) a' b') :
    restrict ha hb hab' f p = f (inclusion (slab_subset_slab ha hb) p) := by
  rw [← mixedDerivL_zero_zero_apply _ _ 0, mixedDerivL_restrict, mixedDerivL_zero_zero_apply]

private theorem timeSliceL_restrict (hab' : a' < b') (f : ParabolicCkHolderSpace k α E F hab)
    (r m : ℕ) (x : E) :
    timeSliceL r m (restrict ha hb hab' f) x =
      HolderSpace.compLipschitzL _ (LipschitzWith.inclusion (Icc_subset_Icc ha hb))
        (timeSliceL r m f x) := by
  by_cases h : 2 * r + m + 1 = k
  · refine HolderSpace.ext fun t ↦ ?_
    rw [timeSliceL_apply _ h, HolderSpace.compLipschitzL_apply, timeSliceL_apply _ h,
      mixedDerivL_restrict, inclusion_slabMk]
  · rw [timeSliceL_of_ne h, timeSliceL_of_ne h]
    simp

private theorem mixedDerivHolderL_restrict (hab' : a' < b')
    (f : ParabolicCkHolderSpace k α E F hab) (r m : ℕ) :
    mixedDerivHolderL r m (restrict ha hb hab' f) =
      HolderSpace.compLipschitzL _ (LipschitzWith.inclusion (slab_subset_slab ha hb))
        (mixedDerivHolderL r m f) := by
  by_cases h : 2 * r + m = k
  · refine HolderSpace.ext fun p ↦ ?_
    have hf := DFunLike.congr_fun (toBoundedContinuousFunction_mixedDerivHolderL f h)
      (inclusion (slab_subset_slab ha hb) p)
    have hr := DFunLike.congr_fun
      (toBoundedContinuousFunction_mixedDerivHolderL (restrict ha hb hab' f) h) p
    rw [HolderSpace.toBoundedContinuousFunction_apply] at hf hr
    rw [hr, HolderSpace.compLipschitzL_apply, hf, mixedDerivL_restrict]
  · rw [mixedDerivHolderL_of_ne h, mixedDerivHolderL_of_ne h]
    simp

private theorem norm_restrict_le (hab' : a' < b') (f : ParabolicCkHolderSpace k α E F hab) :
    ‖restrict ha hb hab' f‖ ≤ ‖f‖ := by
  rw [norm_eq, norm_eq f]
  gcongr with p
  · refine ((mixedDerivL p.1 p.2 (restrict ha hb hab' f)).norm_le
      (norm_nonneg (mixedDerivL p.1 p.2 f))).2 fun q ↦ ?_
    rw [mixedDerivL_restrict]
    exact BoundedContinuousFunction.norm_coe_le_norm _ _
  · refine lp.norm_le_of_forall_le (norm_nonneg _) fun x ↦ ?_
    rw [timeSliceL_restrict]
    exact norm_compLipschitzL_timeSliceL_le ha hb f p.1 p.2 x
  · rw [mixedDerivHolderL_restrict]
    exact HolderSpace.norm_compLipschitzL_apply_le _ _

/-- Restriction of a bounded parabolic Hölder map of order `k` on `E × [a, b]` to the smaller
slab `E × [a', b']`, as a continuous linear map. -/
def restrictL (hab' : a' < b') :
    ParabolicCkHolderSpace k α E F hab →L[ℝ] ParabolicCkHolderSpace k α E F hab' :=
  LinearMap.mkContinuous
    { toFun := restrict ha hb hab'
      map_add' f g := by ext p; simp only [restrict_apply, coe_add, Pi.add_apply]
      map_smul' c f := by
        ext p
        simp only [restrict_apply, coe_smul, Pi.smul_apply, RingHom.id_apply] }
    1 fun f ↦ by
      rw [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      exact norm_restrict_le ha hb hab' f

private theorem restrictL_eq_restrict (hab' : a' < b') (f : ParabolicCkHolderSpace k α E F hab) :
    restrictL ha hb hab' f = restrict ha hb hab' f :=
  (rfl)

variable {ha hb} {hab' : a' < b'}

@[simp]
theorem restrictL_apply (f : ParabolicCkHolderSpace k α E F hab) (p : slab (E := E) a' b') :
    restrictL ha hb hab' f p = f (inclusion (slab_subset_slab ha hb) p) := by
  rw [restrictL_eq_restrict, restrict_apply]

/-- Each mixed derivative `D_t^r D_x^m` of the restriction is the restriction of the mixed
derivative. For `r > 0` this says that the iterated time derivatives within the smaller interval
are those within the larger one, also at its endpoints. -/
@[simp]
theorem mixedDerivL_restrictL (f : ParabolicCkHolderSpace k α E F hab) (r m : ℕ)
    (p : slab (E := E) a' b') :
    mixedDerivL r m (restrictL ha hb hab' f) p =
      mixedDerivL r m f (inclusion (slab_subset_slab ha hb) p) := by
  rw [restrictL_eq_restrict, mixedDerivL_restrict]

/-- As a bounded continuous function, the mixed derivative of a restriction is the original
mixed derivative precomposed with the inclusion of the smaller slab. -/
theorem mixedDerivL_restrictL_eq_compContinuous (f : ParabolicCkHolderSpace k α E F hab)
    (r m : ℕ) :
    mixedDerivL r m (restrictL ha hb hab' f) = (mixedDerivL r m f).compContinuous
      (ContinuousMap.inclusion (slab_subset_slab ha hb)) := by
  refine BoundedContinuousFunction.ext fun p ↦ ?_
  simpa only [BoundedContinuousFunction.compContinuous_apply, ContinuousMap.inclusion,
    ContinuousMap.coe_mk] using mixedDerivL_restrictL (ha := ha) (hb := hb) (hab' := hab') f r m p

/-- Each time slice of the restriction is the restriction of the time slice. -/
@[simp]
theorem timeSliceL_restrictL (f : ParabolicCkHolderSpace k α E F hab) (r m : ℕ) (x : E) :
    timeSliceL r m (restrictL ha hb hab' f) x =
      HolderSpace.compLipschitzL _ (LipschitzWith.inclusion (Icc_subset_Icc ha hb))
        (timeSliceL r m f x) := by
  rw [restrictL_eq_restrict, timeSliceL_restrict]

/-- The top-order Hölder fields of the restriction are the restrictions of the Hölder fields. -/
@[simp]
theorem mixedDerivHolderL_restrictL (f : ParabolicCkHolderSpace k α E F hab) (r m : ℕ) :
    mixedDerivHolderL r m (restrictL ha hb hab' f) =
      HolderSpace.compLipschitzL _ (LipschitzWith.inclusion (slab_subset_slab ha hb))
        (mixedDerivHolderL r m f) := by
  rw [restrictL_eq_restrict, mixedDerivHolderL_restrict]

variable (ha hb hab') in
/-- Restriction to a smaller slab does not increase the norm. -/
theorem norm_restrictL_le :
    ‖restrictL (k := k) (α := α) (E := E) (F := F) (hab := hab) ha hb hab'‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f ↦ by
    rw [restrictL_eq_restrict, one_mul]
    exact norm_restrict_le ha hb hab' f

variable (ha hb hab') in
/-- Restriction to a smaller slab does not increase the full parabolic Hölder norm. -/
theorem norm_restrictL_apply_le (f : ParabolicCkHolderSpace k α E F hab) :
    ‖restrictL ha hb hab' f‖ ≤ ‖f‖ := by
  simpa only [one_mul] using
    (restrictL ha hb hab').le_of_opNorm_le (norm_restrictL_le ha hb hab') f

/-- Restricting to the whole slab does nothing. -/
@[simp]
theorem restrictL_self (f : ParabolicCkHolderSpace k α E F hab) :
    restrictL le_rfl le_rfl hab f = f := by
  ext p
  simp

/-- Successive restrictions compose. -/
@[simp]
theorem restrictL_restrictL {a'' b'' : ℝ} {ha' : a' ≤ a''} {hb' : b'' ≤ b'}
    {hab'' : a'' < b''} (f : ParabolicCkHolderSpace k α E F hab) :
    restrictL ha' hb' hab'' (restrictL ha hb hab' f) =
      restrictL (ha.trans ha') (hb'.trans hb) hab'' f := by
  ext p
  simp

end ParabolicCkHolderSpace

end TauCeti
