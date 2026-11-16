/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Basic
import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Analysis.Holder.MeanValue
import TauCeti.Analysis.PDE.Parabolic.SpaceTime.Holder
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Inclusions between parabolic Hölder spaces of consecutive orders

For `α ≤ 1` and a nondegenerate closed time slab `E × [a, b]`, every bounded parabolic Hölder map
of order `k + 1` is one of order `k`, and the inclusion

`C_{par,b}^{(k+1)+α} → C_{par,b}^{k+α}`

is a bounded linear map (`TauCeti.ParabolicCkHolderSpace.inclusionL`). It keeps the map and its
mixed derivatives `D_t^r D_x^m u` of parabolic order `2 r + m ≤ k`. Its norm is at most
`N (5 + max 1 (b - a))`, where `N` is the number of pairs `(r, m)` with `2 r + m ≤ k`
(`TauCeti.ParabolicCkHolderSpace.norm_inclusionL_le`). The bound depends on the slab only through
its length `b - a`, and not on `E`, `F` or the position of the slab.

Only the two top orders of the smaller space need an argument; below them the conditions of both
spaces are the same derivative identities.

* A field `D_t^r D_x^m u` with `2 r + m = k - 1` must have uniformly `(1 + α) / 2`-Hölder time
  slices. In the larger space its time derivative `D_t^(r+1) D_x^m u` is a bounded field, so by
  the mean value inequality the time slices are Lipschitz with the supremum of that field as
  constant. On the interval `[a, b]`, of length `b - a`, a Lipschitz map is `γ`-Hölder for every
  `γ ≤ 1`, with constant multiplied by `(b - a)^(1 - γ)`; here `γ = (1 + α) / 2 ≤ 1`.
* A field `D_t^r D_x^m u` with `2 r + m = k` must be parabolically `α`-Hölder. In the larger space
  its time slices are `(1 + α) / 2`-Hölder, hence `α / 2`-Hölder on `[a, b]`, and its spatial
  derivative `D_t^r D_x^(m+1) u` is a bounded field, so its spatial slices are bounded and
  Lipschitz, hence `α`-Hölder (`TauCeti.holderWith_of_norm_le_of_norm_fderiv_le`). A spatial
  `α`-Hölder bound and a temporal `α / 2`-Hölder bound give a parabolic `α`-Hölder bound
  (`TauCeti.ParabolicSpaceTime.eHolderNorm_le_spaceEHolderNorm_add_timeEHolderNorm`).

The hypothesis `α ≤ 1` is used for both: a bounded Lipschitz function is `α`-Hölder only for
`α ≤ 1`.

## Main declarations

* `TauCeti.ParabolicCkHolderSpace.inclusionL`: the inclusion
  `C_{par,b}^{(k+1)+α} → C_{par,b}^{k+α}`.
* `TauCeti.ParabolicCkHolderSpace.inclusionL_apply` and
  `TauCeti.ParabolicCkHolderSpace.mixedDerivL_inclusionL`: it keeps the map and its fields.
* `TauCeti.ParabolicCkHolderSpace.norm_inclusionL_le`: the bound on its norm.
* `TauCeti.ParabolicCkHolderSpace.inclusionL_injective`: it is injective.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 3
  (the parabolic Hölder spaces `C^{k+α,(k+α)/2}`).
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996,
  Chapter 8.
-/

public section
noncomputable section

namespace TauCeti

namespace ParabolicCkHolderSpace

open Set ParabolicSpaceTime
open scoped NNReal ENNReal

variable {k : ℕ} {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ} {hab : a < b}

/-- A map on `[a, b]` that is `γ`-Hölder with constant `C` is `β`-Hölder for every `β ≤ γ` with
`γ - β ≤ 1`, with constant `C max 1 (b - a)`. -/
private theorem holderWith_mul_max_one {G : Type*} [PseudoEMetricSpace G] {g : Icc a b → G}
    {C γ β : ℝ≥0} (hg : HolderWith C γ g) (hβγ : β ≤ γ) (hγβ : (γ : ℝ) - β ≤ 1) :
    HolderWith (C * max 1 (b - a).toNNReal) β g :=
  (hg.of_le (D := (b - a).toNNReal) (fun t s ↦ by
    rw [Subtype.edist_eq, edist_dist]
    exact ENNReal.ofReal_le_ofReal (Real.dist_le_of_mem_Icc t.2 s.2)) hβγ).mono
    (mul_le_mul_of_nonneg_left
      (NNReal.rpow_le_max_one (sub_nonneg.2 (by exact_mod_cast hβγ)) hγβ) (zero_le : 0 ≤ C))

/-- For `2 r + m + 2 ≤ k`, the time slices of `D_t^r D_x^m u` are Lipschitz, with constant the
supremum of `D_t^(r+1) D_x^m u`. -/
private theorem lipschitzWith_mixedDerivL_slabMk (f : ParabolicCkHolderSpace k α E F hab)
    {r m : ℕ} (h : 2 * r + m + 2 ≤ k) (x : E) :
    LipschitzWith ‖mixedDerivL (r + 1) m f‖₊ fun t : Icc a b ↦ mixedDerivL r m f (slabMk x t) := by
  have hL : LipschitzOnWith ‖mixedDerivL (r + 1) m f‖₊
      (ParabolicC2HolderSpace.timeExtension hab.le (mixedDerivL r m f) x) (Icc a b) :=
    (convex_Icc a b).lipschitzOnWith_of_nnNorm_hasDerivWithin_le
      (f' := ParabolicC2HolderSpace.timeExtension hab.le (mixedDerivL (r + 1) m f) x)
      (fun t ht ↦ (f.hasDerivWithinAt_mixedDerivL h x ⟨t, ht⟩).congr_deriv
        (ParabolicC2HolderSpace.timeExtension_of_mem hab.le _ x ⟨t, ht⟩).symm)
      (fun t ht ↦ by
        rw [ParabolicC2HolderSpace.timeExtension_of_mem hab.le _ x ⟨t, ht⟩]
        exact (mixedDerivL (r + 1) m f).nnNorm_coe_le_nnNorm _)
  intro t s
  simpa only [ParabolicC2HolderSpace.timeExtension_of_mem, Subtype.edist_eq] using hL t.2 s.2

/-- For `2 r + m + 2 ≤ k` and `α ≤ 1`, the time slices of `D_t^r D_x^m u` are
`(1 + α) / 2`-Hölder, uniformly in space. -/
private theorem holderWith_mixedDerivL_slabMk (f : ParabolicCkHolderSpace k α E F hab)
    {r m : ℕ} (h : 2 * r + m + 2 ≤ k) (hα : α ≤ 1) (x : E) :
    HolderWith (‖mixedDerivL (r + 1) m f‖₊ * max 1 (b - a).toNNReal) ((1 + α) / 2)
      fun t : Icc a b ↦ mixedDerivL r m f (slabMk x t) := by
  have hγ : (1 + α) / 2 ≤ 1 := by
    rw [div_le_one (by norm_num)]
    calc 1 + α ≤ 1 + 1 := by gcongr
      _ = 2 := one_add_one_eq_two
  refine holderWith_mul_max_one (lipschitzWith_mixedDerivL_slabMk f h x).holderWith hγ ?_
  have : (0 : ℝ) ≤ ((1 + α) / 2 : ℝ≥0) := NNReal.coe_nonneg _
  push_cast at this ⊢
  linarith

/-- For `2 r + m + 1 = k` and `α ≤ 1`, the field `D_t^r D_x^m u` is parabolically `α`-Hölder:
its spatial slices are bounded and Lipschitz, and its time slices are `(1 + α) / 2`-Hölder. -/
private theorem holderWith_mixedDerivL (f : ParabolicCkHolderSpace k α E F hab) {r m : ℕ}
    (h : 2 * r + m + 1 = k) (hα : α ≤ 1) :
    HolderWith (‖mixedDerivL r (m + 1) f‖₊ + 2 * ‖mixedDerivL r m f‖₊ +
      ‖timeSliceL r m f‖₊ * max 1 (b - a).toNNReal) α ⇑(mixedDerivL r m f) := by
  set v : slab (E := E) a b → E [×m]→L[ℝ] F := ⇑(mixedDerivL r m f)
  -- The spatial slices are bounded by `‖D_t^r D_x^m u‖` and have derivative bounded by
  -- `‖D_t^r D_x^(m+1) u‖`.
  have hspace (t : Icc a b) : HolderWith (‖mixedDerivL r (m + 1) f‖₊ + 2 * ‖mixedDerivL r m f‖₊)
      α fun y ↦ v (slabMk y t) := by
    have hd (y : E) := f.hasFDerivAt_mixedDerivL (r := r) (m := m) h.le t y
    refine holderWith_of_norm_le_of_norm_fderiv_le (g := fun y ↦ v (slabMk y t))
      (N₀ := ‖mixedDerivL r m f‖₊) (N₁ := ‖mixedDerivL r (m + 1) f‖₊) hα
      (fun y ↦ (hd y).differentiableAt)
      (fun y ↦ (mixedDerivL r m f).norm_coe_le_norm _) fun y ↦ ?_
    rw [(hd y).fderiv, ContinuousMultilinearMap.curryLeft_norm, coe_nnNorm]
    exact (mixedDerivL r (m + 1) f).norm_coe_le_norm _
  -- The time slices are `(1 + α) / 2`-Hölder with constant the norm of the family of slices,
  -- hence `α / 2`-Hölder on `[a, b]`.
  have htime (x : E) : HolderWith (‖timeSliceL r m f‖₊ * max 1 (b - a).toNNReal) (α / 2)
      fun t : Icc a b ↦ v (slabMk x t) := by
    have hx : HolderWith ‖timeSliceL r m f‖₊ ((1 + α) / 2) fun t : Icc a b ↦ v (slabMk x t) := by
      have hslice := (timeSliceL r m f x).holderWith_nnnorm.mono
        (show ‖timeSliceL r m f x‖₊ ≤ ‖timeSliceL r m f‖₊ from
          lp.norm_apply_le_norm ENNReal.top_ne_zero _ x)
      rwa [show ⇑(timeSliceL r m f x) = fun t : Icc a b ↦ v (slabMk x t) from
        funext (timeSliceL_apply f h x)] at hslice
    refine holderWith_mul_max_one hx ?_ ?_
    · rw [div_le_div_iff_of_pos_right (by norm_num)]
      exact le_add_self
    · push_cast
      linarith
  have hle : eHolderNorm α v ≤ ((‖mixedDerivL r (m + 1) f‖₊ + 2 * ‖mixedDerivL r m f‖₊ +
      ‖timeSliceL r m f‖₊ * max 1 (b - a).toNNReal : ℝ≥0) : ℝ≥0∞) := by
    refine (eHolderNorm_le_spaceEHolderNorm_add_timeEHolderNorm α v).trans ?_
    rw [ENNReal.coe_add]
    exact add_le_add (spaceEHolderNorm_le_iff.2 fun t ↦ hspace t)
      (timeEHolderNorm_le_iff.2 fun x ↦ htime x)
  exact eHolderNorm_le_iff.1 hle

/-- The map of order `k + 1` read as a map of order `k`. -/
private def ofSucc (hα : α ≤ 1) (f : ParabolicCkHolderSpace (k + 1) α E F hab) :
    ParabolicCkHolderSpace k α E F hab :=
  mk (fun r m ↦ mixedDerivL r m f) (fun _ _ h t x ↦ f.hasFDerivAt_mixedDerivL (by omega) t x)
    (fun _ _ h x t ↦ f.hasDerivWithinAt_mixedDerivL (by omega) x t)
    (fun _ _ h ↦ ⟨_, holderWith_mixedDerivL_slabMk f (by omega) hα⟩)
    (fun _ _ h ↦ (holderWith_mixedDerivL f (by omega) hα).memHolder)

private theorem mixedDerivL_ofSucc (hα : α ≤ 1) (f : ParabolicCkHolderSpace (k + 1) α E F hab)
    {r m : ℕ} (h : 2 * r + m ≤ k) : mixedDerivL r m (ofSucc hα f) = mixedDerivL r m f :=
  mixedDerivL_mk _ _ _ _ h

private theorem ofSucc_apply (hα : α ≤ 1) (f : ParabolicCkHolderSpace (k + 1) α E F hab)
    (p : slab (E := E) a b) : ofSucc hα f p = f p := by
  rw [ofSucc, mk_apply, ContinuousMultilinearMap.curry0_apply, mixedDerivL_zero_zero_apply]

/-- At the two top orders of the space of order `k`, the norms of the family of time slices and of
the Hölder field of a map of order `k + 1` are at most `(4 + max 1 (b - a)) ‖u‖`. -/
private theorem norm_timeSliceL_add_norm_mixedDerivHolderL_ofSucc_le (hα : α ≤ 1)
    (f : ParabolicCkHolderSpace (k + 1) α E F hab) (r m : ℕ) :
    ‖timeSliceL r m (ofSucc hα f)‖ + ‖mixedDerivHolderL r m (ofSucc hα f)‖ ≤
      (4 + max 1 (b - a)) * ‖f‖ := by
  have hL : ((max 1 (b - a).toNNReal : ℝ≥0) : ℝ) = max 1 (b - a) := by
    rw [NNReal.coe_max, NNReal.coe_one, Real.coe_toNNReal _ (sub_nonneg.2 hab.le)]
  have hf := norm_nonneg f
  have hM : (1 : ℝ) ≤ max 1 (b - a) := le_max_left _ _
  have hD (r m : ℕ) := f.norm_mixedDerivL_le r m
  by_cases hs : 2 * r + m + 1 = k
  · -- The order `k - 1`: the Hölder field vanishes, and the time slices are those of the
    -- `(1 + α) / 2`-Hölder field `D_t^r D_x^m u`.
    rw [mixedDerivHolderL_of_ne (by omega), zero_apply, norm_zero, add_zero]
    have hholder := holderWith_mixedDerivL_slabMk f (r := r) (m := m) (by omega) hα
    have hK : ((‖mixedDerivL (r + 1) m f‖₊ * max 1 (b - a).toNNReal : ℝ≥0) : ℝ) ≤
        max 1 (b - a) * ‖f‖ := by
      rw [NNReal.coe_mul, coe_nnNorm, hL, mul_comm]
      exact mul_le_mul_of_nonneg_left (hD _ _) (zero_le_one.trans hM)
    refine (lp.norm_le_of_forall_le (C := ‖mixedDerivL r m f‖ + max 1 (b - a) * ‖f‖)
      (by positivity) fun x ↦ ?_).trans (by nlinarith [hD r m])
    refine (HolderSpace.norm_le_of_norm_le_of_holderWith (norm_nonneg (mixedDerivL r m f))
      (fun t ↦ ?_) ?_).trans (add_le_add le_rfl hK)
    · rw [timeSliceL_apply _ hs, mixedDerivL_ofSucc hα f (by omega)]
      exact (mixedDerivL r m f).norm_coe_le_norm _
    · rw [show ⇑(timeSliceL r m (ofSucc hα f) x) =
          fun t : Icc a b ↦ mixedDerivL r m f (slabMk x t) from
        funext fun t ↦ by rw [timeSliceL_apply _ hs, mixedDerivL_ofSucc hα f (by omega)]]
      exact hholder x
  · rw [timeSliceL_of_ne hs, zero_apply, norm_zero, zero_add]
    by_cases hh : 2 * r + m = k
    · -- The order `k`: the Hölder field is the parabolically `α`-Hölder field `D_t^r D_x^m u`.
      have hholder := holderWith_mixedDerivL f (r := r) (m := m) (by omega) hα
      have hK : ((‖mixedDerivL r (m + 1) f‖₊ + 2 * ‖mixedDerivL r m f‖₊ +
          ‖timeSliceL r m f‖₊ * max 1 (b - a).toNNReal : ℝ≥0) : ℝ) ≤
          (3 + max 1 (b - a)) * ‖f‖ := by
        rw [NNReal.coe_add, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mul, hL, coe_nnNorm,
          coe_nnNorm, coe_nnNorm, NNReal.coe_ofNat]
        have := f.norm_timeSliceL_le r m
        nlinarith [hD r (m + 1), hD r m]
      have hcoe : ⇑(mixedDerivHolderL r m (ofSucc hα f)) = mixedDerivL r m f := by
        rw [← HolderSpace.coe_toBoundedContinuousFunction,
          toBoundedContinuousFunction_mixedDerivHolderL _ hh, mixedDerivL_ofSucc hα f hh.le]
      refine (HolderSpace.norm_le_of_norm_le_of_holderWith (norm_nonneg (mixedDerivL r m f))
        (fun p ↦ ?_) (hcoe ▸ hholder)).trans ((add_le_add (hD r m) hK).trans (by nlinarith))
      rw [hcoe]
      exact (mixedDerivL r m f).norm_coe_le_norm _
    · rw [mixedDerivHolderL_of_ne hh, zero_apply, norm_zero]
      positivity

/-- The norm of a map of order `k + 1`, read as a map of order `k`, is at most
`N (5 + max 1 (b - a))` times its norm, with `N` the number of pairs `(r, m)`, `2 r + m ≤ k`. -/
private theorem norm_ofSucc_le (hα : α ≤ 1) (f : ParabolicCkHolderSpace (k + 1) α E F hab) :
    ‖ofSucc hα f‖ ≤ (parabolicDerivPairs k).card * (5 + max 1 (b - a)) * ‖f‖ := by
  rw [norm_eq, mul_assoc, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun p hp ↦ ?_
  rw [mixedDerivL_ofSucc hα f (mem_parabolicDerivPairs.1 hp)]
  have := norm_timeSliceL_add_norm_mixedDerivHolderL_ofSucc_le hα f p.1 p.2
  nlinarith [f.norm_mixedDerivL_le p.1 p.2]

/-- **The inclusion of parabolic Hölder spaces of consecutive orders.** For `α ≤ 1`, a bounded
parabolic Hölder map of order `k + 1` on the slab `E × [a, b]` is one of order `k`, with the same
mixed derivatives `D_t^r D_x^m u` for `2 r + m ≤ k`, and the inclusion
`C_{par,b}^{(k+1)+α} → C_{par,b}^{k+α}` is a bounded linear map. -/
def inclusionL (hα : α ≤ 1) :
    ParabolicCkHolderSpace (k + 1) α E F hab →L[ℝ] ParabolicCkHolderSpace k α E F hab :=
  LinearMap.mkContinuous
    { toFun := ofSucc hα
      map_add' f g := ext fun p ↦ by simp only [ofSucc_apply, coe_add, Pi.add_apply]
      map_smul' c f := ext fun p ↦ by
        simp only [ofSucc_apply, coe_smul, Pi.smul_apply, RingHom.id_apply] }
    ((parabolicDerivPairs k).card * (5 + max 1 (b - a))) (norm_ofSucc_le hα)

/-- The inclusion keeps the map. -/
@[simp]
theorem inclusionL_apply (hα : α ≤ 1) (f : ParabolicCkHolderSpace (k + 1) α E F hab)
    (p : slab (E := E) a b) : inclusionL hα f p = f p :=
  ofSucc_apply hα f p

/-- The inclusion keeps the mixed derivatives `D_t^r D_x^m u` of parabolic order `2 r + m ≤ k`. -/
@[simp]
theorem mixedDerivL_inclusionL (hα : α ≤ 1) (f : ParabolicCkHolderSpace (k + 1) α E F hab)
    {r m : ℕ} (h : 2 * r + m ≤ k) :
    mixedDerivL r m (inclusionL hα f) = mixedDerivL r m f :=
  mixedDerivL_ofSucc hα f h

/-- **The norm of the inclusion.** The inclusion `C_{par,b}^{(k+1)+α} → C_{par,b}^{k+α}` has norm
at most `N (5 + max 1 (b - a))`, where `N` is the number of pairs `(r, m)` with `2 r + m ≤ k`. -/
theorem norm_inclusionL_le (hα : α ≤ 1) :
    ‖inclusionL (k := k) (E := E) (F := F) (hab := hab) hα‖ ≤
      (parabolicDerivPairs k).card * (5 + max 1 (b - a)) :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- The inclusion is injective. -/
theorem inclusionL_injective (hα : α ≤ 1) :
    Function.Injective (inclusionL (k := k) (E := E) (F := F) (hab := hab) hα) :=
  fun f g hfg ↦ ext fun p ↦ by rw [← inclusionL_apply hα f p, hfg, inclusionL_apply]

end ParabolicCkHolderSpace

end TauCeti
