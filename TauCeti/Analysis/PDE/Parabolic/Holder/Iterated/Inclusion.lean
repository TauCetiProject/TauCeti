/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Basic
import TauCeti.Analysis.PDE.Parabolic.SpaceTime.Interpolation

/-!
# Inclusions between consecutive orders of the parabolic Hölder scale

For `α ≤ 1`, every map of the bounded parabolic Hölder space `C_{par,b}^{k+1+α}` on a
nondegenerate closed slab `E × [a, b]` lies in `C_{par,b}^{k+α}`, with the same mixed derivative
fields. This file packages the inclusion as a bounded linear map
`TauCeti.ParabolicCkHolderSpace.ofSuccL`, with operator norm at most `12 N`, where `N` is the
number of pairs `(r, m)` with `2 r + m ≤ k`. The constant depends neither on the slab nor on the
dimension.

Only the two top orders of `C_{par,b}^{k+α}` carry Hölder conditions, and both follow from one
more derivative:

* a field `D_t^r D_x^m u` of order `2 r + m = k` has the bounded spatial derivative
  `D_t^r D_x^(m+1) u` and `(1 + α) / 2`-Hölder time slices, since its order is one below the top
  order `k + 1`. A bounded map which is Lipschitz in space and `(1 + α) / 2`-Hölder in time is
  `α`-Hölder in space and `α / 2`-Hölder in time, hence parabolically `α`-Hölder
  (`TauCeti.ParabolicSpaceTime.eHolderNorm_le_of_spaceEHolderNorm_le_of_timeEHolderNorm_le`);
* a field of order `2 r + m = k - 1` has the bounded time derivative `D_t^(r+1) D_x^m u`, so its
  time slices are Lipschitz, hence `(1 + α) / 2`-Hölder.

Both steps lower a Hölder exponent to `α` or `(1 + α) / 2`, which needs `α ≤ 1`. The hypothesis
cannot be dropped: for `α > 1` the map `u (x, t) = t` lies in `C_{par,b}^{2+α}`, its top-order
fields being constant, but not in `C_{par,b}^{1+α}`, whose norm asks for `(1 + α) / 2`-Hölder time
slices of `u`, with an exponent above one.

The inclusions between consecutive orders are used to compare the norms of the scale, for
instance to absorb lower-order terms when the Schauder estimates are raised from one order to the
next.

## Main declarations

* `TauCeti.ParabolicCkHolderSpace.ofSuccL`: the inclusion
  `C_{par,b}^{k+1+α} → C_{par,b}^{k+α}` for `α ≤ 1`, with `ofSuccL_apply` and
  `mixedDerivL_ofSuccL` describing it and `ofSuccL_injective`.
* `TauCeti.ParabolicCkHolderSpace.norm_ofSuccL_apply_le` and
  `TauCeti.ParabolicCkHolderSpace.norm_ofSuccL_le`: the norm bounds.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004,
  Chapter 3 (parabolic Hölder spaces).
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996,
  Chapter 8.
-/

public section
noncomputable section

namespace TauCeti.ParabolicCkHolderSpace

open Set ParabolicSpaceTime
open scoped ENNReal NNReal

variable {k : ℕ} {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ} {hab : a < b}

/-- For `α ≤ 1`, a field of order one below the top order `k + 1` is parabolically `α`-Hölder: it
is Lipschitz in space, with constant the supremum of its spatial derivative, and
`(1 + α) / 2`-Hölder in time. -/
private theorem eHolderNorm_mixedDerivL_le (hα : α ≤ 1)
    (f : ParabolicCkHolderSpace (k + 1) α E F hab) {r m : ℕ} (h : 2 * r + m = k) :
    eHolderNorm α (mixedDerivL r m f : slab (E := E) a b → E [×m]→L[ℝ] F) ≤
      ↑(‖mixedDerivL r (m + 1) f‖₊ + 2 * ‖mixedDerivL r m f‖₊ +
        (‖timeSliceL r m f‖₊ + 2 * ‖mixedDerivL r m f‖₊)) := by
  have hspace : spaceEHolderNorm 1 (mixedDerivL r m f : slab (E := E) a b → E [×m]→L[ℝ] F) ≤
      ‖mixedDerivL r (m + 1) f‖₊ := by
    -- Extend constantly in time, so as to apply the Lipschitz bound on `E × ℝ`.
    rw [← ParabolicC2HolderSpace.timeExtension_space_slabTime hab.le
      (mixedDerivL r m f : slab (E := E) a b → E [×m]→L[ℝ] F)]
    refine spaceEHolderNorm_one_le_of_hasFDerivAt
      (w' := fun y t ↦ (mixedDerivL r (m + 1) f (slabMk y (projIcc a b hab.le t))).curryLeft)
      (fun t ht y ↦ ?_) fun y t _ ↦ ?_
    · simpa only [ParabolicC2HolderSpace.timeExtension_def, projIcc_of_mem hab.le ht] using
        hasFDerivAt_mixedDerivL f (r := r) (m := m) (by omega) ⟨t, ht⟩ y
    · rw [ContinuousMultilinearMap.curryLeft_norm, coe_nnNorm]
      exact (mixedDerivL r (m + 1) f).norm_coe_le_norm _
  have htime : timeEHolderNorm ((1 + α) / 2)
      (mixedDerivL r m f : slab (E := E) a b → E [×m]→L[ℝ] F) ≤ ‖timeSliceL r m f‖₊ := by
    refine timeEHolderNorm_le_iff.2 fun x t s ↦ ?_
    have hnorm : ‖timeSliceL r m f x‖₊ ≤ ‖timeSliceL r m f‖₊ := by
      exact_mod_cast lp.norm_apply_le_norm ENNReal.top_ne_zero (timeSliceL r m f) x
    simpa only [timeSliceL_apply f (by omega : 2 * r + m + 1 = k + 1)] using
      (timeSliceL r m f x).holderWith_nnnorm.mono hnorm t s
  have hdist (p q : slab (E := E) a b) :
      dist (mixedDerivL r m f p) (mixedDerivL r m f q) ≤ ↑(2 * ‖mixedDerivL r m f‖₊) := by
    simpa using (mixedDerivL r m f).dist_le_two_norm p q
  simpa using eHolderNorm_le_of_spaceEHolderNorm_le_of_timeEHolderNorm_le hspace htime hdist hα
    (by gcongr; exact le_add_self) one_pos one_pos

/-- For `α ≤ 1`, a field of order two below the top order `k + 1` has `(1 + α) / 2`-Hölder time
slices: they are Lipschitz, with constant the supremum of its time derivative. -/
private theorem holderWith_mixedDerivL_slabMk (hα : α ≤ 1)
    (f : ParabolicCkHolderSpace (k + 1) α E F hab) {r m : ℕ} (h : 2 * r + m + 1 = k) (x : E) :
    HolderWith (‖mixedDerivL (r + 1) m f‖₊ + 2 * ‖mixedDerivL r m f‖₊) ((1 + α) / 2)
      fun t : Icc a b ↦ mixedDerivL r m f (slabMk x t) := by
  have hlip := (convex_Icc a b).lipschitzOnWith_of_nnNorm_hasDerivWithin_le
    (f := ParabolicC2HolderSpace.timeExtension hab.le (mixedDerivL r m f) x)
    (f' := fun t ↦ mixedDerivL (r + 1) m f (slabMk x (projIcc a b hab.le t)))
    (fun t ht ↦ by
      simpa only [projIcc_of_mem hab.le ht] using
        hasDerivWithinAt_mixedDerivL f (r := r) (m := m) (by omega) x ⟨t, ht⟩)
    fun t _ ↦ (mixedDerivL (r + 1) m f).nnNorm_coe_le_nnNorm _
  have H := (hlip.holderOnWith_of_norm_le (M := ‖mixedDerivL r m f‖₊) (α := (1 + α) / 2)
    (fun t _ ↦ ParabolicC2HolderSpace.norm_timeExtension_le hab.le _ t x)
    (by rw [div_le_one two_pos, one_add_one_eq_two.symm]; gcongr)).holderWith
  intro t s
  simpa only [domRestrict_apply, ParabolicC2HolderSpace.timeExtension_def, projIcc_val] using H t s

/-- The time slices of a field of order `2 r + m = k - 1`, as a family of bounded
`(1 + α) / 2`-Hölder maps, have norm at most `4 ‖f‖`. -/
private theorem norm_le_four_mul_of_forall_apply_eq {f : ParabolicCkHolderSpace (k + 1) α E F hab}
    (hα : α ≤ 1) {r m : ℕ} (h : 2 * r + m + 1 = k)
    {S : lp (fun _ : E ↦ HolderSpace ((1 + α) / 2) (Icc a b) (E [×m]→L[ℝ] F)) ∞}
    (hS : ∀ x t, S x t = mixedDerivL r m f (slabMk x t)) : ‖S‖ ≤ 4 * ‖f‖ := by
  refine lp.norm_le_of_forall_le (by positivity) fun x ↦ ?_
  have hH : HolderWith (‖mixedDerivL (r + 1) m f‖₊ + 2 * ‖mixedDerivL r m f‖₊) ((1 + α) / 2)
      (S x) := by
    simpa only [← funext (hS x)] using holderWith_mixedDerivL_slabMk hα f h x
  refine (HolderSpace.norm_le_of_norm_le_of_holderWith (M := ‖mixedDerivL r m f‖) (by positivity)
    (fun t ↦ ?_) hH).trans ?_
  · rw [hS]
    exact (mixedDerivL r m f).norm_coe_le_norm _
  · push_cast
    linarith [norm_mixedDerivL_le f r m, norm_mixedDerivL_le f (r + 1) m]

private def ofSucc (hα : α ≤ 1) (f : ParabolicCkHolderSpace (k + 1) α E F hab) :
    ParabolicCkHolderSpace k α E F hab :=
  mk (fun r m ↦ mixedDerivL r m f)
    (fun r m h t x ↦ hasFDerivAt_mixedDerivL f (by omega) t x)
    (fun r m h x t ↦ hasDerivWithinAt_mixedDerivL f (by omega) x t)
    (fun r m h ↦ ⟨_, holderWith_mixedDerivL_slabMk hα f h⟩)
    (fun r m h ↦ eHolderNorm_lt_top.1 ((eHolderNorm_mixedDerivL_le hα f h).trans_lt
      ENNReal.coe_lt_top))

private theorem mixedDerivL_ofSucc (hα : α ≤ 1) (f : ParabolicCkHolderSpace (k + 1) α E F hab)
    {r m : ℕ} (h : 2 * r + m ≤ k) : mixedDerivL r m (ofSucc hα f) = mixedDerivL r m f :=
  mixedDerivL_mk _ _ _ _ h

private theorem ofSucc_apply (hα : α ≤ 1) (f : ParabolicCkHolderSpace (k + 1) α E F hab)
    (p : slab (E := E) a b) : ofSucc hα f p = f p := by
  rw [← mixedDerivL_zero_zero_apply (ofSucc hα f) p 0, mixedDerivL_ofSucc hα f (by omega),
    mixedDerivL_zero_zero_apply]

private theorem norm_timeSliceL_ofSucc_le (hα : α ≤ 1)
    (f : ParabolicCkHolderSpace (k + 1) α E F hab) (r m : ℕ) :
    ‖timeSliceL r m (ofSucc hα f)‖ ≤ 4 * ‖f‖ := by
  by_cases h : 2 * r + m + 1 = k
  · refine norm_le_four_mul_of_forall_apply_eq hα h fun x t ↦ ?_
    rw [timeSliceL_apply _ h, mixedDerivL_ofSucc hα f (by omega)]
  · rw [timeSliceL_of_ne h, zero_apply, norm_zero]
    positivity

private theorem norm_mixedDerivHolderL_ofSucc_le (hα : α ≤ 1)
    (f : ParabolicCkHolderSpace (k + 1) α E F hab) (r m : ℕ) :
    ‖mixedDerivHolderL r m (ofSucc hα f)‖ ≤ 7 * ‖f‖ := by
  by_cases h : 2 * r + m = k
  · have hval (p : slab (E := E) a b) :
        mixedDerivHolderL r m (ofSucc hα f) p = mixedDerivL r m f p := by
      rw [← HolderSpace.toBoundedContinuousFunction_apply,
        toBoundedContinuousFunction_mixedDerivHolderL _ h, mixedDerivL_ofSucc hα f h.le]
    have hH : HolderWith (‖mixedDerivL r (m + 1) f‖₊ + 2 * ‖mixedDerivL r m f‖₊ +
        (‖timeSliceL r m f‖₊ + 2 * ‖mixedDerivL r m f‖₊)) α
        (mixedDerivHolderL r m (ofSucc hα f)) := by
      rw [show (mixedDerivHolderL r m (ofSucc hα f) : slab (E := E) a b → E [×m]→L[ℝ] F) =
        mixedDerivL r m f from funext hval]
      exact fun p q ↦ eHolderNorm_le_iff.1 (eHolderNorm_mixedDerivL_le hα f h) p q
    refine (HolderSpace.norm_le_of_norm_le_of_holderWith (M := ‖mixedDerivL r m f‖)
      (by positivity) (fun p ↦ ?_) hH).trans ?_
    · rw [hval]
      exact (mixedDerivL r m f).norm_coe_le_norm p
    · push_cast
      linarith [norm_mixedDerivL_le f r m, norm_mixedDerivL_le f r (m + 1),
        norm_timeSliceL_le f r m]
  · rw [mixedDerivHolderL_of_ne h, zero_apply, norm_zero]
    positivity

private theorem norm_ofSucc_le (hα : α ≤ 1) (f : ParabolicCkHolderSpace (k + 1) α E F hab) :
    ‖ofSucc hα f‖ ≤ 12 * (parabolicDerivPairs k).card * ‖f‖ := by
  rw [norm_eq, mul_comm 12, mul_assoc, ← nsmul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ fun p hp ↦ ?_
  rw [mixedDerivL_ofSucc hα f (mem_parabolicDerivPairs.1 hp)]
  linarith [norm_mixedDerivL_le f p.1 p.2, norm_timeSliceL_ofSucc_le hα f p.1 p.2,
    norm_mixedDerivHolderL_ofSucc_le hα f p.1 p.2]

/-- For `α ≤ 1`, the inclusion `C_{par,b}^{k+1+α} → C_{par,b}^{k+α}` of bounded parabolic
Hölder maps on the same closed slab. It keeps the underlying map (`ofSuccL_apply`) and the mixed
derivative fields of order at most `k` (`mixedDerivL_ofSuccL`), and its operator norm is at most
`12` times the number of pairs `(r, m)` with `2 r + m ≤ k` (`norm_ofSuccL_le`). -/
def ofSuccL (hα : α ≤ 1) :
    ParabolicCkHolderSpace (k + 1) α E F hab →L[ℝ] ParabolicCkHolderSpace k α E F hab :=
  LinearMap.mkContinuous
    { toFun := ofSucc hα
      map_add' := fun f g ↦ ext fun p ↦ by simp only [ofSucc_apply, coe_add, Pi.add_apply]
      map_smul' := fun c f ↦ ext fun p ↦ by
        simp only [ofSucc_apply, coe_smul, Pi.smul_apply, RingHom.id_apply] }
    (12 * (parabolicDerivPairs k).card) (norm_ofSucc_le hα)

/-- The inclusion keeps the underlying map. -/
@[simp]
theorem ofSuccL_apply (hα : α ≤ 1) (f : ParabolicCkHolderSpace (k + 1) α E F hab)
    (p : slab (E := E) a b) : ofSuccL hα f p = f p :=
  ofSucc_apply hα f p

/-- The inclusion keeps the mixed derivative fields of order at most `k`; the fields of higher
order of an element of `C_{par,b}^{k+α}` vanish (`mixedDerivL_of_lt`). -/
@[simp]
theorem mixedDerivL_ofSuccL (hα : α ≤ 1) (f : ParabolicCkHolderSpace (k + 1) α E F hab)
    {r m : ℕ} (h : 2 * r + m ≤ k) : mixedDerivL r m (ofSuccL hα f) = mixedDerivL r m f :=
  mixedDerivL_ofSucc hα f h

/-- The inclusion is injective. -/
theorem ofSuccL_injective (hα : α ≤ 1) :
    Function.Injective (ofSuccL (k := k) (E := E) (F := F) (hab := hab) hα) :=
  fun f g hfg ↦ ext fun p ↦ by rw [← ofSuccL_apply hα f p, hfg, ofSuccL_apply]

/-- The inclusion bound `‖u‖_{k+α} ≤ 12 N ‖u‖_{k+1+α}`, with `N` the number of pairs `(r, m)`
with `2 r + m ≤ k`. -/
theorem norm_ofSuccL_apply_le (hα : α ≤ 1) (f : ParabolicCkHolderSpace (k + 1) α E F hab) :
    ‖ofSuccL hα f‖ ≤ 12 * (parabolicDerivPairs k).card * ‖f‖ :=
  norm_ofSucc_le hα f

/-- The operator norm of the inclusion is at most `12 N`, with `N` the number of pairs `(r, m)`
with `2 r + m ≤ k`. -/
theorem norm_ofSuccL_le (hα : α ≤ 1) :
    ‖ofSuccL (k := k) (E := E) (F := F) (hab := hab) hα‖ ≤
      12 * (parabolicDerivPairs k).card :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

end TauCeti.ParabolicCkHolderSpace
