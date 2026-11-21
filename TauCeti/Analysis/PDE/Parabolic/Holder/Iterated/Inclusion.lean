/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Basic
import TauCeti.Analysis.PDE.Parabolic.SpaceTime.Interpolation

/-!
# Inclusions between parabolic Hölder spaces of consecutive orders

For `α ≤ 1` and a nondegenerate closed time slab `E × [a, b]`, every bounded parabolic Hölder map
of order `k + 1` is one of order `k`, and the inclusion

`C_{par,b}^{(k+1)+α} → C_{par,b}^{k+α}`

is a bounded linear map (`TauCeti.ParabolicCkHolderSpace.inclusionL`). It keeps the map and its
mixed derivatives `D_t^r D_x^m u` of parabolic order `2 r + m ≤ k`. Its norm is at most `8 N`,
where `N` is the number of pairs `(r, m)` with `2 r + m ≤ k`
(`TauCeti.ParabolicCkHolderSpace.norm_inclusionL_le`). The bound depends neither on `E` and `F`
nor on the slab.

Only the two top orders of the smaller space need an argument; below them the conditions of both
spaces are the same derivative identities.

* A field `D_t^r D_x^m u` with `2 r + m = k - 1` must have uniformly `(1 + α) / 2`-Hölder time
  slices. In the larger space its time derivative `D_t^(r+1) D_x^m u` is a bounded field, so by
  the mean value inequality the time slices are Lipschitz with the supremum of that field as
  constant (`TauCeti.ParabolicSpaceTime.timeEHolderNorm_one_le_of_hasDerivWithinAt`). A bounded
  Lipschitz map is `γ`-Hölder for every `γ ≤ 1`, with constant the Lipschitz constant plus twice
  the supremum (`TauCeti.ParabolicSpaceTime.timeEHolderNorm_le_of_timeEHolderNorm_le` at scale
  one); here `γ = (1 + α) / 2 ≤ 1`.
* A field `D_t^r D_x^m u` with `2 r + m = k` must be parabolically `α`-Hölder. In the larger space
  its time slices are `(1 + α) / 2`-Hölder, and its spatial derivative `D_t^r D_x^(m+1) u` is a
  bounded field, so its spatial slices are Lipschitz
  (`TauCeti.ParabolicSpaceTime.spaceEHolderNorm_one_le_of_hasFDerivAt`). Since the field is
  bounded, these give a parabolic `α`-Hölder bound
  (`TauCeti.ParabolicSpaceTime.eHolderNorm_le_of_spaceEHolderNorm_le_of_timeEHolderNorm_le`
  at scale one).

The hypothesis `α ≤ 1` is used for both: a bounded Lipschitz function is `α`-Hölder only for
`α ≤ 1`.

The same arguments bound every field of a single map of order `k` by its norm: for `α ≤ 1`, each
field `D_t^r D_x^m u` is `α`-Hölder in space with constant `3 ‖u‖`
(`TauCeti.ParabolicCkHolderSpace.holderWith_mixedDerivL_space`) and `α / 2`-Hölder in time with
constant `5 ‖u‖` (`TauCeti.ParabolicCkHolderSpace.holderWith_div_two_mixedDerivL_slabMk`), and below
the top order its time slices are `(1 + α) / 2`-Hölder with constant `3 ‖u‖`
(`TauCeti.ParabolicCkHolderSpace.holderWith_mixedDerivL_slabMk_of_add_one_le`).

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

/-- For `2 r + m + 2 ≤ k` and `α ≤ 1`, the time slices of `D_t^r D_x^m u` are
`(1 + α) / 2`-Hölder, uniformly in space, with constant `‖D_t^(r+1) D_x^m u‖ + 2 ‖D_t^r D_x^m u‖`:
they are Lipschitz with the first constant, and at time differences larger than one the
oscillation bound wins. -/
private theorem holderWith_mixedDerivL_slabMk_of_add_two_le (f : ParabolicCkHolderSpace k α E F hab)
    {r m : ℕ} (h : 2 * r + m + 2 ≤ k) (hα : α ≤ 1) (x : E) :
    HolderWith (‖mixedDerivL (r + 1) m f‖₊ + 2 * ‖mixedDerivL r m f‖₊) ((1 + α) / 2)
      fun t : Icc a b ↦ mixedDerivL r m f (slabMk x t) := by
  have hγ : (1 + α) / 2 ≤ 1 := by
    rw [div_le_one (by norm_num)]
    calc 1 + α ≤ 1 + 1 := by gcongr
      _ = 2 := one_add_one_eq_two
  have hlip := timeEHolderNorm_one_le_of_hasDerivWithinAt (C := ‖mixedDerivL (r + 1) m f‖₊)
    (w := ParabolicC2HolderSpace.timeExtension hab.le (mixedDerivL r m f))
    (wₜ := ParabolicC2HolderSpace.timeExtension hab.le (mixedDerivL (r + 1) m f))
    (fun y t ht ↦ (f.hasDerivWithinAt_mixedDerivL h y ⟨t, ht⟩).congr_deriv
      (ParabolicC2HolderSpace.timeExtension_of_mem hab.le _ y ⟨t, ht⟩).symm)
    (fun y t ht ↦ by
      rw [ParabolicC2HolderSpace.timeExtension_of_mem hab.le _ y ⟨t, ht⟩, coe_nnNorm]
      exact (mixedDerivL (r + 1) m f).norm_coe_le_norm _)
  rw [ParabolicC2HolderSpace.timeExtension_space_slabTime] at hlip
  have hle := timeEHolderNorm_le_of_timeEHolderNorm_le (D := 2 * ‖mixedDerivL r m f‖₊) hlip
    (fun p q ↦ by simpa using (mixedDerivL r m f).dist_le_two_norm p q) hγ one_pos
  rw [NNReal.one_rpow, NNReal.one_rpow, mul_one, mul_one] at hle
  exact timeEHolderNorm_le_iff.1 hle x

/-- For `α ≤ 1`, every field `D_t^r D_x^m u` is `α`-Hölder in space with constant `3 ‖u‖`: at the
top order by the Hölder condition, below it because the next spatial derivative is bounded. -/
theorem holderWith_mixedDerivL_space (f : ParabolicCkHolderSpace k α E F hab) {r m : ℕ}
    (h : 2 * r + m ≤ k) (hα : α ≤ 1) (t : Icc a b) :
    HolderWith (3 * ‖f‖₊) α fun x ↦ mixedDerivL r m f (slabMk x t) := by
  rcases h.lt_or_eq with h | h
  · have hlip : LipschitzWith ‖f‖₊ fun x ↦ mixedDerivL r m f (slabMk x t) :=
      lipschitzOnWith_univ.1 (convex_univ.lipschitzOnWith_of_nnNorm_hasFDerivWithin_le
        (fun x _ ↦ (f.hasFDerivAt_mixedDerivL (by omega) t x).hasFDerivWithinAt) fun x _ ↦ by
          rw [← NNReal.coe_le_coe, coe_nnNorm, ContinuousMultilinearMap.curryLeft_norm,
            coe_nnNorm]
          exact f.norm_mixedDerivL_apply_le r (m + 1) _)
    refine (holderOnWith_univ.1 ((hlip.lipschitzOnWith (s := univ)).holderOnWith_of_norm_le
      (M := ‖f‖₊) (fun x _ ↦ f.norm_mixedDerivL_apply_le r m _) hα)).mono (le_of_eq ?_)
    ring
  · have hslab : LipschitzWith 1 fun x : E ↦ slabMk (a := a) (b := b) x t :=
      LipschitzWith.of_edist_le fun x y ↦ by
        rw [edist_slabMk, edist_self, ENNReal.zero_rpow_of_pos (by norm_num), add_zero]
    have hle : ‖mixedDerivHolderL r m f‖₊ ≤ 3 * ‖f‖₊ := by
      rw [← NNReal.coe_le_coe]
      push_cast
      linarith [f.norm_mixedDerivHolderL_le r m, norm_nonneg f]
    have hH := ((mixedDerivHolderL r m f).holderWith_nnnorm.comp_lipschitzWith_one hslab).mono hle
    simpa only [Function.comp_def, mixedDerivHolderL_apply f h] using hH

/-- For `α ≤ 1`, every field `D_t^r D_x^m u` below the top order has `(1 + α) / 2`-Hölder time
slices with constant `3 ‖u‖`. -/
theorem holderWith_mixedDerivL_slabMk_of_add_one_le (f : ParabolicCkHolderSpace k α E F hab)
    {r m : ℕ} (h : 2 * r + m + 1 ≤ k) (hα : α ≤ 1) (x : E) :
    HolderWith (3 * ‖f‖₊) ((1 + α) / 2) fun t : Icc a b ↦ mixedDerivL r m f (slabMk x t) := by
  rcases h.lt_or_eq with h | h
  · refine (holderWith_mixedDerivL_slabMk_of_add_two_le f (by omega) hα x).mono ?_
    have h₁ : ‖mixedDerivL (r + 1) m f‖₊ ≤ ‖f‖₊ := f.norm_mixedDerivL_le (r + 1) m
    have h₂ : ‖mixedDerivL r m f‖₊ ≤ ‖f‖₊ := f.norm_mixedDerivL_le r m
    calc _ ≤ ‖f‖₊ + 2 * ‖f‖₊ := by gcongr
      _ = _ := by ring
  · refine (f.holderWith_mixedDerivL_slabMk h x).mono ?_
    rw [← NNReal.coe_le_coe]
    push_cast
    linarith [f.norm_timeSliceL_le r m, norm_nonneg f]

/-- For `α ≤ 1`, every field `D_t^r D_x^m u` is `α / 2`-Hölder in time with constant `5 ‖u‖`: at
the top order by the parabolic Hölder condition, below it from the `(1 + α) / 2`-Hölder bound at
time differences below one and the bound `2 ‖u‖` on the oscillation above. -/
theorem holderWith_div_two_mixedDerivL_slabMk (f : ParabolicCkHolderSpace k α E F hab)
    {r m : ℕ} (h : 2 * r + m ≤ k) (hα : α ≤ 1) (x : E) :
    HolderWith (5 * ‖f‖₊) (α / 2) fun t : Icc a b ↦ mixedDerivL r m f (slabMk x t) := by
  rcases h.lt_or_eq with h | h
  · have hγ : α / 2 ≤ (1 + α) / 2 := by gcongr; exact le_add_self
    have hH := holderOnWith_univ.1 (HolderOnWith.of_le_of_dist_le (D := 2 * ‖f‖₊)
      (fun t _ s _ _ ↦ (holderWith_mixedDerivL_slabMk_of_add_one_le f (r := r) (m := m)
        (by omega) hα x).dist_le t s)
      (fun t _ s _ ↦ by
        push_cast
        linarith [dist_le_norm_add_norm (mixedDerivL r m f (slabMk x t))
          (mixedDerivL r m f (slabMk x s)), f.norm_mixedDerivL_apply_le r m (slabMk x t),
          f.norm_mixedDerivL_apply_le r m (slabMk x s)]) hγ one_pos)
    refine hH.mono (le_of_eq ?_)
    simp only [NNReal.one_rpow, mul_one]
    ring
  · have hle : ‖mixedDerivHolderL r m f‖₊ ≤ 5 * ‖f‖₊ := by
      rw [← NNReal.coe_le_coe]
      push_cast
      linarith [f.norm_mixedDerivHolderL_le r m, norm_nonneg f]
    intro t s
    calc edist (mixedDerivL r m f (slabMk x t)) (mixedDerivL r m f (slabMk x s))
        = edist (mixedDerivHolderL r m f (slabMk x t)) (mixedDerivHolderL r m f (slabMk x s)) := by
          rw [mixedDerivHolderL_apply f h, mixedDerivHolderL_apply f h]
      _ ≤ ‖mixedDerivHolderL r m f‖₊ * edist (slabMk x t) (slabMk x s) ^ (α : ℝ) :=
          (mixedDerivHolderL r m f).holderWith_nnnorm _ _
      _ ≤ ↑(5 * ‖f‖₊) * edist t s ^ ((α / 2 : ℝ≥0) : ℝ) := by
          rw [edist_slabMk_same_space_rpow]
          gcongr

/-- For `2 r + m + 1 = k` and `α ≤ 1`, the field `D_t^r D_x^m u` is parabolically `α`-Hölder:
it is bounded, Lipschitz in space, and `(1 + α) / 2`-Hölder in time. -/
private theorem holderWith_mixedDerivL (f : ParabolicCkHolderSpace k α E F hab) {r m : ℕ}
    (h : 2 * r + m + 1 = k) (hα : α ≤ 1) :
    HolderWith (‖mixedDerivL r (m + 1) f‖₊ + 2 * ‖mixedDerivL r m f‖₊ +
      (‖timeSliceL r m f‖₊ + 2 * ‖mixedDerivL r m f‖₊)) α ⇑(mixedDerivL r m f) := by
  -- The spatial derivative of `D_t^r D_x^m u` is `D_t^r D_x^(m+1) u`, curried on the left.
  have hspace := spaceEHolderNorm_one_le_of_hasFDerivAt (C := ‖mixedDerivL r (m + 1) f‖₊)
    (w := ParabolicC2HolderSpace.timeExtension hab.le (mixedDerivL r m f))
    (w' := fun y t ↦ (ParabolicC2HolderSpace.timeExtension hab.le
      (mixedDerivL r (m + 1) f) y t).curryLeft)
    (fun t ht y ↦ by
      simpa only [ParabolicC2HolderSpace.timeExtension_of_mem hab.le _ _ ⟨t, ht⟩] using
        f.hasFDerivAt_mixedDerivL h.le ⟨t, ht⟩ y)
    (fun y t ht ↦ by
      rw [ParabolicC2HolderSpace.timeExtension_of_mem hab.le _ y ⟨t, ht⟩,
        ContinuousMultilinearMap.curryLeft_norm, coe_nnNorm]
      exact (mixedDerivL r (m + 1) f).norm_coe_le_norm _)
  rw [ParabolicC2HolderSpace.timeExtension_space_slabTime] at hspace
  -- The time slices are `(1 + α) / 2`-Hölder with constant the norm of the family of slices.
  have htime : timeEHolderNorm ((1 + α) / 2) ⇑(mixedDerivL r m f) ≤ ‖timeSliceL r m f‖₊ :=
    timeEHolderNorm_le_iff.2 fun x ↦ by
      have hslice := (timeSliceL r m f x).holderWith_nnnorm.mono
        (show ‖timeSliceL r m f x‖₊ ≤ ‖timeSliceL r m f‖₊ from
          lp.norm_apply_le_norm ENNReal.top_ne_zero _ x)
      rwa [coe_timeSliceL f h x] at hslice
  have hle := eHolderNorm_le_of_spaceEHolderNorm_le_of_timeEHolderNorm_le
    (D := 2 * ‖mixedDerivL r m f‖₊) hspace htime
    (fun p q ↦ by simpa using (mixedDerivL r m f).dist_le_two_norm p q) hα
    (by rw [div_le_div_iff_of_pos_right (by norm_num)]; exact le_add_self) one_pos one_pos
  simp only [NNReal.one_rpow, mul_one] at hle
  exact eHolderNorm_le_iff.1 hle

/-- The map of order `k + 1` read as a map of order `k`. -/
private def ofSucc (hα : α ≤ 1) (f : ParabolicCkHolderSpace (k + 1) α E F hab) :
    ParabolicCkHolderSpace k α E F hab :=
  mk (fun r m ↦ mixedDerivL r m f) (fun _ _ h t x ↦ f.hasFDerivAt_mixedDerivL (by omega) t x)
    (fun _ _ h x t ↦ f.hasDerivWithinAt_mixedDerivL (by omega) x t)
    (fun _ _ h ↦ ⟨_, holderWith_mixedDerivL_slabMk_of_add_two_le f (by omega) hα⟩)
    (fun _ _ h ↦ (holderWith_mixedDerivL f (by omega) hα).memHolder)

private theorem mixedDerivL_ofSucc (hα : α ≤ 1) (f : ParabolicCkHolderSpace (k + 1) α E F hab)
    {r m : ℕ} (h : 2 * r + m ≤ k) : mixedDerivL r m (ofSucc hα f) = mixedDerivL r m f :=
  mixedDerivL_mk _ _ _ _ h

private theorem ofSucc_apply (hα : α ≤ 1) (f : ParabolicCkHolderSpace (k + 1) α E F hab)
    (p : slab (E := E) a b) : ofSucc hα f p = f p := by
  rw [ofSucc, mk_apply, ContinuousMultilinearMap.curry0_apply, mixedDerivL_zero_zero_apply]

/-- At the two top orders of the space of order `k`, the norms of the family of time slices and of
the Hölder field of a map of order `k + 1` are at most `7 ‖u‖`. -/
private theorem norm_timeSliceL_add_norm_mixedDerivHolderL_ofSucc_le (hα : α ≤ 1)
    (f : ParabolicCkHolderSpace (k + 1) α E F hab) (r m : ℕ) :
    ‖timeSliceL r m (ofSucc hα f)‖ + ‖mixedDerivHolderL r m (ofSucc hα f)‖ ≤ 7 * ‖f‖ := by
  have hf := norm_nonneg f
  have hD (r m : ℕ) := f.norm_mixedDerivL_le r m
  by_cases hs : 2 * r + m + 1 = k
  · -- The order `k - 1`: the Hölder field vanishes, and the time slices are those of the
    -- `(1 + α) / 2`-Hölder field `D_t^r D_x^m u`.
    rw [mixedDerivHolderL_of_ne (by omega), zero_apply, norm_zero, add_zero]
    have hholder := holderWith_mixedDerivL_slabMk_of_add_two_le f (r := r) (m := m) (by omega) hα
    have hK : ((‖mixedDerivL (r + 1) m f‖₊ + 2 * ‖mixedDerivL r m f‖₊ : ℝ≥0) : ℝ) ≤
        3 * ‖f‖ := by
      push_cast
      nlinarith [hD (r + 1) m, hD r m]
    refine (lp.norm_le_of_forall_le (C := ‖mixedDerivL r m f‖ + 3 * ‖f‖)
      (by positivity) fun x ↦ ?_).trans (by nlinarith [hD r m])
    refine (HolderSpace.norm_le_of_norm_le_of_holderWith (norm_nonneg (mixedDerivL r m f))
      (fun t ↦ ?_) ?_).trans (add_le_add le_rfl hK)
    · rw [timeSliceL_apply _ hs, mixedDerivL_ofSucc hα f (by omega)]
      exact (mixedDerivL r m f).norm_coe_le_norm _
    · rw [coe_timeSliceL _ hs, mixedDerivL_ofSucc hα f (by omega)]
      exact hholder x
  · rw [timeSliceL_of_ne hs, zero_apply, norm_zero, zero_add]
    by_cases hh : 2 * r + m = k
    · -- The order `k`: the Hölder field is the parabolically `α`-Hölder field `D_t^r D_x^m u`.
      have hholder := holderWith_mixedDerivL f (r := r) (m := m) (by omega) hα
      have hK : ((‖mixedDerivL r (m + 1) f‖₊ + 2 * ‖mixedDerivL r m f‖₊ +
          (‖timeSliceL r m f‖₊ + 2 * ‖mixedDerivL r m f‖₊) : ℝ≥0) : ℝ) ≤ 6 * ‖f‖ := by
        push_cast
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

/-- The norm of a map of order `k + 1`, read as a map of order `k`, is at most `8 N` times its
norm, with `N` the number of pairs `(r, m)`, `2 r + m ≤ k`. -/
private theorem norm_ofSucc_le (hα : α ≤ 1) (f : ParabolicCkHolderSpace (k + 1) α E F hab) :
    ‖ofSucc hα f‖ ≤ (parabolicDerivPairs k).card * 8 * ‖f‖ := by
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
    ((parabolicDerivPairs k).card * 8) (norm_ofSucc_le hα)

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
at most `8 N`, where `N` is the number of pairs `(r, m)` with `2 r + m ≤ k`. -/
theorem norm_inclusionL_le (hα : α ≤ 1) :
    ‖inclusionL (k := k) (E := E) (F := F) (hab := hab) hα‖ ≤
      (parabolicDerivPairs k).card * 8 :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- The inclusion is injective. -/
theorem inclusionL_injective (hα : α ≤ 1) :
    Function.Injective (inclusionL (k := k) (E := E) (F := F) (hab := hab) hα) :=
  fun f g hfg ↦ ext fun p ↦ by rw [← inclusionL_apply hα f p, hfg, inclusionL_apply]

end ParabolicCkHolderSpace

end TauCeti
