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

## Main declarations

* `TauCeti.ParabolicCkHolderSpace.inclusionL`: the inclusion
  `C_{par,b}^{(k+1)+α} → C_{par,b}^{k+α}`.
* `TauCeti.ParabolicCkHolderSpace.inclusionL_apply` and
  `TauCeti.ParabolicCkHolderSpace.mixedDerivL_inclusionL`: it keeps the map and its fields.
* `TauCeti.ParabolicCkHolderSpace.norm_inclusionL_le`: the bound on its norm.
* `TauCeti.ParabolicCkHolderSpace.inclusionL_injective`: it is injective.
* `TauCeti.ParabolicCkHolderSpace.memHolder_mixedDerivL_of_le`: every field of order at most `k`
  is parabolically `α`-Hölder.

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

/-- For `2 r + m + 1 = k` and `α ≤ 1`, the field `D_t^r D_x^m u` is parabolically `α`-Hölder:
it is bounded, Lipschitz in space, and `(1 + α) / 2`-Hölder in time. -/
private theorem holderWith_mixedDerivL_of_add_one_eq (f : ParabolicCkHolderSpace k α E F hab)
    {r m : ℕ} (h : 2 * r + m + 1 = k) (hα : α ≤ 1) :
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
    (fun _ _ h ↦ (holderWith_mixedDerivL_of_add_one_eq f (by omega) hα).memHolder)

private theorem mixedDerivL_ofSucc (hα : α ≤ 1) (f : ParabolicCkHolderSpace (k + 1) α E F hab)
    {r m : ℕ} (h : 2 * r + m ≤ k) : mixedDerivL r m (ofSucc hα f) = mixedDerivL r m f :=
  mixedDerivL_mk _ _ _ _ h

private theorem ofSucc_apply (hα : α ≤ 1) (f : ParabolicCkHolderSpace (k + 1) α E F hab)
    (p : slab (E := E) a b) : ofSucc hα f p = f p := by
  rw [ofSucc, mk_apply, ContinuousMultilinearMap.curry0_apply, mixedDerivL_zero_zero_apply]

/-- The norm of a map of order `k + 1`, read as a map of order `k`, is at most `8 N` times its
norm, with `N` the number of pairs `(r, m)`, `2 r + m ≤ k`. -/
private theorem norm_ofSucc_le (hα : α ≤ 1) (f : ParabolicCkHolderSpace (k + 1) α E F hab) :
    ‖ofSucc hα f‖ ≤ (parabolicDerivPairs k).card * 8 * ‖f‖ := by
  rw [norm_eq, mul_assoc, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun p hp ↦ ?_
  have hp := mem_parabolicDerivPairs.1 hp
  have hD (r m : ℕ) := f.norm_mixedDerivL_le r m
  -- Each pair contributes at most `2 ‖u‖ + 6 ‖u‖`: the Hölder constants of the two top orders
  -- are at most `3 ‖u‖` and `6 ‖u‖`.
  refine (norm_add_norm_timeSliceL_add_norm_mixedDerivHolderL_le (ofSucc hα f) (B := ‖f‖)
    (C := 6 * ‖f‖₊) ?_ (fun h x ↦ ?_) (fun h ↦ ?_)).trans_eq (by push_cast; ring)
  · rw [mixedDerivL_ofSucc hα f hp]
    exact f.norm_mixedDerivL_le p.1 p.2
  · rw [mixedDerivL_ofSucc hα f hp]
    refine (holderWith_mixedDerivL_slabMk_of_add_two_le f (by omega) hα x).mono ?_
    rw [← NNReal.coe_le_coe]
    push_cast
    linarith [hD (p.1 + 1) p.2, hD p.1 p.2, norm_nonneg f]
  · rw [mixedDerivL_ofSucc hα f hp]
    refine (holderWith_mixedDerivL_of_add_one_eq f (by omega) hα).mono ?_
    rw [← NNReal.coe_le_coe]
    push_cast
    linarith [hD p.1 (p.2 + 1), hD p.1 p.2, f.norm_timeSliceL_le p.1 p.2]

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

/-- **Every field is parabolically Hölder.** For `α ≤ 1`, every field `D_t^r D_x^m u` with
`2 r + m ≤ k` of a map of order `k` is parabolically `α`-Hölder, not only those of top order:
the map is also of every order `2 r + m ≤ k`, where the field has top order. -/
theorem memHolder_mixedDerivL_of_le (hα : α ≤ 1) (f : ParabolicCkHolderSpace k α E F hab)
    {r m : ℕ} (h : 2 * r + m ≤ k) :
    MemHolder α (mixedDerivL r m f : slab (E := E) a b → E [×m]→L[ℝ] F) := by
  induction k with
  | zero => exact f.memHolder_mixedDerivL (by omega)
  | succ k ih =>
    rcases h.eq_or_lt with h | h
    · exact f.memHolder_mixedDerivL h
    · rw [← mixedDerivL_inclusionL hα f (by omega)]
      exact ih _ (by omega)

end ParabolicCkHolderSpace

end TauCeti
