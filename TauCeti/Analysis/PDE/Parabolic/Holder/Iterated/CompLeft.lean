/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import TauCeti.Analysis.Normed.Module.Multilinear.Basic
import TauCeti.Analysis.Normed.Module.Multilinear.Curry
import TauCeti.Analysis.Normed.Operator.Holder

/-!
# Postcomposition with a continuous linear map on parabolic Hölder spaces of every order

For a continuous linear map `L : F →L[ℝ] G`, postcomposition `u ↦ L ∘ u` maps the bounded
parabolic Hölder space `C_{par,b}^{k+α}(E × [a, b], F)` (`TauCeti.ParabolicCkHolderSpace`) to the
same space with values in `G`, as a continuous linear map
`TauCeti.ParabolicCkHolderSpace.compLeftL L` of operator norm at most `‖L‖`. Its fields
are those of `u` followed by `L`:

`D_t^r D_x^m (L ∘ u) = L ∘ D_t^r D_x^m u`

(`TauCeti.ParabolicCkHolderSpace.mixedDerivL_compLeftL_apply`). It reads off components of
vector-valued maps, such as the directional derivatives `∂ₑu = (D_x u) e` of a spatial gradient,
and assembles vector-valued maps from scalar ones, such as `D_x u = ∑ᵢ ∂ᵢu • dxᵢ` on `ℝⁿ`. It is
the parabolic counterpart of `TauCeti.CkHolderSpace.compLeftL`.

## Main declarations

* `TauCeti.ParabolicCkHolderSpace.compLeftL`: postcomposition with `L` as a continuous linear map.
* `TauCeti.ParabolicCkHolderSpace.compLeftL_apply` and
  `TauCeti.ParabolicCkHolderSpace.mixedDerivL_compLeftL_apply`: its values and its fields.
* `TauCeti.ParabolicCkHolderSpace.norm_compLeftL_le`: the operator-norm bound.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 3
  (the parabolic Hölder spaces `C^{k+α,(k+α)/2}`).
-/

public section
noncomputable section

namespace TauCeti.ParabolicCkHolderSpace

open Set ParabolicSpaceTime
open scoped NNReal BoundedContinuousFunction

variable {k : ℕ} {α : ℝ≥0} {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {a b : ℝ} {hab : a < b}

/-- Postcomposition of `m`-multilinear maps with `L`, as a continuous linear map. -/
private abbrev compMultilinearL (L : F →L[ℝ] G) (m : ℕ) : (E [×m]→L[ℝ] F) →L[ℝ] E [×m]→L[ℝ] G :=
  ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin m ↦ E) F G L

/-- The fields `L ∘ D_t^r D_x^m u` of the postcomposition. -/
private def compLeftFields (L : F →L[ℝ] G) (u : ParabolicCkHolderSpace k α E F hab) (r m : ℕ) :
    slab (E := E) a b →ᵇ (E [×m]→L[ℝ] G) :=
  (compMultilinearL L m).compLeftContinuousBounded _ (mixedDerivL r m u)

private theorem compLeftFields_apply (L : F →L[ℝ] G) (u : ParabolicCkHolderSpace k α E F hab)
    (r m : ℕ) (p : slab (E := E) a b) :
    compLeftFields L u r m p = L.compContinuousMultilinearMap (mixedDerivL r m u p) := by
  rw [compLeftFields, ContinuousLinearMap.compLeftContinuousBounded_apply,
    ContinuousLinearMap.compContinuousMultilinearMapL_apply]

private theorem coe_compLeftFields (L : F →L[ℝ] G) (u : ParabolicCkHolderSpace k α E F hab)
    (r m : ℕ) : ⇑(compLeftFields L u r m) = compMultilinearL L m ∘ mixedDerivL r m u :=
  funext fun _ ↦ ContinuousLinearMap.compLeftContinuousBounded_apply _ _ _

private theorem hasFDerivAt_compLeftFields (L : F →L[ℝ] G)
    (u : ParabolicCkHolderSpace k α E F hab) (r m : ℕ) (h : 2 * r + m + 1 ≤ k) (t : Icc a b)
    (x : E) :
    HasFDerivAt (fun y ↦ compLeftFields L u r m (slabMk y t))
      (compLeftFields L u r (m + 1) (slabMk x t)).curryLeft x := by
  have hd := (compMultilinearL L m).hasFDerivAt.comp x (hasFDerivAt_mixedDerivL u h t x)
  rw [compLeftFields_apply, ContinuousLinearMap.compContinuousMultilinearMap_curryLeft]
  exact hd

private theorem hasDerivWithinAt_compLeftFields (L : F →L[ℝ] G)
    (u : ParabolicCkHolderSpace k α E F hab) (r m : ℕ) (h : 2 * r + m + 2 ≤ k) (x : E)
    (t : Icc a b) :
    HasDerivWithinAt (ParabolicC2HolderSpace.timeExtension hab.le (compLeftFields L u r m) x)
      (compLeftFields L u (r + 1) m (slabMk x t)) (Icc a b) t := by
  have hd := HasFDerivAt.comp_hasDerivWithinAt (x := (t : ℝ))
    (compMultilinearL L m).hasFDerivAt (hasDerivWithinAt_mixedDerivL u h x t)
  rw [← ParabolicC2HolderSpace.timeExtension_comp] at hd
  exact hd

private theorem holderWith_compLeftFields_slabMk (L : F →L[ℝ] G)
    (u : ParabolicCkHolderSpace k α E F hab) {r m : ℕ} (h : 2 * r + m + 1 = k) (x : E) :
    HolderWith (‖compMultilinearL (E := E) L m‖₊ * ‖timeSliceL r m u‖₊) ((1 + α) / 2)
      fun t : Icc a b ↦ compLeftFields L u r m (slabMk x t) := by
  have hc := (compMultilinearL (E := E) L m).holderWith_comp (holderWith_mixedDerivL_slabMk u h x)
  rw [coe_compLeftFields]
  exact hc

private theorem holderWith_compLeftFields (L : F →L[ℝ] G)
    (u : ParabolicCkHolderSpace k α E F hab) {r m : ℕ} (h : 2 * r + m = k) :
    HolderWith (‖compMultilinearL (E := E) L m‖₊ * ‖mixedDerivHolderL r m u‖₊) α
      (compLeftFields L u r m : slab (E := E) a b → E [×m]→L[ℝ] G) := by
  have hc := (compMultilinearL (E := E) L m).holderWith_comp (holderWith_mixedDerivL u h)
  rw [coe_compLeftFields]
  exact hc

/-- Postcomposition with `L`; `compLeftL` is its bundled form. -/
private def compLeft (L : F →L[ℝ] G) (u : ParabolicCkHolderSpace k α E F hab) :
    ParabolicCkHolderSpace k α E G hab :=
  mk (compLeftFields L u) (hasFDerivAt_compLeftFields L u) (hasDerivWithinAt_compLeftFields L u)
    (fun _ _ h ↦ ⟨_, holderWith_compLeftFields_slabMk L u h⟩)
    (fun _ _ h ↦ (holderWith_compLeftFields L u h).memHolder)

private theorem mixedDerivL_compLeft (L : F →L[ℝ] G) (u : ParabolicCkHolderSpace k α E F hab)
    {r m : ℕ} (h : 2 * r + m ≤ k) : mixedDerivL r m (compLeft L u) = compLeftFields L u r m :=
  mixedDerivL_mk _ _ _ _ h

private theorem compLeft_apply (L : F →L[ℝ] G) (u : ParabolicCkHolderSpace k α E F hab)
    (p : slab (E := E) a b) : compLeft L u p = L (u p) := by
  rw [compLeft, mk_apply, compLeftFields_apply, ← mixedDerivL_zero_zero_apply u p 0,
    ContinuousMultilinearMap.curry0_apply, ContinuousLinearMap.compContinuousMultilinearMap_coe,
    Function.comp_apply]

/-- Postcomposition with `L` multiplies the norm by at most `‖L‖`. -/
private theorem norm_compLeft_le (L : F →L[ℝ] G) (u : ParabolicCkHolderSpace k α E F hab) :
    ‖compLeft L u‖ ≤ ‖L‖ * ‖u‖ := by
  have hL (m : ℕ) : ‖compMultilinearL (E := E) L m‖ ≤ ‖L‖ :=
    L.norm_compContinuousMultilinearMapL_le
  have hfield {r m : ℕ} (h : 2 * r + m ≤ k) :
      ‖mixedDerivL r m (compLeft L u)‖ ≤ ‖L‖ * ‖mixedDerivL r m u‖ := by
    rw [mixedDerivL_compLeft L u h]
    refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun p ↦ ?_
    rw [compLeftFields_apply]
    exact (L.norm_compContinuousMultilinearMap_le _).trans
      (mul_le_mul_of_nonneg_left ((mixedDerivL _ _ u).norm_coe_le_norm p) (norm_nonneg L))
  have hslice (r m : ℕ) : ‖timeSliceL r m (compLeft L u)‖ ≤ ‖L‖ * ‖timeSliceL r m u‖ := by
    by_cases h : 2 * r + m + 1 = k
    · refine lp.norm_le_of_forall_le (by positivity) fun x ↦ ?_
      refine (HolderSpace.norm_le_mul_norm_of_apply_eq (compMultilinearL L m)
        (f := timeSliceL r m (compLeft L u) x) (g := timeSliceL r m u x) fun t ↦ ?_).trans
        (mul_le_mul (hL m) (lp.norm_apply_le_norm ENNReal.top_ne_zero _ x) (norm_nonneg _)
          (norm_nonneg L))
      rw [timeSliceL_apply (compLeft L u) h, timeSliceL_apply u h,
        mixedDerivL_compLeft L u (by omega),
        compLeftFields_apply, ContinuousLinearMap.compContinuousMultilinearMapL_apply]
    · rw [timeSliceL_of_ne h, _root_.zero_apply, norm_zero]
      positivity
  have hholder (r m : ℕ) :
      ‖mixedDerivHolderL r m (compLeft L u)‖ ≤ ‖L‖ * ‖mixedDerivHolderL r m u‖ := by
    by_cases h : 2 * r + m = k
    · refine (HolderSpace.norm_le_mul_norm_of_apply_eq (compMultilinearL L m)
        (f := mixedDerivHolderL r m (compLeft L u)) (g := mixedDerivHolderL r m u) fun p ↦ ?_).trans
        (mul_le_mul_of_nonneg_right (hL m) (norm_nonneg _))
      rw [mixedDerivHolderL_apply (compLeft L u) h, mixedDerivHolderL_apply u h,
        mixedDerivL_compLeft L u h.le, compLeftFields_apply,
        ContinuousLinearMap.compContinuousMultilinearMapL_apply]
    · rw [mixedDerivHolderL_of_ne h, _root_.zero_apply, norm_zero]
      positivity
  rw [norm_eq, norm_eq u, Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi ↦ ?_
  rw [mul_add, mul_add]
  exact add_le_add (hfield (mem_parabolicDerivPairs.1 hi)) (add_le_add (hslice _ _) (hholder _ _))

/-- **Postcomposition** `u ↦ L ∘ u` with a continuous linear map `L : F →L[ℝ] G`, as a continuous
linear map from `C_{par,b}^{k+α}(E × [a, b], F)` to `C_{par,b}^{k+α}(E × [a, b], G)`. Its fields
are those of `u` followed by `L` (`ParabolicCkHolderSpace.mixedDerivL_compLeftL_apply`). -/
def compLeftL (L : F →L[ℝ] G) :
    ParabolicCkHolderSpace k α E F hab →L[ℝ] ParabolicCkHolderSpace k α E G hab :=
  LinearMap.mkContinuous
    { toFun := compLeft L
      map_add' u v := ext fun p ↦ by simp [compLeft_apply]
      map_smul' c u := ext fun p ↦ by simp [compLeft_apply] }
    ‖L‖ (norm_compLeft_le L)

/-- The values of the postcomposition are those of `u` followed by `L`. -/
@[simp]
theorem compLeftL_apply (L : F →L[ℝ] G) (u : ParabolicCkHolderSpace k α E F hab)
    (p : slab (E := E) a b) : compLeftL L u p = L (u p) :=
  compLeft_apply L u p

theorem coe_compLeftL (L : F →L[ℝ] G) (u : ParabolicCkHolderSpace k α E F hab) :
    ⇑(compLeftL L u) = L ∘ u :=
  funext (compLeftL_apply L u)

/-- The fields of the postcomposition are those of `u` followed by `L`:
`D_t^r D_x^m (L ∘ u) = L ∘ D_t^r D_x^m u`. -/
@[simp]
theorem mixedDerivL_compLeftL_apply (L : F →L[ℝ] G) (u : ParabolicCkHolderSpace k α E F hab)
    {r m : ℕ} (h : 2 * r + m ≤ k) (p : slab (E := E) a b) :
    mixedDerivL r m (compLeftL L u) p = L.compContinuousMultilinearMap (mixedDerivL r m u p) := by
  rw [← compLeftFields_apply]
  exact DFunLike.congr_fun (mixedDerivL_compLeft L u h) p

/-- The operator norm of postcomposition with `L` is at most `‖L‖`. -/
theorem norm_compLeftL_le (L : F →L[ℝ] G) :
    ‖compLeftL (k := k) (α := α) (E := E) (hab := hab) L‖ ≤ ‖L‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg L) _

@[simp]
theorem compLeftL_id (u : ParabolicCkHolderSpace k α E F hab) : compLeftL (.id ℝ F) u = u :=
  ext fun _ ↦ by simp

@[simp]
theorem compLeftL_compLeftL {G' : Type*} [NormedAddCommGroup G'] [NormedSpace ℝ G']
    (L : F →L[ℝ] G) (L' : G →L[ℝ] G') (u : ParabolicCkHolderSpace k α E F hab) :
    compLeftL L' (compLeftL L u) = compLeftL (L'.comp L) u :=
  ext fun _ ↦ by simp

end TauCeti.ParabolicCkHolderSpace
