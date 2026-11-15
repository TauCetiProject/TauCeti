/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated
public import TauCeti.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Spatial directional derivatives in the parabolic Hölder scale

On a nondegenerate closed slab `E × [a, b]`, the spatial derivative `∂_v u` in a direction
`v ∈ E` is a bounded linear map

`C_{par,b}^{k+1+α}(E; F) → C_{par,b}^{k+α}(E; F)`

of norm at most `‖v‖` (`TauCeti.ParabolicCkHolderSpace.lineDerivL`). Its value at `(x, t)` is the
derivative of `y ↦ u (y, t)` at `x` in the direction `v`
(`TauCeti.ParabolicCkHolderSpace.lineDerivL_slabMk`).

The mixed derivative `D_t^r D_x^m (∂_v u)` is `D_t^r D_x^(m+1) u` with `v` inserted as the last of
its `m + 1` spatial arguments. So the parabolic order drops by one: the top-order parabolic Hölder
fields of `u` give the top-order fields of `∂_v u`, and the uniformly Hölder time slices one order
below the top give those one order below the new top. Inserting `v` as the last argument, rather
than the first, matches the derivative identities of the scale without any symmetry of the
fields.

Differentiating a parabolic equation `P u = f` in a spatial direction gives an equation of the
same form for `∂_v u`, with the differentiated coefficients entering as lower-order terms; this is
how the Schauder theory at a higher order of differentiability is reduced to a lower one.

## Main declarations

* `TauCeti.ParabolicCkHolderSpace.lineDerivL`: the spatial derivative in a direction `v`,
  `C_{par,b}^{k+1+α}(E; F) →L[ℝ] C_{par,b}^{k+α}(E; F)`.
* `TauCeti.ParabolicCkHolderSpace.mixedDerivL_lineDerivL_apply`,
  `TauCeti.ParabolicCkHolderSpace.mixedDerivHolderL_lineDerivL_apply` and
  `TauCeti.ParabolicCkHolderSpace.timeSliceL_lineDerivL_apply`: the derivative fields, Hölder
  fields and time slices of `∂_v u` are those of `u` with one more spatial derivative, taken in
  the direction `v`.
* `TauCeti.ParabolicCkHolderSpace.hasLineDerivAt_lineDerivL`,
  `TauCeti.ParabolicCkHolderSpace.lineDerivL_slabMk` and
  `TauCeti.ParabolicCkHolderSpace.lineDerivL_slabMk_eq_fderiv`: `∂_v u` is the spatial
  directional derivative.
* `TauCeti.ParabolicCkHolderSpace.norm_lineDerivL_le`: the operator norm is at most `‖v‖`.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 3
  (the parabolic Hölder spaces `C^{k+α,(k+α)/2}`).
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996,
  Chapter 8.
-/

public section

noncomputable section

namespace TauCeti.ParabolicCkHolderSpace

open Set ParabolicSpaceTime
open ContinuousMultilinearMap
  (evalLastL evalLastL_apply evalLastL_comp_curryLeft norm_evalLastL_le)
open scoped NNReal BoundedContinuousFunction

variable {k : ℕ} {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ} {hab : a < b}

/-- The fields `D_t^r D_x^m (∂_v u)`: the fields `D_t^r D_x^(m+1) u` with `v` inserted last. -/
private def lineDerivField (v : E) (f : ParabolicCkHolderSpace (k + 1) α E F hab) (r m : ℕ) :
    slab (E := E) a b →ᵇ (E [×m]→L[ℝ] F) :=
  BoundedContinuousFunction.comp (evalLastL ℝ F v m) (evalLastL ℝ F v m).lipschitzWith
    (mixedDerivL r (m + 1) f)

private theorem lineDerivField_apply (v : E) (f : ParabolicCkHolderSpace (k + 1) α E F hab)
    (r m : ℕ) (p : slab (E := E) a b) :
    lineDerivField v f r m p = evalLastL ℝ F v m (mixedDerivL r (m + 1) f p) :=
  (rfl)

/-- Postcomposition with `evalLastL` keeps a `γ`-Hölder map `γ`-Hölder. -/
private theorem holderWith_evalLastL_comp (v : E) {m : ℕ} {X : Type*} [PseudoEMetricSpace X]
    {C γ : ℝ≥0} {g : X → E [×(m + 1)]→L[ℝ] F} (hg : HolderWith C γ g) :
    HolderWith (‖evalLastL ℝ F v m‖₊ * C) γ fun p ↦ evalLastL ℝ F v m (g p) := by
  have h := (holderWith_one.2 (evalLastL ℝ F v m).lipschitzWith).comp hg
  rwa [NNReal.coe_one, NNReal.rpow_one, one_mul] at h

private def lineDerivMap (v : E) (f : ParabolicCkHolderSpace (k + 1) α E F hab) :
    ParabolicCkHolderSpace k α E F hab :=
  mk (lineDerivField v f)
    (fun r m h t x ↦ by
      have H := (evalLastL ℝ F v m).hasFDerivAt.comp x
        (hasFDerivAt_mixedDerivL f (r := r) (m := m + 1) (by omega) t x)
      rw [evalLastL_comp_curryLeft] at H
      simpa only [Function.comp_def, lineDerivField_apply] using H)
    (fun r m h x t ↦ by
      -- The chain rule through `HasFDerivWithinAt`: the multilinear maps carry two normed
      -- structures, and the derivative-within form unifies with the one of the field.
      have H := ((evalLastL ℝ F v m).hasFDerivAt.comp_hasFDerivWithinAt (t : ℝ)
        (hasDerivWithinAt_mixedDerivL f (r := r) (m := m + 1) (by omega) x t).hasFDerivWithinAt
        ).hasDerivWithinAt
      simpa only [Function.comp_def, ParabolicC2HolderSpace.timeExtension_def,
        lineDerivField_apply, ContinuousLinearMap.coe_comp,
        ContinuousLinearMap.toSpanSingleton_apply, one_smul] using H)
    (fun r m h ↦ ⟨‖evalLastL ℝ F v m‖₊ * ‖timeSliceL r (m + 1) f‖₊, fun x ↦ by
      have hnorm : ‖timeSliceL r (m + 1) f x‖₊ ≤ ‖timeSliceL r (m + 1) f‖₊ := by
        exact_mod_cast lp.norm_apply_le_norm ENNReal.top_ne_zero (timeSliceL r (m + 1) f) x
      have H := holderWith_evalLastL_comp v
        ((timeSliceL r (m + 1) f x).holderWith_nnnorm.mono hnorm)
      simpa only [lineDerivField_apply, timeSliceL_apply f (r := r) (m := m + 1) (by omega)]
        using H⟩)
    (fun r m h ↦ by
      obtain ⟨C, hC⟩ := memHolder_mixedDerivL f (r := r) (m := m + 1) (by omega)
      exact ⟨_, fun p q ↦ by
        simpa only [lineDerivField_apply] using holderWith_evalLastL_comp v hC p q⟩)

private theorem mixedDerivL_lineDerivMap (v : E) (f : ParabolicCkHolderSpace (k + 1) α E F hab)
    (r m : ℕ) (p : slab (E := E) a b) :
    mixedDerivL r m (lineDerivMap v f) p = evalLastL ℝ F v m (mixedDerivL r (m + 1) f p) := by
  by_cases h : 2 * r + m ≤ k
  · have hf : mixedDerivL r m (lineDerivMap v f) = lineDerivField v f r m :=
      mixedDerivL_mk _ _ _ _ h
    rw [hf, lineDerivField_apply]
  · rw [mixedDerivL_of_lt (k := k) (α := α) (E := E) (F := F) (hab := hab) (r := r) (m := m)
      (by omega), mixedDerivL_of_lt (k := k + 1) (α := α) (E := E) (F := F) (hab := hab) (r := r)
      (m := m + 1) (by omega)]
    simp

private theorem mixedDerivHolderL_lineDerivMap (v : E)
    (f : ParabolicCkHolderSpace (k + 1) α E F hab) (r m : ℕ) :
    mixedDerivHolderL r m (lineDerivMap v f) =
      HolderSpace.compLeftL (evalLastL ℝ F v m) (mixedDerivHolderL r (m + 1) f) := by
  refine HolderSpace.ext fun p ↦ ?_
  rw [HolderSpace.compLeftL_apply]
  by_cases h : 2 * r + m = k
  · have H := congrArg (· p)
      (toBoundedContinuousFunction_mixedDerivHolderL (lineDerivMap v f) h)
    have H' := congrArg (· p)
      (toBoundedContinuousFunction_mixedDerivHolderL f (r := r) (m := m + 1) (by omega))
    simp only [HolderSpace.toBoundedContinuousFunction_apply] at H H'
    rw [H, H', mixedDerivL_lineDerivMap]
  · rw [mixedDerivHolderL_of_ne (k := k) (α := α) (E := E) (F := F) (hab := hab) h,
      mixedDerivHolderL_of_ne (k := k + 1) (α := α) (E := E) (F := F) (hab := hab) (r := r)
      (m := m + 1) (by omega)]
    simp [HolderSpace.zero_apply]

private theorem timeSliceL_lineDerivMap (v : E) (f : ParabolicCkHolderSpace (k + 1) α E F hab)
    (r m : ℕ) (x : E) :
    timeSliceL r m (lineDerivMap v f) x =
      HolderSpace.compLeftL (evalLastL ℝ F v m) (timeSliceL r (m + 1) f x) := by
  refine HolderSpace.ext fun t ↦ ?_
  rw [HolderSpace.compLeftL_apply]
  by_cases h : 2 * r + m + 1 = k
  · rw [timeSliceL_apply _ h, timeSliceL_apply f (by omega), mixedDerivL_lineDerivMap]
  · rw [timeSliceL_of_ne (k := k) (α := α) (E := E) (F := F) (hab := hab) h,
      timeSliceL_of_ne (k := k + 1) (α := α) (E := E) (F := F) (hab := hab) (r := r) (m := m + 1)
      (by omega)]
    simp [HolderSpace.zero_apply]

private theorem norm_compLeftL_evalLastL_le (v : E) {m : ℕ} {γ : ℝ≥0} {X : Type*}
    [MetricSpace X] (g : HolderSpace γ X (E [×(m + 1)]→L[ℝ] F)) :
    ‖HolderSpace.compLeftL (evalLastL ℝ F v m) g‖ ≤ ‖v‖ * ‖g‖ :=
  ((HolderSpace.compLeftL (evalLastL ℝ F v m)).le_opNorm g).trans
    (mul_le_mul_of_nonneg_right ((HolderSpace.norm_compLeftL_le _).trans
      (norm_evalLastL_le v m)) (norm_nonneg g))

/-- Each family of fields of `∂_v u` is bounded by `‖v‖` times the corresponding family of `u`
with one more spatial derivative. -/
private theorem norm_fields_lineDerivMap_le (v : E) (f : ParabolicCkHolderSpace (k + 1) α E F hab)
    (r m : ℕ) :
    ‖mixedDerivL r m (lineDerivMap v f)‖ + (‖timeSliceL r m (lineDerivMap v f)‖ +
        ‖mixedDerivHolderL r m (lineDerivMap v f)‖) ≤
      ‖v‖ * (‖mixedDerivL r (m + 1) f‖ + (‖timeSliceL r (m + 1) f‖ +
        ‖mixedDerivHolderL r (m + 1) f‖)) := by
  have hL := norm_evalLastL_le (𝕜 := ℝ) (F := F) v m
  rw [mul_add, mul_add]
  gcongr
  · refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun p ↦ ?_
    rw [mixedDerivL_lineDerivMap]
    exact (evalLastL ℝ F v m).le_of_opNorm_le_of_le hL
      ((mixedDerivL r (m + 1) f).norm_coe_le_norm p)
  · refine lp.norm_le_of_forall_le (by positivity) fun x ↦ ?_
    rw [timeSliceL_lineDerivMap]
    exact (norm_compLeftL_evalLastL_le v _).trans
      (by gcongr; exact lp.norm_apply_le_norm ENNReal.top_ne_zero _ x)
  · rw [mixedDerivHolderL_lineDerivMap]
    exact norm_compLeftL_evalLastL_le v _

private theorem norm_lineDerivMap_le (v : E) (f : ParabolicCkHolderSpace (k + 1) α E F hab) :
    ‖lineDerivMap v f‖ ≤ ‖v‖ * ‖f‖ := by
  rw [norm_eq, norm_eq, Finset.mul_sum]
  refine Finset.sum_le_sum_of_injOn (fun p : ℕ × ℕ ↦ (p.1, p.2 + 1))
    (fun p _ q _ hpq ↦ by simpa [Prod.ext_iff] using hpq) ?_
    (fun p _ ↦ norm_fields_lineDerivMap_le v f p.1 p.2) fun p _ _ ↦ by positivity
  intro p hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hp
  simp only [mem_parabolicDerivPairs] at hq ⊢
  omega

private theorem lineDerivMap_apply (v : E) (f : ParabolicCkHolderSpace (k + 1) α E F hab)
    (p : slab (E := E) a b) : lineDerivMap v f p = mixedDerivL 0 1 f p fun _ ↦ v := by
  rw [← mixedDerivL_zero_zero_apply (lineDerivMap v f) p 0, mixedDerivL_lineDerivMap,
    evalLastL_apply, Fin.snoc_zero]

/-- **The spatial derivative in a direction `v`**,
`C_{par,b}^{k+1+α}(E; F) → C_{par,b}^{k+α}(E; F)` on a closed slab: `lineDerivL v u (x, t)` is
the derivative of `y ↦ u (y, t)` at `x` in the direction `v`
(`TauCeti.ParabolicCkHolderSpace.lineDerivL_slabMk`). Its operator norm is at most `‖v‖`
(`TauCeti.ParabolicCkHolderSpace.norm_lineDerivL_le`). -/
def lineDerivL (v : E) :
    ParabolicCkHolderSpace (k + 1) α E F hab →L[ℝ] ParabolicCkHolderSpace k α E F hab :=
  LinearMap.mkContinuous
    { toFun := lineDerivMap v
      map_add' := fun f g ↦ ext fun p ↦ by
        simp only [lineDerivMap_apply, coe_add, Pi.add_apply, map_add,
          add_apply]
      map_smul' := fun c f ↦ ext fun p ↦ by
        simp only [lineDerivMap_apply, coe_smul, Pi.smul_apply, map_smul,
          smul_apply, RingHom.id_apply] }
    ‖v‖ fun f ↦ by
      rw [LinearMap.coe_mk, AddHom.coe_mk]
      exact norm_lineDerivMap_le v f

private theorem lineDerivL_eq (v : E) (f : ParabolicCkHolderSpace (k + 1) α E F hab) :
    lineDerivL v f = lineDerivMap v f := by
  rw [lineDerivL, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]

/-- The field `D_t^r D_x^m (∂_v u)` is `D_t^r D_x^(m+1) u` with `v` as the last argument. -/
@[simp]
theorem mixedDerivL_lineDerivL_apply (v : E) (f : ParabolicCkHolderSpace (k + 1) α E F hab)
    (r m : ℕ) (p : slab (E := E) a b) (w : Fin m → E) :
    mixedDerivL r m (lineDerivL v f) p w = mixedDerivL r (m + 1) f p (Fin.snoc w v) := by
  rw [lineDerivL_eq, mixedDerivL_lineDerivMap, evalLastL_apply]

/-- The top-order Hölder field of `∂_v u` is that of `u` with `v` as the last argument. -/
@[simp]
theorem mixedDerivHolderL_lineDerivL_apply (v : E)
    (f : ParabolicCkHolderSpace (k + 1) α E F hab) (r m : ℕ) (p : slab (E := E) a b)
    (w : Fin m → E) :
    mixedDerivHolderL r m (lineDerivL v f) p w =
      mixedDerivHolderL r (m + 1) f p (Fin.snoc w v) := by
  rw [lineDerivL_eq, mixedDerivHolderL_lineDerivMap, HolderSpace.compLeftL_apply, evalLastL_apply]

/-- The uniformly Hölder time slices of `∂_v u` are those of `u` with `v` as the last
argument. -/
@[simp]
theorem timeSliceL_lineDerivL_apply (v : E) (f : ParabolicCkHolderSpace (k + 1) α E F hab)
    (r m : ℕ) (x : E) (t : Icc a b) (w : Fin m → E) :
    timeSliceL r m (lineDerivL v f) x t w = timeSliceL r (m + 1) f x t (Fin.snoc w v) := by
  rw [lineDerivL_eq, timeSliceL_lineDerivMap, HolderSpace.compLeftL_apply, evalLastL_apply]

/-- The value of `∂_v u` is the first spatial field of `u` evaluated on `v`. -/
@[simp]
theorem lineDerivL_apply (v : E) (f : ParabolicCkHolderSpace (k + 1) α E F hab)
    (p : slab (E := E) a b) : lineDerivL v f p = mixedDerivL 0 1 f p fun _ ↦ v := by
  rw [lineDerivL_eq, lineDerivMap_apply]

/-- The slices `y ↦ u (y, t)` of `u ∈ C_{par,b}^{k+1+α}` are differentiable, with derivative
`v ↦ lineDerivL v u (x, t)` at `x`. -/
private theorem exists_hasFDerivAt_slabMk (f : ParabolicCkHolderSpace (k + 1) α E F hab) (x : E)
    (t : Icc a b) : ∃ L : E →L[ℝ] F, HasFDerivAt (fun y ↦ f (slabMk y t)) L x ∧
      ∀ v, L v = lineDerivL v f (slabMk x t) := by
  have H := ((continuousMultilinearCurryFin0 ℝ E F).toLinearIsometry.toContinuousLinearMap
    ).hasFDerivAt.comp x (hasFDerivAt_mixedDerivL f (r := 0) (m := 0) (by omega) t x)
  refine ⟨(continuousMultilinearCurryFin0 ℝ E F).toLinearIsometry.toContinuousLinearMap.comp
    (mixedDerivL 0 1 f (slabMk x t)).curryLeft, ?_, fun v ↦ ?_⟩
  · convert H using 1
    funext y
    simp
  · rw [lineDerivL_apply]
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousMultilinearMap.curryLeft_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry, continuousMultilinearCurryFin0_apply]
    congr 1
    funext i
    rw [Subsingleton.elim (α := Fin 1) i 0, Fin.cons_zero]

/-- The slice `y ↦ u (y, t)` has derivative `lineDerivL v u (x, t)` at `x` in the direction
`v`. -/
theorem hasLineDerivAt_lineDerivL (v : E) (f : ParabolicCkHolderSpace (k + 1) α E F hab) (x : E)
    (t : Icc a b) :
    HasLineDerivAt ℝ (fun y ↦ f (slabMk y t)) (lineDerivL v f (slabMk x t)) x v := by
  obtain ⟨L, hL, hv⟩ := exists_hasFDerivAt_slabMk f x t
  rw [← hv]
  exact hL.hasLineDerivAt v

/-- `lineDerivL v u (x, t)` is the line derivative of `y ↦ u (y, t)` at `x` in the direction
`v`. -/
theorem lineDerivL_slabMk (v : E) (f : ParabolicCkHolderSpace (k + 1) α E F hab) (x : E)
    (t : Icc a b) :
    lineDerivL v f (slabMk x t) = _root_.lineDeriv ℝ (fun y ↦ f (slabMk y t)) x v :=
  (hasLineDerivAt_lineDerivL v f x t).lineDeriv.symm

/-- `lineDerivL v u (x, t)` is the Fréchet derivative of `y ↦ u (y, t)` at `x`, applied to
`v`. -/
theorem lineDerivL_slabMk_eq_fderiv (v : E) (f : ParabolicCkHolderSpace (k + 1) α E F hab)
    (x : E) (t : Icc a b) :
    lineDerivL v f (slabMk x t) = fderiv ℝ (fun y ↦ f (slabMk y t)) x v := by
  obtain ⟨L, hL, hv⟩ := exists_hasFDerivAt_slabMk f x t
  rw [hL.fderiv, hv]

/-- The spatial derivative in a direction `v` has operator norm at most `‖v‖`. -/
theorem norm_lineDerivL_le (v : E) :
    ‖lineDerivL (k := k) (α := α) (F := F) (hab := hab) v‖ ≤ ‖v‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg v) _

end TauCeti.ParabolicCkHolderSpace
