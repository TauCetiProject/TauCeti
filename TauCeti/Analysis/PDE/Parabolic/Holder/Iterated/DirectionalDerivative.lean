/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Multilinear.Curry
public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Differentiation
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# Spatial differentiation in the parabolic Hölder scale

For a direction `h ∈ E`, the spatial directional derivative `u ↦ ∂_h u = D_x u · h` maps the
bounded parabolic Hölder space `C_{par,b}^{k+1+α}` on a nondegenerate closed slab `E × [a, b]`
into `C_{par,b}^{k+α}` on the same slab, with `‖∂_h u‖ ≤ ‖h‖ ‖u‖`. In the parabolic scaling a
spatial derivative has order one, so this is the step down by one order; a time derivative has
order two.

The mixed derivative fields of `∂_h u` are those of `u` with one more spatial derivative, taken
in the direction `h` in the last argument:

`D_t^r D_x^m (∂_h u) (x, t) (h₁, …, h_m) = D_t^r D_x^(m+1) u (x, t) (h₁, …, h_m, h)`

(`TauCeti.ParabolicCkHolderSpace.mixedDerivL_spatialLineDerivL_apply`). The same holds for the
top-order parabolic Hölder fields and for the uniform temporal Hölder slices one order below the
top, and the value of `∂_h u` at `(x, t)` is the derivative of `u (·, t)` at `x` in the direction
`h` (`TauCeti.ParabolicCkHolderSpace.spatialLineDerivL_slabMk`), that is, the spatial derivative
`TauCeti.ParabolicCkHolderSpace.spatialFDerivL` applied to `h`
(`TauCeti.ParabolicCkHolderSpace.spatialLineDerivL_apply_eq_spatialFDerivL`). Spatial
differentiation commutes with the time derivative
(`TauCeti.ParabolicCkHolderSpace.timeDerivL_spatialLineDerivL`).

In the higher-order Schauder theory spatial differentiation is how the order is lowered: the
derivative `∂_i u` of a solution of a parabolic equation in a coordinate direction solves the
differentiated equation, whose data are one order lower.

## Main declarations

* `TauCeti.ParabolicCkHolderSpace.spatialLineDerivL`: the directional derivative
  `∂_h : C_{par,b}^{k+1+α} →L[ℝ] C_{par,b}^{k+α}`.
* `TauCeti.ParabolicCkHolderSpace.mixedDerivL_spatialLineDerivL`,
  `TauCeti.ParabolicCkHolderSpace.mixedDerivHolderL_spatialLineDerivL` and
  `TauCeti.ParabolicCkHolderSpace.timeSliceL_spatialLineDerivL`: its derivative fields, Hölder
  fields and time slices, as compositions with
  `ContinuousMultilinearMap.applyLastL`; their `_apply` forms evaluate them.
* `TauCeti.ParabolicCkHolderSpace.spatialLineDerivL_slabMk`: the values are directional
  derivatives in space.
* `TauCeti.ParabolicCkHolderSpace.spatialLineDerivL_apply_eq_spatialFDerivL`: the values are those
  of the spatial derivative applied to `h`.
* `TauCeti.ParabolicCkHolderSpace.hasSpatialLineDerivAt` and
  `TauCeti.ParabolicCkHolderSpace.spatialLineDerivL_slabMk_eq_lineDeriv`: the time slices have
  line derivative `∂_h u`.
* `TauCeti.ParabolicCkHolderSpace.timeDerivL_spatialLineDerivL`: `∂ₜ (∂_h u) = ∂_h (∂ₜu)`.
* `TauCeti.ParabolicCkHolderSpace.spatialLineDerivL_add` and
  `TauCeti.ParabolicCkHolderSpace.spatialLineDerivL_smul`: linearity in the direction.
* `TauCeti.ParabolicCkHolderSpace.norm_spatialLineDerivL_le`: the operator norm of `∂_h` is at
  most `‖h‖`.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004,
  Chapter 3 (parabolic Hölder spaces).
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996,
  Chapter 8.
-/

public section

noncomputable section

namespace TauCeti.ParabolicCkHolderSpace

open Set ParabolicSpaceTime ContinuousMultilinearMap
open scoped ENNReal NNReal BoundedContinuousFunction

variable {k : ℕ} {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ} {hab : a < b}

/-- The fields of the directional derivative: the fields of `u` with one more spatial
derivative, in the direction `h` in the last argument. -/
private def lineDerivField (h : E) (f : ParabolicCkHolderSpace (k + 1) α E F hab) (r m : ℕ) :
    slab (E := E) a b →ᵇ (E [×m]→L[ℝ] F) :=
  (applyLastL ℝ F m h).compLeftContinuousBounded _ (mixedDerivL r (m + 1) f)

private theorem lineDerivField_apply (h : E) (f : ParabolicCkHolderSpace (k + 1) α E F hab)
    (r m : ℕ) (p : slab (E := E) a b) :
    lineDerivField h f r m p = applyLastL ℝ F m h (mixedDerivL r (m + 1) f p) :=
  rfl

private def lineDeriv (h : E) (f : ParabolicCkHolderSpace (k + 1) α E F hab) :
    ParabolicCkHolderSpace k α E F hab :=
  mk (lineDerivField h f)
    (fun r m hrm t x ↦ by
      have H := (applyLastL ℝ F m h).hasFDerivAt.comp x
        (hasFDerivAt_mixedDerivL f (r := r) (m := m + 1) (by omega) t x)
      rw [applyLastL_comp_curryLeft] at H
      simpa only [Function.comp_def, lineDerivField_apply] using H)
    (fun r m hrm x t ↦ by
      have H := HasFDerivAt.comp_hasDerivWithinAt (t : ℝ) (applyLastL ℝ F m h).hasFDerivAt
        (hasDerivWithinAt_mixedDerivL f (r := r) (m := m + 1) (by omega) x t)
      simpa only [ParabolicC2HolderSpace.timeExtension_def, Function.comp_def,
        lineDerivField_apply] using H)
    (fun r m hrm ↦ ⟨‖h‖₊ * ‖timeSliceL r (m + 1) f‖₊, fun x ↦ by
      have hnorm : ‖timeSliceL r (m + 1) f x‖₊ ≤ ‖timeSliceL r (m + 1) f‖₊ := by
        exact_mod_cast lp.norm_apply_le_norm ENNReal.top_ne_zero (timeSliceL r (m + 1) f) x
      have H := (lipschitzWith_applyLastL (𝕜 := ℝ) (F := F) m h).comp_holderWith
        ((timeSliceL r (m + 1) f x).holderWith_nnnorm.mono hnorm)
      intro t s
      simpa only [lineDerivField_apply, timeSliceL_apply f (r := r) (m := m + 1) (by omega),
        Function.comp_apply] using H t s⟩)
    (fun r m hrm ↦ by
      obtain ⟨C, hC⟩ := memHolder_mixedDerivL f (r := r) (m := m + 1) (by omega)
      exact ((lipschitzWith_applyLastL (𝕜 := ℝ) (F := F) m h).comp_holderWith hC).memHolder)

private theorem mixedDerivL_lineDeriv (h : E) (f : ParabolicCkHolderSpace (k + 1) α E F hab)
    (r m : ℕ) : mixedDerivL r m (lineDeriv h f) = lineDerivField h f r m := by
  by_cases hrm : 2 * r + m ≤ k
  · exact mixedDerivL_mk _ _ _ _ hrm
  · ext1 p
    rw [mixedDerivL_of_lt (by omega), lineDerivField_apply, mixedDerivL_of_lt (by omega)]
    simp

private theorem mixedDerivHolderL_lineDeriv (h : E)
    (f : ParabolicCkHolderSpace (k + 1) α E F hab) (r m : ℕ) :
    mixedDerivHolderL r m (lineDeriv h f) =
      HolderSpace.compLeftL (applyLastL ℝ F m h) (mixedDerivHolderL r (m + 1) f) := by
  refine HolderSpace.ext fun p ↦ ?_
  by_cases hrm : 2 * r + m = k
  · have H := congrArg (fun g ↦ g p)
      (toBoundedContinuousFunction_mixedDerivHolderL (lineDeriv h f) hrm)
    have H' := congrArg (fun g ↦ g p)
      (toBoundedContinuousFunction_mixedDerivHolderL f (r := r) (m := m + 1) (by omega))
    simp only [HolderSpace.toBoundedContinuousFunction_apply, mixedDerivL_lineDeriv,
      lineDerivField_apply] at H H'
    rw [H, HolderSpace.compLeftL_apply, H']
  · rw [mixedDerivHolderL_of_ne hrm, mixedDerivHolderL_of_ne (by omega)]
    simp

private theorem timeSliceL_lineDeriv (h : E) (f : ParabolicCkHolderSpace (k + 1) α E F hab)
    (r m : ℕ) (x : E) : timeSliceL r m (lineDeriv h f) x =
      HolderSpace.compLeftL (applyLastL ℝ F m h) (timeSliceL r (m + 1) f x) := by
  refine HolderSpace.ext fun t ↦ ?_
  by_cases hrm : 2 * r + m + 1 = k
  · rw [timeSliceL_apply _ hrm, mixedDerivL_lineDeriv, lineDerivField_apply,
      HolderSpace.compLeftL_apply, timeSliceL_apply f (by omega)]
  · rw [timeSliceL_of_ne hrm, timeSliceL_of_ne (by omega)]
    simp

private theorem norm_lineDeriv_le (h : E) (f : ParabolicCkHolderSpace (k + 1) α E F hab) :
    ‖lineDeriv h f‖ ≤ ‖h‖ * ‖f‖ := by
  rw [norm_eq, norm_eq, Finset.mul_sum]
  refine Finset.sum_le_sum_of_injOn (fun p : ℕ × ℕ ↦ (p.1, p.2 + 1)) ?_ ?_ ?_ ?_
  · intro p _ q _ hpq
    simp only [Prod.mk.injEq] at hpq
    exact Prod.ext hpq.1 (by omega)
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hp
    simp only [mem_parabolicDerivPairs] at hq ⊢
    omega
  · intro p _
    rw [mul_add, mul_add]
    refine add_le_add ?_ (add_le_add ?_ ?_)
    · rw [mixedDerivL_lineDeriv]
      refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun q ↦ ?_
      rw [lineDerivField_apply]
      exact (applyLastL ℝ F p.2 h).le_of_opNorm_le_of_le (norm_applyLastL_le p.2 h)
        (BoundedContinuousFunction.norm_coe_le_norm _ q)
    · refine lp.norm_le_of_forall_le (by positivity) fun x ↦ ?_
      rw [timeSliceL_lineDeriv]
      exact ((HolderSpace.compLeftL (applyLastL ℝ F p.2 h)).le_opNorm _).trans
        (mul_le_mul ((HolderSpace.norm_compLeftL_le _).trans (norm_applyLastL_le p.2 h))
          (lp.norm_apply_le_norm ENNReal.top_ne_zero _ x) (norm_nonneg _) (norm_nonneg h))
    · rw [mixedDerivHolderL_lineDeriv]
      exact ((HolderSpace.compLeftL (applyLastL ℝ F p.2 h)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right ((HolderSpace.norm_compLeftL_le _).trans
          (norm_applyLastL_le p.2 h)) (norm_nonneg _))
  · intro p _ _
    positivity

private theorem lineDeriv_apply (h : E) (f : ParabolicCkHolderSpace (k + 1) α E F hab)
    (p : slab (E := E) a b) : lineDeriv h f p = mixedDerivL 0 1 f p (fun _ ↦ h) := by
  have hv : (Fin.snoc 0 h : Fin (0 + 1) → E) = fun _ ↦ h :=
    funext fun i ↦ by rw [Fin.fin_one_eq_zero i, ← Fin.last_zero, Fin.snoc_last]
  rw [← mixedDerivL_zero_zero_apply (lineDeriv h f) p 0, mixedDerivL_lineDeriv,
    lineDerivField_apply, applyLastL_apply, hv]

/-- **Spatial differentiation** in the direction `h`, `u ↦ ∂_h u = D_x u · h`, from
`C_{par,b}^{k+1+α}` to `C_{par,b}^{k+α}` on the same closed slab. It lowers the parabolic order by
one, and its operator norm is at most `‖h‖` (`norm_spatialLineDerivL_le`). -/
def spatialLineDerivL (h : E) : ParabolicCkHolderSpace (k + 1) α E F hab →L[ℝ]
    ParabolicCkHolderSpace k α E F hab :=
  LinearMap.mkContinuous
    { toFun := lineDeriv h
      map_add' := fun f g ↦ ext fun p ↦ by
        simp only [lineDeriv_apply, coe_add, Pi.add_apply, map_add,
          add_apply]
      map_smul' := fun c f ↦ ext fun p ↦ by
        simp only [lineDeriv_apply, coe_smul, Pi.smul_apply, map_smul,
          smul_apply, RingHom.id_apply] }
    ‖h‖ fun f ↦ norm_lineDeriv_le h f

private theorem spatialLineDerivL_eq_lineDeriv (h : E)
    (f : ParabolicCkHolderSpace (k + 1) α E F hab) : spatialLineDerivL h f = lineDeriv h f := by
  rw [spatialLineDerivL, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]

/-- The derivative fields of `∂_h u` are those of `u` with one more spatial derivative, composed
with evaluation in the direction `h` in the last argument. -/
theorem mixedDerivL_spatialLineDerivL (h : E) (f : ParabolicCkHolderSpace (k + 1) α E F hab)
    (r m : ℕ) : mixedDerivL r m (spatialLineDerivL h f) =
      (applyLastL ℝ F m h).compLeftContinuousBounded _ (mixedDerivL r (m + 1) f) := by
  rw [spatialLineDerivL_eq_lineDeriv, mixedDerivL_lineDeriv]
  rfl

/-- The top-order parabolic Hölder fields of `∂_h u` are those of `u` with one more spatial
derivative, composed with evaluation in the direction `h` in the last argument. -/
theorem mixedDerivHolderL_spatialLineDerivL (h : E)
    (f : ParabolicCkHolderSpace (k + 1) α E F hab) (r m : ℕ) :
    mixedDerivHolderL r m (spatialLineDerivL h f) =
      HolderSpace.compLeftL (applyLastL ℝ F m h) (mixedDerivHolderL r (m + 1) f) := by
  rw [spatialLineDerivL_eq_lineDeriv, mixedDerivHolderL_lineDeriv]

/-- The uniformly Hölder time slices of `∂_h u` at `x` are those of `u` with one more spatial
derivative, composed with evaluation in the direction `h` in the last argument. -/
theorem timeSliceL_spatialLineDerivL (h : E) (f : ParabolicCkHolderSpace (k + 1) α E F hab)
    (r m : ℕ) (x : E) : timeSliceL r m (spatialLineDerivL h f) x =
      HolderSpace.compLeftL (applyLastL ℝ F m h) (timeSliceL r (m + 1) f x) := by
  rw [spatialLineDerivL_eq_lineDeriv, timeSliceL_lineDeriv]

/-- The derivative fields of `∂_h u` are those of `u` with one more spatial derivative, in the
direction `h` in the last argument. -/
@[simp]
theorem mixedDerivL_spatialLineDerivL_apply (h : E)
    (f : ParabolicCkHolderSpace (k + 1) α E F hab) (r m : ℕ) (p : slab (E := E) a b)
    (v : Fin m → E) :
    mixedDerivL r m (spatialLineDerivL h f) p v = mixedDerivL r (m + 1) f p (Fin.snoc v h) := by
  rw [mixedDerivL_spatialLineDerivL, ContinuousLinearMap.compLeftContinuousBounded_apply,
    applyLastL_apply]

/-- The top-order parabolic Hölder fields of `∂_h u` are those of `u` with one more spatial
derivative, in the direction `h` in the last argument. -/
@[simp]
theorem mixedDerivHolderL_spatialLineDerivL_apply (h : E)
    (f : ParabolicCkHolderSpace (k + 1) α E F hab) (r m : ℕ) (p : slab (E := E) a b)
    (v : Fin m → E) :
    mixedDerivHolderL r m (spatialLineDerivL h f) p v =
      mixedDerivHolderL r (m + 1) f p (Fin.snoc v h) := by
  rw [mixedDerivHolderL_spatialLineDerivL, HolderSpace.compLeftL_apply, applyLastL_apply]

/-- The uniformly Hölder time slices of `∂_h u` are those of `u` with one more spatial
derivative, in the direction `h` in the last argument. -/
@[simp]
theorem timeSliceL_spatialLineDerivL_apply (h : E) (f : ParabolicCkHolderSpace (k + 1) α E F hab)
    (r m : ℕ) (x : E) (t : Icc a b) (v : Fin m → E) :
    timeSliceL r m (spatialLineDerivL h f) x t v = timeSliceL r (m + 1) f x t (Fin.snoc v h) := by
  rw [timeSliceL_spatialLineDerivL, HolderSpace.compLeftL_apply, applyLastL_apply]

/-- The value of `∂_h u` is the first spatial derivative field of `u` on the constant tuple
`h`. -/
@[simp]
theorem spatialLineDerivL_apply (h : E) (f : ParabolicCkHolderSpace (k + 1) α E F hab)
    (p : slab (E := E) a b) : spatialLineDerivL h f p = mixedDerivL 0 1 f p (fun _ ↦ h) := by
  rw [spatialLineDerivL_eq_lineDeriv, lineDeriv_apply]

/-- The value of `∂_h u` at `(x, t)` is the derivative of `u (·, t)` at `x` in the direction
`h`. -/
theorem spatialLineDerivL_slabMk (h : E) (f : ParabolicCkHolderSpace (k + 1) α E F hab) (x : E)
    (t : Icc a b) :
    spatialLineDerivL h f (slabMk x t) = fderiv ℝ (fun y ↦ f (slabMk y t)) x h := by
  rw [spatialLineDerivL_apply, mixedDerivL_zero_slabMk f (by omega), iteratedFDeriv_one_apply]

/-- The value of `∂_h u` is the spatial derivative of `u` applied to `h`. -/
theorem spatialLineDerivL_apply_eq_spatialFDerivL (h : E)
    (f : ParabolicCkHolderSpace (k + 1) α E F hab) (p : slab (E := E) a b) :
    spatialLineDerivL h f p = spatialFDerivL k α E F hab f p h := by
  obtain ⟨x, t, rfl⟩ : ∃ x t, slabMk x t = p := ⟨_, _, slabMk_space_slabTime p⟩
  rw [spatialLineDerivL_slabMk, spatialFDerivL_slabMk]

/-- The time slices of `u` have line derivative `∂_h u` in the direction `h`. -/
theorem hasSpatialLineDerivAt (h : E) (f : ParabolicCkHolderSpace (k + 1) α E F hab)
    (t : Icc a b) (x : E) :
    HasLineDerivAt ℝ (fun y ↦ f (slabMk y t)) (spatialLineDerivL h f (slabMk x t)) x h := by
  rw [spatialLineDerivL_apply_eq_spatialFDerivL]
  exact (f.hasSpatialFDerivAt t x).hasLineDerivAt h

/-- The value of `∂_h u` at `(x, t)` is the line derivative of `u (·, t)` at `x` in the
direction `h`. -/
theorem spatialLineDerivL_slabMk_eq_lineDeriv (h : E)
    (f : ParabolicCkHolderSpace (k + 1) α E F hab) (x : E) (t : Icc a b) :
    spatialLineDerivL h f (slabMk x t) = lineDeriv ℝ (fun y ↦ f (slabMk y t)) x h :=
  (hasSpatialLineDerivAt h f t x).lineDeriv.symm

/-- **Spatial and time derivatives commute**: `∂ₜ (∂_h u) = ∂_h (∂ₜu)` for
`u ∈ C_{par,b}^{(k+3)+α}`. -/
theorem timeDerivL_spatialLineDerivL (h : E) (u : ParabolicCkHolderSpace (k + 3) α E F hab) :
    timeDerivL k α E F hab (spatialLineDerivL h u) =
      spatialLineDerivL h (timeDerivL (k + 1) α E F hab u) := by
  ext p
  rw [← mixedDerivL_zero_zero_apply (timeDerivL k α E F hab (spatialLineDerivL h u)) p 0,
    ← mixedDerivL_zero_zero_apply (spatialLineDerivL h (timeDerivL (k + 1) α E F hab u)) p 0,
    mixedDerivL_timeDerivL, mixedDerivL_spatialLineDerivL_apply,
    mixedDerivL_spatialLineDerivL_apply, mixedDerivL_timeDerivL]

/-- Spatial differentiation is additive in the direction. -/
@[simp]
theorem spatialLineDerivL_add (h h' : E) :
    spatialLineDerivL (k := k) (α := α) (F := F) (hab := hab) (h + h') =
      spatialLineDerivL h + spatialLineDerivL h' := by
  refine ContinuousLinearMap.ext fun f ↦ ext fun p ↦ ?_
  obtain ⟨x, t, rfl⟩ : ∃ x t, slabMk x t = p := ⟨_, _, slabMk_space_slabTime p⟩
  simp only [add_apply, coe_add, Pi.add_apply, spatialLineDerivL_slabMk,
    map_add]

/-- Spatial differentiation is homogeneous in the direction. -/
@[simp]
theorem spatialLineDerivL_smul (c : ℝ) (h : E) :
    spatialLineDerivL (k := k) (α := α) (F := F) (hab := hab) (c • h) =
      c • spatialLineDerivL h := by
  refine ContinuousLinearMap.ext fun f ↦ ext fun p ↦ ?_
  obtain ⟨x, t, rfl⟩ : ∃ x t, slabMk x t = p := ⟨_, _, slabMk_space_slabTime p⟩
  simp only [smul_apply, coe_smul, Pi.smul_apply, spatialLineDerivL_slabMk,
    map_smul]

/-- Spatial differentiation in the direction `h` multiplies the parabolic Hölder norm by at most
`‖h‖`. -/
theorem norm_spatialLineDerivL_apply_le (h : E) (f : ParabolicCkHolderSpace (k + 1) α E F hab) :
    ‖spatialLineDerivL h f‖ ≤ ‖h‖ * ‖f‖ := by
  rw [spatialLineDerivL_eq_lineDeriv]
  exact norm_lineDeriv_le h f

/-- The operator norm of spatial differentiation in the direction `h` is at most `‖h‖`. -/
theorem norm_spatialLineDerivL_le (h : E) :
    ‖spatialLineDerivL (k := k) (α := α) (F := F) (hab := hab) h‖ ≤ ‖h‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg h) _

end TauCeti.ParabolicCkHolderSpace
