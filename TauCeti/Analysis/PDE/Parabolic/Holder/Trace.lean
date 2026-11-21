/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Two
public import TauCeti.Analysis.PDE.Parabolic.Holder.Restriction
public import TauCeti.Analysis.PDE.Parabolic.Holder.One
public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Basic
public import TauCeti.Analysis.Holder.Iterated
public import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-!
# Spatial traces of bounded parabolic Hölder maps

Every time slice of a bounded order-two parabolic Hölder map belongs to the spatial space
`C_b^{2,α}`. The restriction operator `ParabolicC2HolderSpace.spatialTraceL` has norm at most
one, uniformly over the closed time slab. In particular it supplies both the initial and the
terminal trace, including the endpoints without any extension in time. Under the time reversal
`R (x, s) = (x, T - s)`, the trace of `u ∘ R` at `t` is the trace of `u` at `T - t`; in particular
the initial trace of `u ∘ R` is the terminal trace of `u`.

The target is `CkHolderSpace 2`, with its sum of the supremum norms of the iterated Fréchet
derivatives and the Hölder seminorm of the Hessian. The continuous multilinear operator norm
agrees with the curried Hessian norm in the parabolic space.

The same holds one order lower: every time slice of a bounded order-one parabolic Hölder map
(`ParabolicC1HolderSpace`) belongs to `C_b^{1,α}`, the trace operator
`ParabolicC1HolderSpace.spatialTraceL` has norm at most one at every time of the closed slab, and
time reversal exchanges the initial and terminal traces.

At every order `k`, every time slice of a bounded parabolic Hölder map of order `k`
(`ParabolicCkHolderSpace`) belongs to `C_b^{k,α}`: the slice is `k` times continuously
differentiable, its spatial derivatives through order `k` are the fields `D_x^m u` on that slice,
and the `k`-th one is `α`-Hölder since the parabolic distance restricts to the spatial distance at
a fixed time. The trace operator `ParabolicCkHolderSpace.spatialTraceL` again has norm at most one
at every time of the closed slab. These are the initial and terminal trace maps of the parabolic
Cauchy problem at every derivative order.

## Main declarations

* `TauCeti.ParabolicC2HolderSpace.spatialTraceL`: the trace `C_b^{2+α,1+α/2} → C_b^{2,α}` at a
  time of the slab, of norm at most one.
* `TauCeti.ParabolicC1HolderSpace.spatialTraceL`: the trace `C_{par,b}^{1+α} → C_b^{1,α}` at a
  time of the slab, of norm at most one.
* `TauCeti.ParabolicCkHolderSpace.spatialTraceL`: the trace `C_{par,b}^{k+α} → C_b^{k,α}` at a
  time of the slab, of norm at most one, with the spatial derivatives of the trace given by
  `TauCeti.ParabolicCkHolderSpace.iteratedFDeriv_spatialTrace`.
* `TauCeti.ParabolicC2HolderSpace.spatialTrace_timeReverseLIE` and
  `TauCeti.ParabolicC1HolderSpace.spatialTrace_timeReverseLIE`: the traces of a time reversal.

## References

A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes (2004), Chapter 3.
The construction uses the closed derivative graph of `ParabolicC2HolderSpace` and the spatial
constructor `CkHolderSpace.ofContDiff`.
-/

public section
noncomputable section

namespace TauCeti.ParabolicC2HolderSpace

open Set ParabolicSpaceTime
open scoped NNReal BoundedContinuousFunction

variable {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ} {hab : a < b}

/-- Every closed-slab spatial slice is twice continuously differentiable. -/
theorem contDiff_spatialSlice (f : ParabolicC2HolderSpace α E F hab) (t : Icc a b) :
    ContDiff ℝ 2 (fun x ↦ f (slabMk x t)) := by
  have hx : _root_.fderiv ℝ (fun x ↦ f (slabMk x t)) =
      fun x ↦ spatialFDerivL f (slabMk x t) := funext (f.fderiv_eq t)
  have hxx : _root_.fderiv ℝ (_root_.fderiv ℝ fun x ↦ f (slabMk x t)) =
      fun x ↦ spatialSecondFDerivL f (slabMk x t) :=
    funext (f.fderiv_fderiv_eq t)
  have hc : Continuous (fun x : E ↦ slabMk x t) := by fun_prop
  rw [← one_add_one_eq_two, contDiff_succ_iff_fderiv]
  refine ⟨fun x ↦ (f.hasSpatialFDerivAt t x).differentiableAt, by simp, ?_⟩
  rw [contDiff_one_iff_fderiv, hxx, hx]
  exact ⟨fun x ↦ (f.hasSpatialSecondFDerivAt t x).differentiableAt,
    (spatialSecondFDerivL f).continuous.comp hc⟩

/-- The ordinary derivative of a real spatial slice is its gradient evaluated at one. -/
theorem hasDerivAt_spatialSlice (f : ParabolicC2HolderSpace α ℝ F hab)
    (t : Icc a b) (x : ℝ) :
    HasDerivAt (fun y ↦ f (slabMk y t)) (spatialFDerivL f (slabMk x t) 1) x :=
  (f.hasSpatialFDerivAt t x).hasDerivAt

/-- The derivative of a real spatial slice in terms of the recorded gradient. -/
theorem deriv_spatialSlice (f : ParabolicC2HolderSpace α ℝ F hab)
    (t : Icc a b) (x : ℝ) :
    deriv (fun y ↦ f (slabMk y t)) x = spatialFDerivL f (slabMk x t) 1 :=
  (f.hasDerivAt_spatialSlice t x).deriv

/-- Differentiating the spatial gradient applied to a fixed vector gives the Hessian. -/
theorem hasDerivAt_spatialFDerivL_apply (f : ParabolicC2HolderSpace α ℝ F hab)
    (t : Icc a b) (x v : ℝ) :
    HasDerivAt (fun y ↦ spatialFDerivL f (slabMk y t) v)
      (spatialSecondFDerivL f (slabMk x t) 1 v) x := by
  simpa using (f.hasSpatialSecondFDerivAt t x).hasDerivAt.clm_apply
    (hasDerivAt_const x v)

/-- The derivative of the applied spatial gradient in terms of the recorded Hessian. -/
theorem deriv_spatialFDerivL_apply (f : ParabolicC2HolderSpace α ℝ F hab)
    (t : Icc a b) (x v : ℝ) :
    deriv (fun y ↦ spatialFDerivL f (slabMk y t) v) x =
      spatialSecondFDerivL f (slabMk x t) 1 v :=
  (f.hasDerivAt_spatialFDerivL_apply t x v).deriv

/-- The spatial Hessian has Hölder constant at most the parabolic Hessian seminorm, also
when represented as a continuous multilinear second derivative. -/
theorem holderWith_iteratedFDeriv_two_spatialSlice
    (f : ParabolicC2HolderSpace α E F hab) (t : Icc a b) :
    HolderWith (nnHolderNorm α ((spatialSecondFDerivL f).toBoundedContinuousFunction : _ → _))
      α (iteratedFDeriv ℝ 2 (fun x ↦ f (slabMk x t))) := by
  have hh : HolderWith
      (nnHolderNorm α ((spatialSecondFDerivL f).toBoundedContinuousFunction : _ → _))
      α (fun x : E ↦ spatialSecondFDerivL f (slabMk x t)) := by
    intro x y
    simpa [edist_slabMk] using
      (spatialSecondFDerivL f).memHolder.holderWith (slabMk x t) (slabMk y t)
  have he : (fun x ↦ (continuousMultilinearCurryFin2 ℝ E F).symm
      (spatialSecondFDerivL f (slabMk x t))) =
      iteratedFDeriv ℝ 2 (fun x ↦ f (slabMk x t)) := by
    funext x
    ext v
    rw [continuousMultilinearCurryFin2_symm_apply, f.iteratedFDeriv_two_apply]
  simpa [Function.comp_def, he] using
    (continuousMultilinearCurryFin2 ℝ E F).symm.isometry.lipschitzWith.holderWith.comp hh

private theorem norm_iteratedFDeriv_zero_spatialSlice_le
    (f : ParabolicC2HolderSpace α E F hab) (t : Icc a b) (x : E) :
    ‖iteratedFDeriv ℝ 0 (fun y ↦ f (slabMk y t)) x‖ ≤ ‖valueL f‖ := by
  simpa using (valueL f).norm_coe_le_norm (slabMk x t)

private theorem norm_iteratedFDeriv_one_spatialSlice_le
    (f : ParabolicC2HolderSpace α E F hab) (t : Icc a b) (x : E) :
    ‖iteratedFDeriv ℝ 1 (fun y ↦ f (slabMk y t)) x‖ ≤ ‖spatialFDerivL f‖ := by
  simpa using (spatialFDerivL f).norm_coe_le_norm (slabMk x t)

private theorem norm_iteratedFDeriv_two_spatialSlice_le
    (f : ParabolicC2HolderSpace α E F hab) (t : Icc a b) (x : E) :
    ‖iteratedFDeriv ℝ 2 (fun y ↦ f (slabMk y t)) x‖ ≤
      ‖(spatialSecondFDerivL f).toBoundedContinuousFunction‖ := by
  simpa [f.norm_iteratedFDeriv_two t x] using
    (spatialSecondFDerivL f).toBoundedContinuousFunction.norm_coe_le_norm (slabMk x t)

private theorem bounded_iteratedFDeriv_spatialSlice
    (f : ParabolicC2HolderSpace α E F hab) (t : Icc a b) :
    ∀ i ≤ 2, ∃ C, ∀ x, ‖iteratedFDeriv ℝ i (fun y ↦ f (slabMk y t)) x‖ ≤ C := by
  intro i hi
  interval_cases i
  · exact ⟨_, norm_iteratedFDeriv_zero_spatialSlice_le f t⟩
  · exact ⟨_, norm_iteratedFDeriv_one_spatialSlice_le f t⟩
  · exact ⟨_, norm_iteratedFDeriv_two_spatialSlice_le f t⟩

/-- Restrict a bounded order-two parabolic Hölder map to any time in the closed slab,
with values in the spatial sum-norm `C_b^{2,α}` space. -/
def spatialTrace (f : ParabolicC2HolderSpace α E F hab) (t : Icc a b) :
    CkHolderSpace 2 α E F :=
  CkHolderSpace.ofContDiff (fun x ↦ f (slabMk x t)) (f.contDiff_spatialSlice t)
    (bounded_iteratedFDeriv_spatialSlice f t)
    (f.holderWith_iteratedFDeriv_two_spatialSlice t).memHolder

/-- The underlying function of a spatial trace is restriction to its time slice. -/
theorem coe_spatialTrace (f : ParabolicC2HolderSpace α E F hab) (t : Icc a b) :
    ⇑(f.spatialTrace t) = fun x ↦ f (slabMk x t) :=
  CkHolderSpace.coe_ofContDiff _ _ _ _

@[simp]
theorem spatialTrace_apply (f : ParabolicC2HolderSpace α E F hab) (t : Icc a b) (x : E) :
    f.spatialTrace t x = f (slabMk x t) := by
  simp [spatialTrace]

/-- The first derivative of the trace is the spatial gradient on the same slice. -/
@[simp]
theorem fderiv_spatialTrace (f : ParabolicC2HolderSpace α E F hab) (t : Icc a b) (x : E) :
    _root_.fderiv ℝ (f.spatialTrace t) x = spatialFDerivL f (slabMk x t) := by
  rw [coe_spatialTrace, f.fderiv_eq]

/-- The second iterated derivative of the trace is the parabolic spatial Hessian. -/
@[simp]
theorem iteratedFDeriv_two_spatialTrace_apply (f : ParabolicC2HolderSpace α E F hab)
    (t : Icc a b) (x : E) (v : Fin 2 → E) :
    iteratedFDeriv ℝ 2 (f.spatialTrace t) x v =
      spatialSecondFDerivL f (slabMk x t) (v 0) (v 1) := by
  rw [coe_spatialTrace, f.iteratedFDeriv_two_apply]

private theorem norm_iteratedFDeriv_spatialTrace_le
    (f : ParabolicC2HolderSpace α E F hab) (t : Icc a b) (i : Fin 3)
    {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x, ‖iteratedFDeriv ℝ (i : ℕ) (fun y ↦ f (slabMk y t)) x‖ ≤ C) :
    ‖(f.spatialTrace t).iteratedFDeriv i‖ ≤ C := by
  apply (BoundedContinuousFunction.norm_le hC).2
  intro x
  rw [← CkHolderSpace.iteratedFDeriv_eq, coe_spatialTrace]
  exact h x

/-- The supremum norm of the trace's order-zero field is bounded by the slab value norm. -/
theorem norm_iteratedFDeriv_zero_spatialTrace_le
    (f : ParabolicC2HolderSpace α E F hab) (t : Icc a b) :
    ‖(f.spatialTrace t).iteratedFDeriv 0‖ ≤ ‖valueL f‖ :=
  norm_iteratedFDeriv_spatialTrace_le f t 0 (norm_nonneg (valueL f))
    (norm_iteratedFDeriv_zero_spatialSlice_le f t)

/-- The supremum norm of the trace's first derivative is bounded by the slab gradient norm. -/
theorem norm_iteratedFDeriv_one_spatialTrace_le
    (f : ParabolicC2HolderSpace α E F hab) (t : Icc a b) :
    ‖(f.spatialTrace t).iteratedFDeriv 1‖ ≤ ‖spatialFDerivL f‖ :=
  norm_iteratedFDeriv_spatialTrace_le f t 1 (norm_nonneg (spatialFDerivL f))
    (norm_iteratedFDeriv_one_spatialSlice_le f t)

/-- The supremum norm of the trace's second derivative is bounded by the slab Hessian norm. -/
theorem norm_iteratedFDeriv_two_spatialTrace_le
    (f : ParabolicC2HolderSpace α E F hab) (t : Icc a b) :
    ‖(f.spatialTrace t).iteratedFDeriv 2‖ ≤
      ‖(spatialSecondFDerivL f).toBoundedContinuousFunction‖ :=
  norm_iteratedFDeriv_spatialTrace_le f t 2
    (norm_nonneg (spatialSecondFDerivL f).toBoundedContinuousFunction)
    (norm_iteratedFDeriv_two_spatialSlice_le f t)

/-- Spatial restriction is a contraction for the sum-norm spatial space, uniformly in time. -/
theorem norm_spatialTrace_le (f : ParabolicC2HolderSpace α E F hab) (t : Icc a b) :
    ‖f.spatialTrace t‖ ≤ ‖f‖ := by
  have h0 := f.norm_iteratedFDeriv_zero_spatialTrace_le t
  have h1 := f.norm_iteratedFDeriv_one_spatialTrace_le t
  have h2 := f.norm_iteratedFDeriv_two_spatialTrace_le t
  have hh := (f.holderWith_iteratedFDeriv_two_spatialSlice t).nnholderNorm_le
  have hh' : (nnHolderNorm α (iteratedFDeriv ℝ 2 (fun x ↦ f (slabMk x t))) : ℝ) ≤
      nnHolderNorm α ((spatialSecondFDerivL f).toBoundedContinuousFunction : _ → _) :=
    NNReal.coe_le_coe.mpr hh
  rw [CkHolderSpace.norm_eq, coe_spatialTrace, Fin.sum_univ_three]
  have hn := f.norm_def
  have ht := (timeDerivL f).norm_def
  linarith [norm_nonneg (timeDerivL f)]

/-- Spatial restriction as a bounded linear map. Taking `t = a` or `t = b` gives the initial
or terminal trace with the same operator bound. -/
def spatialTraceL (t : Icc a b) :
    ParabolicC2HolderSpace α E F hab →L[ℝ] CkHolderSpace 2 α E F :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ f.spatialTrace t
      map_add' := fun f g ↦ by
        ext x
        simp [CkHolderSpace.coe_add]
      map_smul' := fun c f ↦ by
        ext x
        simp [CkHolderSpace.coe_smul] }
    1 (fun f ↦ by simpa using f.norm_spatialTrace_le t)

@[simp]
theorem spatialTraceL_apply (t : Icc a b) (f : ParabolicC2HolderSpace α E F hab) :
    spatialTraceL t f = f.spatialTrace t := (rfl)

/-- Spatial restriction preserves addition. -/
@[simp]
theorem spatialTrace_add (f g : ParabolicC2HolderSpace α E F hab) (t : Icc a b) :
    (f + g).spatialTrace t = f.spatialTrace t + g.spatialTrace t :=
  (spatialTraceL t).map_add f g

/-- Spatial restriction preserves subtraction. -/
@[simp]
theorem spatialTrace_sub (f g : ParabolicC2HolderSpace α E F hab) (t : Icc a b) :
    (f - g).spatialTrace t = f.spatialTrace t - g.spatialTrace t :=
  (spatialTraceL t).map_sub f g

/-- Spatial restriction preserves scalar multiplication. -/
@[simp]
theorem spatialTrace_smul (c : ℝ) (f : ParabolicC2HolderSpace α E F hab) (t : Icc a b) :
    (c • f).spatialTrace t = c • f.spatialTrace t :=
  (spatialTraceL t).map_smul c f

/-- The spatial trace of zero is zero. -/
@[simp]
theorem spatialTrace_zero (t : Icc a b) :
    (0 : ParabolicC2HolderSpace α E F hab).spatialTrace t = 0 :=
  (spatialTraceL t).map_zero

/-- All time-slice traces, including both endpoint traces, have operator norm at most one. -/
theorem norm_spatialTraceL_le_one (t : Icc a b) :
    ‖spatialTraceL (α := α) (E := E) (F := F) (hab := hab) t‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-! ### Traces of a time reversal -/

section TimeReversal

variable {a' b' T : ℝ} {ha : a' = T - b} {hb : b' = T - a}

/-- The spatial trace of the time reversal `u ∘ R` at time `t` is the spatial trace of `u` at
time `T - t`. -/
@[simp]
theorem spatialTrace_timeReverseLIE (f : ParabolicC2HolderSpace α E F hab) (t : Icc a' b') :
    (timeReverseLIE T ha hb f).spatialTrace t = f.spatialTrace (iccTimeReverse T ha hb t) := by
  ext x
  simp

/-- The initial trace of the time reversal `u ∘ R`, at `T - b`, is the terminal trace of `u`
at `b`. -/
theorem spatialTrace_timeReverseLIE_left (f : ParabolicC2HolderSpace α E F hab) :
    (timeReverseLIE T ha hb f).spatialTrace
        ⟨a', left_mem_Icc.2 (ha ▸ hb ▸ sub_lt_sub_left hab T).le⟩ =
      f.spatialTrace ⟨b, right_mem_Icc.2 hab.le⟩ := by
  rw [spatialTrace_timeReverseLIE]
  congr 1
  ext
  simp [ha]

end TimeReversal

end TauCeti.ParabolicC2HolderSpace

/-! ### Traces of order-one maps -/

namespace TauCeti.ParabolicC1HolderSpace

open Set ParabolicSpaceTime
open scoped NNReal BoundedContinuousFunction

variable {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ}

/-- Every closed-slab spatial slice of an order-one map is continuously differentiable. -/
theorem contDiff_spatialSlice (f : ParabolicC1HolderSpace α E F a b) (t : Icc a b) :
    ContDiff ℝ 1 (fun x ↦ f (slabMk x t)) := by
  have hx : _root_.fderiv ℝ (fun x ↦ f (slabMk x t)) =
      fun x ↦ spatialFDerivL f (slabMk x t) := funext (f.fderiv_eq t)
  have hc : Continuous (fun x : E ↦ slabMk x t) := by fun_prop
  rw [contDiff_one_iff_fderiv, hx]
  exact ⟨fun x ↦ (f.hasSpatialFDerivAt t x).differentiableAt,
    (spatialFDerivL f).continuous.comp hc⟩

/-- The spatial gradient of a slice has Hölder constant at most the parabolic gradient seminorm,
also when represented as a continuous multilinear first derivative. -/
theorem holderWith_iteratedFDeriv_one_spatialSlice
    (f : ParabolicC1HolderSpace α E F a b) (t : Icc a b) :
    HolderWith (nnHolderNorm α ((spatialFDerivL f).toBoundedContinuousFunction : _ → _))
      α (iteratedFDeriv ℝ 1 (fun x ↦ f (slabMk x t))) := by
  have hh : HolderWith
      (nnHolderNorm α ((spatialFDerivL f).toBoundedContinuousFunction : _ → _))
      α (fun x : E ↦ spatialFDerivL f (slabMk x t)) := by
    intro x y
    simpa [edist_slabMk] using
      (spatialFDerivL f).memHolder.holderWith (slabMk x t) (slabMk y t)
  have he : (fun x ↦ (continuousMultilinearCurryFin1 ℝ E F).symm
      (spatialFDerivL f (slabMk x t))) =
      iteratedFDeriv ℝ 1 (fun x ↦ f (slabMk x t)) := by
    funext x
    ext v
    rw [continuousMultilinearCurryFin1_symm_apply, iteratedFDeriv_one_apply, f.fderiv_eq]
  simpa [Function.comp_def, he] using
    (continuousMultilinearCurryFin1 ℝ E F).symm.isometry.lipschitzWith.holderWith.comp hh

private theorem norm_iteratedFDeriv_zero_spatialSlice_le
    (f : ParabolicC1HolderSpace α E F a b) (t : Icc a b) (x : E) :
    ‖iteratedFDeriv ℝ 0 (fun y ↦ f (slabMk y t)) x‖ ≤ ‖valueL f‖ := by
  simpa using (valueL f).norm_coe_le_norm (slabMk x t)

private theorem norm_iteratedFDeriv_one_spatialSlice_le
    (f : ParabolicC1HolderSpace α E F a b) (t : Icc a b) (x : E) :
    ‖iteratedFDeriv ℝ 1 (fun y ↦ f (slabMk y t)) x‖ ≤
      ‖(spatialFDerivL f).toBoundedContinuousFunction‖ := by
  simpa [norm_iteratedFDeriv_one] using
    (spatialFDerivL f).toBoundedContinuousFunction.norm_coe_le_norm (slabMk x t)

private theorem bounded_iteratedFDeriv_spatialSlice
    (f : ParabolicC1HolderSpace α E F a b) (t : Icc a b) :
    ∀ i ≤ 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ i (fun y ↦ f (slabMk y t)) x‖ ≤ C := by
  intro i hi
  interval_cases i
  · exact ⟨_, norm_iteratedFDeriv_zero_spatialSlice_le f t⟩
  · exact ⟨_, norm_iteratedFDeriv_one_spatialSlice_le f t⟩

/-- Restrict a bounded order-one parabolic Hölder map to any time in the closed slab, with values
in the spatial sum-norm `C_b^{1,α}` space. -/
def spatialTrace (f : ParabolicC1HolderSpace α E F a b) (t : Icc a b) :
    CkHolderSpace 1 α E F :=
  CkHolderSpace.ofContDiff (fun x ↦ f (slabMk x t)) (f.contDiff_spatialSlice t)
    (bounded_iteratedFDeriv_spatialSlice f t)
    (f.holderWith_iteratedFDeriv_one_spatialSlice t).memHolder

/-- The underlying function of a spatial trace is restriction to its time slice. -/
theorem coe_spatialTrace (f : ParabolicC1HolderSpace α E F a b) (t : Icc a b) :
    ⇑(f.spatialTrace t) = fun x ↦ f (slabMk x t) :=
  CkHolderSpace.coe_ofContDiff _ _ _ _

@[simp]
theorem spatialTrace_apply (f : ParabolicC1HolderSpace α E F a b) (t : Icc a b) (x : E) :
    f.spatialTrace t x = f (slabMk x t) :=
  congrFun (f.coe_spatialTrace t) x

/-- The derivative of the trace is the spatial gradient on the same slice. -/
@[simp]
theorem fderiv_spatialTrace (f : ParabolicC1HolderSpace α E F a b) (t : Icc a b) (x : E) :
    _root_.fderiv ℝ (f.spatialTrace t) x = spatialFDerivL f (slabMk x t) := by
  rw [coe_spatialTrace, f.fderiv_eq]

/-- Spatial restriction is a contraction for the sum-norm spatial space, uniformly in time. -/
theorem norm_spatialTrace_le (f : ParabolicC1HolderSpace α E F a b) (t : Icc a b) :
    ‖f.spatialTrace t‖ ≤ ‖f‖ := by
  have h0 : ‖(f.spatialTrace t).iteratedFDeriv 0‖ ≤ ‖valueL f‖ := by
    refine (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 fun x ↦ ?_
    rw [← CkHolderSpace.iteratedFDeriv_eq, coe_spatialTrace]
    exact norm_iteratedFDeriv_zero_spatialSlice_le f t x
  have h1 : ‖(f.spatialTrace t).iteratedFDeriv 1‖ ≤
      ‖(spatialFDerivL f).toBoundedContinuousFunction‖ := by
    refine (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 fun x ↦ ?_
    rw [← CkHolderSpace.iteratedFDeriv_eq, coe_spatialTrace]
    exact norm_iteratedFDeriv_one_spatialSlice_le f t x
  have hh : (nnHolderNorm α (iteratedFDeriv ℝ 1 (fun x ↦ f (slabMk x t))) : ℝ) ≤
      nnHolderNorm α ((spatialFDerivL f).toBoundedContinuousFunction : _ → _) :=
    NNReal.coe_le_coe.mpr (f.holderWith_iteratedFDeriv_one_spatialSlice t).nnholderNorm_le
  have hfull := f.fullNorm_le_norm_le.1
  rw [fullNorm_def, HolderSpace.norm_def (spatialFDerivL f)] at hfull
  rw [CkHolderSpace.norm_eq, coe_spatialTrace, Fin.sum_univ_two]
  linarith [ENNReal.toReal_nonneg
    (a := timeEHolderNorm ((1 + α) / 2) (f : slab (E := E) a b → F))]

/-- Spatial restriction as a bounded linear map. Taking `t = a` or `t = b` gives the initial
or terminal trace with the same operator bound. -/
def spatialTraceL (t : Icc a b) :
    ParabolicC1HolderSpace α E F a b →L[ℝ] CkHolderSpace 1 α E F :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ f.spatialTrace t
      map_add' := fun f g ↦ by
        ext x
        simp [CkHolderSpace.coe_add]
      map_smul' := fun c f ↦ by
        ext x
        simp [CkHolderSpace.coe_smul] }
    1 (fun f ↦ by simpa using f.norm_spatialTrace_le t)

@[simp]
theorem spatialTraceL_apply (t : Icc a b) (f : ParabolicC1HolderSpace α E F a b) :
    spatialTraceL t f = f.spatialTrace t := (rfl)

/-- Spatial restriction preserves addition. -/
@[simp]
theorem spatialTrace_add (f g : ParabolicC1HolderSpace α E F a b) (t : Icc a b) :
    (f + g).spatialTrace t = f.spatialTrace t + g.spatialTrace t :=
  (spatialTraceL t).map_add f g

/-- Spatial restriction preserves scalar multiplication. -/
@[simp]
theorem spatialTrace_smul (c : ℝ) (f : ParabolicC1HolderSpace α E F a b) (t : Icc a b) :
    (c • f).spatialTrace t = c • f.spatialTrace t :=
  (spatialTraceL t).map_smul c f

/-- The spatial trace of zero is zero. -/
@[simp]
theorem spatialTrace_zero (t : Icc a b) :
    (0 : ParabolicC1HolderSpace α E F a b).spatialTrace t = 0 :=
  (spatialTraceL t).map_zero

/-- All time-slice traces, including both endpoint traces, have operator norm at most one. -/
theorem norm_spatialTraceL_le_one (t : Icc a b) :
    ‖spatialTraceL (α := α) (E := E) (F := F) t‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

section TimeReversal

variable {a' b' T : ℝ} {ha : a' = T - b} {hb : b' = T - a}

/-- The spatial trace of the time reversal `u ∘ R` at time `t` is the spatial trace of `u` at
time `T - t`. -/
@[simp]
theorem spatialTrace_timeReverseLIE (f : ParabolicC1HolderSpace α E F a b) (t : Icc a' b') :
    (timeReverseLIE T ha hb f).spatialTrace t = f.spatialTrace (iccTimeReverse T ha hb t) := by
  ext x
  simp

/-- The initial trace of the time reversal `u ∘ R`, at `T - b`, is the terminal trace of `u`
at `b`. -/
theorem spatialTrace_timeReverseLIE_left (hab : a ≤ b) (f : ParabolicC1HolderSpace α E F a b) :
    (timeReverseLIE T ha hb f).spatialTrace
        ⟨a', left_mem_Icc.2 (ha ▸ hb ▸ sub_le_sub_left hab T)⟩ =
      f.spatialTrace ⟨b, right_mem_Icc.2 hab⟩ := by
  rw [spatialTrace_timeReverseLIE]
  congr 1
  ext
  simp [ha]

end TimeReversal

end TauCeti.ParabolicC1HolderSpace

/-! ### Traces of maps of every order -/

namespace TauCeti.ParabolicCkHolderSpace

open Set ParabolicSpaceTime
open scoped NNReal BoundedContinuousFunction

variable {k : ℕ} {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ} {hab : a < b}

/-- Every closed-slab spatial slice of a map of order `k` is `k` times continuously
differentiable. -/
theorem contDiff_spatialSlice (f : ParabolicCkHolderSpace k α E F hab) (t : Icc a b) :
    ContDiff ℝ k (fun x ↦ f (slabMk x t)) := by
  simpa [ContinuousMultilinearMap.curry0_apply] using
    (f.hasFTaylorSeriesUpTo_mixedDerivL 0 t).contDiff

/-- The `k`-th spatial derivative of a slice has Hölder constant at most the parabolic Hölder
seminorm of the top-order field `D_x^k u`. -/
theorem holderWith_iteratedFDeriv_spatialSlice (f : ParabolicCkHolderSpace k α E F hab)
    (t : Icc a b) :
    HolderWith
      (nnHolderNorm α ((mixedDerivHolderL 0 k f).toBoundedContinuousFunction : _ → _))
      α (iteratedFDeriv ℝ k (fun x ↦ f (slabMk x t))) := by
  have he : iteratedFDeriv ℝ k (fun x ↦ f (slabMk x t)) =
      fun x ↦ (mixedDerivHolderL 0 k f).toBoundedContinuousFunction (slabMk x t) := by
    funext x
    rw [toBoundedContinuousFunction_mixedDerivHolderL f (by omega),
      mixedDerivL_zero_slabMk f le_rfl]
  rw [he]
  intro x y
  simpa [edist_slabMk] using
    (mixedDerivHolderL 0 k f).memHolder.holderWith (slabMk x t) (slabMk y t)

/-- Restrict a bounded parabolic Hölder map of order `k` to any time of the closed slab, with
values in the spatial sum-norm space `C_b^{k,α}`. -/
def spatialTrace (f : ParabolicCkHolderSpace k α E F hab) (t : Icc a b) :
    CkHolderSpace k α E F :=
  CkHolderSpace.ofContDiff (fun x ↦ f (slabMk x t)) (f.contDiff_spatialSlice t)
    (fun i hi ↦ ⟨‖mixedDerivL 0 i f‖, fun x ↦ by
      rw [← mixedDerivL_zero_slabMk f hi]
      exact (mixedDerivL 0 i f).norm_coe_le_norm _⟩)
    (f.holderWith_iteratedFDeriv_spatialSlice t).memHolder

/-- The underlying function of a spatial trace is restriction to its time slice. -/
theorem coe_spatialTrace (f : ParabolicCkHolderSpace k α E F hab) (t : Icc a b) :
    ⇑(f.spatialTrace t) = fun x ↦ f (slabMk x t) :=
  CkHolderSpace.coe_ofContDiff _ _ _ _

@[simp]
theorem spatialTrace_apply (f : ParabolicCkHolderSpace k α E F hab) (t : Icc a b) (x : E) :
    f.spatialTrace t x = f (slabMk x t) :=
  congrFun (f.coe_spatialTrace t) x

/-- The spatial derivatives of the trace, through order `k`, are the fields `D_x^m u` on the same
slice. -/
@[simp]
theorem iteratedFDeriv_spatialTrace (f : ParabolicCkHolderSpace k α E F hab) (t : Icc a b)
    {m : ℕ} (hm : m ≤ k) (x : E) :
    iteratedFDeriv ℝ m (f.spatialTrace t) x = mixedDerivL 0 m f (slabMk x t) := by
  rw [coe_spatialTrace, mixedDerivL_zero_slabMk f hm]

/-- The top spatial Hölder field of the trace at `x` agrees with the top purely spatial
parabolic Hölder field at `(x, t)`. -/
theorem iteratedFDerivHolder_spatialTrace (f : ParabolicCkHolderSpace k α E F hab)
    (t : Icc a b) (x : E) :
    (f.spatialTrace t).iteratedFDerivHolder x = mixedDerivHolderL 0 k f (slabMk x t) := by
  rw [CkHolderSpace.iteratedFDerivHolder_apply, iteratedFDeriv_spatialTrace f t le_rfl,
    mixedDerivHolderL_apply f (by simp)]

/-- Spatial restriction is a contraction for the sum-norm spatial space, uniformly in time. -/
theorem norm_spatialTrace_le (f : ParabolicCkHolderSpace k α E F hab) (t : Icc a b) :
    ‖f.spatialTrace t‖ ≤ ‖f‖ := by
  -- The trace norm is bounded by the supremum norms of the spatial fields `D_x^m u` and the
  -- Hölder seminorm of `D_x^k u`; these are among the terms of the norm of `f` at the pairs
  -- `(0, m)`.
  have hD : ∀ i : Fin (k + 1), ‖(f.spatialTrace t).iteratedFDeriv i‖ ≤ ‖mixedDerivL 0 i f‖ :=
    fun i ↦ (BoundedContinuousFunction.norm_le (by positivity)).2 fun x ↦ by
      rw [← CkHolderSpace.iteratedFDeriv_eq, iteratedFDeriv_spatialTrace f t i.is_le]
      exact (mixedDerivL 0 i f).norm_coe_le_norm _
  have hH : (nnHolderNorm α (iteratedFDeriv ℝ k (f.spatialTrace t)) : ℝ) ≤
      ‖mixedDerivHolderL 0 k f‖ := by
    rw [coe_spatialTrace]
    exact (NNReal.coe_le_coe.mpr
      (f.holderWith_iteratedFDeriv_spatialSlice t).nnholderNorm_le).trans
      (HolderSpace.nnHolderNorm_le _)
  have hpairs : ∑ m ∈ Finset.range (k + 1), (‖mixedDerivL 0 m f‖ +
      (‖timeSliceL 0 m f‖ + ‖mixedDerivHolderL 0 m f‖)) ≤ ‖f‖ := by
    have hsub : (Finset.range (k + 1)).image (Prod.mk 0) ⊆ parabolicDerivPairs k := fun p hp ↦ by
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hp
      simpa [Nat.lt_succ_iff] using hm
    have h := Finset.sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ × ℕ ↦ ‖mixedDerivL p.1 p.2 f‖ +
      (‖timeSliceL p.1 p.2 f‖ + ‖mixedDerivHolderL p.1 p.2 f‖)) hsub
      fun _ _ _ ↦ by positivity
    rw [Finset.sum_image fun _ _ _ _ h ↦ Prod.mk_right_injective 0 h] at h
    exact h.trans (norm_eq f).ge
  have htop : ‖mixedDerivHolderL 0 k f‖ ≤ ∑ m ∈ Finset.range (k + 1),
      (‖timeSliceL 0 m f‖ + ‖mixedDerivHolderL 0 m f‖) :=
    (le_add_of_nonneg_left (norm_nonneg _)).trans (Finset.single_le_sum
      (f := fun m ↦ ‖timeSliceL 0 m f‖ + ‖mixedDerivHolderL 0 m f‖)
      (fun _ _ ↦ by positivity) (Finset.self_mem_range_succ k))
  have hsumD : ∑ i : Fin (k + 1), ‖(f.spatialTrace t).iteratedFDeriv i‖ ≤
      ∑ m ∈ Finset.range (k + 1), ‖mixedDerivL 0 m f‖ :=
    (Finset.sum_le_sum fun i _ ↦ hD i).trans_eq
      (Fin.sum_univ_eq_sum_range (fun m ↦ ‖mixedDerivL 0 m f‖) (k + 1))
  rw [Finset.sum_add_distrib] at hpairs
  rw [CkHolderSpace.norm_eq]
  linarith

/-- Spatial restriction as a bounded linear map. Taking `t = a` or `t = b` gives the initial
or terminal trace with the same operator bound. -/
def spatialTraceL (t : Icc a b) :
    ParabolicCkHolderSpace k α E F hab →L[ℝ] CkHolderSpace k α E F :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ f.spatialTrace t
      map_add' := fun f g ↦ by
        ext x
        simp [CkHolderSpace.coe_add]
      map_smul' := fun c f ↦ by
        ext x
        simp [CkHolderSpace.coe_smul] }
    1 (fun f ↦ by simpa using f.norm_spatialTrace_le t)

@[simp low]
theorem spatialTraceL_apply (t : Icc a b) (f : ParabolicCkHolderSpace k α E F hab) :
    spatialTraceL t f = f.spatialTrace t := (rfl)

/-- Spatial restriction preserves addition. -/
@[simp]
theorem spatialTrace_add (f g : ParabolicCkHolderSpace k α E F hab) (t : Icc a b) :
    (f + g).spatialTrace t = f.spatialTrace t + g.spatialTrace t :=
  (spatialTraceL t).map_add f g

/-- Spatial restriction preserves negation. -/
@[simp]
theorem spatialTrace_neg (f : ParabolicCkHolderSpace k α E F hab) (t : Icc a b) :
    (-f).spatialTrace t = -f.spatialTrace t :=
  (spatialTraceL t).map_neg f

/-- Spatial restriction preserves subtraction. -/
@[simp]
theorem spatialTrace_sub (f g : ParabolicCkHolderSpace k α E F hab) (t : Icc a b) :
    (f - g).spatialTrace t = f.spatialTrace t - g.spatialTrace t :=
  (spatialTraceL t).map_sub f g

/-- Spatial restriction preserves scalar multiplication. -/
@[simp]
theorem spatialTrace_smul (c : ℝ) (f : ParabolicCkHolderSpace k α E F hab) (t : Icc a b) :
    (c • f).spatialTrace t = c • f.spatialTrace t :=
  (spatialTraceL t).map_smul c f

/-- The spatial trace of zero is zero. -/
@[simp]
theorem spatialTrace_zero (t : Icc a b) :
    (0 : ParabolicCkHolderSpace k α E F hab).spatialTrace t = 0 :=
  (spatialTraceL t).map_zero

/-- All time-slice traces, including both endpoint traces, have operator norm at most one. -/
theorem norm_spatialTraceL_le_one (t : Icc a b) :
    ‖spatialTraceL (k := k) (α := α) (E := E) (F := F) (hab := hab) t‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end TauCeti.ParabolicCkHolderSpace
