/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Normed
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-!
# Bounded `C^{1,α}` maps

This file constructs the normed space of bounded continuously differentiable maps whose Fréchet
derivative is bounded and globally Hölder continuous, and proves that it is Banach when the
codomain is Banach.  Its norm is the maximum of the supremum norm of the function and the
`HolderSpace` norm of its derivative.  This is an equivalent form of the usual `C^{1,α}` norm

`‖f‖_∞ + ‖Df‖_∞ + [Df]_α`.

An element is represented by a bounded continuous function and a Hölder-space derivative, subject
to the condition that the latter is the Fréchet derivative of the former.  The derivative field is
therefore uniquely determined, and `C1HolderSpace.ext` only asks for equality of the functions.

This is the first positive-order member of the bounded global `C^{k,α}` scale used in Schauder
estimates.  It extends `TauCeti.HolderSpace`, which supplies the order-zero member and the complete
space in which the derivative fields converge.

## Main declarations

* `TauCeti.C1HolderSpace`: bounded `C¹` maps with bounded globally `α`-Hölder derivative.
* `TauCeti.C1HolderSpace.valueL`: the continuous linear map forgetting the derivative.
* `TauCeti.C1HolderSpace.fderivL`: the continuous linear map returning the Hölder derivative.
* `TauCeti.C1HolderSpace.instCompleteSpace`: the Banach-space structure.

## References

L. C. Evans, *Partial Differential Equations*, Section 6.3; D. Gilbarg and N. Trudinger,
*Elliptic Partial Differential Equations of Second Order*, Section 4.1.
-/

public section

noncomputable section

namespace TauCeti

open Filter Topology
open scoped NNReal BoundedContinuousFunction

universe u v

variable (α : ℝ≥0) (E : Type u) (F : Type v)
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The ambient jet space for bounded `C^{1,α}` maps: a bounded continuous value field paired with
a bounded globally Hölder derivative field. -/
abbrev C1HolderJet := (E →ᵇ F) × HolderSpace α E (E →L[ℝ] F)

/-- The derivative graph inside the ambient `C^{1,α}` jet space. -/
def c1HolderSubmodule : Submodule ℝ (C1HolderJet α E F) where
  carrier := {J | ∀ x, HasFDerivAt (J.1 : E → F) (J.2 x) x}
  zero_mem' := fun x ↦ by
    have hfun : ((0 : E →ᵇ F) : E → F) = fun _ ↦ 0 := by
      ext
      rfl
    have hder : (0 : HolderSpace α E (E →L[ℝ] F)) x = 0 := rfl
    rw [Prod.fst_zero, Prod.snd_zero, hfun, hder]
    exact hasFDerivAt_const (x := x) (c := (0 : F))
  add_mem' := fun {f g} hf hg x ↦ by
    have hfun : (((f + g).1 : E →ᵇ F) : E → F) =
        (f.1 : E → F) + (g.1 : E → F) := by
      ext
      rfl
    have hder : (f + g).2 x = f.2 x + g.2 x := rfl
    rw [hfun, hder]
    exact (hf x).add (hg x)
  smul_mem' := fun c {f} hf x ↦ by
    have hfun : (((c • f).1 : E →ᵇ F) : E → F) = c • (f.1 : E → F) := by
      ext
      rfl
    have hder : (c • f).2 x = c • f.2 x := rfl
    rw [hfun, hder]
    exact (hf x).const_smul c

/-- The space of bounded `C¹` maps whose Fréchet derivative is bounded and globally
`α`-Hölder.  Its inherited product norm is

`max ‖f‖_∞ (‖Df‖_∞ + [Df]_α)`.
-/
abbrev C1HolderSpace := c1HolderSubmodule α E F

namespace C1HolderSpace

variable {α : ℝ≥0} {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A bounded `C^{1,α}` element coerces to its underlying function from `E` to `F`. -/
instance : CoeFun (C1HolderSpace α E F) fun _ ↦ E → F :=
  ⟨fun f ↦ f.1.1⟩

/-- The underlying bounded continuous function of a bounded `C^{1,α}` map. -/
def toBoundedContinuousFunction (f : C1HolderSpace α E F) : E →ᵇ F := f.1.1

/-- The Fréchet derivative, as a bounded globally Hölder function with values in continuous
linear maps. -/
def fderiv (f : C1HolderSpace α E F) : HolderSpace α E (E →L[ℝ] F) := f.1.2

@[simp]
theorem toBoundedContinuousFunction_apply (f : C1HolderSpace α E F) (x : E) :
    toBoundedContinuousFunction f x = f x := (rfl)

/-- Construct a bounded `C^{1,α}` map from a function, its Hölder derivative, and the derivative
identity. -/
def mk (f : E →ᵇ F) (f' : HolderSpace α E (E →L[ℝ] F))
    (hf : ∀ x, HasFDerivAt (f : E → F) (f' x) x) : C1HolderSpace α E F :=
  ⟨(f, f'), hf⟩

@[simp]
theorem toBoundedContinuousFunction_mk (f : E →ᵇ F)
    (f' : HolderSpace α E (E →L[ℝ] F)) (hf) :
    toBoundedContinuousFunction (mk f f' hf) = f := (rfl)

@[simp]
theorem fderiv_mk (f : E →ᵇ F) (f' : HolderSpace α E (E →L[ℝ] F)) (hf) :
    fderiv (mk f f' hf) = f' := (rfl)

/-- The constant map as a bounded `C^{1,α}` map. -/
def const (c : F) : C1HolderSpace α E F :=
  mk (BoundedContinuousFunction.const E c) 0 fun x ↦ by
    have hder : (0 : HolderSpace α E (E →L[ℝ] F)) x = 0 := rfl
    rw [hder]
    exact hasFDerivAt_const (x := x) (c := c)

@[simp]
theorem const_apply (c : F) (x : E) : const (α := α) (E := E) c x = c := (rfl)

/-- A constant bounded `C^{1,α}` map has zero derivative. -/
@[simp]
theorem fderiv_const (c : F) : fderiv (const (α := α) (E := E) c) = 0 := by
  rw [const, fderiv_mk]

/-- The recorded derivative is the Fréchet derivative of the underlying function. -/
theorem hasFDerivAt (f : C1HolderSpace α E F) (x : E) :
    HasFDerivAt (f : E → F) (fderiv f x) x :=
  f.2 x

/-- The derivative accessor agrees with Mathlib's `fderiv`. -/
@[simp]
theorem fderiv_eq (f : C1HolderSpace α E F) (x : E) :
    _root_.fderiv ℝ (f : E → F) x = fderiv f x :=
  (hasFDerivAt f x).fderiv

/-- A bounded `C^{1,α}` map is differentiable. -/
theorem differentiable (f : C1HolderSpace α E F) : Differentiable ℝ (f : E → F) :=
  fun x ↦ (hasFDerivAt f x).differentiableAt

/-- A bounded `C^{1,α}` map is continuously differentiable. -/
theorem contDiff_one (f : C1HolderSpace α E F) : ContDiff ℝ 1 (f : E → F) := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨differentiable f, ?_⟩
  have hEq : _root_.fderiv ℝ (f : E → F) =
      ((fderiv f).toBoundedContinuousFunction : E → E →L[ℝ] F) := by
    funext x
    exact (fderiv_eq f x).trans
      (HolderSpace.toBoundedContinuousFunction_apply (fderiv f) x).symm
  rw [hEq]
  exact (fderiv f).toBoundedContinuousFunction.continuous

/-- The derivative field of a bounded `C^{1,α}` map is globally `α`-Hölder. -/
theorem memHolder_fderiv (f : C1HolderSpace α E F) :
    MemHolder α (fun x ↦ _root_.fderiv ℝ (f : E → F) x) := by
  have hEq : (fun x ↦ _root_.fderiv ℝ (f : E → F) x) =
      ((fderiv f).toBoundedContinuousFunction : E → E →L[ℝ] F) := by
    funext x
    exact (fderiv_eq f x).trans
      (HolderSpace.toBoundedContinuousFunction_apply (fderiv f) x).symm
  rw [hEq]
  exact (fderiv f).memHolder

/-- Two bounded `C^{1,α}` maps are equal when their underlying functions agree pointwise. -/
@[ext]
theorem ext {f g : C1HolderSpace α E F} (h : ∀ x, f x = g x) : f = g := by
  have hvalue : toBoundedContinuousFunction f = toBoundedContinuousFunction g := by
    ext x
    exact h x
  apply Subtype.ext
  apply Prod.ext hvalue
  apply HolderSpace.ext
  intro x
  calc
    fderiv f x = _root_.fderiv ℝ (f : E → F) x := (fderiv_eq f x).symm
    _ = _root_.fderiv ℝ (g : E → F) x := by
      congr 1
      exact congrArg DFunLike.coe hvalue
    _ = fderiv g x := fderiv_eq g x

/-- Forgetting the derivative defines a continuous linear map to bounded continuous functions. -/
def valueL : C1HolderSpace α E F →L[ℝ] (E →ᵇ F) :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ (f : C1HolderJet α E F).1
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
    1 fun f ↦ by simpa using norm_fst_le (f : C1HolderJet α E F)

@[simp]
theorem valueL_apply (f : C1HolderSpace α E F) :
    valueL f = toBoundedContinuousFunction f :=
  (rfl)

/-- Returning the derivative defines a continuous linear map to the global Hölder space. -/
def fderivL : C1HolderSpace α E F →L[ℝ] HolderSpace α E (E →L[ℝ] F) :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ (f : C1HolderJet α E F).2
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
    1 fun f ↦ by simpa using norm_snd_le (f : C1HolderJet α E F)

@[simp]
theorem fderivL_apply (f : C1HolderSpace α E F) : fderivL f = fderiv f := (rfl)

/-- The `C^{1,α}` norm is the maximum of the supremum norm of the function and the
supremum-plus-Hölder norm of its derivative. -/
theorem norm_eq_max (f : C1HolderSpace α E F) :
    ‖f‖ = max ‖toBoundedContinuousFunction f‖ ‖fderiv f‖ := by
  simpa [toBoundedContinuousFunction, fderiv] using
    Prod.norm_def (f : C1HolderJet α E F)

/-- The supremum norm of the function is controlled by the `C^{1,α}` norm. -/
theorem norm_toBoundedContinuousFunction_le (f : C1HolderSpace α E F) :
    ‖toBoundedContinuousFunction f‖ ≤ ‖f‖ :=
  norm_fst_le (f : C1HolderJet α E F)

/-- The Hölder-space norm of the derivative is controlled by the `C^{1,α}` norm. -/
theorem norm_fderiv_le (f : C1HolderSpace α E F) : ‖fderiv f‖ ≤ ‖f‖ :=
  norm_snd_le (f : C1HolderJet α E F)

/-- The derivative graph defining `C1HolderSpace` is closed. -/
theorem isClosed_c1HolderSubmodule :
    IsClosed (c1HolderSubmodule α E F : Set (C1HolderJet α E F)) := by
  rw [← isSeqClosed_iff_isClosed]
  intro J j hJ hjlim x
  apply hasFDerivAt_of_tendstoUniformly
      (f := fun n ↦ (J n).1) (f' := fun n y ↦ (J n).2 y)
      (g := j.1) (g' := fun y ↦ j.2 y) (l := atTop)
  · have hder : Tendsto (fun n ↦ (J n).2) atTop (𝓝 j.2) :=
      (continuous_snd.tendsto j).comp hjlim
    have hcontinuous : Continuous
        (HolderSpace.toBoundedContinuousFunction :
          HolderSpace α E (E →L[ℝ] F) → E →ᵇ (E →L[ℝ] F)) := by
      have h := (HolderSpace.toBoundedContinuousFunctionCLM
        (α := α) (X := E) (Y := E →L[ℝ] F)).continuous
      apply h.congr
      exact fun f ↦ HolderSpace.toBoundedContinuousFunctionCLM_apply f
    have hderBCF : Tendsto
        (fun n ↦ (J n).2.toBoundedContinuousFunction) atTop
        (𝓝 j.2.toBoundedContinuousFunction) :=
      (hcontinuous.tendsto j.2).comp hder
    have huni := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hderBCF
    have hseq : (fun n y ↦ (J n).2 y) =
        (fun n y ↦ (J n).2.toBoundedContinuousFunction y) := by
      funext n y
      exact (HolderSpace.toBoundedContinuousFunction_apply (J n).2 y).symm
    have hlim : (fun y ↦ j.2 y) =
        (fun y ↦ j.2.toBoundedContinuousFunction y) := by
      funext y
      exact (HolderSpace.toBoundedContinuousFunction_apply j.2 y).symm
    rw [hseq, hlim]
    exact huni
  · intro n y
    exact hJ n y
  · intro y
    exact ((BoundedContinuousFunction.evalCLM ℝ y).continuous.tendsto j.1).comp
      (continuous_fst.tendsto j |>.comp hjlim)

/-- Bounded `C^{1,α}` maps into a Banach space form a Banach space. -/
noncomputable instance instCompleteSpace [CompleteSpace F] :
    CompleteSpace (C1HolderSpace α E F) :=
  isClosed_c1HolderSubmodule.completeSpace_coe

end C1HolderSpace

end TauCeti
