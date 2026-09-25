/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.One
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-!
# Bounded `C^{2,α}` maps

This file constructs the normed space of bounded twice continuously differentiable maps whose
first derivative is bounded and whose second derivative is bounded and globally Hölder continuous,
and proves that it is Banach when the codomain is Banach. Its max norm is equivalent to the usual
`C^{2,α}` norm

`‖f‖_∞ + ‖Df‖_∞ + ‖D²f‖_∞ + [D²f]_α`.

An element is represented recursively by a bounded value field and a `C^{1,α}` first-derivative
field, subject to the Fréchet derivative identity. The derivative data is therefore uniquely
determined. The identity is closed under uniform convergence, which makes the resulting space
complete when the codomain is complete. This is the bounded global `C^{2,α}` target space used by
Schauder estimates.

## Main declarations

* `TauCeti.C2HolderSpace`: bounded `C²` maps with bounded first derivative and bounded globally
  `α`-Hölder second derivative.
* `TauCeti.C2HolderSpace.fderiv`: the bounded continuous first derivative field.
* `TauCeti.C2HolderSpace.secondFDeriv`: the globally Hölder second derivative field.
* `TauCeti.C2HolderSpace.instCompleteSpace`: completeness when the codomain is complete.

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

namespace C2HolderSpace

/-- The ambient second-order jet of a bounded `C^{2,α}` map. -/
private abbrev C2HolderJet := (E →ᵇ F) × C1HolderSpace α E (E →L[ℝ] F)

/-- The space of bounded `C²` maps whose first derivative is bounded and whose second derivative
is bounded and globally `α`-Hölder. Its inherited product norm is

`max ‖f‖_∞ (max ‖Df‖_∞ (‖D²f‖_∞ + [D²f]_α))`.
-/
-- The module system requires exposure while the declarations below construct and project through
-- this graph alias. The final `irreducible` attribute restores the abstraction boundary.
@[expose] def _root_.TauCeti.C2HolderSpace : Type _ :=
  let graph : Submodule ℝ ((E →ᵇ F) × C1HolderSpace α E (E →L[ℝ] F)) :=
    { carrier := {J | ∀ x, HasFDerivAt (J.1 : E → F) (C1HolderSpace.valueL J.2 x) x}
      zero_mem' := fun x ↦ by
        have hfun : ((0 : E →ᵇ F) : E → F) = fun _ ↦ 0 := by
          ext
          rfl
        rw [Prod.fst_zero, Prod.snd_zero, hfun, map_zero]
        exact hasFDerivAt_const (x := x) (c := (0 : F))
      add_mem' := fun {f g} hf hg x ↦ by
        have hfun : (((f + g).1 : E →ᵇ F) : E → F) =
            (f.1 : E → F) + (g.1 : E → F) := by
          ext
          rfl
        have hder : (f + g).2 = f.2 + g.2 := rfl
        rw [hfun, hder, map_add]
        exact (hf x).add (hg x)
      smul_mem' := fun c {f} hf x ↦ by
        have hfun : (((c • f).1 : E →ᵇ F) : E → F) = c • (f.1 : E → F) := by
          ext
          rfl
        have hder : (c • f).2 = c • f.2 := rfl
        rw [hfun, hder, map_smul]
        exact (hf x).const_smul c }
  graph

variable {α : ℝ≥0} {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

instance instNormedAddCommGroup : NormedAddCommGroup (C2HolderSpace α E F) := by
  unfold C2HolderSpace
  infer_instance

instance instNormedSpace : NormedSpace ℝ (C2HolderSpace α E F) := by
  unfold C2HolderSpace
  infer_instance

private abbrev toJet (f : C2HolderSpace α E F) : C2HolderJet α E F := f.1

private theorem norm_toJet (f : C2HolderSpace α E F) : ‖toJet f‖ = ‖f‖ :=
  Submodule.norm_coe f

/-- The underlying bounded continuous function. -/
def toBoundedContinuousFunction (f : C2HolderSpace α E F) : E →ᵇ F := f.1.1

/-- A bounded `C^{2,α}` element coerces to its underlying function from `E` to `F`. -/
instance instCoeFun : CoeFun (C2HolderSpace α E F) fun _ ↦ E → F :=
  ⟨fun f ↦ f.1.1⟩

attribute [irreducible] instCoeFun

@[simp]
theorem toBoundedContinuousFunction_apply (f : C2HolderSpace α E F) (x : E) :
    f.toBoundedContinuousFunction x = f x := by
  rw [instCoeFun]
  rfl

/-- The first derivative field, retaining its `C^{1,α}` structure. -/
def fderivC1 (f : C2HolderSpace α E F) : C1HolderSpace α E (E →L[ℝ] F) := f.1.2

/-- The first derivative as a bounded continuous field. -/
def fderiv (f : C2HolderSpace α E F) : E →ᵇ (E →L[ℝ] F) :=
  C1HolderSpace.valueL f.fderivC1

/-- The second derivative as a bounded globally Hölder field. -/
def secondFDeriv (f : C2HolderSpace α E F) :
    HolderSpace α E (E →L[ℝ] E →L[ℝ] F) := C1HolderSpace.fderivL f.fderivC1

@[simp]
theorem toBoundedContinuousFunction_fderivC1 (f : C2HolderSpace α E F) :
    C1HolderSpace.toBoundedContinuousFunction f.fderivC1 = f.fderiv := by
  rw [fderiv, C1HolderSpace.valueL_apply]

@[simp]
theorem fderiv_fderivC1 (f : C2HolderSpace α E F) :
    C1HolderSpace.fderiv f.fderivC1 = f.secondFDeriv := by
  rw [secondFDeriv, C1HolderSpace.fderivL_apply]

private theorem toBoundedContinuousFunction_eq_fst (f : C2HolderSpace α E F) :
    f.toBoundedContinuousFunction = (toJet f).1 := rfl

private theorem fderivC1_eq_snd (f : C2HolderSpace α E F) :
    f.fderivC1 = (toJet f).2 := rfl

/-- Construct a bounded `C^{2,α}` map from a function and two compatible derivative fields. -/
def mk (f : E →ᵇ F) (f' : E →ᵇ (E →L[ℝ] F))
    (f'' : HolderSpace α E (E →L[ℝ] E →L[ℝ] F))
    (hf : ∀ x, HasFDerivAt (f : E → F) (f' x) x)
    (hf' : ∀ x, HasFDerivAt (f' : E → E →L[ℝ] F) (f'' x) x) :
    C2HolderSpace α E F := by
  refine ⟨(f, C1HolderSpace.mk f' f'' hf'), ?_⟩
  intro x
  rw [C1HolderSpace.valueL_apply, C1HolderSpace.toBoundedContinuousFunction_mk]
  exact hf x

@[simp]
theorem toBoundedContinuousFunction_mk (f : E →ᵇ F) (f' : E →ᵇ (E →L[ℝ] F))
    (f'' : HolderSpace α E (E →L[ℝ] E →L[ℝ] F)) (hf) (hf') :
    toBoundedContinuousFunction (mk f f' f'' hf hf') = f := by
  rw [toBoundedContinuousFunction, mk]

@[simp]
theorem fderivC1_mk (f : E →ᵇ F) (f' : E →ᵇ (E →L[ℝ] F))
    (f'' : HolderSpace α E (E →L[ℝ] E →L[ℝ] F)) (hf) (hf') :
    fderivC1 (mk f f' f'' hf hf') = C1HolderSpace.mk f' f'' hf' := by
  rw [fderivC1, mk]

@[simp]
theorem fderiv_mk (f : E →ᵇ F) (f' : E →ᵇ (E →L[ℝ] F))
    (f'' : HolderSpace α E (E →L[ℝ] E →L[ℝ] F)) (hf) (hf') :
    fderiv (mk f f' f'' hf hf') = f' := by
  rw [fderiv, fderivC1_mk, C1HolderSpace.valueL_apply,
    C1HolderSpace.toBoundedContinuousFunction_mk]

@[simp]
theorem secondFDeriv_mk (f : E →ᵇ F) (f' : E →ᵇ (E →L[ℝ] F))
    (f'' : HolderSpace α E (E →L[ℝ] E →L[ℝ] F)) (hf) (hf') :
    secondFDeriv (mk f f' f'' hf hf') = f'' := by
  rw [secondFDeriv, fderivC1_mk, C1HolderSpace.fderivL_apply, C1HolderSpace.fderiv_mk]

/-- The constant map as a bounded `C^{2,α}` map. -/
def const (c : F) : C2HolderSpace α E F :=
  mk (BoundedContinuousFunction.const E c)
    (BoundedContinuousFunction.const E (0 : E →L[ℝ] F)) 0
    (fun x ↦ by
      rw [BoundedContinuousFunction.const_apply]
      exact hasFDerivAt_const (x := x) (c := c))
    (fun x ↦ by
      rw [BoundedContinuousFunction.const_apply]
      have hzero : (0 : HolderSpace α E (E →L[ℝ] E →L[ℝ] F)) x = 0 := rfl
      rw [hzero]
      exact hasFDerivAt_const (x := x) (c := (0 : E →L[ℝ] F)))

@[simp]
theorem const_apply (c : F) (x : E) : const (α := α) (E := E) c x = c := by
  rw [← toBoundedContinuousFunction_apply, const, toBoundedContinuousFunction_mk]
  exact BoundedContinuousFunction.const_apply' x c

@[simp]
theorem fderiv_const (c : F) : fderiv (const (α := α) (E := E) c) = 0 := by
  rw [const, fderiv_mk]
  apply DFunLike.ext _ _
  intro x
  exact BoundedContinuousFunction.const_apply' x (0 : E →L[ℝ] F)

@[simp]
theorem secondFDeriv_const (c : F) : secondFDeriv (const (α := α) (E := E) c) = 0 := by
  rw [const, secondFDeriv_mk]

/-- The recorded first derivative is the Fréchet derivative of the underlying function. -/
theorem hasFDerivAt (f : C2HolderSpace α E F) (x : E) :
    HasFDerivAt (f : E → F) (f.fderiv x) x := by
  rw [instCoeFun, fderiv]
  exact f.2 x

/-- The first derivative accessor agrees with Mathlib's `fderiv`. -/
@[simp]
theorem fderiv_eq (f : C2HolderSpace α E F) (x : E) :
    _root_.fderiv ℝ (f : E → F) x = f.fderiv x :=
  (hasFDerivAt f x).fderiv

/-- The Fréchet derivative agrees with the recorded derivative field. -/
theorem fderiv_eq_fderiv (f : C2HolderSpace α E F) :
    _root_.fderiv ℝ (f : E → F) = (f.fderiv : E → E →L[ℝ] F) :=
  funext f.fderiv_eq

/-- A bounded `C^{2,α}` map is differentiable. -/
theorem differentiable (f : C2HolderSpace α E F) : Differentiable ℝ (f : E → F) :=
  fun x ↦ (hasFDerivAt f x).differentiableAt

private theorem fderiv_eq_fderivC1_coe (f : C2HolderSpace α E F) :
    (f.fderiv : E → E →L[ℝ] F) = (f.fderivC1 : E → E →L[ℝ] F) := by
  funext x
  rw [fderiv, C1HolderSpace.valueL_apply,
    C1HolderSpace.toBoundedContinuousFunction_apply]

/-- The recorded second derivative is the Fréchet derivative of the first derivative field. -/
theorem hasFDerivAt_fderiv (f : C2HolderSpace α E F) (x : E) :
    HasFDerivAt (f.fderiv : E → E →L[ℝ] F) (f.secondFDeriv x) x := by
  rw [f.fderiv_eq_fderivC1_coe, ← f.fderiv_fderivC1]
  exact C1HolderSpace.hasFDerivAt f.fderivC1 x

/-- The second derivative accessor agrees with the Fréchet derivative of the first derivative
field. -/
@[simp]
theorem fderiv_fderiv_eq (f : C2HolderSpace α E F) (x : E) :
    _root_.fderiv ℝ (f.fderiv : E → E →L[ℝ] F) x = f.secondFDeriv x :=
  (hasFDerivAt_fderiv f x).fderiv

/-- A bounded `C^{2,α}` map is twice continuously differentiable. -/
theorem contDiff_two (f : C2HolderSpace α E F) : ContDiff ℝ 2 (f : E → F) := by
  rw [← one_add_one_eq_two, contDiff_succ_iff_fderiv]
  refine ⟨f.differentiable, by simp, ?_⟩
  rw [f.fderiv_eq_fderiv]
  rw [f.fderiv_eq_fderivC1_coe]
  exact C1HolderSpace.contDiff_one f.fderivC1

/-- The second Fréchet derivative of the underlying function is globally `α`-Hölder. -/
theorem memHolder_secondFDeriv (f : C2HolderSpace α E F) :
    MemHolder α (fun x ↦ _root_.fderiv ℝ
      (_root_.fderiv ℝ (f : E → F)) x) := by
  rw [f.fderiv_eq_fderiv]
  rw [f.fderiv_eq_fderivC1_coe]
  exact C1HolderSpace.memHolder_fderiv f.fderivC1

private noncomputable def secondIteratedEquiv :
    (E →L[ℝ] E →L[ℝ] F) ≃ₗᵢ[ℝ] E [×2]→L[ℝ] F :=
  (continuousMultilinearCurryFin1 ℝ E (E →L[ℝ] F)).symm.trans
    (continuousMultilinearCurryRightEquiv' ℝ 1 E F).symm

private theorem secondIteratedEquiv_apply (g : E →L[ℝ] E →L[ℝ] F) (m : Fin 2 → E) :
    secondIteratedEquiv (E := E) (F := F) g m = g (m 0) (m 1) := by
  simp [secondIteratedEquiv, Fin.init]

private theorem iteratedFDeriv_two_eq (f : C2HolderSpace α E F) :
    iteratedFDeriv ℝ 2 (f : E → F) =
      (secondIteratedEquiv (E := E) (F := F) : _ → _) ∘
        _root_.fderiv ℝ (_root_.fderiv ℝ (f : E → F)) := by
  funext x
  ext m
  rw [iteratedFDeriv_two_apply, Function.comp_apply, secondIteratedEquiv_apply]

/-- The canonical second iterated Fréchet derivative is globally `α`-Hölder. -/
theorem memHolder_iteratedFDeriv_two (f : C2HolderSpace α E F) :
    MemHolder α (iteratedFDeriv ℝ 2 (f : E → F)) := by
  rw [f.iteratedFDeriv_two_eq]
  simpa using f.memHolder_secondFDeriv.comp
    (secondIteratedEquiv (E := E) (F := F)).lipschitz.holderWith.memHolder

/-- Two bounded `C^{2,α}` maps are equal when their underlying functions agree pointwise. -/
@[ext]
theorem ext {f g : C2HolderSpace α E F} (h : ∀ x, f x = g x) : f = g := by
  have hvalue : f.toBoundedContinuousFunction = g.toBoundedContinuousFunction := by
    ext x
    rw [toBoundedContinuousFunction_apply, toBoundedContinuousFunction_apply]
    exact h x
  have hfirst : f.fderiv = g.fderiv := by
    apply DFunLike.ext _ _
    intro x
    calc
      f.fderiv x = _root_.fderiv ℝ (f : E → F) x := (f.fderiv_eq x).symm
      _ = _root_.fderiv ℝ (g : E → F) x := by
        congr 1
        exact funext h
      _ = g.fderiv x := g.fderiv_eq x
  have hderivative : f.fderivC1 = g.fderivC1 := by
    apply C1HolderSpace.ext
    intro x
    rw [← f.fderiv_eq_fderivC1_coe, ← g.fderiv_eq_fderivC1_coe]
    exact DFunLike.congr_fun hfirst x
  apply Subtype.ext
  exact Prod.ext hvalue hderivative

/-- Returning the `C^{1,α}` first-derivative field is a continuous linear map. -/
def fderivC1L : C2HolderSpace α E F →L[ℝ] C1HolderSpace α E (E →L[ℝ] F) :=
  (ContinuousLinearMap.snd ℝ (E →ᵇ F) (C1HolderSpace α E (E →L[ℝ] F))).comp (by
    unfold C2HolderSpace
    exact Submodule.subtypeL _)

@[simp]
theorem fderivC1L_apply (f : C2HolderSpace α E F) : fderivC1L f = f.fderivC1 := by
  rw [fderivC1L]
  rfl

@[simp]
theorem fderivC1_const (c : F) :
    fderivC1 (const (α := α) (E := E) c) = 0 := by
  apply C1HolderSpace.ext
  intro x
  calc
    fderivC1 (const (α := α) (E := E) c) x =
        fderiv (const (α := α) (E := E) c) x :=
      congrFun (fderiv_eq_fderivC1_coe (const (α := α) (E := E) c)).symm x
    _ = 0 := by rw [fderiv_const]; rfl
    _ = (0 : C1HolderSpace α E (E →L[ℝ] F)) x :=
      (C1HolderSpace.zero_apply x).symm

@[simp]
theorem fderivC1_zero : fderivC1 (0 : C2HolderSpace α E F) = 0 := by
  simpa only [fderivC1L_apply] using
    (fderivC1L (α := α) (E := E) (F := F)).map_zero

@[simp]
theorem fderivC1_add (f g : C2HolderSpace α E F) :
    fderivC1 (f + g) = f.fderivC1 + g.fderivC1 := by
  simpa only [fderivC1L_apply] using
    (fderivC1L (α := α) (E := E) (F := F)).map_add f g

@[simp]
theorem fderivC1_smul (c : ℝ) (f : C2HolderSpace α E F) :
    fderivC1 (c • f) = c • f.fderivC1 := by
  simpa only [fderivC1L_apply] using
    (fderivC1L (α := α) (E := E) (F := F)).map_smul c f

/-- Forgetting the derivatives defines a continuous linear map to bounded continuous functions. -/
def valueL : C2HolderSpace α E F →L[ℝ] (E →ᵇ F) :=
  (ContinuousLinearMap.fst ℝ (E →ᵇ F) (C1HolderSpace α E (E →L[ℝ] F))).comp (by
    unfold C2HolderSpace
    exact Submodule.subtypeL _)

@[simp]
theorem valueL_apply (f : C2HolderSpace α E F) :
    valueL f = f.toBoundedContinuousFunction := by
  rw [valueL, toBoundedContinuousFunction]
  rfl

/-- Returning the first derivative defines a continuous linear map to bounded continuous fields. -/
def fderivL : C2HolderSpace α E F →L[ℝ] (E →ᵇ (E →L[ℝ] F)) :=
  C1HolderSpace.valueL.comp fderivC1L

@[simp]
theorem fderivL_apply (f : C2HolderSpace α E F) : fderivL f = f.fderiv := by
  simp only [fderivL, ContinuousLinearMap.comp_apply, fderivC1L_apply,
    C1HolderSpace.valueL_apply]
  rw [fderiv]
  exact (C1HolderSpace.valueL_apply f.fderivC1).symm

/-- Returning the second derivative defines a continuous linear map to its Hölder space. -/
def secondFDerivL : C2HolderSpace α E F →L[ℝ]
    HolderSpace α E (E →L[ℝ] E →L[ℝ] F) :=
  C1HolderSpace.fderivL.comp fderivC1L

@[simp]
theorem secondFDerivL_apply (f : C2HolderSpace α E F) :
    secondFDerivL f = f.secondFDeriv := by
  simp only [secondFDerivL, ContinuousLinearMap.comp_apply, fderivC1L_apply,
    C1HolderSpace.fderivL_apply]
  rw [secondFDeriv]
  exact (C1HolderSpace.fderivL_apply f.fderivC1).symm

@[simp]
theorem toBoundedContinuousFunction_zero :
    toBoundedContinuousFunction (0 : C2HolderSpace α E F) = 0 := by
  simpa only [valueL_apply] using (valueL (α := α) (E := E) (F := F)).map_zero

@[simp]
theorem fderiv_zero : fderiv (0 : C2HolderSpace α E F) = 0 := by
  simpa only [fderivL_apply] using (fderivL (α := α) (E := E) (F := F)).map_zero

@[simp]
theorem secondFDeriv_zero : secondFDeriv (0 : C2HolderSpace α E F) = 0 := by
  simpa only [secondFDerivL_apply] using
    (secondFDerivL (α := α) (E := E) (F := F)).map_zero

@[simp]
theorem toBoundedContinuousFunction_add (f g : C2HolderSpace α E F) :
    toBoundedContinuousFunction (f + g) =
      f.toBoundedContinuousFunction + g.toBoundedContinuousFunction := by
  simpa only [valueL_apply] using (valueL (α := α) (E := E) (F := F)).map_add f g

@[simp]
theorem fderiv_add (f g : C2HolderSpace α E F) : fderiv (f + g) = f.fderiv + g.fderiv := by
  simpa only [fderivL_apply] using (fderivL (α := α) (E := E) (F := F)).map_add f g

@[simp]
theorem secondFDeriv_add (f g : C2HolderSpace α E F) :
    secondFDeriv (f + g) = f.secondFDeriv + g.secondFDeriv := by
  simpa only [secondFDerivL_apply] using
    (secondFDerivL (α := α) (E := E) (F := F)).map_add f g

@[simp]
theorem toBoundedContinuousFunction_smul (c : ℝ) (f : C2HolderSpace α E F) :
    toBoundedContinuousFunction (c • f) = c • f.toBoundedContinuousFunction := by
  simpa only [valueL_apply] using (valueL (α := α) (E := E) (F := F)).map_smul c f

@[simp]
theorem fderiv_smul (c : ℝ) (f : C2HolderSpace α E F) :
    fderiv (c • f) = c • f.fderiv := by
  simpa only [fderivL_apply] using (fderivL (α := α) (E := E) (F := F)).map_smul c f

@[simp]
theorem secondFDeriv_smul (c : ℝ) (f : C2HolderSpace α E F) :
    secondFDeriv (c • f) = c • f.secondFDeriv := by
  simpa only [secondFDerivL_apply] using
    (secondFDerivL (α := α) (E := E) (F := F)).map_smul c f

@[simp]
theorem zero_apply (x : E) : (0 : C2HolderSpace α E F) x = 0 := by
  rw [← toBoundedContinuousFunction_apply, toBoundedContinuousFunction_zero]
  rfl

@[simp]
theorem add_apply (f g : C2HolderSpace α E F) (x : E) :
    (f + g) x = f x + g x := by
  rw [← toBoundedContinuousFunction_apply, toBoundedContinuousFunction_add,
    BoundedContinuousFunction.add_apply, toBoundedContinuousFunction_apply,
    toBoundedContinuousFunction_apply]

@[simp]
theorem smul_apply (c : ℝ) (f : C2HolderSpace α E F) (x : E) :
    (c • f) x = c • f x := by
  rw [← toBoundedContinuousFunction_apply, toBoundedContinuousFunction_smul,
    BoundedContinuousFunction.smul_apply, toBoundedContinuousFunction_apply]

/-- The `C^{2,α}` norm is the maximum of the two supremum norms and the second-derivative
Hölder norm. -/
theorem norm_eq_max (f : C2HolderSpace α E F) :
    ‖f‖ = max ‖f.toBoundedContinuousFunction‖
      (max ‖f.fderiv‖ ‖f.secondFDeriv‖) := by
  rw [← norm_toJet f, Prod.norm_def, C1HolderSpace.norm_eq_max]
  rw [toBoundedContinuousFunction_eq_fst, ← fderivC1_eq_snd]
  rw [fderiv, secondFDeriv, C1HolderSpace.valueL_apply,
    C1HolderSpace.fderivL_apply]

/-- The supremum norm of the function is controlled by its `C^{2,α}` norm. -/
theorem norm_toBoundedContinuousFunction_le (f : C2HolderSpace α E F) :
    ‖f.toBoundedContinuousFunction‖ ≤ ‖f‖ := by
  rw [norm_eq_max]
  exact le_max_left _ _

/-- The supremum norm of the first derivative is controlled by its `C^{2,α}` norm. -/
theorem norm_fderiv_le (f : C2HolderSpace α E F) : ‖f.fderiv‖ ≤ ‖f‖ := by
  rw [norm_eq_max]
  exact le_trans (le_max_left _ _) (le_max_right _ _)

/-- The Hölder norm of the second derivative is controlled by its `C^{2,α}` norm. -/
theorem norm_secondFDeriv_le (f : C2HolderSpace α E F) : ‖f.secondFDeriv‖ ≤ ‖f‖ := by
  rw [norm_eq_max]
  exact le_trans (le_max_right _ _) (le_max_right _ _)

/-- The second-order derivative graph defining `C2HolderSpace` is closed. -/
private theorem isClosed_c2HolderSpace :
    IsClosed {J : C2HolderJet α E F |
      ∀ x, HasFDerivAt (J.1 : E → F) (C1HolderSpace.valueL J.2 x) x} := by
  let forgetDerivative : C2HolderJet α E F →
      (E →ᵇ F) × (E →ᵇ (E →L[ℝ] F)) :=
    fun J ↦ (J.1, C1HolderSpace.valueL J.2)
  have hcontinuous : Continuous forgetDerivative :=
    continuous_fst.prodMk (C1HolderSpace.valueL.continuous.comp continuous_snd)
  have hset : {J : C2HolderJet α E F |
        ∀ x, HasFDerivAt (J.1 : E → F) (C1HolderSpace.valueL J.2 x) x} =
      forgetDerivative ⁻¹' {J | ∀ x, HasFDerivAt (J.1 : E → F) (J.2 x) x} := by
    ext J
    simp only [forgetDerivative, Set.mem_ofPred_eq, Set.mem_preimage,
      C1HolderSpace.valueL_apply, C1HolderSpace.toBoundedContinuousFunction_apply]
  rw [hset]
  exact (isClosed_setOf_hasFDerivAt (E := E) (Y := F)).preimage hcontinuous

/-- Bounded `C^{2,α}` maps into a Banach space form a Banach space. -/
noncomputable instance instCompleteSpace [CompleteSpace F] :
    CompleteSpace (C2HolderSpace α E F) := by
  unfold C2HolderSpace
  exact (isClosed_c2HolderSpace (α := α) (E := E) (F := F)).completeSpace_coe

attribute [irreducible] instNormedAddCommGroup instNormedSpace
  _root_.TauCeti.C2HolderSpace

end C2HolderSpace

end TauCeti
