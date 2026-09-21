/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.One

/-!
# Bounded `C^{2,α}` maps

This file constructs the Banach space of bounded twice continuously differentiable maps whose
first and second derivatives are bounded and globally Hölder continuous. Its norm is the maximum
of the supremum norm of the function and the Hölder-space norms of its first two derivatives.

An element is represented by its bounded zero-, first-, and second-order fields, subject to the
two Fréchet derivative identities. The derivative data is therefore uniquely determined. Both
identities are closed under uniform convergence, which makes the resulting space complete. This
is the bounded global `C^{2,α}` target space used by Schauder estimates.

## Main declarations

* `TauCeti.C2HolderSpace`: bounded `C²` maps with bounded globally `α`-Hölder first and second
  derivatives.
* `TauCeti.C2HolderSpace.fderiv`: the globally Hölder first derivative field.
* `TauCeti.C2HolderSpace.secondFDeriv`: the globally Hölder second derivative field.
* `TauCeti.C2HolderSpace.instCompleteSpace`: the Banach-space structure.

## References

L. C. Evans, *Partial Differential Equations*, Section 6.3; D. Gilbarg and N. Trudinger,
*Elliptic Partial Differential Equations of Second Order*, Section 4.1.
-/

public section

noncomputable section

namespace TauCeti

open Filter Topology
open scoped BoundedContinuousFunction NNReal

universe u v

variable (α : NNReal) (E : Type u) (F : Type v)
  [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]

namespace C2HolderSpace

/-- The ambient second-order jet of a bounded `C^{2,α}` map. -/
private abbrev C2HolderJet :=
  C1HolderSpace α E F × HolderSpace α E (E →L[Real] E →L[Real] F)

/-- The space of bounded `C²` maps whose first and second Fréchet derivatives are bounded and
globally `α`-Hölder. Its inherited product norm is

`max (max ‖f‖_∞ ‖Df‖_{C^{0,α}}) ‖D²f‖_{C^{0,α}}`.
-/
-- The module system requires exposure while the declarations below construct and project through
-- this graph alias. The final `irreducible` attribute restores the abstraction boundary.
@[expose] def _root_.TauCeti.C2HolderSpace : Type _ :=
  let graph : Submodule Real
      (C1HolderSpace α E F × HolderSpace α E (E →L[Real] E →L[Real] F)) :=
    { carrier := {J |
          ∀ x, HasFDerivAt (J.1.fderiv : E → E →L[Real] F) (J.2 x) x}
      zero_mem' := fun x ↦ by
        change HasFDerivAt
          (((0 : C1HolderSpace α E F).fderiv : HolderSpace α E (E →L[Real] F)) :
            E → E →L[Real] F)
          ((0 : HolderSpace α E (E →L[Real] E →L[Real] F)) x) x
        have hfun : (((0 : C1HolderSpace α E F).fderiv :
            HolderSpace α E (E →L[Real] F)) : E → E →L[Real] F) = fun _ ↦ 0 := by
          rw [C1HolderSpace.fderiv_zero]
          ext
          rfl
        rw [hfun]
        change HasFDerivAt (fun _ : E ↦ (0 : E →L[Real] F)) 0 x
        exact hasFDerivAt_const (x := x) (c := (0 : E →L[Real] F))
      add_mem' := fun {f g} hf hg x ↦ by
        change HasFDerivAt
          ((((f.1 + g.1).fderiv : HolderSpace α E (E →L[Real] F))) :
            E → E →L[Real] F) ((f.2 + g.2) x) x
        have hfun : (((f.1 + g.1).fderiv : HolderSpace α E (E →L[Real] F)) :
            E → E →L[Real] F) =
            (f.1.fderiv : E → E →L[Real] F) + (g.1.fderiv : E → E →L[Real] F) := by
          rw [C1HolderSpace.fderiv_add]
          ext
          rfl
        have hder : (f.2 + g.2) x = f.2 x + g.2 x := rfl
        rw [hfun, hder]
        exact (hf x).add (hg x)
      smul_mem' := fun c {f} hf x ↦ by
        change HasFDerivAt
          ((((c • f.1).fderiv : HolderSpace α E (E →L[Real] F))) :
            E → E →L[Real] F) ((c • f.2) x) x
        have hfun : (((c • f.1).fderiv : HolderSpace α E (E →L[Real] F)) :
            E → E →L[Real] F) = c • (f.1.fderiv : E → E →L[Real] F) := by
          rw [C1HolderSpace.fderiv_smul]
          ext
          rfl
        have hder : (c • f.2) x = c • f.2 x := rfl
        rw [hfun, hder]
        exact (hf x).const_smul c }
  graph

variable {α : NNReal} {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]

instance instNormedAddCommGroup : NormedAddCommGroup (C2HolderSpace α E F) := by
  unfold C2HolderSpace
  infer_instance

instance instNormedSpace : NormedSpace Real (C2HolderSpace α E F) := by
  unfold C2HolderSpace
  infer_instance

private abbrev toJet (f : C2HolderSpace α E F) : C2HolderJet α E F := f.1

private theorem norm_toJet (f : C2HolderSpace α E F) : ‖toJet f‖ = ‖f‖ := by
  exact Submodule.norm_coe f

/-- The underlying bounded continuous function. -/
def toBoundedContinuousFunction (f : C2HolderSpace α E F) : E →ᵇ F :=
  f.1.1.toBoundedContinuousFunction

/-- A bounded `C^{2,α}` element coerces to its underlying function. -/
instance : CoeFun (C2HolderSpace α E F) fun _ ↦ E → F :=
  ⟨fun f ↦ f.toBoundedContinuousFunction⟩

/-- The first derivative as a bounded globally Hölder field. -/
def fderiv (f : C2HolderSpace α E F) : HolderSpace α E (E →L[Real] F) :=
  f.1.1.fderiv

/-- The second derivative as a bounded globally Hölder field. -/
def secondFDeriv (f : C2HolderSpace α E F) :
    HolderSpace α E (E →L[Real] E →L[Real] F) := f.1.2

/-- Construct a bounded `C^{2,α}` map from a function and two compatible derivative fields. -/
def mk (f : E →ᵇ F) (f' : HolderSpace α E (E →L[Real] F))
    (f'' : HolderSpace α E (E →L[Real] E →L[Real] F))
    (hf : ∀ x, HasFDerivAt (f : E → F) (f' x) x)
    (hf' : ∀ x, HasFDerivAt (f' : E → E →L[Real] F) (f'' x) x) :
    C2HolderSpace α E F := by
  refine ⟨(C1HolderSpace.mk f f' hf, f''), ?_⟩
  intro x
  simpa only [C1HolderSpace.fderiv_mk] using hf' x

@[simp] theorem toBoundedContinuousFunction_mk (f : E →ᵇ F)
    (f' : HolderSpace α E (E →L[Real] F))
    (f'' : HolderSpace α E (E →L[Real] E →L[Real] F)) (hf) (hf') :
    toBoundedContinuousFunction (mk f f' f'' hf hf') = f := by
  exact C1HolderSpace.toBoundedContinuousFunction_mk f f' hf

@[simp] theorem fderiv_mk (f : E →ᵇ F) (f' : HolderSpace α E (E →L[Real] F))
    (f'' : HolderSpace α E (E →L[Real] E →L[Real] F)) (hf) (hf') :
    fderiv (mk f f' f'' hf hf') = f' := by
  exact C1HolderSpace.fderiv_mk f f' hf

@[simp] theorem secondFDeriv_mk (f : E →ᵇ F) (f' : HolderSpace α E (E →L[Real] F))
    (f'' : HolderSpace α E (E →L[Real] E →L[Real] F)) (hf) (hf') :
    secondFDeriv (mk f f' f'' hf hf') = f'' := (rfl)

/-- The constant map as a bounded `C^{2,α}` map. -/
def const (c : F) : C2HolderSpace α E F :=
  mk (BoundedContinuousFunction.const E c) 0 0
    (fun x ↦ by
      change HasFDerivAt (fun _ : E ↦ c) 0 x
      exact hasFDerivAt_const (x := x) (c := c))
    (fun x ↦ by
      change HasFDerivAt (fun _ : E ↦ (0 : E →L[Real] F)) 0 x
      exact hasFDerivAt_const (x := x) (c := (0 : E →L[Real] F)))

@[simp]
theorem const_apply (c : F) (x : E) : const (α := α) (E := E) c x = c := by
  rw [const, toBoundedContinuousFunction_mk]
  rfl

/-- A constant bounded `C^{2,α}` map has zero first derivative. -/
@[simp]
theorem fderiv_const (c : F) : fderiv (const (α := α) (E := E) c) = 0 := by
  rw [const, fderiv_mk]

/-- A constant bounded `C^{2,α}` map has zero second derivative. -/
@[simp]
theorem secondFDeriv_const (c : F) : secondFDeriv (const (α := α) (E := E) c) = 0 := by
  rw [const, secondFDeriv_mk]

/-- The recorded first derivative is the Fréchet derivative of the underlying function. -/
theorem hasFDerivAt (f : C2HolderSpace α E F) (x : E) :
    HasFDerivAt (f : E → F) (f.fderiv x) x := by
  have hfun : (f : E → F) = (f.1.1 : E → F) := by
    funext y
    exact C1HolderSpace.toBoundedContinuousFunction_apply f.1.1 y
  rw [hfun]
  exact C1HolderSpace.hasFDerivAt f.1.1 x

/-- The first derivative accessor agrees with Mathlib's `fderiv`. -/
@[simp]
theorem fderiv_eq (f : C2HolderSpace α E F) (x : E) :
    _root_.fderiv Real (f : E → F) x = f.fderiv x :=
  (hasFDerivAt f x).fderiv

/-- A bounded `C^{2,α}` map is differentiable. -/
theorem differentiable (f : C2HolderSpace α E F) : Differentiable Real (f : E → F) := by
  have hfun : (f : E → F) = (f.1.1 : E → F) := by
    funext y
    exact C1HolderSpace.toBoundedContinuousFunction_apply f.1.1 y
  rw [hfun]
  exact C1HolderSpace.differentiable f.1.1

/-- The first derivative field is globally `α`-Hölder. -/
theorem memHolder_fderiv (f : C2HolderSpace α E F) :
    MemHolder α (fun x ↦ _root_.fderiv Real (f : E → F) x) := by
  have hfun : (f : E → F) = (f.1.1 : E → F) := by
    funext y
    exact C1HolderSpace.toBoundedContinuousFunction_apply f.1.1 y
  rw [hfun]
  exact C1HolderSpace.memHolder_fderiv f.1.1

/-- The recorded second derivative is the Fréchet derivative of the first derivative field. -/
theorem hasFDerivAt_fderiv (f : C2HolderSpace α E F) (x : E) :
    HasFDerivAt (f.fderiv : E → E →L[Real] F) (f.secondFDeriv x) x :=
  f.2 x

/-- The second derivative accessor agrees with the Fréchet derivative of the first derivative
field. -/
@[simp]
theorem fderiv_fderiv_eq (f : C2HolderSpace α E F) (x : E) :
    _root_.fderiv Real (f.fderiv : E → E →L[Real] F) x = f.secondFDeriv x :=
  (hasFDerivAt_fderiv f x).fderiv

/-- A bounded `C^{2,α}` map is twice continuously differentiable. -/
theorem contDiff_two (f : C2HolderSpace α E F) : ContDiff Real 2 (f : E → F) := by
  let Df : C1HolderSpace α E (E →L[Real] F) :=
    C1HolderSpace.mk f.fderiv.toBoundedContinuousFunction f.secondFDeriv fun x ↦ by
      have hfun : (f.fderiv.toBoundedContinuousFunction : E → E →L[Real] F) =
          (f.fderiv : E → E →L[Real] F) := by
        funext y
        exact HolderSpace.toBoundedContinuousFunction_apply f.fderiv y
      rw [hfun]
      exact f.hasFDerivAt_fderiv x
  have hDf : ContDiff Real 1 (f.fderiv : E → E →L[Real] F) := by
    have h := C1HolderSpace.contDiff_one Df
    have hfun : (Df : E → E →L[Real] F) = (f.fderiv : E → E →L[Real] F) := by
      funext x
      calc
        Df x = Df.toBoundedContinuousFunction x :=
          (C1HolderSpace.toBoundedContinuousFunction_apply Df x).symm
        _ = f.fderiv.toBoundedContinuousFunction x := by
          change C1HolderSpace.toBoundedContinuousFunction
            (C1HolderSpace.mk f.fderiv.toBoundedContinuousFunction f.secondFDeriv _) x = _
          rw [C1HolderSpace.toBoundedContinuousFunction_mk]
        _ = f.fderiv x := HolderSpace.toBoundedContinuousFunction_apply f.fderiv x
    rw [hfun] at h
    exact h
  change ContDiff Real (1 + 1) (f : E → F)
  rw [contDiff_succ_iff_fderiv]
  refine ⟨f.differentiable, by simp, ?_⟩
  have hfun : _root_.fderiv Real (f : E → F) =
      (f.fderiv : E → E →L[Real] F) := by
    funext x
    exact f.fderiv_eq x
  rw [hfun]
  exact hDf

/-- The second Fréchet derivative of the underlying function is globally `α`-Hölder. -/
theorem memHolder_secondFDeriv (f : C2HolderSpace α E F) :
    MemHolder α (fun x ↦ _root_.fderiv Real
      (_root_.fderiv Real (f : E → F)) x) := by
  have hfirst : _root_.fderiv Real (f : E → F) =
      (f.fderiv : E → E →L[Real] F) := by
    funext x
    exact f.fderiv_eq x
  rw [hfirst]
  have hsecond : (fun x ↦ _root_.fderiv Real (f.fderiv : E → E →L[Real] F) x) =
      (f.secondFDeriv.toBoundedContinuousFunction : E → E →L[Real] E →L[Real] F) := by
    funext x
    exact (f.fderiv_fderiv_eq x).trans
      (HolderSpace.toBoundedContinuousFunction_apply f.secondFDeriv x).symm
  rw [hsecond]
  exact f.secondFDeriv.memHolder

/-- Two bounded `C^{2,α}` maps are equal when their underlying functions agree pointwise. -/
@[ext]
theorem ext {f g : C2HolderSpace α E F} (h : ∀ x, f x = g x) : f = g := by
  have hfirst : f.1.1 = g.1.1 := by
    apply C1HolderSpace.ext
    intro x
    rw [← C1HolderSpace.toBoundedContinuousFunction_apply,
      ← C1HolderSpace.toBoundedContinuousFunction_apply]
    exact h x
  have hder : f.fderiv = g.fderiv := by
    change f.1.1.fderiv = g.1.1.fderiv
    rw [hfirst]
  have hsecond : f.secondFDeriv = g.secondFDeriv := by
    apply HolderSpace.ext
    intro x
    calc
      f.secondFDeriv x = _root_.fderiv Real
          (f.fderiv : E → E →L[Real] F) x := (f.fderiv_fderiv_eq x).symm
      _ = _root_.fderiv Real (g.fderiv : E → E →L[Real] F) x := by rw [hder]
      _ = g.secondFDeriv x := g.fderiv_fderiv_eq x
  apply Subtype.ext
  exact Prod.ext hfirst hsecond

/-- Forgetting the derivatives defines a continuous linear map to bounded continuous functions. -/
def valueL : C2HolderSpace α E F →L[Real] (E →ᵇ F) :=
  (C1HolderSpace.valueL (α := α) (E := E) (F := F)).comp
    ((ContinuousLinearMap.fst Real (C1HolderSpace α E F)
      (HolderSpace α E (E →L[Real] E →L[Real] F))).comp (by
        unfold C2HolderSpace
        exact Submodule.subtypeL _))

@[simp] theorem valueL_apply (f : C2HolderSpace α E F) :
    valueL f = f.toBoundedContinuousFunction := by
  exact C1HolderSpace.valueL_apply f.1.1

/-- Returning the first derivative defines a continuous linear map to its Hölder space. -/
def fderivL : C2HolderSpace α E F →L[Real] HolderSpace α E (E →L[Real] F) :=
  (C1HolderSpace.fderivL (α := α) (E := E) (F := F)).comp
    ((ContinuousLinearMap.fst Real (C1HolderSpace α E F)
      (HolderSpace α E (E →L[Real] E →L[Real] F))).comp (by
        unfold C2HolderSpace
        exact Submodule.subtypeL _))

@[simp] theorem fderivL_apply (f : C2HolderSpace α E F) :
    fderivL f = f.fderiv := by
  exact C1HolderSpace.fderivL_apply f.1.1

/-- Returning the second derivative defines a continuous linear map to its Hölder space. -/
def secondFDerivL : C2HolderSpace α E F →L[Real]
    HolderSpace α E (E →L[Real] E →L[Real] F) :=
  (ContinuousLinearMap.snd Real
    (C1HolderSpace α E F)
    (HolderSpace α E (E →L[Real] E →L[Real] F))).comp (by
      unfold C2HolderSpace
      exact Submodule.subtypeL _)

@[simp] theorem secondFDerivL_apply (f : C2HolderSpace α E F) :
    secondFDerivL f = f.secondFDeriv := (rfl)

@[simp] theorem toBoundedContinuousFunction_zero :
    toBoundedContinuousFunction (0 : C2HolderSpace α E F) = 0 := by
  simpa only [valueL_apply] using (valueL (α := α) (E := E) (F := F)).map_zero

@[simp] theorem fderiv_zero : fderiv (0 : C2HolderSpace α E F) = 0 := by
  simpa only [fderivL_apply] using
    (fderivL (α := α) (E := E) (F := F)).map_zero

@[simp] theorem secondFDeriv_zero : secondFDeriv (0 : C2HolderSpace α E F) = 0 := by
  simpa only [secondFDerivL_apply] using
    (secondFDerivL (α := α) (E := E) (F := F)).map_zero

@[simp] theorem toBoundedContinuousFunction_add (f g : C2HolderSpace α E F) :
    toBoundedContinuousFunction (f + g) =
      f.toBoundedContinuousFunction + g.toBoundedContinuousFunction := by
  simpa only [valueL_apply] using (valueL (α := α) (E := E) (F := F)).map_add f g

@[simp] theorem fderiv_add (f g : C2HolderSpace α E F) :
    fderiv (f + g) = f.fderiv + g.fderiv := by
  simpa only [fderivL_apply] using
    (fderivL (α := α) (E := E) (F := F)).map_add f g

@[simp] theorem secondFDeriv_add (f g : C2HolderSpace α E F) :
    secondFDeriv (f + g) = f.secondFDeriv + g.secondFDeriv := by
  simpa only [secondFDerivL_apply] using
    (secondFDerivL (α := α) (E := E) (F := F)).map_add f g

@[simp] theorem toBoundedContinuousFunction_smul (c : Real) (f : C2HolderSpace α E F) :
    toBoundedContinuousFunction (c • f) = c • f.toBoundedContinuousFunction := by
  simpa only [valueL_apply] using (valueL (α := α) (E := E) (F := F)).map_smul c f

@[simp] theorem fderiv_smul (c : Real) (f : C2HolderSpace α E F) :
    fderiv (c • f) = c • f.fderiv := by
  simpa only [fderivL_apply] using
    (fderivL (α := α) (E := E) (F := F)).map_smul c f

@[simp] theorem secondFDeriv_smul (c : Real) (f : C2HolderSpace α E F) :
    secondFDeriv (c • f) = c • f.secondFDeriv := by
  simpa only [secondFDerivL_apply] using
    (secondFDerivL (α := α) (E := E) (F := F)).map_smul c f

/-- The `C^{2,α}` norm is the maximum of the supremum norm and the two derivative Hölder norms. -/
theorem norm_eq_max (f : C2HolderSpace α E F) :
    ‖f‖ = max (max ‖f.toBoundedContinuousFunction‖ ‖f.fderiv‖) ‖f.secondFDeriv‖ := by
  rw [← norm_toJet f]
  rw [Prod.norm_def, C1HolderSpace.norm_eq_max]
  rfl

/-- The supremum norm of the function is controlled by its `C^{2,α}` norm. -/
theorem norm_toBoundedContinuousFunction_le (f : C2HolderSpace α E F) :
    ‖f.toBoundedContinuousFunction‖ ≤ ‖f‖ := by
  rw [norm_eq_max]
  exact le_trans (le_max_left _ _) (le_max_left _ _)

/-- The Hölder norm of the first derivative is controlled by the `C^{2,α}` norm. -/
theorem norm_fderiv_le (f : C2HolderSpace α E F) : ‖f.fderiv‖ ≤ ‖f‖ := by
  rw [norm_eq_max]
  exact le_trans (le_max_right _ _) (le_max_left _ _)

/-- The Hölder norm of the second derivative is controlled by the `C^{2,α}` norm. -/
theorem norm_secondFDeriv_le (f : C2HolderSpace α E F) : ‖f.secondFDeriv‖ ≤ ‖f‖ := by
  rw [norm_eq_max]
  exact le_max_right _ _

/-- The second-order derivative graph defining `C2HolderSpace` is closed. -/
private theorem isClosed_c2HolderSpace :
    IsClosed {J : C2HolderJet α E F |
      ∀ x, HasFDerivAt (J.1.fderiv : E → E →L[Real] F) (J.2 x) x} := by
  let secondJet : C2HolderJet α E F →
      (E →ᵇ (E →L[Real] F)) × HolderSpace α E (E →L[Real] E →L[Real] F) :=
    fun J ↦ (HolderSpace.toBoundedContinuousFunctionCLM J.1.fderiv, J.2)
  have hfirst : Continuous (fun J : C2HolderJet α E F ↦ J.1.fderiv) := by
    apply ((C1HolderSpace.fderivL (α := α) (E := E) (F := F)).continuous.comp
      continuous_fst).congr
    intro J
    exact C1HolderSpace.fderivL_apply J.1
  have hsecond : Continuous secondJet := by
    exact (HolderSpace.toBoundedContinuousFunctionCLM.continuous.comp hfirst).prodMk
      continuous_snd
  have hset : {J : C2HolderJet α E F |
        ∀ x, HasFDerivAt (J.1.fderiv : E → E →L[Real] F) (J.2 x) x} =
      secondJet ⁻¹' {J | ∀ x, HasFDerivAt (J.1 : E → E →L[Real] F) (J.2 x) x} := by
    ext J
    dsimp only [secondJet, Set.mem_preimage, Set.mem_ofPred_eq]
    have heq : (J.1.fderiv.toBoundedContinuousFunction : E → E →L[Real] F) =
        (J.1.fderiv : E → E →L[Real] F) := by
      funext x
      exact HolderSpace.toBoundedContinuousFunction_apply J.1.fderiv x
    constructor
    · intro h x
      change HasFDerivAt
        ((HolderSpace.toBoundedContinuousFunctionCLM J.1.fderiv :
          E →ᵇ (E →L[Real] F)) : E → E →L[Real] F) (J.2 x) x
      rw [HolderSpace.toBoundedContinuousFunctionCLM_apply, heq]
      exact h x
    · intro h x
      have hx := h x
      change HasFDerivAt
        ((HolderSpace.toBoundedContinuousFunctionCLM J.1.fderiv :
          E →ᵇ (E →L[Real] F)) : E → E →L[Real] F) (J.2 x) x at hx
      rw [HolderSpace.toBoundedContinuousFunctionCLM_apply, heq] at hx
      exact hx
  rw [hset]
  exact (HolderSpace.isClosed_fderivGraph
    (α := α) (E := E) (Y := E →L[Real] F)).preimage hsecond

/-- Bounded `C^{2,α}` maps into a Banach space form a Banach space. -/
noncomputable instance instCompleteSpace [CompleteSpace F] :
    CompleteSpace (C2HolderSpace α E F) := by
  unfold C2HolderSpace
  exact (isClosed_c2HolderSpace (α := α) (E := E) (F := F)).completeSpace_coe

attribute [irreducible] _root_.TauCeti.C2HolderSpace

end C2HolderSpace

end TauCeti
