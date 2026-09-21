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
first derivative is bounded and whose second derivative is bounded and globally Hölder continuous.
Its norm is the maximum of the supremum norm of the function and the Hölder-space norms of its
first two derivatives.

An element is represented by its bounded zero-, first-, and second-order fields, subject to the
two Fréchet derivative identities. The derivative data is therefore uniquely determined. Both
identities are closed under uniform convergence, which makes the resulting space complete. This
is the bounded global `C^{2,α}` target space used by Schauder estimates.

## Main declarations

* `TauCeti.C2HolderSpace`: bounded `C²` maps with bounded globally `α`-Hölder second derivative.
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
  ((E →ᵇ F) × HolderSpace α E (E →L[Real] F)) ×
    HolderSpace α E (E →L[Real] E →L[Real] F)

/-- The space of bounded `C²` maps whose second Fréchet derivative is bounded and globally
`α`-Hölder. Its inherited product norm is

`max (max ‖f‖_∞ ‖Df‖_{C^{0,α}}) ‖D²f‖_{C^{0,α}}`.
-/
-- The module system requires exposure while the declarations below construct and project through
-- this graph alias. The final `irreducible` attribute restores the abstraction boundary.
@[expose] def _root_.TauCeti.C2HolderSpace : Type _ :=
  let graph : Submodule Real
      (((E →ᵇ F) × HolderSpace α E (E →L[Real] F)) ×
        HolderSpace α E (E →L[Real] E →L[Real] F)) :=
    { carrier := {J |
          (∀ x, HasFDerivAt (J.1.1 : E → F) (J.1.2 x) x) ∧
          ∀ x, HasFDerivAt (J.1.2 : E → E →L[Real] F) (J.2 x) x}
      zero_mem' := by
        constructor
        · intro x
          change HasFDerivAt (fun _ : E ↦ (0 : F)) 0 x
          exact hasFDerivAt_const (x := x) (c := (0 : F))
        · intro x
          change HasFDerivAt (fun _ : E ↦ (0 : E →L[Real] F)) 0 x
          exact hasFDerivAt_const (x := x) (c := (0 : E →L[Real] F))
      add_mem' := fun {f g} hf hg ↦ by
        constructor
        · intro x
          have hfun : (((f + g).1.1 : E →ᵇ F) : E → F) =
              (f.1.1 : E → F) + (g.1.1 : E → F) := by
            ext
            rfl
          have hder : (f + g).1.2 x = f.1.2 x + g.1.2 x := rfl
          rw [hfun, hder]
          exact (hf.1 x).add (hg.1 x)
        · intro x
          have hfun : ((f + g).1.2 : E → E →L[Real] F) =
              (f.1.2 : E → E →L[Real] F) + (g.1.2 : E → E →L[Real] F) := by
            ext
            rfl
          have hder : (f + g).2 x = f.2 x + g.2 x := rfl
          rw [hfun, hder]
          exact (hf.2 x).add (hg.2 x)
      smul_mem' := fun c {f} hf ↦ by
        constructor
        · intro x
          have hfun : (((c • f).1.1 : E →ᵇ F) : E → F) = c • (f.1.1 : E → F) := by
            ext
            rfl
          have hder : (c • f).1.2 x = c • f.1.2 x := rfl
          rw [hfun, hder]
          exact (hf.1 x).const_smul c
        · intro x
          have hfun : ((c • f).1.2 : E → E →L[Real] F) =
              c • (f.1.2 : E → E →L[Real] F) := by
            ext
            rfl
          have hder : (c • f).2 x = c • f.2 x := rfl
          rw [hfun, hder]
          exact (hf.2 x).const_smul c }
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

private theorem norm_toJet (f : C2HolderSpace α E F) : ‖toJet f‖ = ‖f‖ :=
  Submodule.norm_coe f

/-- The underlying bounded continuous function. -/
def toBoundedContinuousFunction (f : C2HolderSpace α E F) : E →ᵇ F := f.1.1.1

/-- A bounded `C^{2,α}` element coerces to its underlying function. -/
instance : CoeFun (C2HolderSpace α E F) fun _ ↦ E → F :=
  ⟨fun f ↦ f.toBoundedContinuousFunction⟩

/-- The first derivative as a bounded globally Hölder field. -/
def fderiv (f : C2HolderSpace α E F) : HolderSpace α E (E →L[Real] F) := f.1.1.2

/-- The second derivative as a bounded globally Hölder field. -/
def secondFDeriv (f : C2HolderSpace α E F) :
    HolderSpace α E (E →L[Real] E →L[Real] F) := f.1.2

@[simp]
theorem toBoundedContinuousFunction_apply (f : C2HolderSpace α E F) (x : E) :
    f.toBoundedContinuousFunction x = f x := (rfl)

/-- Construct a bounded `C^{2,α}` map from a function and two compatible derivative fields. -/
def mk (f : E →ᵇ F) (f' : HolderSpace α E (E →L[Real] F))
    (f'' : HolderSpace α E (E →L[Real] E →L[Real] F))
    (hf : ∀ x, HasFDerivAt (f : E → F) (f' x) x)
    (hf' : ∀ x, HasFDerivAt (f' : E → E →L[Real] F) (f'' x) x) :
    C2HolderSpace α E F :=
  ⟨((f, f'), f''), hf, hf'⟩

@[simp] theorem toBoundedContinuousFunction_mk (f : E →ᵇ F)
    (f' : HolderSpace α E (E →L[Real] F))
    (f'' : HolderSpace α E (E →L[Real] E →L[Real] F)) (hf) (hf') :
    toBoundedContinuousFunction (mk f f' f'' hf hf') = f := (rfl)

@[simp] theorem fderiv_mk (f : E →ᵇ F) (f' : HolderSpace α E (E →L[Real] F))
    (f'' : HolderSpace α E (E →L[Real] E →L[Real] F)) (hf) (hf') :
    fderiv (mk f f' f'' hf hf') = f' := (rfl)

@[simp] theorem secondFDeriv_mk (f : E →ᵇ F) (f' : HolderSpace α E (E →L[Real] F))
    (f'' : HolderSpace α E (E →L[Real] E →L[Real] F)) (hf) (hf') :
    secondFDeriv (mk f f' f'' hf hf') = f'' := (rfl)

/-- The recorded first derivative is the Fréchet derivative of the underlying function. -/
theorem hasFDerivAt (f : C2HolderSpace α E F) (x : E) :
    HasFDerivAt (f : E → F) (f.fderiv x) x :=
  f.2.1 x

/-- The first derivative accessor agrees with Mathlib's `fderiv`. -/
@[simp]
theorem fderiv_eq (f : C2HolderSpace α E F) (x : E) :
    _root_.fderiv Real (f : E → F) x = f.fderiv x :=
  (hasFDerivAt f x).fderiv

/-- A bounded `C^{2,α}` map is differentiable. -/
theorem differentiable (f : C2HolderSpace α E F) : Differentiable Real (f : E → F) :=
  fun x ↦ (f.hasFDerivAt x).differentiableAt

/-- The first derivative field is globally `α`-Hölder. -/
theorem memHolder_fderiv (f : C2HolderSpace α E F) :
    MemHolder α (fun x ↦ _root_.fderiv Real (f : E → F) x) := by
  have hfun : (fun x ↦ _root_.fderiv Real (f : E → F) x) =
      (f.fderiv.toBoundedContinuousFunction : E → E →L[Real] F) := by
    funext x
    exact (f.fderiv_eq x).trans
      (HolderSpace.toBoundedContinuousFunction_apply f.fderiv x).symm
  rw [hfun]
  exact f.fderiv.memHolder

/-- The recorded second derivative is the Fréchet derivative of the first derivative field. -/
theorem hasFDerivAt_fderiv (f : C2HolderSpace α E F) (x : E) :
    HasFDerivAt (f.fderiv : E → E →L[Real] F) (f.secondFDeriv x) x :=
  f.2.2 x

/-- The second derivative accessor agrees with the Fréchet derivative of the first derivative
field. -/
@[simp]
theorem fderiv_fderiv_eq (f : C2HolderSpace α E F) (x : E) :
    _root_.fderiv Real (f.fderiv : E → E →L[Real] F) x = f.secondFDeriv x :=
  (hasFDerivAt_fderiv f x).fderiv

/-- A bounded `C^{2,α}` map is twice continuously differentiable. -/
theorem contDiff_two (f : C2HolderSpace α E F) : ContDiff Real 2 (f : E → F) := by
  change ContDiff Real (1 + 1) (f : E → F)
  rw [contDiff_succ_iff_fderiv]
  refine ⟨f.differentiable, by simp, ?_⟩
  have hfun : _root_.fderiv Real (f : E → F) =
      (f.fderiv : E → E →L[Real] F) := by
    funext x
    exact f.fderiv_eq x
  rw [hfun]
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun x ↦ (f.hasFDerivAt_fderiv x).differentiableAt, ?_⟩
  have hsecond : _root_.fderiv Real (f.fderiv : E → E →L[Real] F) =
      (f.secondFDeriv : E → E →L[Real] E →L[Real] F) := by
    funext x
    exact f.fderiv_fderiv_eq x
  rw [hsecond]
  apply f.secondFDeriv.toBoundedContinuousFunction.continuous.congr
  intro x
  exact HolderSpace.toBoundedContinuousFunction_apply f.secondFDeriv x

/-- The second derivative field is globally `α`-Hölder. -/
theorem memHolder_secondFDeriv (f : C2HolderSpace α E F) :
    MemHolder α (fun x ↦ _root_.fderiv Real
      (f.fderiv : E → E →L[Real] F) x) := by
  have hfun : (fun x ↦ _root_.fderiv Real (f.fderiv : E → E →L[Real] F) x) =
      (f.secondFDeriv.toBoundedContinuousFunction : E → E →L[Real] E →L[Real] F) := by
    funext x
    exact (f.fderiv_fderiv_eq x).trans
      (HolderSpace.toBoundedContinuousFunction_apply f.secondFDeriv x).symm
  rw [hfun]
  exact f.secondFDeriv.memHolder

/-- Two bounded `C^{2,α}` maps are equal when their underlying functions agree pointwise. -/
@[ext]
theorem ext {f g : C2HolderSpace α E F} (h : ∀ x, f x = g x) : f = g := by
  have hvalue : f.toBoundedContinuousFunction = g.toBoundedContinuousFunction := by
    ext x
    exact h x
  have hfirst : f.fderiv = g.fderiv := by
    apply HolderSpace.ext
    intro x
    calc
      f.fderiv x = _root_.fderiv Real (f : E → F) x := (f.fderiv_eq x).symm
      _ = _root_.fderiv Real (g : E → F) x := by
        congr 1
        exact congrArg DFunLike.coe hvalue
      _ = g.fderiv x := g.fderiv_eq x
  have hsecond : f.secondFDeriv = g.secondFDeriv := by
    apply HolderSpace.ext
    intro x
    calc
      f.secondFDeriv x = _root_.fderiv Real
          (f.fderiv : E → E →L[Real] F) x := (f.fderiv_fderiv_eq x).symm
      _ = _root_.fderiv Real (g.fderiv : E → E →L[Real] F) x := by rw [hfirst]
      _ = g.secondFDeriv x := g.fderiv_fderiv_eq x
  apply Subtype.ext
  exact Prod.ext (Prod.ext hvalue hfirst) hsecond

/-- Forgetting the derivatives defines a continuous linear map to bounded continuous functions. -/
def valueL : C2HolderSpace α E F →L[Real] (E →ᵇ F) :=
  (ContinuousLinearMap.fst Real (E →ᵇ F) (HolderSpace α E (E →L[Real] F))).comp
    ((ContinuousLinearMap.fst Real
      ((E →ᵇ F) × HolderSpace α E (E →L[Real] F))
      (HolderSpace α E (E →L[Real] E →L[Real] F))).comp (by
        unfold C2HolderSpace
        exact Submodule.subtypeL _))

@[simp] theorem valueL_apply (f : C2HolderSpace α E F) :
    valueL f = f.toBoundedContinuousFunction := (rfl)

/-- Returning the first derivative defines a continuous linear map to its Hölder space. -/
def fderivL : C2HolderSpace α E F →L[Real] HolderSpace α E (E →L[Real] F) :=
  (ContinuousLinearMap.snd Real (E →ᵇ F) (HolderSpace α E (E →L[Real] F))).comp
    ((ContinuousLinearMap.fst Real
      ((E →ᵇ F) × HolderSpace α E (E →L[Real] F))
      (HolderSpace α E (E →L[Real] E →L[Real] F))).comp (by
        unfold C2HolderSpace
        exact Submodule.subtypeL _))

@[simp] theorem fderivL_apply (f : C2HolderSpace α E F) :
    fderivL f = f.fderiv := (rfl)

/-- Returning the second derivative defines a continuous linear map to its Hölder space. -/
def secondFDerivL : C2HolderSpace α E F →L[Real]
    HolderSpace α E (E →L[Real] E →L[Real] F) :=
  (ContinuousLinearMap.snd Real
    ((E →ᵇ F) × HolderSpace α E (E →L[Real] F))
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

@[simp] theorem zero_apply (x : E) : (0 : C2HolderSpace α E F) x = 0 := by
  rw [← toBoundedContinuousFunction_apply, toBoundedContinuousFunction_zero]
  rfl

@[simp] theorem add_apply (f g : C2HolderSpace α E F) (x : E) :
    (f + g) x = f x + g x := by
  rw [← toBoundedContinuousFunction_apply, toBoundedContinuousFunction_add]
  rfl

@[simp] theorem smul_apply (c : Real) (f : C2HolderSpace α E F) (x : E) :
    (c • f) x = c • f x := by
  rw [← toBoundedContinuousFunction_apply, toBoundedContinuousFunction_smul]
  rfl

/-- The `C^{2,α}` norm is the maximum of the supremum norm and the two derivative Hölder norms. -/
theorem norm_eq_max (f : C2HolderSpace α E F) :
    ‖f‖ = max (max ‖f.toBoundedContinuousFunction‖ ‖f.fderiv‖) ‖f.secondFDeriv‖ := by
  rw [← norm_toJet f]
  rw [Prod.norm_def, Prod.norm_def]
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

/-- Derivative graphs between bounded continuous and Hölder fields are closed. -/
private theorem isClosed_derivativeGraph {Y : Type v}
    [NormedAddCommGroup Y] [NormedSpace Real Y] :
    IsClosed {J : (E →ᵇ Y) × HolderSpace α E (E →L[Real] Y) |
      ∀ x, HasFDerivAt (J.1 : E → Y) (J.2 x) x} := by
  rw [← isSeqClosed_iff_isClosed]
  intro J j hJ hjlim x
  apply hasFDerivAt_of_tendstoUniformly
      (f := fun n ↦ (J n).1) (f' := fun n y ↦ (J n).2 y)
      (g := j.1) (g' := fun y ↦ j.2 y) (l := atTop)
  · have hder : Tendsto (fun n ↦ (J n).2) atTop (𝓝 j.2) :=
      (continuous_snd.tendsto j).comp hjlim
    have hcontinuous : Continuous
        (HolderSpace.toBoundedContinuousFunction :
          HolderSpace α E (E →L[Real] Y) → E →ᵇ (E →L[Real] Y)) := by
      apply HolderSpace.toBoundedContinuousFunctionCLM.continuous.congr
      exact fun f ↦ HolderSpace.toBoundedContinuousFunctionCLM_apply f
    have hderBCF : Tendsto (fun n ↦ (J n).2.toBoundedContinuousFunction) atTop
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
    exact ((BoundedContinuousFunction.evalCLM Real y).continuous.tendsto j.1).comp
      (continuous_fst.tendsto j |>.comp hjlim)

/-- The second-order derivative graph defining `C2HolderSpace` is closed. -/
private theorem isClosed_c2HolderSpace :
    IsClosed {J : C2HolderJet α E F |
      (∀ x, HasFDerivAt (J.1.1 : E → F) (J.1.2 x) x) ∧
      ∀ x, HasFDerivAt (J.1.2 : E → E →L[Real] F) (J.2 x) x} := by
  let firstJet : C2HolderJet α E F →
      (E →ᵇ F) × HolderSpace α E (E →L[Real] F) := fun J ↦ J.1
  let secondJet : C2HolderJet α E F →
      (E →ᵇ (E →L[Real] F)) × HolderSpace α E (E →L[Real] E →L[Real] F) :=
    fun J ↦ (HolderSpace.toBoundedContinuousFunctionCLM J.1.2, J.2)
  have hfirst : Continuous firstJet := continuous_fst
  have hsecond : Continuous secondJet :=
    ((HolderSpace.toBoundedContinuousFunctionCLM.continuous.comp
      (continuous_snd.comp continuous_fst)).prodMk continuous_snd)
  have hset : {J : C2HolderJet α E F |
        (∀ x, HasFDerivAt (J.1.1 : E → F) (J.1.2 x) x) ∧
        ∀ x, HasFDerivAt (J.1.2 : E → E →L[Real] F) (J.2 x) x} =
      firstJet ⁻¹' {J | ∀ x, HasFDerivAt (J.1 : E → F) (J.2 x) x} ∩
      secondJet ⁻¹' {J | ∀ x, HasFDerivAt (J.1 : E → E →L[Real] F) (J.2 x) x} := by
    ext J
    dsimp only [firstJet, secondJet, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_ofPred_eq]
    have heq : (J.1.2.toBoundedContinuousFunction : E → E →L[Real] F) =
        (J.1.2 : E → E →L[Real] F) := by
      funext x
      exact HolderSpace.toBoundedContinuousFunction_apply J.1.2 x
    constructor
    · intro h
      refine ⟨h.1, ?_⟩
      intro x
      change HasFDerivAt
        ((HolderSpace.toBoundedContinuousFunctionCLM J.1.2 :
          E →ᵇ (E →L[Real] F)) : E → E →L[Real] F) (J.2 x) x
      rw [HolderSpace.toBoundedContinuousFunctionCLM_apply, heq]
      exact h.2 x
    · intro h
      rcases h with ⟨hfirstJ, hsecondJ⟩
      refine ⟨hfirstJ, ?_⟩
      intro x
      have hx := hsecondJ x
      change HasFDerivAt
        ((HolderSpace.toBoundedContinuousFunctionCLM J.1.2 :
          E →ᵇ (E →L[Real] F)) : E → E →L[Real] F) (J.2 x) x at hx
      rw [HolderSpace.toBoundedContinuousFunctionCLM_apply, heq] at hx
      exact hx
  rw [hset]
  exact ((isClosed_derivativeGraph (α := α) (E := E) (Y := F)).preimage hfirst).inter
    ((isClosed_derivativeGraph (α := α) (E := E) (Y := E →L[Real] F)).preimage hsecond)

/-- Bounded `C^{2,α}` maps into a Banach space form a Banach space. -/
noncomputable instance instCompleteSpace [CompleteSpace F] :
    CompleteSpace (C2HolderSpace α E F) := by
  unfold C2HolderSpace
  exact (isClosed_c2HolderSpace (α := α) (E := E) (F := F)).completeSpace_coe

attribute [irreducible] _root_.TauCeti.C2HolderSpace

end C2HolderSpace

end TauCeti
