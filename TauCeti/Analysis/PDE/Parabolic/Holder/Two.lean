/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.SpaceTime.Holder
public import TauCeti.Analysis.Holder.Normed
public import TauCeti.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-!
# Bounded order-two parabolic Hölder maps

`ParabolicC2HolderSpace α E F hab` consists of bounded maps on the closed slab
`E × [a,b]` with bounded continuous spatial gradient, parabolically Hölder spatial Hessian
and time derivative. The time derivative is the native derivative within `[a,b]`, so its
endpoint values are the continuous one-sided derivatives. All derivative fields are uniquely
determined by the underlying map.

The norm sums the four supremum norms and the parabolic Hölder seminorms of the two top-order
fields. It is equivalent to the full parabolic norm, which additionally includes the temporal
`(1+α)/2` seminorm of the gradient. Completeness follows from closedness of the spatial and
time derivative identities under uniform convergence.

The construction follows the closed derivative graph used in `TauCeti.Analysis.Holder.Two`.
For the parabolic norm convention, see A. Lunardi, *Linear and nonlinear diffusion problems*,
Cortona lecture notes, 2004, Chapter 3.
-/

public section
noncomputable section

namespace TauCeti

open Set Filter Topology ParabolicSpaceTime
open scoped NNReal ENNReal BoundedContinuousFunction

variable (α : ℝ≥0) {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ}

namespace ParabolicC2HolderSpace

variable (E F) (a b : ℝ)

/-- A local shortcut for bounded value fields, keeping nested sum instance search shallow. -/
local instance : NormedAddCommGroup (slab (E := E) a b →ᵇ F) := inferInstance
/-- A local shortcut for bounded gradient fields in the nested sum norm. -/
local instance : NormedAddCommGroup (slab (E := E) a b →ᵇ (E →L[ℝ] F)) := inferInstance
/-- A local shortcut for scalar operations on bounded value fields. -/
local instance : NormedSpace ℝ (slab (E := E) a b →ᵇ F) := inferInstance
/-- A local shortcut for scalar operations on bounded gradient fields. -/
local instance : NormedSpace ℝ (slab (E := E) a b →ᵇ (E →L[ℝ] F)) := inferInstance
/-- A local shortcut for Hölder Hessian fields in the nested sum norm. -/
local instance : NormedSpace ℝ
    (HolderSpace α (slab (E := E) a b) (E →L[ℝ] E →L[ℝ] F)) := inferInstance
/-- A local shortcut for Hölder time-derivative fields in the nested sum norm. -/
local instance : NormedSpace ℝ (HolderSpace α (slab (E := E) a b) F) := inferInstance

private abbrev Jet := WithLp 1
  (WithLp 1 ((slab (E := E) a b →ᵇ F) × (slab (E := E) a b →ᵇ (E →L[ℝ] F))) ×
    WithLp 1 (HolderSpace α (slab (E := E) a b) (E →L[ℝ] E →L[ℝ] F) ×
      HolderSpace α (slab (E := E) a b) F))

variable {α E F a b}

private def valueJetL : Jet α E F a b →L[ℝ] (slab (E := E) a b →ᵇ F) :=
  (WithLp.fstL 1 ℝ _ _).comp (WithLp.fstL 1 ℝ _ _)

private def spatialJetL : Jet α E F a b →L[ℝ] (slab (E := E) a b →ᵇ (E →L[ℝ] F)) :=
  (WithLp.sndL 1 ℝ _ _).comp (WithLp.fstL 1 ℝ _ _)

private def secondJetL : Jet α E F a b →L[ℝ]
    HolderSpace α (slab (E := E) a b) (E →L[ℝ] E →L[ℝ] F) :=
  (WithLp.fstL 1 ℝ _ _).comp (WithLp.sndL 1 ℝ _ _)

private def timeJetL : Jet α E F a b →L[ℝ] HolderSpace α (slab (E := E) a b) F :=
  (WithLp.sndL 1 ℝ _ _).comp (WithLp.sndL 1 ℝ _ _)

/-- The canonical extension of a slab map to a total time slice, constant outside the interval.
Only its values on `[a,b]` enter derivatives within the slab. -/
def timeExtension (hab : a ≤ b) (f : slab (E := E) a b → F) (x : E) (t : ℝ) : F :=
  f (slabMk x (projIcc a b hab t))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- The total time slice evaluates the slab map at the clamped time. -/
theorem timeExtension_def (hab : a ≤ b) (f : slab (E := E) a b → F) (x : E) :
    timeExtension hab f x = fun t ↦ f (slabMk x (projIcc a b hab t)) := (rfl)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
@[simp]
theorem timeExtension_of_mem (hab : a ≤ b) (f : slab (E := E) a b → F)
    (x : E) (t : Icc a b) : timeExtension hab f x t = f (slabMk x t) := by
  simp [timeExtension, projIcc_of_mem hab t.2]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- A slab map is recovered from its total time slices. -/
theorem timeExtension_space_slabTime (hab : a ≤ b) (f : slab (E := E) a b → F) :
    (fun p : slab (E := E) a b ↦
      timeExtension hab f (p : ParabolicSpaceTime E).space (slabTime p)) = f :=
  funext fun p ↦ by rw [timeExtension_of_mem, slabMk_space_slabTime]

private def IsJetGraph (hab : a < b) (J : Jet α E F a b) : Prop :=
  (∀ (t : Icc a b) (x : E), HasFDerivAt (fun y ↦ valueJetL J (slabMk y t))
    (spatialJetL J (slabMk x t)) x) ∧
  (∀ (t : Icc a b) (x : E), HasFDerivAt (fun y ↦ spatialJetL J (slabMk y t))
    (secondJetL J (slabMk x t)) x) ∧
  ∀ (x : E) (t : Icc a b), HasDerivWithinAt (timeExtension hab.le (valueJetL J) x)
    (timeJetL J (slabMk x t)) (Icc a b) t

variable (α E F) in
/-- Bounded order-two parabolic Hölder maps on a nondegenerate closed time slab.
The norm is the sum of the value and gradient supremum norms and the two top-order
supremum-plus-Hölder norms. -/
-- Exposure is needed for the module compiler to construct instances on this graph alias;
-- the final irreducibility attribute keeps consumers at the characteristic API boundary.
@[expose] def _root_.TauCeti.ParabolicC2HolderSpace (hab : a < b) : Type _ :=
  let Jet := WithLp 1
    (WithLp 1 ((slab (E := E) a b →ᵇ F) × (slab (E := E) a b →ᵇ (E →L[ℝ] F))) ×
      WithLp 1 (HolderSpace α (slab (E := E) a b) (E →L[ℝ] E →L[ℝ] F) ×
        HolderSpace α (slab (E := E) a b) F))
  let valueJetL : Jet →L[ℝ] (slab (E := E) a b →ᵇ F) :=
    (WithLp.fstL 1 ℝ _ _).comp (WithLp.fstL 1 ℝ _ _)
  let spatialJetL : Jet →L[ℝ] (slab (E := E) a b →ᵇ (E →L[ℝ] F)) :=
    (WithLp.sndL 1 ℝ _ _).comp (WithLp.fstL 1 ℝ _ _)
  let secondJetL : Jet →L[ℝ]
      HolderSpace α (slab (E := E) a b) (E →L[ℝ] E →L[ℝ] F) :=
    (WithLp.fstL 1 ℝ _ _).comp (WithLp.sndL 1 ℝ _ _)
  let timeJetL : Jet →L[ℝ] HolderSpace α (slab (E := E) a b) F :=
    (WithLp.sndL 1 ℝ _ _).comp (WithLp.sndL 1 ℝ _ _)
  let IsJetGraph (J : Jet) : Prop :=
    (∀ (t : Icc a b) (x : E), HasFDerivAt (fun y ↦ valueJetL J (slabMk y t))
      (spatialJetL J (slabMk x t)) x) ∧
    (∀ (t : Icc a b) (x : E), HasFDerivAt (fun y ↦ spatialJetL J (slabMk y t))
      (secondJetL J (slabMk x t)) x) ∧
    ∀ (x : E) (t : Icc a b), HasDerivWithinAt (timeExtension hab.le (valueJetL J) x)
      (timeJetL J (slabMk x t)) (Icc a b) t
  let graph : Submodule ℝ Jet :=
    { carrier := {J | IsJetGraph J}
      zero_mem' := by
        constructor
        · intro t x
          simpa [valueJetL, spatialJetL] using hasFDerivAt_const (x := x) (c := (0 : F))
        constructor
        · intro t x
          simpa [spatialJetL, secondJetL] using
            hasFDerivAt_const (x := x) (c := (0 : E →L[ℝ] F))
        · intro x t
          simpa [valueJetL, timeJetL, timeExtension_def] using
            (hasDerivWithinAt_const (x := (t : ℝ)) (s := Icc a b) (c := (0 : F)))
      add_mem' := by
        rintro J K ⟨hJ, hJ', hJt⟩ ⟨hK, hK', hKt⟩
        refine ⟨fun t x ↦ ?_, fun t x ↦ ?_, fun x t ↦ ?_⟩
        · simpa only [map_add, BoundedContinuousFunction.add_apply, Pi.add_def] using
            (hJ t x).add (hK t x)
        · simpa only [map_add, BoundedContinuousFunction.add_apply,
            HolderSpace.add_apply, Pi.add_def] using
            (hJ' t x).add (hK' t x)
        · simpa only [map_add, timeExtension_def, BoundedContinuousFunction.add_apply,
            HolderSpace.add_apply, Pi.add_def] using (hJt x t).add (hKt x t)
      smul_mem' := by
        rintro c J ⟨hJ, hJ', hJt⟩
        refine ⟨fun t x ↦ ?_, fun t x ↦ ?_, fun x t ↦ ?_⟩
        · simpa only [map_smul, BoundedContinuousFunction.smul_apply, Pi.smul_def] using
            (hJ t x).const_smul c
        · simpa only [map_smul, BoundedContinuousFunction.smul_apply,
            HolderSpace.smul_apply, Pi.smul_def] using
            (hJ' t x).const_smul c
        · simpa only [map_smul, timeExtension_def, BoundedContinuousFunction.smul_apply,
            HolderSpace.smul_apply, Pi.smul_def] using (hJt x t).const_smul c }
  graph

variable {hab : a < b}

instance : NormedAddCommGroup (ParabolicC2HolderSpace α E F hab) := by
  unfold ParabolicC2HolderSpace
  infer_instance

instance : NormedSpace ℝ (ParabolicC2HolderSpace α E F hab) := by
  unfold ParabolicC2HolderSpace
  infer_instance

private def toJetL : ParabolicC2HolderSpace α E F hab →L[ℝ] Jet α E F a b :=
  (by unfold ParabolicC2HolderSpace; exact Submodule.subtypeL _)

/-- Forgetting all derivatives is continuous and linear. -/
def valueL : ParabolicC2HolderSpace α E F hab →L[ℝ] (slab (E := E) a b →ᵇ F) :=
  valueJetL.comp toJetL

/-- The bounded continuous spatial gradient, as a continuous linear operator on the space. -/
def spatialFDerivL : ParabolicC2HolderSpace α E F hab →L[ℝ]
    (slab (E := E) a b →ᵇ (E →L[ℝ] F)) := spatialJetL.comp toJetL

/-- The parabolically Hölder spatial Hessian, as a continuous linear operator on the space. -/
def spatialSecondFDerivL : ParabolicC2HolderSpace α E F hab →L[ℝ]
    HolderSpace α (slab (E := E) a b) (E →L[ℝ] E →L[ℝ] F) := secondJetL.comp toJetL

/-- The parabolically Hölder time derivative, as a continuous linear operator on the space. -/
def timeDerivL : ParabolicC2HolderSpace α E F hab →L[ℝ]
    HolderSpace α (slab (E := E) a b) F := timeJetL.comp toJetL

/-- A bounded order-two parabolic map is a function on the closed slab. -/
instance : CoeFun (ParabolicC2HolderSpace α E F hab) fun _ ↦ slab (E := E) a b → F :=
  ⟨fun f ↦ valueL f⟩

@[simp]
theorem valueL_apply (f : ParabolicC2HolderSpace α E F hab) (p : slab (E := E) a b) :
    valueL f p = f p := (rfl)

theorem zero_apply (p : slab (E := E) a b) :
    (0 : ParabolicC2HolderSpace α E F hab) p = 0 := by
  simpa only [valueL_apply, BoundedContinuousFunction.coe_zero, Pi.zero_apply] using
    congrArg (fun g : slab (E := E) a b →ᵇ F ↦ g p)
      (valueL (α := α) (E := E) (F := F) (hab := hab)).map_zero

theorem add_apply (f g : ParabolicC2HolderSpace α E F hab) (p : slab (E := E) a b) :
    (f + g) p = f p + g p := by
  simpa only [valueL_apply, BoundedContinuousFunction.add_apply] using
    congrArg (fun g : slab (E := E) a b →ᵇ F ↦ g p) (valueL.map_add f g)

theorem smul_apply (c : ℝ) (f : ParabolicC2HolderSpace α E F hab) (p : slab (E := E) a b) :
    (c • f) p = c • f p := by
  simpa only [valueL_apply, BoundedContinuousFunction.smul_apply] using
    congrArg (fun g : slab (E := E) a b →ᵇ F ↦ g p) (valueL.map_smul c f)

/-- The spatial gradient is the actual Fréchet derivative of every time slice. -/
theorem hasSpatialFDerivAt (f : ParabolicC2HolderSpace α E F hab) (t : Icc a b) (x : E) :
    HasFDerivAt (fun y ↦ f (slabMk y t)) (spatialFDerivL f (slabMk x t)) x := f.2.1 t x

/-- The Hessian is the actual Fréchet derivative of the gradient. -/
theorem hasSpatialSecondFDerivAt (f : ParabolicC2HolderSpace α E F hab)
    (t : Icc a b) (x : E) : HasFDerivAt (fun y ↦ spatialFDerivL f (slabMk y t))
      (spatialSecondFDerivL f (slabMk x t)) x := f.2.2.1 t x

/-- The recorded time derivative is the derivative within the closed time interval. -/
theorem hasTimeDerivWithinAt (f : ParabolicC2HolderSpace α E F hab) (x : E) (t : Icc a b) :
    HasDerivWithinAt (timeExtension hab.le f x) (timeDerivL f (slabMk x t)) (Icc a b) t :=
  f.2.2.2 x t

@[simp]
theorem fderiv_eq (f : ParabolicC2HolderSpace α E F hab) (t : Icc a b) (x : E) :
    fderiv ℝ (fun y ↦ f (slabMk y t)) x = spatialFDerivL f (slabMk x t) :=
  (f.hasSpatialFDerivAt t x).fderiv

@[simp]
theorem fderiv_spatialFDeriv_eq (f : ParabolicC2HolderSpace α E F hab)
    (t : Icc a b) (x : E) : fderiv ℝ (fun y ↦ spatialFDerivL f (slabMk y t)) x =
      spatialSecondFDerivL f (slabMk x t) := (f.hasSpatialSecondFDerivAt t x).fderiv

@[simp]
theorem derivWithin_eq (f : ParabolicC2HolderSpace α E F hab) (x : E) (t : Icc a b) :
    derivWithin (timeExtension hab.le f x) (Icc a b) t = timeDerivL f (slabMk x t) :=
  (f.hasTimeDerivWithinAt x t).derivWithin (uniqueDiffOn_Icc hab t t.2)

/-- At an interior time, the same field agrees with the ordinary time derivative. -/
theorem deriv_eq (f : ParabolicC2HolderSpace α E F hab) (x : E) (t : Icc a b)
    (ht : (t : ℝ) ∈ Ioo a b) : deriv (timeExtension hab.le f x) t =
      timeDerivL f (slabMk x t) :=
  ((f.hasTimeDerivWithinAt x t).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).deriv

/-- Construct an element from its bounded fields and the three derivative identities. -/
def mk (u : slab (E := E) a b →ᵇ F) (ux : slab (E := E) a b →ᵇ (E →L[ℝ] F))
    (uxx : HolderSpace α (slab (E := E) a b) (E →L[ℝ] E →L[ℝ] F))
    (ut : HolderSpace α (slab (E := E) a b) F)
    (hx : ∀ t x, HasFDerivAt (fun y ↦ u (slabMk y t)) (ux (slabMk x t)) x)
    (hxx : ∀ t x, HasFDerivAt (fun y ↦ ux (slabMk y t)) (uxx (slabMk x t)) x)
    (ht : ∀ x (t : Icc a b), HasDerivWithinAt (timeExtension hab.le u x)
      (ut (slabMk x t)) (Icc a b) t) : ParabolicC2HolderSpace α E F hab :=
  ⟨WithLp.toLp 1 (WithLp.toLp 1 (u, ux), WithLp.toLp 1 (uxx, ut)), hx, hxx, ht⟩

@[simp]
theorem valueL_mk (u ux uxx ut hx hxx ht) :
    valueL (mk (α := α) (E := E) (F := F) (hab := hab) u ux uxx ut hx hxx ht) = u := (rfl)

theorem mk_apply (u ux uxx ut hx hxx ht) (p : slab (E := E) a b) :
    mk (α := α) (E := E) (F := F) (hab := hab) u ux uxx ut hx hxx ht p = u p := by
  rw [← valueL_apply, valueL_mk]

@[simp]
theorem spatialFDerivL_mk (u ux uxx ut hx hxx ht) :
    spatialFDerivL (mk (α := α) (E := E) (F := F) (hab := hab) u ux uxx ut hx hxx ht) = ux :=
  (rfl)

@[simp]
theorem spatialSecondFDerivL_mk (u ux uxx ut hx hxx ht) :
    spatialSecondFDerivL (mk (α := α) (E := E) (F := F) (hab := hab) u ux uxx ut hx hxx ht) =
      uxx := (rfl)

@[simp]
theorem timeDerivL_mk (u ux uxx ut hx hxx ht) :
    timeDerivL (mk (α := α) (E := E) (F := F) (hab := hab) u ux uxx ut hx hxx ht) = ut := (rfl)

/-- Constant functions belong to the bounded parabolic Hölder space. -/
def const (c : F) : ParabolicC2HolderSpace α E F hab :=
  mk (BoundedContinuousFunction.const _ c) 0 0 0
    (fun _ x ↦ by simpa using hasFDerivAt_const (x := x) (c := c))
    (fun _ x ↦ by simpa using hasFDerivAt_const (x := x) (c := (0 : E →L[ℝ] F)))
    (fun _ t ↦ by
      simpa [timeExtension_def] using
        hasDerivWithinAt_const (x := (t : ℝ)) (s := Icc a b) (c := c))

theorem const_apply (c : F) (p : slab (E := E) a b) :
    const (α := α) (hab := hab) c p = c := by
  rw [← valueL_apply, const, valueL_mk, BoundedContinuousFunction.const_apply]

@[simp]
theorem valueL_const (c : F) :
    valueL (const (α := α) (E := E) (hab := hab) c) =
      BoundedContinuousFunction.const _ c := by
  rw [const, valueL_mk]

@[simp]
theorem spatialFDerivL_const (c : F) :
    spatialFDerivL (const (α := α) (E := E) (hab := hab) c) = 0 := by
  rw [const, spatialFDerivL_mk]

@[simp]
theorem spatialSecondFDerivL_const (c : F) :
    spatialSecondFDerivL (const (α := α) (E := E) (hab := hab) c) = 0 := by
  rw [const, spatialSecondFDerivL_mk]

@[simp]
theorem timeDerivL_const (c : F) :
    timeDerivL (const (α := α) (E := E) (hab := hab) c) = 0 := by
  rw [const, timeDerivL_mk]

/-- Equality of the underlying maps determines all derivative fields, including the endpoints. -/
@[ext]
theorem ext {f g : ParabolicC2HolderSpace α E F hab} (h : ∀ p, f p = g p) : f = g := by
  have hv : valueL f = valueL g := DFunLike.ext _ _ h
  have hx : spatialFDerivL f = spatialFDerivL g := by
    apply DFunLike.ext
    intro p
    obtain ⟨x, t, rfl⟩ : ∃ x t, slabMk x t = p := ⟨_, _, slabMk_space_slabTime p⟩
    rw [← f.fderiv_eq, ← g.fderiv_eq]
    exact congrArg (fun q : E → F ↦ fderiv ℝ q x) (funext fun y ↦ h (slabMk y t))
  have hxx : spatialSecondFDerivL f = spatialSecondFDerivL g := by
    apply HolderSpace.ext
    intro p
    obtain ⟨x, t, rfl⟩ : ∃ x t, slabMk x t = p := ⟨_, _, slabMk_space_slabTime p⟩
    rw [← f.fderiv_spatialFDeriv_eq, ← g.fderiv_spatialFDeriv_eq, hx]
  have ht : timeDerivL f = timeDerivL g := by
    apply HolderSpace.ext
    intro p
    obtain ⟨x, t, rfl⟩ : ∃ x t, slabMk x t = p := ⟨_, _, slabMk_space_slabTime p⟩
    rw [← f.derivWithin_eq, ← g.derivWithin_eq]
    congr 1
    exact funext fun s ↦ h _
  apply Subtype.ext
  exact congrArg (WithLp.toLp 1) (Prod.ext
    (congrArg (WithLp.toLp 1) (Prod.ext hv hx))
    (congrArg (WithLp.toLp 1) (Prod.ext hxx ht)))

private theorem norm_toJet (f : ParabolicC2HolderSpace α E F hab) :
    ‖toJetL f‖ = ‖f‖ := Submodule.norm_coe f

/-- The reduced parabolic norm is the sum of the four field norms. -/
theorem norm_eq (f : ParabolicC2HolderSpace α E F hab) :
    ‖f‖ = ‖valueL f‖ + ‖spatialFDerivL f‖ +
      (‖spatialSecondFDerivL f‖ + ‖timeDerivL f‖) := by
  rw [← norm_toJet f]
  simp only [WithLp.prod_norm_eq_add (show (0 : ℝ) < (1 : ℝ≥0∞).toReal by norm_num),
    Real.rpow_one, ENNReal.toReal_one, one_div_one]
  rfl

/-- Written in supremum and Hölder seminorms, the norm has the usual reduced order-two form. -/
theorem norm_def (f : ParabolicC2HolderSpace α E F hab) :
    ‖f‖ = ‖valueL f‖ + ‖spatialFDerivL f‖ +
      (‖(spatialSecondFDerivL f).toBoundedContinuousFunction‖ +
        nnHolderNorm α ((spatialSecondFDerivL f).toBoundedContinuousFunction : _ → _)) +
      (‖(timeDerivL f).toBoundedContinuousFunction‖ +
        nnHolderNorm α ((timeDerivL f).toBoundedContinuousFunction : _ → _)) := by
  rw [norm_eq, HolderSpace.norm_def, HolderSpace.norm_def]
  ring

/-- The supremum norm of the value is bounded by the reduced parabolic norm. -/
theorem norm_valueL_le (f : ParabolicC2HolderSpace α E F hab) : ‖valueL f‖ ≤ ‖f‖ := by
  rw [norm_eq]
  linarith [norm_nonneg (spatialFDerivL f), norm_nonneg (spatialSecondFDerivL f),
    norm_nonneg (timeDerivL f)]

/-- The Hessian field gives the native second iterated Fréchet derivative of each slice. -/
theorem iteratedFDeriv_two_apply (f : ParabolicC2HolderSpace α E F hab)
    (t : Icc a b) (x : E) (v : Fin 2 → E) :
    iteratedFDeriv ℝ 2 (fun y ↦ f (slabMk y t)) x v =
      spatialSecondFDerivL f (slabMk x t) (v 0) (v 1) := by
  rw [_root_.iteratedFDeriv_two_apply]
  have hx : fderiv ℝ (fun y ↦ f (slabMk y t)) =
      fun y ↦ spatialFDerivL f (slabMk y t) := funext (f.fderiv_eq t)
  rw [hx, f.fderiv_spatialFDeriv_eq]

/-- The iterated derivative uses its continuous multilinear operator norm. -/
theorem norm_iteratedFDeriv_two (f : ParabolicC2HolderSpace α E F hab)
    (t : Icc a b) (x : E) :
    ‖iteratedFDeriv ℝ 2 (fun y ↦ f (slabMk y t)) x‖ =
      ‖spatialSecondFDerivL f (slabMk x t)‖ := by
  rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
  have hx : fderiv ℝ (fun y ↦ f (slabMk y t)) =
      fun y ↦ spatialFDerivL f (slabMk y t) := funext (f.fderiv_eq t)
  rw [hx, f.fderiv_spatialFDeriv_eq]

/-- The temporal gradient seminorm is controlled by the top-order parabolic seminorms. -/
theorem timeEHolderNorm_spatialFDeriv_le (f : ParabolicC2HolderSpace α E F hab) :
    timeEHolderNorm ((1 + α) / 2) (spatialFDerivL f : _ → _) ≤
      eHolderNorm α ((spatialSecondFDerivL f).toBoundedContinuousFunction : _ → _) +
        eHolderNorm α ((timeDerivL f).toBoundedContinuousFunction : _ → _) := by
  have hx : ∀ t ∈ Icc a b, ∀ x,
      HasFDerivAt (fun y ↦ timeExtension hab.le f y t)
        (timeExtension hab.le (spatialFDerivL f) x t) x := by
    intro t ht x
    simpa [timeExtension, projIcc_of_mem hab.le ht] using f.hasSpatialFDerivAt ⟨t, ht⟩ x
  have hxx : ∀ t ∈ Icc a b, ∀ x,
      HasFDerivAt (fun y ↦ timeExtension hab.le (spatialFDerivL f) y t)
        (timeExtension hab.le (spatialSecondFDerivL f) x t) x := by
    intro t ht x
    simpa [timeExtension, projIcc_of_mem hab.le ht] using
      f.hasSpatialSecondFDerivAt ⟨t, ht⟩ x
  have ht : ∀ x, ∀ t ∈ Icc a b,
      HasDerivWithinAt (timeExtension hab.le f x)
        (timeExtension hab.le (timeDerivL f) x t) (Icc a b) t := by
    intro x t ht
    simpa [timeExtension, projIcc_of_mem hab.le ht] using f.hasTimeDerivWithinAt x ⟨t, ht⟩
  have h := timeEHolderNorm_le_eHolderNorm_add_eHolderNorm
    (E := E) (F := F) (a := a) (b := b)
    (u := timeExtension hab.le f) (u' := timeExtension hab.le (spatialFDerivL f))
    (u'' := timeExtension hab.le (spatialSecondFDerivL f))
    (uₜ := timeExtension hab.le (timeDerivL f)) α hx hxx ht
  simpa only [timeExtension_of_mem, slabMk_space_slabTime,
    HolderSpace.coe_toBoundedContinuousFunction] using h

/-- In particular the separate temporal gradient seminorm is finite. -/
theorem timeEHolderNorm_spatialFDeriv_lt_top (f : ParabolicC2HolderSpace α E F hab) :
    timeEHolderNorm ((1 + α) / 2) (spatialFDerivL f : _ → _) < ∞ :=
  f.timeEHolderNorm_spatialFDeriv_le.trans_lt (ENNReal.add_lt_top.2
    ⟨(spatialSecondFDerivL f).memHolder.eHolderNorm_lt_top,
      (timeDerivL f).memHolder.eHolderNorm_lt_top⟩)

/-- The full order-two norm, including the separate temporal gradient seminorm. -/
def fullNorm (f : ParabolicC2HolderSpace α E F hab) : ℝ :=
  ‖f‖ + (timeEHolderNorm ((1 + α) / 2) (spatialFDerivL f : _ → _)).toReal

/-- The full norm adds the finite temporal gradient seminorm to the reduced norm. -/
theorem fullNorm_def (f : ParabolicC2HolderSpace α E F hab) :
    f.fullNorm = ‖f‖ +
      (timeEHolderNorm ((1 + α) / 2) (spatialFDerivL f : _ → _)).toReal := (rfl)

/-- The inherited Banach norm and the full parabolic norm are equivalent with constants 1 and 2. -/
theorem norm_le_fullNorm_le (f : ParabolicC2HolderSpace α E F hab) :
    ‖f‖ ≤ f.fullNorm ∧ f.fullNorm ≤ 2 * ‖f‖ := by
  refine ⟨le_add_of_nonneg_right ENNReal.toReal_nonneg, ?_⟩
  have h := f.timeEHolderNorm_spatialFDeriv_le
  rw [← (spatialSecondFDerivL f).memHolder.coe_nnHolderNorm_eq_eHolderNorm,
    ← (timeDerivL f).memHolder.coe_nnHolderNorm_eq_eHolderNorm] at h
  have hr := ENNReal.toReal_mono (by finiteness) h
  simp only [← ENNReal.coe_add, ENNReal.coe_toReal, NNReal.coe_add] at hr
  have hs := (spatialSecondFDerivL f).nnHolderNorm_le
  have ht := (timeDerivL f).nnHolderNorm_le
  rw [fullNorm, norm_eq]
  nlinarith [norm_nonneg (valueL f), norm_nonneg (spatialFDerivL f)]

private def spatialSlice (t : Icc a b) : C(E, slab (E := E) a b) :=
  ⟨fun x ↦ slabMk x t, continuous_slabMk.comp (continuous_id.prodMk continuous_const)⟩

private def timeSlice (x : E) : C(Icc a b, slab (E := E) a b) :=
  ⟨slabMk x, continuous_slabMk.comp (continuous_const.prodMk continuous_id)⟩

private theorem isClosed_spatialGraph (t : Icc a b) : IsClosed {J : Jet α E F a b |
      ∀ x, HasFDerivAt (fun y ↦ valueJetL J (slabMk y t))
        (spatialJetL J (slabMk x t)) x} := by
    simpa only [preimage_ofPred_eq, Function.comp_def,
      BoundedContinuousFunction.coe_compContinuous, BoundedContinuousFunction.compContinuous_apply,
      HolderSpace.toBoundedContinuousFunctionCLM_apply,
      HolderSpace.toBoundedContinuousFunction_apply, spatialSlice, ContinuousMap.coe_mk] using
      (isClosed_setOf_hasFDerivAt (𝕜 := ℝ) (E := E) (Y := F)).preimage
      (((BoundedContinuousFunction.continuous_compContinuous (spatialSlice t)).comp
        valueJetL.continuous).prodMk
          ((BoundedContinuousFunction.continuous_compContinuous (spatialSlice t)).comp
            spatialJetL.continuous))

private theorem isClosed_secondGraph (t : Icc a b) : IsClosed {J : Jet α E F a b |
      ∀ x, HasFDerivAt (fun y ↦ spatialJetL J (slabMk y t))
        (secondJetL J (slabMk x t)) x} := by
    simpa only [preimage_ofPred_eq, Function.comp_def,
      BoundedContinuousFunction.coe_compContinuous, BoundedContinuousFunction.compContinuous_apply,
      HolderSpace.toBoundedContinuousFunctionCLM_apply,
      HolderSpace.toBoundedContinuousFunction_apply, spatialSlice, ContinuousMap.coe_mk] using
      (isClosed_setOf_hasFDerivAt (𝕜 := ℝ) (E := E) (Y := E →L[ℝ] F)).preimage
      (((BoundedContinuousFunction.continuous_compContinuous (spatialSlice t)).comp
        spatialJetL.continuous).prodMk
          ((BoundedContinuousFunction.continuous_compContinuous (spatialSlice t)).comp
            (HolderSpace.toBoundedContinuousFunctionCLM.continuous.comp secondJetL.continuous)))

private theorem isClosed_timeGraph (x : E) : IsClosed {J : Jet α E F a b |
      ∀ t : Icc a b, HasDerivWithinAt (timeExtension hab.le (valueJetL J) x)
        (timeJetL J (slabMk x t)) (Icc a b) t} := by
    simpa only [preimage_ofPred_eq, Function.comp_def,
      BoundedContinuousFunction.coe_compContinuous, BoundedContinuousFunction.compContinuous_apply,
      HolderSpace.toBoundedContinuousFunctionCLM_apply,
      HolderSpace.toBoundedContinuousFunction_apply, timeSlice, ContinuousMap.coe_mk,
      timeExtension_def] using
      (isClosed_setOf_hasDerivWithinAt_Icc (F := F) hab).preimage
      (((BoundedContinuousFunction.continuous_compContinuous (timeSlice x)).comp
        valueJetL.continuous).prodMk
          ((BoundedContinuousFunction.continuous_compContinuous (timeSlice x)).comp
            (HolderSpace.toBoundedContinuousFunctionCLM.continuous.comp timeJetL.continuous)))

private theorem isClosed_isJetGraph : IsClosed {J : Jet α E F a b | IsJetGraph hab J} := by
  simpa only [IsJetGraph, ofPred_and, ofPred_forall] using
    (isClosed_iInter (isClosed_spatialGraph (α := α) (E := E) (F := F))).inter
      ((isClosed_iInter (isClosed_secondGraph (α := α) (E := E) (F := F))).inter
        (isClosed_iInter (isClosed_timeGraph (α := α) (E := E) (F := F) (hab := hab))))

/-- Bounded order-two parabolic Hölder maps with Banach values form a Banach space. -/
instance [CompleteSpace F] : CompleteSpace (ParabolicC2HolderSpace α E F hab) := by
  unfold ParabolicC2HolderSpace
  exact (isClosed_isJetGraph (α := α) (E := E) (F := F) (hab := hab)).completeSpace_coe

attribute [irreducible] _root_.TauCeti.ParabolicC2HolderSpace

end ParabolicC2HolderSpace
end TauCeti
