/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Interpolation
public import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# Bounded order-one parabolic Hölder maps

`ParabolicC1HolderSpace α E F a b` is the space `C_{par,b}^{1+α}` on the closed slab
`E × [a, b]`: bounded continuous maps `u` with a bounded spatial gradient `D_x u` that is
parabolically `α`-Hölder, and whose time slices `t ↦ u (x, t)` are `(1 + α) / 2`-Hölder,
uniformly in `x`. In the parabolic scaling one time derivative counts as two spatial ones, so the
time regularity of an order-one map is the fractional exponent `(1 + α) / 2`; it is not
controlled by the other terms, and the temporal seminorm is part of the norm.

An element is represented by its value, its gradient in `HolderSpace α`, and the family of its
time slices in `HolderSpace ((1 + α) / 2)`, bounded uniformly in `x` (an `ℓ^∞` family), subject
to the conditions that the gradient is the spatial Fréchet derivative of the value and the slices
are the time slices of the value. These conditions are closed, which gives completeness. The norm
is the sum of the three field norms; it is equivalent, with constants `1` and `2`, to the norm

`‖u‖_∞ + ‖D_x u‖_∞ + [D_x u]_{α,par} + [u]_{t,(1+α)/2}`

(`ParabolicC1HolderSpace.fullNorm_le_norm_le`).

The order-one space sits between `C_b^{α,α/2}`, the parabolic `HolderSpace α`, and the order-two
space `ParabolicC2HolderSpace`. This file proves the continuous inclusions between these
consecutive orders, and that the spatial gradient lowers the order by one: it maps
`C_b^{2+α,1+α/2}` boundedly into the order-one space of gradient-valued maps. The inclusions need
`α ≤ 1`; the gradient map holds for every `α`.

## Main declarations

* `TauCeti.ParabolicC1HolderSpace`: bounded order-one parabolic Hölder maps, a Banach space when
  the codomain is complete.
* `TauCeti.ParabolicC1HolderSpace.valueL`, `TauCeti.ParabolicC1HolderSpace.spatialFDerivL`: the
  value and the Hölder gradient, as continuous linear maps.
* `TauCeti.ParabolicC1HolderSpace.mk`: the constructor from a value, a Hölder gradient and a
  finite temporal seminorm.
* `TauCeti.ParabolicC1HolderSpace.timeSliceL` and `TauCeti.ParabolicC1HolderSpace.norm_eq`: the
  `ℓ^∞` family of Hölder time slices, and the norm as the sum of the three field norms.
* `TauCeti.ParabolicC1HolderSpace.timeEHolderNorm_le_nnnorm` and
  `TauCeti.ParabolicC1HolderSpace.fullNorm_le_norm_le`: the temporal seminorm and the comparison
  with the full parabolic norm.
* `TauCeti.ParabolicC1HolderSpace.valueHolderL`: the inclusion into `C_b^{α,α/2}`.
* `TauCeti.ParabolicC2HolderSpace.toC1L`: the inclusion of `C_b^{2+α,1+α/2}`.
* `TauCeti.ParabolicC2HolderSpace.spatialFDerivC1L`: the spatial gradient as a map from
  `C_b^{2+α,1+α/2}` to the order-one space.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, lecture notes, Cortona, 2004, Chapter 3.
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996,
  Chapter 8.
-/

public section
noncomputable section

namespace TauCeti

open Set Filter Topology ParabolicSpaceTime
open scoped NNReal ENNReal BoundedContinuousFunction

variable {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ}

namespace ParabolicC1HolderSpace

variable (α E F a b) in
/-- The ambient jet space: the value, the Hölder gradient and the `ℓ^∞` family of Hölder time
slices, with the `ℓ¹` norm. -/
private abbrev Jet := WithLp 1 ((slab (E := E) a b →ᵇ F) ×
  WithLp 1 (HolderSpace α (slab (E := E) a b) (E →L[ℝ] F) ×
    lp (fun _ : E ↦ HolderSpace ((1 + α) / 2) (Icc a b) F) ∞))

private def valueJetL : Jet α E F a b →L[ℝ] (slab (E := E) a b →ᵇ F) :=
  WithLp.fstL 1 ℝ _ _

private def gradJetL : Jet α E F a b →L[ℝ] HolderSpace α (slab (E := E) a b) (E →L[ℝ] F) :=
  (WithLp.fstL 1 ℝ _ _).comp (WithLp.sndL 1 ℝ _ _)

private def sliceJetL :
    Jet α E F a b →L[ℝ] lp (fun _ : E ↦ HolderSpace ((1 + α) / 2) (Icc a b) F) ∞ :=
  (WithLp.sndL 1 ℝ _ _).comp (WithLp.sndL 1 ℝ _ _)

private def IsJetGraph (J : Jet α E F a b) : Prop :=
  (∀ (t : Icc a b) (x : E), HasFDerivAt (fun y ↦ valueJetL J (slabMk y t))
    (gradJetL J (slabMk x t)) x) ∧
  ∀ (x : E) (t : Icc a b), sliceJetL J x t = valueJetL J (slabMk x t)

end ParabolicC1HolderSpace

variable (α E F a b) in
/-- Bounded order-one parabolic Hölder maps on the closed slab `E × [a, b]`: bounded continuous
maps with a parabolically `α`-Hölder spatial gradient and `(1 + α) / 2`-Hölder time slices,
uniformly in space. The norm is the sum of the supremum norm, the Hölder norm of the gradient,
and the supremum over `x` of the Hölder norms of the time slices. -/
-- Exposure is needed for the module compiler to construct instances on this graph alias;
-- the final irreducibility attribute keeps consumers at the characteristic API boundary.
@[expose] def ParabolicC1HolderSpace : Type _ :=
  let Jet := WithLp 1 ((slab (E := E) a b →ᵇ F) ×
    WithLp 1 (HolderSpace α (slab (E := E) a b) (E →L[ℝ] F) ×
      lp (fun _ : E ↦ HolderSpace ((1 + α) / 2) (Icc a b) F) ∞))
  let valueJetL : Jet →L[ℝ] (slab (E := E) a b →ᵇ F) := WithLp.fstL 1 ℝ _ _
  let gradJetL : Jet →L[ℝ] HolderSpace α (slab (E := E) a b) (E →L[ℝ] F) :=
    (WithLp.fstL 1 ℝ _ _).comp (WithLp.sndL 1 ℝ _ _)
  let sliceJetL : Jet →L[ℝ] lp (fun _ : E ↦ HolderSpace ((1 + α) / 2) (Icc a b) F) ∞ :=
    (WithLp.sndL 1 ℝ _ _).comp (WithLp.sndL 1 ℝ _ _)
  let graph : Submodule ℝ Jet :=
    { carrier := {J | (∀ (t : Icc a b) (x : E), HasFDerivAt (fun y ↦ valueJetL J (slabMk y t))
          (gradJetL J (slabMk x t)) x) ∧
        ∀ (x : E) (t : Icc a b), sliceJetL J x t = valueJetL J (slabMk x t)}
      zero_mem' := by
        refine ⟨fun t x ↦ ?_, fun x t ↦ ?_⟩
        · simpa using hasFDerivAt_const (x := x) (c := (0 : F))
        · simp [HolderSpace.zero_apply]
      add_mem' := by
        rintro J K ⟨hJ, hJs⟩ ⟨hK, hKs⟩
        refine ⟨fun t x ↦ ?_, fun x t ↦ ?_⟩
        · simpa only [map_add, _root_.add_apply,
            HolderSpace.add_apply, Pi.add_def] using (hJ t x).add (hK t x)
        · simp only [map_add, lp.coeFn_add, Pi.add_apply, HolderSpace.add_apply,
            _root_.add_apply, hJs x t, hKs x t]
      smul_mem' := by
        rintro c J ⟨hJ, hJs⟩
        refine ⟨fun t x ↦ ?_, fun x t ↦ ?_⟩
        · simpa only [map_smul, _root_.smul_apply,
            HolderSpace.smul_apply, Pi.smul_def] using (hJ t x).const_smul c
        · simp only [map_smul, lp.coeFn_smul, Pi.smul_apply, HolderSpace.smul_apply,
            _root_.smul_apply, hJs x t] }
  graph

namespace ParabolicC1HolderSpace

instance : NormedAddCommGroup (ParabolicC1HolderSpace α E F a b) := by
  unfold ParabolicC1HolderSpace
  infer_instance

instance : NormedSpace ℝ (ParabolicC1HolderSpace α E F a b) := by
  unfold ParabolicC1HolderSpace
  infer_instance

private def toJetL : ParabolicC1HolderSpace α E F a b →L[ℝ] Jet α E F a b :=
  (by unfold ParabolicC1HolderSpace; exact Submodule.subtypeL _)

private theorem isJetGraph_toJetL (f : ParabolicC1HolderSpace α E F a b) :
    IsJetGraph (toJetL f) :=
  -- `toJetL` is the submodule inclusion, so its value is the underlying jet of `f`.
  f.2

private theorem norm_toJetL (f : ParabolicC1HolderSpace α E F a b) : ‖toJetL f‖ = ‖f‖ :=
  Submodule.norm_coe f

/-- Forgetting the gradient and the time slices is continuous and linear. -/
def valueL : ParabolicC1HolderSpace α E F a b →L[ℝ] (slab (E := E) a b →ᵇ F) :=
  valueJetL.comp toJetL

/-- The parabolically Hölder spatial gradient, as a continuous linear operator on the space. -/
def spatialFDerivL :
    ParabolicC1HolderSpace α E F a b →L[ℝ] HolderSpace α (slab (E := E) a b) (E →L[ℝ] F) :=
  gradJetL.comp toJetL

/-- The family of Hölder time slices `x ↦ (t ↦ u (x, t))`. -/
def timeSliceL : ParabolicC1HolderSpace α E F a b →L[ℝ]
    lp (fun _ : E ↦ HolderSpace ((1 + α) / 2) (Icc a b) F) ∞ :=
  sliceJetL.comp toJetL

/-- A bounded order-one parabolic map is a function on the closed slab. -/
instance : CoeFun (ParabolicC1HolderSpace α E F a b) fun _ ↦ slab (E := E) a b → F :=
  ⟨fun f ↦ valueL f⟩

@[simp]
theorem valueL_apply (f : ParabolicC1HolderSpace α E F a b) (p : slab (E := E) a b) :
    valueL f p = f p := (rfl)

theorem zero_apply (p : slab (E := E) a b) : (0 : ParabolicC1HolderSpace α E F a b) p = 0 := by
  rw [← valueL_apply, map_zero, FunLike.coe_zero, Pi.zero_apply]

theorem add_apply (f g : ParabolicC1HolderSpace α E F a b) (p : slab (E := E) a b) :
    (f + g) p = f p + g p := by
  rw [← valueL_apply, map_add, _root_.add_apply, valueL_apply, valueL_apply]

theorem neg_apply (f : ParabolicC1HolderSpace α E F a b) (p : slab (E := E) a b) :
    (-f) p = -f p := by
  rw [← valueL_apply, map_neg, _root_.neg_apply, valueL_apply]

theorem sub_apply (f g : ParabolicC1HolderSpace α E F a b) (p : slab (E := E) a b) :
    (f - g) p = f p - g p := by
  rw [← valueL_apply, map_sub, _root_.sub_apply, valueL_apply, valueL_apply]

theorem smul_apply (c : ℝ) (f : ParabolicC1HolderSpace α E F a b) (p : slab (E := E) a b) :
    (c • f) p = c • f p := by
  rw [← valueL_apply, map_smul, _root_.smul_apply, valueL_apply]

/-- The gradient field is the actual Fréchet derivative of every time slice. -/
theorem hasSpatialFDerivAt (f : ParabolicC1HolderSpace α E F a b) (t : Icc a b) (x : E) :
    HasFDerivAt (fun y ↦ f (slabMk y t)) (spatialFDerivL f (slabMk x t)) x :=
  (isJetGraph_toJetL f).1 t x

@[simp]
theorem fderiv_eq (f : ParabolicC1HolderSpace α E F a b) (t : Icc a b) (x : E) :
    fderiv ℝ (fun y ↦ f (slabMk y t)) x = spatialFDerivL f (slabMk x t) :=
  (f.hasSpatialFDerivAt t x).fderiv

/-- The time slice at `x` is the map `t ↦ u (x, t)`. -/
theorem timeSliceL_apply (f : ParabolicC1HolderSpace α E F a b) (x : E) (t : Icc a b) :
    timeSliceL f x t = f (slabMk x t) :=
  (isJetGraph_toJetL f).2 x t

/-- The family of time slices is determined by the map. -/
private theorem coe_timeSliceL (f : ParabolicC1HolderSpace α E F a b) (x : E) :
    ((timeSliceL f x : HolderSpace ((1 + α) / 2) (Icc a b) F) : Icc a b → F) =
      fun t ↦ f (slabMk x t) :=
  funext (f.timeSliceL_apply x)

/-- The norm is the sum of the supremum norm, the Hölder norm of the gradient, and the norm of
the family of Hölder time slices. -/
theorem norm_eq (f : ParabolicC1HolderSpace α E F a b) :
    ‖f‖ = ‖valueL f‖ + (‖spatialFDerivL f‖ + ‖timeSliceL f‖) := by
  rw [← norm_toJetL f]
  simp only [WithLp.prod_norm_eq_add (show (0 : ℝ) < (1 : ℝ≥0∞).toReal by norm_num),
    Real.rpow_one, ENNReal.toReal_one, one_div_one]
  -- The three field maps are the `WithLp` projections composed with `toJetL`.
  rfl

/-- Each time slice is `(1 + α) / 2`-Hölder, with the Hölder seminorm bounded by the norm of
the family of slices. -/
private theorem eHolderNorm_timeSlice_le (f : ParabolicC1HolderSpace α E F a b) (x : E) :
    eHolderNorm ((1 + α) / 2) (fun t : Icc a b ↦ f (slabMk x t)) ≤ ‖timeSliceL f‖₊ := by
  have hm := (timeSliceL f x).memHolder
  rw [HolderSpace.coe_toBoundedContinuousFunction, coe_timeSliceL] at hm
  rw [← hm.coe_nnHolderNorm_eq_eHolderNorm, ENNReal.coe_le_coe, ← NNReal.coe_le_coe,
    coe_nnnorm]
  have h := (timeSliceL f x).nnHolderNorm_le
  rw [HolderSpace.coe_toBoundedContinuousFunction, coe_timeSliceL] at h
  exact h.trans (lp.norm_apply_le_norm ENNReal.top_ne_zero _ x)

/-- The temporal seminorm is at most the norm of the family of time slices. -/
private theorem timeEHolderNorm_le_nnnorm_timeSliceL (f : ParabolicC1HolderSpace α E F a b) :
    timeEHolderNorm ((1 + α) / 2) (f : slab (E := E) a b → F) ≤ ‖timeSliceL f‖₊ :=
  timeEHolderNorm_le_iff.2 fun x ↦ eHolderNorm_le_iff.1 (f.eHolderNorm_timeSlice_le x)

/-- **The temporal seminorm is controlled by the norm.** The temporal `(1 + α) / 2`-seminorm
`[u]_{t,(1+α)/2}`, the supremum over `x` of the Hölder seminorms of the time slices, is at most
the norm. -/
theorem timeEHolderNorm_le_nnnorm (f : ParabolicC1HolderSpace α E F a b) :
    timeEHolderNorm ((1 + α) / 2) (f : slab (E := E) a b → F) ≤ ‖f‖₊ := by
  refine f.timeEHolderNorm_le_nnnorm_timeSliceL.trans ?_
  rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm, norm_eq]
  linarith [norm_nonneg (valueL f), norm_nonneg (spatialFDerivL f)]

/-- In particular the temporal seminorm is finite. -/
theorem timeEHolderNorm_lt_top (f : ParabolicC1HolderSpace α E F a b) :
    timeEHolderNorm ((1 + α) / 2) (f : slab (E := E) a b → F) < ∞ :=
  f.timeEHolderNorm_le_nnnorm.trans_lt ENNReal.coe_lt_top

/-- Each time slice `t ↦ u (x, t)` is `(1 + α) / 2`-Hölder. -/
theorem memHolder_timeSlice (f : ParabolicC1HolderSpace α E F a b) (x : E) :
    MemHolder ((1 + α) / 2) fun t : Icc a b ↦ f (slabMk x t) := by
  have hm := (timeSliceL f x).memHolder
  rwa [HolderSpace.coe_toBoundedContinuousFunction, coe_timeSliceL] at hm

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Composing with the time slice at `x` gives the time slice `t ↦ u (x, t)`. -/
private theorem coe_compContinuous_timeSlice (u : slab (E := E) a b →ᵇ F) (x : E) :
    (u.compContinuous (timeSlice x) : Icc a b → F) = fun t ↦ u (slabMk x t) :=
  funext fun t ↦ by rw [BoundedContinuousFunction.compContinuous_apply, timeSlice_apply]

omit [NormedSpace ℝ E] in
/-- The norm of the Hölder time slice of `u` at `x` is at most `‖u‖_∞ + [u]_{t,(1+α)/2}`. -/
private theorem norm_sliceHolder_le (u : slab (E := E) a b →ᵇ F)
    (ht : timeEHolderNorm ((1 + α) / 2) (u : slab (E := E) a b → F) < ∞) (x : E)
    (hx : MemHolder ((1 + α) / 2) (u.compContinuous (timeSlice x) : Icc a b → F)) :
    ‖HolderSpace.ofBoundedContinuousFunction (u.compContinuous (timeSlice x)) hx‖ ≤
      ‖u‖ + (timeEHolderNorm ((1 + α) / 2) (u : slab (E := E) a b → F)).toReal := by
  rw [HolderSpace.norm_def, HolderSpace.toBoundedContinuousFunction_ofBoundedContinuousFunction]
  gcongr
  · exact (BoundedContinuousFunction.norm_le (norm_nonneg u)).2 fun t ↦ u.norm_coe_le_norm _
  · rw [← ENNReal.coe_toReal (r := nnHolderNorm _ _), hx.coe_nnHolderNorm_eq_eHolderNorm,
      coe_compContinuous_timeSlice]
    exact ENNReal.toReal_mono ht.ne (eHolderNorm_le_timeEHolderNorm _ _ x)

/-- The `ℓ^∞` family of Hölder time slices of a bounded continuous map with finite temporal
seminorm. -/
private def sliceFamily (u : slab (E := E) a b →ᵇ F)
    (ht : timeEHolderNorm ((1 + α) / 2) (u : slab (E := E) a b → F) < ∞) :
    lp (fun _ : E ↦ HolderSpace ((1 + α) / 2) (Icc a b) F) ∞ :=
  ⟨fun x ↦ HolderSpace.ofBoundedContinuousFunction (u.compContinuous (timeSlice x))
      (coe_compContinuous_timeSlice u x ▸ memHolder_timeSlice_of_timeEHolderNorm_lt_top ht x),
    memℓp_infty_iff.2 ⟨_, by
      rintro _ ⟨x, rfl⟩
      exact norm_sliceHolder_le u ht x _⟩⟩

omit [NormedSpace ℝ E] in
private theorem sliceFamily_apply (u : slab (E := E) a b →ᵇ F)
    (ht : timeEHolderNorm ((1 + α) / 2) (u : slab (E := E) a b → F) < ∞) (x : E) (t : Icc a b) :
    sliceFamily u ht x t = u (slabMk x t) :=
  (HolderSpace.ofBoundedContinuousFunction_apply _ _ t).trans
    (congrFun (coe_compContinuous_timeSlice u x) t)

omit [NormedSpace ℝ E] in
private theorem norm_sliceFamily_le (u : slab (E := E) a b →ᵇ F)
    (ht : timeEHolderNorm ((1 + α) / 2) (u : slab (E := E) a b → F) < ∞) :
    ‖sliceFamily u ht‖ ≤
      ‖u‖ + (timeEHolderNorm ((1 + α) / 2) (u : slab (E := E) a b → F)).toReal :=
  lp.norm_le_of_forall_le (by positivity) fun x ↦ norm_sliceHolder_le u ht x _

/-- Construct an element from its value, its Hölder gradient, the derivative identity and the
finiteness of the temporal `(1 + α) / 2`-seminorm. -/
def mk (u : slab (E := E) a b →ᵇ F) (ux : HolderSpace α (slab (E := E) a b) (E →L[ℝ] F))
    (hx : ∀ t x, HasFDerivAt (fun y ↦ u (slabMk y t)) (ux (slabMk x t)) x)
    (ht : timeEHolderNorm ((1 + α) / 2) (u : slab (E := E) a b → F) < ∞) :
    ParabolicC1HolderSpace α E F a b :=
  ⟨WithLp.toLp 1 (u, WithLp.toLp 1 (ux, sliceFamily u ht)), hx, sliceFamily_apply u ht⟩

@[simp]
theorem valueL_mk (u ux hx ht) :
    valueL (mk (α := α) (E := E) (F := F) (a := a) (b := b) u ux hx ht) = u := (rfl)

theorem mk_apply (u ux hx ht) (p : slab (E := E) a b) :
    mk (α := α) (E := E) (F := F) (a := a) (b := b) u ux hx ht p = u p := by
  rw [← valueL_apply, valueL_mk]

@[simp]
theorem spatialFDerivL_mk (u ux hx ht) :
    spatialFDerivL (mk (α := α) (E := E) (F := F) (a := a) (b := b) u ux hx ht) = ux := (rfl)

private theorem timeSliceL_mk (u ux hx ht) :
    timeSliceL (mk (α := α) (E := E) (F := F) (a := a) (b := b) u ux hx ht) =
      sliceFamily u ht := (rfl)

/-- The norm of a constructed element is at most `2 ‖u‖_∞ + ‖D_x u‖_{α,par} + [u]_{t,(1+α)/2}`,
with the Hölder norm of the gradient. -/
theorem norm_mk_le (u ux hx ht) :
    ‖mk (α := α) (E := E) (F := F) (a := a) (b := b) u ux hx ht‖ ≤
      2 * ‖u‖ + ‖ux‖ + (timeEHolderNorm ((1 + α) / 2) (u : slab (E := E) a b → F)).toReal := by
  rw [norm_eq, valueL_mk, spatialFDerivL_mk, timeSliceL_mk]
  linarith [norm_sliceFamily_le u ht]

/-- Equality of the underlying maps determines the gradient and the time slices. -/
@[ext]
theorem ext {f g : ParabolicC1HolderSpace α E F a b} (h : ∀ p, f p = g p) : f = g := by
  have hv : valueL f = valueL g := DFunLike.ext _ _ h
  have hx : spatialFDerivL f = spatialFDerivL g := by
    apply HolderSpace.ext
    intro p
    obtain ⟨x, t, rfl⟩ : ∃ x t, slabMk x t = p := ⟨_, _, slabMk_space_slabTime p⟩
    rw [← f.fderiv_eq, ← g.fderiv_eq]
    exact congrArg (fun q : E → F ↦ fderiv ℝ q x) (funext fun y ↦ h (slabMk y t))
  have hs : timeSliceL f = timeSliceL g :=
    lp.ext (funext fun x ↦ HolderSpace.ext fun t ↦ by
      rw [timeSliceL_apply, timeSliceL_apply, h])
  apply Subtype.ext
  exact congrArg (WithLp.toLp 1) (Prod.ext hv (congrArg (WithLp.toLp 1) (Prod.ext hx hs)))

/-- The supremum norm of the value is bounded by the norm. -/
theorem norm_valueL_le (f : ParabolicC1HolderSpace α E F a b) : ‖valueL f‖ ≤ ‖f‖ := by
  rw [norm_eq]
  linarith [norm_nonneg (spatialFDerivL f), norm_nonneg (timeSliceL f)]

/-- The Hölder norm of the gradient is bounded by the norm. -/
theorem norm_spatialFDerivL_le (f : ParabolicC1HolderSpace α E F a b) :
    ‖spatialFDerivL f‖ ≤ ‖f‖ := by
  rw [norm_eq]
  linarith [norm_nonneg (valueL f), norm_nonneg (timeSliceL f)]

/-- The full order-one parabolic norm
`‖u‖_∞ + ‖D_x u‖_∞ + [D_x u]_{α,par} + [u]_{t,(1+α)/2}`. -/
def fullNorm (f : ParabolicC1HolderSpace α E F a b) : ℝ :=
  ‖valueL f‖ + ‖spatialFDerivL f‖ +
    (timeEHolderNorm ((1 + α) / 2) (f : slab (E := E) a b → F)).toReal

/-- The full norm adds the temporal seminorm to the supremum norm and the Hölder norm of the
gradient. -/
theorem fullNorm_def (f : ParabolicC1HolderSpace α E F a b) :
    f.fullNorm = ‖valueL f‖ + ‖spatialFDerivL f‖ +
      (timeEHolderNorm ((1 + α) / 2) (f : slab (E := E) a b → F)).toReal := (rfl)

/-- The norm and the full parabolic norm are equivalent with constants `1` and `2`. -/
theorem fullNorm_le_norm_le (f : ParabolicC1HolderSpace α E F a b) :
    f.fullNorm ≤ ‖f‖ ∧ ‖f‖ ≤ 2 * f.fullNorm := by
  have hT : (timeEHolderNorm ((1 + α) / 2) (f : slab (E := E) a b → F)).toReal ≤
      ‖timeSliceL f‖ := by
    simpa using ENNReal.toReal_mono ENNReal.coe_ne_top f.timeEHolderNorm_le_nnnorm_timeSliceL
  have hS : ‖timeSliceL f‖ ≤
      ‖valueL f‖ + (timeEHolderNorm ((1 + α) / 2) (f : slab (E := E) a b → F)).toReal := by
    have h := norm_sliceFamily_le (valueL f) f.timeEHolderNorm_lt_top
    have he : sliceFamily (valueL f) f.timeEHolderNorm_lt_top = timeSliceL f :=
      lp.ext (funext fun x ↦ HolderSpace.ext fun t ↦ by
        rw [timeSliceL_apply, sliceFamily_apply, valueL_apply])
    rwa [he] at h
  rw [fullNorm, norm_eq]
  constructor <;> linarith [norm_nonneg (valueL f), norm_nonneg (spatialFDerivL f),
    ENNReal.toReal_nonneg (a := timeEHolderNorm ((1 + α) / 2) (f : slab (E := E) a b → F))]

/-! ### Completeness -/

private theorem isClosed_spatialGraph (t : Icc a b) : IsClosed {J : Jet α E F a b |
    ∀ x, HasFDerivAt (fun y ↦ valueJetL J (slabMk y t)) (gradJetL J (slabMk x t)) x} := by
  simpa only [preimage_ofPred_eq, Function.comp_def,
    HolderSpace.toBoundedContinuousFunctionCLM_apply,
    HolderSpace.toBoundedContinuousFunction_apply] using
    (isClosed_setOf_hasFDerivAt_spatialSlice t).preimage
      (valueJetL.continuous.prodMk
        (HolderSpace.toBoundedContinuousFunctionCLM.continuous.comp gradJetL.continuous))

private theorem isClosed_sliceGraph (x : E) (t : Icc a b) :
    IsClosed {J : Jet α E F a b | sliceJetL J x t = valueJetL J (slabMk x t)} := by
  refine isClosed_eq ?_ ((continuous_eval_const (slabMk x t)).comp valueJetL.continuous)
  refine ((HolderSpace.evalCLM t).continuous.comp
    ((lp.evalCLM ℝ (fun _ : E ↦ HolderSpace ((1 + α) / 2) (Icc a b) F) ∞ x).continuous.comp
      sliceJetL.continuous)).congr fun J ↦ ?_
  rw [Function.comp_apply, Function.comp_apply, HolderSpace.evalCLM_apply]
  -- Evaluation in `lp` is the application of the underlying family.
  rfl

private theorem isClosed_isJetGraph : IsClosed {J : Jet α E F a b | IsJetGraph J} := by
  simpa only [IsJetGraph, ofPred_and, ofPred_forall] using
    (isClosed_iInter (isClosed_spatialGraph (α := α) (E := E) (F := F))).inter
      (isClosed_iInter fun x ↦ isClosed_iInter (isClosed_sliceGraph (α := α) (F := F) x))

/-- Bounded order-one parabolic Hölder maps with Banach values form a Banach space. -/
instance [CompleteSpace F] : CompleteSpace (ParabolicC1HolderSpace α E F a b) := by
  unfold ParabolicC1HolderSpace
  exact (isClosed_isJetGraph (α := α) (E := E) (F := F)).completeSpace_coe

/-! ### The inclusion into `C_b^{α,α/2}` -/

/-- For `α ≤ 1`, the parabolic `α`-seminorm of the value is at most
`‖D_x u‖_∞ + [u]_{t,(1+α)/2} + 4 ‖u‖_∞`: a bounded gradient makes the spatial slices Lipschitz,
and `α / 2 ≤ (1 + α) / 2`. -/
private theorem eHolderNorm_le (hα : α ≤ 1) (f : ParabolicC1HolderSpace α E F a b) :
    eHolderNorm α (f : slab (E := E) a b → F) ≤
      ↑(‖(spatialFDerivL f).toBoundedContinuousFunction‖₊ +
        (timeEHolderNorm ((1 + α) / 2) (f : slab (E := E) a b → F)).toNNReal +
        4 * ‖valueL f‖₊) := by
  have hspace : spaceEHolderNorm 1 (f : slab (E := E) a b → F) ≤
      ‖(spatialFDerivL f).toBoundedContinuousFunction‖₊ := by
    rcases le_or_gt a b with hab | hab
    · -- Extend constantly in time, so as to apply the Lipschitz bound on `E × ℝ`.
      rw [← ParabolicC2HolderSpace.timeExtension_space_slabTime hab
        (f : slab (E := E) a b → F)]
      refine spaceEHolderNorm_one_le_of_hasFDerivAt
        (w' := ParabolicC2HolderSpace.timeExtension hab (spatialFDerivL f))
        (fun t ht y ↦ ?_) fun y t ht ↦ ?_
      · simpa [ParabolicC2HolderSpace.timeExtension_def, projIcc_of_mem hab ht] using
          f.hasSpatialFDerivAt ⟨t, ht⟩ y
      · simpa only [ParabolicC2HolderSpace.timeExtension_def,
          HolderSpace.toBoundedContinuousFunction_apply, coe_nnnorm] using
          (spatialFDerivL f).toBoundedContinuousFunction.norm_coe_le_norm _
    · -- The slab is empty.
      exact spaceEHolderNorm_le_iff.2 fun t ↦ absurd (t.2.1.trans t.2.2) hab.not_ge
  have hD : ∀ p q, dist (f p) (f q) ≤ ((2 * ‖valueL f‖₊ : ℝ≥0) : ℝ) := fun p q ↦ by
    simpa using (valueL f).dist_le_two_norm p q
  have h := eHolderNorm_le_of_spaceEHolderNorm_le_of_timeEHolderNorm_le hspace
    (ENNReal.coe_toNNReal f.timeEHolderNorm_lt_top.ne).ge hD hα
    (by gcongr; exact le_add_self) one_pos one_pos
  refine h.trans (le_of_eq ?_)
  simp only [NNReal.one_rpow]
  congr 1
  ring

/-- For `α ≤ 1`, the value of a bounded order-one parabolic Hölder map is parabolically
`α`-Hölder. -/
theorem memHolder_valueL (hα : α ≤ 1) (f : ParabolicC1HolderSpace α E F a b) :
    MemHolder α (valueL f : slab (E := E) a b → F) :=
  eHolderNorm_lt_top.1 ((f.eHolderNorm_le hα).trans_lt ENNReal.coe_lt_top)

/-- For `α ≤ 1`, the inclusion `C_{par,b}^{1+α} → C_b^{α,α/2}`, as a continuous linear map of
norm at most `5`. -/
def valueHolderL (hα : α ≤ 1) :
    ParabolicC1HolderSpace α E F a b →L[ℝ] HolderSpace α (slab (E := E) a b) F :=
  LinearMap.mkContinuous
    { toFun f := HolderSpace.ofBoundedContinuousFunction (valueL f) (memHolder_valueL hα f)
      map_add' f g := HolderSpace.ext fun p ↦ by simp [HolderSpace.add_apply]
      map_smul' c f := HolderSpace.ext fun p ↦ by simp [HolderSpace.smul_apply] }
    5 fun f ↦ by
      have h := f.eHolderNorm_le hα
      rw [← (memHolder_valueL hα f).coe_nnHolderNorm_eq_eHolderNorm, ENNReal.coe_le_coe,
        ← NNReal.coe_le_coe] at h
      push_cast at h
      have hfull := (f.fullNorm_le_norm_le).1
      have hu := f.norm_valueL_le
      rw [fullNorm, HolderSpace.norm_def (spatialFDerivL f)] at hfull
      simp only [LinearMap.coe_mk, AddHom.coe_mk, HolderSpace.norm_def,
        HolderSpace.toBoundedContinuousFunction_ofBoundedContinuousFunction]
      nlinarith [norm_nonneg (valueL f), NNReal.coe_nonneg (nnHolderNorm α
        ((spatialFDerivL f).toBoundedContinuousFunction : _ → _))]

/-- The inclusion into `C_b^{α,α/2}` has operator norm at most `5`. -/
theorem norm_valueHolderL_le (hα : α ≤ 1) :
    ‖valueHolderL (E := E) (F := F) (a := a) (b := b) hα‖ ≤ 5 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) _

@[simp]
theorem toBoundedContinuousFunction_valueHolderL (hα : α ≤ 1)
    (f : ParabolicC1HolderSpace α E F a b) :
    (valueHolderL hα f).toBoundedContinuousFunction = valueL f := by
  simp [valueHolderL]

@[simp]
theorem valueHolderL_apply (hα : α ≤ 1) (f : ParabolicC1HolderSpace α E F a b)
    (p : slab (E := E) a b) : valueHolderL hα f p = f p := by
  rw [← HolderSpace.toBoundedContinuousFunction_apply, toBoundedContinuousFunction_valueHolderL,
    valueL_apply]

end ParabolicC1HolderSpace

/-! ### Order two to order one -/

namespace ParabolicC2HolderSpace

variable {hab : a < b}

/-- For `α ≤ 1` the temporal exponent `(1 + α) / 2` of the order-one space is at most one. -/
private theorem one_add_div_two_le_one (hα : α ≤ 1) : (1 + α) / 2 ≤ 1 := by
  rw [div_le_one₀ two_pos]
  calc 1 + α ≤ 1 + 1 := by gcongr
    _ = 2 := one_add_one_eq_two

/-- For `α ≤ 1`, the inclusion `C_b^{2+α,1+α/2} → C_{par,b}^{1+α}`: an order-two map is
an order-one map with the same value and gradient. It is a continuous linear map of norm at most
`29`. -/
def toC1L (hα : α ≤ 1) : ParabolicC2HolderSpace α E F hab →L[ℝ]
    ParabolicC1HolderSpace α E F a b :=
  LinearMap.mkContinuous
    { toFun f := ParabolicC1HolderSpace.mk (valueL f) (spatialFDerivHolderL hα f)
        (fun t x ↦ by simpa using f.hasSpatialFDerivAt t x)
        ((timeEHolderNorm_le (one_add_div_two_le_one hα) f).trans_lt
          ENNReal.coe_lt_top)
      map_add' f g := ParabolicC1HolderSpace.ext fun p ↦ by simp
      map_smul' c f := ParabolicC1HolderSpace.ext fun p ↦ by simp }
    29 fun f ↦ by
      have hγ := one_add_div_two_le_one hα
      have hT := ENNReal.toReal_mono ENNReal.coe_ne_top (timeEHolderNorm_le hγ f)
      rw [ENNReal.coe_toReal] at hT
      push_cast at hT
      have hD := norm_valueHolderL_add_norm_spatialFDerivHolderL_le hα f one_pos le_rfl
      simp only [Real.one_rpow, mul_one] at hD
      have hM := ParabolicC1HolderSpace.norm_mk_le (valueL f) (spatialFDerivHolderL hα f)
        (fun t x ↦ by simpa using f.hasSpatialFDerivAt t x)
        ((timeEHolderNorm_le hγ f).trans_lt ENNReal.coe_lt_top)
      have hu := norm_valueL_le f
      have ht := (HolderSpace.norm_toBoundedContinuousFunction_le (timeDerivL f)).trans
        (norm_timeDerivL_le f)
      have hv := norm_nonneg (valueHolderL hα f)
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      linarith

/-- The inclusion into the order-one space has operator norm at most `29`. -/
theorem norm_toC1L_le (hα : α ≤ 1) :
    ‖toC1L (E := E) (F := F) (hab := hab) hα‖ ≤ 29 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) _

@[simp]
theorem valueL_toC1L (hα : α ≤ 1) (f : ParabolicC2HolderSpace α E F hab) :
    ParabolicC1HolderSpace.valueL (toC1L hα f) = valueL f := by
  simp [toC1L]

@[simp]
theorem spatialFDerivL_toC1L (hα : α ≤ 1) (f : ParabolicC2HolderSpace α E F hab) :
    ParabolicC1HolderSpace.spatialFDerivL (toC1L hα f) = spatialFDerivHolderL hα f := by
  simp [toC1L]

theorem toC1L_apply (hα : α ≤ 1) (f : ParabolicC2HolderSpace α E F hab)
    (p : slab (E := E) a b) : toC1L hα f p = f p := by
  rw [← ParabolicC1HolderSpace.valueL_apply, valueL_toC1L, valueL_apply]

/-- The inclusions `C_b^{2+α,1+α/2} → C_{par,b}^{1+α} → C_b^{α,α/2}` compose to the inclusion
`valueHolderL` of the order-two space. -/
@[simp]
theorem valueHolderL_toC1L (hα : α ≤ 1) (f : ParabolicC2HolderSpace α E F hab) :
    ParabolicC1HolderSpace.valueHolderL hα (toC1L hα f) = valueHolderL hα f :=
  HolderSpace.ext fun p ↦ by simp

/-- **The spatial gradient lowers the order by one.** For every `α`, `u ↦ D_x u` maps
`C_b^{2+α,1+α/2}` into the order-one space `C_{par,b}^{1+α}` of gradient-valued maps, whose
gradient is the Hessian `D_x² u`. It is a continuous linear map of norm at most `2`. -/
def spatialFDerivC1L :
    ParabolicC2HolderSpace α E F hab →L[ℝ] ParabolicC1HolderSpace α E (E →L[ℝ] F) a b :=
  LinearMap.mkContinuous
    { toFun f := ParabolicC1HolderSpace.mk (spatialFDerivL f) (spatialSecondFDerivL f)
        f.hasSpatialSecondFDerivAt f.timeEHolderNorm_spatialFDeriv_lt_top
      map_add' f g := ParabolicC1HolderSpace.ext fun p ↦ by simp
      map_smul' c f := ParabolicC1HolderSpace.ext fun p ↦ by simp }
    2 fun f ↦ by
      have hM := ParabolicC1HolderSpace.norm_mk_le (spatialFDerivL f) (spatialSecondFDerivL f)
        f.hasSpatialSecondFDerivAt f.timeEHolderNorm_spatialFDeriv_lt_top
      have hT := f.toReal_timeEHolderNorm_spatialFDeriv_le
      have hf := f.norm_eq
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      nlinarith [norm_nonneg (valueL f), norm_nonneg (timeDerivL f)]

/-- The gradient map into the order-one space has operator norm at most `2`. -/
theorem norm_spatialFDerivC1L_le : ‖spatialFDerivC1L (α := α) (E := E) (F := F) (hab := hab)‖ ≤ 2 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) _

@[simp]
theorem valueL_spatialFDerivC1L (f : ParabolicC2HolderSpace α E F hab) :
    ParabolicC1HolderSpace.valueL (spatialFDerivC1L f) = spatialFDerivL f := by
  simp [spatialFDerivC1L]

@[simp]
theorem spatialFDerivL_spatialFDerivC1L (f : ParabolicC2HolderSpace α E F hab) :
    ParabolicC1HolderSpace.spatialFDerivL (spatialFDerivC1L f) = spatialSecondFDerivL f := by
  simp [spatialFDerivC1L]

theorem spatialFDerivC1L_apply (f : ParabolicC2HolderSpace α E F hab) (p : slab (E := E) a b) :
    spatialFDerivC1L f p = spatialFDerivL f p := by
  rw [← ParabolicC1HolderSpace.valueL_apply, valueL_spatialFDerivC1L]

end ParabolicC2HolderSpace

attribute [irreducible] _root_.TauCeti.ParabolicC1HolderSpace

end TauCeti
