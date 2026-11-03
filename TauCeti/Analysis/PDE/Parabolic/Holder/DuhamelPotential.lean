/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.DuhamelPotential.Holder
public import TauCeti.Analysis.Holder.Normed

/-!
# The Duhamel potential as a bounded parabolic Hölder map

`heatDuhamelPotentialHolderL` sends bounded parabolic Hölder forcing on `E × [0,T]` to its
Duhamel heat potential in the same space. Its operator norm is at most
`T (2 + M_α) + max(1,T)`, where `M_α` is the heat-kernel moment. Its initial value is zero,
and, for complete codomains, constant forcing `c` produces exactly `t • c`.

This is the value component of the classical inhomogeneous heat solution operator. Spatial
Hölder regularity of the forcing controls the value's parabolic seminorm; time regularity is
not needed for that estimate. Derivative fields and the heat equation are separate assertions,
not part of this map's codomain.

## References

* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 1, Section 3.
* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4.
-/

public section
noncomputable section

namespace TauCeti

open MeasureTheory Set Real ParabolicSpaceTime
open scoped NNReal Interval BoundedContinuousFunction

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {α T : ℝ≥0}

private def forcing (f : HolderSpace α (slab (E := E) 0 T) F) (s : ℝ) (x : E) : F :=
  f (slabMk x (projIcc (0 : ℝ) (T : ℝ) T.coe_nonneg s))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem forcing_continuous (f : HolderSpace α (slab (E := E) 0 T) F) :
    Continuous (Function.uncurry (forcing f)) :=
  f.continuous.comp (continuous_slabMk.comp
    (continuous_snd.prodMk ((continuous_projIcc (h := T.coe_nonneg)).comp continuous_fst)))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem norm_forcing_le (f : HolderSpace α (slab (E := E) 0 T) F) (s : ℝ) (x : E) :
    ‖forcing f s x‖ ≤ ‖f‖ := f.norm_apply_le _

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem holderWith_forcing (f : HolderSpace α (slab (E := E) 0 T) F) (s : ℝ) :
    HolderWith ‖f‖₊ α (forcing f s) := by
  intro x y
  have h := f.memHolder.holderWith (slabMk x (projIcc (0 : ℝ) (T : ℝ) T.coe_nonneg s))
    (slabMk y (projIcc (0 : ℝ) (T : ℝ) T.coe_nonneg s))
  simp only [HolderSpace.toBoundedContinuousFunction_apply] at h
  unfold forcing
  refine h.trans ?_
  simp only [edist_slabMk, edist_self,
    ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2), add_zero]
  gcongr
  exact_mod_cast f.nnHolderNorm_le

private theorem holderWith_potential (hα : 0 < α) (hα₂ : α ≤ 2)
    (f : HolderSpace α (slab (E := E) 0 T) F) :
    HolderWith (T * ‖f‖₊ * (1 + heatKernelMoment E α) + ‖f‖₊ * max 1 T) α
      (fun p : slab (E := E) 0 T => heatDuhamelPotential (forcing f)
        (p : ParabolicSpaceTime E).time (p : ParabolicSpaceTime E).space) :=
  holderWith_heatDuhamelPotential (forcing_continuous f).stronglyMeasurable
    (fun s _ x => norm_forcing_le f s x) (fun s _ => holderWith_forcing f s) hα hα₂

private theorem norm_forcing_potential_le (f : HolderSpace α (slab (E := E) 0 T) F)
    (p : slab (E := E) 0 T) :
    ‖heatDuhamelPotential (forcing f) (p : ParabolicSpaceTime E).time
      (p : ParabolicSpaceTime E).space‖ ≤ (T : ℝ) * ‖f‖ := by
  have hp := (slabTime p).2
  rw [coe_slabTime] at hp
  exact ((norm_heatDuhamelPotential_le hp.1
    (ae_of_all _ fun s => ae_of_all _ fun x => norm_forcing_le f s x) _).trans
    (mul_le_mul_of_nonneg_left hp.2 (norm_nonneg f))).trans_eq (mul_comm _ _)

private def potentialBCF (hα : 0 < α) (hα₂ : α ≤ 2)
    (f : HolderSpace α (slab (E := E) 0 T) F) : slab (E := E) 0 T →ᵇ F :=
  BoundedContinuousFunction.ofNormedAddCommGroup _
    ((holderWith_potential hα hα₂ f).continuous hα) ((T : ℝ) * ‖f‖)
    (norm_forcing_potential_le f)

private theorem coe_potentialBCF (hα : 0 < α) (hα₂ : α ≤ 2)
    (f : HolderSpace α (slab (E := E) 0 T) F) :
    ⇑(potentialBCF hα hα₂ f) = fun p : slab (E := E) 0 T =>
      heatDuhamelPotential (forcing f) (p : ParabolicSpaceTime E).time
        (p : ParabolicSpaceTime E).space :=
  BoundedContinuousFunction.coe_ofNormedAddCommGroup _ _ _ _

private def potential (hα : 0 < α) (hα₂ : α ≤ 2)
    (f : HolderSpace α (slab (E := E) 0 T) F) : HolderSpace α (slab (E := E) 0 T) F :=
  HolderSpace.ofBoundedContinuousFunction (potentialBCF hα hα₂ f) (by
    rw [coe_potentialBCF]
    exact (holderWith_potential hα hα₂ f).memHolder)

private theorem potential_apply (hα : 0 < α) (hα₂ : α ≤ 2)
    (f : HolderSpace α (slab (E := E) 0 T) F) (p : slab (E := E) 0 T) :
    potential hα hα₂ f p = heatDuhamelPotential (forcing f)
      (p : ParabolicSpaceTime E).time (p : ParabolicSpaceTime E).space := by
  rw [potential, HolderSpace.ofBoundedContinuousFunction_apply, coe_potentialBCF]

private theorem norm_potential_le (hα : 0 < α) (hα₂ : α ≤ 2)
    (f : HolderSpace α (slab (E := E) 0 T) F) :
    ‖potential hα hα₂ f‖ ≤ (T * (2 + heatKernelMoment E α) + max 1 T : ℝ≥0) * ‖f‖ := by
  have hH := (holderWith_potential hα hα₂ f).nnholderNorm_le
  have hB : ‖(potential hα hα₂ f).toBoundedContinuousFunction‖ ≤ (T : ℝ) * ‖f‖ := by
    refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun p => ?_
    rw [HolderSpace.toBoundedContinuousFunction_apply, potential_apply]
    exact norm_forcing_potential_le f p
  rw [HolderSpace.norm_def]
  have hH' : (nnHolderNorm α ((potential hα hα₂ f).toBoundedContinuousFunction : _ → _) : ℝ) ≤
      (T * ‖f‖₊ * (1 + heatKernelMoment E α) + ‖f‖₊ * max 1 T : ℝ≥0) := by
    have heq : ((potential hα hα₂ f).toBoundedContinuousFunction : _ → _) =
        fun p : slab (E := E) 0 T => heatDuhamelPotential (forcing f)
          (p : ParabolicSpaceTime E).time (p : ParabolicSpaceTime E).space :=
      funext fun p => by rw [HolderSpace.toBoundedContinuousFunction_apply, potential_apply]
    rw [heq]
    exact_mod_cast hH
  push_cast at hH' ⊢
  linarith

/-- The Duhamel heat potential as a bounded linear endomorphism of the bounded parabolic
`α`-Hölder space on `E × [0,T]`, for `0 < α ≤ 2`. Its values are independent of the constant
extension of the forcing outside the slab used in the formula. -/
def heatDuhamelPotentialHolderL (hα : 0 < α) (hα₂ : α ≤ 2) :
    HolderSpace α (slab (E := E) 0 T) F →L[ℝ] HolderSpace α (slab (E := E) 0 T) F :=
  LinearMap.mkContinuous
    { toFun := potential hα hα₂
      map_add' f g := by
        ext p
        simp only [HolderSpace.add_apply, potential_apply, ← coe_slabTime]
        rw [heatDuhamelPotential_eq_integral_heatCauchyPotential (slabTime p).2.1,
          heatDuhamelPotential_eq_integral_heatCauchyPotential (slabTime p).2.1,
          heatDuhamelPotential_eq_integral_heatCauchyPotential (slabTime p).2.1]
        have hf := intervalIntegrable_heatCauchyPotential (forcing_continuous f).stronglyMeasurable
          (fun s _ x => norm_forcing_le f s x) (slabTime p).2 (slabTime p)
          (p : ParabolicSpaceTime E).space
        have hg := intervalIntegrable_heatCauchyPotential (forcing_continuous g).stronglyMeasurable
          (fun s _ x => norm_forcing_le g s x) (slabTime p).2 (slabTime p)
          (p : ParabolicSpaceTime E).space
        rw [← intervalIntegral.integral_add hf hg]
        apply intervalIntegral.integral_congr
        intro s _
        dsimp only
        have heq : forcing (f + g) s = forcing f s + forcing g s :=
          funext fun x => by simp [forcing, HolderSpace.add_apply]
        rw [heq]
        have hpair : Continuous (fun x : E => (s, x)) := continuous_const.prodMk continuous_id
        have hfc : Continuous (forcing f s) := (forcing_continuous f).comp hpair
        have hgc : Continuous (forcing g s) := (forcing_continuous g).comp hpair
        exact heatCauchyPotential_add hfc (norm_forcing_le f s) hgc (norm_forcing_le g s) _ _
      map_smul' c f := by
        ext p
        simp only [HolderSpace.smul_apply, potential_apply]
        rw [heatDuhamelPotential_def, heatDuhamelPotential_def,
          ← intervalIntegral.integral_smul]
        apply intervalIntegral.integral_congr
        intro s _
        dsimp only
        have heq : forcing (c • f) s = c • forcing f s :=
          funext fun x => by simp [forcing, HolderSpace.smul_apply]
        rw [heq, MeasureTheory.convolution_smul]
        rfl }
    (T * (2 + heatKernelMoment E α) + max 1 T : ℝ≥0)
    (norm_potential_le hα hα₂)

/-- Evaluation of the bounded Hölder Duhamel operator. The clamped extension only uses the
given forcing at times in `[0,t]` when evaluating at a slab point of time `t`. -/
@[simp]
theorem heatDuhamelPotentialHolderL_apply (hα : 0 < α) (hα₂ : α ≤ 2)
    (f : HolderSpace α (slab (E := E) 0 T) F) (p : slab (E := E) 0 T) :
    heatDuhamelPotentialHolderL hα hα₂ f p =
      heatDuhamelPotential (fun s x => f (slabMk x (projIcc (0 : ℝ) (T : ℝ) T.coe_nonneg s)))
        (p : ParabolicSpaceTime E).time (p : ParabolicSpaceTime E).space := by
  exact potential_apply hα hα₂ f p

/-- The norm of the Duhamel operator is bounded in terms of the horizon, exponent and
heat-kernel moment, independently of the forcing and the codomain. -/
theorem norm_heatDuhamelPotentialHolderL_le (hα : 0 < α) (hα₂ : α ≤ 2) :
    ‖heatDuhamelPotentialHolderL (E := E) (F := F) (T := T) hα hα₂‖ ≤
      (T * (2 + heatKernelMoment E α) + max 1 T : ℝ≥0) :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (norm_potential_le hα hα₂)

end TauCeti
