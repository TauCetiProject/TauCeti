/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import TauCeti.MeasureTheory.Function.L0.Convergence
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Topology.Sequences

/-!
# Continuous operations on real random variables

Real random variables inherit addition, multiplication and real scalar multiplication from
their native almost-everywhere classes. These operations are continuous for convergence in
measure on finite measure spaces, without boundedness or integrability assumptions.
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace TauCeti.L0

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The additive group of real almost-everywhere classes, transported to `L0`. -/
instance instAddCommGroup : AddCommGroup (L0 μ) := equivAEEqFun.addCommGroup

/-- The multiplicative monoid of real almost-everywhere classes, transported to `L0`. -/
instance instCommMonoid : CommMonoid (L0 μ) := equivAEEqFun.commMonoid

/-- The real module of almost-everywhere classes, transported to `L0`. -/
instance instModule : Module ℝ (L0 μ) := equivAEEqFun.addEquiv.module ℝ

/-- The zero class in `L0` is the native zero class. -/
@[simp]
theorem toAEEqFun_zero : (0 : L0 μ).toAEEqFun = 0 := by
  simpa only [Equiv.addEquiv_apply, equivAEEqFun_apply] using
    (equivAEEqFun (μ := μ)).addEquiv.map_zero

/-- The unit class in `L0` is the native unit class. -/
@[simp]
theorem toAEEqFun_one : (1 : L0 μ).toAEEqFun = 1 := by
  simpa only [Equiv.mulEquiv_apply, equivAEEqFun_apply] using
    (equivAEEqFun (μ := μ)).mulEquiv.map_one

/-- Addition on `L0` is inherited from the native almost-everywhere quotient. -/
@[simp]
theorem toAEEqFun_add (f g : L0 μ) : (f + g).toAEEqFun = f.toAEEqFun + g.toAEEqFun := by
  simpa only [Equiv.addEquiv_apply, equivAEEqFun_apply] using
    (equivAEEqFun (μ := μ)).addEquiv.map_add f g

/-- Negation on `L0` is inherited from the native almost-everywhere quotient. -/
@[simp]
theorem toAEEqFun_neg (f : L0 μ) : (-f).toAEEqFun = -f.toAEEqFun := by
  simpa only [Equiv.addEquiv_apply, equivAEEqFun_apply] using
    (equivAEEqFun (μ := μ)).addEquiv.map_neg f

/-- Subtraction on `L0` is inherited from the native almost-everywhere quotient. -/
@[simp]
theorem toAEEqFun_sub (f g : L0 μ) : (f - g).toAEEqFun = f.toAEEqFun - g.toAEEqFun := by
  simpa only [Equiv.addEquiv_apply, equivAEEqFun_apply] using
    (equivAEEqFun (μ := μ)).addEquiv.map_sub f g

/-- Multiplication on `L0` is inherited from the native almost-everywhere quotient. -/
@[simp]
theorem toAEEqFun_mul (f g : L0 μ) : (f * g).toAEEqFun = f.toAEEqFun * g.toAEEqFun := by
  simpa only [Equiv.mulEquiv_apply, equivAEEqFun_apply] using
    (equivAEEqFun (μ := μ)).mulEquiv.map_mul f g

/-- Real scalar multiplication on `L0` is inherited from the native almost-everywhere quotient. -/
@[simp]
theorem toAEEqFun_smul (c : ℝ) (f : L0 μ) :
    (c • f).toAEEqFun = c • f.toAEEqFun := by
  simpa only [AddEquiv.linearEquiv_apply, Equiv.addEquiv_apply, equivAEEqFun_apply] using
    ((equivAEEqFun (μ := μ)).addEquiv.linearEquiv ℝ).map_smul c f

/-- Representatives of a sum agree almost everywhere with the pointwise sum. -/
theorem coeFn_add (f g : L0 μ) : ((f + g : L0 μ) : Ω → ℝ) =ᵐ[μ] fun x ↦ f x + g x := by
  filter_upwards [AEEqFun.coeFn_add f.toAEEqFun g.toAEEqFun] with x hx
  simpa only [toAEEqFun_add, Pi.add_apply] using hx

/-- Representatives of a product agree almost everywhere with the pointwise product. -/
theorem coeFn_mul (f g : L0 μ) : ((f * g : L0 μ) : Ω → ℝ) =ᵐ[μ] fun x ↦ f x * g x := by
  filter_upwards [AEEqFun.coeFn_mul f.toAEEqFun g.toAEEqFun] with x hx
  simpa only [toAEEqFun_mul, Pi.mul_apply] using hx

/-- Representatives of a scalar multiple agree almost everywhere with the pointwise multiple. -/
theorem coeFn_smul (c : ℝ) (f : L0 μ) : ((c • f : L0 μ) : Ω → ℝ) =ᵐ[μ] fun x ↦ c * f x := by
  filter_upwards [AEEqFun.coeFn_smul c f.toAEEqFun] with x hx
  simpa only [toAEEqFun_smul, Pi.smul_apply, smul_eq_mul] using hx

/-- Constructing a sum agrees with adding the constructed random variables. -/
@[simp]
theorem ofFun_add (f g : Ω → ℝ) (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) :
    ofFun f hf + ofFun g hg = ofFun (f + g) (hf.add hg) := by
  apply equivAEEqFun.injective
  simpa only [equivAEEqFun_apply, toAEEqFun_add, toAEEqFun_ofFun] using
    AEEqFun.mk_add_mk f g hf hg

/-- Constructing a product agrees with multiplying the constructed random variables. -/
@[simp]
theorem ofFun_mul (f g : Ω → ℝ) (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) :
    ofFun f hf * ofFun g hg = ofFun (f * g) (hf.mul hg) := by
  apply equivAEEqFun.injective
  simpa only [equivAEEqFun_apply, toAEEqFun_mul, toAEEqFun_ofFun] using
    AEEqFun.mk_mul_mk f g hf hg

/-- Constructing a scalar multiple agrees with scalar multiplication of a random variable. -/
@[simp]
theorem ofFun_smul (c : ℝ) (f : Ω → ℝ) (hf : AEStronglyMeasurable f μ) :
    c • ofFun f hf = ofFun (c • f) (hf.const_smul c) := by
  apply equivAEEqFun.injective
  simpa only [equivAEEqFun_apply, toAEEqFun_smul, toAEEqFun_ofFun] using
    AEEqFun.smul_mk c f hf

section FiniteMeasure

variable [IsFiniteMeasure μ]

private theorem continuous_binary {op : L0 μ → L0 μ → L0 μ} {φ : ℝ → ℝ → ℝ}
    (hφ : Continuous (Function.uncurry φ))
    (hop : ∀ f g, (op f g : Ω → ℝ) =ᵐ[μ] fun x ↦ φ (f x) (g x)) :
    Continuous (Function.uncurry op) := by
  apply continuous_iff_seqContinuous.2
  intro f g hfg
  apply tendsto_iff_tendstoInMeasure.2
  have h₁ := tendsto_iff_tendstoInMeasure.1 (continuous_fst.tendsto g |>.comp hfg)
  have h₂ := tendsto_iff_tendstoInMeasure.1 (continuous_snd.tendsto g |>.comp hfg)
  have h := h₁.continuous_comp₂ h₂ hφ
    (fun n ↦ (hφ.comp_stronglyMeasurable
      ((f n).1.stronglyMeasurable.prodMk (f n).2.stronglyMeasurable)).aestronglyMeasurable)
  exact h.congr (fun n ↦ (hop (f n).1 (f n).2).symm) (hop g.1 g.2).symm

/-- Addition of real random variables is continuous for convergence in measure. -/
instance instContinuousAdd : ContinuousAdd (L0 μ) where
  continuous_add := continuous_binary continuous_add coeFn_add

/-- Multiplication of real random variables is continuous for convergence in measure. -/
instance instContinuousMul : ContinuousMul (L0 μ) where
  continuous_mul := continuous_binary continuous_mul coeFn_mul

/-- Joint real scalar multiplication is continuous for convergence in measure. -/
instance instContinuousSMul : ContinuousSMul ℝ (L0 μ) where
  continuous_smul := by
    apply continuous_iff_seqContinuous.2
    intro f g hfg
    apply tendsto_iff_tendstoInMeasure.2
    have h₁ : TendstoInMeasure μ (fun n (_ : Ω) ↦ (f n).1) atTop (fun _ ↦ g.1) :=
      tendstoInMeasure_of_tendsto_ae (fun _ ↦ aestronglyMeasurable_const)
        (ae_of_all μ fun _ ↦ continuous_fst.tendsto g |>.comp hfg)
    have h₂ := tendsto_iff_tendstoInMeasure.1 (continuous_snd.tendsto g |>.comp hfg)
    have h := h₁.continuous_comp₂ h₂ continuous_mul
      (fun n ↦ ((f n).2.stronglyMeasurable.const_mul (f n).1).aestronglyMeasurable)
    exact h.congr (fun n ↦ (coeFn_smul (f n).1 (f n).2).symm)
      (coeFn_smul g.1 g.2).symm

end FiniteMeasure
end TauCeti.L0
