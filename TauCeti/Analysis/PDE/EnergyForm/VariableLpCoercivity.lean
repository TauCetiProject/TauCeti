/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.VariableLp
public import TauCeti.Analysis.PDE.Uniform.EllipticEnergy
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Coercivity of variable-coefficient energy forms on `L²` jets

This file completes the lower-bound API for the variable-coefficient energy form
`PDE.energyFormLpVariable`.  A pointwise diagonal estimate

`C * ‖U x‖² ≤ energyIntegrand (a x) (b x) (c x) (U x) (U x)`

integrates to the corresponding estimate on `L²`.  A positive constant therefore makes the
bundled energy form coercive in Mathlib's sense.  Uniform ellipticity, a bounded drift, and a
sufficiently positive mass coefficient provide such a constant through the Gårding estimate
already developed for raw jets.

This is the coercivity part of Lane D, item 16 of the PDE roadmap.  It is stated on the full
`L²` value-gradient jet space; a later weak-derivative Sobolev Hilbert space can pull the form
and this estimate back along its value-gradient map before applying Lax--Milgram.

## Main declarations

* `TauCeti.PDE.lower_bound_energyFormLpVariable_self`: integration of a pointwise diagonal
  lower bound.
* `TauCeti.PDE.isCoercive_energyFormLpVariable`: coercivity from a positive pointwise constant.
* `TauCeti.PDE.UniformlyEllipticOn.isCoercive_energyFormLpVariable`: coercivity from uniform
  ellipticity and lower-order coefficient bounds.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open MeasureTheory Matrix
open scoped InnerProductSpace

variable {X n : Type*} [MeasurableSpace X] [Fintype n]

/-- A local classical decidable equality instance for the finite index type. -/
noncomputable local instance variableLpCoercivityDecidableEq : DecidableEq n := Classical.decEq n

private lemma integral_const_mul_norm_sq_eq (μ : Measure X) (C : ℝ)
    (U : Lp (ℝ × EuclideanSpace ℝ n) 2 μ) :
    ∫ x, C * ‖U x‖ ^ 2 ∂μ = C * ‖U‖ * ‖U‖ := by
  rw [integral_const_mul]
  have hsquare : (∫ x, ‖U x‖ ^ 2 ∂μ) = ‖U‖ ^ 2 := by
    rw [Lp.norm_def, toReal_eLpNorm (Lp.aestronglyMeasurable U),
      lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
        (Lp.aestronglyMeasurable U)]
    norm_num
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt]
    exact integral_nonneg fun _ => sq_nonneg _
  rw [hsquare, pow_two, mul_assoc]

/-- A uniform pointwise diagonal lower bound integrates to the same lower bound for the
variable-coefficient `L²` energy form. -/
theorem lower_bound_energyFormLpVariable_self (μ : Measure X)
    (a : X → Matrix n n ℝ) (b : X → EuclideanSpace ℝ n) (c : X → ℝ)
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ μ)
    {C : ℝ} (hlower : ∀ᵐ x ∂μ, ∀ U : ℝ × EuclideanSpace ℝ n,
      C * ‖U‖ ^ 2 ≤ energyIntegrand (a x) (b x) (c x) U U)
    (U : Lp (ℝ × EuclideanSpace ℝ n) 2 μ) :
    C * ‖U‖ * ‖U‖ ≤ energyFormLpVariable μ a b c hcoeff U U := by
  rw [energyFormLpVariable_apply, ← integral_const_mul_norm_sq_eq μ C U]
  refine integral_mono_ae ?_ (integrable_bilinear_apply_of_memLp hcoeff U U) ?_
  · exact ((Lp.memLp U).integrable_norm_pow (by norm_num)).const_mul C
  · filter_upwards [hlower] with x hx
    exact hx (U x)

/-- A nonnegative pointwise energy density gives a nonnegative variable-coefficient `L²`
energy form on the diagonal. -/
theorem energyFormLpVariable_self_nonneg (μ : Measure X)
    (a : X → Matrix n n ℝ) (b : X → EuclideanSpace ℝ n) (c : X → ℝ)
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ μ)
    (hnonneg : ∀ᵐ x ∂μ, ∀ U : ℝ × EuclideanSpace ℝ n,
      0 ≤ energyIntegrand (a x) (b x) (c x) U U)
    (U : Lp (ℝ × EuclideanSpace ℝ n) 2 μ) :
    0 ≤ energyFormLpVariable μ a b c hcoeff U U := by
  have h := lower_bound_energyFormLpVariable_self μ a b c hcoeff (C := 0)
    (by simpa using hnonneg) U
  simpa using h

/-- A positive uniform pointwise diagonal lower bound makes the variable-coefficient `L²`
energy form coercive. -/
theorem isCoercive_energyFormLpVariable (μ : Measure X)
    (a : X → Matrix n n ℝ) (b : X → EuclideanSpace ℝ n) (c : X → ℝ)
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ μ)
    {C : ℝ} (hC : 0 < C) (hlower : ∀ᵐ x ∂μ, ∀ U : ℝ × EuclideanSpace ℝ n,
      C * ‖U‖ ^ 2 ≤ energyIntegrand (a x) (b x) (c x) U U) :
    IsCoercive (energyFormLpVariable μ a b c hcoeff) :=
  ⟨C, hC, lower_bound_energyFormLpVariable_self μ a b c hcoeff hlower⟩

namespace UniformlyEllipticOn

variable {Ω : Set X} {a : X → Matrix n n ℝ}
variable {b : X → EuclideanSpace ℝ n} {c : X → ℝ}
variable {lam Lam beta mass : ℝ}

/-- Uniform ellipticity, a drift bound, and a mass floor give the explicit diagonal lower
bound for the variable-coefficient `L²` energy form. -/
theorem lower_bound_energyFormLpVariable_self (μ : Measure X)
    (h : UniformlyEllipticOn Ω a lam Lam) (hΩ : ∀ᵐ x ∂μ, x ∈ Ω)
    (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta) (hc : ∀ᵐ x ∂μ, mass ≤ c x)
    (hmass : beta ^ 2 / (2 * lam) ≤ mass)
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ μ)
    (U : Lp (ℝ × EuclideanSpace ℝ n) 2 μ) :
    min (lam / 2) (mass - beta ^ 2 / (2 * lam)) * ‖U‖ * ‖U‖ ≤
      energyFormLpVariable μ a b c hcoeff U U := by
  apply PDE.lower_bound_energyFormLpVariable_self μ a b c hcoeff
  filter_upwards [hΩ, hb, hc] with x hx hbx hcx
  intro V
  exact h.min_diagonal_lower_bound_mul_norm_sq_le_energyIntegrand_self hx hbx hcx hmass V

/-- The variable-coefficient `L²` energy form is coercive when uniform ellipticity and the
mass floor make the explicit Gårding constant positive. -/
theorem isCoercive_energyFormLpVariable (μ : Measure X)
    (h : UniformlyEllipticOn Ω a lam Lam) (hΩ : ∀ᵐ x ∂μ, x ∈ Ω)
    (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta) (hc : ∀ᵐ x ∂μ, mass ≤ c x)
    (hmass : beta ^ 2 / (2 * lam) ≤ mass)
    (hpos : 0 < min (lam / 2) (mass - beta ^ 2 / (2 * lam)))
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ μ) :
    IsCoercive (energyFormLpVariable μ a b c hcoeff) := by
  refine ⟨min (lam / 2) (mass - beta ^ 2 / (2 * lam)), hpos, ?_⟩
  exact lower_bound_energyFormLpVariable_self μ h hΩ hb hc hmass hcoeff

end UniformlyEllipticOn

end PDE

end TauCeti

end
