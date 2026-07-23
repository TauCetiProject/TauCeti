/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.VariableLp.Basic
public import TauCeti.Analysis.PDE.Uniform.EllipticEnergy
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

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

* `TauCeti.PDE.const_mul_norm_mul_norm_le_energyFormLpVariable_self`: integration of a
  pointwise diagonal lower bound.
* `TauCeti.PDE.isCoercive_energyFormLpVariable`: coercivity from a positive pointwise constant.
* `TauCeti.PDE.min_diagonal_lower_bound_mul_norm_sq_le_energyFormLpVariable_self_of_bounds`:
  the integrated Gårding bound from a principal quadratic lower bound.
* `TauCeti.PDE.isCoercive_energyFormLpVariable_of_bounds`: coercivity from that bound.
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
theorem const_mul_norm_mul_norm_le_energyFormLpVariable_self (μ : Measure X)
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

/-- A positive uniform pointwise diagonal lower bound makes the variable-coefficient `L²`
energy form coercive. -/
theorem isCoercive_energyFormLpVariable (μ : Measure X)
    (a : X → Matrix n n ℝ) (b : X → EuclideanSpace ℝ n) (c : X → ℝ)
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ μ)
    {C : ℝ} (hC : 0 < C) (hlower : ∀ᵐ x ∂μ, ∀ U : ℝ × EuclideanSpace ℝ n,
      C * ‖U‖ ^ 2 ≤ energyIntegrand (a x) (b x) (c x) U U) :
    IsCoercive (energyFormLpVariable μ a b c hcoeff) :=
  ⟨C, hC, const_mul_norm_mul_norm_le_energyFormLpVariable_self μ a b c hcoeff hlower⟩

/-- A positive principal quadratic lower bound, a drift bound, and a mass floor give the
explicit diagonal lower bound for the variable-coefficient `L²` energy form. -/
theorem min_diagonal_lower_bound_mul_norm_sq_le_energyFormLpVariable_self_of_bounds
    (μ : Measure X) (a : X → Matrix n n ℝ) (b : X → EuclideanSpace ℝ n) (c : X → ℝ)
    {lam beta mass : ℝ} (hlam : 0 < lam)
    (ha : ∀ᵐ x ∂μ, ∀ ξ : EuclideanSpace ℝ n,
      lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ)
    (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta) (hc : ∀ᵐ x ∂μ, mass ≤ c x)
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ μ)
    (U : Lp (ℝ × EuclideanSpace ℝ n) 2 μ) :
    min (lam / 2) (mass - beta ^ 2 / (2 * lam)) * ‖U‖ * ‖U‖ ≤
      energyFormLpVariable μ a b c hcoeff U U := by
  apply const_mul_norm_mul_norm_le_energyFormLpVariable_self μ a b c hcoeff
  filter_upwards [ha, hb, hc] with x hax hbx hcx
  intro V
  have hdiag :
      min (lam / 2) (mass - beta ^ 2 / (2 * lam)) * ‖V‖ ^ 2 ≤
        lam / 2 * ‖V.2‖ ^ 2 + (mass - beta ^ 2 / (2 * lam)) * V.1 ^ 2 := by
    rw [Prod.norm_def, max_def]
    split_ifs with hV
    · have hVsq : V.1 ^ 2 ≤ ‖V.2‖ ^ 2 := by
        have habs : |V.1| ≤ ‖V.2‖ := by simpa [Real.norm_eq_abs] using hV
        rw [← sq_abs]
        nlinarith [abs_nonneg V.1, norm_nonneg V.2]
      nlinarith [min_le_left (lam / 2) (mass - beta ^ 2 / (2 * lam)),
        min_le_right (lam / 2) (mass - beta ^ 2 / (2 * lam)), hlam.le,
        sq_nonneg ‖V.2‖, sq_nonneg V.1]
    · rw [Real.norm_eq_abs, sq_abs]
      nlinarith [min_le_right (lam / 2) (mass - beta ^ 2 / (2 * lam)), hlam.le,
        sq_nonneg ‖V.2‖, sq_nonneg V.1]
  exact hdiag.trans
    (garding_energyIntegrand_self_of_mass_lower_bound_of_bounds hlam hax hbx hcx V)

/-- A positive explicit Gårding constant makes the variable-coefficient `L²` energy form
coercive under only a principal quadratic lower bound. -/
theorem isCoercive_energyFormLpVariable_of_bounds (μ : Measure X)
    (a : X → Matrix n n ℝ) (b : X → EuclideanSpace ℝ n) (c : X → ℝ)
    {lam beta mass : ℝ} (hlam : 0 < lam)
    (ha : ∀ᵐ x ∂μ, ∀ ξ : EuclideanSpace ℝ n,
      lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ)
    (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta) (hc : ∀ᵐ x ∂μ, mass ≤ c x)
    (hpos : 0 < min (lam / 2) (mass - beta ^ 2 / (2 * lam)))
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ μ) :
    IsCoercive (energyFormLpVariable μ a b c hcoeff) := by
  refine ⟨min (lam / 2) (mass - beta ^ 2 / (2 * lam)), hpos, ?_⟩
  exact min_diagonal_lower_bound_mul_norm_sq_le_energyFormLpVariable_self_of_bounds
    μ a b c hlam ha hb hc hcoeff

namespace UniformlyEllipticOn

variable {Ω : Set X} {a : X → Matrix n n ℝ}
variable {b : X → EuclideanSpace ℝ n} {c : X → ℝ}
variable {lam Lam beta mass : ℝ}

/-- Uniform ellipticity, a drift bound, and a mass floor give the explicit diagonal lower
bound for the variable-coefficient `L²` energy form. -/
theorem min_diagonal_lower_bound_mul_norm_sq_le_energyFormLpVariable_self (μ : Measure X)
    (h : UniformlyEllipticOn Ω a lam Lam) (hΩ : ∀ᵐ x ∂μ, x ∈ Ω)
    (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta) (hc : ∀ᵐ x ∂μ, mass ≤ c x)
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ μ)
    (U : Lp (ℝ × EuclideanSpace ℝ n) 2 μ) :
    min (lam / 2) (mass - beta ^ 2 / (2 * lam)) * ‖U‖ * ‖U‖ ≤
      energyFormLpVariable μ a b c hcoeff U U := by
  apply PDE.min_diagonal_lower_bound_mul_norm_sq_le_energyFormLpVariable_self_of_bounds
    μ a b c h.pos
  · filter_upwards [hΩ] with x hx
    exact h.lower_bound hx
  · exact hb
  · exact hc

/-- The variable-coefficient `L²` energy form is coercive when uniform ellipticity and the
mass floor make the explicit Gårding constant positive. -/
theorem isCoercive_energyFormLpVariable (μ : Measure X)
    (h : UniformlyEllipticOn Ω a lam Lam) (hΩ : ∀ᵐ x ∂μ, x ∈ Ω)
    (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta) (hc : ∀ᵐ x ∂μ, mass ≤ c x)
    (hpos : 0 < min (lam / 2) (mass - beta ^ 2 / (2 * lam)))
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ μ) :
    IsCoercive (energyFormLpVariable μ a b c hcoeff) := by
  apply PDE.isCoercive_energyFormLpVariable_of_bounds μ a b c h.pos
  · filter_upwards [hΩ] with x hx
    exact h.lower_bound hx
  · exact hb
  · exact hc
  · exact hpos

end UniformlyEllipticOn

end PDE

end TauCeti

end
