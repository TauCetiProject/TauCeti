/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Haar.ResidueClass
public import TauCeti.Topology.Algebra.Ring.Subring.ResidueClass
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.NoncommRing

/-!
# Quadratic Gauss integrals over residue classes

For a subring `R` of a ring with a star operation, the class Gauss sum is
`∫_{x₀ + g R^ι} ψ(τ b (x* J x - α)) dx`, for a chosen product measure.
In a second countable Hausdorff topological ring with continuous star, for a
sigma-finite measure finite on compact sets, a compact subring and a continuous
character, the integrand is integrable and its integral varies continuously
with the frequency `b` and norm `α`.
Its absolute value is at most the volume of the class, and its value at frequency
zero is exactly that volume. We also give conjugation and change-of-norm formulas.

The construction is useful for Fourier descriptions of local densities of hermitian
forms. The elementary API does not require `J` to be hermitian: that hypothesis
enters the subsequent differencing and density arguments.

## References

The corresponding finite-place integral is `New.Floors.IntegralPlace.classGaussSum` in
`grh/src/Lib/SiegelWeil/OneVector/ClassGaussSums.lean` of
[grh-lean](https://github.com/lsernau/grh-lean), commit
`72fead102f663d5c7a407964a13dc0cf9d977207` (Apache 2.0, Copyright 2026 Anthropic PBC).
-/

public section

open MeasureTheory Matrix
open scoped ENNReal ComplexConjugate

namespace Subring

variable {A ι : Type*} [Ring A] [Star A] [Fintype ι]
  [MeasurableSpace A]

/-- The quadratic Gauss integral over `x₀ + g R^ι`, with phase
`ψ(τ b (x* J x - α))` and product measure. -/
noncomputable def classGaussSum (R : Subring A) (μ : Measure A) (ψ : AddChar A Circle)
    (τ : A) (J : Matrix ι ι A) (g : Aˣ) (x₀ : ι → A) (α b : A) : ℂ :=
  ∫ x in R.residueClass g x₀,
    (ψ (τ * b * (star x ⬝ᵥ J.mulVec x - α)) : ℂ) ∂Measure.pi (fun _ : ι ↦ μ)

/-- The defining integral of the class Gauss sum. -/
theorem classGaussSum_def (R : Subring A) (μ : Measure A) (ψ : AddChar A Circle)
    (τ : A) (J : Matrix ι ι A) (g : Aˣ) (x₀ : ι → A) (α b : A) :
    classGaussSum R μ ψ τ J g x₀ α b =
      ∫ x in R.residueClass g x₀,
        (ψ (τ * b * (star x ⬝ᵥ J.mulVec x - α)) : ℂ) ∂Measure.pi (fun _ : ι ↦ μ) := (rfl)

variable (R : Subring A) (μ : Measure A) (ψ : AddChar A Circle)
  (τ : A) (J : Matrix ι ι A) (g : Aˣ) (x₀ : ι → A) (α b : A)

/-- At frequency zero, the Gauss integral equals the volume of its class. -/
@[simp]
theorem classGaussSum_zero_frequency : classGaussSum R μ ψ τ J g x₀ α 0 =
    ((Measure.pi (fun _ : ι ↦ μ)).real (R.residueClass g x₀) : ℂ) := by
  simp [classGaussSum]

/-- The trivial character also gives the volume of the class. -/
@[simp]
theorem classGaussSum_zero_character : classGaussSum R μ 0 τ J g x₀ α b =
    ((Measure.pi (fun _ : ι ↦ μ)).real (R.residueClass g x₀) : ℂ) := by
  simp [classGaussSum]

/-- A Gauss integral depends on the class, rather than its chosen centre. -/
theorem classGaussSum_eq_of_mem {x₁ : ι → A} (hx : x₁ ∈ R.residueClass g x₀) :
    classGaussSum R μ ψ τ J g x₁ α b = classGaussSum R μ ψ τ J g x₀ α b := by
  simp only [classGaussSum, R.residueClass_eq_of_mem g hx]

/-- Adding to the prescribed norm multiplies the integral by a character value. -/
theorem classGaussSum_add_target (a : A) :
    classGaussSum R μ ψ τ J g x₀ (α + a) b =
      (ψ (-(τ * b * a)) : ℂ) * classGaussSum R μ ψ τ J g x₀ α b := by
  have hphase (x : ι → A) : τ * b * (star x ⬝ᵥ J.mulVec x - (α + a)) =
      -(τ * b * a) + τ * b * (star x ⬝ᵥ J.mulVec x - α) := by noncomm_ring
  simp_rw [classGaussSum, hphase, ψ.map_add_eq_mul, Circle.coe_mul]
  exact integral_const_mul _ _

/-- The prescribed norm contributes only an explicit unit-modulus factor. -/
theorem classGaussSum_eq_mul_classGaussSum_zero_target :
    classGaussSum R μ ψ τ J g x₀ α b =
      (ψ (-(τ * b * α)) : ℂ) * classGaussSum R μ ψ τ J g x₀ 0 b := by
  simpa using classGaussSum_add_target R μ ψ τ J g x₀ 0 b α

/-- The absolute value of a class Gauss integral is independent of the prescribed norm. -/
theorem norm_classGaussSum_eq_norm_classGaussSum_zero_target :
    ‖classGaussSum R μ ψ τ J g x₀ α b‖ = ‖classGaussSum R μ ψ τ J g x₀ 0 b‖ := by
  rw [classGaussSum_eq_mul_classGaussSum_zero_target, norm_mul, Circle.norm_coe, one_mul]

/-- Reversing the frequency conjugates the Gauss integral. -/
@[simp]
theorem classGaussSum_neg_frequency :
    classGaussSum R μ ψ τ J g x₀ α (-b) = conj (classGaussSum R μ ψ τ J g x₀ α b) := by
  simp only [classGaussSum, mul_neg, neg_mul, ψ.map_neg_eq_inv, Circle.coe_inv_eq_conj]
  exact integral_conj

/-- The absolute value of a Gauss integral is at most the volume of its class.
This includes infinite-volume classes, for which the Bochner integral is zero. -/
theorem norm_classGaussSum_le :
    ‖classGaussSum R μ ψ τ J g x₀ α b‖ ≤
      (Measure.pi (fun _ : ι ↦ μ)).real (R.residueClass g x₀) := by
  calc
    ‖classGaussSum R μ ψ τ J g x₀ α b‖ ≤
        ∫ x in R.residueClass g x₀,
          ‖(ψ (τ * b * (star x ⬝ᵥ J.mulVec x - α)) : ℂ)‖
            ∂Measure.pi (fun _ : ι ↦ μ) := norm_integral_le_integral_norm _
    _ = _ := by simp

section Topology

variable [TopologicalSpace A] [IsTopologicalRing A] [ContinuousStar A] [T2Space A]
  [BorelSpace A] [SecondCountableTopology A] [SigmaFinite μ] [IsFiniteMeasureOnCompacts μ]

/-- For a continuous character and a compact subring, the Gauss integrand is integrable. -/
theorem integrableOn_addChar_quadratic_residueClass (hR : IsCompact (R : Set A))
    (hψ : Continuous ψ) :
    IntegrableOn (fun x : ι → A ↦
      (ψ (τ * b * (star x ⬝ᵥ J.mulVec x - α)) : ℂ))
      (R.residueClass g x₀) (Measure.pi (fun _ : ι ↦ μ)) := by
  apply ContinuousOn.integrableOn_compact (R.isCompact_residueClass hR g x₀)
  exact (continuous_subtypeVal.comp (hψ.comp (by fun_prop))).continuousOn

/-- The class Gauss integral is jointly continuous in its norm and frequency. -/
theorem continuous_classGaussSum (hR : IsCompact (R : Set A)) (hψ : Continuous ψ) :
    Continuous fun p : A × A ↦ classGaussSum R μ ψ τ J g x₀ p.1 p.2 := by
  have hK := R.isCompact_residueClass hR g x₀
  let ν := (Measure.pi (fun _ : ι ↦ μ)).restrict (R.residueClass g x₀)
  have : IsFiniteMeasure ν := ⟨by simpa [ν] using hK.measure_lt_top⟩
  apply continuous_of_dominated (μ := ν) (bound := fun _ ↦ (1 : ℝ))
  · intro p
    exact (integrableOn_addChar_quadratic_residueClass R μ ψ τ J g x₀ p.1 p.2 hR
      hψ).aestronglyMeasurable
  · intro p
    exact Filter.Eventually.of_forall fun x ↦ (Circle.norm_coe _).le
  · exact integrable_const _
  · exact Filter.Eventually.of_forall fun x ↦
      continuous_subtypeVal.comp (hψ.comp (by fun_prop))

end Topology

section Haar

variable [TopologicalSpace A] [IsTopologicalRing A] [LocallyCompactSpace A]
  [BorelSpace A] [SigmaFinite μ] [μ.IsAddHaarMeasure] [μ.Regular]

/-- For normalized Haar measure, the zero-frequency value is `Δ(g)^|ι|`. -/
theorem classGaussSum_zero_frequency_of_measure_eq_one (hμ : μ R = 1) :
    classGaussSum R μ ψ τ J g x₀ α 0 =
      ((distribHaarChar A g : ℝ) ^ Fintype.card ι : ℂ) := by
  rw [classGaussSum_zero_frequency, Measure.real,
    R.measure_residueClass_of_measure_eq_one μ hμ]
  simp

/-- For normalized Haar measure, the absolute value is bounded by `Δ(g)^|ι|`. -/
theorem norm_classGaussSum_le_of_measure_eq_one (hμ : μ R = 1) :
    ‖classGaussSum R μ ψ τ J g x₀ α b‖ ≤
      (distribHaarChar A g : ℝ) ^ Fintype.card ι := by
  simpa [Measure.real, R.measure_residueClass_of_measure_eq_one μ hμ] using
    norm_classGaussSum_le R μ ψ τ J g x₀ α b

end Haar

end Subring
