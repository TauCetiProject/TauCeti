/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.ScalarSum
public import TauCeti.NumberTheory.NumberField.SUnits.ExponentHeight
public import Mathlib.Analysis.Normed.Module.Seminorm.Norm

/-!
# The scalar-height norm in logarithmic coordinates

The scalar height of an `S`-unit extends to a real norm on its logarithmic space.
The omitted infinite coordinate is recovered as the negative sum of the retained
coordinates. Consequently the norm is the sum of their absolute values, including
the omitted coordinate, divided by twice the degree of the number field.

For tuples, summing these norms gives exactly `TauCeti.scalarSumHeight` on the
logarithmic image. Pulling back along the logarithms of generators gives a seminorm
on real exponent vectors. Independence modulo torsion makes it a norm: discreteness
of the `S`-unit lattice upgrades integer independence to real independence.
This supplies the arithmetic norm used in packing arguments for multiplicative groups.

## References

* J.-H. Evertse, H. P. Schlickewei and W. M. Schmidt, *Linear equations in variables
  which lie in a multiplicative group*, Annals of Mathematics 155 (2002), §7.
-/

public noncomputable section

open Finset Height IsDedekindDomain Module NumberField
open scoped NNReal

namespace TauCeti.NumberField.SUnit

variable {K : Type*} [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The absolute scalar-height norm on the `S`-logarithmic space, bundled as a
seminorm. It is positive definite by `logHeightSeminorm_eq_zero_iff`. -/
def logHeightSeminorm : Seminorm ℝ (logSpace S) := by
  classical
  exact ((2 * finrank ℚ K : ℝ≥0)⁻¹) •
    ((∑ i, (normSeminorm ℝ ℝ).comp (LinearMap.proj i)) +
      (normSeminorm ℝ ℝ).comp (∑ i, LinearMap.proj i))

open Classical in
/-- The norm includes the absolute value of the omitted logarithmic coordinate. -/
theorem logHeightSeminorm_apply (v : logSpace S) :
    logHeightSeminorm S v = (∑ i, |v i| + |∑ i, v i|) / (2 * finrank ℚ K) := by
  classical
  simp [logHeightSeminorm, Real.norm_eq_abs, div_eq_mul_inv, mul_comm,
    NNReal.smul_def, smul_eq_mul, mul_add]

/-- The scalar-height seminorm on logarithmic space is positive definite. -/
@[simp]
theorem logHeightSeminorm_eq_zero_iff (v : logSpace S) :
    logHeightSeminorm S v = 0 ↔ v = 0 := by
  classical
  rw [logHeightSeminorm_apply, div_eq_zero_iff]
  have hd : (2 * finrank ℚ K : ℝ) ≠ 0 :=
    mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr finrank_pos.ne')
  simp only [hd, or_false]
  constructor
  · intro h
    have hs : ∑ i, |v i| = 0 := by
      have := abs_nonneg (∑ i, v i)
      have := sum_nonneg (fun i (_ : i ∈ univ) ↦ abs_nonneg (v i))
      linarith
    have hcoord := (sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ univ) ↦ abs_nonneg (v i))).mp hs
    ext i
    exact abs_eq_zero.mp (hcoord i (mem_univ i))
  · rintro rfl
    simp

/-- The logarithmic embedding has norm equal to the absolute scalar height. -/
@[simp]
theorem logHeightSeminorm_logEmbedding
    (x : (S : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    logHeightSeminorm S (logEmbedding S (Additive.ofMul x)) =
      absLogHeight₁ ((x : Kˣ) : K) := by
  rw [logHeightSeminorm_apply, ← two_mul_logHeight₁_eq_sum_abs_logEmbedding,
    absLogHeight₁_eq_div]
  ring

/-- The sum of the scalar-height norms on a finite tuple of logarithmic spaces. -/
def scalarSumHeightSeminorm : Seminorm ℝ (κ → logSpace S) := by
  classical
  exact ∑ k, (logHeightSeminorm S).comp (LinearMap.proj k)

/-- The tuple norm is the sum of the coordinate norms. -/
theorem scalarSumHeightSeminorm_apply (v : κ → logSpace S) :
    scalarSumHeightSeminorm S v = ∑ k, logHeightSeminorm S (v k) := by
  classical
  simp [scalarSumHeightSeminorm]

/-- The tuple scalar-height seminorm is positive definite. -/
@[simp]
theorem scalarSumHeightSeminorm_eq_zero_iff (v : κ → logSpace S) :
    scalarSumHeightSeminorm S v = 0 ↔ v = 0 := by
  classical
  simp [scalarSumHeightSeminorm_apply,
    sum_eq_zero_iff_of_nonneg (fun k (_ : k ∈ univ) ↦ apply_nonneg (logHeightSeminorm S) (v k)),
    funext_iff]

/-- The logarithmic image of a tuple has norm equal to its scalar-sum height. -/
@[simp]
theorem scalarSumHeightSeminorm_logEmbedding
    (x : κ → (S : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    scalarSumHeightSeminorm S (fun k ↦ logEmbedding S (Additive.ofMul (x k))) =
      TauCeti.scalarSumHeight (fun k ↦ ((x k : Kˣ) : K)) := by
  simp [scalarSumHeightSeminorm_apply, TauCeti.scalarSumHeight_def]

/-- The scalar-height seminorm on real exponents of a family of tuples of `S`-units.
It is a norm when the generators are independent modulo torsion. -/
def exponentHeightSeminorm
    (γ : ι → κ → (S : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    Seminorm ℝ (ι → ℝ) :=
  (scalarSumHeightSeminorm S).comp
    (Fintype.linearCombination ℝ (fun j k ↦ logEmbedding S (Additive.ofMul (γ j k))))

/-- Real exponent vectors are sent to linear combinations of the generator logarithms. -/
theorem exponentHeightSeminorm_apply
    (γ : ι → κ → (S : Set (HeightOneSpectrum (𝓞 K))).unit K) (u : ι → ℝ) :
    exponentHeightSeminorm S γ u = scalarSumHeightSeminorm S
      (∑ j, u j • (fun k ↦ logEmbedding S (Additive.ofMul (γ j k)))) := by
  simp [exponentHeightSeminorm, Fintype.linearCombination_apply]

/-- The exponent seminorm is positive definite for generators independent modulo torsion.
This includes rank zero. -/
@[simp]
theorem exponentHeightSeminorm_eq_zero_iff
    {γ : ι → κ → (S : Set (HeightOneSpectrum (𝓞 K))).unit K}
    (hγ : ∀ z : ι → ℤ,
      (∀ k, ∏ j, γ j k ^ z j ∈
        CommGroup.torsion ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) → z = 0)
    (u : ι → ℝ) : exponentHeightSeminorm S γ u = 0 ↔ u = 0 := by
  rw [exponentHeightSeminorm_apply, scalarSumHeightSeminorm_eq_zero_iff]
  constructor
  · intro h
    exact funext (Fintype.linearIndependent_iff.mp (linearIndependent_logEmbedding_pi S hγ) u h)
  · rintro rfl
    simp

/-- On integer exponents the real seminorm is exactly the scalar-sum height.
Multiplication by an arbitrary tuple of torsion elements does not change it. -/
theorem exponentHeightSeminorm_intCast
    (γ : ι → κ → (S : Set (HeightOneSpectrum (𝓞 K))).unit K)
    (ζ : κ → (S : Set (HeightOneSpectrum (𝓞 K))).unit K)
    (hζ : ∀ k, ζ k ∈ CommGroup.torsion ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
    (z : ι → ℤ) :
    exponentHeightSeminorm S γ (fun j ↦ (z j : ℝ)) =
      TauCeti.scalarSumHeight (fun k ↦ (((ζ k * ∏ j, γ j k ^ z j : _) : Kˣ) : K)) := by
  rw [exponentHeightSeminorm_apply]
  have hlog : (∑ j, (z j : ℝ) • (fun k ↦ logEmbedding S (Additive.ofMul (γ j k)))) =
      (fun k ↦ logEmbedding S (Additive.ofMul (ζ k * ∏ j, γ j k ^ z j))) := by
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply, Int.cast_smul_eq_zsmul]
    exact (logEmbedding_mul_prod_zpow (hζ k) z).symm
  rw [hlog, scalarSumHeightSeminorm_logEmbedding]

end TauCeti.NumberField.SUnit
