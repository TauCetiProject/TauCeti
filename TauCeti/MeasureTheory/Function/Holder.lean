/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Holder

/-!
# Integrability of dual pairings

Pointwise evaluation pairs dual-valued and vector-valued functions with Hölder conjugate
exponents to give an integrable scalar function. This supplies the integrability needed to
split integrals in weak integration-by-parts formulas. The result specializes Mathlib's
bilinear Hölder estimate `ContinuousLinearMap.memLp_of_bilin` to the dual pairing.

The Hölder pairing `ContinuousLinearMap.lpPairing` of the multiplication of a normed algebra is
the integral of the product (`ContinuousLinearMap.lpPairing_mul_eq_integral`).
-/

public section

open scoped ENNReal

namespace MeasureTheory.MemLp

variable {α 𝕜 V : Type*} [MeasurableSpace α] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] {μ : Measure α} {p q : ℝ≥0∞}
  [p.HolderConjugate q] {f : α → StrongDual 𝕜 V} {g : α → V}

/-- Evaluating a dual-valued `L^p` function on an `L^q` function is integrable when the
exponents are Hölder conjugate. -/
theorem integrable_apply (hf : MemLp f p μ) (hg : MemLp g q μ) :
    Integrable (fun x ↦ f x (g x)) μ :=
  memLp_one_iff_integrable.1
    ((ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 V)).memLp_of_bilin 1 hf hg)

end MeasureTheory.MemLp

namespace ContinuousLinearMap

open MeasureTheory

variable {α 𝕜 R : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing R] [NormedSpace 𝕜 R]
  [IsScalarTower 𝕜 R R] [SMulCommClass 𝕜 R R] [NormedSpace ℝ R] [SMulCommClass ℝ 𝕜 R]
  [CompleteSpace R] {mα : MeasurableSpace α} {μ : Measure α} {q q' : ℝ≥0∞} [Fact (1 ≤ q)]
  [Fact (1 ≤ q')] [q.HolderConjugate q']

/-- The Hölder pairing of the multiplication `ContinuousLinearMap.mul 𝕜 R` is the integral of the
product. -/
theorem lpPairing_mul_eq_integral (g : Lp R q μ) (f : Lp R q' μ) :
    (mul 𝕜 R).lpPairing μ q q' g f = ∫ x, g x * f x ∂μ := by
  simp [lpPairing_eq_integral]

end ContinuousLinearMap

namespace TauCeti

open MeasureTheory

/-- **Hölder's inequality** for the Bochner integral of a scalar multiple. -/
theorem enorm_integral_smul_le {α 𝕜 F : Type*} [MeasurableSpace α]
    [NormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F]
    {μ : Measure α} {p q : ℝ≥0∞} [p.HolderConjugate q] {a : α → 𝕜} {f : α → F} :
    ‖∫ x, a x • f x ∂μ‖ₑ ≤ eLpNorm a p μ * eLpNorm f q μ := by
  calc ‖∫ x, a x • f x ∂μ‖ₑ ≤ eLpNorm (fun x => a x • f x) 1 μ :=
      (enorm_integral_le_lintegral_enorm _).trans lintegral_enorm_le_eLpNorm_one
    _ ≤ eLpNorm a p μ * eLpNorm f q μ := eLpNorm_smul_le_mul_eLpNorm_of_pos zero_lt_one

end TauCeti
