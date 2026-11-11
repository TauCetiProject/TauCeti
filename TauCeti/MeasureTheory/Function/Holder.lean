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

More generally, an essentially bounded field of continuous bilinear maps applied to an `Lᵖ`
function and an `Lᵠ` function is integrable (`MeasureTheory.MemLp.integrable_bilinear_apply`).

The Hölder pairing `ContinuousLinearMap.lpPairing` of the multiplication of a normed algebra is
the integral of the product (`ContinuousLinearMap.lpPairing_mul_eq_integral`).
-/

public section

open scoped ENNReal

namespace MeasureTheory.MemLp

variable {α 𝕜 : Type*} [MeasurableSpace α] [NontriviallyNormedField 𝕜] {μ : Measure α}
  {p q : ℝ≥0∞} [p.HolderConjugate q]

section DualPairing

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] {f : α → StrongDual 𝕜 V}
  {g : α → V}

/-- Evaluating a dual-valued `L^p` function on an `L^q` function is integrable when the
exponents are Hölder conjugate. -/
theorem integrable_apply (hf : MemLp f p μ) (hg : MemLp g q μ) :
    Integrable (fun x ↦ f x (g x)) μ :=
  memLp_one_iff_integrable.1
    ((ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 V)).memLp_of_bilin 1 hf hg)

end DualPairing

section Bilinear

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G] {B : α → E →L[𝕜] F →L[𝕜] G}
  {f : α → E} {g : α → F}

/-- Applying an essentially bounded field of continuous bilinear maps to an `L^p` function and
an `L^q` function gives an integrable function when the exponents are Hölder conjugate. -/
theorem integrable_bilinear_apply (hB : MemLp B ⊤ μ) (hf : MemLp f p μ) (hg : MemLp g q μ) :
    Integrable (fun x ↦ B x (f x) (g x)) μ := by
  -- The Hölder exponents are pinned explicitly, and the application goes through `exact`:
  -- elaborating it against the expected type in term mode unfolds `MemLp` and loops.
  have hBf : MemLp (fun x ↦ B x (f x)) p μ := by
    exact (ContinuousLinearMap.id 𝕜 (E →L[𝕜] F →L[𝕜] G)).memLp_of_bilin (𝕜 := 𝕜)
      (p := ⊤) (q := p) (f := B) (g := f) p hB hf
  exact memLp_one_iff_integrable.mp
    ((ContinuousLinearMap.id 𝕜 (F →L[𝕜] G)).memLp_of_bilin
      (p := p) (q := q) (f := fun x ↦ B x (f x)) (g := g) 1 hBf hg)

end Bilinear

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
