/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Holder

/-!
# Hölder estimates for pointwise pairings

Consequences of Mathlib's Hölder estimates for the pairings used in duality and weak
integration-by-parts arguments:

* `MeasureTheory.MemLp.integrable_apply`: evaluating an `L^p` function with values in continuous
  linear maps `V →L[𝕜] W` on a `V`-valued `L^q` function, for Hölder conjugate exponents, gives
  an integrable function. This supplies the integrability needed to split integrals in weak
  integration-by-parts formulas. It specializes Mathlib's bilinear Hölder estimate
  `ContinuousLinearMap.memLp_of_bilin` to evaluation.
* `MeasureTheory.MemLp.integrable_bilinear_apply`: more generally, an essentially bounded field of
  continuous bilinear maps applied to an `L^p` function and an `L^q` function is integrable.
* `ContinuousLinearMap.lpPairing_mul_eq_integral`: the Hölder pairing
  `ContinuousLinearMap.lpPairing` of the multiplication of a complete normed algebra is the
  integral of the product.
* `TauCeti.enorm_integral_smul_le`: Hölder's inequality `‖∫ a • f‖ ≤ ‖a‖_p ‖f‖_q` for the
  Bochner integral of a pointwise scalar multiple, for any boundedly acting scalars.
* `MeasureTheory.Lp.sum_smul` and `MeasureTheory.Lp.smul_sum`: the heterogeneous scalar
  multiplication `Lᵖ × L^q → Lʳ` distributes over finite sums in each factor.
-/

public section

open scoped ENNReal

namespace MeasureTheory.MemLp

variable {α 𝕜 : Type*} [MeasurableSpace α] [NontriviallyNormedField 𝕜] {μ : Measure α}
  {p q : ℝ≥0∞} [p.HolderConjugate q]

section Evaluation

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W]
  [NormedSpace 𝕜 W] {f : α → V →L[𝕜] W} {g : α → V}

/-- Evaluating an `L^p` function with values in continuous linear maps on an `L^q` function is
integrable when the exponents are Hölder conjugate. This covers dual pairings, where
`W = 𝕜`. -/
theorem integrable_apply (hf : MemLp f p μ) (hg : MemLp g q μ) :
    Integrable (fun x ↦ f x (g x)) μ :=
  memLp_one_iff_integrable.1
    ((ContinuousLinearMap.id 𝕜 (V →L[𝕜] W)).memLp_of_bilin 1 hf hg)

end Evaluation

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
  -- The partial application `x ↦ B x (f x)` is an `L^p` field of linear maps `F →L[𝕜] G`.
  exact hBf.integrable_apply hg

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

namespace MeasureTheory.Lp

variable {α ι 𝕜 E : Type*} {mα : MeasurableSpace α} {μ : Measure α} {p q r : ℝ≥0∞}
  [p.HolderTriple q r] [NormedRing 𝕜] [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- The heterogeneous scalar multiplication of `Lp` functions distributes over finite sums in the
scalar factor. -/
protected theorem sum_smul (s : Finset ι) (f : ι → Lp 𝕜 p μ) (g : Lp E q μ) :
    (∑ i ∈ s, f i) • g = ∑ i ∈ s, (f i • g : Lp E r μ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, Lp.smul_add, ih]

/-- The heterogeneous scalar multiplication of `Lp` functions distributes over finite sums in the
vector factor. -/
protected theorem smul_sum (s : Finset ι) (f : Lp 𝕜 p μ) (g : ι → Lp E q μ) :
    f • (∑ i ∈ s, g i) = ∑ i ∈ s, (f • g i : Lp E r μ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, Lp.add_smul, ih]

end MeasureTheory.Lp

namespace TauCeti

open MeasureTheory

/-- **Hölder's inequality** for the Bochner integral of a pointwise scalar multiple:
`‖∫ a • f‖ ≤ ‖a‖_p ‖f‖_q` for Hölder conjugate exponents `p` and `q`. The scalars only need to
act boundedly, as a normed field does on a normed space and a normed ring does on itself. -/
theorem enorm_integral_smul_le {α 𝕜 F : Type*} [MeasurableSpace α]
    [NormedAddGroup 𝕜] [NormedAddCommGroup F] [SMulZeroClass 𝕜 F] [IsBoundedSMul 𝕜 F]
    [NormedSpace ℝ F] {μ : Measure α} {p q : ℝ≥0∞} [p.HolderConjugate q] {a : α → 𝕜}
    {f : α → F} :
    ‖∫ x, a x • f x ∂μ‖ₑ ≤ eLpNorm a p μ * eLpNorm f q μ := by
  calc ‖∫ x, a x • f x ∂μ‖ₑ ≤ eLpNorm (fun x => a x • f x) 1 μ :=
      (eNorm_integral_le_lintegral_eNorm _).trans lintegral_eNorm_le_eLpNorm_one
    _ ≤ eLpNorm a p μ * eLpNorm f q μ := by
      simpa using eLpNorm_le_eLpNorm_mul_eLpNorm_of_eNorm_of_pos (· • ·) 1
        continuous_smul.comp_aestronglyMeasurable₂
        (.of_forall fun _ => by simpa using eNorm_smul_le) zero_lt_one

end TauCeti
