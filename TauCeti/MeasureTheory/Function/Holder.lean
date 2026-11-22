/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Function.Holder
public import TauCeti.MeasureTheory.Function.Lp.One
import Mathlib.Analysis.InnerProductSpace.Continuous

import Mathlib.MeasureTheory.Integral.IntegrableOn

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
* `MeasureTheory.MemLp.integrable_inner_of_holderConjugate`: Hölder's inequality makes the
  pointwise inner product `⟪h, g⟫` of `h ∈ L^q` and `g ∈ L^{q'}` integrable.
* `ContinuousLinearMap.lpPairing_mul_eq_integral`: the Hölder pairing
  `ContinuousLinearMap.lpPairing` of the multiplication of a complete normed algebra is the
  integral of the product.
* `ContinuousLinearMap.integrable_of_bilin_of_continuousOn`: a continuous bilinear pairing of an
  integrable function vanishing off a compact set `K` with a function continuous on `K` is
  integrable.
* `ContinuousLinearMap.norm_lpPairing_apply_apply_le`: Hölder's inequality
  `‖B.lpPairing μ p q g f‖ ≤ ‖B‖ * ‖g‖ * ‖f‖` for the integral pairing of a bilinear map `B`.
* `TauCeti.enorm_integral_smul_le`: Hölder's inequality `‖∫ a • f‖ ≤ ‖a‖_p ‖f‖_q` for the
  Bochner integral of a pointwise scalar multiple, for any boundedly acting scalars.
* `MeasureTheory.Lp.sum_smul` and `MeasureTheory.Lp.smul_sum`: the heterogeneous scalar
  multiplication `Lᵖ × L^q → Lʳ` distributes over finite sums in each factor.
* `MeasureTheory.MemLp.toLp_smul_toLp`: the product of the classes of `f` and `g` is the class of
  `f • g`; `MeasureTheory.Lp.one_smul`: the constant one of `L^∞` acts trivially.
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

namespace MeasureTheory

open scoped InnerProductSpace

variable {α 𝕜 H : Type*} [MeasurableSpace α] [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] {μ : Measure α}

/-- Hölder's inequality makes the pairing `x ↦ ⟪h x, g x⟫` integrable for `h ∈ L^q` and
`g ∈ L^{q'}`. For `q = q' = 2` this is `MeasureTheory.MemLp.integrable_inner`. -/
theorem MemLp.integrable_inner_of_holderConjugate {q q' : ℝ≥0∞} [q.HolderConjugate q']
    {h g : α → H} (hh : MemLp h q μ) (hg : MemLp g q' μ) :
    Integrable (fun x => ⟪h x, g x⟫_𝕜) μ :=
  memLp_one_iff_integrable.1 <| hh.of_bilin (fun a b => ⟪a, b⟫_𝕜) 1 hg continuous_inner
    (ae_of_all _ fun x => by simpa [← NNReal.coe_le_coe] using norm_inner_le_norm (h x) (g x))

end MeasureTheory

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

namespace ContinuousLinearMap

open MeasureTheory

variable {α 𝕜 E F G : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
  [T2Space α] [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G] {μ : Measure α}

/-- A continuous bilinear pairing of an integrable function vanishing off a compact set `K` with a
function continuous on `K` is integrable. -/
theorem integrable_of_bilin_of_continuousOn (B : E →L[𝕜] F →L[𝕜] G) {f : α → E}
    (hf : Integrable f μ) {K : Set α} (hK : IsCompact K) (hfK : ∀ x ∉ K, f x = 0) {g : α → F}
    (hg : ContinuousOn g K) : Integrable (fun x => B (f x) (g x)) μ := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg
  have heq : (fun x => B (f x) (g x)) = fun x => B (f x) (K.indicator g x) := by
    funext x
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx]
    · simp [hfK x hx]
  rw [heq]
  refine B.integrable_of_bilin_of_bdd_right (max C 0) hf
    ((aestronglyMeasurable_indicator_iff hK.measurableSet).2
      (hg.aestronglyMeasurable_of_isCompact hK hK.measurableSet))
    (.of_forall fun x => ?_)
  by_cases hx : x ∈ K
  · rw [Set.indicator_of_mem hx]
    exact (hC x hx).trans (le_max_left _ _)
  · rw [Set.indicator_of_notMem hx, norm_zero]
    exact le_max_right _ _

end ContinuousLinearMap

namespace ContinuousLinearMap

open MeasureTheory

variable {α 𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [NormedSpace ℝ G] [SMulCommClass ℝ 𝕜 G] [CompleteSpace G] {mα : MeasurableSpace α}
  {μ : Measure α} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- **Hölder's inequality** for the integral pairing `lpPairing` of a bilinear map `B`. -/
theorem norm_lpPairing_apply_apply_le (B : E →L[𝕜] F →L[𝕜] G) (g : Lp E p μ) (f : Lp F q μ) :
    ‖B.lpPairing μ p q g f‖ ≤ ‖B‖ * ‖g‖ * ‖f‖ := by
  have h : B.lpPairing μ p q g f = L1.integral (B.holder 1 g f) := by
    simp [lpPairing, L1.integral_eq' 𝕜]
  rw [h]
  exact (L1.norm_integral_le _).trans (B.norm_holder_apply_apply_le _ _)

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

/-- The heterogeneous product of the `Lp` classes of `f` and `g` is the class of the pointwise
product `f • g`. -/
theorem _root_.MeasureTheory.MemLp.toLp_smul_toLp {f : α → 𝕜} {g : α → E} (hf : MemLp f p μ)
    (hg : MemLp g q μ) : (hf.toLp f • hg.toLp g : Lp E r μ) = (hf.smul hg).toLp (f • g) :=
  MemLp.toLp_congr _ _ <| by
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h₁ h₂
    rw [Pi.smul_apply', h₁, h₂, Pi.smul_apply']

omit [p.HolderTriple q r] in
/-- The constant one of `L^∞` acts trivially on every `L^q` function. -/
@[simp]
protected theorem one_smul (g : Lp E q μ) : ((1 : Lp 𝕜 ∞ μ) • g : Lp E q μ) = g := by
  conv_lhs => rw [one_def, ← Lp.toLp_coeFn g (Lp.memLp g), MemLp.toLp_smul_toLp]
  conv_rhs => rw [← Lp.toLp_coeFn g (Lp.memLp g)]
  exact MemLp.toLp_congr _ _ (.of_forall fun x ↦ by simp)

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
