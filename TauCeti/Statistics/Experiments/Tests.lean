/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Randomized tests and their power

A randomized test on an observation space `X` is a measurable function `φ : X → [0, 1]`, the
probability of rejecting the null hypothesis at the observation `x`. For a family of laws
`P : Θ → Measure X`, its power function is `θ ↦ ∫ φ dP θ`. A test has level `α` on the null
hypothesis `H₀` when its power is at most `α` at every `θ ∈ H₀`; this is stated pointwise, so no
supremum over a possibly empty `H₀` is taken. A test is similar of size `α` on `B` when its power
is `α` on `B`. Uniformly most powerful tests maximize the power on the alternative `H₁` among all
level-`α` tests; uniformly most powerful unbiased tests do so among the unbiased level-`α` tests,
those with power at least `α` on `H₁`.

The one-sided threshold test rejects when a statistic exceeds a constant, and the two-sided
interval test rejects inside an interval, both with randomization at the endpoints.

## Main definitions

* `TauCeti.IsStatisticalTest φ`: `φ` is a measurable `[0, 1]`-valued function.
* `TauCeti.testPower P φ θ`: the power `∫ φ dP θ`.
* `TauCeti.HasTestLevel P H₀ α φ`: `φ` is a test of level `α` on `H₀`.
* `TauCeti.IsSimilarTest P B α φ`: `φ` is a test of power `α` at every `θ ∈ B`.
* `TauCeti.IsUniformlyMostPowerfulTest P H₀ H₁ α φ`,
  `TauCeti.IsUniformlyMostPowerfulUnbiasedTest P H₀ H₁ α φ`: optimal tests.
* `TauCeti.thresholdTest T c γ`, `TauCeti.intervalTest t c₁ c₂ γ₁ γ₂`: the one-sided and the
  two-sided randomized tests.

## Main results

* `TauCeti.IsStatisticalTest.const`, `TauCeti.IsStatisticalTest.one_sub`: constants in `[0, 1]`
  and complements of tests are tests.
* `TauCeti.IsStatisticalTest.integrable`, `TauCeti.IsStatisticalTest.integrable_mul`: a test is
  integrable for every finite measure, as is its product with an integrable function.
* `TauCeti.IsStatisticalTest.integral_mem_Icc`: the integral of a test under a probability
  measure lies in `[0, 1]`.
* `TauCeti.IsUniformlyMostPowerfulTest.hasTestLevel`,
  `TauCeti.IsUniformlyMostPowerfulUnbiasedTest.hasTestLevel`: optimal tests have the level.
* `TauCeti.isStatisticalTest_thresholdTest`, `TauCeti.isStatisticalTest_intervalTest`: threshold
  and interval tests in measurable statistics are tests.

## References

* M. J. Schervish, *Theory of Statistics*, Springer (1995), Definitions 4.4, 4.34 and 4.91.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti

variable {Θ X : Type*} [MeasurableSpace X]

/-- A **randomized test**: a measurable function `φ : X → [0, 1]`, the probability of rejecting
the null hypothesis at each observation. -/
@[expose]
def IsStatisticalTest (φ : X → ℝ) : Prop :=
  Measurable φ ∧ ∀ x, φ x ∈ Icc 0 1

/-- The **power function** `θ ↦ ∫ φ dP θ` of a test `φ` in the family `P`. -/
@[expose]
def testPower (P : Θ → Measure X) (φ : X → ℝ) (θ : Θ) : ℝ := ∫ x, φ x ∂P θ

theorem testPower_def (P : Θ → Measure X) (φ : X → ℝ) (θ : Θ) :
    testPower P φ θ = ∫ x, φ x ∂P θ := (rfl)

/-- `φ` is a test of **level** `α` for the null hypothesis `H₀`: its power is at most `α` at every
`θ ∈ H₀`. This is stated pointwise, so that no supremum over a possibly empty `H₀` is taken. -/
@[expose]
def HasTestLevel (P : Θ → Measure X) (H₀ : Set Θ) (α : ℝ) (φ : X → ℝ) : Prop :=
  IsStatisticalTest φ ∧ ∀ θ ∈ H₀, testPower P φ θ ≤ α

/-- `φ` is a test **similar** of size `α` on `B`: its power is `α` at every `θ ∈ B`. -/
@[expose]
def IsSimilarTest (P : Θ → Measure X) (B : Set Θ) (α : ℝ) (φ : X → ℝ) : Prop :=
  IsStatisticalTest φ ∧ ∀ θ ∈ B, testPower P φ θ = α

/-- `φ` is a **uniformly most powerful** test of level `α` for `H₀` against `H₁`: it has level `α`
and at every `θ ∈ H₁` its power is at least that of every test of level `α`. -/
@[expose]
def IsUniformlyMostPowerfulTest (P : Θ → Measure X) (H₀ H₁ : Set Θ) (α : ℝ) (φ : X → ℝ) :
    Prop :=
  HasTestLevel P H₀ α φ ∧ ∀ ψ, HasTestLevel P H₀ α ψ → ∀ θ ∈ H₁, testPower P ψ θ ≤ testPower P φ θ

/-- `φ` is a **uniformly most powerful unbiased** test of level `α` for `H₀` against `H₁`: it has
level `α`, power at least `α` on `H₁`, and at every `θ ∈ H₁` power at least that of every test of
level `α` with power at least `α` on `H₁`. -/
@[expose]
def IsUniformlyMostPowerfulUnbiasedTest (P : Θ → Measure X) (H₀ H₁ : Set Θ) (α : ℝ)
    (φ : X → ℝ) : Prop :=
  HasTestLevel P H₀ α φ ∧ (∀ θ ∈ H₁, α ≤ testPower P φ θ) ∧
    ∀ ψ, HasTestLevel P H₀ α ψ → (∀ θ ∈ H₁, α ≤ testPower P ψ θ) →
      ∀ θ ∈ H₁, testPower P ψ θ ≤ testPower P φ θ

namespace IsStatisticalTest

variable {φ : X → ℝ}

theorem measurable (hφ : IsStatisticalTest φ) : Measurable φ := hφ.1

theorem nonneg (hφ : IsStatisticalTest φ) (x : X) : 0 ≤ φ x := (hφ.2 x).1

theorem le_one (hφ : IsStatisticalTest φ) (x : X) : φ x ≤ 1 := (hφ.2 x).2

theorem abs_le_one (hφ : IsStatisticalTest φ) (x : X) : |φ x| ≤ 1 :=
  abs_le.2 ⟨by linarith [hφ.nonneg x], hφ.le_one x⟩

/-- A constant in `[0, 1]` is a test. -/
theorem const {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) : IsStatisticalTest fun _ : X ↦ c :=
  ⟨measurable_const, fun _ ↦ hc⟩

/-- The complement `1 - φ` of a test is a test. -/
theorem one_sub (hφ : IsStatisticalTest φ) : IsStatisticalTest fun x ↦ 1 - φ x :=
  ⟨measurable_const.sub hφ.1, fun x ↦ ⟨by linarith [hφ.le_one x], by linarith [hφ.nonneg x]⟩⟩

/-- A test is integrable for every finite measure. -/
theorem integrable (hφ : IsStatisticalTest φ) (μ : Measure X) [IsFiniteMeasure μ] :
    Integrable φ μ :=
  Integrable.of_bound hφ.1.aestronglyMeasurable 1 (ae_of_all _ hφ.abs_le_one)

/-- The product of a test with an integrable function is integrable. -/
theorem integrable_mul (hφ : IsStatisticalTest φ) {μ : Measure X} {f : X → ℝ}
    (hf : Integrable f μ) : Integrable (fun x ↦ φ x * f x) μ :=
  hf.bdd_mul hφ.1.aestronglyMeasurable (ae_of_all _ hφ.abs_le_one)

/-- The integral of a test under a probability measure, or the zero measure, lies in `[0, 1]`. -/
theorem integral_mem_Icc (hφ : IsStatisticalTest φ) (μ : Measure X)
    [IsZeroOrProbabilityMeasure μ] : ∫ x, φ x ∂μ ∈ Icc (0 : ℝ) 1 :=
  ⟨integral_nonneg hφ.nonneg, (integral_mono (hφ.integrable μ) (integrable_const 1)
    hφ.le_one).trans (by simp)⟩

/-- The integral of the complementary test `1 - φ` under a probability measure. -/
theorem integral_one_sub (hφ : IsStatisticalTest φ) (μ : Measure X) [IsProbabilityMeasure μ] :
    ∫ x, (1 - φ x) ∂μ = 1 - ∫ x, φ x ∂μ := by
  rw [integral_sub (integrable_const 1) (hφ.integrable μ)]
  simp

end IsStatisticalTest

/-- A uniformly most powerful test of level `α` has level `α`. -/
theorem IsUniformlyMostPowerfulTest.hasTestLevel {P : Θ → Measure X} {H₀ H₁ : Set Θ} {α : ℝ}
    {φ : X → ℝ} (h : IsUniformlyMostPowerfulTest P H₀ H₁ α φ) : HasTestLevel P H₀ α φ :=
  h.1

/-- A uniformly most powerful unbiased test of level `α` has level `α`. -/
theorem IsUniformlyMostPowerfulUnbiasedTest.hasTestLevel {P : Θ → Measure X} {H₀ H₁ : Set Θ}
    {α : ℝ} {φ : X → ℝ} (h : IsUniformlyMostPowerfulUnbiasedTest P H₀ H₁ α φ) :
    HasTestLevel P H₀ α φ :=
  h.1

/-- A test similar of size `α` on `B` has level `α` for the null hypothesis `B`. -/
theorem IsSimilarTest.hasTestLevel {P : Θ → Measure X} {B : Set Θ} {α : ℝ} {φ : X → ℝ}
    (h : IsSimilarTest P B α φ) : HasTestLevel P B α φ :=
  ⟨h.1, fun θ hθ ↦ (h.2 θ hθ).le⟩

/-- A constant test `c ∈ [0, 1]` is similar of size `c` on every set `B` of parameters whose
laws are probability measures. -/
theorem isSimilarTest_const {P : Θ → Measure X} {B : Set Θ}
    (hP : ∀ θ ∈ B, IsProbabilityMeasure (P θ)) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    IsSimilarTest P B c fun _ ↦ c := by
  refine ⟨IsStatisticalTest.const hc, fun θ hθ ↦ ?_⟩
  have := hP θ hθ
  simp [testPower]

section ThresholdTest

variable {α : Type*} [LinearOrder α]

/-- The one-sided **threshold test** in a statistic `T`: reject when `c < T x`, reject with
probability `γ` when `T x = c`, and accept otherwise. -/
def thresholdTest (T : X → α) (c : α) (γ : ℝ) (x : X) : ℝ :=
  if c < T x then 1 else if T x = c then γ else 0

omit [MeasurableSpace X] in
theorem thresholdTest_apply (T : X → α) (c : α) (γ : ℝ) (x : X) :
    thresholdTest T c γ x = if c < T x then 1 else if T x = c then γ else 0 := (rfl)

/-- A threshold test in a measurable statistic, with randomization `γ ∈ [0, 1]`, is a test. -/
theorem isStatisticalTest_thresholdTest [TopologicalSpace α] [OrderClosedTopology α]
    [MeasurableSpace α] [OpensMeasurableSpace α] {T : X → α} (hT : Measurable T) (c : α)
    {γ : ℝ} (hγ : γ ∈ Icc (0 : ℝ) 1) : IsStatisticalTest (thresholdTest T c γ) := by
  refine ⟨?_, fun x ↦ ?_⟩
  · simp_rw [funext (thresholdTest_apply T c γ)]
    exact Measurable.ite (hT measurableSet_Ioi) measurable_const
      (Measurable.ite (hT (measurableSet_singleton c)) measurable_const measurable_const)
  · rw [thresholdTest_apply]
    split_ifs
    exacts [⟨zero_le_one, le_rfl⟩, hγ, ⟨le_rfl, zero_le_one⟩]

end ThresholdTest

/-- The two-sided **interval test** in a real statistic value `t`: reject when `c₁ < t < c₂`,
reject with probability `γ₁` at `t = c₁` and `γ₂` at `t = c₂`, and accept otherwise. For
`c₁ = c₂` the open interval is empty and the value at `c₁` is `γ₁`. -/
def intervalTest (t c₁ c₂ γ₁ γ₂ : ℝ) : ℝ :=
  if c₁ < t ∧ t < c₂ then 1 else if t = c₁ then γ₁ else if t = c₂ then γ₂ else 0

theorem intervalTest_def (t c₁ c₂ γ₁ γ₂ : ℝ) : intervalTest t c₁ c₂ γ₁ γ₂ =
    if c₁ < t ∧ t < c₂ then 1 else if t = c₁ then γ₁ else if t = c₂ then γ₂ else 0 := (rfl)

/-- An interval test in a measurable real statistic, with randomizations in `[0, 1]`, is a
test. -/
theorem isStatisticalTest_intervalTest {T : X → ℝ} (hT : Measurable T) (c₁ c₂ : ℝ)
    {γ₁ γ₂ : ℝ} (hγ₁ : γ₁ ∈ Icc (0 : ℝ) 1) (hγ₂ : γ₂ ∈ Icc (0 : ℝ) 1) :
    IsStatisticalTest fun x ↦ intervalTest (T x) c₁ c₂ γ₁ γ₂ := by
  refine ⟨?_, fun x ↦ ?_⟩
  · simp_rw [intervalTest_def]
    exact Measurable.ite (hT measurableSet_Ioo) measurable_const
      (Measurable.ite (hT (measurableSet_singleton c₁)) measurable_const
        (Measurable.ite (hT (measurableSet_singleton c₂)) measurable_const measurable_const))
  · simp only [intervalTest_def]
    split_ifs
    exacts [⟨zero_le_one, le_rfl⟩, hγ₁, hγ₂, ⟨le_rfl, zero_le_one⟩]

end TauCeti
