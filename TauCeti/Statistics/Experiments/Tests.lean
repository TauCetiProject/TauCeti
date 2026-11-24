/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Set

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

The predicates are not exposed: each has a characteristic lemma (`isStatisticalTest_iff`,
`hasTestLevel_iff`, ...), a constructor `mk` and accessors such as `HasTestLevel.testPower_le`,
`IsSimilarTest.testPower_eq` and `IsUniformlyMostPowerfulUnbiasedTest.le_testPower`. The
threshold and interval tests are evaluated by `simp` lemmas such as `thresholdTest_of_lt` and
`intervalTest_left`.

## Main results

* `TauCeti.IsStatisticalTest.const`, `TauCeti.IsStatisticalTest.one_sub`: constants in `[0, 1]`
  and complements of tests are tests.
* `TauCeti.IsStatisticalTest.integrable`, `TauCeti.IsStatisticalTest.integrable_mul`: a test is
  integrable for every finite measure, as is its product with an integrable function.
* `TauCeti.IsStatisticalTest.integral_mem_Icc`: the integral of a test under a probability
  measure lies in `[0, 1]`.
* `TauCeti.isStatisticalTest_indicator_one_iff`, `TauCeti.testPower_indicator_one`: the
  nonrandomized test rejecting on `s` is a test iff `s` is measurable, and its power at `θ` is
  the probability of `s` under `P θ`.
* `TauCeti.IsUniformlyMostPowerfulTest.hasTestLevel`,
  `TauCeti.IsUniformlyMostPowerfulUnbiasedTest.hasTestLevel`: optimal tests have the level.
* `TauCeti.IsSimilarTest.hasTestLevel`, `TauCeti.isSimilarTest_const`: a similar test has the
  level, and a constant in `[0, 1]` is similar of its own size under probability laws.
* `TauCeti.isStatisticalTest_thresholdTest`, `TauCeti.isStatisticalTest_intervalTest`: threshold
  and interval tests in measurable statistics are tests.

## References

* M. J. Schervish, *Theory of Statistics*, Springer (1995), Definitions 4.4, 4.34 and 4.91.

The definitions and lemmas are adapted from the lean-CKSD project
(<https://github.com/bjbraams/lean-CKSD>), files `CKSD/Inference/Basic.lean`,
`CKSD/Inference/Model.lean` and `CKSD/Inference/Testing.lean`.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti

variable {Θ X : Type*} [MeasurableSpace X]

/-- A **randomized test**: a measurable function `φ : X → [0, 1]`, the probability of rejecting
the null hypothesis at each observation. -/
def IsStatisticalTest (φ : X → ℝ) : Prop :=
  Measurable φ ∧ ∀ x, φ x ∈ Icc 0 1

/-- The **power function** `θ ↦ ∫ φ dP θ` of a test `φ` in the family `P`. -/
def testPower (P : Θ → Measure X) (φ : X → ℝ) (θ : Θ) : ℝ := ∫ x, φ x ∂P θ

theorem testPower_def (P : Θ → Measure X) (φ : X → ℝ) (θ : Θ) :
    testPower P φ θ = ∫ x, φ x ∂P θ := (rfl)

/-- `φ` is a test of **level** `α` for the null hypothesis `H₀`: its power is at most `α` at every
`θ ∈ H₀`. This is stated pointwise, so that no supremum over a possibly empty `H₀` is taken. -/
def HasTestLevel (P : Θ → Measure X) (H₀ : Set Θ) (α : ℝ) (φ : X → ℝ) : Prop :=
  IsStatisticalTest φ ∧ ∀ θ ∈ H₀, testPower P φ θ ≤ α

/-- `φ` is a test **similar** of size `α` on `B`: its power is `α` at every `θ ∈ B`. -/
def IsSimilarTest (P : Θ → Measure X) (B : Set Θ) (α : ℝ) (φ : X → ℝ) : Prop :=
  IsStatisticalTest φ ∧ ∀ θ ∈ B, testPower P φ θ = α

/-- `φ` is a **uniformly most powerful** test of level `α` for `H₀` against `H₁`: it has level `α`
and at every `θ ∈ H₁` its power is at least that of every test of level `α`. -/
def IsUniformlyMostPowerfulTest (P : Θ → Measure X) (H₀ H₁ : Set Θ) (α : ℝ) (φ : X → ℝ) :
    Prop :=
  HasTestLevel P H₀ α φ ∧ ∀ ψ, HasTestLevel P H₀ α ψ → ∀ θ ∈ H₁, testPower P ψ θ ≤ testPower P φ θ

/-- `φ` is a **uniformly most powerful unbiased** test of level `α` for `H₀` against `H₁`: it has
level `α`, power at least `α` on `H₁`, and at every `θ ∈ H₁` power at least that of every test of
level `α` with power at least `α` on `H₁`. -/
def IsUniformlyMostPowerfulUnbiasedTest (P : Θ → Measure X) (H₀ H₁ : Set Θ) (α : ℝ)
    (φ : X → ℝ) : Prop :=
  HasTestLevel P H₀ α φ ∧ (∀ θ ∈ H₁, α ≤ testPower P φ θ) ∧
    ∀ ψ, HasTestLevel P H₀ α ψ → (∀ θ ∈ H₁, α ≤ testPower P ψ θ) →
      ∀ θ ∈ H₁, testPower P ψ θ ≤ testPower P φ θ

section API

variable {P : Θ → Measure X} {H₀ H₁ B : Set Θ} {α : ℝ} {φ ψ : X → ℝ} {θ : Θ}

theorem isStatisticalTest_iff : IsStatisticalTest φ ↔ Measurable φ ∧ ∀ x, φ x ∈ Icc 0 1 :=
  Iff.rfl

namespace IsStatisticalTest

theorem mk (hm : Measurable φ) (h : ∀ x, φ x ∈ Icc 0 1) : IsStatisticalTest φ := ⟨hm, h⟩

theorem measurable (hφ : IsStatisticalTest φ) : Measurable φ := hφ.1

theorem mem_Icc (hφ : IsStatisticalTest φ) (x : X) : φ x ∈ Icc 0 1 := hφ.2 x

theorem nonneg (hφ : IsStatisticalTest φ) (x : X) : 0 ≤ φ x := (hφ.mem_Icc x).1

theorem le_one (hφ : IsStatisticalTest φ) (x : X) : φ x ≤ 1 := (hφ.mem_Icc x).2

theorem abs_le_one (hφ : IsStatisticalTest φ) (x : X) : |φ x| ≤ 1 :=
  abs_le.2 ⟨by linarith [hφ.nonneg x], hφ.le_one x⟩

/-- A constant in `[0, 1]` is a test. -/
theorem const {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) : IsStatisticalTest fun _ : X ↦ c :=
  .mk measurable_const fun _ ↦ hc

/-- The complement `1 - φ` of a test is a test. -/
theorem one_sub (hφ : IsStatisticalTest φ) : IsStatisticalTest fun x ↦ 1 - φ x :=
  .mk (measurable_const.sub hφ.measurable) fun x ↦
    ⟨by linarith [hφ.le_one x], by linarith [hφ.nonneg x]⟩

/-- A test is integrable for every finite measure. -/
theorem integrable (hφ : IsStatisticalTest φ) (μ : Measure X) [IsFiniteMeasure μ] :
    Integrable φ μ :=
  Integrable.of_bound hφ.measurable.aestronglyMeasurable 1 (ae_of_all _ hφ.abs_le_one)

/-- The product of a test with an integrable function is integrable. -/
theorem integrable_mul (hφ : IsStatisticalTest φ) {μ : Measure X} {f : X → ℝ}
    (hf : Integrable f μ) : Integrable (fun x ↦ φ x * f x) μ :=
  hf.bdd_mul hφ.measurable.aestronglyMeasurable (ae_of_all _ hφ.abs_le_one)

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

/-- The nonrandomized test `s.indicator 1`, rejecting exactly on `s`, is a test iff its rejection
region `s` is measurable. -/
@[simp]
theorem isStatisticalTest_indicator_one_iff {s : Set X} :
    IsStatisticalTest (s.indicator (1 : X → ℝ)) ↔ MeasurableSet s := by
  rw [isStatisticalTest_iff, Pi.one_def, measurable_indicator_const_iff]
  exact and_iff_left_of_imp fun _ x ↦ ⟨indicator_nonneg (fun _ _ ↦ zero_le_one) x,
    indicator_le' (fun _ _ ↦ le_rfl) (fun _ _ ↦ zero_le_one) x⟩

/-- The power at `θ` of the nonrandomized test with measurable rejection region `s` is the
probability `(P θ).real s` of rejecting. -/
@[simp]
theorem testPower_indicator_one {s : Set X} (hs : MeasurableSet s) :
    testPower P (s.indicator 1) θ = (P θ).real s := by
  rw [testPower_def, integral_indicator_one hs]

/-! ### Tests of a given level -/

theorem hasTestLevel_iff :
    HasTestLevel P H₀ α φ ↔ IsStatisticalTest φ ∧ ∀ θ ∈ H₀, testPower P φ θ ≤ α :=
  Iff.rfl

theorem HasTestLevel.mk (hφ : IsStatisticalTest φ) (h : ∀ θ ∈ H₀, testPower P φ θ ≤ α) :
    HasTestLevel P H₀ α φ :=
  ⟨hφ, h⟩

theorem HasTestLevel.isStatisticalTest (h : HasTestLevel P H₀ α φ) : IsStatisticalTest φ :=
  h.1

theorem HasTestLevel.testPower_le (h : HasTestLevel P H₀ α φ) (hθ : θ ∈ H₀) :
    testPower P φ θ ≤ α :=
  h.2 θ hθ

/-! ### Similar tests -/

theorem isSimilarTest_iff :
    IsSimilarTest P B α φ ↔ IsStatisticalTest φ ∧ ∀ θ ∈ B, testPower P φ θ = α :=
  Iff.rfl

theorem IsSimilarTest.mk (hφ : IsStatisticalTest φ) (h : ∀ θ ∈ B, testPower P φ θ = α) :
    IsSimilarTest P B α φ :=
  ⟨hφ, h⟩

theorem IsSimilarTest.isStatisticalTest (h : IsSimilarTest P B α φ) : IsStatisticalTest φ :=
  h.1

theorem IsSimilarTest.testPower_eq (h : IsSimilarTest P B α φ) (hθ : θ ∈ B) :
    testPower P φ θ = α :=
  h.2 θ hθ

/-- A test similar of size `α` on `B` has level `α` for the null hypothesis `B`. -/
theorem IsSimilarTest.hasTestLevel (h : IsSimilarTest P B α φ) : HasTestLevel P B α φ :=
  .mk h.isStatisticalTest fun _ hθ ↦ (h.testPower_eq hθ).le

/-- A constant test `c ∈ [0, 1]` is similar of size `c` on every set `B` of parameters whose
laws are probability measures. -/
theorem isSimilarTest_const (hP : ∀ θ ∈ B, IsProbabilityMeasure (P θ)) {c : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) : IsSimilarTest P B c fun _ ↦ c :=
  .mk (.const hc) fun θ hθ ↦ by
    have := hP θ hθ
    simp [testPower_def]

/-! ### Uniformly most powerful tests -/

theorem isUniformlyMostPowerfulTest_iff : IsUniformlyMostPowerfulTest P H₀ H₁ α φ ↔
    HasTestLevel P H₀ α φ ∧
      ∀ ψ, HasTestLevel P H₀ α ψ → ∀ θ ∈ H₁, testPower P ψ θ ≤ testPower P φ θ :=
  Iff.rfl

theorem IsUniformlyMostPowerfulTest.mk (hφ : HasTestLevel P H₀ α φ)
    (h : ∀ ψ, HasTestLevel P H₀ α ψ → ∀ θ ∈ H₁, testPower P ψ θ ≤ testPower P φ θ) :
    IsUniformlyMostPowerfulTest P H₀ H₁ α φ :=
  ⟨hφ, h⟩

/-- A uniformly most powerful test of level `α` has level `α`. -/
theorem IsUniformlyMostPowerfulTest.hasTestLevel (h : IsUniformlyMostPowerfulTest P H₀ H₁ α φ) :
    HasTestLevel P H₀ α φ :=
  h.1

/-- At every alternative, a uniformly most powerful test is at least as powerful as every test
of the same level. -/
theorem IsUniformlyMostPowerfulTest.testPower_le (h : IsUniformlyMostPowerfulTest P H₀ H₁ α φ)
    (hψ : HasTestLevel P H₀ α ψ) (hθ : θ ∈ H₁) : testPower P ψ θ ≤ testPower P φ θ :=
  h.2 ψ hψ θ hθ

theorem isUniformlyMostPowerfulUnbiasedTest_iff :
    IsUniformlyMostPowerfulUnbiasedTest P H₀ H₁ α φ ↔
      HasTestLevel P H₀ α φ ∧ (∀ θ ∈ H₁, α ≤ testPower P φ θ) ∧
        ∀ ψ, HasTestLevel P H₀ α ψ → (∀ θ ∈ H₁, α ≤ testPower P ψ θ) →
          ∀ θ ∈ H₁, testPower P ψ θ ≤ testPower P φ θ :=
  Iff.rfl

theorem IsUniformlyMostPowerfulUnbiasedTest.mk (hφ : HasTestLevel P H₀ α φ)
    (hu : ∀ θ ∈ H₁, α ≤ testPower P φ θ)
    (h : ∀ ψ, HasTestLevel P H₀ α ψ → (∀ θ ∈ H₁, α ≤ testPower P ψ θ) →
      ∀ θ ∈ H₁, testPower P ψ θ ≤ testPower P φ θ) :
    IsUniformlyMostPowerfulUnbiasedTest P H₀ H₁ α φ :=
  ⟨hφ, hu, h⟩

/-- A uniformly most powerful unbiased test of level `α` has level `α`. -/
theorem IsUniformlyMostPowerfulUnbiasedTest.hasTestLevel
    (h : IsUniformlyMostPowerfulUnbiasedTest P H₀ H₁ α φ) : HasTestLevel P H₀ α φ :=
  h.1

/-- A uniformly most powerful unbiased test is unbiased: its power is at least `α` on `H₁`. -/
theorem IsUniformlyMostPowerfulUnbiasedTest.le_testPower
    (h : IsUniformlyMostPowerfulUnbiasedTest P H₀ H₁ α φ) (hθ : θ ∈ H₁) :
    α ≤ testPower P φ θ :=
  h.2.1 θ hθ

/-- At every alternative, a uniformly most powerful unbiased test is at least as powerful as
every unbiased test of the same level. -/
theorem IsUniformlyMostPowerfulUnbiasedTest.testPower_le
    (h : IsUniformlyMostPowerfulUnbiasedTest P H₀ H₁ α φ) (hψ : HasTestLevel P H₀ α ψ)
    (hψu : ∀ θ ∈ H₁, α ≤ testPower P ψ θ) (hθ : θ ∈ H₁) : testPower P ψ θ ≤ testPower P φ θ :=
  h.2.2 ψ hψ hψu θ hθ

end API

section ThresholdTest

variable {α : Type*} [LinearOrder α]

/-- The one-sided **threshold test** in a statistic `T`: reject when `c < T x`, reject with
probability `γ` when `T x = c`, and accept otherwise. -/
def thresholdTest (T : X → α) (c : α) (γ : ℝ) (x : X) : ℝ :=
  if c < T x then 1 else if T x = c then γ else 0

omit [MeasurableSpace X] in
theorem thresholdTest_apply (T : X → α) (c : α) (γ : ℝ) (x : X) :
    thresholdTest T c γ x = if c < T x then 1 else if T x = c then γ else 0 := (rfl)

omit [MeasurableSpace X] in
@[simp]
theorem thresholdTest_of_lt {T : X → α} {c : α} {x : X} (h : c < T x) (γ : ℝ) :
    thresholdTest T c γ x = 1 := by
  simp [thresholdTest_apply, h]

omit [MeasurableSpace X] in
@[simp]
theorem thresholdTest_of_eq {T : X → α} {c : α} {x : X} (h : T x = c) (γ : ℝ) :
    thresholdTest T c γ x = γ := by
  simp [thresholdTest_apply, h]

omit [MeasurableSpace X] in
@[simp]
theorem thresholdTest_of_gt {T : X → α} {c : α} {x : X} (h : T x < c) (γ : ℝ) :
    thresholdTest T c γ x = 0 := by
  simp [thresholdTest_apply, h.not_gt, h.ne]

/-- A threshold test in a measurable statistic, with randomization `γ ∈ [0, 1]`, is a test. -/
theorem isStatisticalTest_thresholdTest [TopologicalSpace α] [OrderClosedTopology α]
    [MeasurableSpace α] [OpensMeasurableSpace α] {T : X → α} (hT : Measurable T) (c : α)
    {γ : ℝ} (hγ : γ ∈ Icc (0 : ℝ) 1) : IsStatisticalTest (thresholdTest T c γ) := by
  refine .mk ?_ fun x ↦ ?_
  · simp_rw [funext (thresholdTest_apply T c γ)]
    exact Measurable.ite (hT measurableSet_Ioi) measurable_const
      (Measurable.ite (hT (measurableSet_singleton c)) measurable_const measurable_const)
  · rcases lt_trichotomy (T x) c with h | h | h <;> simp [h, hγ]

end ThresholdTest

/-- The two-sided **interval test** in a real statistic value `t`: reject when `c₁ < t < c₂`,
reject with probability `γ₁` at `t = c₁` and `γ₂` at `t = c₂`, and accept otherwise. For
`c₁ = c₂` the open interval is empty and the value at `c₁` is `γ₁`. -/
def intervalTest (t c₁ c₂ γ₁ γ₂ : ℝ) : ℝ :=
  if c₁ < t ∧ t < c₂ then 1 else if t = c₁ then γ₁ else if t = c₂ then γ₂ else 0

theorem intervalTest_def (t c₁ c₂ γ₁ γ₂ : ℝ) : intervalTest t c₁ c₂ γ₁ γ₂ =
    if c₁ < t ∧ t < c₂ then 1 else if t = c₁ then γ₁ else if t = c₂ then γ₂ else 0 := (rfl)

@[simp]
theorem intervalTest_of_mem_Ioo {t c₁ c₂ : ℝ} (h : t ∈ Ioo c₁ c₂) (γ₁ γ₂ : ℝ) :
    intervalTest t c₁ c₂ γ₁ γ₂ = 1 := by
  simp_all [intervalTest_def]

/-- At the left endpoint the interval test takes the value `γ₁`, also when `c₁ = c₂`. -/
@[simp]
theorem intervalTest_left (c₁ c₂ γ₁ γ₂ : ℝ) : intervalTest c₁ c₁ c₂ γ₁ γ₂ = γ₁ := by
  simp [intervalTest_def]

@[simp]
theorem intervalTest_right_of_ne {c₁ c₂ : ℝ} (h : c₂ ≠ c₁) (γ₁ γ₂ : ℝ) :
    intervalTest c₂ c₁ c₂ γ₁ γ₂ = γ₂ := by
  simp [intervalTest_def, h]

@[simp]
theorem intervalTest_of_notMem_Ioo {t c₁ c₂ : ℝ} (h : t ∉ Ioo c₁ c₂) (h₁ : t ≠ c₁)
    (h₂ : t ≠ c₂) (γ₁ γ₂ : ℝ) : intervalTest t c₁ c₂ γ₁ γ₂ = 0 := by
  simp_all [intervalTest_def]

/-- An interval test in a measurable real statistic, with randomizations in `[0, 1]`, is a
test. -/
theorem isStatisticalTest_intervalTest {T : X → ℝ} (hT : Measurable T) (c₁ c₂ : ℝ)
    {γ₁ γ₂ : ℝ} (hγ₁ : γ₁ ∈ Icc (0 : ℝ) 1) (hγ₂ : γ₂ ∈ Icc (0 : ℝ) 1) :
    IsStatisticalTest fun x ↦ intervalTest (T x) c₁ c₂ γ₁ γ₂ := by
  refine .mk ?_ fun x ↦ ?_
  · simp_rw [intervalTest_def]
    exact Measurable.ite (hT measurableSet_Ioo) measurable_const
      (Measurable.ite (hT (measurableSet_singleton c₁)) measurable_const
        (Measurable.ite (hT (measurableSet_singleton c₂)) measurable_const measurable_const))
  · simp only [intervalTest_def]
    split_ifs
    exacts [⟨zero_le_one, le_rfl⟩, hγ₁, hγ₂, ⟨le_rfl, zero_le_one⟩]

end TauCeti
