/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Divergence.Trace
import Mathlib.Analysis.Distribution.Distribution
import Mathlib.MeasureTheory.Measure.OpenPos
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Distribution.TestFunction.Gradient
import TauCeti.Analysis.Distribution.TestFunction.Inner

/-!
# Weak divergence and solenoidal fields

On an open set, weak divergence is defined by pairing a locally integrable vector field with
scalar test gradients. The field is solenoidal if these pairings vanish. The predicate supports
restriction and changes of representative, and agrees with the trace when the field has a weak
Fréchet derivative. Against an additive Haar measure it therefore recovers classical divergence
for a continuously differentiable field. In particular, the kernel of divergence on test
fields consists exactly of the weakly solenoidal test fields.
-/

public section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped BigOperators ContDiff Distributions Gradient InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  {μ : Measure E} {Ω Ω' : Opens E} {u v : E → E} {g h : E → ℝ}

section Basic

variable [CompleteSpace E]

/-- The locally integrable field `u` has weak divergence `g` on `Ω` with respect to `μ` if
`∫ ⟪u, ∇φ⟫ ∂μ = -∫ φ g ∂μ` for every scalar test function on `Ω`. This gives the usual
distributional divergence when `μ` is an additive Haar measure. -/
def HasWeakDivergenceOn (μ : Measure E) (Ω : Opens E) (u : E → E) (g : E → ℝ) : Prop :=
  LocallyIntegrableOn u Ω μ ∧ LocallyIntegrableOn g Ω μ ∧
    ∀ φ : 𝓓(Ω, ℝ), ∫ x, ⟪u x, ∇ (φ : E → ℝ) x⟫_ℝ ∂μ = -∫ x, φ x * g x ∂μ

/-- The defining conditions for weak divergence, expressed using scalar test functions. -/
theorem hasWeakDivergenceOn_iff :
    HasWeakDivergenceOn μ Ω u g ↔ LocallyIntegrableOn u Ω μ ∧ LocallyIntegrableOn g Ω μ ∧
      ∀ φ : 𝓓(Ω, ℝ), ∫ x, ⟪u x, ∇ (φ : E → ℝ) x⟫_ℝ ∂μ = -∫ x, φ x * g x ∂μ :=
  (Iff.rfl)

/-- A solenoidal field is locally integrable and has weak divergence zero on `Ω`. -/
def IsSolenoidalOn (μ : Measure E) (Ω : Opens E) (u : E → E) : Prop :=
  HasWeakDivergenceOn μ Ω u 0

/-- Solenoidality is weak divergence zero. -/
theorem isSolenoidalOn_iff_hasWeakDivergenceOn :
    IsSolenoidalOn μ Ω u ↔ HasWeakDivergenceOn μ Ω u 0 :=
  (Iff.rfl)

/-- A field is solenoidal exactly when it is locally integrable and annihilates scalar test
gradients under integration. -/
theorem isSolenoidalOn_iff :
    IsSolenoidalOn μ Ω u ↔
      LocallyIntegrableOn u Ω μ ∧ ∀ φ : 𝓓(Ω, ℝ), ∫ x, ⟪u x, ∇ (φ : E → ℝ) x⟫_ℝ ∂μ = 0 := by
  have hzero : LocallyIntegrableOn (0 : E → ℝ) Ω μ := locallyIntegrableOn_zero
  simp [isSolenoidalOn_iff_hasWeakDivergenceOn, hasWeakDivergenceOn_iff, hzero]

namespace HasWeakDivergenceOn

/-- A field with a weak divergence is locally integrable on the open set. -/
theorem locallyIntegrableOn (hu : HasWeakDivergenceOn μ Ω u g) : LocallyIntegrableOn u Ω μ :=
  hu.1

/-- The weak divergence is locally integrable on the open set. -/
theorem locallyIntegrableOn_divergence (hu : HasWeakDivergenceOn μ Ω u g) :
    LocallyIntegrableOn g Ω μ :=
  hu.2.1

/-- The integration-by-parts identity pairing the field with a scalar test gradient. -/
theorem integral_inner_gradient_eq_neg_integral_mul (hu : HasWeakDivergenceOn μ Ω u g)
    (φ : 𝓓(Ω, ℝ)) :
    ∫ x, ⟪u x, ∇ (φ : E → ℝ) x⟫_ℝ ∂μ = -∫ x, φ x * g x ∂μ :=
  hu.2.2 φ

/-- A weak divergence restricts to smaller open sets. -/
theorem mono (hu : HasWeakDivergenceOn μ Ω u g) (hΩ : Ω' ≤ Ω) : HasWeakDivergenceOn μ Ω' u g :=
  ⟨hu.locallyIntegrableOn.mono_set hΩ, hu.locallyIntegrableOn_divergence.mono_set hΩ,
    fun φ ↦ hu.integral_inner_gradient_eq_neg_integral_mul
      ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans hΩ⟩⟩

/-- Almost-everywhere changes of the field and of its divergence on `Ω` preserve weak divergence. -/
theorem congr_ae (hu : HasWeakDivergenceOn μ Ω u g) (huv : u =ᵐ[μ.restrict Ω] v)
    (hgh : g =ᵐ[μ.restrict Ω] h) : HasWeakDivergenceOn μ Ω v h := by
  refine ⟨hu.locallyIntegrableOn.congr huv, hu.locallyIntegrableOn_divergence.congr hgh, fun φ ↦ ?_⟩
  have hfield : ∫ x, ⟪u x, ∇ (φ : E → ℝ) x⟫_ℝ ∂μ = ∫ x, ⟪v x, ∇ (φ : E → ℝ) x⟫_ℝ ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [ae_imp_of_ae_restrict huv] with x hx
    by_cases hxΩ : x ∈ (Ω : Set E)
    · rw [hx hxΩ]
    · rw [gradient_of_notMem_tsupport (fun hmem ↦ hxΩ (φ.tsupport_subset hmem))]
      simp
  have hdiv : ∫ x, φ x * g x ∂μ = ∫ x, φ x * h x ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [ae_imp_of_ae_restrict hgh] with x hx
    by_cases hxΩ : x ∈ (Ω : Set E)
    · rw [hx hxΩ]
    · simp [φ.zero_on_compl hxΩ]
  rw [← hfield, ← hdiv, hu.integral_inner_gradient_eq_neg_integral_mul]

/-- The zero field has weak divergence zero. -/
@[simp]
theorem zero : HasWeakDivergenceOn μ Ω (0 : E → E) 0 := by
  refine ⟨locallyIntegrableOn_zero, locallyIntegrableOn_zero, fun φ ↦ ?_⟩
  simp

/-- Negating a vector field negates its weak divergence. -/
theorem neg (hu : HasWeakDivergenceOn μ Ω u g) : HasWeakDivergenceOn μ Ω (-u) (-g) := by
  refine ⟨hu.locallyIntegrableOn.neg, hu.locallyIntegrableOn_divergence.neg, fun φ ↦ ?_⟩
  simp only [Pi.neg_apply, inner_neg_left, mul_neg, integral_neg,
    hu.integral_inner_gradient_eq_neg_integral_mul]

/-- Multiplying a field by a constant scales its weak divergence by that constant. -/
theorem const_smul (hu : HasWeakDivergenceOn μ Ω u g) (c : ℝ) :
    HasWeakDivergenceOn μ Ω (c • u) (c • g) := by
  refine ⟨hu.locallyIntegrableOn.smul c, hu.locallyIntegrableOn_divergence.smul c, fun φ ↦ ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, real_inner_smul_left, mul_left_comm (φ _),
    integral_const_mul, hu.integral_inner_gradient_eq_neg_integral_mul, mul_neg]

variable [OpensMeasurableSpace E]

/-- The divergence of the sum is the sum of the weak divergences. -/
theorem add (hu : HasWeakDivergenceOn μ Ω u g) (hv : HasWeakDivergenceOn μ Ω v h) :
    HasWeakDivergenceOn μ Ω (u + v) (g + h) := by
  refine ⟨hu.locallyIntegrableOn.add hv.locallyIntegrableOn,
    hu.locallyIntegrableOn_divergence.add hv.locallyIntegrableOn_divergence, fun φ ↦ ?_⟩
  have hinner {w : E → E} (hw : LocallyIntegrableOn w Ω μ) :
      Integrable (fun x ↦ ⟪w x, ∇ (φ : E → ℝ) x⟫_ℝ) μ := by
    simpa only [real_inner_comm, TestFunction.gradientCLM_apply] using
      (TestFunction.gradientCLM φ).integrable_inner hw
  have hmul {q : E → ℝ} (hq : LocallyIntegrableOn q Ω μ) :
      Integrable (fun x ↦ φ x * q x) μ := by
    simpa only [smul_eq_mul] using φ.integrable_smul hq
  simp only [Pi.add_apply, inner_add_left, mul_add]
  rw [integral_add (hinner hu.locallyIntegrableOn) (hinner hv.locallyIntegrableOn),
    integral_add (hmul hu.locallyIntegrableOn_divergence) (hmul hv.locallyIntegrableOn_divergence),
    hu.integral_inner_gradient_eq_neg_integral_mul, hv.integral_inner_gradient_eq_neg_integral_mul,
    neg_add]

/-- The weak divergence of a difference is the difference of the weak divergences. -/
theorem sub (hu : HasWeakDivergenceOn μ Ω u g) (hv : HasWeakDivergenceOn μ Ω v h) :
    HasWeakDivergenceOn μ Ω (u - v) (g - h) := by
  simpa only [sub_eq_add_neg] using hu.add hv.neg

/-- Weak divergence commutes with finite sums. -/
theorem sum {ι : Type*} {w : ι → E → E} {q : ι → E → ℝ} (s : Finset ι)
    (hs : ∀ i ∈ s, HasWeakDivergenceOn μ Ω (w i) (q i)) :
    HasWeakDivergenceOn μ Ω (∑ i ∈ s, w i) (∑ i ∈ s, q i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (zero (μ := μ) (Ω := Ω))
  | insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using
      (hs a (Finset.mem_insert_self a s)).add (ih fun i hi ↦ hs i (Finset.mem_insert_of_mem hi))

end HasWeakDivergenceOn

namespace IsSolenoidalOn

/-- The zero field is solenoidal on every open set. -/
@[simp]
theorem zero : IsSolenoidalOn μ Ω (0 : E → E) :=
  isSolenoidalOn_iff_hasWeakDivergenceOn.mpr HasWeakDivergenceOn.zero

/-- Solenoidality is preserved when restricting the open set. -/
theorem mono (hu : IsSolenoidalOn μ Ω u) (hΩ : Ω' ≤ Ω) : IsSolenoidalOn μ Ω' u :=
  HasWeakDivergenceOn.mono hu hΩ

/-- Changing the field almost everywhere on the open set preserves solenoidality. -/
theorem congr_ae (hu : IsSolenoidalOn μ Ω u) (huv : u =ᵐ[μ.restrict Ω] v) :
    IsSolenoidalOn μ Ω v :=
  HasWeakDivergenceOn.congr_ae hu huv .rfl

/-- The negative of a solenoidal field is solenoidal. -/
theorem neg (hu : IsSolenoidalOn μ Ω u) : IsSolenoidalOn μ Ω (-u) := by
  rw [isSolenoidalOn_iff_hasWeakDivergenceOn]
  simpa only [neg_zero] using HasWeakDivergenceOn.neg hu

/-- Scalar multiplication by a constant preserves solenoidality. -/
theorem const_smul (hu : IsSolenoidalOn μ Ω u) (c : ℝ) : IsSolenoidalOn μ Ω (c • u) := by
  rw [isSolenoidalOn_iff_hasWeakDivergenceOn]
  simpa only [smul_zero] using HasWeakDivergenceOn.const_smul hu c

/-- A sum of solenoidal fields is solenoidal. -/
theorem add [OpensMeasurableSpace E] (hu : IsSolenoidalOn μ Ω u) (hv : IsSolenoidalOn μ Ω v) :
    IsSolenoidalOn μ Ω (u + v) := by
  rw [isSolenoidalOn_iff_hasWeakDivergenceOn]
  simpa only [add_zero] using HasWeakDivergenceOn.add hu hv

/-- The difference of two solenoidal fields is solenoidal. -/
theorem sub [OpensMeasurableSpace E] (hu : IsSolenoidalOn μ Ω u) (hv : IsSolenoidalOn μ Ω v) :
    IsSolenoidalOn μ Ω (u - v) := by
  rw [isSolenoidalOn_iff_hasWeakDivergenceOn]
  simpa only [sub_zero] using HasWeakDivergenceOn.sub hu hv

/-- A finite sum of solenoidal fields is solenoidal. -/
theorem sum [OpensMeasurableSpace E] {ι : Type*} {w : ι → E → E} (s : Finset ι)
    (hs : ∀ i ∈ s, IsSolenoidalOn μ Ω (w i)) : IsSolenoidalOn μ Ω (∑ i ∈ s, w i) := by
  rw [isSolenoidalOn_iff_hasWeakDivergenceOn]
  simpa only [Finset.sum_const_zero] using
    (HasWeakDivergenceOn.sum (q := fun _ ↦ 0) s fun i hi ↦
      isSolenoidalOn_iff_hasWeakDivergenceOn.mp (hs i hi))

end IsSolenoidalOn

end Basic

variable [FiniteDimensional ℝ E]

/-- The trace of a weak Fréchet derivative is a weak divergence. -/
theorem HasWeakFDerivOn.hasWeakDivergenceOn [OpensMeasurableSpace E] {U : E → E →L[ℝ] E}
    (hu : HasWeakFDerivOn μ Ω u U) :
    HasWeakDivergenceOn μ Ω u (fun x ↦ LinearMap.trace ℝ E (U x)) := by
  refine ⟨hu.locallyIntegrableOn, ?_, fun φ ↦ ?_⟩
  · simpa only [Function.comp_def, traceCLM_apply] using
      (traceCLM ℝ E).locallyIntegrableOn_comp hu.locallyIntegrableOn_deriv
  · simpa only [real_inner_comm, smul_eq_mul] using
      hu.integral_inner_gradient_eq_neg_integral_smul_trace φ

variable [BorelSpace E]

/-- Two weak divergences of the same field agree almost everywhere on the open set. -/
theorem HasWeakDivergenceOn.ae_eq (hu : HasWeakDivergenceOn μ Ω u g)
    (hv : HasWeakDivergenceOn μ Ω u h) : g =ᵐ[μ.restrict Ω] h := by
  apply Distribution.ofFun_injective (n := ⊤)
    hu.locallyIntegrableOn_divergence hv.locallyIntegrableOn_divergence
  ext φ
  rw [Distribution.ofFun_apply hu.locallyIntegrableOn_divergence,
    Distribution.ofFun_apply hv.locallyIntegrableOn_divergence]
  exact neg_injective ((hu.integral_inner_gradient_eq_neg_integral_mul φ).symm.trans
    (hv.integral_inner_gradient_eq_neg_integral_mul φ))

variable [μ.IsAddHaarMeasure]

/-- The weak divergence of a `C¹` field is the trace of its classical derivative. -/
theorem _root_.ContDiffOn.hasWeakDivergenceOn (hu : ContDiffOn ℝ 1 u Ω) :
    HasWeakDivergenceOn μ Ω u (fun x ↦ LinearMap.trace ℝ E (fderiv ℝ u x)) :=
  hu.hasWeakFDerivOn_fderiv.hasWeakDivergenceOn

/-- A `C¹` field is solenoidal exactly when its classical divergence vanishes throughout the
open set. -/
theorem _root_.ContDiffOn.isSolenoidalOn_iff (hu : ContDiffOn ℝ 1 u Ω) :
    IsSolenoidalOn μ Ω u ↔ ∀ x ∈ (Ω : Set E), LinearMap.trace ℝ E (fderiv ℝ u x) = 0 := by
  have hdiv := hu.hasWeakDivergenceOn (μ := μ)
  rw [isSolenoidalOn_iff_hasWeakDivergenceOn]
  constructor
  · intro hzero
    refine Measure.eqOn_open_of_ae_eq (hdiv.ae_eq hzero) Ω.isOpen ?_ continuousOn_const
    simpa only [Function.comp_def, traceCLM_apply] using
      (traceCLM ℝ E).continuous.comp_continuousOn
        (hu.continuousOn_fderiv_of_isOpen Ω.isOpen le_rfl)
  · intro hzero
    exact hdiv.congr_ae .rfl (ae_restrict_of_forall_mem Ω.isOpen.measurableSet hzero)

end TauCeti

namespace TestFunction

open MeasureTheory Set TopologicalSpace
open scoped Distributions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Ω : Opens E}

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- A test field belongs to the kernel of divergence exactly when its underlying field is
weakly solenoidal. -/
theorem mem_solenoidalSubmodule_iff_isSolenoidalOn {φ : 𝓓(Ω, E)} :
    φ ∈ solenoidalSubmodule Ω ↔ TauCeti.IsSolenoidalOn μ Ω (φ : E → E) := by
  have hφ : ContDiffOn ℝ 1 (φ : E → E) Ω := (φ.contDiff.of_le (by simp)).contDiffOn
  rw [hφ.isSolenoidalOn_iff, mem_solenoidalSubmodule_iff]
  constructor
  · intro h x _
    simpa only [divergenceCLM_apply, FunLike.coe_zero, Pi.zero_apply] using congrArg (· x) h
  · intro h
    ext x
    by_cases hx : x ∈ (Ω : Set E)
    · simpa only [divergenceCLM_apply, FunLike.coe_zero, Pi.zero_apply] using h x hx
    · rw [(divergenceCLM φ).zero_on_compl hx, FunLike.coe_zero, Pi.zero_apply]

end TestFunction
