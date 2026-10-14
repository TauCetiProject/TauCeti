/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.Analysis.InnerProductSpace.GelfandTriple
public import TauCeti.Analysis.Sobolev.WeakDeriv.GelfandTriple
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Calculus.LineDeriv.Basic
import TauCeti.Analysis.InnerProductSpace.Lions
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.LpSeminorm.ContinuousOn
import TauCeti.MeasureTheory.Function.StronglyMeasurable.Caratheodory
import TauCeti.MeasureTheory.Function.StronglyMeasurable.Pettis
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive

/-!
# Existence for linear parabolic equations

Let `ι : V →L[ℝ] H` be a continuous linear map from a real Hilbert space `V` into a real inner
product space `H`, inducing `H → V*` (`ContinuousLinearMap.gelfandDual`). No injectivity or dense
range is assumed; with both, `V ↪ H ↪ V*` is a Gelfand triple. Consider on a time interval
`(a, b)` the abstract linear parabolic problem

`u' + A(t) u = f`, `u(a) = u₀`,

with `A(t) : V →L[ℝ] V*` bounded and satisfying Gårding's inequality
`α ‖v‖² - β ‖ι v‖² ≤ A(t) v v`, `f ∈ L²(a, b; V*)` and `u₀ ∈ H`. Testing the equation against a
`C¹` function `φ : ℝ → V` with `φ(b) = 0` and integrating the time derivative by parts turns it
into the **variational formulation**

`∫ₐᵇ (A(t) u(t) φ(t) - ⟪ι u(t), ι φ'(t)⟫) dt = ∫ₐᵇ f(t) φ(t) dt + ⟪u₀, ι φ(a)⟫`,

in which neither the time derivative of `u` nor its value at `t = a` appears: the initial
condition is carried by the boundary term `⟪u₀, ι φ(a)⟫`. This term does not change when `u₀` is
modified by an element of `(range ι)ᗮ`, so the formulation determines the initial value only
modulo `(range ι)ᗮ`; it encodes `u(a) = u₀` itself only when `ι` has dense range, as it does for a
genuine Gelfand triple. This file proves that the variational formulation has a
solution `u ∈ L²(a, b; V)` (`TauCeti.exists_memLp_forall_setIntegral_eq_add_inner`).

When `V` is moreover separable, every solution `u` of the variational formulation is a weak
solution in the sense of `TauCeti.HasWeakLineDerivOn.ae_eq_of_gelfandDual`: its weak time
derivative is `u' = f - A u ∈ L²(a, b; V*)`
(`TauCeti.hasWeakLineDerivOn_gelfandDual_of_forall_setIntegral_eq_add_inner`), and the value at
`t = a` of a continuous representative of `ι ∘ u` agrees with `u₀` modulo `(range ι)ᗮ`
(`TauCeti.gelfandDual_eq_of_forall_setIntegral_eq_add_inner`). For a Gelfand triple this gives
existence of a weak solution of `u' + A(t) u = f`, `u(a) = u₀`
(`TauCeti.exists_hasWeakLineDerivOn_gelfandDual`), which the energy estimate in
`TauCeti.Analysis.PDE.Parabolic.EnergyEstimate` shows to be unique when `β ≥ 0`. Separability
makes `t ↦ A(t) u(t)` strongly measurable as a function into `V*`
(`MeasureTheory.MemLp.clm_apply_of_forall_aestronglyMeasurable`, a consequence of Pettis'
theorem), which a weak derivative in `L²(a, b; V*)` needs.

## The proof

For coercive `A(t)` (the case `β = 0`) this is an application of Lions' representation theorem
(`LinearMap.exists_forall_apply_eq_and_norm_le_of_coercive`), with the Hilbert space
`L²(a, b; V)` for the solution and the `C¹` functions `φ` with `φ(b) = 0` for the test
functions. The left-hand side `E(φ, u)` is continuous in `u ∈ L²(a, b; V)`: its integrand is
bounded by a multiple of `‖u(t)‖`, and `L²(a, b) ⊆ L¹(a, b)` continuously. On the diagonal,
the fundamental theorem of calculus for `t ↦ ‖ι φ(t)‖²` and `φ(b) = 0` give

`E(φ, φ) = ∫ₐᵇ A(t) φ φ + ½ ‖ι φ(a)‖² ≥ α ‖φ‖²_{L²(V)} + ½ ‖ι φ(a)‖²`,

so `c p(φ)² ≤ E(φ, φ)` for `p(φ) = (‖φ‖²_{L²(V)} + ‖ι φ(a)‖²)^{1/2}` and `c = min α ½`, and the
right-hand side is bounded by `(‖f‖_{L²(V*)} + ‖u₀‖) p(φ)` by Cauchy–Schwarz.

In general, `u = e^{β (t - a)} w` solves the problem exactly when `w` solves it for the coercive
operator `A(t) + β ι* ι` and the right-hand side `e^{-β (t - a)} f`.

The coefficient `A` is only assumed weakly measurable, `t ↦ A(t) u v` almost everywhere strongly
measurable on `(a, b)` for all `u, v ∈ V` as in Lions and Showalter, and essentially bounded by
`Λ`. This covers divergence-form operators with `L^∞` coefficients, which are in general not
strongly measurable as maps into `V →L[ℝ] V*`. Measurability of `t ↦ A(t) u(t) φ(t)` for
`u ∈ L²(a, b; V)` then follows from
`MeasureTheory.AEStronglyMeasurable.apply_of_forall_of_continuous`, which approximates `(u, φ)`
with simple functions, so the variational existence theorem needs no separability of `V`.

For the weak derivative, test the variational formulation against `φ(t) = ψ(t) v` with `ψ`
smooth and compactly supported in `(a, b)`. For the initial value, test it against
`φ(t) = (b - t) / (b - a) v` and integrate by parts against the primitive of `u'`.

## Main declarations

* `TauCeti.exists_memLp_forall_setIntegral_eq_add_inner`: the variational formulation of
  `u' + A(t) u = f`, `u(a) = u₀`, has a solution in `L²(a, b; V)`.
* `TauCeti.exists_memLp_forall_setIntegral_eq_add_inner_of_ae_eq`: the same, with the
  hypotheses and the conclusion stated for bilinear functionals `B(t)` that agree with `A(t)` for
  almost every `t`.
* `TauCeti.hasWeakLineDerivOn_gelfandDual_of_forall_setIntegral_eq_add_inner`: a solution of the
  variational formulation has weak time derivative `f - A u`.
* `TauCeti.gelfandDual_eq_of_forall_setIntegral_eq_add_inner`: its continuous representative
  takes the initial value `u₀` modulo `(range ι)ᗮ`.
* `TauCeti.exists_hasWeakLineDerivOn_gelfandDual`: existence of a weak solution of
  `u' + A(t) u = f`, `u(a) = u₀`, in a Gelfand triple.

## References

* J.-L. Lions, *Équations différentielles opérationnelles et problèmes aux limites*,
  Grundlehren **111**, Springer, 1961.
* R. E. Showalter, *Monotone Operators in Banach Space and Nonlinear Partial Differential
  Equations*, Mathematical Surveys and Monographs **49**, AMS, 1997, Chapter III, Section 2.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §7.1.2, which constructs weak solutions
  of second-order parabolic equations by the Galerkin method instead.
-/

public section

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

namespace TauCeti

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] {A : ℝ → V →L[ℝ] StrongDual ℝ V}
  {f : ℝ → StrongDual ℝ V} {a b α β Λ : ℝ}

/-- For a `C¹` test function `φ`, the integrand `A(t) u(t) φ(t) - ⟪ι u(t), ι φ'(t)⟫` of the
variational formulation is integrable for every `u ∈ L²(a, b; V)`, and its integral is bounded by
a multiple of `‖u‖_{L²}`. -/
private theorem exists_forall_integrable_and_abs_integral_le (ι : V →L[ℝ] H)
    (hA : ∀ u v, AEStronglyMeasurable (fun t => A t u v) (volume.restrict (Ioo a b)))
    (hA_bound : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖A t‖ ≤ Λ) {φ : ℝ → V}
    (hφ : ContDiff ℝ 1 φ) :
    ∃ K, ∀ u : Lp V 2 (volume.restrict (Ioo a b)),
      Integrable (fun t => A t (u t) (φ t) - ⟪ι (u t), ι (deriv φ t)⟫_ℝ)
        (volume.restrict (Ioo a b)) ∧
      |∫ t in Ioo a b, (A t (u t) (φ t) - ⟪ι (u t), ι (deriv φ t)⟫_ℝ)| ≤ K * ‖u‖ := by
  have hφ' : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  set μ := volume.restrict (Ioo a b)
  set C₁ := lpNorm φ ∞ μ
  set C₂ := lpNorm (deriv φ) ∞ μ
  have hC₁ : ∀ᵐ t ∂μ, ‖φ t‖ ≤ C₁ := ae_le_lpNorm_exponent_top <|
    hφ.continuous.continuousOn.memLp_top_restrict_of_subset_isCompact isCompact_Icc
      measurableSet_Ioo Ioo_subset_Icc_self
  have hC₂ : ∀ᵐ t ∂μ, ‖deriv φ t‖ ≤ C₂ := ae_le_lpNorm_exponent_top <|
    hφ'.continuousOn.memLp_top_restrict_of_subset_isCompact isCompact_Icc measurableSet_Ioo
      Ioo_subset_Icc_self
  set K := |Λ| * C₁ + ‖ι‖ * ‖ι‖ * C₂
  have hK : 0 ≤ K := add_nonneg (mul_nonneg (abs_nonneg _) lpNorm_nonneg)
    (mul_nonneg (mul_self_nonneg _) lpNorm_nonneg)
  -- The integrand is dominated by `K ‖u‖`.
  have hdom : ∀ u : Lp V 2 μ,
      ∀ᵐ t ∂μ, ‖A t (u t) (φ t) - ⟪ι (u t), ι (deriv φ t)⟫_ℝ‖ ≤ K * ‖u t‖ := by
    intro u
    filter_upwards [hA_bound, hC₁, hC₂] with t hAt h₁ h₂
    calc ‖A t (u t) (φ t) - ⟪ι (u t), ι (deriv φ t)⟫_ℝ‖
        ≤ ‖A t (u t) (φ t)‖ + ‖⟪ι (u t), ι (deriv φ t)⟫_ℝ‖ := norm_sub_le _ _
      _ ≤ ‖A t‖ * ‖u t‖ * ‖φ t‖ + ‖ι (u t)‖ * ‖ι (deriv φ t)‖ :=
          add_le_add ((A t).le_opNorm₂ _ _) (norm_inner_le_norm _ _)
      _ ≤ |Λ| * ‖u t‖ * C₁ + ‖ι‖ * ‖u t‖ * (‖ι‖ * C₂) := by
          gcongr
          · exact hAt.trans (le_abs_self Λ)
          · exact ι.le_opNorm _
          · exact (ι.le_opNorm _).trans (by gcongr)
      _ = K * ‖u t‖ := by ring
  refine ⟨K * (μ univ ^ (1 - 1 / (2 : ℝ≥0∞).toReal)).toReal, fun u => ⟨?_, ?_⟩⟩
  · refine (((Lp.memLp u).integrable one_le_two).norm.const_mul K).mono' ?_ (hdom u)
    exact (((Lp.aestronglyMeasurable u).prodMk hφ.continuous.aestronglyMeasurable)
      |>.apply_of_forall_of_continuous (g := fun t p => A t p.1 p.2)
        (fun p => hA p.1 p.2) fun t => (A t).continuous₂).sub
      ((ι.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u)).inner
        (ι.continuous.comp hφ').aestronglyMeasurable)
  · simpa only [Real.norm_eq_abs] using Lp.norm_integral_le_of_ae_norm_le_mul u hK (hdom u)

/-- **The energy inequality behind coercivity.** For a `C¹` function `φ` with `φ(b) = 0`,
integrating `d/dt ‖ι φ‖² = 2 ⟪ι φ, ι φ'⟫` by parts and using coercivity of `A` gives

`α ∫ₐᵇ ‖φ‖² + ‖ι φ(a)‖² / 2 ≤ ∫ₐᵇ (A(t) φ φ - ⟪ι φ, ι φ'⟫)`. -/
private theorem mul_setIntegral_norm_sq_add_le (ι : V →L[ℝ] H) (hab : a ≤ b)
    (hA : ∀ u v, AEStronglyMeasurable (fun t => A t u v) (volume.restrict (Ioo a b)))
    (hA_bound : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖A t‖ ≤ Λ)
    (hA_coercive : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ v, α * ‖v‖ ^ 2 ≤ A t v v) {φ : ℝ → V}
    (hφ : ContDiff ℝ 1 φ) (hφb : φ b = 0) :
    α * (∫ t in Ioo a b, ‖φ t‖ ^ 2) + ‖ι (φ a)‖ ^ 2 / 2 ≤
      ∫ t in Ioo a b, (A t (φ t) (φ t) - ⟪ι (φ t), ι (deriv φ t)⟫_ℝ) := by
  have hφ' : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  have hint : ∀ {g : ℝ → ℝ}, Continuous g → Integrable g (volume.restrict (Ioo a b)) :=
    fun hg => (hg.integrableOn_Icc (a := a) (b := b)).mono_set Ioo_subset_Icc_self
  have hcont₁ : Continuous fun t => α * ‖φ t‖ ^ 2 := continuous_const.mul (hφ.continuous.norm.pow 2)
  have hcont₂ : Continuous fun t => ⟪ι (φ t), ι (deriv φ t)⟫_ℝ :=
    (ι.continuous.comp hφ.continuous).inner (ι.continuous.comp hφ')
  -- The fundamental theorem of calculus for `‖ι φ‖²`, with `φ(b) = 0`.
  have hftc : ∫ t in Ioo a b, ⟪ι (φ t), ι (deriv φ t)⟫_ℝ = -(‖ι (φ a)‖ ^ 2 / 2) := by
    have hderiv : ∀ t, HasDerivAt (fun s => ‖ι (φ s)‖ ^ 2)
        (2 * ⟪ι (φ t), ι (deriv φ t)⟫_ℝ) t := fun t =>
      (ι.hasFDerivAt.comp_hasDerivAt t ((hφ.differentiable one_ne_zero t).hasDerivAt)).norm_sq
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := b)
      (fun t _ => hderiv t) ((continuous_const.mul hcont₂).intervalIntegrable a b)
    rw [hφb, map_zero, norm_zero, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo] at h
    linarith
  -- `t ↦ A(t) φ(t) φ(t)` is bounded and strongly measurable, hence integrable.
  have hAφφ : Integrable (fun t => A t (φ t) (φ t)) (volume.restrict (Ioo a b)) := by
    set C := lpNorm φ ∞ (volume.restrict (Ioo a b))
    have hC : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖φ t‖ ≤ C := ae_le_lpNorm_exponent_top <|
      hφ.continuous.continuousOn.memLp_top_restrict_of_subset_isCompact isCompact_Icc
        measurableSet_Ioo Ioo_subset_Icc_self
    refine (MemLp.of_bound ((hφ.continuous.aestronglyMeasurable.prodMk
      hφ.continuous.aestronglyMeasurable).apply_of_forall_of_continuous
        (g := fun t p => A t p.1 p.2) (fun p => hA p.1 p.2) fun t => (A t).continuous₂)
      (Λ * C * C) ?_).integrable le_rfl
    filter_upwards [hA_bound, hC] with t hAt hφt
    have hΛ : 0 ≤ Λ := (norm_nonneg (A t)).trans hAt
    have hC0 : 0 ≤ C := (norm_nonneg _).trans hφt
    calc ‖A t (φ t) (φ t)‖ ≤ ‖A t‖ * ‖φ t‖ * ‖φ t‖ := (A t).le_opNorm₂ _ _
      _ ≤ Λ * C * C := by gcongr
  calc α * (∫ t in Ioo a b, ‖φ t‖ ^ 2) + ‖ι (φ a)‖ ^ 2 / 2
      = ∫ t in Ioo a b, (α * ‖φ t‖ ^ 2 - ⟪ι (φ t), ι (deriv φ t)⟫_ℝ) := by
        rw [integral_sub (hint hcont₁) (hint hcont₂), integral_const_mul, hftc]
        ring
    _ ≤ ∫ t in Ioo a b, (A t (φ t) (φ t) - ⟪ι (φ t), ι (deriv φ t)⟫_ℝ) := by
        refine integral_mono_ae (hint (hcont₁.sub hcont₂)) (hAφφ.sub (hint hcont₂)) ?_
        filter_upwards [hA_coercive] with t ht
        linarith [ht (φ t)]

variable (V b) in
/-- The test functions of the variational formulation: the `C¹` functions `φ : ℝ → V` with
`φ(b) = 0`. -/
private def testFunctions : Submodule ℝ (ℝ → V) where
  carrier := {φ | ContDiff ℝ 1 φ ∧ φ b = 0}
  add_mem' hφ hψ := ⟨hφ.1.add hψ.1, by simp [hφ.2, hψ.2]⟩
  zero_mem' := ⟨contDiff_const, rfl⟩
  smul_mem' c _ hφ := ⟨hφ.1.const_smul c, by simp [hφ.2]⟩

private theorem mem_testFunctions {φ : ℝ → V} :
    φ ∈ testFunctions V b ↔ ContDiff ℝ 1 φ ∧ φ b = 0 :=
  Iff.rfl

private theorem memLp_testFunctions (φ : testFunctions V b) :
    MemLp (φ : ℝ → V) 2 (volume.restrict (Ioo a b)) := by
  exact (φ.2.1.continuous.continuousOn.memLp_top_restrict_of_subset_isCompact isCompact_Icc
    measurableSet_Ioo Ioo_subset_Icc_self).mono_exponent le_top

variable (a) in
/-- The test functions as elements of `L²(a, b; V)`. -/
private noncomputable def testFunctionsToL2 :
    testFunctions V b →ₗ[ℝ] Lp V 2 (volume.restrict (Ioo a b)) where
  toFun φ := (memLp_testFunctions φ).toLp φ
  map_add' φ ψ := MemLp.toLp_add (memLp_testFunctions φ) (memLp_testFunctions ψ)
  map_smul' c φ := MemLp.toLp_const_smul c (memLp_testFunctions φ)

private theorem coeFn_testFunctionsToL2 (φ : testFunctions V b) :
    (testFunctionsToL2 a φ : ℝ → V) =ᵐ[volume.restrict (Ioo a b)] φ :=
  (memLp_testFunctions φ).coeFn_toLp

/-- The left-hand side `E(φ, u) = ∫ₐᵇ (A(t) u(t) φ(t) - ⟪ι u(t), ι φ'(t)⟫) dt` of the variational
formulation, as a continuous linear functional of `u ∈ L²(a, b; V)` depending linearly on the
test function `φ`. -/
private noncomputable def variationalForm (ι : V →L[ℝ] H)
    (hA : ∀ u v, AEStronglyMeasurable (fun t => A t u v) (volume.restrict (Ioo a b)))
    (hA_bound : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖A t‖ ≤ Λ) :
    testFunctions V b →ₗ[ℝ] StrongDual ℝ (Lp V 2 (volume.restrict (Ioo a b))) where
  toFun φ := LinearMap.mkContinuousOfExistsBound
    { toFun := fun u =>
        ∫ t in Ioo a b, (A t (u t) ((φ : ℝ → V) t) - ⟪ι (u t), ι (deriv (φ : ℝ → V) t)⟫_ℝ)
      map_add' := fun u v => by
        obtain ⟨K, hK⟩ := exists_forall_integrable_and_abs_integral_le ι hA hA_bound φ.2.1
        rw [← integral_add (hK u).1 (hK v).1]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add u v] with t ht
        simp only [ht, Pi.add_apply, map_add, add_apply, inner_add_left]
        ring
      map_smul' := fun c u => by
        rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c u] with t ht
        simp only [ht, Pi.smul_apply, map_smul, smul_apply, smul_eq_mul,
          inner_smul_left, RCLike.conj_to_real]
        ring }
    (by
      obtain ⟨K, hK⟩ := exists_forall_integrable_and_abs_integral_le ι hA hA_bound φ.2.1
      exact ⟨K, fun u => (hK u).2⟩)
  map_add' φ ψ := by
    ext u
    obtain ⟨K₁, hK₁⟩ := exists_forall_integrable_and_abs_integral_le ι hA hA_bound φ.2.1
    obtain ⟨K₂, hK₂⟩ := exists_forall_integrable_and_abs_integral_le ι hA hA_bound ψ.2.1
    simp only [add_apply, LinearMap.mkContinuousOfExistsBound_apply,
      LinearMap.coe_mk, AddHom.coe_mk]
    rw [← integral_add (hK₁ u).1 (hK₂ u).1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    have hφ := φ.2.1.differentiable one_ne_zero t
    have hψ := ψ.2.1.differentiable one_ne_zero t
    simp only [Submodule.coe_add, Pi.add_apply, deriv_add hφ hψ, map_add, inner_add_right]
    ring
  map_smul' c φ := by
    ext u
    simp only [smul_apply, LinearMap.mkContinuousOfExistsBound_apply,
      LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, smul_eq_mul]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [Submodule.coe_smul, Pi.smul_apply,
      deriv_const_smul c (φ.2.1.differentiable one_ne_zero t), map_smul, inner_smul_right,
      smul_eq_mul]
    ring

private theorem variationalForm_apply (ι : V →L[ℝ] H)
    (hA : ∀ u v, AEStronglyMeasurable (fun t => A t u v) (volume.restrict (Ioo a b)))
    (hA_bound : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖A t‖ ≤ Λ) (φ : testFunctions V b)
    (u : Lp V 2 (volume.restrict (Ioo a b))) :
    variationalForm ι hA hA_bound φ u =
      ∫ t in Ioo a b, (A t (u t) ((φ : ℝ → V) t) - ⟪ι (u t), ι (deriv (φ : ℝ → V) t)⟫_ℝ) :=
  rfl

/-- **Coercivity of the variational form**: `α ‖φ‖²_{L²(V)} + ‖ι φ(a)‖² / 2 ≤ E(φ, φ)`. -/
private theorem mul_norm_sq_add_le_variationalForm (ι : V →L[ℝ] H) (hab : a ≤ b)
    (hA : ∀ u v, AEStronglyMeasurable (fun t => A t u v) (volume.restrict (Ioo a b)))
    (hA_bound : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖A t‖ ≤ Λ)
    (hA_coercive : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ v, α * ‖v‖ ^ 2 ≤ A t v v)
    (φ : testFunctions V b) :
    α * ‖testFunctionsToL2 a φ‖ ^ 2 + ‖ι ((φ : ℝ → V) a)‖ ^ 2 / 2 ≤
      variationalForm ι hA hA_bound φ (testFunctionsToL2 a φ) := by
  have hnorm : ∫ t in Ioo a b, ‖(φ : ℝ → V) t‖ ^ 2 = ‖testFunctionsToL2 a φ‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_testFunctionsToL2 φ] with t ht
    rw [ht, real_inner_self_eq_norm_sq]
  rw [← hnorm, variationalForm_apply]
  refine (mul_setIntegral_norm_sq_add_le ι hab hA hA_bound hA_coercive φ.2.1 φ.2.2).trans_eq
    (integral_congr_ae ?_)
  filter_upwards [coeFn_testFunctionsToL2 φ] with t ht
  rw [ht]

/-- The variational formulation of `u' + A(t) u = f`, `u(a) = u₀`, has a solution when `A(t)` is
coercive. This is the case `β = 0` of `TauCeti.exists_memLp_forall_setIntegral_eq_add_inner`,
to which the general case is reduced by an exponential change of the unknown. -/
private theorem exists_memLp_forall_setIntegral_eq_add_inner_of_coercive [CompleteSpace V]
    (ι : V →L[ℝ] H) (hab : a ≤ b)
    (hA : ∀ u v, AEStronglyMeasurable (fun t => A t u v) (volume.restrict (Ioo a b)))
    (hA_bound : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖A t‖ ≤ Λ) (hα : 0 < α)
    (hA_coercive : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ v, α * ‖v‖ ^ 2 ≤ A t v v)
    (hf : MemLp f 2 (volume.restrict (Ioo a b))) (u₀ : H) :
    ∃ u : ℝ → V, MemLp u 2 (volume.restrict (Ioo a b)) ∧
      ∀ φ : ℝ → V, ContDiff ℝ 1 φ → φ b = 0 →
        ∫ t in Ioo a b, (A t (u t) (φ t) - ⟪ι (u t), ι (deriv φ t)⟫_ℝ) =
          (∫ t in Ioo a b, f t (φ t)) + ⟪u₀, ι (φ a)⟫_ℝ := by
  set μ := volume.restrict (Ioo a b)
  set R := (InnerProductSpace.toDual ℝ V).symm
  set j := testFunctionsToL2 (V := V) (b := b) a
  -- The right-hand side `ℓ(φ) = ⟪R f, φ⟫_{L²} + ⟪u₀, ι φ(a)⟫`.
  have hRf : MemLp (fun t => R (f t)) 2 μ :=
    hf.of_le (R.continuous.comp_aestronglyMeasurable hf.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t => by simp [R])
  set F : Lp V 2 μ := hRf.toLp (fun t => R (f t))
  let ℓ : testFunctions V b →ₗ[ℝ] ℝ :=
    { toFun := fun φ => ⟪F, j φ⟫_ℝ + ⟪u₀, ι ((φ : ℝ → V) a)⟫_ℝ
      map_add' := fun φ ψ => by
        simp only [map_add, inner_add_right, Submodule.coe_add, Pi.add_apply]
        ring
      map_smul' := fun c φ => by
        simp only [map_smul, inner_smul_right, Submodule.coe_smul, Pi.smul_apply,
          RingHom.id_apply, smul_eq_mul]
        ring }
  have hℓ_def : ∀ φ : testFunctions V b, ℓ φ = ⟪F, j φ⟫_ℝ + ⟪u₀, ι ((φ : ℝ → V) a)⟫_ℝ :=
    fun _ => rfl
  have hℓ_apply : ∀ φ : testFunctions V b,
      ℓ φ = (∫ t in Ioo a b, f t ((φ : ℝ → V) t)) + ⟪u₀, ι ((φ : ℝ → V) a)⟫_ℝ := by
    intro φ
    rw [hℓ_def, L2.inner_def]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hRf.coeFn_toLp, coeFn_testFunctionsToL2 φ] with t hFt hjt
    rw [hFt, hjt, InnerProductSpace.toDual_symm_apply]
  -- `p(φ) = (‖φ‖²_{L²(V)} + ‖ι φ(a)‖²)^{1/2}` controls `j φ` and `ι φ(a)`.
  let p : testFunctions V b → ℝ := fun φ => √(‖j φ‖ ^ 2 + ‖ι ((φ : ℝ → V) a)‖ ^ 2)
  have hp_sq : ∀ φ : testFunctions V b, p φ ^ 2 = ‖j φ‖ ^ 2 + ‖ι ((φ : ℝ → V) a)‖ ^ 2 := fun φ =>
    Real.sq_sqrt (by positivity)
  have hjp : ∀ φ : testFunctions V b, ‖j φ‖ ≤ p φ := fun φ =>
    Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖ι ((φ : ℝ → V) a)‖])
  have hιp : ∀ φ : testFunctions V b, ‖ι ((φ : ℝ → V) a)‖ ≤ p φ := fun φ =>
    Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖j φ‖])
  -- Coercivity of `E` with respect to `p`.
  have hcoer : ∀ φ : testFunctions V b,
      min α (1 / 2) * p φ ^ 2 ≤ variationalForm ι hA hA_bound φ (j φ) := by
    intro φ
    have hlow := mul_norm_sq_add_le_variationalForm ι hab hA hA_bound hA_coercive φ
    have hmin₁ : min α (1 / 2) ≤ α := min_le_left _ _
    have hmin₂ : min α (1 / 2) ≤ 1 / 2 := min_le_right _ _
    rw [hp_sq]
    nlinarith [sq_nonneg ‖j φ‖, sq_nonneg ‖ι ((φ : ℝ → V) a)‖]
  -- The right-hand side is bounded by `p`.
  have hbound : ∀ φ : testFunctions V b, |ℓ φ| ≤ (‖F‖ + ‖u₀‖) * p φ := by
    intro φ
    calc |ℓ φ| = |⟪F, j φ⟫_ℝ + ⟪u₀, ι ((φ : ℝ → V) a)⟫_ℝ| := by rw [hℓ_def]
      _ ≤ ‖F‖ * ‖j φ‖ + ‖u₀‖ * ‖ι ((φ : ℝ → V) a)‖ :=
          (abs_add_le _ _).trans
            (add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _))
      _ ≤ ‖F‖ * p φ + ‖u₀‖ * p φ := by gcongr <;> [exact hjp φ; exact hιp φ]
      _ = (‖F‖ + ‖u₀‖) * p φ := by ring
  -- Lions' theorem produces the solution.
  obtain ⟨u, hu, -⟩ := LinearMap.exists_forall_apply_eq_and_norm_le_of_coercive
    (variationalForm ι hA hA_bound) (fun φ => j φ) p ℓ (lt_min hα one_half_pos) (by positivity)
    hcoer hjp hbound
  refine ⟨u, Lp.memLp u, fun φ hφ hφb => ?_⟩
  have h := hu ⟨φ, mem_testFunctions.2 ⟨hφ, hφb⟩⟩
  rwa [variationalForm_apply, hℓ_apply] at h

/-- **Existence for linear parabolic equations, in variational form.** Let `ι : V →L[ℝ] H`
be any continuous linear map (neither injectivity nor dense range is assumed) with `V` a Hilbert
space, and let `A(t) : V →L[ℝ] V*` be weakly
measurable in `t` (`t ↦ A(t) u v` almost everywhere strongly measurable on `(a, b)` for all
`u, v`), bounded by `Λ` and satisfy
**Gårding's inequality** `α ‖v‖² - β ‖ι v‖² ≤ A(t) v v` with `α > 0`, for almost every
`t ∈ (a, b)`. Then for every
`f ∈ L²(a, b; V*)` and `u₀ ∈ H` there is `u ∈ L²(a, b; V)` with

`∫ₐᵇ (A(t) u(t) φ(t) - ⟪ι u(t), ι φ'(t)⟫) dt = ∫ₐᵇ f(t) φ(t) dt + ⟪u₀, ι φ(a)⟫`

for every `C¹` function `φ : ℝ → V` with `φ(b) = 0`. This is the weak formulation of
`u' + A(t) u = f` with initial value `u₀`, obtained by integrating `⟪u', φ⟫` by parts. Since `u₀`
enters only through `⟪u₀, ι φ(a)⟫`, it is seen only modulo `(range ι)ᗮ`; the condition is
`u(a) = u₀` itself when `ι` has dense range. No sign is imposed on
`β`. -/
theorem exists_memLp_forall_setIntegral_eq_add_inner [CompleteSpace V] {ι : V →L[ℝ] H}
    (hab : a ≤ b)
    (hA : ∀ u v, AEStronglyMeasurable (fun t => A t u v) (volume.restrict (Ioo a b)))
    (hA_bound : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖A t‖ ≤ Λ) (hα : 0 < α)
    (hA_garding : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ v, α * ‖v‖ ^ 2 - β * ‖ι v‖ ^ 2 ≤ A t v v)
    (hf : MemLp f 2 (volume.restrict (Ioo a b))) (u₀ : H) :
    ∃ u : ℝ → V, MemLp u 2 (volume.restrict (Ioo a b)) ∧
      ∀ φ : ℝ → V, ContDiff ℝ 1 φ → φ b = 0 →
        ∫ t in Ioo a b, (A t (u t) (φ t) - ⟪ι (u t), ι (deriv φ t)⟫_ℝ) =
          (∫ t in Ioo a b, f t (φ t)) + ⟪u₀, ι (φ a)⟫_ℝ := by
  -- Writing `u = e w` with `e(t) = exp (β (t - a))`, the unknown `w` solves the problem for the
  -- coercive operator `A + β ι* ι` with right-hand side `e⁻¹ f`.
  set e : ℝ → ℝ := fun t => Real.exp (β * (t - a)) with he
  have he_pos : ∀ t, 0 < e t := fun t => Real.exp_pos _
  have he_cont : Continuous e :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub continuous_const))
  have he_deriv : ∀ t, HasDerivAt e (β * e t) t := fun t => by
    simpa [he, mul_comm] using (((hasDerivAt_id t).sub_const a).const_mul β).exp
  -- Continuous functions are essentially bounded on `(a, b)`, so `e` and `e⁻¹` are multipliers
  -- of `L²(a, b)`.
  have htop : ∀ {g : ℝ → ℝ}, Continuous g → MemLp g ⊤ (volume.restrict (Ioo a b)) := fun hg =>
    hg.continuousOn.memLp_top_restrict_of_subset_isCompact isCompact_Icc measurableSet_Ioo
      Ioo_subset_Icc_self
  set B : V →L[ℝ] StrongDual ℝ V := ι.gelfandDual.comp ι
  have hB : ∀ v w, B v w = ⟪ι v, ι w⟫_ℝ := fun v w => ι.gelfandDual_apply _ _
  have hshift_bound : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖A t + β • B‖ ≤ Λ + |β| * ‖B‖ := by
    filter_upwards [hA_bound] with t ht
    exact (ContinuousLinearMap.opNorm_add_le _ _).trans
      (add_le_add ht ((ContinuousLinearMap.opNorm_smul_le β B).trans_eq
        (by rw [Real.norm_eq_abs])))
  have hshift_coercive : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ v,
      α * ‖v‖ ^ 2 ≤ (A t + β • B) v v := by
    filter_upwards [hA_garding] with t ht v
    simp only [add_apply, smul_apply, hB, real_inner_self_eq_norm_sq, smul_eq_mul]
    linarith [ht v]
  obtain ⟨w, hw, hweq⟩ := exists_memLp_forall_setIntegral_eq_add_inner_of_coercive
    (A := fun t => A t + β • B) ι hab (fun u v => (hA u v).add aestronglyMeasurable_const)
    hshift_bound hα hshift_coercive ((htop (he_cont.inv₀ fun t => (he_pos t).ne')).smul hf) u₀
  refine ⟨fun t => e t • w t, (htop he_cont).smul hw, fun φ hφ hφb => ?_⟩
  -- Test the equation for `w` against `e φ`.
  have hψ : ContDiff ℝ 1 (fun t => e t • φ t) :=
    (Real.contDiff_exp.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))).smul hφ
  have hψ_deriv : ∀ t, deriv (fun s => e s • φ s) t = (β * e t) • φ t + e t • deriv φ t :=
    fun t => ((he_deriv t).smul ((hφ.differentiable one_ne_zero t).hasDerivAt)).deriv.trans
      (add_comm _ _)
  have h := hweq (fun t => e t • φ t) hψ (by simp [hφb])
  have hea : e a = 1 := by simp [he]
  simp only [hea, one_smul] at h
  -- Pointwise, the two weak formulations have the same integrands.
  have hlhs : ∀ t, A t (e t • w t) (φ t) - ⟪ι (e t • w t), ι (deriv φ t)⟫_ℝ =
      (A t + β • B) (w t) (e t • φ t) - ⟪ι (w t), ι (deriv (fun s => e s • φ s) t)⟫_ℝ := by
    intro t
    simp only [hψ_deriv, map_add, map_smul, add_apply, smul_apply, hB, inner_add_right,
      inner_smul_left, inner_smul_right, smul_eq_mul, RCLike.conj_to_real]
    ring
  have hrhs : ∀ t, f t (φ t) = ((e t)⁻¹ • f t) (e t • φ t) := by
    intro t
    simp only [map_smul, smul_apply, smul_eq_mul]
    field_simp [(he_pos t).ne']
  simp only [hlhs, hrhs]
  exact h

/-- `TauCeti.exists_memLp_forall_setIntegral_eq_add_inner` with the operators `A(t)` known only
through a family of bilinear functionals `B(t)` that they agree with for almost every `t`:
measurability, boundedness and Gårding's inequality are then hypotheses on `B`, and so is the
conclusion. This is the form in which a concrete parabolic problem supplies its operators. -/
theorem exists_memLp_forall_setIntegral_eq_add_inner_of_ae_eq [CompleteSpace V]
    (ι : V →L[ℝ] H) (hab : a ≤ b) {B : ℝ → V → V → ℝ}
    (hAB : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ u v, A t u v = B t u v)
    (hB : ∀ u v, AEStronglyMeasurable (fun t => B t u v) (volume.restrict (Ioo a b)))
    (hΛ : 0 ≤ Λ)
    (hB_bound : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ u v, ‖B t u v‖ ≤ Λ * (‖u‖ * ‖v‖))
    (hα : 0 < α)
    (hB_garding : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ v, α * ‖v‖ ^ 2 - β * ‖ι v‖ ^ 2 ≤ B t v v)
    (hf : MemLp f 2 (volume.restrict (Ioo a b))) (u₀ : H) :
    ∃ u : ℝ → V, MemLp u 2 (volume.restrict (Ioo a b)) ∧
      ∀ φ : ℝ → V, ContDiff ℝ 1 φ → φ b = 0 →
        ∫ t in Ioo a b, (B t (u t) (φ t) - ⟪ι (u t), ι (deriv φ t)⟫_ℝ) =
          (∫ t in Ioo a b, f t (φ t)) + ⟪u₀, ι (φ a)⟫_ℝ := by
  obtain ⟨u, hu, hueq⟩ := exists_memLp_forall_setIntegral_eq_add_inner (A := A) hab
    (fun u v => (hB u v).congr (hAB.mono fun t ht => (ht u v).symm))
    (by
      filter_upwards [hAB, hB_bound] with t hABt hBt
      refine (A t).opNorm_le_bound₂ hΛ fun u v => ?_
      rw [hABt, mul_assoc]
      exact hBt u v)
    hα (by
      filter_upwards [hAB, hB_garding] with t hABt hBt v
      rw [hABt]
      exact hBt v) hf u₀
  refine ⟨u, hu, fun φ hφ hφb => ?_⟩
  rw [← hueq φ hφ hφb]
  refine integral_congr_ae ?_
  filter_upwards [hAB] with t hABt
  rw [hABt]

/-! ### The variational solution is a weak solution -/

section WeakSolution

variable {ι : V →L[ℝ] H} {u : ℝ → V} {u₀ : H}

/-- **The variational formulation gives the weak time derivative.** Let `V` be a separable Hilbert
space, let `A(t) : V →L[ℝ] V*` be weakly measurable and essentially bounded on `(a, b)`, and let
`f ∈ L²(a, b; V*)`. If `u ∈ L²(a, b; V)` satisfies the variational formulation

`∫ₐᵇ (A(t) u(t) φ(t) - ⟪ι u(t), ι φ'(t)⟫) dt = ∫ₐᵇ f(t) φ(t) dt + ⟪u₀, ι φ(a)⟫`

for every `C¹` function `φ : ℝ → V` with `φ(b) = 0`, then `u' = f - A u` is the weak time
derivative of `ι.gelfandDual ∘ ι ∘ u` on `(a, b)`: `u` is a weak solution of `u' + A(t) u = f`. -/
theorem hasWeakLineDerivOn_gelfandDual_of_forall_setIntegral_eq_add_inner [CompleteSpace V]
    [TopologicalSpace.SeparableSpace V]
    (hA : ∀ u v, AEStronglyMeasurable (fun t => A t u v) (volume.restrict (Ioo a b)))
    (hA_bound : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖A t‖ ≤ Λ)
    (hf : MemLp f 2 (volume.restrict (Ioo a b))) (hu : MemLp u 2 (volume.restrict (Ioo a b)))
    (hvar : ∀ φ : ℝ → V, ContDiff ℝ 1 φ → φ b = 0 →
      ∫ t in Ioo a b, (A t (u t) (φ t) - ⟪ι (u t), ι (deriv φ t)⟫_ℝ) =
        (∫ t in Ioo a b, f t (φ t)) + ⟪u₀, ι (φ a)⟫_ℝ) :
    HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (fun t => ι.gelfandDual (ι (u t)))
      (fun t => f t - A t (u t)) 1 := by
  set μ := volume.restrict (Ioo a b)
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.2 measure_Ioo_lt_top.ne
  have hloc {g : ℝ → StrongDual ℝ V} (hg : MemLp g 2 μ) : LocallyIntegrableOn g (Ioo a b) :=
    IntegrableOn.locallyIntegrableOn (hg.integrable one_le_two)
  have hG : LocallyIntegrableOn (fun t => ι.gelfandDual (ι (u t))) (Ioo a b) :=
    hloc ((ι.gelfandDual.comp ι).comp_memLp' hu)
  have hAu := hloc (hu.clm_apply_of_forall_aestronglyMeasurable hA hA_bound)
  have hf' := hloc hf
  have hg : LocallyIntegrableOn (fun t => f t - A t (u t)) (Ioo a b) := hf'.sub hAu
  refine hasWeakLineDerivOn_iff_testFunction.2 ⟨inferInstance, hG, hg, fun φ => ?_⟩
  set ψ : ℝ → ℝ := (φ : ℝ → ℝ) with hψ_def
  have hψ : ContDiff ℝ 1 ψ := φ.contDiff.of_le (by simp)
  have hψ0 : ∀ t ∉ Ioo a b, ψ t = 0 := fun t ht =>
    image_eq_zero_of_notMem_tsupport fun h => ht (φ.tsupport_subset h)
  -- Both sides are integrals over `(a, b)`; compare them on each `v ∈ V`.
  rw [← setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul,
    ← setIntegral_smul_eq_integral_smul]
  ext v
  have hI {g : ℝ → StrongDual ℝ V} (hg : LocallyIntegrableOn g (Ioo a b)) :
      Integrable (fun t => ψ t * g t v) μ := by
    simpa using ((integrable_smul_of_locallyIntegrableOn hg φ).restrict
      (s := Ioo a b)).apply_continuousLinearMap v
  have hI' : Integrable (fun t => deriv ψ t * ⟪ι (u t), ι v⟫_ℝ) μ := by
    simpa [ContinuousLinearMap.gelfandDual_apply, lineDeriv_one] using
      ((integrable_lineDeriv_smul_of_locallyIntegrableOn hG φ 1).restrict
        (s := Ioo a b)).apply_continuousLinearMap v
  rw [ContinuousLinearMap.integral_apply
      ((integrable_lineDeriv_smul_of_locallyIntegrableOn hG φ 1).restrict) v,
    neg_apply, ContinuousLinearMap.integral_apply
      ((integrable_smul_of_locallyIntegrableOn hg φ).restrict) v]
  -- Test the variational formulation against `ψ v`.
  have h := hvar (fun t => ψ t • v) (hψ.smul contDiff_const) (by simp [hψ0 b (by simp)])
  have hd : ∀ t, deriv (fun s => ψ s • v) t = deriv ψ t • v := fun t =>
    deriv_smul_const ((hψ.differentiable one_ne_zero) t) v
  simp only [hd, hψ0 a (by simp), zero_smul, map_zero, inner_zero_right, add_zero, map_smul,
    smul_eq_mul, inner_smul_right] at h
  rw [integral_sub (hI hAu) hI'] at h
  simp only [TopologicalSpace.Opens.coe_mk, ← hψ_def, smul_apply, sub_apply,
    ContinuousLinearMap.gelfandDual_apply, smul_eq_mul, mul_sub, lineDeriv_one]
  rw [integral_sub (hI hf') (hI hAu)]
  linarith

/-- **The variational formulation gives the initial value.** In the setting of
`TauCeti.hasWeakLineDerivOn_gelfandDual_of_forall_setIntegral_eq_add_inner`, let `a < b` and let
`w` be a representative of `ι ∘ u` continuous on `[a, b]`. Then `w a` agrees with `u₀` modulo
`(range ι)ᗮ`: `⟪w a, ι v⟫ = ⟪u₀, ι v⟫` for every `v ∈ V`. -/
theorem gelfandDual_eq_of_forall_setIntegral_eq_add_inner [CompleteSpace V]
    [TopologicalSpace.SeparableSpace V] {w : ℝ → H} (hab : a < b)
    (hA : ∀ u v, AEStronglyMeasurable (fun t => A t u v) (volume.restrict (Ioo a b)))
    (hA_bound : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖A t‖ ≤ Λ)
    (hf : MemLp f 2 (volume.restrict (Ioo a b))) (hu : MemLp u 2 (volume.restrict (Ioo a b)))
    (hvar : ∀ φ : ℝ → V, ContDiff ℝ 1 φ → φ b = 0 →
      ∫ t in Ioo a b, (A t (u t) (φ t) - ⟪ι (u t), ι (deriv φ t)⟫_ℝ) =
        (∫ t in Ioo a b, f t (φ t)) + ⟪u₀, ι (φ a)⟫_ℝ)
    (hw : ContinuousOn w (Icc a b)) (hae : (fun t => ι (u t)) =ᵐ[volume.restrict (Ioo a b)] w) :
    ι.gelfandDual (w a) = ι.gelfandDual u₀ := by
  set μ := volume.restrict (Ioo a b)
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.2 measure_Ioo_lt_top.ne
  have hd := hasWeakLineDerivOn_gelfandDual_of_forall_setIntegral_eq_add_inner hA hA_bound hf hu
    hvar
  have hAu := hu.clm_apply_of_forall_aestronglyMeasurable hA hA_bound
  set g : ℝ → StrongDual ℝ V := fun t => f t - A t (u t) with hg_def
  have hg : MemLp g 2 μ := hf.sub hAu
  have hgi : IntervalIntegrable g volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 (hg.integrable one_le_two)
  -- `ξ` is a continuous representative of `ι.gelfandDual ∘ ι ∘ u`, whose weak derivative is `g`.
  set ξ : ℝ → StrongDual ℝ V := fun t => ι.gelfandDual (w t)
  have hξ : ContinuousOn ξ (Icc a b) := ι.gelfandDual.continuous.comp_continuousOn hw
  have hξae : (fun t => ι.gelfandDual (ι (u t))) =ᵐ[μ] ξ := hae.fun_comp ι.gelfandDual
  -- Test against `θ v`, where `θ` decreases affinely from `θ a = 1` to `θ b = 0`.
  set θ : ℝ → ℝ := fun t => (b - t) / (b - a) with hθ_def
  have hθ : ContDiff ℝ 1 θ := (contDiff_const.sub contDiff_id).div_const _
  have hθd : Continuous (deriv θ) := hθ.continuous_deriv le_rfl
  have hθa : θ a = 1 := div_self (sub_ne_zero.2 hab.ne')
  have hθb : θ b = 0 := by simp [hθ_def]
  -- Integrating by parts gives `∫ₐᵇ θ' ξ = -ξ a - ∫ₐᵇ θ g`.
  have hK : ∫ t in a..b, deriv θ t • ξ t = -ξ a - ∫ t in a..b, θ t • g t := by
    rw [hd.integral_deriv_smul_eq_sub (hg.integrable one_le_two) hξ hξae hab.le hθ, hθa, hθb,
      zero_smul, one_smul, zero_sub]
  refine ContinuousLinearMap.ext fun v => ?_
  -- Evaluate at `v` and pass to integrals over `(a, b)`.
  have hKv := congrArg (fun L : StrongDual ℝ V => L v) hK
  rw [ContinuousLinearMap.intervalIntegral_apply
      (hθd.continuousOn.smul (uIcc_of_le hab.le ▸ hξ)).intervalIntegrable v, sub_apply, neg_apply,
    ContinuousLinearMap.intervalIntegral_apply
      (hgi.continuousOn_smul hθ.continuous.continuousOn) v,
    intervalIntegral.integral_of_le hab.le, intervalIntegral.integral_of_le hab.le,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo] at hKv
  have hQ : ∫ t in Ioo a b, (deriv θ t • ξ t) v = ∫ t in Ioo a b, deriv θ t * ⟪ι (u t), ι v⟫_ℝ := by
    refine integral_congr_ae ?_
    filter_upwards [hξae] with t ht
    rw [smul_apply, ← ht, ContinuousLinearMap.gelfandDual_apply, smul_eq_mul]
  rw [hQ] at hKv
  simp only [smul_apply, smul_eq_mul, hg_def, sub_apply, mul_sub, ξ,
    ContinuousLinearMap.gelfandDual_apply] at hKv
  have hI {F : ℝ → StrongDual ℝ V} {c : ℝ → ℝ} (hc : Continuous c) (hF : MemLp F 2 μ) :
      Integrable (fun t => c t * F t v) μ := by
    have hcF : MemLp (fun t => c t • F t) 2 μ :=
      (hc.continuousOn.memLp_top_restrict_of_subset_isCompact isCompact_Icc measurableSet_Ioo
        Ioo_subset_Icc_self).smul hF
    simpa using (hcF.integrable one_le_two).apply_continuousLinearMap v
  have hIQ : Integrable (fun t => deriv θ t * ⟪ι (u t), ι v⟫_ℝ) μ := by
    simpa [ContinuousLinearMap.gelfandDual_apply] using
      hI (F := fun t => ι.gelfandDual (ι (u t))) hθd ((ι.gelfandDual.comp ι).comp_memLp' hu)
  rw [integral_sub (hI hθ.continuous hf) (hI hθ.continuous hAu)] at hKv
  -- Test the variational formulation against `θ v`.
  have h := hvar (fun t => θ t • v) (hθ.smul contDiff_const) (by simp [hθb])
  have hd' : ∀ t, deriv (fun s => θ s • v) t = deriv θ t • v := fun t =>
    deriv_smul_const ((hθ.differentiable one_ne_zero) t) v
  simp only [hd', hθa, one_smul, map_smul, smul_eq_mul, inner_smul_right] at h
  rw [integral_sub (hI hθ.continuous hAu) hIQ] at h
  simp only [ContinuousLinearMap.gelfandDual_apply]
  linarith

/-- **Existence of weak solutions for linear parabolic equations.** Let `V ↪ H ↪ V*` be a Gelfand
triple: `V` a separable Hilbert space, `H` a Hilbert space and `ι : V →L[ℝ] H` with dense range.
Let `A(t) : V →L[ℝ] V*` be weakly measurable (`t ↦ A(t) u v` almost everywhere strongly
measurable on `(a, b)` for all `u, v`), bounded by `Λ` and satisfy **Gårding's inequality**
`α ‖v‖² - β ‖ι v‖² ≤ A(t) v v` with `α > 0`, for almost every `t ∈ (a, b)`. Then for every
`f ∈ L²(a, b; V*)` and `u₀ ∈ H` there is a weak solution of

`u' + A(t) u = f`, `u(a) = u₀`:

a `u ∈ L²(a, b; V)` such that `u' = f - A u ∈ L²(a, b; V*)` is the weak time derivative of
`ι.gelfandDual ∘ ι ∘ u` on `(a, b)`, and a representative `w` of `ι ∘ u` continuous on `[a, b]`
with `w a = u₀`. For `β ≥ 0` it is unique: see `TauCeti.HasWeakLineDerivOn.eqOn_of_gelfandDual`
and `TauCeti.HasWeakLineDerivOn.ae_eq_of_gelfandDual`. -/
theorem exists_hasWeakLineDerivOn_gelfandDual [CompleteSpace V] [TopologicalSpace.SeparableSpace V]
    [CompleteSpace H] (hι : DenseRange ι) (hab : a ≤ b)
    (hA : ∀ u v, AEStronglyMeasurable (fun t => A t u v) (volume.restrict (Ioo a b)))
    (hA_bound : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖A t‖ ≤ Λ) (hα : 0 < α)
    (hA_garding : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ v, α * ‖v‖ ^ 2 - β * ‖ι v‖ ^ 2 ≤ A t v v)
    (hf : MemLp f 2 (volume.restrict (Ioo a b))) (u₀ : H) :
    ∃ u : ℝ → V, ∃ w : ℝ → H, MemLp u 2 (volume.restrict (Ioo a b)) ∧
      MemLp (fun t => f t - A t (u t)) 2 (volume.restrict (Ioo a b)) ∧
      HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (fun t => ι.gelfandDual (ι (u t)))
        (fun t => f t - A t (u t)) 1 ∧
      ContinuousOn w (Icc a b) ∧ (fun t => ι (u t)) =ᵐ[volume.restrict (Ioo a b)] w ∧
      w a = u₀ := by
  obtain ⟨u, hu, hvar⟩ :=
    exists_memLp_forall_setIntegral_eq_add_inner hab hA hA_bound hα hA_garding hf u₀
  have hd := hasWeakLineDerivOn_gelfandDual_of_forall_setIntegral_eq_add_inner hA hA_bound hf hu
    hvar
  have hg := hf.sub (hu.clm_apply_of_forall_aestronglyMeasurable hA hA_bound)
  rcases hab.eq_or_lt with rfl | hab
  · exact ⟨u, fun _ => u₀, hu, hg, hd, continuousOn_const, by simp [Filter.EventuallyEq], rfl⟩
  obtain ⟨w, hw, hae⟩ := hd.exists_continuousOn_ae_eq_of_gelfandDual hu hg
  exact ⟨u, w, hu, hg, hd, hw, hae, ι.gelfandDual_injective hι
    (gelfandDual_eq_of_forall_setIntegral_eq_add_inner hab hA hA_bound hf hu hvar hw hae)⟩

end WeakSolution

end TauCeti
