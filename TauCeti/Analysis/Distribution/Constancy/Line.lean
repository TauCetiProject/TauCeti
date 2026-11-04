/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.LocalConstancy
public import TauCeti.Analysis.Distribution.TestFunction.DualEquiv
import TauCeti.Analysis.Distribution.Constancy.Basic
import TauCeti.Analysis.Distribution.DuBoisReymond
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv

/-!
# Constancy of distributions on the real line

A Banach-valued distribution on a connected nonempty open subset of the real line has zero
first derivative exactly when it is integration against a unique constant. No order-zero or
finite-mass assumption is needed. The local statement computes the constant using any
integral-one test in a bounded interval: subtracting that test times the integral leaves a
mean-zero test, which has a compactly supported smooth primitive in the same interval; this
needs no completeness of `F`. For a Banach space `F`, the global statements are the case `E = ℝ`,
`μ = volume` of `Distribution.existsUnique_eq_ofFun_const_of_forall_lineDerivOp_eq_zero` and
`Distribution.lineDerivOp_ofFun_const`, since `∂_{v} T = v • ∂_{1} T` on the line.

The corresponding theorem for finite-dimensional vector-valued tests identifies a functional
annihilating derivatives with integration against one fixed continuous linear map. This is the
coordinate form of constancy for one-dimensional currents and of uniqueness of distributional
primitives up to a constant.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §2.3,
  distributions with vanishing derivatives.
-/

public section

open Set MeasureTheory TopologicalSpace LineDeriv
open scoped Distributions Topology

namespace Distribution

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens ℝ}

/-- On a bounded interval, a distribution with zero derivative evaluates a test by its integral
and its value on any integral-one test supported in that interval. -/
theorem apply_eq_integral_smul_of_lineDerivOp_eq_zero {T : 𝓓'(Ω, F)}
    (hT : ∂_{(1 : ℝ)} T = 0) {a b : ℝ} (hab : Ioo a b ⊆ Ω)
    (η : 𝓓(Ω, ℝ)) (hη : tsupport η ⊆ Ioo a b) (hηint : ∫ x, η x = 1)
    (φ : 𝓓(Ω, ℝ)) (hφ : tsupport φ ⊆ Ioo a b) :
    T φ = (∫ x, φ x) • T η := by
  let g := φ - (∫ x, φ x) • η
  have hgs : tsupport g ⊆ Ioo a b := by
    apply (tsupport_sub _ _).trans (union_subset hφ ?_)
    simpa only [FunLike.coe_smul, Pi.smul_def] using
      (tsupport_smul_subset_right (fun _ : ℝ ↦ ∫ x, φ x) η).trans hη
  have hgint : ∫ x, g x = 0 := by
    simp only [g, FunLike.coe_sub, Pi.sub_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [integral_sub (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport)
      ((η.continuous.integrable_of_hasCompactSupport η.hasCompactSupport).const_mul _),
      integral_const_mul, hηint]
    ring
  obtain ⟨ψ, hψ, hcψ, hsψ, hdψ⟩ :=
    g.contDiff.exists_contDiff_deriv_eq_of_integral_eq_zero hgs hgint
  let χ : 𝓓(Ω, ℝ) := ⟨ψ, hψ, hcψ, hsψ.trans hab⟩
  have hd : ∂_{(1 : ℝ)} χ = g := by
    ext x
    rw [TestFunction.lineDerivOp_one_apply_eq_deriv]
    exact congrFun hdψ x
  have hz : T g = 0 := by
    have he := congrArg (fun S : 𝓓'(Ω, F) ↦ S χ) hT
    simpa only [lineDerivOp_apply_apply, map_neg, hd, zero_apply, neg_eq_zero] using he
  simpa only [g, map_sub, map_smul, sub_eq_zero] using hz

variable [CompleteSpace F]

/-- A distribution on a connected nonempty open subset of the real line with vanishing first
derivative is integration against a unique constant. -/
theorem existsUnique_eq_ofFun_const_of_lineDerivOp_eq_zero (T : 𝓓'(Ω, F))
    (hΩ : IsConnected (Ω : Set ℝ)) (hT : ∂_{(1 : ℝ)} T = 0) :
    ∃! c : F, T = ofFun Ω (fun _ ↦ c) volume ⊤ :=
  T.existsUnique_eq_ofFun_const_of_forall_lineDerivOp_eq_zero volume hΩ fun v ↦ by
    rw [← mul_one v, ← smul_eq_mul, lineDerivOp_left_smul, hT, smul_zero]

/-- On a connected nonempty real open domain, zero derivative characterizes constant
Banach-valued distributions. The nonemptiness makes the constant unique. -/
theorem lineDerivOp_one_eq_zero_iff (T : 𝓓'(Ω, F)) (hΩ : IsConnected (Ω : Set ℝ)) :
    ∂_{(1 : ℝ)} T = 0 ↔ ∃! c : F, T = ofFun Ω (fun _ ↦ c) volume ⊤ := by
  refine ⟨T.existsUnique_eq_ofFun_const_of_lineDerivOp_eq_zero hΩ, ?_⟩
  rintro ⟨c, rfl, -⟩
  exact lineDerivOp_ofFun_const volume c 1

/-- Two distributional primitives on a connected nonempty real open domain differ by
integration against a unique constant. -/
theorem existsUnique_sub_eq_ofFun_const_of_lineDerivOp_eq (T S : 𝓓'(Ω, F))
    (hΩ : IsConnected (Ω : Set ℝ)) (hTS : ∂_{(1 : ℝ)} T = ∂_{(1 : ℝ)} S) :
    ∃! c : F, T - S = ofFun Ω (fun _ ↦ c) volume ⊤ := by
  apply (T - S).existsUnique_eq_ofFun_const_of_lineDerivOp_eq_zero hΩ
  simpa only [lineDerivOp_eq_lineDerivCLM, map_sub, sub_eq_zero] using hTS

end Distribution

namespace TestFunction

open ContinuousLinearMap
open scoped CompactConvergenceCLM

variable {F V : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] {Ω : Opens ℝ}

/-- A functional on finite-dimensional vector-valued tests on a connected nonempty real open
domain that annihilates their derivatives is integration against a unique fixed linear map. -/
theorem existsUnique_eq_integralAgainstBilinCLM_of_lineDeriv_eq_zero
    (T : 𝓓(Ω, F) →L_c[ℝ] V) (hΩ : IsConnected (Ω : Set ℝ))
    (hT : ∀ φ : 𝓓(Ω, F), T (∂_{(1 : ℝ)} φ) = 0) :
    ∃! A : F →L[ℝ] V, T = toUniformConvergenceCLM _ V _
      (integralAgainstBilinCLM (apply ℝ V) volume (fun _ ↦ A) : 𝓓(Ω, F) →L[ℝ] V) := by
  have hd : ∂_{(1 : ℝ)} (dualEquivDistribution T) = 0 :=
    lineDeriv_dualEquivDistribution_eq_zero hT
  obtain ⟨A, hA, hu⟩ := (dualEquivDistribution T
    ).existsUnique_eq_ofFun_const_of_lineDerivOp_eq_zero hΩ hd
  refine ⟨A, ?_, fun B hB ↦ hu B ?_⟩
  · apply dualEquivDistribution.injective
    exact hA.trans (dualEquivDistribution_integralAgainstBilinCLM _ _).symm
  · rw [hB, dualEquivDistribution_integralAgainstBilinCLM]

end TestFunction
