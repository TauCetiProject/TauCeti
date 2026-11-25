/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import TauCeti.Analysis.Semigroups.Group.MeanErgodic
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.MeasureTheory.Integral.IntervalIntegral.InnerProduct
import TauCeti.MeasureTheory.Measure.CharacteristicFunction.Wiener

/-!
# Spectral atomic-mass identity for unitary C₀-groups

When `U` is a unitary C₀-group on a complete complex Hilbert space `H` and `σ` is a finite Borel
measure on `ℝ` representing `t ↦ ⟪v, U t v⟫_ℂ` as `charFun σ`, combining the twisted mean ergodic
theorem (`IsUnitary.tendsto_twistedAverage_starProjection`) with atomic-mass inversion for
characteristic functions (`TauCeti.tendsto_average_cexp_mul_charFun`) identifies the squared
norm of the eigenprojection onto `U.eigenspace hU.isComplexLinear ω` as the spectral atomic mass
`σ.real {ω}`. At every finite averaging horizon `T`, Fubini's theorem also expresses the squared
norm of the twisted average as the `σ`-integral of the squared modulus of the Dirichlet averaging
kernel (`IsUnitary.norm_twistedAverage_sq_eq_integral`).

## Main results

* `IsUnitary.norm_twistedAverage_sq_eq_integral`: spectral representation of the squared norm of a
  twisted orbit average over `[0, T]`.
* `IsUnitary.norm_starProjection_eigenspace_sq_eq_measureReal_singleton`:
  `‖(U.eigenspace hU.isComplexLinear ω).starProjection v‖ ^ 2 = σ.real {ω}`.
* `IsUnitary.exists_tendsto_twistedAverage`: existence of the twisted mean ergodic limit `w`
  at frequency `a` (`ω = 2πa`) together with its eigenfunction, orthogonality, and spectral
  atomic-mass properties.
-/

public section

noncomputable section

open ComplexConjugate Filter MeasureTheory
open scoped InnerProductSpace Topology

namespace TauCeti.Semigroups.StronglyContinuousGroup

namespace IsUnitary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {U : StronglyContinuousGroup H}

/-- Spectral integral representation of the inner product between two twisted orbit vectors. -/
private theorem inner_twisted_orbit_eq_integral (hU : U.IsUnitary) (v : H) {σ : Measure ℝ}
    (hσ : ∀ t : ℝ, ⟪v, U t v⟫_ℂ = charFun σ t) (ω s t : ℝ) :
    ⟪Complex.exp (-(ω * s * Complex.I)) • U s v,
      Complex.exp (-(ω * t * Complex.I)) • U t v⟫_ℂ =
      ∫ ξ, conj (Complex.exp (s * (ξ - ω) * Complex.I)) *
        Complex.exp (t * (ξ - ω) * Complex.I) ∂σ := by
  have hUst : ⟪U s v, U t v⟫_ℂ = ⟪v, U (t - s) v⟫_ℂ := by
    calc
      ⟪U s v, U t v⟫_ℂ = ⟪U (-s) (U s v), U (-s) (U t v)⟫_ℂ :=
        (hU.inner_map_map (-s) _ _).symm
      _ = ⟪v, U (t - s) v⟫_ℂ := by
          rw [U.map_neg_apply_map_apply, ← U.map_add_apply, neg_add_eq_sub]
  rw [inner_smul_left, inner_smul_right, hUst, hσ (t - s), charFun_apply_real,
    ← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ξ ↦ ?_)
  simp only [← Complex.exp_conj, map_neg, map_mul, map_sub, Complex.conj_ofReal,
    Complex.conj_I, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Integrating the inner product of twisted orbit vectors over the second time variable via
Fubini's theorem. -/
private theorem intervalIntegral_inner_twisted_orbit_eq (hU : U.IsUnitary)
    (v : H) {σ : Measure ℝ} [IsFiniteMeasure σ]
    (hσ : ∀ t : ℝ, ⟪v, U t v⟫_ℂ = charFun σ t) (ω T s : ℝ) :
    (∫ t in (0 : ℝ)..T,
        ⟪Complex.exp (-(ω * s * Complex.I)) • U s v,
          Complex.exp (-(ω * t * Complex.I)) • U t v⟫_ℂ) =
      ∫ ξ, conj (Complex.exp (s * (ξ - ω) * Complex.I)) *
        (∫ t in (0 : ℝ)..T, Complex.exp (t * (ξ - ω) * Complex.I)) ∂σ := by
  simp_rw [inner_twisted_orbit_eq_integral hU v hσ ω s]
  have : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) T)) :=
    Real.isFiniteMeasure_restrict_Ioc (min 0 T) (max 0 T)
  have hint : Integrable (Function.uncurry fun t ξ : ℝ ↦
      conj (Complex.exp (s * (ξ - ω) * Complex.I)) * Complex.exp (t * (ξ - ω) * Complex.I))
      ((volume.restrict (Set.uIoc 0 T)).prod σ) :=
    Integrable.of_bound (by fun_prop : Continuous _).aestronglyMeasurable 1
      (Eventually.of_forall fun p ↦ by
        rw [Function.uncurry_apply_pair, norm_mul, Complex.norm_conj, ← Complex.ofReal_sub,
          ← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I, ← Complex.ofReal_mul,
          Complex.norm_exp_ofReal_mul_I, mul_one])
  rw [intervalIntegral_integral_swap hint]
  exact integral_congr_ae (Eventually.of_forall fun ξ ↦ intervalIntegral.integral_const_mul _ _)

/-- Unnormalized spectral representation for the squared norm of a twisted orbit integral. -/
private theorem norm_intervalIntegral_twisted_sq_eq [CompleteSpace H] (hU : U.IsUnitary)
    (v : H) {σ : Measure ℝ} [IsFiniteMeasure σ]
    (hσ : ∀ t : ℝ, ⟪v, U t v⟫_ℂ = charFun σ t) (ω T : ℝ) :
    ‖∫ t in (0 : ℝ)..T, Complex.exp (-(ω * t * Complex.I)) • U t v‖ ^ 2 =
      ∫ ξ, ‖∫ t in (0 : ℝ)..T, Complex.exp (t * (ξ - ω) * Complex.I)‖ ^ 2 ∂σ := by
  let f : ℝ → H := fun t ↦ Complex.exp (-(ω * t * Complex.I)) • U t v
  let e : ℝ → ℝ → ℂ := fun t ξ ↦ Complex.exp (t * (ξ - ω) * Complex.I)
  let K : ℝ → ℂ := fun ξ ↦ ∫ t in (0 : ℝ)..T, e t ξ
  have hf_int : IntervalIntegrable f volume 0 T :=
    ((by fun_prop : Continuous fun t : ℝ ↦ Complex.exp (-(ω * t * Complex.I))).smul
      (U.continuous_orbit v)).intervalIntegrable 0 T
  have hK_cont : Continuous K :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun ξ t ↦ e t ξ) (by fun_prop) 0 T
  have : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) T)) :=
    Real.isFiniteMeasure_restrict_Ioc (min 0 T) (max 0 T)
  have hint2 : Integrable (Function.uncurry fun s ξ ↦ conj (e s ξ) * K ξ)
      ((volume.restrict (Set.uIoc 0 T)).prod σ) :=
    Integrable.of_bound
      ((Complex.continuous_conj.comp (by fun_prop)).mul
        (hK_cont.comp continuous_snd)).aestronglyMeasurable |T|
      (Eventually.of_forall fun p ↦ by
        dsimp only [e]
        rw [Function.uncurry_apply_pair, norm_mul, Complex.norm_conj, ← Complex.ofReal_sub,
          ← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
        simpa only [Complex.ofReal_mul, Complex.ofReal_sub, sub_zero] using
          TauCeti.norm_integral_cexp_le (p.2 - ω) 0 T)
  have hcomplex :
      ((‖∫ t in (0 : ℝ)..T, f t‖ ^ 2 : ℝ) : ℂ) = ((∫ ξ, ‖K ξ‖ ^ 2 ∂σ : ℝ) : ℂ) := by
    calc
      ((‖∫ t in (0 : ℝ)..T, f t‖ ^ 2 : ℝ) : ℂ)
          = ∫ s in (0 : ℝ)..T, ∫ t in (0 : ℝ)..T, ⟪f s, f t⟫_ℂ := by
        convert TauCeti.norm_intervalIntegral_sq_eq (𝕜 := ℂ) hf_int
      _ = ∫ s in (0 : ℝ)..T, ∫ ξ, conj (e s ξ) * K ξ ∂σ :=
        intervalIntegral.integral_congr fun s _ ↦
          intervalIntegral_inner_twisted_orbit_eq hU v hσ ω T s
      _ = ∫ ξ, (∫ s in (0 : ℝ)..T, conj (e s ξ) * K ξ) ∂σ :=
        intervalIntegral_integral_swap hint2
      _ = ∫ ξ, ((‖K ξ‖ ^ 2 : ℝ) : ℂ) ∂σ := by
        refine integral_congr_ae (Eventually.of_forall fun ξ ↦ ?_)
        dsimp only
        rw [intervalIntegral.integral_mul_const, intervalIntegral.intervalIntegral_conj,
          Complex.conj_mul', Complex.ofReal_pow]
      _ = ((∫ ξ, ‖K ξ‖ ^ 2 ∂σ : ℝ) : ℂ) := integral_ofReal
  exact Complex.ofReal_injective hcomplex

/-- **Spectral representation of the squared norm of a twisted average**: if `σ` is a finite Borel
measure whose characteristic function is `t ↦ ⟪v, U t v⟫_ℂ`, then the squared norm of the twisted
average over `[0, T]` is the `σ`-integral of the squared modulus of the Dirichlet average kernel. -/
theorem norm_twistedAverage_sq_eq_integral [CompleteSpace H] (hU : U.IsUnitary) (v : H)
    {σ : Measure ℝ} [IsFiniteMeasure σ]
    (hσ : ∀ t : ℝ, ⟪v, U t v⟫_ℂ = charFun σ t) (ω T : ℝ) :
    ‖(T : ℂ)⁻¹ • ∫ t in (0 : ℝ)..T, Complex.exp (-(ω * t * Complex.I)) • U t v‖ ^ 2 =
      ∫ ξ, ‖(T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T,
        Complex.exp (t * (ξ - ω) * Complex.I)‖ ^ 2 ∂σ := by
  rw [norm_smul, mul_pow, norm_intervalIntegral_twisted_sq_eq hU v hσ ω T, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ξ ↦ ?_)
  dsimp only
  rw [norm_mul, mul_pow]

/-- **Spectral atomic-mass identity.** For a unitary C₀-group `U` on a complete complex Hilbert
space `H`, an angular frequency `ω : ℝ`, a vector `v : H`, and any finite Borel measure `σ` on `ℝ`
representing `t ↦ ⟪v, U t v⟫_ℂ` as `charFun σ`, the squared norm of the orthogonal projection of
`v` onto `U.eigenspace hU.isComplexLinear ω` equals `σ.real {ω}`. -/
theorem norm_starProjection_eigenspace_sq_eq_measureReal_singleton [CompleteSpace H]
    (hU : U.IsUnitary) (ω : ℝ) (v : H) {σ : Measure ℝ} [IsFiniteMeasure σ]
    (hσ : ∀ t : ℝ, ⟪v, U t v⟫_ℂ = charFun σ t) :
    ‖(U.eigenspace hU.isComplexLinear ω).starProjection v‖ ^ 2 = σ.real {ω} := by
  set P := (U.eigenspace hU.isComplexLinear ω).starProjection
  have hlim₁ : Tendsto (fun T : ℝ ↦
      ⟪v, T⁻¹ • ∫ t in (0 : ℝ)..T, Complex.exp (-(ω * t * Complex.I)) • U t v⟫_ℂ)
      atTop (𝓝 ⟪v, P v⟫_ℂ) :=
    ((innerSL ℂ v).continuous.continuousAt.tendsto).comp
      (hU.tendsto_twistedAverage_starProjection ω v)
  have hlim₂ : Tendsto (fun T : ℝ ↦
      (T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, Complex.exp (-(ω * t * Complex.I)) * charFun σ t)
      atTop (𝓝 (σ.real {ω} : ℂ)) :=
    by simpa only [neg_mul] using TauCeti.tendsto_average_cexp_mul_charFun σ ω
  have hfun : (fun T : ℝ ↦
      ⟪v, T⁻¹ • ∫ t in (0 : ℝ)..T, Complex.exp (-(ω * t * Complex.I)) • U t v⟫_ℂ) =
      fun T : ℝ ↦
        (T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, Complex.exp (-(ω * t * Complex.I)) * charFun σ t := by
    funext T
    have horbit : (fun t : ℝ ↦ Complex.exp (-(ω * t * Complex.I)) • U t v) =
        fun t : ℝ ↦ U.phaseShift hU.isComplexLinear ω t v :=
      funext fun t ↦ by rw [U.phaseShift_apply_apply, neg_mul]
    rw [horbit, inner_smul_right_eq_smul, Complex.real_smul, Complex.ofReal_inv,
      (U.phaseShift hU.isComplexLinear ω).inner_intervalIntegral_orbit]
    congr 2
    ext t
    rw [phaseShift_apply_apply, neg_mul, inner_smul_right, hσ]
  rw [hfun] at hlim₁
  have heq : ⟪v, P v⟫_ℂ = (σ.real {ω} : ℂ) := tendsto_nhds_unique hlim₁ hlim₂
  have hre := congrArg RCLike.re heq
  simpa [P, ← Submodule.inner_starProjection_left_eq_right,
    Submodule.re_inner_starProjection_eq_normSq] using hre

/-- **Continuous-time twisted mean ergodic theorem with spectral atomic mass.** For a unitary
C₀-group `U` on a complete complex Hilbert space `H`, a frequency `a : ℝ`, and `v : H`, the
twisted time averages `(T⁻¹ : ℂ) • ∫ t in (0 : ℝ)..T, exp (-(2 * π * a * t * I)) • U t v`
converge in norm as `T → ∞` to a vector `w` satisfying `U t w = exp (2 * π * a * t * I) • w` for
all `t`, orthogonal to `v - w` against every vector with the same eigenvalue behavior, and
satisfying `‖w‖ ^ 2 = σ.real {2 * π * a}` for every finite Borel measure `σ` with
`⟪v, U t v⟫_ℂ = charFun σ t`. -/
theorem exists_tendsto_twistedAverage [CompleteSpace H] (hU : U.IsUnitary) (a : ℝ) (v : H) :
    ∃ w : H, (∀ t : ℝ, U t w = Complex.exp (2 * Real.pi * a * t * Complex.I) • w) ∧
      (∀ u : H, (∀ t : ℝ, U t u = Complex.exp (2 * Real.pi * a * t * Complex.I) • u) →
        ⟪u, v - w⟫_ℂ = 0) ∧
      Tendsto (fun T : ℝ ↦ (T⁻¹ : ℂ) •
          ∫ t in (0 : ℝ)..T, Complex.exp (-(2 * Real.pi * a * t * Complex.I)) • U t v)
        atTop (𝓝 w) ∧
      ∀ σ : Measure ℝ, IsFiniteMeasure σ →
        (∀ t : ℝ, ⟪v, U t v⟫_ℂ = charFun σ t) →
        ‖w‖ ^ 2 = σ.real {2 * Real.pi * a} := by
  let ω : ℝ := 2 * Real.pi * a
  let E := U.eigenspace hU.isComplexLinear ω
  let w : H := E.starProjection v
  have hcast (t : ℝ) : (ω : ℂ) * (t : ℂ) * Complex.I = 2 * Real.pi * a * t * Complex.I := by
    dsimp only [ω]
    push_cast
    ring
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · have hw : w ∈ E := by
      dsimp only [w]
      rw [Submodule.starProjection_apply]
      exact Submodule.coe_mem _
    rw [U.mem_eigenspace_iff hU.isComplexLinear ω w] at hw
    simpa only [hcast] using hw
  · intro u hu
    have hu_mem : u ∈ E := by
      rw [U.mem_eigenspace_iff hU.isComplexLinear ω u]
      simpa only [hcast] using hu
    have horth := Submodule.sub_starProjection_mem_orthogonal (K := E) v
    rw [Submodule.mem_orthogonal] at horth
    exact horth u hu_mem
  · have hlim := hU.tendsto_twistedAverage_starProjection ω v
    refine hlim.congr fun T ↦ ?_
    conv_rhs => rw [← Complex.ofReal_inv, Complex.coe_smul]
    congr 1
    refine intervalIntegral.integral_congr fun t _ ↦ ?_
    rw [hcast]
  · intro σ _ hσ
    exact hU.norm_starProjection_eigenspace_sq_eq_measureReal_singleton ω v hσ

end IsUnitary

end TauCeti.Semigroups.StronglyContinuousGroup

end
