/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.DirichletProblem
public import TauCeti.Analysis.PDE.Spectrum.Interval
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Separated solutions of the parabolic Dirichlet problem

Let `L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` have time-independent coefficients on an open set
`Ω ⊆ ℝⁿ`, and let `s ∈ H¹₀(Ω)` be a weak Dirichlet eigenfunction of `L` with eigenvalue `κ ∈ ℝ`:

`a(s, v) = κ ∫_Ω s v` for every `v ∈ H¹₀(Ω)`,

where `a` is the energy form `TauCeti.PDE.energyFormH1` of `L`. Then the separated function
`u(t) = e^{-κ (t - t₀)} s` is a weak solution of `∂ₜu + L u = 0` in the sense of
`TauCeti.PDE.exists_hasWeakLineDerivOn_gelfandDual_energyFormH1`: the curve
`t ↦ u(t) ∈ H⁻¹(Ω)` has the weak time derivative `u'(t) = -κ e^{-κ (t - t₀)} s`, and
`u'(t)(v) + a(u(t), v) = 0` for every `v ∈ H¹₀(Ω)`
(`TauCeti.PDE.hasWeakLineDerivOn_gelfandDual_valueL_exp_smul`,
`TauCeti.PDE.smul_gelfandDual_apply_add_energyFormH1_exp_smul_eq_zero`). No sign of `κ` and no
ellipticity is needed for this. For uniformly elliptic coefficients the weak solution is unique,
so every weak solution with initial value `s` is the separated one
(`TauCeti.PDE.eqOn_exp_smul_of_hasWeakLineDerivOn_gelfandDual_energyFormH1`).

The same construction runs backward in time: if `L` has eigenfunctions with arbitrarily large
eigenvalues, then `e^{κ (t - t₀)} s` solves the backward
equation `∂ₜu - L u = 0` and grows like `e^{κ (t - t₀)}`, so the backward problem admits no
stability estimate `‖u(t₁)‖ ≤ C ‖u(t₀)‖`
(`TauCeti.PDE.not_exists_forall_norm_le_mul_norm_of_sub_energyFormH1_eq_zero`).

On the interval `(a, b)` the sine modes `sin (k π (x - a) / (b - a))` are such eigenfunctions of
`-Δ`, with eigenvalues `κₖ = (k π / (b - a))²`. This gives two explicit computations.

* **The heat equation.** The weak solution of `∂ₜu - Δu = 0` on `(a, b)` with zero boundary values
  and the sine mode `s` as initial value is `e^{-κₖ (t - t₀)} s`
  (`TauCeti.PDE.eqOn_exp_smul_of_value_ae_eq_sin`), and both sides of its energy identity
  `‖u(t)‖² + 2 ∫_{t₀}^t ‖∂ₓu‖² = ‖u(t₀)‖²` equal `(b - a) / 2`
  (`TauCeti.PDE.norm_sq_add_two_mul_integral_energyFormH1_eq_of_value_ae_eq_sin`). On `(0, π)`
  with `k = 1` and `t₀ = 0` this is `u(t) = e^{-t} sin x`, and both sides are `π / 2`.
* **The backward heat equation is ill-posed.** For `∂ₜu + Δu = 0`, the equation `∂ₜu + L u = 0`
  for the operator `L = Δ` of the wrong sign, the separated solutions are `e^{κₖ (t - t₀)} s`.
  Their initial values all have `L²` norm `√((b - a) / 2)` while their values at any later time
  are unbounded in `k`, so no bound `‖u(t₁)‖ ≤ C ‖u(t₀)‖` holds for weak solutions
  (`TauCeti.PDE.not_exists_forall_norm_le_mul_norm_of_sub_energyFormH1_eq_zero_intervalDomain`).
  The energy form of `Δ` satisfies no Gårding inequality on `H¹₀(a, b)`
  (`TauCeti.PDE.not_exists_forall_mul_norm_sq_sub_mul_norm_sq_le_neg_energyFormH1`), and
  Gårding's inequality is the hypothesis of the existence and uniqueness theorems for the forward
  problem.

## Main declarations

* `TauCeti.PDE.hasWeakLineDerivOn_gelfandDual_valueL_exp_smul`: the weak time derivative of
  `t ↦ e^{μ (t - t₀)} s`.
* `TauCeti.PDE.smul_gelfandDual_apply_add_energyFormH1_exp_smul_eq_zero` and
  `TauCeti.PDE.smul_gelfandDual_apply_sub_energyFormH1_exp_smul_eq_zero`: separated solutions of
  the forward and backward equations.
* `TauCeti.PDE.eqOn_exp_smul_of_hasWeakLineDerivOn_gelfandDual_energyFormH1`: weak solutions with
  eigenfunction data are separated.
* `TauCeti.PDE.not_exists_forall_norm_le_mul_norm_of_sub_energyFormH1_eq_zero`: the backward
  problem admits no stability estimate when the eigenvalues are unbounded.
* `TauCeti.PDE.eqOn_exp_smul_of_value_ae_eq_sin`,
  `TauCeti.PDE.norm_sq_add_two_mul_integral_energyFormH1_eq_of_value_ae_eq_sin`,
  `TauCeti.PDE.not_exists_forall_norm_le_mul_norm_of_sub_energyFormH1_eq_zero_intervalDomain` and
  `TauCeti.PDE.not_exists_forall_mul_norm_sq_sub_mul_norm_sq_le_neg_energyFormH1`: the heat and
  backward heat equations on an interval.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §7.1.2 (energy estimates and
  uniqueness for weak solutions) and §2.3.3 (the backward heat equation).
-/

public section

open MeasureTheory Set TopologicalSpace
open scoped Real InnerProductSpace

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)}

section Separated

attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace

variable {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c : EuclideanSpace ℝ ι → ℝ} {s : W1p0 mu Omega 2} {κ t₀ t₁ : ℝ}

/-- The separated curve `t ↦ e^{μ (t - t₀)} s`, read in `H⁻¹(Ω)` through the Gelfand triple
`H¹₀(Ω) ↪ L²(Ω) ↪ H⁻¹(Ω)`, has the weak time derivative `t ↦ μ e^{μ (t - t₀)} s` on every
interval. -/
theorem hasWeakLineDerivOn_gelfandDual_valueL_exp_smul (s : W1p0 mu Omega 2) (μ t₀ t₁ : ℝ) :
    HasWeakLineDerivOn volume ⟨Ioo t₀ t₁, isOpen_Ioo⟩
      (fun t => (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).gelfandDual
        (W1p0.valueL (Real.exp (μ * (t - t₀)) • s)))
      (fun t => (μ * Real.exp (μ * (t - t₀))) •
        (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).gelfandDual (W1p0.valueL s)) 1 := by
  -- The scalar factor `t ↦ e^{μ (t - t₀)}` is smooth, and the curve is its image under the
  -- continuous linear map `r ↦ r • s` into `H⁻¹(Ω)`.
  have hscalar : HasWeakLineDerivOn volume ⟨Ioo t₀ t₁, isOpen_Ioo⟩
      (fun t => Real.exp (μ * (t - t₀))) (fun t => μ * Real.exp (μ * (t - t₀))) 1 := by
    refine hasWeakLineDerivOn_of_hasLineDerivAt
      ((Continuous.locallyIntegrable (by fun_prop)).locallyIntegrableOn _)
      ((Continuous.locallyIntegrable (by fun_prop)).locallyIntegrableOn _) fun t _ => ?_
    have h := (((hasDerivAt_id t).sub_const t₀).const_mul μ).exp
    rw [mul_one, mul_comm] at h
    simpa using h.hasFDerivAt.hasLineDerivAt 1
  simpa only [ContinuousLinearMap.toSpanSingleton_apply, map_smul] using hscalar.clm_comp
    (ContinuousLinearMap.toSpanSingleton ℝ
      ((W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).gelfandDual (W1p0.valueL s)))

/-- **Separated solutions.** If `s ∈ H¹₀(Ω)` is a weak Dirichlet eigenfunction of `L` with
eigenvalue `κ`, `a(s, v) = κ ∫_Ω s v` for every `v`, then `u(t) = e^{-κ (t - t₀)} s` satisfies the
weak form `u'(t)(v) + a(u(t), v) = 0` of `∂ₜu + L u = 0`, with the weak time derivative
`u'(t) = -κ e^{-κ (t - t₀)} s` of `TauCeti.PDE.hasWeakLineDerivOn_gelfandDual_valueL_exp_smul`. -/
theorem smul_gelfandDual_apply_add_energyFormH1_exp_smul_eq_zero
    (hs : ∀ v : W1p0 mu Omega 2, energyFormH1 a b c (s : W1p mu Omega 2) (v : W1p mu Omega 2) =
      κ * ⟪W1p0.valueL s, W1p0.valueL v⟫_ℝ) (t : ℝ) (v : W1p0 mu Omega 2) :
    ((-κ * Real.exp (-κ * (t - t₀))) •
        (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).gelfandDual (W1p0.valueL s)) v +
      energyFormH1 a b c ((Real.exp (-κ * (t - t₀)) • s : W1p0 mu Omega 2) : W1p mu Omega 2)
        (v : W1p mu Omega 2) = 0 := by
  rw [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.gelfandDual_apply, smul_eq_mul,
    Submodule.coe_smul, energyFormH1_smul_left, hs]
  ring

/-- **Separated solutions of the backward equation.** If `s ∈ H¹₀(Ω)` is a weak Dirichlet
eigenfunction of `L` with eigenvalue `κ`, then `u(t) = e^{κ (t - t₀)} s`, with the weak time
derivative `u'(t) = κ e^{κ (t - t₀)} s` of
`TauCeti.PDE.hasWeakLineDerivOn_gelfandDual_valueL_exp_smul`, satisfies the weak form
`u'(t)(v) - a(u(t), v) = 0` of the backward equation `∂ₜu - L u = 0`. -/
theorem smul_gelfandDual_apply_sub_energyFormH1_exp_smul_eq_zero
    (hs : ∀ v : W1p0 mu Omega 2, energyFormH1 a b c (s : W1p mu Omega 2) (v : W1p mu Omega 2) =
      κ * ⟪W1p0.valueL s, W1p0.valueL v⟫_ℝ) (t : ℝ) (v : W1p0 mu Omega 2) :
    ((κ * Real.exp (κ * (t - t₀))) •
        (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).gelfandDual (W1p0.valueL s)) v -
      energyFormH1 a b c ((Real.exp (κ * (t - t₀)) • s : W1p0 mu Omega 2) : W1p mu Omega 2)
        (v : W1p mu Omega 2) = 0 := by
  rw [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.gelfandDual_apply, smul_eq_mul,
    Submodule.coe_smul, energyFormH1_smul_left, hs]
  ring

/-- A curve `t ↦ φ t • x` with continuous `φ` is square integrable on every bounded interval.
Stated for an abstract normed space, so that instance search stays cheap when it is applied in
`H⁻¹(Ω)`. -/
private theorem memLp_smul_const_restrict_Ioo {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : ℝ → ℝ} (hφ : Continuous φ) (x : F) (t₀ t₁ : ℝ) :
    MemLp (fun t => φ t • x) 2 (volume.restrict (Ioo t₀ t₁)) :=
  (hφ.smul continuous_const).continuousOn.memLp_restrict_of_subset_isCompact isCompact_Icc
    measurableSet_Ioo Ioo_subset_Icc_self 2

/-- **The backward equation is ill-posed when the eigenvalues are unbounded.** Suppose that `L`
has weak Dirichlet eigenfunctions with arbitrarily large eigenvalues, as `-Δ` does on a bounded
domain. Then weak solutions of the backward equation
`∂ₜu - L u = 0` on `(t₀, t₁) × Ω`, `t₀ < t₁`, with zero boundary values, whose weak form is
`u'(t)(v) - a(u(t), v) = 0`, admit no bound `‖u(t₁)‖_{L²} ≤ C ‖u(t₀)‖_{L²}`: the separated solution
`e^{κ (t - t₀)} s` of an eigenfunction `s` with eigenvalue `κ` has
`‖u(t₁)‖ = e^{κ (t₁ - t₀)} ‖u(t₀)‖`. -/
theorem not_exists_forall_norm_le_mul_norm_of_sub_energyFormH1_eq_zero (ht : t₀ < t₁)
    (hev : ∀ C : ℝ, ∃ κ : ℝ, ∃ s : W1p0 mu Omega 2, C < κ ∧ 0 < ‖W1p0.valueL s‖ ∧
      ∀ v : W1p0 mu Omega 2, energyFormH1 a b c (s : W1p mu Omega 2) (v : W1p mu Omega 2) =
        κ * ⟪W1p0.valueL s, W1p0.valueL v⟫_ℝ) :
    ¬ ∃ C : ℝ, ∀ (u : ℝ → W1p0 mu Omega 2) (u' : ℝ → StrongDual ℝ (W1p0 mu Omega 2))
      (w : ℝ → Lp ℝ 2 (mu.restrict Omega)),
      HasWeakLineDerivOn volume ⟨Ioo t₀ t₁, isOpen_Ioo⟩
        (fun t => (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).gelfandDual
          (W1p0.valueL (u t))) u' 1 →
      MemLp u 2 (volume.restrict (Ioo t₀ t₁)) → MemLp u' 2 (volume.restrict (Ioo t₀ t₁)) →
      (∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), ∀ v : W1p0 mu Omega 2,
        u' t v - energyFormH1 a b c (u t : W1p mu Omega 2) (v : W1p mu Omega 2) = 0) →
      ContinuousOn w (Icc t₀ t₁) →
      (fun t => W1p0.valueL (u t)) =ᵐ[volume.restrict (Ioo t₀ t₁)] w →
      ‖w t₁‖ ≤ C * ‖w t₀‖ := by
  rintro ⟨C, hC⟩
  obtain ⟨κ, s, hκ, hpos, hs⟩ := hev (C / (t₁ - t₀))
  have hsol := hC (fun t => Real.exp (κ * (t - t₀)) • s)
    (fun t => (κ * Real.exp (κ * (t - t₀))) •
      (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).gelfandDual (W1p0.valueL s))
    (fun t => Real.exp (κ * (t - t₀)) • W1p0.valueL s)
    (hasWeakLineDerivOn_gelfandDual_valueL_exp_smul s κ t₀ t₁)
    (memLp_smul_const_restrict_Ioo (by fun_prop) s t₀ t₁)
    (memLp_smul_const_restrict_Ioo (by fun_prop)
      ((W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).gelfandDual (W1p0.valueL s)) t₀ t₁)
    (ae_of_all _ fun t v => smul_gelfandDual_apply_sub_energyFormH1_exp_smul_eq_zero hs t v)
    (Continuous.continuousOn (by fun_prop)) (ae_of_all _ fun t => map_smul _ _ _)
  rw [norm_smul, norm_smul, sub_self, mul_zero, Real.exp_zero, norm_one, one_mul,
    Real.norm_of_nonneg (Real.exp_pos _).le] at hsol
  have hle := le_of_mul_le_mul_right hsol hpos
  rw [div_lt_iff₀ (sub_pos.2 ht)] at hκ
  linarith [Real.add_one_le_exp (κ * (t₁ - t₀))]

variable [DecidableEq ι] {lam Lam beta gamma : ℝ}

/-- **Weak solutions with eigenfunction data are separated.** Let the time-independent
coefficients of `L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` be a.e. strongly measurable on `Ω`, `a`
uniformly elliptic with constants `λ, Λ`, `‖b‖ ≤ β` and `|c| ≤ γ`, and let `s ∈ H¹₀(Ω)` be a weak
Dirichlet eigenfunction of `L` with eigenvalue `κ`. Then every weak solution of `∂ₜu + L u = 0` on
`(t₀, t₁) × Ω` with zero boundary values and initial value `s`, in the sense of
`TauCeti.PDE.exists_hasWeakLineDerivOn_gelfandDual_energyFormH1`, is `e^{-κ (t - t₀)} s`: its
continuous `L²(Ω)`-valued representative is `w(t) = e^{-κ (t - t₀)} s` on `[t₀, t₁]`. -/
theorem eqOn_exp_smul_of_hasWeakLineDerivOn_gelfandDual_energyFormH1
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hell : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hs : ∀ v : W1p0 mu Omega 2, energyFormH1 a b c (s : W1p mu Omega 2) (v : W1p mu Omega 2) =
      κ * ⟪W1p0.valueL s, W1p0.valueL v⟫_ℝ)
    {u : ℝ → W1p0 mu Omega 2} {u' : ℝ → StrongDual ℝ (W1p0 mu Omega 2)}
    {w : ℝ → Lp ℝ 2 (mu.restrict Omega)}
    (hd : HasWeakLineDerivOn volume ⟨Ioo t₀ t₁, isOpen_Ioo⟩
      (fun t => (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).gelfandDual
        (W1p0.valueL (u t))) u' 1)
    (hu : MemLp u 2 (volume.restrict (Ioo t₀ t₁)))
    (hu' : MemLp u' 2 (volume.restrict (Ioo t₀ t₁)))
    (heq : ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), ∀ v : W1p0 mu Omega 2,
      u' t v + energyFormH1 a b c (u t : W1p mu Omega 2) (v : W1p mu Omega 2) = 0)
    (hw : ContinuousOn w (Icc t₀ t₁))
    (hae : (fun t => W1p0.valueL (u t)) =ᵐ[volume.restrict (Ioo t₀ t₁)] w)
    (h₀ : w t₀ = W1p0.valueL s) :
    EqOn w (fun t => Real.exp (-κ * (t - t₀)) • W1p0.valueL s) (Icc t₀ t₁) := by
  have h₂ :=
    hasWeakLineDerivOn_gelfandDual_valueL_exp_smul (mu := mu) (Omega := Omega) s (-κ) t₀ t₁
  have hae₂ : (fun t => W1p0.valueL (Real.exp (-κ * (t - t₀)) • s))
      =ᵐ[volume.restrict (Ioo t₀ t₁)] fun t => Real.exp (-κ * (t - t₀)) • W1p0.valueL s :=
    ae_of_all _ fun t => map_smul _ _ _
  have hw₂ : ContinuousOn (fun t => Real.exp (-κ * (t - t₀)) • W1p0.valueL s) (Icc t₀ t₁) :=
    Continuous.continuousOn (by fun_prop)
  have h₀' : w t₀ = Real.exp (-κ * (t₀ - t₀)) • W1p0.valueL s := by
    rw [h₀, sub_self, mul_zero, Real.exp_zero, one_smul]
  exact eqOn_of_hasWeakLineDerivOn_gelfandDual_energyFormH1 (a := fun _ => a) (b := fun _ => b)
    (c := fun _ => c) (f := fun _ => 0) ha.comp_snd hb.comp_snd hc.comp_snd
    (ae_of_all _ fun _ => hell) (ae_of_all _ fun _ => hb_bound) (ae_of_all _ fun _ => hc_bound)
    hd h₂ hu hu' (memLp_smul_const_restrict_Ioo (by fun_prop) s t₀ t₁)
    (memLp_smul_const_restrict_Ioo (by fun_prop)
      ((W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)).gelfandDual (W1p0.valueL s)) t₀ t₁)
    heq (ae_of_all _ fun t v => smul_gelfandDual_apply_add_energyFormH1_exp_smul_eq_zero hs t v)
    hw hae hw₂ hae₂ h₀'

end Separated

section Interval

attribute [local instance] W1p0.instNormedAddCommGroup

variable {a b t₀ t₁ : ℝ}

/-- **The heat equation with a sine mode as initial value.** On the interval `(a, b)`, every weak
solution of `∂ₜu - Δu = 0` in `(t₀, t₁) × (a, b)` with zero boundary values and initial value the
sine mode `s = sin (k π (x - a) / (b - a))` is `e^{-(k π / (b - a))² (t - t₀)} s`. On `(0, π)` with
`k = 1` this is `u(t) = e^{-(t - t₀)} sin x`. -/
theorem eqOn_exp_smul_of_value_ae_eq_sin (hab : a < b) (k : ℕ)
    {s : W1p0 volume (intervalDomain a b) 2}
    (hs : W1p.value (s : W1p volume (intervalDomain a b) 2)
      =ᵐ[volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))]
        fun x => Real.sin (k * π * (x 0 - a) / (b - a)))
    {u : ℝ → W1p0 volume (intervalDomain a b) 2}
    {u' : ℝ → StrongDual ℝ (W1p0 volume (intervalDomain a b) 2)}
    {w : ℝ → Lp ℝ 2 (volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1))))}
    (hd : HasWeakLineDerivOn volume ⟨Ioo t₀ t₁, isOpen_Ioo⟩
      (fun t => (W1p0.valueL (mu := volume) (Omega := intervalDomain a b) (p := 2)).gelfandDual
        (W1p0.valueL (u t))) u' 1)
    (hu : MemLp u 2 (volume.restrict (Ioo t₀ t₁)))
    (hu' : MemLp u' 2 (volume.restrict (Ioo t₀ t₁)))
    (heq : ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), ∀ v : W1p0 volume (intervalDomain a b) 2,
      u' t v + energyFormH1 (fun _ => 1) 0 0 (u t : W1p volume (intervalDomain a b) 2)
        (v : W1p volume (intervalDomain a b) 2) = 0)
    (hw : ContinuousOn w (Icc t₀ t₁))
    (hae : (fun t => W1p0.valueL (u t)) =ᵐ[volume.restrict (Ioo t₀ t₁)] w)
    (h₀ : w t₀ = W1p0.valueL s) :
    EqOn w (fun t => Real.exp (-(k * π / (b - a)) ^ 2 * (t - t₀)) • W1p0.valueL s)
      (Icc t₀ t₁) := by
  exact eqOn_exp_smul_of_hasWeakLineDerivOn_gelfandDual_energyFormH1 (lam := 1) (Lam := 1)
    (beta := 0) (gamma := 0) aestronglyMeasurable_const aestronglyMeasurable_const
    aestronglyMeasurable_const (uniformlyEllipticOn_const_one_one _)
    (fun _ _ => by simp) (fun _ _ => (norm_eq_zero.2 rfl).le)
    (energyFormH1_eq_of_value_ae_eq_sin hab k hs) hd hu hu' heq hw hae h₀

/-- **The energy identity for a sine mode.** On the interval `(a, b)`, every weak solution of
`∂ₜu - Δu = 0` with zero boundary values and initial value the sine mode
`s = sin (k π (x - a) / (b - a))`, `k ≥ 1`, satisfies

`‖u(t)‖²_{L²} + 2 ∫_{t₀}^t ‖∂ₓu(r)‖²_{L²} dr = (b - a) / 2 = ‖s‖²_{L²}`

for every `t ∈ [t₀, t₁]`, where `∫ ‖∂ₓu‖²` is the energy form of `-Δ`. On `(0, π)` with `k = 1`,
where the solution is `e^{-(t - t₀)} sin x` (`TauCeti.PDE.eqOn_exp_smul_of_value_ae_eq_sin`),
both sides are `π / 2`. -/
theorem norm_sq_add_two_mul_integral_energyFormH1_eq_of_value_ae_eq_sin (hab : a < b) {k : ℕ}
    (hk : 0 < k) {s : W1p0 volume (intervalDomain a b) 2}
    (hs : W1p.value (s : W1p volume (intervalDomain a b) 2)
      =ᵐ[volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))]
        fun x => Real.sin (k * π * (x 0 - a) / (b - a)))
    {u : ℝ → W1p0 volume (intervalDomain a b) 2}
    {u' : ℝ → StrongDual ℝ (W1p0 volume (intervalDomain a b) 2)}
    {w : ℝ → Lp ℝ 2 (volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1))))}
    (hd : HasWeakLineDerivOn volume ⟨Ioo t₀ t₁, isOpen_Ioo⟩
      (fun t => (W1p0.valueL (mu := volume) (Omega := intervalDomain a b) (p := 2)).gelfandDual
        (W1p0.valueL (u t))) u' 1)
    (hu : MemLp u 2 (volume.restrict (Ioo t₀ t₁)))
    (hu' : MemLp u' 2 (volume.restrict (Ioo t₀ t₁)))
    (heq : ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), ∀ v : W1p0 volume (intervalDomain a b) 2,
      u' t v + energyFormH1 (fun _ => 1) 0 0 (u t : W1p volume (intervalDomain a b) 2)
        (v : W1p volume (intervalDomain a b) 2) = 0)
    (hw : ContinuousOn w (Icc t₀ t₁))
    (hae : (fun t => W1p0.valueL (u t)) =ᵐ[volume.restrict (Ioo t₀ t₁)] w)
    (h₀ : w t₀ = W1p0.valueL s) {t : ℝ} (ht : t ∈ Icc t₀ t₁) :
    ‖w t‖ ^ 2 + 2 * ∫ r in t₀..t, energyFormH1 (fun _ => 1) 0 0
        (u r : W1p volume (intervalDomain a b) 2) (u r : W1p volume (intervalDomain a b) 2) =
      (b - a) / 2 := by
  rw [norm_sq_add_two_mul_integral_energyFormH1_eq_norm_sq_of_hasWeakLineDerivOn_gelfandDual
    (a := fun _ _ => 1) (b := fun _ => 0) (c := fun _ => 0) hd hu hu' heq hw hae
    ⟨le_rfl, ht.1.trans ht.2⟩ ht, h₀, W1p0.valueL_apply]
  exact norm_value_sq_of_value_ae_eq_sin hab hk hs

/-- **The backward heat equation is ill-posed.** On the interval `(a, b)` and a time interval
`(t₀, t₁)`, `t₀ < t₁`, consider weak solutions of the backward heat equation `∂ₜu + Δu = 0` with
zero boundary values, whose weak form is `u'(t)(v) - ∫ ∂ₓu(t) ∂ₓv = 0` for `v ∈ H¹₀(a, b)`: the
equation `∂ₜu + L u = 0` for the operator `L = Δ` of the wrong sign. They admit no bound
`‖u(t₁)‖_{L²} ≤ C ‖u(t₀)‖_{L²}`. The separated solutions `e^{(k π / (b - a))² (t - t₀)} s`, `s` the
`k`-th sine mode, have the initial norm `√((b - a) / 2)` for every `k ≥ 1`, while their norm at
`t₁` grows without bound in `k`. -/
theorem not_exists_forall_norm_le_mul_norm_of_sub_energyFormH1_eq_zero_intervalDomain
    (hab : a < b) (ht : t₀ < t₁) :
    ¬ ∃ C : ℝ, ∀ (u : ℝ → W1p0 volume (intervalDomain a b) 2)
      (u' : ℝ → StrongDual ℝ (W1p0 volume (intervalDomain a b) 2))
      (w : ℝ → Lp ℝ 2 (volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1))))),
      HasWeakLineDerivOn volume ⟨Ioo t₀ t₁, isOpen_Ioo⟩
        (fun t => (W1p0.valueL (mu := volume) (Omega := intervalDomain a b) (p := 2)).gelfandDual
          (W1p0.valueL (u t))) u' 1 →
      MemLp u 2 (volume.restrict (Ioo t₀ t₁)) → MemLp u' 2 (volume.restrict (Ioo t₀ t₁)) →
      (∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), ∀ v : W1p0 volume (intervalDomain a b) 2,
        u' t v - energyFormH1 (fun _ => 1) 0 0 (u t : W1p volume (intervalDomain a b) 2)
          (v : W1p volume (intervalDomain a b) 2) = 0) →
      ContinuousOn w (Icc t₀ t₁) →
      (fun t => W1p0.valueL (u t)) =ᵐ[volume.restrict (Ioo t₀ t₁)] w →
      ‖w t₁‖ ≤ C * ‖w t₀‖ :=
  not_exists_forall_norm_le_mul_norm_of_sub_energyFormH1_eq_zero ht
    (exists_lt_and_energyFormH1_eq_intervalDomain hab)

/-- **No Gårding inequality for the backward heat equation.** The energy form of `Δ` on
`H¹₀(a, b)`, `-∫ |v'|²`, satisfies no Gårding inequality `α ‖v‖²_{H¹} - β ‖v‖²_{L²} ≤ -∫ |v'|²`
with `α > 0`: on the `k`-th sine mode it would give `α - β ≤ -(k π / (b - a))²` for every
`k ≥ 1`. Gårding's inequality is the hypothesis of the existence and uniqueness theorems for the
parabolic Dirichlet problem, and the backward problem is ill-posed
(`TauCeti.PDE.not_exists_forall_norm_le_mul_norm_of_sub_energyFormH1_eq_zero_intervalDomain`).
-/
theorem not_exists_forall_mul_norm_sq_sub_mul_norm_sq_le_neg_energyFormH1 (hab : a < b) :
    ¬ ∃ α > 0, ∃ β : ℝ, ∀ v : W1p0 volume (intervalDomain a b) 2,
      α * ‖v‖ ^ 2 - β * ‖W1p0.valueL v‖ ^ 2 ≤
        -energyFormH1 (fun _ => 1) 0 0 (v : W1p volume (intervalDomain a b) 2)
          (v : W1p volume (intervalDomain a b) 2) := by
  rintro ⟨α, hα, β, h⟩
  obtain ⟨k, hk, hlt⟩ := exists_lt_sq_natCast_mul_pi_div hab.ne (β - α)
  obtain ⟨s, hs, -⟩ := exists_value_ae_eq_sin_and_energyFormH1_eq hab k
  have hs' := h s
  rw [energyFormH1_self_eq_of_value_ae_eq_sin hab hk hs, W1p0.valueL_apply,
    norm_value_sq_of_value_ae_eq_sin hab hk hs] at hs'
  have hle : ‖W1p.value (s : W1p volume (intervalDomain a b) 2)‖ ^ 2 ≤ ‖s‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (W1p.norm_value_le _) 2
  rw [norm_value_sq_of_value_ae_eq_sin hab hk hs] at hle
  nlinarith [mul_le_mul_of_nonneg_left hle hα.le]

end Interval

end PDE

end TauCeti
