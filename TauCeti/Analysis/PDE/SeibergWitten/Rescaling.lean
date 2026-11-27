/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.AlternatingForm
public import TauCeti.Analysis.PDE.SeibergWitten.CutoffCurrent
public import TauCeti.Analysis.PDE.SeibergWitten.QuadraticTwoForm
import TauCeti.Analysis.Calculus.DifferentialForm.Basic

/-!
# Rescaling large-parameter Seiberg–Witten fields to the flat limiting equations

On a symplectic four-manifold Taubes perturbs the Seiberg–Witten equations by a large multiple `r`
of the symplectic form. In a flat chart `V`, with the connection on the line `E` written `a = i b`
and the normalized spinor `χ`, the equations read

`D_b χ = 0`,  `F + ⋆F = (r / 4) ω - q(√r χ) - η`,  `F = i F_a = -db`,

where `q` is the quadratic two-form `TauCeti.SeibergWitten.quadraticTwoForm`, indexed by real
forms as in `TauCeti.Analysis.PDE.SeibergWitten.LargeParameterCurvature`. Their natural length
scale is `h = (2 r)^(-1/2)`. Blowing a solution up by `h` about a point `x₀`, that is pulling it
back along the dilation `z ↦ x₀ + h • z`, gives the connection form `z ↦ h • b (x₀ + h • z)` and
the spinor `z ↦ χ (x₀ + h • z)`. Covariant derivatives scale by `h`
(`TauCeti.SeibergWitten.covariantDeriv_comp_add_smul`) and curvature by `h²`
(`TauCeti.extDeriv_comp_add_smul`), and since `h² r = 1 / 2` the rescaled fields solve

`D_b χ = 0`,  `F + ⋆F = ω / 8 - q(χ) / 2 - h² η`,

the flat limiting equations of `TauCeti.Analysis.PDE.SeibergWitten.FlatLimit` with the forcing
`h² η`, which tends to zero as `r → ∞` for bounded `η`. Conversely the rescaled equations give back
the original ones. The spinor is written in a constant frame `(w j)` of the positive half-spinors,
`χ = ∑ⱼ αⱼ wⱼ`, with complex coefficients `αⱼ`, for instance `(u₀, v₀)` with `u₀` spanning the
canonical line, so that `D_b χ = ∑ₖ ∑ⱼ (∇_b αⱼ)(eₖ) c(eₖ) wⱼ` for an orthonormal basis `(eₖ)`.

The flat limiting equations are closed under convergence of `1`-jets at a point: if the
connection forms and coefficients of solutions converge at `y`, together with their first
derivatives, and the forcing tends to zero, the limit solves the unforced flat equations at `y`.
So any limit of blown-up solutions, in this sense, solves the flat limiting equations
(`sum_sum_covariantDeriv_smul_eq_zero_and_add_hodgeStar_eq_of_tendsto_rescale`).
The flat limiting equations are also invariant under unit gauge transformations
`(b, α) ↦ (b - Im (u⁻¹ du), u α)`: the Dirac expression is multiplied by `u` and the curvature and
`q(χ)` are unchanged. So limits of gauge transforms of blown-up solutions solve them too
(`sum_sum_covariantDeriv_smul_eq_zero_and_add_hodgeStar_eq_of_tendsto_rescale_sub_phaseForm`).
This is how the plane vortex equations, which are the base-independent solutions of the flat
limiting equations on the canonical line, arise from Seiberg–Witten solutions at large `r`. The
compactness that produces convergent subsequences of blown-up solutions, modulo gauge and given
uniform bounds on the blown-up fields, is in
`TauCeti.Analysis.PDE.SeibergWitten.Rescaling.Compactness`.

## Main results

* `TauCeti.SeibergWitten.smul_add_hodgeStar_smul_eq_iff`: the curvature equation at parameter `r`
  for `F` is the flat curvature equation for `h² F` with forcing `h² η`, when `h² r = 1 / 2`.
* `TauCeti.SeibergWitten.sum_sum_covariantDeriv_comp_add_smul_eq_zero_iff` and
  `TauCeti.SeibergWitten.add_hodgeStar_extDeriv_comp_add_smul_eq_iff`: the Dirac and curvature
  equations of the blown-up fields at `y` are those of the original fields at `x₀ + h • y`.
* `TauCeti.SeibergWitten.sum_sum_covariantDeriv_sub_phaseForm_mul_smul`: a unit gauge multiplies
  the Dirac expression by `u`.
* `sum_sum_covariantDeriv_sub_phaseForm_mul_smul_eq_zero_and_add_hodgeStar_eq_iff`: gauge
  invariance of the flat limiting equations.
* `sum_sum_covariantDeriv_smul_eq_zero_and_add_hodgeStar_eq_of_tendsto`: the flat limiting
  equations pass to limits of `1`-jets.
* `sum_sum_covariantDeriv_smul_eq_zero_and_add_hodgeStar_eq_of_tendsto_rescale`: limits of
  blown-up large-parameter solutions solve the flat limiting equations.
* `sum_sum_covariantDeriv_smul_eq_zero_and_add_hodgeStar_eq_of_tendsto_rescale_sub_phaseForm`:
  limits of gauge transforms of blown-up solutions solve the flat limiting equations.

## References

* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Sections 2 and 4.
-/

public section

open CliffordAlgebra Filter Module
open scoped Topology

namespace TauCeti.SeibergWitten

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} {o : Orientation ℝ V (Fin 4)}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W} (hkl : 2 + 2 = finrank ℝ V)

/-- The dimension `Fact` makes the oriented four-space finite-dimensional. -/
local instance instFiniteDimensionalRealRescaling : FiniteDimensional ℝ V :=
  .of_fact_finrank_eq_succ 3

/-! ### The equations under rescaling -/

/-- **The curvature equation under rescaling.** If `h² r = 1 / 2`, the large-parameter curvature
equation `F + ⋆F = (r / 4) ω - q(√r ψ) - η` holds exactly when `h² F` solves the flat curvature
equation `h² F + ⋆(h² F) = ω / 8 - q(ψ) / 2 - h² η`. -/
theorem smul_add_hodgeStar_smul_eq_iff {h r : ℝ} (hr : h ^ 2 * r = 1 / 2) (ω F η : ⋀[ℝ]^2 V)
    (ψ : positiveHalfSpinors o ρ) :
    h ^ 2 • F + o.hodgeStar hkl (h ^ 2 • F) =
        (8⁻¹ : ℝ) • ω - (2⁻¹ : ℝ) • (quadraticTwoForm o ρ hkl ψ : ⋀[ℝ]^2 V) - h ^ 2 • η ↔
      F + o.hodgeStar hkl F =
        (r / 4) • ω - (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • ψ) : ⋀[ℝ]^2 V) - η := by
  have hh : h ^ 2 ≠ 0 := by
    rintro h0
    rw [h0, zero_mul] at hr
    norm_num at hr
  have hr₀ : 0 ≤ r := by
    by_contra! hneg
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg h) hneg.le]
  have h₈ : (8⁻¹ : ℝ) = h ^ 2 * (r / 4) := by linear_combination -hr / 4
  have h₂ : (2⁻¹ : ℝ) = h ^ 2 * r := by linear_combination -hr
  rw [quadraticTwoForm_sqrt_smul o ρ hkl hr₀, Submodule.coe_smul, map_smul, ← smul_add, h₈, h₂,
    ← smul_smul, ← smul_smul, ← smul_sub, ← smul_sub, (smul_right_injective _ hh).eq_iff]

variable {ν κ : Type*} [Fintype ν] [Fintype κ]

omit [Fact (finrank ℝ V = 4)] [FiniteDimensional ℂ W] in
/-- **The Dirac equation under rescaling.** For `h ≠ 0`, the Dirac equation
`∑ₖ ∑ⱼ (∇_b αⱼ)(eₖ) c(eₖ) wⱼ = 0` of the spinor `∑ⱼ αⱼ wⱼ` holds at `x₀ + h • y` exactly when the
Dirac equation of the blown-up fields `z ↦ h • b (x₀ + h • z)`, `z ↦ αⱼ (x₀ + h • z)` holds at
`y`. -/
theorem sum_sum_covariantDeriv_comp_add_smul_eq_zero_iff {h : ℝ} (hh : h ≠ 0) (e : ν → V)
    (w : κ → W) (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (α : κ → V → ℂ) (x₀ y : V) :
    ∑ k, ∑ j, covariantDeriv (fun z ↦ h • b (x₀ + h • z)) (fun z ↦ α j (x₀ + h • z)) y (e k) •
        ρ (ι Q (e k)) (w j) = 0 ↔
      ∑ k, ∑ j, covariantDeriv b (α j) (x₀ + h • y) (e k) • ρ (ι Q (e k)) (w j) = 0 := by
  simp only [covariantDeriv_comp_add_smul, FunLike.coe_smul, Pi.smul_apply, Complex.real_smul,
    mul_smul, ← Finset.smul_sum, smul_eq_zero, Complex.ofReal_eq_zero, hh, false_or]

/-- **The curvature equation of the blown-up connection.** If `h² r = 1 / 2`, the curvature
`F = i F_a = -db` of a connection form `b` solves the large-parameter equation
`F + ⋆F = (r / 4) ω - q(√r ψ) - η` at `x₀ + h • y` exactly when the curvature of the blown-up
connection form `z ↦ h • b (x₀ + h • z)` solves the flat equation `F + ⋆F = ω / 8 - q(ψ) / 2 - h² η`
at `y`. -/
theorem add_hodgeStar_extDeriv_comp_add_smul_eq_iff {h r : ℝ} (hr : h ^ 2 * r = 1 / 2)
    (ω η : ⋀[ℝ]^2 V) (ψ : positiveHalfSpinors o ρ) (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (x₀ y : V) :
    (alternatingFormEquiv V 2).symm (-extDeriv (fun z ↦ h • b (x₀ + h • z)) y) +
        o.hodgeStar hkl
          ((alternatingFormEquiv V 2).symm (-extDeriv (fun z ↦ h • b (x₀ + h • z)) y)) =
        (8⁻¹ : ℝ) • ω - (2⁻¹ : ℝ) • (quadraticTwoForm o ρ hkl ψ : ⋀[ℝ]^2 V) - h ^ 2 • η ↔
      (alternatingFormEquiv V 2).symm (-extDeriv b (x₀ + h • y)) +
          o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (-extDeriv b (x₀ + h • y))) =
        (r / 4) • ω - (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • ψ) : ⋀[ℝ]^2 V) - η := by
  have hF : (alternatingFormEquiv V 2).symm (-extDeriv (fun z ↦ h • b (x₀ + h • z)) y) =
      h ^ 2 • (alternatingFormEquiv V 2).symm (-extDeriv b (x₀ + h • y)) := by
    rw [← Pi.smul_def, extDeriv_fun_smul, extDeriv_comp_add_smul, smul_smul, ← sq,
      ← smul_neg, map_smul]
  rw [hF]
  exact smul_add_hodgeStar_smul_eq_iff hkl hr ω _ η ψ

/-! ### Gauge invariance of the flat limiting equations -/

omit [Fact (finrank ℝ V = 4)] [FiniteDimensional ℂ W] in
/-- **The Dirac expression under a unit gauge.** If `|u| = 1` near `y`, the gauge transformation
`(b, α) ↦ (b - Im (u⁻¹ du), u α)` multiplies the Dirac expression
`∑ₖ ∑ⱼ (∇_b αⱼ)(eₖ) c(eₖ) wⱼ` at `y` by `u y`. -/
theorem sum_sum_covariantDeriv_sub_phaseForm_mul_smul (e : ν → V) (w : κ → W)
    {b : V → V [⋀^Fin 1]→L[ℝ] ℝ} {α : κ → V → ℂ} {u : V → ℂ} {y : V}
    (hu : ∀ᶠ z in 𝓝 y, ‖u z‖ = 1) (hud : DifferentiableAt ℝ u y)
    (hα : ∀ j, DifferentiableAt ℝ (α j) y) :
    ∑ i, ∑ j, covariantDeriv (b - phaseForm u) (u * α j) y (e i) • ρ (ι Q (e i)) (w j) =
      u y • ∑ i, ∑ j, covariantDeriv b (α j) y (e i) • ρ (ι Q (e i)) (w j) := by
  simp only [covariantDeriv_sub_phaseForm_mul hu hud (hα _), Finset.smul_sum,
    smul_apply, smul_eq_mul, mul_smul]

/-- **Gauge invariance of the flat limiting equations.** For a gauge `u` of class `C²` near `y`
with `|u| = 1` near `y`, the gauge transform `(b - Im (u⁻¹ du), u α)` solves the flat limiting
equations `∑ₖ ∑ⱼ (∇_b αⱼ)(eₖ) c(eₖ) wⱼ = 0`, `F + ⋆F = ω / 8 - q(∑ⱼ αⱼ wⱼ) / 2 - η` at `y`
exactly when `(b, α)` does. -/
theorem sum_sum_covariantDeriv_sub_phaseForm_mul_smul_eq_zero_and_add_hodgeStar_eq_iff
    (e : ν → V) (w : κ → positiveHalfSpinors o ρ) (ω η : ⋀[ℝ]^2 V)
    {b : V → V [⋀^Fin 1]→L[ℝ] ℝ} {α : κ → V → ℂ} {u : V → ℂ} {y : V}
    (hu : ∀ᶠ z in 𝓝 y, ‖u z‖ = 1) (hu₂ : ContDiffAt ℝ 2 u y) (hb : DifferentiableAt ℝ b y)
    (hα : ∀ j, DifferentiableAt ℝ (α j) y) :
    (∑ i, ∑ j, covariantDeriv (b - phaseForm u) (u * α j) y (e i) •
          ρ (ι Q (e i)) (w j : W) = 0 ∧
        (alternatingFormEquiv V 2).symm (-extDeriv (b - phaseForm u) y) +
            o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (-extDeriv (b - phaseForm u) y)) =
          (8⁻¹ : ℝ) • ω -
            (2⁻¹ : ℝ) • (quadraticTwoForm o ρ hkl (∑ j, (u * α j) y • w j) : ⋀[ℝ]^2 V) - η) ↔
      (∑ i, ∑ j, covariantDeriv b (α j) y (e i) • ρ (ι Q (e i)) (w j : W) = 0 ∧
        (alternatingFormEquiv V 2).symm (-extDeriv b y) +
            o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (-extDeriv b y)) =
          (8⁻¹ : ℝ) • ω -
            (2⁻¹ : ℝ) • (quadraticTwoForm o ρ hkl (∑ j, α j y • w j) : ⋀[ℝ]^2 V) - η) := by
  have hu₁ : ‖u y‖ = 1 := hu.self_of_nhds
  have hu₀ : u y ≠ 0 := norm_ne_zero_iff.1 (by rw [hu₁]; exact one_ne_zero)
  have hφ : DifferentiableAt ℝ (phaseForm u) y :=
    (contDiffAt_phaseForm hu₂ hu₀ (by norm_num : ((1 : ℕ) : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt
      one_ne_zero
  have hψ : ∑ j, (u * α j) y • w j = u y • ∑ j, α j y • w j := by
    simp only [Pi.mul_apply, mul_smul, Finset.smul_sum]
  rw [sum_sum_covariantDeriv_sub_phaseForm_mul_smul e (fun j ↦ (w j : W)) hu
      (hu₂.differentiableAt two_ne_zero) hα, smul_eq_zero_iff_right hu₀,
    extDeriv_sub hb hφ, extDeriv_phaseForm hu₂ hu₀, sub_zero, hψ,
    quadraticTwoForm_smul_of_norm_eq_one o ρ hkl hu₁]

/-! ### Limits of solutions of the flat limiting equations -/

/-- **The flat limiting equations pass to limits of `1`-jets.** Let `(b i, α i)` solve the flat
limiting equations at `y`,

`∑ₖ ∑ⱼ (∇_{b i} αᵢⱼ)(eₖ) c(eₖ) wⱼ = 0`,  `F + ⋆F = ω / 8 - q(∑ⱼ αᵢⱼ(y) wⱼ) / 2 - η i`,

with forcing `η i → 0`. If the values of `b i` and the values and first derivatives of the
coefficients `α i j` at `y` converge to those of `(b₀, α₀)`, and so do the first derivatives of
`b i` at `y`, then `(b₀, α₀)` solves the unforced flat limiting equations at `y`. -/
theorem sum_sum_covariantDeriv_smul_eq_zero_and_add_hodgeStar_eq_of_tendsto {τ : Type*}
    {l : Filter τ} [l.NeBot] (e : ν → V) (w : κ → positiveHalfSpinors o ρ) (ω : ⋀[ℝ]^2 V)
    {b : τ → V → V [⋀^Fin 1]→L[ℝ] ℝ} {α : τ → κ → V → ℂ} {η : τ → ⋀[ℝ]^2 V}
    {b₀ : V → V [⋀^Fin 1]→L[ℝ] ℝ} {α₀ : κ → V → ℂ} {y : V}
    (hb : Tendsto (fun i ↦ b i y) l (𝓝 (b₀ y)))
    (hdb : Tendsto (fun i ↦ fderiv ℝ (b i) y) l (𝓝 (fderiv ℝ b₀ y)))
    (hα : ∀ j, Tendsto (fun i ↦ α i j y) l (𝓝 (α₀ j y)))
    (hdα : ∀ j, Tendsto (fun i ↦ fderiv ℝ (α i j) y) l (𝓝 (fderiv ℝ (α₀ j) y)))
    (hη : Tendsto η l (𝓝 0))
    (hD : ∀ᶠ i in l,
      ∑ k, ∑ j, covariantDeriv (b i) (α i j) y (e k) • ρ (ι Q (e k)) (w j : W) = 0)
    (hF : ∀ᶠ i in l,
      (alternatingFormEquiv V 2).symm (-extDeriv (b i) y) +
          o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (-extDeriv (b i) y)) =
        (8⁻¹ : ℝ) • ω -
          (2⁻¹ : ℝ) • (quadraticTwoForm o ρ hkl (∑ j, α i j y • w j) : ⋀[ℝ]^2 V) - η i) :
    ∑ k, ∑ j, covariantDeriv b₀ (α₀ j) y (e k) • ρ (ι Q (e k)) (w j : W) = 0 ∧
      (alternatingFormEquiv V 2).symm (-extDeriv b₀ y) +
          o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (-extDeriv b₀ y)) =
        (8⁻¹ : ℝ) • ω -
          (2⁻¹ : ℝ) • (quadraticTwoForm o ρ hkl (∑ j, α₀ j y • w j) : ⋀[ℝ]^2 V) := by
  have hcd (j : κ) := tendsto_covariantDeriv hb (hα j) (hdα j)
  constructor
  · -- The Dirac expression is a continuous function of the covariant derivatives.
    have hlim : Tendsto
        (fun i ↦ ∑ k, ∑ j, covariantDeriv (b i) (α i j) y (e k) • ρ (ι Q (e k)) (w j : W)) l
        (𝓝 (∑ k, ∑ j, covariantDeriv b₀ (α₀ j) y (e k) • ρ (ι Q (e k)) (w j : W))) :=
      tendsto_finsetSum _ fun k _ ↦ tendsto_finsetSum _ fun j _ ↦
        (((ContinuousLinearMap.apply ℝ ℂ (e k)).continuous.tendsto _).comp (hcd j)).smul_const _
    exact tendsto_nhds_unique_of_eventuallyEq hlim tendsto_const_nhds hD
  · -- The curvature is a continuous function of the derivative of the connection form, and `q` is
    -- a continuous function of the spinor.
    let A : (V [⋀^Fin 2]→L[ℝ] ℝ) ≃ₗ[ℝ] ⋀[ℝ]^2 V := (alternatingFormEquiv V 2).symm
    have : FiniteDimensional ℝ (V [⋀^Fin 2]→L[ℝ] ℝ) := A.symm.finiteDimensional
    have hcurv : Tendsto (fun i ↦ A (-extDeriv (b i) y)) l (𝓝 (A (-extDeriv b₀ y))) :=
      (A.toLinearMap.continuous_of_finiteDimensional.tendsto _).comp
        (((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ V ℝ).continuous.tendsto _).comp
          hdb).neg
    have hψ : Tendsto (fun i ↦ ∑ j, α i j y • w j) l (𝓝 (∑ j, α₀ j y • w j)) :=
      tendsto_finsetSum _ fun j _ ↦ (hα j).smul_const _
    have hq : Tendsto (fun i ↦ (quadraticTwoForm o ρ hkl (∑ j, α i j y • w j) : ⋀[ℝ]^2 V)) l
        (𝓝 (quadraticTwoForm o ρ hkl (∑ j, α₀ j y • w j))) :=
      continuous_subtypeVal.continuousAt.tendsto.comp
        ((contDiff_quadraticTwoForm (n := 0) o ρ hkl).continuous.continuousAt.tendsto.comp hψ)
    have hlhs := hcurv.add
      (((o.hodgeStar hkl).toLinearMap.continuous_of_finiteDimensional.tendsto _).comp hcurv)
    have hrhs := ((tendsto_const_nhds (x := (8⁻¹ : ℝ) • ω)).sub (hq.const_smul (2⁻¹ : ℝ))).sub hη
    rw [sub_zero] at hrhs
    exact tendsto_nhds_unique_of_eventuallyEq hlhs hrhs hF

/-- **Limits of blown-up large-parameter solutions solve the flat limiting equations.** Let
`(b i, ∑ⱼ αᵢⱼ wⱼ)` solve the large-parameter Seiberg–Witten equations

`∑ₖ ∑ⱼ (∇_{b i} αᵢⱼ)(eₖ) c(eₖ) wⱼ = 0`,  `F + ⋆F = (r i / 4) ω - q(√(r i) ∑ⱼ αᵢⱼ wⱼ) - η i`

at the points `x i + h i • y`, where `h i ^ 2 * r i = 1 / 2` and `h i ^ 2 • η i → 0`, as for
`r i → ∞` with bounded forcing. If the fields blown up by `h i` about `x i`,
`z ↦ h i • b i (x i + h i • z)` and `z ↦ αᵢⱼ (x i + h i • z)`, converge at `y` to `(b₀, α₀)`
together with their first derivatives, then `(b₀, α₀)` solves the unforced flat limiting
equations `∑ₖ ∑ⱼ (∇_{b₀} α₀ⱼ)(eₖ) c(eₖ) wⱼ = 0` and `F + ⋆F = ω / 8 - q(∑ⱼ α₀ⱼ wⱼ) / 2` at `y`. -/
theorem sum_sum_covariantDeriv_smul_eq_zero_and_add_hodgeStar_eq_of_tendsto_rescale
    {τ : Type*} {l : Filter τ} [l.NeBot] (e : ν → V) (w : κ → positiveHalfSpinors o ρ)
    (ω : ⋀[ℝ]^2 V) {h r : τ → ℝ} {x : τ → V} {b : τ → V → V [⋀^Fin 1]→L[ℝ] ℝ}
    {α : τ → κ → V → ℂ} {η : τ → ⋀[ℝ]^2 V} {b₀ : V → V [⋀^Fin 1]→L[ℝ] ℝ} {α₀ : κ → V → ℂ}
    {y : V} (hr : ∀ i, h i ^ 2 * r i = 1 / 2)
    (hb : Tendsto (fun i ↦ h i • b i (x i + h i • y)) l (𝓝 (b₀ y)))
    (hdb : Tendsto (fun i ↦ fderiv ℝ (fun z ↦ h i • b i (x i + h i • z)) y) l
      (𝓝 (fderiv ℝ b₀ y)))
    (hα : ∀ j, Tendsto (fun i ↦ α i j (x i + h i • y)) l (𝓝 (α₀ j y)))
    (hdα : ∀ j, Tendsto (fun i ↦ fderiv ℝ (fun z ↦ α i j (x i + h i • z)) y) l
      (𝓝 (fderiv ℝ (α₀ j) y)))
    (hη : Tendsto (fun i ↦ h i ^ 2 • η i) l (𝓝 0))
    (hD : ∀ᶠ i in l, ∑ k, ∑ j,
      covariantDeriv (b i) (α i j) (x i + h i • y) (e k) • ρ (ι Q (e k)) (w j : W) = 0)
    (hF : ∀ᶠ i in l,
      (alternatingFormEquiv V 2).symm (-extDeriv (b i) (x i + h i • y)) +
          o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (-extDeriv (b i) (x i + h i • y))) =
        (r i / 4) • ω - (quadraticTwoForm o ρ hkl
          (((√(r i) : ℝ) : ℂ) • ∑ j, α i j (x i + h i • y) • w j) : ⋀[ℝ]^2 V) - η i) :
    ∑ k, ∑ j, covariantDeriv b₀ (α₀ j) y (e k) • ρ (ι Q (e k)) (w j : W) = 0 ∧
      (alternatingFormEquiv V 2).symm (-extDeriv b₀ y) +
          o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (-extDeriv b₀ y)) =
        (8⁻¹ : ℝ) • ω -
          (2⁻¹ : ℝ) • (quadraticTwoForm o ρ hkl (∑ j, α₀ j y • w j) : ⋀[ℝ]^2 V) := by
  have hh (i : τ) : h i ≠ 0 := by
    rintro h0
    have := hr i
    rw [h0] at this
    norm_num at this
  refine sum_sum_covariantDeriv_smul_eq_zero_and_add_hodgeStar_eq_of_tendsto hkl e w ω
    (b := fun i z ↦ h i • b i (x i + h i • z)) (α := fun i j z ↦ α i j (x i + h i • z))
    hb hdb hα hdα hη ?_ ?_
  · filter_upwards [hD] with i hi
    exact (sum_sum_covariantDeriv_comp_add_smul_eq_zero_iff (hh i) e (fun j ↦ (w j : W)) (b i)
      (α i) (x i) y).2 hi
  · filter_upwards [hF] with i hi
    exact (add_hodgeStar_extDeriv_comp_add_smul_eq_iff hkl (hr i) ω (η i) _ (b i) (x i) y).2 hi

/-- **Limits of gauge transforms of blown-up solutions solve the flat limiting equations.** Let
`(b i, ∑ⱼ αᵢⱼ wⱼ)` solve the large-parameter Seiberg–Witten equations

`∑ₖ ∑ⱼ (∇_{b i} αᵢⱼ)(eₖ) c(eₖ) wⱼ = 0`,  `F + ⋆F = (r i / 4) ω - q(√(r i) ∑ⱼ αᵢⱼ wⱼ) - η i`

at the points `x i + h i • y`, where `h i ^ 2 * r i = 1 / 2` and `h i ^ 2 • η i → 0`. Let `u i`
be gauges of class `C²` near `y` with `|u i| = 1` near `y`, and suppose that the gauge transforms
`(Bᵢ - Im (uᵢ⁻¹ duᵢ), uᵢ Aᵢⱼ)` of the blown-up fields `Bᵢ z = h i • b i (x i + h i • z)` and
`Aᵢⱼ z = αᵢⱼ (x i + h i • z)` converge at `y`, together with their first derivatives, to
`(b₀, α₀)`. Then `(b₀, α₀)` solves the unforced flat limiting equations at `y`. -/
theorem sum_sum_covariantDeriv_smul_eq_zero_and_add_hodgeStar_eq_of_tendsto_rescale_sub_phaseForm
    {τ : Type*} {l : Filter τ} [l.NeBot] (e : ν → V) (w : κ → positiveHalfSpinors o ρ)
    (ω : ⋀[ℝ]^2 V) {h r : τ → ℝ} {x : τ → V} {b : τ → V → V [⋀^Fin 1]→L[ℝ] ℝ}
    {α : τ → κ → V → ℂ} {η : τ → ⋀[ℝ]^2 V} {u : τ → V → ℂ} {b₀ : V → V [⋀^Fin 1]→L[ℝ] ℝ}
    {α₀ : κ → V → ℂ} {y : V} (hr : ∀ i, h i ^ 2 * r i = 1 / 2)
    (hb : ∀ i, DifferentiableAt ℝ (b i) (x i + h i • y))
    (hα : ∀ i j, DifferentiableAt ℝ (α i j) (x i + h i • y)) (hu : ∀ i, ∀ᶠ z in 𝓝 y, ‖u i z‖ = 1)
    (hu₂ : ∀ i, ContDiffAt ℝ 2 (u i) y)
    (hb₀ : Tendsto
      (fun i ↦ ((fun z ↦ h i • b i (x i + h i • z)) - phaseForm (u i)) y) l (𝓝 (b₀ y)))
    (hdb₀ : Tendsto (fun i ↦ fderiv ℝ ((fun z ↦ h i • b i (x i + h i • z)) - phaseForm (u i)) y)
      l (𝓝 (fderiv ℝ b₀ y)))
    (hα₀ : ∀ j, Tendsto (fun i ↦ (u i * fun z ↦ α i j (x i + h i • z)) y) l (𝓝 (α₀ j y)))
    (hdα₀ : ∀ j, Tendsto (fun i ↦ fderiv ℝ (u i * fun z ↦ α i j (x i + h i • z)) y) l
      (𝓝 (fderiv ℝ (α₀ j) y)))
    (hη : Tendsto (fun i ↦ h i ^ 2 • η i) l (𝓝 0))
    (hD : ∀ᶠ i in l, ∑ k, ∑ j,
      covariantDeriv (b i) (α i j) (x i + h i • y) (e k) • ρ (ι Q (e k)) (w j : W) = 0)
    (hF : ∀ᶠ i in l,
      (alternatingFormEquiv V 2).symm (-extDeriv (b i) (x i + h i • y)) +
          o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (-extDeriv (b i) (x i + h i • y))) =
        (r i / 4) • ω - (quadraticTwoForm o ρ hkl
          (((√(r i) : ℝ) : ℂ) • ∑ j, α i j (x i + h i • y) • w j) : ⋀[ℝ]^2 V) - η i) :
    ∑ k, ∑ j, covariantDeriv b₀ (α₀ j) y (e k) • ρ (ι Q (e k)) (w j : W) = 0 ∧
      (alternatingFormEquiv V 2).symm (-extDeriv b₀ y) +
          o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (-extDeriv b₀ y)) =
        (8⁻¹ : ℝ) • ω -
          (2⁻¹ : ℝ) • (quadraticTwoForm o ρ hkl (∑ j, α₀ j y • w j) : ⋀[ℝ]^2 V) := by
  have hh (i : τ) : h i ≠ 0 := by
    rintro h0
    have := hr i
    rw [h0] at this
    norm_num at this
  -- The blown-up fields are differentiable, and solve the flat limiting equations at `y`.
  have hBd (i : τ) : DifferentiableAt ℝ (fun z ↦ h i • b i (x i + h i • z)) y :=
    (DifferentiableAt.fun_comp' (f := fun z ↦ x i + h i • z) y (hb i) (by fun_prop)).fun_const_smul
      (h i)
  have hAd (i : τ) (j : κ) : DifferentiableAt ℝ (fun z ↦ α i j (x i + h i • z)) y :=
    DifferentiableAt.fun_comp' (f := fun z ↦ x i + h i • z) y (hα i j) (by fun_prop)
  refine sum_sum_covariantDeriv_smul_eq_zero_and_add_hodgeStar_eq_of_tendsto hkl e w ω
    (b := fun i ↦ (fun z ↦ h i • b i (x i + h i • z)) - phaseForm (u i))
    (α := fun i j ↦ u i * fun z ↦ α i j (x i + h i • z)) hb₀ hdb₀ hα₀ hdα₀ hη ?_ ?_
  all_goals
    filter_upwards [hD, hF] with i hDi hFi
    have hflat := (sum_sum_covariantDeriv_sub_phaseForm_mul_smul_eq_zero_and_add_hodgeStar_eq_iff
      hkl e w ω (h i ^ 2 • η i) (hu i) (hu₂ i) (hBd i) (hAd i)).2
      ⟨(sum_sum_covariantDeriv_comp_add_smul_eq_zero_iff (hh i) e (fun j ↦ (w j : W)) (b i)
        (α i) (x i) y).2 hDi,
        (add_hodgeStar_extDeriv_comp_add_smul_eq_iff hkl (hr i) ω (η i) _ (b i) (x i) y).2 hFi⟩
  · exact hflat.1
  · exact hflat.2

end TauCeti.SeibergWitten
