/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.RadialGauge.Connection
public import TauCeti.Analysis.PDE.SeibergWitten.Rescaling
import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Analysis.Calculus.ContDiff.TendstoAt
import TauCeti.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Compactness modulo gauge of blown-up large-parameter Seiberg–Witten fields

On a symplectic four-manifold, Taubes's large-parameter Seiberg–Witten equations read, in a flat
chart `V` with the connection on the line `E` written `a = i b` and the normalized spinor
`χ = ∑ⱼ αⱼ wⱼ` in a constant frame `(wⱼ)` of the positive half-spinors,

`D_b χ = 0`,  `F + ⋆F = (r / 4) ω - q(√r χ) - η`,  `F = i F_a = -db`.

Blowing a solution up by `h = (2 r)^(-1/2)` about a point `x₀`, that is pulling it back along
`z ↦ x₀ + h • z`, gives the fields `z ↦ h • b (x₀ + h • z)` and `z ↦ αⱼ (x₀ + h • z)`, which solve
the flat limiting equations `D_b χ = 0`, `F + ⋆F = ω / 8 - q(χ) / 2 - h² η`
(`TauCeti.Analysis.PDE.SeibergWitten.Rescaling`). Taubes's estimates bound the blown-up fields
uniformly in `r`, but only up to gauge: the connection form itself can be large in a bad gauge.
This file proves the resulting compactness theorem. Given, on every ball about the origin, uniform
bounds on finitely many derivatives of the blown-up curvatures and on finitely many iterated
covariant derivatives of the blown-up spinor coefficients, a subsequence of the blown-up fields
converges, after the radial gauge transformation centred at the origin
(`TauCeti.Analysis.PDE.SeibergWitten.RadialGauge.Connection`), in `Cᵏ_loc` on the whole of `V`,
and its limit solves the unforced flat limiting equations
(`TauCeti.SeibergWitten.exists_strictMono_tendstoLocallyUniformly_radialGauge_rescale`). This is
how the solutions of the flat limiting equations, among them the pulled-back plane vortices,
arise from sequences of Seiberg–Witten solutions with `r → ∞`.

The identification of the limit rests on two facts. The flat limiting equations are invariant under
unit gauge transformations `(b, α) ↦ (b - Im (u⁻¹ du), u α)`: the Dirac expression is multiplied by
`u` and the curvature and `q(χ)` are unchanged
(`sum_sum_covariantDeriv_sub_phaseForm_mul_smul_eq_zero_and_add_hodgeStar_eq_iff`).
And the flat limiting equations pass to limits of `1`-jets
(`TauCeti.SeibergWitten.sum_sum_covariantDeriv_smul_eq_zero_and_add_hodgeStar_eq_of_tendsto`), so
a limit of gauge transforms of blown-up solutions, converging with first derivatives at a point,
solves the unforced flat limiting equations there
(`sum_sum_covariantDeriv_smul_eq_zero_and_add_hodgeStar_eq_of_tendsto_rescale_sub_phaseForm`).

The bounds on the blown-up fields are hypotheses here: for actual solutions they are the
rescaled derivative estimates that come from the equations by elliptic regularity. The fields are
assumed to be defined and regular on all of `V`, but the equations are only used, at each point of
the blown-up picture, for all large indices, so the theorem applies to solutions on balls whose
blown-up radii tend to infinity, extended arbitrarily outside them.

## Main results

* `TauCeti.SeibergWitten.sum_sum_covariantDeriv_sub_phaseForm_mul_smul`: a unit gauge multiplies
  the Dirac expression by `u`.
* `sum_sum_covariantDeriv_sub_phaseForm_mul_smul_eq_zero_and_add_hodgeStar_eq_iff`, in the namespace
  `TauCeti.SeibergWitten`: gauge invariance of the flat limiting equations.
* `sum_sum_covariantDeriv_smul_eq_zero_and_add_hodgeStar_eq_of_tendsto_rescale_sub_phaseForm`, in
  the namespace `TauCeti.SeibergWitten`: limits of gauge transforms of blown-up solutions solve
  the flat limiting equations.
* `TauCeti.SeibergWitten.exists_strictMono_tendstoLocallyUniformly_radialGauge_rescale`: Taubes's
  compactness modulo gauge for blown-up large-parameter solutions.

## References

* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Section 4 (Proposition 4.2).
* K. K. Uhlenbeck, *Removable singularities in Yang–Mills fields*, Comm. Math. Phys. 83 (1982),
  11–29 (the exponential gauge).
-/

public section

open CliffordAlgebra Filter Metric Module Set
open scoped Topology

namespace TauCeti.SeibergWitten

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} {o : Orientation ℝ V (Fin 4)}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W} (hkl : 2 + 2 = finrank ℝ V)
  {ν κ : Type*} [Fintype ν] [Fintype κ]

/-- The dimension `Fact` makes the oriented four-space finite-dimensional. -/
local instance instFiniteDimensionalRealRescalingCompactness : FiniteDimensional ℝ V :=
  .of_fact_finrank_eq_succ 3

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

/-! ### Limits of blown-up solutions -/

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

/-- The step of `exists_strictMono_tendstoLocallyUniformly_radialGauge_rescale` at one point: if
the blown-up fields in radial gauge centred at the origin converge in `C¹` at `y` and the original
fields solve the large-parameter equations at `x n + h n • y` for all large `n`, the limit solves
the unforced flat limiting equations at `y`. -/
private theorem flat_of_tendstoContDiffAt_radialGauge_rescale (e : ν → V)
    (w : κ → positiveHalfSpinors o ρ) (ω : ⋀[ℝ]^2 V) {h r : ℕ → ℝ} {x : ℕ → V}
    {b : ℕ → V → V [⋀^Fin 1]→L[ℝ] ℝ} {α : ℕ → κ → V → ℂ} {η : ℕ → ⋀[ℝ]^2 V}
    {b₀ : V → V [⋀^Fin 1]→L[ℝ] ℝ} {α₀ : V → κ → ℂ} {y : V} (hr : ∀ n, h n ^ 2 * r n = 1 / 2)
    (hb : ∀ n, ContDiff ℝ 2 (b n)) (hα : ∀ n j, ContDiff ℝ 1 (α n j))
    (hα₀ : DifferentiableAt ℝ α₀ y)
    (hTb : TendstoContDiffAt ℝ 1
      (fun n ↦ radialConnection 0 fun z ↦ h n • b n (x n + h n • z)) b₀ atTop y)
    (hTα : TendstoContDiffAt ℝ 1 (fun n z j ↦
      radialGauge 0 (fun z ↦ h n • b n (x n + h n • z)) z * α n j (x n + h n • z)) α₀ atTop y)
    (hη : Tendsto (fun n ↦ h n ^ 2 • η n) atTop (𝓝 0))
    (hD : ∀ᶠ n in atTop, ∑ i, ∑ j,
      covariantDeriv (b n) (α n j) (x n + h n • y) (e i) • ρ (ι Q (e i)) (w j : W) = 0)
    (hF : ∀ᶠ n in atTop,
      (alternatingFormEquiv V 2).symm (-extDeriv (b n) (x n + h n • y)) +
          o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (-extDeriv (b n) (x n + h n • y))) =
        (r n / 4) • ω - (quadraticTwoForm o ρ hkl
          (((√(r n) : ℝ) : ℂ) • ∑ j, α n j (x n + h n • y) • w j) : ⋀[ℝ]^2 V) - η n) :
    ∑ i, ∑ j, covariantDeriv b₀ (fun z ↦ α₀ z j) y (e i) • ρ (ι Q (e i)) (w j : W) = 0 ∧
      (alternatingFormEquiv V 2).symm (-extDeriv b₀ y) +
          o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (-extDeriv b₀ y)) =
        (8⁻¹ : ℝ) • ω -
          (2⁻¹ : ℝ) • (quadraticTwoForm o ρ hkl (∑ j, α₀ y j • w j) : ⋀[ℝ]^2 V) := by
  have hdil (n : ℕ) : ContDiff ℝ 2 fun z : V ↦ x n + h n • z :=
    contDiff_const.add (contDiff_const.smul contDiff_id)
  have hB (n : ℕ) : ContDiff ℝ 2 fun z ↦ h n • b n (x n + h n • z) :=
    ((hb n).fun_comp (hdil n)).const_smul (h n)
  -- The radial connection is the gauge transform of the blown-up connection by the radial gauge.
  have hrad (n : ℕ) : radialConnection 0 (fun z ↦ h n • b n (x n + h n • z)) =
      (fun z ↦ h n • b n (x n + h n • z)) -
        phaseForm (radialGauge 0 fun z ↦ h n • b n (x n + h n • z)) :=
    (sub_phaseForm_radialGauge 0 ((hB n).of_le one_le_two)).symm
  have hy : Tendsto (fun n : ℕ ↦ (n, y)) atTop (atTop ×ˢ 𝓝 y) :=
    tendsto_id.prodMk tendsto_const_nhds
  refine sum_sum_covariantDeriv_smul_eq_zero_and_add_hodgeStar_eq_of_tendsto_rescale_sub_phaseForm
    hkl e w ω (u := fun n ↦ radialGauge 0 fun z ↦ h n • b n (x n + h n • z))
    (α₀ := fun j z ↦ α₀ z j) hr (fun n ↦ (hb n).differentiable two_ne_zero _)
    (fun n j ↦ (hα n j).differentiable one_ne_zero _)
    (fun n ↦ .of_forall (norm_radialGauge 0 _))
    (fun n ↦ (contDiff_radialGauge (r := 2) 0 (hB n)).contDiffAt) ?_ ?_ (fun j ↦ ?_) (fun j ↦ ?_)
    hη hD hF
  · simpa only [Function.comp_def, hrad] using hTb.tendsto.comp hy
  · simpa only [Function.comp_def, hrad] using (hTb.tendsto_fderiv le_rfl).comp hy
  · exact ((continuous_apply j).tendsto _).comp (hTα.tendsto.comp hy)
  · -- The derivative of a component is the component of the derivative.
    have hU (n : ℕ) : DifferentiableAt ℝ (fun z j ↦
        radialGauge 0 (fun z ↦ h n • b n (x n + h n • z)) z * α n j (x n + h n • z)) y :=
      differentiableAt_pi.2 fun j ↦ (((contDiff_radialGauge 0 ((hB n).of_le one_le_two)).mul
        ((hα n j).fun_comp ((hdil n).of_le one_le_two))).differentiable one_ne_zero) y
    have hcomp := ((ContinuousLinearMap.compL ℝ V (κ → ℂ) ℂ
      (ContinuousLinearMap.proj j)).continuous.tendsto _).comp
        ((hTα.tendsto_fderiv le_rfl).comp hy)
    simp only [Function.comp_def, ← fderiv_apply (hU _) j, ← fderiv_apply hα₀ j,
      ContinuousLinearMap.compL_apply] at hcomp
    simpa only [Pi.mul_def] using hcomp

/-- **Taubes's compactness modulo gauge for blown-up large-parameter solutions.** Let
`(b n, ∑ⱼ αₙⱼ wⱼ)` be fields on `V`, the connection forms of class `C^(k+2)` and the spinor
coefficients of class `C^(l+1)`, with `1 ≤ k` and `1 ≤ l ≤ k + 1`, and let `h n ^ 2 * r n = 1 / 2`.
Blow them up by `h n` about `x n`: `Bₙ z = h n • b n (x n + h n • z)`,
`Aₙⱼ z = αₙⱼ (x n + h n • z)`. Suppose that

* at each point `y`, for all large `n`, the fields solve the large-parameter equations
  `∑ₖ ∑ⱼ (∇_{b n} αₙⱼ)(eₖ) c(eₖ) wⱼ = 0`, `F + ⋆F = (r n / 4) ω - q(√(r n) ∑ⱼ αₙⱼ wⱼ) - η n` at
  `x n + h n • y`, with blown-up forcing `h n ^ 2 • η n (x n + h n • y) → 0`;
* on every ball about the origin, the derivatives of order at most `k + 1` of the blown-up
  curvatures `dBₙ` and the iterated covariant derivatives `∇ʲ_{Bₙ} Aₙⱼ` of order at most `l + 1`
  are bounded uniformly in `n` and `j`.

Then along a subsequence the blown-up fields in radial gauge centred at the origin converge on all
of `V`: the radial connections `K (dBₙ)` with their derivatives of order at most `k`, and the
transformed sections `(uₙ Aₙⱼ)ⱼ`, `uₙ = exp (i K Bₙ)`, with their derivatives of order at most `l`,
locally uniformly. The limit `(b', α')` is of class `Cᵏ × Cˡ` and solves the unforced flat limiting
equations `∑ₖ ∑ⱼ (∇_{b'} α'ⱼ)(eₖ) c(eₖ) wⱼ = 0`, `F + ⋆F = ω / 8 - q(∑ⱼ α'ⱼ wⱼ) / 2` everywhere. -/
theorem exists_strictMono_tendstoLocallyUniformly_radialGauge_rescale (e : ν → V)
    (w : κ → positiveHalfSpinors o ρ) (ω : ⋀[ℝ]^2 V) {h r : ℕ → ℝ} {x : ℕ → V}
    {b : ℕ → V → V [⋀^Fin 1]→L[ℝ] ℝ} {α : ℕ → κ → V → ℂ} {η : ℕ → V → ⋀[ℝ]^2 V} {k l : ℕ}
    (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k + 1) (hr : ∀ n, h n ^ 2 * r n = 1 / 2)
    (hb : ∀ n, ContDiff ℝ (k + 2) (b n)) (hα : ∀ n j, ContDiff ℝ (l + 1) (α n j))
    (hD : ∀ y, ∀ᶠ n in atTop, ∑ i, ∑ j,
      covariantDeriv (b n) (α n j) (x n + h n • y) (e i) • ρ (ι Q (e i)) (w j : W) = 0)
    (hF : ∀ y, ∀ᶠ n in atTop,
      (alternatingFormEquiv V 2).symm (-extDeriv (b n) (x n + h n • y)) +
          o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (-extDeriv (b n) (x n + h n • y))) =
        (r n / 4) • ω - (quadraticTwoForm o ρ hkl
          (((√(r n) : ℝ) : ℂ) • ∑ j, α n j (x n + h n • y) • w j) : ⋀[ℝ]^2 V) -
          η n (x n + h n • y))
    (hη : ∀ y, Tendsto (fun n ↦ h n ^ 2 • η n (x n + h n • y)) atTop (𝓝 0))
    (hFb : ∀ R, ∃ A, ∀ n, ∀ m ≤ k + 1, ∀ z ∈ ball (0 : V) R,
      ‖iteratedFDeriv ℝ m (extDeriv fun z ↦ h n • b n (x n + h n • z)) z‖ ≤ A)
    (hcov : ∀ R, ∃ C, ∀ n j, ∀ m ≤ l + 1, ∀ z ∈ ball (0 : V) R,
      ‖iteratedCovariantDeriv (fun z ↦ h n • b n (x n + h n • z))
        (fun z ↦ α n j (x n + h n • z)) m z‖ ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (b' : V → V [⋀^Fin 1]→L[ℝ] ℝ) (α' : V → κ → ℂ),
      ContDiff ℝ k b' ∧ ContDiff ℝ l α' ∧
      (∀ m ≤ k, TendstoLocallyUniformly (fun n ↦ iteratedFDeriv ℝ m
        (radialConnection 0 fun z ↦ h (φ n) • b (φ n) (x (φ n) + h (φ n) • z)))
          (iteratedFDeriv ℝ m b') atTop) ∧
      (∀ m ≤ l, TendstoLocallyUniformly (fun n ↦ iteratedFDeriv ℝ m
        (fun z j ↦ radialGauge 0 (fun z ↦ h (φ n) • b (φ n) (x (φ n) + h (φ n) • z)) z *
          α (φ n) j (x (φ n) + h (φ n) • z)))
          (iteratedFDeriv ℝ m α') atTop) ∧
      ∀ y, ∑ i, ∑ j, covariantDeriv b' (fun z ↦ α' z j) y (e i) • ρ (ι Q (e i)) (w j : W) = 0 ∧
        (alternatingFormEquiv V 2).symm (-extDeriv b' y) +
            o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (-extDeriv b' y)) =
          (8⁻¹ : ℝ) • ω -
            (2⁻¹ : ℝ) • (quadraticTwoForm o ρ hkl (∑ j, α' y j • w j) : ⋀[ℝ]^2 V) := by
  -- The blown-up fields have the regularity of the original ones.
  set B : ℕ → V → V [⋀^Fin 1]→L[ℝ] ℝ := fun n z ↦ h n • b n (x n + h n • z)
  set A : ℕ → κ → V → ℂ := fun n j z ↦ α n j (x n + h n • z)
  have hdil (n : ℕ) : ContDiff ℝ ⊤ fun z : V ↦ x n + h n • z :=
    contDiff_const.add (contDiff_const.smul contDiff_id)
  have hB (n : ℕ) : ContDiff ℝ (k + 2) (B n) :=
    ((hb n).fun_comp ((hdil n).of_le le_top)).const_smul (h n)
  have hA (n : ℕ) (j : κ) : ContDiff ℝ (l + 1) (A n j) :=
    (hα n j).fun_comp ((hdil n).of_le le_top)
  obtain ⟨φ, hφ, b', α', hb', hα', hconv, hconvα⟩ :=
    exists_strictMono_tendstoLocallyUniformly_iteratedFDeriv_radialGauge_mul (0 : V) k l hlk hB hA
      hFb hcov
  refine ⟨φ, hφ, b', α', hb', hα', hconv, hconvα, fun y ↦ ?_⟩
  have hk₁ (m : ℕ) (hm : (m : ℕ∞) ≤ 1) : m ≤ k := by norm_cast at hm; omega
  have hl₁ (m : ℕ) (hm : (m : ℕ∞) ≤ 1) : m ≤ l := by norm_cast at hm; omega
  -- The fields in radial gauge converge in `C¹` at `y`.
  refine flat_of_tendstoContDiffAt_radialGauge_rescale hkl e w ω (fun n ↦ hr (φ n))
    (fun n ↦ (hb (φ n)).of_le (by norm_cast; omega))
    (fun n j ↦ (hα (φ n) j).of_le (by norm_cast; omega))
    ((hα'.differentiable (by norm_cast; omega)) y)
    ((tendstoContDiffAt_iff_tendstoLocallyUniformlyOn isOpen_univ fun m hm ↦
      (hb'.continuous_iteratedFDeriv (by exact_mod_cast hk₁ m hm)).continuousOn).2
      (fun m hm ↦ tendstoLocallyUniformlyOn_univ.2 (hconv m (hk₁ m hm))) y (mem_univ y))
    ((tendstoContDiffAt_iff_tendstoLocallyUniformlyOn isOpen_univ fun m hm ↦
      (hα'.continuous_iteratedFDeriv (by exact_mod_cast hl₁ m hm)).continuousOn).2
      (fun m hm ↦ tendstoLocallyUniformlyOn_univ.2 (hconvα m (hl₁ m hm))) y (mem_univ y))
    ((hη y).comp hφ.tendsto_atTop) (hφ.tendsto_atTop.eventually (hD y))
    (hφ.tendsto_atTop.eventually (hF y))

end TauCeti.SeibergWitten
