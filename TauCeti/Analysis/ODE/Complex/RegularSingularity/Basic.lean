/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import TauCeti.Analysis.ODE.Complex.LinearEquation
public import TauCeti.Analysis.ODE.Complex.RegularSingularity.Defs

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.Analytic.OfScalars
import TauCeti.Analysis.Complex.PowerSeries.BranchCut
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Analysis.ODE.Complex.RegularSingularity.Primary
import TauCeti.Analysis.ODE.Complex.RegularSingularPoint
import TauCeti.Analysis.ODE.Complex.SecondOrder
import TauCeti.Analysis.ODE.SecondOrder.Operator
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Convergent series solutions at a regular singularity

For `f, g` around `z₀` with `(z - z₀) f(z) = ∑ f_s (z - z₀)^s` and
`(z - z₀)² g(z) = ∑ g_s (z - z₀)^s` on `0 < ‖z - z₀‖ < r`, let
`Q(α) = TauCeti.indicialPoly (fs 0) (gs 0) α = (α - α₁)(α - α₂)` (`Re α₂ ≤ Re α₁`). On the slit
punctured disc `TauCeti.regularSingularSlitDisc z₀ r`
(`{z | z - z₀ ∈ Complex.slitPlane ∧ ‖z - z₀‖ < r}`, via
`TauCeti.Analysis.Complex.PowerSeries.BranchCut`):
* For a non-resonant root `ρ` of `Q` (`Q(ρ + s) ≠ 0` for `s ≥ 1`), the canonical series
  `TauCeti.regularSingularSolution` (`TauCeti.regularSingularSolution_eq`) satisfies
  `TauCeti.regularSingularCoeff_solution` (via `TauCeti.regularSingular_solution` from
  `TauCeti.Analysis.ODE.Complex.RegularSingularPoint`, returning series convergence and
  `IsSolution` for `TauCeti.regularSingularEquation`), with normalized uniqueness
  `TauCeti.eq_regularSingularCoeff_of_solution`.
* The shifted logarithmic forcing coefficients `TauCeti.regularSingularLogForcing` sum to the
  Euler–Frobenius forcing series (`TauCeti.hasSum_regularSingularLogForcing_mul_pow`).
* When `α₁ - α₂ = N ∈ ℕ`, `TauCeti.regularSingularSecondSolution`
  (`TauCeti.regularSingularSecondSolution_eq`) defines the holomorphic second solution
  `w₂(z) = (z - z₀)^{α₂} ∑ b_s (z - z₀)^s + c w₁(z) log(z - z₀)` (`b_N = 0`, `c = 1` for
  `N = 0`, `b₀ = 1` for `N ≥ 1`) with `∑ b_s (z - z₀)^s` convergent on `‖z - z₀‖ < r` and solving
  `TauCeti.regularSingularEquation` (`TauCeti.regularSingular_second_solution`, uniqueness
  `TauCeti.eq_regularSingularSecondCoeff_of_solution`).

Fundamental-pair existence for `TauCeti.regularSingularEquation` is in
`TauCeti.Analysis.ODE.Complex.RegularSingularity.Wronskian` (via the Abel–Liouville Wronskian
theorems in `TauCeti.Analysis.ODE.Complex.RegularSingularPoint`).

## References
* NIST DLMF §2.7(ii), 2.7.1–2.7.6, <https://dlmf.nist.gov/2.7.ii>.
* F. W. J. Olver, *Asymptotics and Special Functions*, A K Peters, 1997, Chapter 5, §§4–5.
-/

public noncomputable section

open Complex Filter Finset Metric Set
open scoped Topology ENNReal

namespace TauCeti

/-! ### Slit punctured disc and `LinearEquation` setup -/

/-- The slit punctured open disc `{z : ℂ | z - z₀ ∈ Complex.slitPlane ∧ ‖z - z₀‖ < r}` as an
open subset of `ℂ`. -/
def regularSingularSlitDisc (z₀ : ℂ) (r : ℝ) : TopologicalSpace.Opens ℂ :=
  ⟨{z : ℂ | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r},
    isOpen_setOf_sub_mem_slitPlane_and_norm_sub_lt z₀ r⟩

/-- Membership in `regularSingularSlitDisc z₀ r`. -/
@[simp]
theorem mem_regularSingularSlitDisc {z₀ z : ℂ} {r : ℝ} :
    z ∈ regularSingularSlitDisc z₀ r ↔ z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r :=
  Iff.rfl

/-- Carrier set of `regularSingularSlitDisc z₀ r`. -/
@[simp]
theorem coe_regularSingularSlitDisc (z₀ : ℂ) (r : ℝ) :
    (regularSingularSlitDisc z₀ r : Set ℂ) = {z : ℂ | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r} :=
  (rfl)

/-- The slit punctured open disc `regularSingularSlitDisc z₀ r` is contained in the punctured open
ball `ball z₀ r \ {z₀}`. -/
theorem regularSingularSlitDisc_subset_ball_diff (z₀ : ℂ) (r : ℝ) :
    (regularSingularSlitDisc z₀ r : Set ℂ) ⊆ ball z₀ r \ {z₀} :=
  fun _ hz => ⟨by simpa [Metric.mem_ball, dist_eq_norm] using hz.2,
    sub_ne_zero.mp (Complex.slitPlane_ne_zero hz.1)⟩

/-- Construct the second-order `LinearEquation (regularSingularSlitDisc z₀ r) 2` associated with
`w'' + f w' + g w = 0` from regular-singularity series expansions of `(z - z₀) f(z)` and
`(z - z₀)² g(z)` on `0 < ‖z - z₀‖ < r`. -/
def regularSingularEquation {z₀ : ℂ} {r : ℝ} {f g : ℂ → ℂ} {fs gs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z)) :
    LinearEquation (regularSingularSlitDisc z₀ r) 2 :=
  LinearEquation.ofTwo f g
    ((FormalMultilinearSeries.analyticOnNhd_of_hasSum_ofScalars_of_norm_sub_lt z₀
      (k := 1) fun w hw0 hwr => by simpa only [pow_one] using hf w hw0 hwr).differentiableOn.mono
        (regularSingularSlitDisc_subset_ball_diff z₀ r))
    ((FormalMultilinearSeries.analyticOnNhd_of_hasSum_ofScalars_of_norm_sub_lt z₀
      (k := 2) hg).differentiableOn.mono (regularSingularSlitDisc_subset_ball_diff z₀ r))

/-- The order-zero coefficient of `regularSingularEquation hf hg` evaluates to `g` on
`regularSingularSlitDisc z₀ r`. -/
@[simp]
theorem extend_regularSingularEquation_coeff_zero {z₀ : ℂ} {r : ℝ} {f g : ℂ → ℂ}
    {fs gs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    {z : ℂ} (hz : z ∈ regularSingularSlitDisc z₀ r) :
    HolomorphicFunctions.extend ((regularSingularEquation hf hg).coeff 0) z = g z := by
  rw [regularSingularEquation]
  exact LinearEquation.extend_ofTwo_coeff_zero _ _ hz

/-- The order-one coefficient of `regularSingularEquation hf hg` evaluates to `f` on
`regularSingularSlitDisc z₀ r`. -/
@[simp]
theorem extend_regularSingularEquation_coeff_one {z₀ : ℂ} {r : ℝ} {f g : ℂ → ℂ}
    {fs gs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    {z : ℂ} (hz : z ∈ regularSingularSlitDisc z₀ r) :
    HolomorphicFunctions.extend ((regularSingularEquation hf hg).coeff 1) z = f z := by
  rw [regularSingularEquation]
  exact LinearEquation.extend_ofTwo_coeff_one _ _ hz

/-- Solutions of `regularSingularEquation hf hg` are precisely complex-differentiable functions on
`regularSingularSlitDisc z₀ r` satisfying `w'' + f w' + g w = 0` there. -/
@[simp]
theorem isSolution_regularSingularEquation_iff {z₀ : ℂ} {r : ℝ} {f g : ℂ → ℂ} {fs gs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (y : ℂ → ℂ) :
    (regularSingularEquation hf hg).IsSolution y ↔
      DifferentiableOn ℂ y (regularSingularSlitDisc z₀ r) ∧
        ∀ z ∈ regularSingularSlitDisc z₀ r,
          deriv (deriv y) z + f z * deriv y z + g z * y z = 0 := by
  rw [regularSingularEquation]
  exact LinearEquation.isSolution_ofTwo_iff _ _ y

/-! ### Primary series solution at a regular singularity -/

/-- Canonical Frobenius series solution
`(z - z₀)^ρ * ∑' s, regularSingularCoeff fs gs ρ s * (z - z₀)^s` attached to an indicial
root `ρ`. -/
def regularSingularSolution (fs gs : ℕ → ℂ) (z₀ ρ z : ℂ) : ℂ :=
  (z - z₀) ^ ρ * ∑' s, regularSingularCoeff fs gs ρ s * (z - z₀) ^ s

/-- Application formula for `regularSingularSolution`. -/
theorem regularSingularSolution_apply (fs gs : ℕ → ℂ) (z₀ ρ z : ℂ) :
    regularSingularSolution fs gs z₀ ρ z =
      (z - z₀) ^ ρ * ∑' s, regularSingularCoeff fs gs ρ s * (z - z₀) ^ s :=
  (rfl)

/-- Function-level formula for `regularSingularSolution`. -/
theorem regularSingularSolution_eq (fs gs : ℕ → ℂ) (z₀ ρ : ℂ) :
    regularSingularSolution fs gs z₀ ρ = fun z =>
      (z - z₀) ^ ρ * ∑' s, regularSingularCoeff fs gs ρ s * (z - z₀) ^ s :=
  funext fun z => regularSingularSolution_apply fs gs z₀ ρ z

/-- Specialization of `TauCeti.regularSingular_solution` to the canonical normalized series
`regularSingularSolution fs gs z₀ ρ` (`a₀ = 1`) attached to a non-resonant indicial root `ρ`,
yielding series convergence on `‖z - z₀‖ < r` and `IsSolution` for
`regularSingularEquation hf hg`. -/
theorem regularSingularCoeff_solution {z₀ ρ : ℂ} {r : ℝ} {f g : ℂ → ℂ} {fs gs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hρ : indicialPoly (fs 0) (gs 0) ρ = 0)
    (hres : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (ρ + s) ≠ 0) :
    (∀ z, ‖z - z₀‖ < r → Summable fun s => regularSingularCoeff fs gs ρ s * (z - z₀) ^ s) ∧
      (regularSingularEquation hf hg).IsSolution (regularSingularSolution fs gs z₀ ρ) := by
  obtain ⟨hsum, hdiff, hsol⟩ := regularSingular_solution hf hg hρ
    (fun s hs => indicialPoly_mul_regularSingularCoeff hs (hres s hs))
    (regularSingularSolution_eq fs gs z₀ ρ)
  exact ⟨hsum, (isSolution_regularSingularEquation_iff hf hg _).mpr
    ⟨hdiff, fun z hz => hsol z hz.1 hz.2⟩⟩

/-- **Analytic uniqueness of the normalized series coefficients**: for `0 < r` and a non-resonant
indicial root `ρ`, any convergent power series `∑ a_s (z - z₀)^s` with `a 0 = 1` such that
`(z - z₀)^ρ ∑ a_s (z - z₀)^s` solves `w'' + f w' + g w = 0` on the slit punctured disc has
`a = regularSingularCoeff fs gs ρ`. -/
theorem eq_regularSingularCoeff_of_solution {z₀ ρ : ℂ} {r : ℝ} {f g : ℂ → ℂ} {fs gs a : ℕ → ℂ}
    (hr : 0 < r)
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hres : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (ρ + s) ≠ 0)
    (ha0 : a 0 = 1)
    (hsum : ∀ z, ‖z - z₀‖ < r → Summable fun s => a s * (z - z₀) ^ s)
    (hsol : ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      deriv (deriv (fun w => (w - z₀) ^ ρ * ∑' s, a s * (w - z₀) ^ s)) z +
        f z * deriv (fun w => (w - z₀) ^ ρ * ∑' s, a s * (w - z₀) ^ s) z +
        g z * ((z - z₀) ^ ρ * ∑' s, a s * (z - z₀) ^ s) = 0) :
    a = regularSingularCoeff fs gs ρ := by
  have hall := eq_zero_of_cpow_mul_tsum_eq_zero (z₀ := z₀) (α := ρ - 2) hr
    (fun u _ hu => (hasSum_eulerOperator_ofScalars_of_norm_sub_lt (σ := ρ)
      (fun w hw0 hwr => (hf w hw0 hwr).summable)
      (fun w hw0 hwr => (hg w hw0 hwr).summable) hsum hu).summable)
    fun z hzs hzb =>
      (deriv_deriv_add_mul_deriv_add_mul_cpow_mul_tsum hf hg hsum hzs hzb).symm.trans
        (hsol z hzs hzb)
  exact eq_regularSingularCoeff_of_rec hres ha0 fun s _ => by linear_combination hall s

/-! ### Second solution when the indicial roots differ by a natural number -/

/-- Power-series expansion for the shifted logarithmic forcing terms
`u ^ N * (2 u A₁'(u) + (2(α₂ + N) + P(u) - 1) A₁(u))` on `‖u‖ < r`. -/
theorem hasSum_regularSingularLogForcing_mul_pow {z₀ α₂ : ℂ} {N : ℕ} {r : ℝ}
    {fs a : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r → Summable fun s => fs s * (z - z₀) ^ s)
    (ha : ∀ z, ‖z - z₀‖ < r → Summable fun s => a s * (z - z₀) ^ s)
    {u : ℂ} (hu : ‖u‖ < r) :
    HasSum (fun s => regularSingularLogForcing fs a α₂ N s * u ^ s)
      (u ^ N * (2 * u * deriv (fun w => ∑' s, a s * w ^ s) u +
        (2 * (α₂ + N) + (∑' s, fs s * u ^ s) - 1) * ∑' s, a s * u ^ s)) := by
  have hr : 0 < r := (norm_nonneg u).trans_lt hu
  have hue : ‖u‖ₑ < ENNReal.ofReal r := eNorm_lt_ofReal_iff.mpr hu
  have har := le_radius_ofScalars_of_summable_sub a fun z _ hzr => ha z hzr
  have hfr := le_radius_ofScalars_of_summable_sub fs hf
  have hpA := hasFPowerSeriesOnBall_tsum_mul_pow a (ENNReal.ofReal_pos.mpr hr) har
  have hf_sum := (FormalMultilinearSeries.summable_norm_mul_pow_of_lt_radius fs
    (hue.trans_le hfr)).of_norm
  have hfor := hasSum_regularSingularLogForcing_ofScalars (α₂ := α₂) (c := 1) (N := N)
    hpA hue (hue.trans_le hfr) hf_sum.hasSum
  simp only [one_mul] at hfor
  convert hfor using 1
  ring

/-- Algebraic recombination of `(z - z₀)^α` powers when adding the `(z - z₀)^α₂` series part
to `c'` times the logarithmic forcing of `w₁(z) = (z - z₀)^{α₂ + N} A₁(z - z₀)`. -/
private theorem operator_second_ansatz_cpow_recombine {u α₂ : ℂ} {N : ℕ} (hu0 : u ≠ 0)
    (c' A₁ dA₁ fz S : ℂ) :
    u ^ (α₂ - 2) * S + c' * ((u ^ 2)⁻¹ *
      (2 * u * (u ^ (α₂ + (N : ℂ) - 1) * ((α₂ + N) * A₁ + u * dA₁)) +
        (u * fz - 1) * (u ^ (α₂ + (N : ℂ)) * A₁))) =
      u ^ (α₂ - 2) *
        (S + c' * (u ^ N * (2 * u * dA₁ + (2 * (α₂ + N) + u * fz - 1) * A₁))) := by
  have hcpow1 : u ^ (α₂ + (N : ℂ)) = u ^ (α₂ + (N : ℂ) - 1) * u := by
    simpa [Nat.cast_one, pow_one] using cpow_eq_cpow_sub_natCast_mul_pow hu0 (α₂ + (N : ℂ)) 1
  have hcpow2 : u ^ α₂ = u ^ (α₂ - 2) * u ^ 2 := by
    simpa using cpow_eq_cpow_sub_natCast_mul_pow hu0 α₂ 2
  have hcpow_N : (u ^ 2)⁻¹ * u ^ (α₂ + (N : ℂ)) = u ^ (α₂ - 2) * u ^ N := by
    rw [Complex.cpow_add _ _ hu0, Complex.cpow_natCast, hcpow2]
    field_simp [hu0]
  linear_combination
    c' * (2 * (u ^ 2)⁻¹ * ((α₂ + ↑N) * A₁ + u * dA₁)) * hcpow1.symm +
    c' * (2 * u * dA₁ + (2 * (α₂ + ↑N) + u * fz - 1) * A₁) * hcpow_N

/-- Shared operator formula for any second-solution candidate
`w₂'(z) = (z - z₀)^{α₂} ∑ b' s * (z - z₀)^s + c' * w₁(z) * log(z - z₀)` when `α₁ = α₂ + N`. -/
private theorem operator_second_ansatz_eq {z₀ α₂ : ℂ} {N : ℕ} {r : ℝ} {f g : ℂ → ℂ}
    {fs gs b' : ℕ → ℂ} {c' : ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (ha_sum : ∀ z, ‖z - z₀‖ < r →
      Summable fun s => regularSingularCoeff fs gs (α₂ + N) s * (z - z₀) ^ s)
    (hw₁_sol : (regularSingularEquation hf hg).IsSolution
      (regularSingularSolution fs gs z₀ (α₂ + N)))
    (hlog_sum : ∀ u : ℂ, ‖u‖ < r →
      let a := regularSingularCoeff fs gs (α₂ + N)
      HasSum (fun s => regularSingularLogForcing fs a α₂ N s * u ^ s)
        (u ^ N * (2 * u * deriv (fun w => ∑' s, a s * w ^ s) u +
          (2 * (α₂ + N) + (∑' s, fs s * u ^ s) - 1) * ∑' s, a s * u ^ s)))
    (hb'_sum : ∀ z, ‖z - z₀‖ < r → Summable fun s => b' s * (z - z₀) ^ s) :
    let a := regularSingularCoeff fs gs (α₂ + N)
    let w₁ : ℂ → ℂ := fun w => (w - z₀) ^ (α₂ + (N : ℂ)) * ∑' s, a s * (w - z₀) ^ s
    let w₂' : ℂ → ℂ := fun w =>
      (w - z₀) ^ α₂ * (∑' s, b' s * (w - z₀) ^ s) + c' * w₁ w * Complex.log (w - z₀)
    let D : ℕ → ℂ := fun s =>
      (indicialPoly (fs 0) (gs 0) (α₂ + s) * b' s +
        ∑ k ∈ range s, ((α₂ + k) * fs (s - k) + gs (s - k)) * b' k) +
      c' * regularSingularLogForcing fs a α₂ N s
    let U : Set ℂ := {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}
    DifferentiableOn ℂ w₂' U ∧
      (∀ u : ℂ, ‖u‖ < r → Summable fun s => D s * u ^ s) ∧
      ∀ z ∈ U, deriv (deriv w₂') z + f z * deriv w₂' z + g z * w₂' z =
        (z - z₀) ^ (α₂ - 2) * ∑' s, D s * (z - z₀) ^ s := by
  intro a w₁ w₂' D U
  -- 1. Unpack holomorphy and the ODE for `w₁`, and derive the forcing on `Φ = w₁ * log(· - z₀)`.
  obtain ⟨hw₁_diff, hw₁_op⟩ := (isSolution_regularSingularEquation_iff hf hg _).mp hw₁_sol
  have hopen := isOpen_setOf_sub_mem_slitPlane_and_norm_sub_lt z₀ r
  obtain ⟨hΦ_diff, hΦ_op⟩ := operator_mul_log (z₀ := z₀) hopen (fun _ hz => hz.1) hw₁_diff hw₁_op
  set ψ : ℂ → ℂ := fun w => (w - z₀) ^ α₂ * ∑' s, b' s * (w - z₀) ^ s
  set Φ : ℂ → ℂ := fun w => regularSingularSolution fs gs z₀ (α₂ + N) w * Complex.log (w - z₀)
  have hψ_diff : DifferentiableOn ℂ ψ U := fun w hw =>
    (hasDerivAt_cpow_mul_tsum hb'_sum hw.1 hw.2).differentiableAt.differentiableWithinAt
  have hw₁_fn : w₁ = regularSingularSolution fs gs z₀ (α₂ + N) :=
    (regularSingularSolution_eq fs gs z₀ (α₂ + N)).symm
  have hw₂'_eq : w₂' = fun w => ψ w + c' * Φ w := by
    dsimp only [w₂', ψ, Φ]; rw [hw₁_fn]; simp only [mul_assoc]
  -- 2. Sum the series contributions from `ψ` and the logarithmic forcing series `D`.
  have hD_hasSum : ∀ u : ℂ, ‖u‖ < r → HasSum (fun s => D s * u ^ s)
      ((∑' s : ℕ, (indicialPoly (fs 0) (gs 0) (α₂ + s) * b' s +
          ∑ k ∈ range s, ((α₂ + k) * fs (s - k) + gs (s - k)) * b' k) * u ^ s) +
        c' * (u ^ N * (2 * u * deriv (fun w => ∑' s, a s * w ^ s) u +
          (2 * (α₂ + N) + (∑' s, fs s * u ^ s) - 1) * ∑' s, a s * u ^ s))) := fun u hu =>
    (((hasSum_eulerOperator_ofScalars_of_norm_sub_lt (σ := α₂)
        (fun w hw0 hwr => (hf w hw0 hwr).summable)
        (fun w hw0 hwr => (hg w hw0 hwr).summable) hb'_sum hu).summable.hasSum).add
      ((hlog_sum u hu).mul_left c')).congr_fun fun _ => by dsimp [D]; ring
  refine ⟨by rw [hw₂'_eq]; exact hψ_diff.add (hΦ_diff.const_mul c'),
    fun u hu => (hD_hasSum u hu).summable, fun z ⟨hzs, hzb⟩ => ?_⟩
  -- 3. Apply operator linearity to `ψ + c' Φ` and recombine the `cpow` prefactors.
  have hzU : z ∈ U := ⟨hzs, hzb⟩
  have hlin := secondOrder_operator_add_const_mul (f := f) (g := g) (c' := c') (z := z)
    (Eventually.mono (hopen.mem_nhds hzU) fun _ hw => hψ_diff.differentiableAt (hopen.mem_nhds hw))
    (Eventually.mono (hopen.mem_nhds hzU) fun _ hw => hΦ_diff.differentiableAt (hopen.mem_nhds hw))
    ((hψ_diff.deriv hopen).differentiableAt (hopen.mem_nhds hzU))
    ((hΦ_diff.deriv hopen).differentiableAt (hopen.mem_nhds hzU))
  rw [hw₂'_eq, hlin,
    deriv_deriv_add_mul_deriv_add_mul_cpow_mul_tsum (σ := α₂) hf hg hb'_sum hzs hzb,
    hΦ_op z hzU, (hD_hasSum (z - z₀) hzb).tsum_eq]
  have hu0 : z - z₀ ≠ 0 := Complex.slitPlane_ne_zero hzs
  have hdw₁ : deriv w₁ z = (z - z₀) ^ (α₂ + (N : ℂ) - 1) *
      ((α₂ + N) * (∑' s, a s * (z - z₀) ^ s) +
        (z - z₀) * deriv (fun w => ∑' s, a s * w ^ s) (z - z₀)) :=
    (hasDerivAt_cpow_mul_tsum ha_sum hzs hzb).deriv
  rw [(hf z (norm_pos_iff.mpr hu0) hzb).tsum_eq, ← hw₁_fn, hdw₁]
  exact operator_second_ansatz_cpow_recombine hu0 c' _ _ (f z) _

/-- Canonical logarithmic second Frobenius solution attached to indicial roots `α₁ = α₂ + N`:
`(z - z₀)^{α₂} ∑' s, regularSingularSecondCoeff fs gs α₂ N s * (z - z₀)^s +`
`regularSingularLogMultiplier fs gs α₂ N * regularSingularSolution fs gs z₀ (α₂ + N) z *`
`Complex.log (z - z₀)`. -/
def regularSingularSecondSolution (fs gs : ℕ → ℂ) (z₀ α₂ : ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  (z - z₀) ^ α₂ * (∑' s, regularSingularSecondCoeff fs gs α₂ N s * (z - z₀) ^ s) +
    regularSingularLogMultiplier fs gs α₂ N * regularSingularSolution fs gs z₀ (α₂ + N) z *
      Complex.log (z - z₀)

/-- Application formula for `regularSingularSecondSolution`. -/
theorem regularSingularSecondSolution_apply (fs gs : ℕ → ℂ) (z₀ α₂ : ℂ) (N : ℕ) (z : ℂ) :
    regularSingularSecondSolution fs gs z₀ α₂ N z =
      (z - z₀) ^ α₂ * (∑' s, regularSingularSecondCoeff fs gs α₂ N s * (z - z₀) ^ s) +
        regularSingularLogMultiplier fs gs α₂ N * regularSingularSolution fs gs z₀ (α₂ + N) z *
          Complex.log (z - z₀) :=
  (rfl)

/-- Function-level formula for `regularSingularSecondSolution`. -/
theorem regularSingularSecondSolution_eq (fs gs : ℕ → ℂ) (z₀ α₂ : ℂ) (N : ℕ) :
    regularSingularSecondSolution fs gs z₀ α₂ N = fun z =>
      (z - z₀) ^ α₂ * (∑' s, regularSingularSecondCoeff fs gs α₂ N s * (z - z₀) ^ s) +
        regularSingularLogMultiplier fs gs α₂ N * regularSingularSolution fs gs z₀ (α₂ + N) z *
          Complex.log (z - z₀) :=
  funext fun z => regularSingularSecondSolution_apply fs gs z₀ α₂ N z

/-- In the resonant case `α₁ = α₂ + N` (`N : ℕ`), the primary root `α₂ + N` satisfies the
non-resonance condition, so `regularSingularCoeff fs gs (α₂ + N)` converges on `‖z - z₀‖ < r`,
`regularSingularSolution fs gs z₀ (α₂ + N)` solves `regularSingularEquation hf hg`, and the
shifted logarithmic forcing coefficients sum to the Euler–Frobenius forcing series. -/
theorem regularSingularCoeff_solution_add_nat {z₀ α₂ : ℂ} {N : ℕ} {r : ℝ} {f g : ℂ → ℂ}
    {fs gs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hfact : ∀ α, indicialPoly (fs 0) (gs 0) α = (α - (α₂ + N)) * (α - α₂)) :
    (∀ z, ‖z - z₀‖ < r →
        Summable fun s => regularSingularCoeff fs gs (α₂ + N) s * (z - z₀) ^ s) ∧
      (regularSingularEquation hf hg).IsSolution
        (regularSingularSolution fs gs z₀ (α₂ + N)) ∧
      ∀ u : ℂ, ‖u‖ < r →
        HasSum
          (fun s =>
            regularSingularLogForcing fs (regularSingularCoeff fs gs (α₂ + N)) α₂ N s * u ^ s)
          (u ^ N * (2 * u *
              deriv (fun w => ∑' s, regularSingularCoeff fs gs (α₂ + N) s * w ^ s) u +
            (2 * (α₂ + N) + (∑' s, fs s * u ^ s) - 1) *
              ∑' s, regularSingularCoeff fs gs (α₂ + N) s * u ^ s)) := by
  obtain ⟨ha_sum, hw₁_sol⟩ := regularSingularCoeff_solution hf hg (by simp [hfact])
    fun s hs => indicialPoly_add_nat_ne_zero_of_re_le hfact (by simp) hs
  exact ⟨ha_sum, hw₁_sol, fun u hu => hasSum_regularSingularLogForcing_mul_pow (α₂ := α₂) (N := N)
    (fun w hw0 hwr => (hf w hw0 hwr).summable) ha_sum hu⟩

/-- **Logarithmic second solution at a regular singularity** (DLMF 2.7.6). When the indicial
polynomial factors as `(α - α₁)(α - α₂)` with `α₁ - α₂ = N ∈ ℕ`, the series
`∑ regularSingularSecondCoeff fs gs α₂ N s * (z - z₀)^s` converges on `‖z - z₀‖ < r`, and
`regularSingularSecondSolution fs gs z₀ α₂ N` solves `regularSingularEquation hf hg` on
`regularSingularSlitDisc z₀ r`. -/
theorem regularSingular_second_solution {z₀ α₁ α₂ : ℂ} {N : ℕ} {r : ℝ} {f g : ℂ → ℂ}
    {fs gs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hfact : ∀ α, indicialPoly (fs 0) (gs 0) α = (α - α₁) * (α - α₂))
    (hdiff : α₁ - α₂ = N) :
    (∀ z, ‖z - z₀‖ < r →
        Summable fun s => regularSingularSecondCoeff fs gs α₂ N s * (z - z₀) ^ s) ∧
      (regularSingularEquation hf hg).IsSolution
        (regularSingularSecondSolution fs gs z₀ α₂ N) := by
  have hα₁ : α₁ = α₂ + N := by linear_combination hdiff
  subst hα₁
  obtain ⟨hb_sum, hw₂_diff, hw₂_sol⟩ := regularSingular_log_solution
    (a := regularSingularCoeff fs gs (α₂ + N))
    (b := regularSingularSecondCoeff fs gs α₂ N)
    (c := regularSingularLogMultiplier fs gs α₂ N)
    (w := regularSingularSecondSolution fs gs z₀ α₂ N)
    hf hg (by simp [hfact]) rfl
    (fun s hs => indicialPoly_mul_regularSingularCoeff hs
      (indicialPoly_add_nat_ne_zero_of_re_le hfact (by simp) hs))
    (fun s hs => by
      have hrec := regularSingularSecondCoeff_rec hfact s
      rw [regularSingularLogForcing_of_lt _ _ _ hs, mul_zero, add_zero] at hrec
      linear_combination hrec)
    (fun s => by
      have hrec := regularSingularSecondCoeff_rec hfact (s + N)
      rw [show α₂ + ((s + N : ℕ) : ℂ) = (α₂ + N) + s by push_cast; ring] at hrec
      linear_combination hrec)
    (by
      funext w
      simp only [regularSingularSecondSolution_apply, regularSingularSolution_apply, mul_assoc])
  exact ⟨hb_sum, (isSolution_regularSingularEquation_iff hf hg _).mpr
    ⟨hw₂_diff, fun z hz => hw₂_sol z hz.1 hz.2⟩⟩

/-- **Analytic uniqueness of the second solution's coefficients**: for `0 < r` and
`α₁ - α₂ = N ∈ ℕ`, if `b' : ℕ → ℂ` and `c' : ℂ` satisfy `b' N = 0`, the normalization
`(N = 0 → c' = 1) ∧ (1 ≤ N → b' 0 = 1)`, convergence of `∑ b'_s (z - z₀)^s` on `‖z - z₀‖ < r`,
and `(z - z₀)^{α₂} ∑ b'_s (z - z₀)^s + c' * regularSingularSolution fs gs z₀ α₁ z * log(z - z₀)`
solves `w'' + f w' + g w = 0` on `{z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}`, then
`b' = regularSingularSecondCoeff fs gs α₂ N` and `c' = regularSingularLogMultiplier fs gs α₂ N`. -/
theorem eq_regularSingularSecondCoeff_of_solution {z₀ α₁ α₂ : ℂ} {N : ℕ} {r : ℝ}
    {f g : ℂ → ℂ} {fs gs b' : ℕ → ℂ} {c' : ℂ} (hr : 0 < r)
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s => gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hfact : ∀ α, indicialPoly (fs 0) (gs 0) α = (α - α₁) * (α - α₂))
    (hdiff : α₁ - α₂ = N)
    (hb'N : b' N = 0)
    (hc'0 : N = 0 → c' = 1)
    (hb'0 : 1 ≤ N → b' 0 = 1)
    (hb'_sum : ∀ z, ‖z - z₀‖ < r → Summable fun s => b' s * (z - z₀) ^ s)
    (hsol : ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      deriv (deriv (fun w =>
        (w - z₀) ^ α₂ * (∑' s, b' s * (w - z₀) ^ s) +
          c' * regularSingularSolution fs gs z₀ α₁ w * Complex.log (w - z₀))) z +
        f z * deriv (fun w =>
          (w - z₀) ^ α₂ * (∑' s, b' s * (w - z₀) ^ s) +
            c' * regularSingularSolution fs gs z₀ α₁ w * Complex.log (w - z₀)) z +
        g z * ((z - z₀) ^ α₂ * (∑' s, b' s * (z - z₀) ^ s) +
          c' * regularSingularSolution fs gs z₀ α₁ z * Complex.log (z - z₀)) = 0) :
    b' = regularSingularSecondCoeff fs gs α₂ N ∧
      c' = regularSingularLogMultiplier fs gs α₂ N := by
  have hα₁ : α₁ = α₂ + N := by linear_combination hdiff
  subst hα₁
  obtain ⟨ha_sum, hw₁_sol, hlog_sum⟩ := regularSingularCoeff_solution_add_nat hf hg hfact
  obtain ⟨_, hD_sum, hD_op⟩ :=
    operator_second_ansatz_eq (c' := c') hf hg ha_sum hw₁_sol hlog_sum hb'_sum
  exact eq_regularSingularSecondCoeff_of_rec hfact hb'N hc'0 hb'0 <|
    eq_zero_of_cpow_mul_tsum_eq_zero (z₀ := z₀) (α := α₂ - 2) hr (fun u _ hu => hD_sum u hu)
      fun z hzs hzb => (hD_op z ⟨hzs, hzb⟩).symm.trans (hsol z hzs hzb)

end TauCeti
