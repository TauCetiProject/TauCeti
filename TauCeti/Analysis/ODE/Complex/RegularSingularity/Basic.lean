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

import TauCeti.Analysis.Analytic.OfScalars
import TauCeti.Analysis.Complex.PowerSeries.BranchCut
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.ODE.Complex.RegularSingularity.Primary
import TauCeti.Analysis.ODE.Complex.RegularSingularPoint

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
  obtain ⟨hb, hc⟩ := (forall_regularSingularLogForcing_rec_iff rfl).mp
    (regularSingularSecondCoeff_rec hfact)
  obtain ⟨hb_sum, hw₂_diff, hw₂_sol⟩ := regularSingular_log_solution
    (a := regularSingularCoeff fs gs (α₂ + N))
    (b := regularSingularSecondCoeff fs gs α₂ N)
    (c := regularSingularLogMultiplier fs gs α₂ N)
    (w := regularSingularSecondSolution fs gs z₀ α₂ N)
    hf hg (by simp [hfact]) rfl
    (fun s hs => indicialPoly_mul_regularSingularCoeff hs
      (indicialPoly_add_nat_ne_zero_of_re_le hfact (by simp) hs))
    hb hc
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
  obtain ⟨ha_sum, hw₁_sol⟩ := regularSingularCoeff_solution hf hg (by simp [hfact])
    fun _ hs => indicialPoly_add_nat_ne_zero_of_re_le hfact (by simp) hs
  have hw₁_op : ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      deriv (deriv fun w => (w - z₀) ^ (α₂ + (N : ℂ)) *
          ∑' s, regularSingularCoeff fs gs (α₂ + N) s * (w - z₀) ^ s) z +
        f z * deriv (fun w => (w - z₀) ^ (α₂ + (N : ℂ)) *
          ∑' s, regularSingularCoeff fs gs (α₂ + N) s * (w - z₀) ^ s) z +
        g z * ((z - z₀) ^ (α₂ + (N : ℂ)) *
          ∑' s, regularSingularCoeff fs gs (α₂ + N) s * (z - z₀) ^ s) = 0 := by
    have hw₁ := ((isSolution_regularSingularEquation_iff hf hg _).mp hw₁_sol).2
    intro z hzs hzb
    rw [regularSingularSolution_eq] at hw₁
    exact hw₁ z ⟨hzs, hzb⟩
  obtain ⟨_, hD_sum, hD_op⟩ := deriv_deriv_add_mul_deriv_add_mul_cpow_mul_tsum_add_log
    (c := c') hf hg ha_sum hb'_sum hw₁_op
  exact eq_regularSingularSecondCoeff_of_rec hfact hb'N hc'0 hb'0 <|
    eq_zero_of_cpow_mul_tsum_eq_zero (z₀ := z₀) (α := α₂ - 2) hr (fun u _ hu => hD_sum u hu)
      fun z hzs hzb => by
        have hD := hD_op z hzs hzb
        have hsolz := hsol z hzs hzb
        simp only [regularSingularSolution_apply, mul_assoc] at hD hsolz
        exact hD.symm.trans hsolz

end TauCeti
