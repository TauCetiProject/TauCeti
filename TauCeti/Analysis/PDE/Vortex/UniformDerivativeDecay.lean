/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.DerivativeDecay
public import TauCeti.Analysis.PDE.Vortex.ModulusBound
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import TauCeti.Analysis.PDE.Regularity.PlanarGradientEstimate
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.SpecialFunctions.Exp.Deriv
import TauCeti.Analysis.SpecialFunctions.Exp.Shift
import TauCeti.Analysis.SpecialFunctions.Log.Bounds
import TauCeti.Analysis.SpecialFunctions.Log.Deriv

/-!
# Uniform decay of the derivatives of plane vortices away from their zeros

Let `x` be a smooth plane vortex with the degree-`m` end framing and zero divisor `D`, and write
`α` for its section, so that `|α|² = 4 (p² + q²)` in the coordinates `x = (b₁, b₂, p, q)`. The
modulus defect decays exponentially in the distance to the zeros with a constant depending only on
`m` and the rate: for `0 ≤ c < 1 / 2`, `1 - |α(z)|² ≤ K exp (-c ρ)` whenever every zero is at
distance at least `ρ` from `z`
(`TauCeti.Vortex.exists_one_sub_normSq_le_mul_exp_of_forall_le_norm_sub`). This file proves the
same uniform decay for the derivatives of every order of `log |α|²` and of the defect `1 - |α|²`,
and, at first order, for the gradient of `|α|²`, the covariant derivative `d_a α` and the energy
density. By the second vortex equation `*i F_a = (1 - |α|²) / 8`, the derivatives of the defect are
those of the curvature density. In each case the constants depend only on
`m` and the rate, not on the vortex or on the position of its zeros, so the estimates hold over
the whole noncompact space of divisors of degree `m`, for instance for clusters of zeros moving
apart. For a single vortex and decay in `|z|` instead, these are
`TauCeti.Vortex.exists_eventually_norm_fderiv_log_normSq_le_mul_exp`,
`TauCeti.Vortex.exists_norm_fderiv_normSq_le_mul_exp`,
`TauCeti.Vortex.exists_norm_covariantDerivative_le_mul_exp` and
`TauCeti.Vortex.exists_energyDensity_le_mul_exp`.

The estimates hold at distance at least a fixed `R` from the zeros, with `R` depending only on `m`
and the rate. Some threshold is needed for `log |α|²`, which tends to `-∞` at a zero.

The argument is local. At distance at least `L = √(2 m (16 m + 1))` from the zeros, `|α|² > 1 / 2`
(`TauCeti.Vortex.one_sub_lt_normSq_of_forall_le_norm_sub`). Let `z` be at distance `ρ ≥ L + 3`
from the zeros. On the closed disc of radius `3` about `z`, the function `ℓ = log |α|²` is then
smooth (`TauCeti.Vortex.contDiffAt_log_normSq_of_equation_eq_zero`) and solves
`Δ ℓ = (|α|² - 1) / 4` (`TauCeti.Vortex.laplacian_log_normSq_of_equation_eq_zero`). There
`|ℓ| ≤ 2 (1 - |α|²)` (`Real.abs_log_le_two_mul_one_sub`), and every point is at distance at least
`ρ - 3` from the zeros, so both `ℓ` and `Δ ℓ` are at most a constant times `exp (-c (ρ - 3))`.
The interior estimate for Poisson's equation, applied to the components of `Dⁿ ℓ`
(`TauCeti.norm_iteratedFDeriv_succ_le_of_norm_iteratedFDeriv_laplacian_le`), bounds `Dⁿ⁺¹ ℓ (z)`
by `Dⁿ ℓ` and `Dⁿ (Δ ℓ)` on the disc. Near the disc `Δ ℓ = (exp ℓ - 1) / 4`, so for `n ≥ 1` the
Faà di Bruno bound for `exp ℓ` (`ContDiffOn.norm_iteratedFDeriv_exp_comp_le`) controls `Dⁿ (Δ ℓ)`
by the derivatives of `ℓ` of orders `1` to `n`, and for `n = 0` it is the defect. By induction on
the order, every derivative of `ℓ` is at most a constant times `exp (-c ρ)` at distance at least
`L + 3 n` from the zeros. The derivatives of the defect `1 - |α|² = 1 - exp ℓ` follow by the same
Faà di Bruno bound. Since `∇ |α|² = |α|² ∇ ℓ` and `|α|² ≤ 1`, the first-order bound holds for the
gradient of `|α|²`, and where `|α|² ≥ 1 / 2` it controls the covariant derivative
(`TauCeti.Vortex.norm_covariantDerivative_one_le_norm_fderiv_normSq`).

## Main results

All in the namespace `TauCeti.Vortex`, for a degree `m` and a rate `0 ≤ c < 1 / 2`, with constants
`K` and `R` depending only on `m` and `c`, at every point at distance at least `ρ ≥ R` from every
zero:

* `exists_norm_iteratedFDeriv_log_normSq_le_mul_exp_of_forall_le_norm_sub`: for every order `n`,
  `‖Dⁿ log |α|²‖ ≤ K exp (-c ρ)`, with `K` and `R` depending also on `n`; the case `n = 1` is
  `exists_norm_fderiv_log_normSq_le_mul_exp_of_forall_le_norm_sub`.
* `exists_norm_iteratedFDeriv_one_sub_normSq_le_mul_exp_of_forall_le_norm_sub`: for every order
  `n`, `‖Dⁿ (1 - |α|²)‖ ≤ K exp (-c ρ)`.
* `exists_norm_fderiv_normSq_le_mul_exp_of_forall_le_norm_sub`: `|∇ |α|²| ≤ K exp (-c ρ)`.
* `exists_norm_covariantDerivative_le_mul_exp_of_forall_le_norm_sub`:
  `|d_a α (v)| ≤ K |v| exp (-c ρ)`.
* `exists_energyDensity_le_mul_exp_of_forall_le_norm_sub`: the energy density
  `|F_a|² + |d_a α|² + (1 - |α|²)²` is at most `K exp (-c ρ)`, here for every rate `0 ≤ c < 1`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 3.4 and Theorem 4.6.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter Metric Topology InnerProductSpace Laplacian
open scoped ContDiff

/-- At distance at least `√(2 m (16 m + 1))` from every zero, `|α|² > 1 / 2`: the case `δ = 1 / 2`
of `TauCeti.Vortex.one_sub_lt_normSq_of_forall_le_norm_sub`. -/
private theorem half_lt_normSq_of_forall_le_norm_sub {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0) {m : ℕ}
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    {D : Multiset ℂ} (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {z : ℂ}
    (hz : ∀ a ∈ D, Real.sqrt (m * (16 * m + 1) / (1 / 2)) ≤ ‖z - a‖) :
    1 / 2 < 4 * (x z 2 ^ 2 + x z 3 ^ 2) := by
  have := one_sub_lt_normSq_of_forall_le_norm_sub hx hsol hframe hD (lt_add_one _)
    (by norm_num : (0 : ℝ) < 1 / 2) hz
  linarith

/-- At distance at least `√(2 m (16 m + 1))` from every zero, the section does not vanish. -/
private theorem normSq_ne_zero_of_forall_le_norm_sub {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0) {m : ℕ}
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    {D : Multiset ℂ} (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {z : ℂ}
    (hz : ∀ a ∈ D, Real.sqrt (m * (16 * m + 1) / (1 / 2)) ≤ ‖z - a‖) :
    x z 2 ^ 2 + x z 3 ^ 2 ≠ 0 := fun h0 ↦ by
  have := half_lt_normSq_of_forall_le_norm_sub hx hsol hframe hD hz
  rw [h0, mul_zero] at this
  norm_num at this

/-- Where the section does not vanish, `|α|² = 4 (p² + q²)` is positive. -/
private theorem normSq_pos_of_ne_zero {x : ℂ → EuclideanSpace ℝ (Fin 4)} {w : ℂ}
    (hw : x w 2 ^ 2 + x w 3 ^ 2 ≠ 0) : 0 < 4 * (x w 2 ^ 2 + x w 3 ^ 2) :=
  mul_pos (by norm_num) ((by positivity : (0 : ℝ) ≤ x w 2 ^ 2 + x w 3 ^ 2).lt_of_ne' hw)

/-- A smooth vortex with the degree-`m` end framing satisfies `|α|² ≤ 1` everywhere: the framed
case of `TauCeti.Vortex.normSq_le_one_of_tendsto`. -/
private theorem normSq_le_one_of_framed {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0) {m : ℕ}
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    (w : ℂ) : 4 * (x w 2 ^ 2 + x w 3 ^ 2) ≤ 1 :=
  normSq_le_one_of_tendsto (((contDiff_piLp 2).1 hx 2).of_le (by simp))
    (((contDiff_piLp 2).1 hx 3).of_le (by simp)) hsol
    (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe) w

/-- The set where the section of a smooth vortex does not vanish is open. -/
private theorem isOpen_normSq_ne_zero {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x) :
    IsOpen {w | x w 2 ^ 2 + x w 3 ^ 2 ≠ 0} :=
  isOpen_ne_fun ((((contDiff_piLp 2).1 hx 2).continuous.pow 2).add
    (((contDiff_piLp 2).1 hx 3).continuous.pow 2)) continuous_const

/-- `log |α|²` is smooth where the section of a smooth vortex does not vanish. -/
private theorem contDiffOn_log_normSq {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x)
    (hsol : ∀ z, equation x z = 0) :
    ContDiffOn ℝ ∞ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2)))
      {w | x w 2 ^ 2 + x w 3 ^ 2 ≠ 0} := fun w hw ↦
  (contDiffAt_log_normSq_of_equation_eq_zero
    (((contDiff_piLp 2).1 hx 2).of_le (by simp)).contDiffAt
    (((contDiff_piLp 2).1 hx 3).of_le (by simp)).contDiffAt hw
    (Eventually.of_forall hsol)).contDiffWithinAt

/-- Near a point where the section of a smooth vortex does not vanish, the Laplacian of `log |α|²`
is `exp (log |α|²) / 4 - 1 / 4`. -/
private theorem laplacian_log_normSq_eventuallyEq_exp {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0) {y : ℂ}
    (hy : x y 2 ^ 2 + x y 3 ^ 2 ≠ 0) :
    Δ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) =ᶠ[𝓝 y]
      fun w ↦ (4 : ℝ)⁻¹ • Real.exp (Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) + -4⁻¹ := by
  have hp : ContDiff ℝ 2 fun w ↦ x w 2 := ((contDiff_piLp 2).1 hx 2).of_le (by simp)
  have hq : ContDiff ℝ 2 fun w ↦ x w 3 := ((contDiff_piLp 2).1 hx 3).of_le (by simp)
  filter_upwards [(isOpen_normSq_ne_zero hx).mem_nhds hy] with w hw
  rw [laplacian_log_normSq_of_equation_eq_zero hp.contDiffAt hq.contDiffAt hw
    (Eventually.of_forall hsol), Real.exp_log (normSq_pos_of_ne_zero hw), smul_eq_mul]
  ring

open scoped Nat in
/-- At a point `y` where the section of a smooth vortex does not vanish, let `f` agree near `y`
with `a exp (log |α|²) + b`, that is with `a |α|² + b`. If the derivatives of `log |α|²` of orders
`1` to `n` have norm at most `K E` at `y`, with `0 ≤ E ≤ 1`, then the derivative of order `n ≥ 1`
of `f` at `y` has norm at most `|a| n! max 1 K ^ n E`. -/
private theorem norm_iteratedFDeriv_le_of_eventuallyEq_smul_exp_log_normSq_add
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0)
    {y : ℂ} (hy : x y 2 ^ 2 + x y 3 ^ 2 ≠ 0) (hs₁ : 4 * (x y 2 ^ 2 + x y 3 ^ 2) ≤ 1) {n : ℕ}
    (hn : 1 ≤ n) {f : ℂ → ℝ} {a b : ℝ}
    (hf : f =ᶠ[𝓝 y] fun w ↦ a • Real.exp (Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) + b)
    {K E : ℝ} (hK : 0 ≤ K) (hE₀ : 0 ≤ E) (hE₁ : E ≤ 1)
    (hD : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDeriv ℝ i (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) y‖ ≤ K * E) :
    ‖iteratedFDeriv ℝ n f y‖ ≤ |a| * n ! * max 1 K ^ n * E := by
  have hU := isOpen_normSq_ne_zero hx
  have hℓ := contDiffOn_log_normSq hx hsol
  have hexp : ContDiffAt ℝ n (fun w ↦ Real.exp (Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2)))) y :=
    (Real.contDiff_exp.contDiffAt.comp y (hℓ.contDiffAt (hU.mem_nhds hy))).of_le (by simp)
  have hB := (hℓ.of_le (by simp)).norm_iteratedFDeriv_exp_comp_le hU hy (mul_nonneg hK hE₀) hD
  rw [Real.exp_log (normSq_pos_of_ne_zero hy)] at hB
  -- `max (K E) ((K E)ⁿ) ≤ max 1 K ^ n E`, since `E ≤ 1` and `n ≥ 1`.
  have hmax : max (K * E) ((K * E) ^ n) ≤ max 1 K ^ n * E := by
    refine max_le (mul_le_mul_of_nonneg_right ((le_max_right 1 K).trans
      (le_self_pow₀ (le_max_left 1 K) (by omega))) hE₀) ?_
    rw [mul_pow]
    exact mul_le_mul (pow_le_pow_left₀ hK (le_max_right 1 K) n)
      (pow_le_of_le_one hE₀ hE₁ (by omega)) (pow_nonneg hE₀ n) (by positivity)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [(hf.iteratedFDeriv ℝ (k + 1)).self_of_nhds, iteratedFDeriv_succ_add_const,
    iteratedFDeriv_const_smul_apply' hexp, norm_smul, Real.norm_eq_abs]
  calc _ ≤ |a| * ((k + 1)! * (4 * (x y 2 ^ 2 + x y 3 ^ 2)) * max (K * E) ((K * E) ^ (k + 1))) :=
        mul_le_mul_of_nonneg_left hB (abs_nonneg a)
    _ ≤ |a| * ((k + 1)! * 1 * (max 1 K ^ (k + 1) * E)) := by gcongr
    _ = _ := by ring

open scoped Nat in
/-- At a point where the section of a smooth vortex does not vanish, the derivative of order `n`
of `Δ log |α|² = (|α|² - 1) / 4` has norm at most `(K₀ + n! max 1 K ^ n) E / 4` when the
derivatives of `log |α|²` of order at most `n` have norm at most `K E` and the defect `1 - |α|²`
is at most `K₀ E`, with `0 ≤ E ≤ 1`. -/
private theorem norm_iteratedFDeriv_laplacian_log_normSq_le {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0) {y : ℂ}
    (hy : x y 2 ^ 2 + x y 3 ^ 2 ≠ 0) (hs₁ : 4 * (x y 2 ^ 2 + x y 3 ^ 2) ≤ 1) {n : ℕ}
    {K K₀ E : ℝ} (hK : 0 ≤ K) (hE₀ : 0 ≤ E) (hE₁ : E ≤ 1)
    (hD : ∀ i ≤ n,
      ‖iteratedFDeriv ℝ i (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) y‖ ≤ K * E)
    (hdef : 1 - 4 * (x y 2 ^ 2 + x y 3 ^ 2) ≤ K₀ * E) :
    ‖iteratedFDeriv ℝ n (Δ fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) y‖ ≤
      (K₀ + n ! * max 1 K ^ n) / 4 * E := by
  have : 0 ≤ K₀ * E := by linarith
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hxi (i : Fin 4) : ContDiff ℝ ∞ fun w ↦ x w i := (contDiff_piLp 2).1 hx i
    rw [norm_iteratedFDeriv_zero, laplacian_log_normSq_of_equation_eq_zero
      ((hxi 2).of_le (by simp)).contDiffAt ((hxi 3).of_le (by simp)).contDiffAt hy
      (Eventually.of_forall hsol), Real.norm_eq_abs, abs_div, abs_of_nonpos (by linarith)]
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul]
    nlinarith
  · have hB := norm_iteratedFDeriv_le_of_eventuallyEq_smul_exp_log_normSq_add hx hsol hy hs₁ hn
      (laplacian_log_normSq_eventuallyEq_exp hx hsol hy) hK hE₀ hE₁
      fun i _ hi ↦ hD i hi
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 4⁻¹)] at hB
    nlinarith

open scoped Nat in
/-- The induction step for the derivatives of `log |α|²`. Let `x` be a smooth vortex with the
degree-`m` end framing, let `R ≥ √(2 m (16 m + 1))`, and suppose that at every point at distance at
least `ρ' ≥ R` from the zeros the derivatives of `log |α|²` of order at most `n` have norm at most
`K exp (-c ρ')`, while the defect `1 - |α|²` is at most `K₀ exp (-c ρ')` wherever the distance is
at least `ρ'`. Then at distance at least `ρ ≥ R + 3` the derivative of order `n + 1` has norm at
most `exp (3 c) (8 K + 340 (K₀ + n! max 1 K ^ n) / 4) exp (-c ρ)`. -/
private theorem norm_iteratedFDeriv_succ_log_normSq_le {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0) {m : ℕ}
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    {D : Multiset ℂ} (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {n : ℕ}
    {c K K₀ R ρ : ℝ} {z : ℂ} (hc₀ : 0 ≤ c) (hK : 0 ≤ K)
    (hLR : Real.sqrt (m * (16 * m + 1) / (1 / 2)) ≤ R) (hR : R + 3 ≤ ρ)
    (hρ : ∀ a ∈ D, ρ ≤ ‖z - a‖)
    (hdef : ∀ w ρ', (∀ a ∈ D, ρ' ≤ ‖w - a‖) →
      1 - 4 * (x w 2 ^ 2 + x w 3 ^ 2) ≤ K₀ * Real.exp (-(c * ρ')))
    (hlow : ∀ w ρ', R ≤ ρ' → (∀ a ∈ D, ρ' ≤ ‖w - a‖) → ∀ j ≤ n,
      ‖iteratedFDeriv ℝ j (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) w‖ ≤
        K * Real.exp (-(c * ρ'))) :
    ‖iteratedFDeriv ℝ (n + 1) (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z‖ ≤
      Real.exp (c * 3) * (8 * K + 340 * ((K₀ + n ! * max 1 K ^ n) / 4)) *
        Real.exp (-(c * ρ)) := by
  have hU := isOpen_normSq_ne_zero hx
  have hℓ := contDiffOn_log_normSq hx hsol
  set E : ℝ := Real.exp (-(c * (ρ - 3)))
  have hE₀ : 0 ≤ E := (Real.exp_pos _).le
  have hρ₃ : 0 ≤ ρ - 3 := by linarith [(Real.sqrt_nonneg _).trans hLR]
  have hE₁ : E ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hc₀ hρ₃))
  -- Every point of the closed disc of radius `3` about `z` is at distance at least `ρ - 3 ≥ R`
  -- from the zeros, so there `|α|² > 1 / 2`.
  have hfar (w : ℂ) (hw : w ∈ closedBall z 3) (a : ℂ) (ha : a ∈ D) : ρ - 3 ≤ ‖w - a‖ := by
    have hwz : ‖w - z‖ ≤ 3 := by rw [← dist_eq_norm]; exact mem_closedBall.1 hw
    have := norm_sub_le_norm_sub_add_norm_sub z w a
    rw [norm_sub_rev z w] at this
    linarith [hρ a ha]
  have hα (w : ℂ) (hw : w ∈ closedBall z 3) : x w 2 ^ 2 + x w 3 ^ 2 ≠ 0 :=
    normSq_ne_zero_of_forall_le_norm_sub hx hsol hframe hD fun a ha ↦
      (show Real.sqrt (m * (16 * m + 1) / (1 / 2)) ≤ ‖w - a‖ by linarith [hfar w hw a ha])
  have hlow' (w : ℂ) (hw : w ∈ closedBall z 3) :=
    hlow w (ρ - 3) (by linarith) (hfar w hw)
  -- The interior estimate for the derivatives, with the bound on `Dⁿ (Δ log |α|²)` on the disc.
  have hest := norm_iteratedFDeriv_succ_le_of_norm_iteratedFDeriv_laplacian_le
    (u := fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) (x := z) (ρ := 1) (ε := K * E)
    (K := (K₀ + n ! * max 1 K ^ n) / 4 * E) (n := n)
    (fun w hw ↦ (hℓ.contDiffAt (hU.mem_nhds (hα w (by simpa using hw)))).of_le (by simp)) one_pos
    (fun w hw ↦ hlow' w (ball_subset_closedBall (ball_subset_ball (by norm_num) hw)) n le_rfl)
    (fun w hw ↦ have hw' := ball_subset_closedBall (by simpa using hw)
      norm_iteratedFDeriv_laplacian_log_normSq_le hx hsol (hα w hw')
        (normSq_le_one_of_framed hx hsol hframe w) hK hE₀ hE₁ (hlow' w hw')
        (hdef w (ρ - 3) (hfar w hw')))
  calc _ ≤ 8 * (K * E) / 1 + 340 * ((K₀ + n ! * max 1 K ^ n) / 4 * E) * 1 := hest
    _ = _ := by
      simp only [E, exp_neg_mul_sub]
      ring

open scoped Nat in
/-- Uniform decay of the derivatives of `log |α|²` of order at most `n`, with a radius `R` beyond
the threshold `√(2 m (16 m + 1))` where `|α|² > 1 / 2`. -/
private theorem exists_forall_le_norm_iteratedFDeriv_log_normSq_le_mul_exp (m n : ℕ) {c : ℝ}
    (hc₀ : 0 ≤ c) (hc : c < 1 / 2) :
    ∃ K R, 0 ≤ K ∧ Real.sqrt (m * (16 * m + 1) / (1 / 2)) ≤ R ∧
      ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) →
      ∀ z ρ, R ≤ ρ → (∀ a ∈ D, ρ ≤ ‖z - a‖) → ∀ j ≤ n,
        ‖iteratedFDeriv ℝ j (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z‖ ≤
          K * Real.exp (-(c * ρ)) := by
  obtain ⟨K₀, hK₀, hdef⟩ := exists_one_sub_normSq_le_mul_exp_of_forall_le_norm_sub m hc₀ hc
  induction n with
  | zero =>
    -- Order zero: `|log |α|²| ≤ 2 (1 - |α|²)` where `|α|² ≥ 1 / 2`.
    refine ⟨2 * K₀, _, by positivity, le_rfl, fun x D hx hsol hframe hD z ρ hR hρ j hj ↦ ?_⟩
    obtain rfl : j = 0 := by omega
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    exact (Real.abs_log_le_two_mul_one_sub (half_lt_normSq_of_forall_le_norm_sub hx hsol hframe hD
      fun a ha ↦ hR.trans (hρ a ha)).le (normSq_le_one_of_framed hx hsol hframe z)).trans
      (by linarith [hdef x D hx hsol hframe hD z ρ hρ])
  | succ n ih =>
    obtain ⟨K, R, hK, hLR, h⟩ := ih
    refine ⟨max K (Real.exp (c * 3) * (8 * K + 340 * ((K₀ + n ! * max 1 K ^ n) / 4))), R + 3,
      le_max_of_le_left hK, by linarith, fun x D hx hsol hframe hD z ρ hR hρ j hj ↦ ?_⟩
    rcases Nat.lt_or_eq_of_le hj with hj | rfl
    · exact (h x D hx hsol hframe hD z ρ (by linarith) hρ j (by omega)).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    · exact (norm_iteratedFDeriv_succ_log_normSq_le hx hsol hframe hD hc₀ hK hLR hR hρ
        (hdef x D hx hsol hframe hD) (h x D hx hsol hframe hD)).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)

/-- **Uniform exponential decay of all derivatives of `log |α|²` away from the zeros.** For every
degree `m`, order `n` and rate `0 ≤ c < 1 / 2` there are constants `K ≥ 0` and `R` such that every
smooth plane vortex with the degree-`m` end framing and zero divisor `D` satisfies
`‖Dⁿ log |α|²‖ ≤ K exp (-c ρ)` at every point whose distance to every zero is at least `ρ ≥ R`. -/
theorem exists_norm_iteratedFDeriv_log_normSq_le_mul_exp_of_forall_le_norm_sub (m n : ℕ) {c : ℝ}
    (hc₀ : 0 ≤ c) (hc : c < 1 / 2) :
    ∃ K R, 0 ≤ K ∧ ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) →
      ∀ z ρ, R ≤ ρ → (∀ a ∈ D, ρ ≤ ‖z - a‖) →
        ‖iteratedFDeriv ℝ n (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z‖ ≤
          K * Real.exp (-(c * ρ)) := by
  obtain ⟨K, R, hK, -, h⟩ := exists_forall_le_norm_iteratedFDeriv_log_normSq_le_mul_exp m n hc₀ hc
  exact ⟨K, R, hK, fun x D hx hsol hframe hD z ρ hR hρ ↦
    h x D hx hsol hframe hD z ρ hR hρ n le_rfl⟩

open scoped Nat in
/-- **Uniform exponential decay of all derivatives of the modulus defect away from the zeros.** For
every degree `m`, order `n` and rate `0 ≤ c < 1 / 2` there are constants `K ≥ 0` and `R` such that
every smooth plane vortex with the degree-`m` end framing and zero divisor `D` satisfies
`‖Dⁿ (1 - |α|²)‖ ≤ K exp (-c ρ)` at every point whose distance to every zero is at least
`ρ ≥ R`. By the second vortex equation `*i F_a = (1 - |α|²) / 8`, these are also the bounds on
the derivatives of the curvature density. -/
theorem exists_norm_iteratedFDeriv_one_sub_normSq_le_mul_exp_of_forall_le_norm_sub (m n : ℕ)
    {c : ℝ} (hc₀ : 0 ≤ c) (hc : c < 1 / 2) :
    ∃ K R, 0 ≤ K ∧ ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) →
      ∀ z ρ, R ≤ ρ → (∀ a ∈ D, ρ ≤ ‖z - a‖) →
        ‖iteratedFDeriv ℝ n (fun w ↦ 1 - 4 * (x w 2 ^ 2 + x w 3 ^ 2)) z‖ ≤
          K * Real.exp (-(c * ρ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- Order zero is the decay of the defect itself, which is nonnegative.
    obtain ⟨K₀, hK₀, hdef⟩ := exists_one_sub_normSq_le_mul_exp_of_forall_le_norm_sub m hc₀ hc
    refine ⟨K₀, 0, hK₀, fun x D hx hsol hframe hD z ρ _ hρ ↦ ?_⟩
    have hs₁ := normSq_le_one_of_framed hx hsol hframe z
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    exact hdef x D hx hsol hframe hD z ρ hρ
  -- Positive orders: near `z`, `1 - |α|² = (-1) exp (log |α|²) + 1`.
  obtain ⟨K, R, hK, hLR, h⟩ := exists_forall_le_norm_iteratedFDeriv_log_normSq_le_mul_exp m n hc₀ hc
  refine ⟨n ! * max 1 K ^ n, R, by positivity, fun x D hx hsol hframe hD z ρ hR hρ ↦ ?_⟩
  have hU := isOpen_normSq_ne_zero hx
  have hα : x z 2 ^ 2 + x z 3 ^ 2 ≠ 0 :=
    normSq_ne_zero_of_forall_le_norm_sub hx hsol hframe hD fun a ha ↦
      hLR.trans (hR.trans (hρ a ha))
  have hE₁ : Real.exp (-(c * ρ)) ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2
    (mul_nonneg hc₀ ((Real.sqrt_nonneg _).trans (hLR.trans hR))))
  have heq : (fun w ↦ 1 - 4 * (x w 2 ^ 2 + x w 3 ^ 2)) =ᶠ[𝓝 z]
      fun w ↦ (-1 : ℝ) • Real.exp (Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) + 1 := by
    filter_upwards [hU.mem_nhds hα] with w hw
    rw [Real.exp_log (normSq_pos_of_ne_zero hw), smul_eq_mul]
    ring
  have hB := norm_iteratedFDeriv_le_of_eventuallyEq_smul_exp_log_normSq_add hx hsol hα
    (normSq_le_one_of_framed hx hsol hframe z) hn heq hK (Real.exp_pos _).le hE₁
    fun i _ hi ↦ h x D hx hsol hframe hD z ρ hR hρ i hi
  rwa [abs_neg, abs_one, one_mul] at hB

/-- **Uniform exponential decay of the gradient of `log |α|²` away from the zeros.** For every
degree `m` and rate `0 ≤ c < 1 / 2` there are constants `K ≥ 0` and `R` such that every smooth plane
vortex with the degree-`m` end framing and zero divisor `D` satisfies
`|∇ log |α|²| ≤ K exp (-c ρ)` at every point whose distance to every zero is at least `ρ ≥ R`. This
is the case `n = 1` of
`TauCeti.Vortex.exists_norm_iteratedFDeriv_log_normSq_le_mul_exp_of_forall_le_norm_sub`. -/
theorem exists_norm_fderiv_log_normSq_le_mul_exp_of_forall_le_norm_sub (m : ℕ) {c : ℝ}
    (hc₀ : 0 ≤ c) (hc : c < 1 / 2) :
    ∃ K R, 0 ≤ K ∧ ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) →
      ∀ z ρ, R ≤ ρ → (∀ a ∈ D, ρ ≤ ‖z - a‖) →
        ‖fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z‖ ≤
          K * Real.exp (-(c * ρ)) := by
  obtain ⟨K, R, hK, h⟩ :=
    exists_norm_iteratedFDeriv_log_normSq_le_mul_exp_of_forall_le_norm_sub m 1 hc₀ hc
  exact ⟨K, R, hK, fun x D hx hsol hframe hD z ρ hR hρ ↦ by
    simpa only [norm_iteratedFDeriv_one] using h x D hx hsol hframe hD z ρ hR hρ⟩

/-- **Uniform exponential decay of the gradient of `|α|²` away from the zeros.** For every degree
`m` and rate `0 ≤ c < 1 / 2` there are constants `K ≥ 0` and `R` such that every smooth plane vortex
with the degree-`m` end framing and zero divisor `D` satisfies `|∇ |α|²| ≤ K exp (-c ρ)` at every
point whose distance to every zero is at least `ρ ≥ R`. -/
theorem exists_norm_fderiv_normSq_le_mul_exp_of_forall_le_norm_sub (m : ℕ) {c : ℝ}
    (hc₀ : 0 ≤ c) (hc : c < 1 / 2) :
    ∃ K R, 0 ≤ K ∧ ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) →
      ∀ z ρ, R ≤ ρ → (∀ a ∈ D, ρ ≤ ‖z - a‖) →
        ‖fderiv ℝ (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) z‖ ≤ K * Real.exp (-(c * ρ)) := by
  obtain ⟨K, R, hK₀, hK⟩ := exists_norm_fderiv_log_normSq_le_mul_exp_of_forall_le_norm_sub m hc₀ hc
  set L : ℝ := Real.sqrt (m * (16 * m + 1) / (1 / 2))
  refine ⟨K, max R L, hK₀, fun x D hx hsol hframe hD z ρ hR hρ ↦ ?_⟩
  have hxi (i : Fin 4) : ContDiff ℝ ∞ fun w ↦ x w i := (contDiff_piLp 2).1 hx i
  have hp : ContDiff ℝ 2 fun w ↦ x w 2 := (hxi 2).of_le (by simp)
  have hq : ContDiff ℝ 2 fun w ↦ x w 3 := (hxi 3).of_le (by simp)
  have hpos : 1 / 2 < 4 * (x z 2 ^ 2 + x z 3 ^ 2) :=
    half_lt_normSq_of_forall_le_norm_sub hx hsol hframe hD fun a ha ↦
      (le_max_right R L).trans (hR.trans (hρ a ha))
  have hs₁ := normSq_le_one_of_framed hx hsol hframe z
  -- Where `0 < |α|² ≤ 1`, `|∇ |α|²| ≤ |∇ log |α|²|`.
  exact (norm_fderiv_le_norm_fderiv_log (((contDiff_normSq hp hq).differentiable (by norm_num)) z)
    (by linarith) hs₁).trans (hK x D hx hsol hframe hD z ρ ((le_max_left R L).trans hR) hρ)

/-- **Uniform exponential decay of the covariant derivative of plane vortices away from the
zeros.** For every degree `m` and rate `0 ≤ c < 1 / 2` there are constants `K ≥ 0` and `R` such that
every smooth plane vortex with the degree-`m` end framing and zero divisor `D` satisfies
`|d_a α (v)| ≤ K |v| exp (-c ρ)` at every point whose distance to every zero is at least `ρ ≥ R`. -/
theorem exists_norm_covariantDerivative_le_mul_exp_of_forall_le_norm_sub (m : ℕ) {c : ℝ}
    (hc₀ : 0 ≤ c) (hc : c < 1 / 2) :
    ∃ K R, 0 ≤ K ∧ ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) →
      ∀ z ρ, R ≤ ρ → (∀ a ∈ D, ρ ≤ ‖z - a‖) →
        ∀ v, ‖covariantDerivative x z v‖ ≤ K * ‖v‖ * Real.exp (-(c * ρ)) := by
  obtain ⟨K, R, hK₀, hK⟩ := exists_norm_fderiv_normSq_le_mul_exp_of_forall_le_norm_sub m hc₀ hc
  set L : ℝ := Real.sqrt (m * (16 * m + 1) / (1 / 2))
  refine ⟨K, max R L, hK₀, fun x D hx hsol hframe hD z ρ hR hρ v ↦ ?_⟩
  have hxi (i : Fin 4) : ContDiff ℝ ∞ fun w ↦ x w i := (contDiff_piLp 2).1 hx i
  have hp : DifferentiableAt ℝ (fun w ↦ x w 2) z := ((hxi 2).differentiable (by simp)) z
  have hq : DifferentiableAt ℝ (fun w ↦ x w 3) z := ((hxi 3).differentiable (by simp)) z
  have hhalf : 1 / 2 ≤ 4 * (x z 2 ^ 2 + x z 3 ^ 2) :=
    (half_lt_normSq_of_forall_le_norm_sub hx hsol hframe hD fun a ha ↦
      (le_max_right R L).trans (hR.trans (hρ a ha))).le
  -- `d_a α` is complex linear, and `|d_a α (1)|` is bounded by the gradient of `|α|²`.
  rw [norm_covariantDerivative_eq_mul_of_equation_eq_zero hp hq (by simp [hsol z])
    (by simp [hsol z]) v, mul_comm K, mul_assoc]
  exact mul_le_mul_of_nonneg_left ((norm_covariantDerivative_one_le_norm_fderiv_normSq hp hq
    (by simp [hsol z]) (by simp [hsol z]) hhalf).trans
    (hK x D hx hsol hframe hD z ρ ((le_max_left R L).trans hR) hρ)) (norm_nonneg v)

/-- **Uniform exponential decay of the energy density of plane vortices away from the zeros.** For
every degree `m` and rate `0 ≤ c < 1` there are constants `K ≥ 0` and `R` such that every smooth
plane vortex with the degree-`m` end framing and zero divisor `D` has energy density
`|F_a|² + |d_a α|² + (1 - |α|²)²` at most `K exp (-c ρ)` at every point whose distance to every zero
is at least `ρ ≥ R`. -/
theorem exists_energyDensity_le_mul_exp_of_forall_le_norm_sub (m : ℕ) {c : ℝ} (hc₀ : 0 ≤ c)
    (hc : c < 1) :
    ∃ K R, 0 ≤ K ∧ ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) →
      ∀ z ρ, R ≤ ρ → (∀ a ∈ D, ρ ≤ ‖z - a‖) →
        energyDensity x z ≤ K * Real.exp (-(c * ρ)) := by
  have hc₀' : 0 ≤ c / 2 := by positivity
  have hc' : c / 2 < 1 / 2 := by linarith
  obtain ⟨K₁, -, hK₁⟩ := exists_one_sub_normSq_le_mul_exp_of_forall_le_norm_sub m hc₀' hc'
  obtain ⟨K₂, R, -, hK₂⟩ :=
    exists_norm_covariantDerivative_le_mul_exp_of_forall_le_norm_sub m hc₀' hc'
  refine ⟨65 / 64 * K₁ ^ 2 + 2 * K₂ ^ 2, R, by positivity,
    fun x D hx hsol hframe hD z ρ hR hρ ↦ ?_⟩
  have hxi (i : Fin 4) : ContDiff ℝ ∞ fun w ↦ x w i := (contDiff_piLp 2).1 hx i
  have hs₁ := normSq_le_one_of_tendsto ((hxi 2).of_le (by simp)) ((hxi 3).of_le (by simp)) hsol
    (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe) z
  -- The modulus defect is at most `K₁ exp (-(c / 2) ρ)`, and `|d_a α (1)| ≤ K₂ exp (-(c / 2) ρ)`.
  refine (energyDensity_le_of_equation_eq_zero (((hxi 2).differentiable (by simp)) z)
    (((hxi 3).differentiable (by simp)) z) (hsol z) (by linarith)
    (hK₁ x D hx hsol hframe hD z ρ hρ)
    (by simpa using hK₂ x D hx hsol hframe hD z ρ hR hρ 1)).trans_eq ?_
  rw [mul_pow, mul_pow, exp_neg_half_mul_sq]
  ring

end TauCeti.Vortex
