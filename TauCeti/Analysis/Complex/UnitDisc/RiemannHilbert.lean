/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Topology.MetricSpace.Holder
public import TauCeti.Analysis.Complex.Pompeiu.Basic
public import TauCeti.Analysis.Complex.UnitDisc.RotatingLineBoundary
import Mathlib.Analysis.Complex.LocallyUniformLimit
import TauCeti.Analysis.Complex.BoundaryHolder
import TauCeti.Analysis.Complex.Circle
import TauCeti.Analysis.Complex.CircleRotation
import TauCeti.Analysis.Complex.PowerSeries.FourierCoeff
import TauCeti.Analysis.Complex.UnitDisc.CauchyIntegralHolder
import TauCeti.Analysis.Complex.Wirtinger.Holomorphic
import TauCeti.Analysis.Fourier.AddCircle
import TauCeti.Analysis.Fourier.Decay
import TauCeti.Analysis.Fourier.FourierCoeffOn
import TauCeti.Analysis.Holder.MeanValue
import TauCeti.Analysis.SpecialFunctions.Complex.CircleMap
import TauCeti.MeasureTheory.Integral.Circle.Haar
import TauCeti.Topology.MetricSpace.Holder

/-!
# The Riemann–Hilbert problem on the disc with boundary values on a rotating line

Fix an integer `k`. The file `TauCeti.Analysis.Complex.UnitDisc.RotatingLineBoundary` computes the
kernel of the Cauchy–Riemann operator `∂/∂(conj z)` on the closed unit disc with the boundary
condition `u w = w ^ k * conj (u w)` on the unit circle, that is `u(e^{iθ}) ∈ e^{ikθ/2} ℝ`, whose
loop of real lines has Maslov index `k`. This file treats the cokernel side, following the Fourier
series computation of McDuff and Salamon, Theorem C.4.1.

**The boundary problem.** For a function `φ` on the unit circle, the *Riemann–Hilbert problem*
asks for `h` holomorphic on the open disc and continuous on the closed disc with
`h w - w ^ k * conj (h w) = φ w` on the circle. The left side always satisfies
`ψ w = -(w ^ k * conj (ψ w))`, so `φ(e^{iθ})` is required to lie on the line `i e^{ikθ/2} ℝ`.
Write `c n` for the `n`-th Fourier coefficient of `θ ↦ φ(e^{iθ})` on `[0, 2π]`. The condition
on `φ` reads `c n = -conj (c (k - n))`, and for `h = ∑ aₙ zⁿ` the problem reads
`aₙ - conj a_{k-n} = c n` for every integer `n`, with `aₙ = 0` for `n < 0`. If the Fourier
coefficients are summable, the problem is solved by

`aₙ = c n / 2` for `0 ≤ n ≤ k` and `aₙ = c n` for `n > k`

(`TauCeti.unitDiscRiemannHilbertSolution`), exactly when `c n = 0` for `k < n < 0`. Those
`-1 - k` complex numbers come in conjugate pairs `c n = -conj (c (k - n))`, so they are `-1 - k`
real conditions. For `k ≥ -1` there are none and the problem is always solvable
(`TauCeti.exists_diffContOnCl_sub_zpow_mul_conj_eq`); for `k ≤ -2` the conditions are necessary
too (`TauCeti.exists_diffContOnCl_sub_zpow_mul_conj_eq_iff`), since a function holomorphic on the
disc has vanishing negative Fourier coefficients on the circle. A function `φ` with
`θ ↦ φ(e^{iθ})` of class `C²` has Fourier coefficients of size `O(n⁻²)`, which are summable
(`TauCeti.summable_fourierCoeffOn_circleMap_of_contDiff`), and summable Fourier coefficients
of a continuous `θ ↦ φ(e^{iθ})` sum to `φ` on the circle
(`TauCeti.hasSum_fourierCoeffOn_circleMap_mul_zpow`).

**Hölder data.** For `α`-Hölder data, `0 < α < 1`, the Fourier coefficients need not be summable,
and the solution is built from the Cauchy integral instead: by Privalov's theorem it extends to an
`α`-Hölder function `G` on the closed disc whose boundary values have the Fourier coefficients `c n`
for `n ≥ 0` and `0` for `n < 0`. So `h = G - ∑_{0 ≤ n ≤ k} (c n / 2) zⁿ` has on the circle the
Fourier coefficients `aₙ` above, and solves the problem when `c n = 0` for `k < n < 0`, in
particular for every `k ≥ -1`
(`TauCeti.exists_holderOnWith_closedBall_sub_zpow_mul_conj_eq_of_fourierCoeffOn_eq_zero`,
`TauCeti.exists_holderOnWith_closedBall_sub_zpow_mul_conj_eq`). If moreover `φ` has an
`α`-Hölder derivative along the rotations, the derivative of `h` extends to an `α`-Hölder function
on the closed disc
(`TauCeti.exists_holderOnWith_closedBall_deriv_sub_zpow_mul_conj_eq_of_fourierCoeffOn_eq_zero`):
the boundary values of `G` then have the extension of the Cauchy integral of that derivative as
their derivative along the rotations, and `TauCeti.Analysis.Complex.BoundaryHolder` applies.

**Surjectivity.** For `k ≥ -1` the operator `∂/∂(conj z)` with this boundary condition is
onto, on compactly supported `C²` data
(`TauCeti.exists_conjWirtingerDeriv_eq_and_eq_zpow_mul_conj`): a solution of
`∂u/∂(conj z) = f` on the open disc with `u w = w ^ k * conj (u w)` on the circle is
`u = T f + h`, where `T f` is the Cauchy transform of `f`, which inverts `∂/∂(conj z)` on the whole
plane and is `C²`, and `h` solves the Riemann–Hilbert problem with
`φ w = w ^ k * conj (T f w) - T f w`, correcting the boundary values. The solution is unique up
to the kernel `TauCeti.unitDiscCauchyRiemannKernel k`
(`TauCeti.domRestrict_sub_mem_unitDiscCauchyRiemannKernel`). So for `k ≥ -1` the operator has no
cokernel on this class of data, and the index `k + 1` predicted by the Riemann–Roch formula
`n χ + μ` with `n = 1`, `χ = 1`, `μ = k` is the dimension of its kernel.

## Main definitions

* `TauCeti.unitDiscRiemannHilbertSolution k φ`: the power series `∑ aₙ zⁿ` with `aₙ = c n / 2`
  for `0 ≤ n ≤ k` and `aₙ = c n` for `n > k`.

## Main results

* `TauCeti.hasSum_unitDiscRiemannHilbertSolution`: for summable nonnegative-index Fourier
  coefficients the series converges on the closed disc.
* `TauCeti.diffContOnCl_unitDiscRiemannHilbertSolution`: for summable nonnegative-index Fourier
  coefficients the series is holomorphic on the open disc and continuous on the closed disc.
* `TauCeti.unitDiscRiemannHilbertSolution_sub_zpow_mul_conj`: it solves the Riemann–Hilbert
  problem when `c n = 0` for `k < n < 0`.
* `TauCeti.exists_diffContOnCl_sub_zpow_mul_conj_eq_iff`: the problem is solvable exactly when
  `c n = 0` for `k < n < 0`.
* `TauCeti.exists_diffContOnCl_sub_zpow_mul_conj_eq`: for `k ≥ -1` it is always solvable.
* `TauCeti.exists_holderOnWith_closedBall_sub_zpow_mul_conj_eq_of_fourierCoeffOn_eq_zero`,
  `TauCeti.exists_holderOnWith_closedBall_sub_zpow_mul_conj_eq`: for `α`-Hölder data there is a
  solution `α`-Hölder on the closed disc.
* `TauCeti.exists_holderOnWith_closedBall_deriv_sub_zpow_mul_conj_eq_of_fourierCoeffOn_eq_zero`:
  for data with an `α`-Hölder derivative along the rotations there is a solution whose derivative
  is `α`-Hölder on the closed disc.
* `TauCeti.exists_conjWirtingerDeriv_eq_and_eq_zpow_mul_conj_of_fourierCoeffOn_eq_zero`: for every
  `k`, `∂u/∂(conj z) = f` with boundary values `u(e^{iθ}) ∈ e^{ikθ/2} ℝ` is solvable when the
  boundary defect of the Cauchy transform of `f` has vanishing Fourier coefficients for
  `k < n < 0`.
* `TauCeti.exists_conjWirtingerDeriv_eq_and_eq_zpow_mul_conj`: for `k ≥ -1`, `∂/∂(conj z)` with
  boundary values `u(e^{iθ}) ∈ e^{ikθ/2} ℝ` is onto on compactly supported `C²` data.
* `TauCeti.domRestrict_sub_mem_unitDiscCauchyRiemannKernel`: two solutions differ by an element of
  the kernel `TauCeti.unitDiscCauchyRiemannKernel k`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Theorem C.4.1 (p. 598) and its proof by Fourier series.
-/

public section

namespace TauCeti

open AddCircle Complex MeasureTheory Metric Set
open scoped ComplexConjugate NNReal Real

/-! ### The explicit solution -/

/-- The explicit solution of the Riemann–Hilbert problem on the unit disc with boundary values on
the rotating lines `e^{ikθ/2} ℝ` at `w = e^{iθ}`: the power series `∑ aₙ zⁿ` whose coefficient
`aₙ` is the `n`-th Fourier coefficient `c n` of `θ ↦ φ(e^{iθ})` on `[0, 2π]`, halved for `n ≤ k`.
When the Fourier coefficients `c n` with `n ≥ 0` are summable, it is holomorphic on the open disc
and continuous on the closed disc (`TauCeti.diffContOnCl_unitDiscRiemannHilbertSolution`). If
moreover `θ ↦ φ(e^{iθ})` is continuous with summable Fourier coefficients over `ℤ`,
`φ w = -(w ^ k * conj (φ w))` on the unit circle and `c n = 0` for `k < n < 0`, it
satisfies `h w - w ^ k * conj (h w) = φ w` on the unit circle
(`TauCeti.unitDiscRiemannHilbertSolution_sub_zpow_mul_conj`). -/
noncomputable def unitDiscRiemannHilbertSolution (k : ℤ) (φ : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, ((if (n : ℤ) ≤ k then 2⁻¹ else 1) *
    fourierCoeffOn Real.two_pi_pos (fun θ ↦ φ (circleMap 0 1 θ)) n) * z ^ n

variable {k : ℤ} {φ : ℂ → ℂ}

/-- The positivity of the period `2π`, as an instance for the Fourier theory of
`AddCircle (2 * π)`. -/
private theorem fact_two_pi_pos : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

attribute [local instance] fact_two_pi_pos

/-- The points of `toCircle` lie on the unit circle of `ℂ`. -/
private theorem coe_toCircle_mem_sphere (x : AddCircle (2 * π)) :
    (toCircle x : ℂ) ∈ sphere (0 : ℂ) 1 := by
  simp

/-- The boundary condition `φ w = -(w ^ k * conj (φ w))` in terms of Fourier coefficients:
`c n = -conj (c (k - n))`. -/
private theorem fourierCoeffOn_eq_neg_conj
    (hb : ∀ w ∈ sphere (0 : ℂ) 1, φ w = -(w ^ k * conj (φ w))) (n : ℤ) :
    fourierCoeffOn Real.two_pi_pos (fun θ ↦ φ (circleMap 0 1 θ)) n =
      -conj (fourierCoeffOn Real.two_pi_pos (fun θ ↦ φ (circleMap 0 1 θ)) (k - n)) := by
  rw [← fourierCoeff_comp_toCircle, ← fourierCoeff_comp_toCircle, ← fourierCoeff_fourier_mul_conj,
    ← neg_one_mul, ← fourierCoeff.const_mul]
  refine congrArg (fourierCoeff · n) (funext fun x ↦ ?_)
  rw [fourier_apply_eq_coe_toCircle_zpow, neg_one_mul]
  exact hb _ (coe_toCircle_mem_sphere x)

/-! ### Convergence of the solution -/

/-- The coefficients of the explicit solution, extended by zero to negative indices. -/
private noncomputable def solutionCoeff (k : ℤ) (b : ℤ → ℂ) (n : ℤ) : ℂ :=
  if 0 ≤ n then (if n ≤ k then 2⁻¹ else 1) * b n else 0

/-- The coefficients of the explicit solution satisfy `aₙ - conj a_{k-n} = bₙ` when
`bₙ = -conj b_{k-n}` for every `n` and `bₙ = 0` for `k < n < 0`. -/
private theorem solutionCoeff_sub_conj {b : ℤ → ℂ} (hsym : ∀ n, b n = -conj (b (k - n)))
    (hvan : ∀ n, k < n → n < 0 → b n = 0) (n : ℤ) :
    solutionCoeff k b n - conj (solutionCoeff k b (k - n)) = b n := by
  have hs := hsym n
  have hs' := hsym (k - n)
  rw [sub_sub_cancel] at hs'
  unfold solutionCoeff
  split_ifs with h₁ h₂ h₃ h₄ h₃ h₄ h₃ h₄ <;> try omega
  · rw [map_mul, map_inv₀, map_ofNat, hs]
    ring
  · simp
  · simp [hs]
  · simp [hvan n (by omega) (by omega)]

/-- A coefficient of the explicit solution, times a point of the closed disc, is bounded by the
corresponding Fourier coefficient. -/
private theorem norm_coeff_mul_pow_le {b : ℂ} (n : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖((if (n : ℤ) ≤ k then 2⁻¹ else 1) * b) * z ^ n‖ ≤ ‖b‖ := by
  rw [norm_mul, norm_mul, norm_pow]
  have h₁ : ‖(if (n : ℤ) ≤ k then (2⁻¹ : ℂ) else 1)‖ ≤ 1 := by
    split_ifs <;> norm_num
  calc _ ≤ 1 * ‖b‖ * 1 := by gcongr; exact pow_le_one₀ (norm_nonneg _) hz
    _ = ‖b‖ := by ring

/-- **The power series of the explicit solution** converges on the closed unit disc when the
Fourier coefficients `c n` of `θ ↦ φ(e^{iθ})` with `n ≥ 0` are summable. -/
theorem hasSum_unitDiscRiemannHilbertSolution
    (hs : Summable fun n : ℕ ↦ fourierCoeffOn Real.two_pi_pos (fun θ ↦ φ (circleMap 0 1 θ)) n)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    HasSum (fun n : ℕ ↦ ((if (n : ℤ) ≤ k then 2⁻¹ else 1) *
      fourierCoeffOn Real.two_pi_pos (fun θ ↦ φ (circleMap 0 1 θ)) n) * z ^ n)
      (unitDiscRiemannHilbertSolution k φ z) :=
  ((summable_norm_iff.mpr hs).of_norm_bounded fun n ↦ norm_coeff_mul_pow_le n hz).hasSum

/-- **The explicit solution is holomorphic on the disc and continuous up to the boundary**, when
the Fourier coefficients `c n` of `θ ↦ φ(e^{iθ})` with `n ≥ 0` are summable. -/
theorem diffContOnCl_unitDiscRiemannHilbertSolution
    (hs : Summable fun n : ℕ ↦ fourierCoeffOn Real.two_pi_pos (fun θ ↦ φ (circleMap 0 1 θ)) n) :
    DiffContOnCl ℂ (unitDiscRiemannHilbertSolution k φ) (ball 0 1) := by
  have hn := summable_norm_iff.mpr hs
  refine ⟨differentiableOn_tsum_of_summable_norm hn
    (fun n ↦ ((differentiable_const _).mul (differentiable_id.pow n)).differentiableOn)
    isOpen_ball fun n z hz ↦ norm_coeff_mul_pow_le n ?_, ?_⟩
  · simpa using (mem_ball_zero_iff.mp hz).le
  · rw [closure_ball 0 one_ne_zero]
    exact continuousOn_tsum (fun n ↦ (continuous_const.mul (continuous_id.pow n)).continuousOn)
      hn fun n z hz ↦ norm_coeff_mul_pow_le n (mem_closedBall_zero_iff.mp hz)

/-- **The explicit solution solves the Riemann–Hilbert problem.** Let `θ ↦ φ(e^{iθ})` be
continuous with summable Fourier coefficients `c n`, let `φ w = -(w ^ k * conj (φ w))` on the unit
circle, and let `c n = 0` for `k < n < 0`. Then
`h w - w ^ k * conj (h w) = φ w` on the unit circle for `h = unitDiscRiemannHilbertSolution k φ`. -/
theorem unitDiscRiemannHilbertSolution_sub_zpow_mul_conj
    (hφ : Continuous fun θ ↦ φ (circleMap 0 1 θ))
    (hs : Summable fun n : ℤ ↦ fourierCoeffOn Real.two_pi_pos (fun θ ↦ φ (circleMap 0 1 θ)) n)
    (hb : ∀ w ∈ sphere (0 : ℂ) 1, φ w = -(w ^ k * conj (φ w)))
    (hvan : ∀ n : ℤ, k < n → n < 0 →
      fourierCoeffOn Real.two_pi_pos (fun θ ↦ φ (circleMap 0 1 θ)) n = 0)
    {w : ℂ} (hw : w ∈ sphere (0 : ℂ) 1) :
    unitDiscRiemannHilbertSolution k φ w - w ^ k * conj (unitDiscRiemannHilbertSolution k φ w) =
      φ w := by
  set b : ℤ → ℂ := fun n ↦ fourierCoeffOn Real.two_pi_pos (fun θ ↦ φ (circleMap 0 1 θ)) n
  set h := unitDiscRiemannHilbertSolution k φ w
  have hw1 : ‖w‖ = 1 := by simpa using hw
  -- The power series of `h` at `w`, as a sum over `ℤ`.
  have hhw : HasSum (fun n : ℤ ↦ solutionCoeff k b n * w ^ n) h := by
    have hN := hasSum_unitDiscRiemannHilbertSolution (k := k)
      (hs.comp_injective Nat.cast_injective) hw1.le
    refine (Nat.cast_injective.hasSum_iff fun n hn ↦ ?_).mp ?_
    · have : n < 0 := by
        by_contra! h0
        exact hn ⟨n.toNat, Int.toNat_of_nonneg h0⟩
      simp [solutionCoeff, this.not_ge]
    · simpa [Function.comp_def, solutionCoeff] using hN
  -- The power series of `w ^ k * conj (h w)`, reindexed by `n ↦ k - n`.
  have hchw : HasSum (fun n : ℤ ↦ conj (solutionCoeff k b (k - n)) * w ^ n) (w ^ k * conj h) := by
    have := (hasSum_conj'.mpr hhw).mul_left (w ^ k)
    rw [← (Equiv.subLeft k).hasSum_iff] at this
    convert this using 2 with n
    simp only [Function.comp_apply, Equiv.subLeft_apply, map_mul]
    rw [mul_left_comm, zpow_mul_conj_zpow_of_mem_sphere hw, sub_sub_cancel]
  refine (hhw.sub hchw).unique ?_
  convert hasSum_fourierCoeffOn_circleMap_mul_zpow hφ hs hw using 2 with n
  rw [← sub_mul, solutionCoeff_sub_conj (fun n ↦ fourierCoeffOn_eq_neg_conj hb n) hvan]

/-! ### Solvability -/

/-- A function `h` holomorphic on the open unit disc and continuous on the closed disc has
continuous boundary values `x ↦ h (toCircle x)` on `AddCircle (2 * π)`, and so does their product
`x ↦ fourier k x * conj (h (toCircle x))` with a Fourier monomial. -/
private theorem continuous_comp_toCircle_and_fourier_mul_conj {h : ℂ → ℂ}
    (hh : DiffContOnCl ℂ h (ball 0 1)) :
    Continuous (fun x : AddCircle (2 * π) ↦ h (toCircle x)) ∧
      Continuous fun x : AddCircle (2 * π) ↦ fourier k x * conj (h (toCircle x)) := by
  have hc : Continuous fun x : AddCircle (2 * π) ↦ h (toCircle x) := by
    refine hh.continuousOn.comp_continuous (continuous_subtypeVal.comp continuous_toCircle)
      fun x ↦ ?_
    rw [closure_ball 0 one_ne_zero]
    exact sphere_subset_closedBall (coe_toCircle_mem_sphere x)
  exact ⟨hc, (map_continuous (fourier k)).mul (continuous_conj.comp hc)⟩

/-- A continuous function on the circle `AddCircle (2 * π)` is integrable for its Haar measure. -/
private theorem integrable_haarAddCircle_of_continuous {g : AddCircle (2 * π) → ℂ}
    (hg : Continuous g) : Integrable g haarAddCircle :=
  hg.integrable_of_hasCompactSupport (.of_compactSpace _)

/-- **Solvability of the Riemann–Hilbert problem on the disc.** Let `θ ↦ φ(e^{iθ})` be continuous
with summable Fourier coefficients `c n`, and let `φ w = -(w ^ k * conj (φ w))` on the unit
circle. There is a function `h`, holomorphic on the open disc and continuous on the closed disc,
with `h w - w ^ k * conj (h w) = φ w` on the circle exactly when `c n = 0` for `k < n < 0`. These
are `-1 - k` real conditions for `k ≤ -2`, and none for `k ≥ -1`. -/
theorem exists_diffContOnCl_sub_zpow_mul_conj_eq_iff
    (hφ : Continuous fun θ ↦ φ (circleMap 0 1 θ))
    (hs : Summable fun n : ℤ ↦ fourierCoeffOn Real.two_pi_pos (fun θ ↦ φ (circleMap 0 1 θ)) n)
    (hb : ∀ w ∈ sphere (0 : ℂ) 1, φ w = -(w ^ k * conj (φ w))) :
    (∃ h : ℂ → ℂ, DiffContOnCl ℂ h (ball 0 1) ∧
        ∀ w ∈ sphere (0 : ℂ) 1, h w - w ^ k * conj (h w) = φ w) ↔
      ∀ n : ℤ, k < n → n < 0 →
        fourierCoeffOn Real.two_pi_pos (fun θ ↦ φ (circleMap 0 1 θ)) n = 0 := by
  refine ⟨fun ⟨h, hh, hhb⟩ n hkn hn ↦ ?_, fun hvan ↦
    ⟨_, diffContOnCl_unitDiscRiemannHilbertSolution (hs.comp_injective Nat.cast_injective),
      fun w hw ↦ unitDiscRiemannHilbertSolution_sub_zpow_mul_conj hφ hs hb hvan hw⟩⟩
  obtain ⟨hc, hc'⟩ := continuous_comp_toCircle_and_fourier_mul_conj (k := k) hh
  have hφh : (fun x : AddCircle (2 * π) ↦ φ (toCircle x)) =
      fun x ↦ h (toCircle x) - fourier k x * conj (h (toCircle x)) := funext fun x ↦ by
    rw [fourier_apply_eq_coe_toCircle_zpow, hhb _ (coe_toCircle_mem_sphere x)]
  rw [← fourierCoeff_comp_toCircle, hφh, fourierCoeff_sub
    (integrable_haarAddCircle_of_continuous hc) (integrable_haarAddCircle_of_continuous hc'),
    fourierCoeff_fourier_mul_conj, hh.fourierCoeff_comp_toCircle_eq_zero hn,
    hh.fourierCoeff_comp_toCircle_eq_zero (by omega)]
  simp

/-- **The Riemann–Hilbert problem is solvable for `k ≥ -1`.** If `θ ↦ φ(e^{iθ})` is continuous
with summable Fourier coefficients and `φ w = -(w ^ k * conj (φ w))` on the unit circle, there is
`h`, holomorphic on the open disc and continuous on the closed disc, with
`h w - w ^ k * conj (h w) = φ w` on the circle. -/
theorem exists_diffContOnCl_sub_zpow_mul_conj_eq (hk : -1 ≤ k)
    (hφ : Continuous fun θ ↦ φ (circleMap 0 1 θ))
    (hs : Summable fun n : ℤ ↦ fourierCoeffOn Real.two_pi_pos (fun θ ↦ φ (circleMap 0 1 θ)) n)
    (hb : ∀ w ∈ sphere (0 : ℂ) 1, φ w = -(w ^ k * conj (φ w))) :
    ∃ h : ℂ → ℂ, DiffContOnCl ℂ h (ball 0 1) ∧
      ∀ w ∈ sphere (0 : ℂ) 1, h w - w ^ k * conj (h w) = φ w :=
  (exists_diffContOnCl_sub_zpow_mul_conj_eq_iff hφ hs hb).mpr fun n hkn hn ↦ by omega

/-! ### Hölder boundary data -/

/-- The power series of the Hölder solution: on the open disc, the Cauchy integral `G` of `φ`
minus the polynomial `∑_{0 ≤ n ≤ k} (c n / 2) zⁿ` has the coefficients of the explicit solution. -/
private theorem hasSum_sub_sum_range_toNat {c : ℤ → ℂ} {G : ℂ → ℂ} {z : ℂ}
    (hG : HasSum (fun n : ℕ ↦ z ^ n * c n) (G z)) :
    HasSum (fun n : ℕ ↦ z ^ n * ((if (n : ℤ) ≤ k then 2⁻¹ else 1) * c n))
      (G z - ∑ n ∈ Finset.range (k + 1).toNat, 2⁻¹ * c n * z ^ n) := by
  have hp : HasSum (fun n : ℕ ↦ if (n : ℤ) ≤ k then 2⁻¹ * c n * z ^ n else 0)
      (∑ n ∈ Finset.range (k + 1).toNat, 2⁻¹ * c n * z ^ n) := by
    have : HasSum (fun n : ℕ ↦ if (n : ℤ) ≤ k then 2⁻¹ * c n * z ^ n else 0)
        (∑ n ∈ Finset.range (k + 1).toNat, if (n : ℤ) ≤ k then 2⁻¹ * c n * z ^ n else 0) :=
      hasSum_sum_of_ne_finset_zero fun n hn ↦ by
        simp only [Finset.mem_range] at hn
        exact ite_eq_right_iff.2 fun h ↦ absurd h (by omega)
    have hsum : ∑ n ∈ Finset.range (k + 1).toNat,
        (if (n : ℤ) ≤ k then 2⁻¹ * c n * z ^ n else 0) =
          ∑ n ∈ Finset.range (k + 1).toNat, 2⁻¹ * c n * z ^ n :=
      Finset.sum_congr rfl fun n hn ↦ by
        simp only [Finset.mem_range] at hn
        exact ite_eq_left_iff.2 fun h ↦ absurd (by omega) h
    rwa [hsum] at this
  convert hG.sub hp using 2 with n
  split_ifs <;> ring

/-- The boundary identity of the Hölder solution: if `G` is holomorphic on the open disc,
continuous on the closed disc and equal on the open disc to the Cauchy integral of `φ`, then
`h = G - ∑_{0 ≤ n ≤ k} (c n / 2) zⁿ` satisfies `h w - w ^ k * conj (h w) = φ w` on the unit
circle, by comparing Fourier coefficients. -/
private theorem sub_sum_range_toNat_sub_zpow_mul_conj_eq {G : ℂ → ℂ}
    (hφc : ContinuousOn φ (sphere 0 1)) (hb : ∀ w ∈ sphere (0 : ℂ) 1, φ w = -(w ^ k * conj (φ w)))
    (hvan : ∀ n : ℤ, k < n → n < 0 →
      fourierCoeffOn Real.two_pi_pos (fun θ ↦ φ (circleMap 0 1 θ)) n = 0)
    (hGd : DiffContOnCl ℂ G (ball 0 1))
    (hGF : EqOn G (fun z ↦ (2 * π * I)⁻¹ • ∮ w in C(0, 1), (w - z)⁻¹ • φ w) (ball 0 1))
    {w : ℂ} (hw : w ∈ sphere (0 : ℂ) 1) :
    let c : ℤ → ℂ := fun n ↦ fourierCoeffOn Real.two_pi_pos (fun θ ↦ φ (circleMap 0 1 θ)) n
    let h : ℂ → ℂ := fun z ↦ G z - ∑ n ∈ Finset.range (k + 1).toNat, 2⁻¹ * c n * z ^ n
    h w - w ^ k * conj (h w) = φ w := by
  intro c h
  have hp : Differentiable ℂ fun z ↦ ∑ n ∈ Finset.range (k + 1).toNat, 2⁻¹ * c n * z ^ n := by
    fun_prop
  have hhd : DiffContOnCl ℂ h (ball 0 1) := hGd.sub hp.diffContOnCl
  -- On the circle, `h` has the Fourier coefficients of the explicit solution.
  have hcoeff (n : ℤ) :
      fourierCoeffOn Real.two_pi_pos (fun θ ↦ h (circleMap 0 1 θ)) n = solutionCoeff k c n := by
    rcases le_or_gt 0 n with hn | hn
    · lift n to ℕ using hn
      simp only [solutionCoeff, Nat.cast_nonneg, ↓reduceIte]
      refine hhd.fourierCoeffOn_circleMap_eq_of_hasSum
        (a := fun n : ℕ ↦ (if (n : ℤ) ≤ k then 2⁻¹ else 1) * c n) (fun z hz ↦ ?_) n
      simp only [smul_eq_mul]
      refine hasSum_sub_sum_range_toNat ?_
      rw [hGF hz]
      simpa only [smul_eq_mul] using
        hasSum_pow_smul_fourierCoeffOn_two_pi_I_inv_smul_circleIntegral_sub_inv_smul
          (hφc.circleIntegrable zero_le_one) hz
    · simp only [solutionCoeff, not_le.2 hn, ↓reduceIte]
      rw [← fourierCoeff_comp_toCircle]
      exact hhd.fourierCoeff_comp_toCircle_eq_zero hn
  -- The boundary defect is continuous on the circle with vanishing Fourier coefficients.
  obtain ⟨hc, hc'⟩ := continuous_comp_toCircle_and_fourier_mul_conj (k := k) hhd
  have hcφ : Continuous fun x : AddCircle (2 * π) ↦ φ (toCircle x) :=
    hφc.comp_continuous (continuous_subtypeVal.comp continuous_toCircle) coe_toCircle_mem_sphere
  have hD := ContinuousMap.eq_zero_of_forall_fourierCoeff_eq_zero
    ⟨fun x ↦ h (toCircle x) - fourier k x * conj (h (toCircle x)) - φ (toCircle x),
      (hc.sub hc').sub hcφ⟩ fun n ↦ by
    simp only [ContinuousMap.coe_mk]
    rw [fourierCoeff_sub (f := fun x ↦ h (toCircle x) - fourier k x * conj (h (toCircle x)))
      (integrable_haarAddCircle_of_continuous (hc.sub hc'))
      (integrable_haarAddCircle_of_continuous hcφ),
      fourierCoeff_sub (integrable_haarAddCircle_of_continuous hc)
        (integrable_haarAddCircle_of_continuous hc'),
      fourierCoeff_fourier_mul_conj, fourierCoeff_comp_toCircle, fourierCoeff_comp_toCircle,
      fourierCoeff_comp_toCircle, hcoeff, hcoeff,
      solutionCoeff_sub_conj (fun n ↦ fourierCoeffOn_eq_neg_conj hb n) hvan n, sub_self]
  have := congrArg (fun F : C(AddCircle (2 * π), ℂ) ↦ F (arg w : AddCircle (2 * π))) hD
  simp only [ContinuousMap.coe_mk, ContinuousMap.zero_apply, fourier_apply_eq_coe_toCircle_zpow,
    toCircle_arg_of_mem_sphere hw] at this
  exact sub_eq_zero.1 this

/-- **The Riemann–Hilbert problem with Hölder data.** Let `φ` be `α`-Hölder on the unit circle,
for `0 < α < 1`, with `φ w = -(w ^ k * conj (φ w))` there, and let the Fourier coefficients `c n` of
`θ ↦ φ(e^{iθ})` on `[0, 2π]` vanish for `k < n < 0`. Then there is `h`, holomorphic on the open
disc and `α`-Hölder on the closed disc, with `h w - w ^ k * conj (h w) = φ w` on the unit circle.
On the open disc, `h` is the Cauchy integral of `φ` minus the polynomial
`∑_{0 ≤ n ≤ k} (c n / 2) zⁿ`; on the circle its Fourier coefficients are those of the explicit
solution `TauCeti.unitDiscRiemannHilbertSolution`, whose series need not converge for Hölder
data. -/
theorem exists_holderOnWith_closedBall_sub_zpow_mul_conj_eq_of_fourierCoeffOn_eq_zero
    {K α : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1) (hφ : HolderOnWith K α φ (sphere 0 1))
    (hb : ∀ w ∈ sphere (0 : ℂ) 1, φ w = -(w ^ k * conj (φ w)))
    (hvan : ∀ n : ℤ, k < n → n < 0 →
      fourierCoeffOn Real.two_pi_pos (fun θ ↦ φ (circleMap 0 1 θ)) n = 0) :
    ∃ h : ℂ → ℂ, DiffContOnCl ℂ h (ball 0 1) ∧ (∃ C, HolderOnWith C α h (closedBall 0 1)) ∧
      ∀ w ∈ sphere (0 : ℂ) 1, h w - w ^ k * conj (h w) = φ w := by
  set c : ℤ → ℂ := fun n ↦ fourierCoeffOn Real.two_pi_pos (fun θ ↦ φ (circleMap 0 1 θ)) n
  obtain ⟨G, hGF, hG, hGd⟩ :=
    exists_eqOn_two_pi_I_inv_smul_circleIntegral_sub_inv_smul_holderOnWith_closedBall hα0 hα1 hφ
  set p : ℂ → ℂ := fun z ↦ ∑ n ∈ Finset.range (k + 1).toNat, 2⁻¹ * c n * z ^ n
  have hp : ContDiff ℂ 1 p := by fun_prop
  obtain ⟨Cp, hpC⟩ := ContDiffOn.exists_holderOnWith (hp.restrict_scalars ℝ).contDiffOn
    (convex_closedBall 0 1) (isCompact_closedBall 0 1) hα1.le
  exact ⟨fun z ↦ G z - p z, hGd.sub (hp.differentiable one_ne_zero).diffContOnCl,
    ⟨_, hG.sub hpC⟩, fun w hw ↦ sub_sum_range_toNat_sub_zpow_mul_conj_eq (hφ.continuousOn hα0)
      hb hvan hGd hGF hw⟩

/-- **The Riemann–Hilbert problem with `C^{1,α}` data.** Let `φ` have at every point `w` of the
unit circle a derivative `v w` along the rotations, that is of `t ↦ φ (e^{it} w)` at `t = 0`, where
`v` is `α`-Hölder on the circle, for `0 < α < 1`. Let
`φ w = -(w ^ k * conj (φ w))` on the circle, and let the Fourier coefficients `c n` of
`θ ↦ φ(e^{iθ})` on `[0, 2π]` vanish for `k < n < 0`. Then there is `h`, holomorphic on the open
disc and `α`-Hölder on the closed disc, whose derivative extends from the open disc to an
`α`-Hölder function on the closed disc, with `h w - w ^ k * conj (h w) = φ w` on the unit
circle. -/
theorem exists_holderOnWith_closedBall_deriv_sub_zpow_mul_conj_eq_of_fourierCoeffOn_eq_zero
    {L α : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1) {v : ℂ → ℂ}
    (hv : ∀ w ∈ sphere (0 : ℂ) 1, HasDerivAt (fun t : ℝ ↦ φ (exp (I * t) * w)) (v w) 0)
    (hvH : HolderOnWith L α v (sphere 0 1))
    (hb : ∀ w ∈ sphere (0 : ℂ) 1, φ w = -(w ^ k * conj (φ w)))
    (hvan : ∀ n : ℤ, k < n → n < 0 →
      fourierCoeffOn Real.two_pi_pos (fun θ ↦ φ (circleMap 0 1 θ)) n = 0) :
    ∃ h : ℂ → ℂ, DiffContOnCl ℂ h (ball 0 1) ∧ (∃ C, HolderOnWith C α h (closedBall 0 1)) ∧
      (∃ (h' : ℂ → ℂ) (C : ℝ≥0), HolderOnWith C α h' (closedBall 0 1) ∧
        ∀ z ∈ ball (0 : ℂ) 1, h' z = deriv h z) ∧
      ∀ w ∈ sphere (0 : ℂ) 1, h w - w ^ k * conj (h w) = φ w := by
  -- `φ` is Lipschitz, hence `α`-Hölder, on the circle.
  obtain ⟨Mv, hMv⟩ :=
    (isCompact_sphere (0 : ℂ) 1).exists_bound_of_continuousOn (hvH.continuousOn hα0)
  have hlip := lipschitzOnWith_sphere_of_hasDerivAt_exp_mul (M := Mv.toNNReal) hv fun w hw ↦
    (hMv w hw).trans (Real.le_coe_toNNReal Mv)
  obtain ⟨Mφ, hMφ⟩ := (isCompact_sphere (0 : ℂ) 1).exists_bound_of_continuousOn hlip.continuousOn
  have hφ := hlip.holderOnWith_of_norm_le (M := Mφ.toNNReal)
    (fun w hw ↦ (hMφ w hw).trans (Real.le_coe_toNNReal Mφ)) hα1.le
  set c : ℤ → ℂ := fun n ↦ fourierCoeffOn Real.two_pi_pos (fun θ ↦ φ (circleMap 0 1 θ)) n
  obtain ⟨G, hGF, hG, hGd⟩ :=
    exists_eqOn_two_pi_I_inv_smul_circleIntegral_sub_inv_smul_holderOnWith_closedBall hα0 hα1 hφ
  obtain ⟨G', hG'F, hG', -⟩ :=
    exists_eqOn_two_pi_I_inv_smul_circleIntegral_sub_inv_smul_holderOnWith_closedBall hα0 hα1 hvH
  set p : ℂ → ℂ := fun z ↦ ∑ n ∈ Finset.range (k + 1).toNat, 2⁻¹ * c n * z ^ n
  have hp : ContDiff ℂ 2 p := by fun_prop
  have hp' : ContDiff ℂ 1 fun z ↦ I * z * deriv p z :=
    contDiff_const.mul contDiff_id |>.mul (contDiff_succ_iff_deriv.1 hp).2.2
  obtain ⟨Cp, hpC⟩ := ContDiffOn.exists_holderOnWith
    ((hp.of_le one_le_two).restrict_scalars ℝ).contDiffOn (convex_closedBall 0 1)
    (isCompact_closedBall 0 1) hα1.le
  obtain ⟨Cp', hpC'⟩ := ContDiffOn.exists_holderOnWith (hp'.restrict_scalars ℝ).contDiffOn
    (convex_closedBall 0 1) (isCompact_closedBall 0 1) hα1.le
  set h : ℂ → ℂ := fun z ↦ G z - p z
  have hhd : DiffContOnCl ℂ h (ball 0 1) := hGd.sub (hp.differentiable two_ne_zero).diffContOnCl
  -- The boundary values of `h` have the Hölder derivative `G' w - i w p'(w)` along the rotations.
  have hV (w : ℂ) (hw : w ∈ sphere (0 : ℂ) 1) :
      HasDerivAt (fun t : ℝ ↦ h (exp (I * t) * w)) (G' w - I * w * deriv p w) 0 := by
    have hpath : HasDerivAt (fun t : ℝ ↦ exp (I * t) * w) (I * w) 0 := by
      simpa using hasDerivAt_exp_I_mul_mul w 0
    have hpd : HasDerivAt p (deriv p w) (exp (I * ((0 : ℝ) : ℂ)) * w) := by
      rw [ofReal_zero, mul_zero, exp_zero, one_mul]
      exact ((hp.differentiable two_ne_zero).differentiableAt (x := w)).hasDerivAt
    have hpw : HasDerivAt (fun t : ℝ ↦ p (exp (I * t) * w)) ((I * w) • deriv p w) 0 := by
      convert hpd.scomp 0 hpath using 2
      simp
    exact (hasDerivAt_comp_exp_mul_of_eqOn_two_pi_I_inv_smul_circleIntegral_sub_inv_smul hv
      (hvH.continuousOn hα0) (hG.continuousOn hα0) hGF (hG'.continuousOn hα0) hG'F hw).sub
      (by simpa only [smul_eq_mul] using hpw)
  obtain ⟨h', K', hh', hh'd, -⟩ := hhd.exists_holderOnWith_closedBall_deriv hV hα0 hα1
    ((hG'.mono sphere_subset_closedBall).sub (hpC'.mono sphere_subset_closedBall))
  exact ⟨h, hhd, ⟨_, hG.sub hpC⟩, ⟨h', K', hh', hh'd⟩, fun w hw ↦
    sub_sum_range_toNat_sub_zpow_mul_conj_eq (hφ.continuousOn hα0) hb hvan hGd hGF hw⟩

/-- **The Riemann–Hilbert problem with Hölder data is solvable for `k ≥ -1`.** If `φ` is
`α`-Hölder on the unit circle, for `0 < α < 1`, and `φ w = -(w ^ k * conj (φ w))` there, then
there is `h`, holomorphic on the open disc and `α`-Hölder on the closed disc, with
`h w - w ^ k * conj (h w) = φ w` on the unit circle. -/
theorem exists_holderOnWith_closedBall_sub_zpow_mul_conj_eq (hk : -1 ≤ k) {K α : ℝ≥0}
    (hα0 : 0 < α) (hα1 : α < 1) (hφ : HolderOnWith K α φ (sphere 0 1))
    (hb : ∀ w ∈ sphere (0 : ℂ) 1, φ w = -(w ^ k * conj (φ w))) :
    ∃ h : ℂ → ℂ, DiffContOnCl ℂ h (ball 0 1) ∧ (∃ C, HolderOnWith C α h (closedBall 0 1)) ∧
      ∀ w ∈ sphere (0 : ℂ) 1, h w - w ^ k * conj (h w) = φ w :=
  exists_holderOnWith_closedBall_sub_zpow_mul_conj_eq_of_fourierCoeffOn_eq_zero hα0 hα1 hφ hb
    fun _ _ _ ↦ by omega

/-! ### Solving `∂u/∂(conj z) = f` with boundary values on a rotating line -/

/-- **Correcting boundary values.** For a `C²` function `v` whose boundary defect
`θ ↦ e^{ikθ} conj (v(e^{iθ})) - v(e^{iθ})` has vanishing Fourier coefficients in the range
`k < n < 0`, there is `h`, holomorphic on the open disc and continuous on the closed disc, such
that `v + h` satisfies the boundary condition `(v + h) w = w ^ k * conj ((v + h) w)` on the unit
circle. -/
private theorem exists_diffContOnCl_add_eq_zpow_mul_conj {v : ℂ → ℂ} (hv : ContDiff ℝ 2 v)
    (hvan : ∀ n : ℤ, k < n → n < 0 → fourierCoeffOn Real.two_pi_pos
      (fun θ ↦ circleMap 0 1 θ ^ k * conj (v (circleMap 0 1 θ)) - v (circleMap 0 1 θ)) n = 0) :
    ∃ h : ℂ → ℂ, DiffContOnCl ℂ h (ball 0 1) ∧
      ∀ w ∈ sphere (0 : ℂ) 1, v w + h w = w ^ k * conj (v w + h w) := by
  have hvc : ContDiff ℝ 2 fun θ ↦ v (circleMap 0 1 θ) := hv.comp (contDiff_circleMap 0 1)
  have hφ : ContDiff ℝ 2 fun θ ↦ circleMap 0 1 θ ^ k * conj (v (circleMap 0 1 θ)) -
      v (circleMap 0 1 θ) :=
    ((contDiff_circleMap_zpow 1 k).mul (conjCLE.contDiff.comp hvc)).sub hvc
  set φ : ℂ → ℂ := fun w ↦ w ^ k * conj (v w) - v w
  replace hφ : ContDiff ℝ 2 fun θ ↦ φ (circleMap 0 1 θ) := hφ
  obtain ⟨h, hh, hhb⟩ := (exists_diffContOnCl_sub_zpow_mul_conj_eq_iff hφ.continuous
    (summable_fourierCoeffOn_circleMap_of_contDiff hφ)
    fun w hw ↦ zpow_mul_conj_sub_eq_neg_of_mem_sphere hw k (v w)).mpr hvan
  refine ⟨h, hh, fun w hw ↦ ?_⟩
  have := hhb w hw
  rw [map_add, mul_add]
  linear_combination this

/-- **Solving the boundary problem from the Fourier conditions.** Let `f` be compactly supported
`C²` with Cauchy transform `T f`, and let the boundary defect
`θ ↦ e^{ikθ} conj (T f (e^{iθ})) - T f (e^{iθ})` have vanishing Fourier coefficients in the range
`k < n < 0`. Then there is `u`, continuous on the closed unit disc and real differentiable on the
open disc, with `∂u/∂(conj z) = f` on the open disc and `u w = w ^ k * conj (u w)` on the unit
circle: `u = T f + h`, where `h` solves the Riemann–Hilbert problem correcting the boundary values
of `T f`. For `k ≥ -1` the range `k < n < 0` is empty
(`TauCeti.exists_conjWirtingerDeriv_eq_and_eq_zpow_mul_conj`). -/
theorem exists_conjWirtingerDeriv_eq_and_eq_zpow_mul_conj_of_fourierCoeffOn_eq_zero {f : ℂ → ℂ}
    (hc : HasCompactSupport f) (hf : ContDiff ℝ 2 f)
    (hvan : ∀ n : ℤ, k < n → n < 0 → fourierCoeffOn Real.two_pi_pos
      (fun θ ↦ circleMap 0 1 θ ^ k * conj (cauchyTransform f (circleMap 0 1 θ)) -
        cauchyTransform f (circleMap 0 1 θ)) n = 0) :
    ∃ u : ℂ → ℂ, ContinuousOn u (closedBall 0 1) ∧ DifferentiableOn ℝ u (ball 0 1) ∧
      (∀ z ∈ ball (0 : ℂ) 1, conjWirtingerDeriv u z 1 = f z) ∧
      ∀ w ∈ sphere (0 : ℂ) 1, u w = w ^ k * conj (u w) := by
  have hv : ContDiff ℝ 2 (cauchyTransform f) := hc.contDiff_cauchyTransform hf
  obtain ⟨h, hh, hhb⟩ := exists_diffContOnCl_add_eq_zpow_mul_conj hv hvan
  have hhd (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : DifferentiableAt ℂ h z :=
    hh.differentiableAt isOpen_ball hz
  have hvd (z : ℂ) : DifferentiableAt ℝ (cauchyTransform f) z := hv.differentiable (by simp) z
  refine ⟨cauchyTransform f + h, hv.continuous.continuousOn.add hh.continuousOn_ball,
    fun z hz ↦ ((hvd z).add ((hhd z hz).restrictScalars ℝ)).differentiableWithinAt,
    fun z hz ↦ ?_, hhb⟩
  rw [conjWirtingerDeriv_add (hvd z) ((hhd z hz).restrictScalars ℝ), add_apply,
    (hhd z hz).conjWirtingerDeriv_eq_zero,
    hc.conjWirtingerDeriv_cauchyTransform (hf.of_le (by simp))]
  simp

/-- **The Cauchy–Riemann operator on the disc with boundary values on a rotating line is onto for
`k ≥ -1`.** For a compactly supported `C²` function `f` there is `u`, continuous on the closed
unit disc and real differentiable on the open disc, with `∂u/∂(conj z) = f` on the open disc and
`u w = w ^ k * conj (u w)` on the unit circle. The solution is `u = T f + h`, where `T f` is the
Cauchy transform of `f` and `h` solves the Riemann–Hilbert problem correcting the boundary values
of `T f`. It is unique up to the kernel `TauCeti.unitDiscCauchyRiemannKernel k`
(`TauCeti.domRestrict_sub_mem_unitDiscCauchyRiemannKernel`). -/
theorem exists_conjWirtingerDeriv_eq_and_eq_zpow_mul_conj (hk : -1 ≤ k) {f : ℂ → ℂ}
    (hc : HasCompactSupport f) (hf : ContDiff ℝ 2 f) :
    ∃ u : ℂ → ℂ, ContinuousOn u (closedBall 0 1) ∧ DifferentiableOn ℝ u (ball 0 1) ∧
      (∀ z ∈ ball (0 : ℂ) 1, conjWirtingerDeriv u z 1 = f z) ∧
      ∀ w ∈ sphere (0 : ℂ) 1, u w = w ^ k * conj (u w) :=
  exists_conjWirtingerDeriv_eq_and_eq_zpow_mul_conj_of_fourierCoeffOn_eq_zero hc hf
    fun _ _ _ ↦ by omega

/-- **Uniqueness modulo the kernel.** Two functions, continuous on the closed unit disc and real
differentiable on the open disc, with the same `∂/∂(conj z)` on the open disc and boundary values
at `w = e^{iθ}` on the line `e^{ikθ/2} ℝ`, differ on the closed disc by an element of the kernel
`TauCeti.unitDiscCauchyRiemannKernel k`. -/
theorem domRestrict_sub_mem_unitDiscCauchyRiemannKernel {u₁ u₂ : ℂ → ℂ}
    (hc₁ : ContinuousOn u₁ (closedBall 0 1)) (hc₂ : ContinuousOn u₂ (closedBall 0 1))
    (hd₁ : DifferentiableOn ℝ u₁ (ball 0 1)) (hd₂ : DifferentiableOn ℝ u₂ (ball 0 1))
    (heq : ∀ z ∈ ball (0 : ℂ) 1, conjWirtingerDeriv u₁ z 1 = conjWirtingerDeriv u₂ z 1)
    (hb₁ : ∀ w ∈ sphere (0 : ℂ) 1, u₁ w = w ^ k * conj (u₁ w))
    (hb₂ : ∀ w ∈ sphere (0 : ℂ) 1, u₂ w = w ^ k * conj (u₂ w)) :
    (closedBall 0 1).domRestrict (u₁ - u₂) ∈ unitDiscCauchyRiemannKernel k :=
  mem_unitDiscCauchyRiemannKernel_iff.mpr
    ⟨u₁ - u₂, diffContOnCl_sub_of_conjWirtingerDeriv_eq isOpen_ball
      (by rwa [closure_ball 0 one_ne_zero]) (by rwa [closure_ball 0 one_ne_zero]) hd₁ hd₂ heq,
      fun w hw ↦ by simp only [Pi.sub_apply, map_sub, mul_sub, ← hb₁ w hw, ← hb₂ w hw], rfl⟩

end TauCeti
