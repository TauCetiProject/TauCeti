/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import TauCeti.Analysis.Complex.Pompeiu.Basic
public import TauCeti.Analysis.Complex.UnitDisc.RotatingLineBoundary
import Mathlib.Analysis.Complex.LocallyUniformLimit
import TauCeti.Analysis.Complex.Circle
import TauCeti.Analysis.Complex.PowerSeries.FourierCoeff
import TauCeti.Analysis.Complex.Wirtinger.Holomorphic
import TauCeti.Analysis.Fourier.AddCircle
import TauCeti.Analysis.Fourier.Decay
import TauCeti.Analysis.Fourier.FourierCoeffOn
import TauCeti.Analysis.SpecialFunctions.Complex.CircleMap

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
open scoped ComplexConjugate Real

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
  have hc : Continuous fun x : AddCircle (2 * π) ↦ h (toCircle x) := by
    refine hh.continuousOn.comp_continuous (continuous_subtype_val.comp continuous_toCircle)
      fun x ↦ ?_
    rw [closure_ball 0 one_ne_zero]
    exact sphere_subset_closedBall (coe_toCircle_mem_sphere x)
  have hc' : Continuous fun x : AddCircle (2 * π) ↦ fourier k x * conj (h (toCircle x)) :=
    (map_continuous (fourier k)).mul (continuous_conj.comp hc)
  have hi {g : AddCircle (2 * π) → ℂ} (hg : Continuous g) : Integrable g haarAddCircle :=
    hg.integrable_of_hasCompactSupport (.of_compactSpace _)
  have hφh : (fun x : AddCircle (2 * π) ↦ φ (toCircle x)) =
      fun x ↦ h (toCircle x) - fourier k x * conj (h (toCircle x)) := funext fun x ↦ by
    rw [fourier_apply_eq_coe_toCircle_zpow, hhb _ (coe_toCircle_mem_sphere x)]
  rw [← fourierCoeff_comp_toCircle, hφh, fourierCoeff_sub (hi hc) (hi hc'),
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
