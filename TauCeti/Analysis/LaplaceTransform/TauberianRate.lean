/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.LaplaceTransform.Basic
public import Mathlib.Analysis.Calculus.DSlope
import TauCeti.Analysis.Complex.Taylor.RapidDecay
import TauCeti.Analysis.LaplaceTransform.PostWidder

/-!
# A quantitative Laplace Tauberian theorem

A Lipschitz function on the positive half-line decays faster than every inverse power if
its Laplace transform is a holomorphic divided difference with polynomial bounds on
regions extending to the left of the convergence line by an inverse logarithmic power.
The proof uses the Post–Widder Gamma approximation and the rapid decay of the same
normalized Taylor coefficient of the divided difference, obtained from Cauchy's estimate.

The quantitative Taylor-coefficient method follows `New.eventually_abs_le_inv_pow_of_transform`
in `Lib/Analytic/PrimeNumberTheorem/Tauberian.lean` of lsernau/grh-lean (commit `72fead1`).
-/

public section

open Filter Set
open scoped Nat NNReal Topology

namespace TauCeti

/-- A quantitative Tauberian criterion for a real input with Laplace transform
`(F(s) - F(1)) / (s - 1)` at `s - 1`. Polynomial growth of `F` on the expanding regions
`Re s ≥ 1 - l⁻ᴬ`, `‖s‖ ≤ exp l`, with `F` holomorphic there, forces the input to decay
faster than every inverse power. Only the positive half-line of the input is used. -/
theorem eventually_abs_le_inv_pow_of_laplace_transform {R : ℝ → ℝ} {F : ℂ → ℂ}
    {L : ℝ≥0} (hR : LipschitzOnWith L R (Ioi 0))
    (hLap : ∀ s : ℂ, 2 < s.re → HasLaplace (fun u ↦ (R u : ℂ)) (s - 1) (dslope F 1 s))
    {A : ℕ} (hF : ∀ᶠ l : ℝ in atTop, ∀ s : ℂ, 1 - 1 / l ^ A ≤ s.re → ‖s‖ ≤ Real.exp l →
      DifferentiableAt ℂ F s ∧ ‖F s‖ ≤ l ^ A) (B : ℕ) :
    ∀ᶠ u : ℝ in atTop, |R u| ≤ (u ^ B)⁻¹ := by
  have hRℂ : LipschitzOnWith L (fun u ↦ (R u : ℂ)) (Ioi 0) :=
    lipschitzOnWith_iff_dist_le_mul.2 fun x hx y hy ↦
      (Complex.isometry_ofReal.dist_eq (R x) (R y)).trans_le (hR.dist_le_mul x hx y hy)
  -- A Gamma shape of order `u^(2(B+2))` gives a width of order `u^(-B-1)`.
  let P := 2 * B + 3
  filter_upwards [eventually_norm_normalized_iteratedDeriv_dslope_le_inv_pow hF P (B + 1),
    eventually_gt_atTop (1 : ℝ), eventually_ge_atTop ((L : ℝ) + 1)] with u hcoeff hu hL
  let k := ⌊u ^ (P + 1)⌋₊
  let H : ℝ := ((k + 1 : ℕ) : ℝ) / u
  have hu₀ : 0 < u := zero_lt_one.trans hu
  have hP : P + 1 = 2 * (B + 2) := by dsimp [P]; omega
  have hk : u ^ (P + 1) < ((k + 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_succ] using Nat.lt_floor_add_one (u ^ (P + 1))
  have hH : 1 < H := (lt_div_iff₀ hu₀).2
    (by simpa only [one_mul] using (le_self_pow₀ hu.le (Nat.succ_ne_zero P)).trans_lt hk)
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : (H : ℂ) ∈ {z : ℂ | 1 < z.re} := by
    simpa only [mem_ofPred_eq, Complex.ofReal_re] using hH
  have hnear : ∀ᶠ z in 𝓝 (H : ℂ), HasLaplace (fun v ↦ (R v : ℂ)) z (dslope F 1 (1 + z)) := by
    filter_upwards [hopen.mem_nhds hmem] with z hz
    have hz' : 2 < 1 + z.re := by linarith only [hz]
    simpa only [add_sub_cancel_left] using
      hLap (1 + z) (by simpa only [Complex.add_re, Complex.one_re] using hz')
  have hcenter : ((k + 1 : ℕ) : ℝ) / H = u := div_div_cancel₀ (by positivity)
  have hscalar : (H : ℂ) ^ (k + 1) * (-1) ^ k = (-(H : ℂ)) ^ k * H := by
    rw [← neg_one_mul (H : ℂ), mul_pow, pow_succ (H : ℂ) k]
    ring
  have happrox := norm_smul_iteratedDeriv_sub_le_of_hasLaplace (zero_lt_one.trans hH) hnear hRℂ k
  simp only [iteratedDeriv_comp_const_add, hcenter, hscalar, mul_div_assoc (L : ℝ)] at happrox
  have hwidth : Real.sqrt (k + 1 : ℕ) / H ≤ (u ^ (B + 1))⁻¹ := calc
    _ = u / Real.sqrt (k + 1 : ℕ) := by
      dsimp only [H]
      field_simp
      exact Real.sq_sqrt (by positivity)
    _ ≤ u / u ^ (B + 2) := by
      apply div_le_div_of_nonneg_left hu₀.le (by positivity) (Real.le_sqrt_of_sq_le ?_)
      rw [← pow_mul, mul_comm (B + 2), ← hP]
      exact hk.le
    _ = _ := by rw [pow_succ u (B + 1)]; field_simp
  let c := ((-(H : ℂ)) ^ k * H / k !) • iteratedDeriv k (dslope F 1) (1 + (H : ℂ))
  calc
    |R u| = ‖(R u : ℂ)‖ := (Complex.norm_real _).symm
    _ ≤ ‖c‖ + ‖c - (R u : ℂ)‖ := norm_le_norm_add_norm_sub ..
    _ ≤ (u ^ (B + 1))⁻¹ + (L : ℝ) * (u ^ (B + 1))⁻¹ :=
      add_le_add (by simpa only [c, H, k, Nat.cast_succ] using hcoeff)
        (happrox.trans (mul_le_mul_of_nonneg_left hwidth L.coe_nonneg))
    _ = ((L : ℝ) + 1) / u ^ (B + 1) := by ring
    _ ≤ (u ^ B)⁻¹ := by
      rw [pow_succ, ← div_div, ← one_div, div_right_comm]
      exact div_le_div_of_nonneg_right ((div_le_one hu₀).2 hL) (by positivity)

end TauCeti
