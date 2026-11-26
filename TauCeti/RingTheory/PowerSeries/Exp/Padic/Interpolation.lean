/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Exp.Padic.Eval
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Schwarz
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Algebra.CharP.Algebra

/-!
# Interpolation of p-adic exponential polynomials on closed discs

An exponential polynomial `Φ(z) = ∑ᵢ aᵢ exp(z xᵢ)` over a complete normed field `K ⊇ ℚ_p`, on a
closed disc of radius `c` strictly inside the exponential discs of its frequencies, is the value
of a restricted series with Gauss norm at most `max ‖aᵢ‖`. The Schwarz lemma for Hasse derivatives
then bounds its divided derivatives `Φ⁽ᵏ⁾(z) / k!` on the disc by its vanishing at finitely many
points of the disc, with arbitrary multiplicities.

The grids of the p-adic method of linear forms in logarithms consist of `p`-adic integers; the
explicit forms of the bound on them are in `TauCeti.NumberTheory.Padics.Exp.Polynomial`.
-/

public section

open PowerSeries Finset
open scoped Nat

namespace TauCeti

variable {p : ℕ} [Fact p.Prime] {K : Type*} [NormedField K]
  [NormedAlgebra ℚ_[p] K] [CompleteSpace K] {ι : Type*} {s : Finset ι} {a x : ι → K} {c : ℝ}

/-- **Interpolation on a closed disc with pointwise multiplicities.** If the ordinary
exponential derivative sums vanish to order `T b` at every grid point `b`, the divided
derivative at any point of the disc satisfies the Schwarz product bound. Each exponent
`T b - k` uses natural-number subtraction, truncated at zero. -/
theorem norm_sum_mul_exp_le_mul_prod_pow (hc : 0 < c)
    (hxc : ∀ i ∈ s, ‖x i‖ * c < (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) {A : ℝ} (hA : 0 ≤ A)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ A) {g : Finset K} {T : K → ℕ}
    (hg : ∀ b ∈ g, ‖b‖ ≤ c)
    (hzero : ∀ b ∈ g, ∀ t < T b, ∑ i ∈ s, a i * x i ^ t * NormedSpace.exp (b * x i) = 0)
    (k : ℕ) {z : K} (hz : ‖z‖ ≤ c) :
    ‖∑ i ∈ s, a i * (x i ^ k / k !) * NormedSpace.exp (z * x i)‖ ≤
      c⁻¹ ^ k * A * ∏ b ∈ g, (‖z - b‖ / c) ^ (T b - k) := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  have : IsUltrametricDist K := .of_normedAlgebra ℚ_[p]
  have hF := isRestricted_sum_smul_rescale_exp s a x hc.le hxc
  have h := hF.norm_evalAt_hasseDeriv_le_gaussNorm_mul_prod_pow (L := K) hc hg
    (fun b hb t ht ↦ (evalAt_hasseDeriv_sum_smul_rescale_exp_eq_zero_iff hxc t (hg b hb)).mpr
      (hzero b hb t ht)) k hz
  rw [evalAt_hasseDeriv_sum_smul_rescale_exp hxc k hz] at h
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (gaussNorm_sum_smul_rescale_exp_le s a x hc.le (fun i hi ↦ (hxc i hi).le) hA ha)
      (by positivity)) (prod_nonneg fun _ _ ↦ by positivity))

end TauCeti
