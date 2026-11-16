/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# The conjugate Wirtinger derivative of a finite product

For real-differentiable functions `f i : V → ℂ` on a complex normed space, the Leibniz rule gives

`\bar∂ (∏_{i ∈ s} f i) = ∑_{i ∈ s} (∏_{j ∈ s ∖ i} f j) \bar∂ (f i)`

(`TauCeti.conjWirtingerDeriv_finsetProd`). Consequently a bound on the logarithmic derivatives
of the factors bounds that of the product: if `‖\bar∂ (f i)(x)‖ ≤ K |f i (x)|` for every `i ∈ s`,
then `‖\bar∂ (∏ f i)(x)‖ ≤ #s K |∏ f i (x)|` (`TauCeti.norm_conjWirtingerDeriv_finsetProd_le`).
For solutions of a real Cauchy–Riemann equation `\bar∂ f + f ν + \bar f μ = 0` the factors satisfy
such a bound with `K = ‖ν‖ + ‖μ‖`, so products of solutions satisfy the differential inequality
`|\bar∂ F| ≤ C |F|` through which the similarity principle controls their zeros.
-/

public section

open Finset

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {ι : Type*} {s : Finset ι}
  {f : ι → V → ℂ} {x : V}

/-- **The Leibniz rule for a finite product**:
`\bar∂ (∏_{i ∈ s} f i) = ∑_{i ∈ s} (∏_{j ∈ s ∖ i} f j) \bar∂ (f i)`. -/
theorem conjWirtingerDeriv_finsetProd [DecidableEq ι]
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) :
    conjWirtingerDeriv (fun y ↦ ∏ i ∈ s, f i y) x =
      ∑ i ∈ s, (∏ j ∈ s.erase i, f j x) • conjWirtingerDeriv (f i) x :=
  conjWirtingerDeriv_eq_sum_smul (fderiv_finsetProd hf)

/-- **Logarithmic derivative bound for a finite product.** If every factor satisfies
`‖\bar∂ (f i)(x)‖ ≤ K |f i (x)|`, then the product satisfies
`‖\bar∂ (∏ f i)(x)‖ ≤ #s K |∏ f i (x)|`. -/
theorem norm_conjWirtingerDeriv_finsetProd_le (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) x)
    {K : ℝ} (hK : ∀ i ∈ s, ‖conjWirtingerDeriv (f i) x‖ ≤ K * ‖f i x‖) :
    ‖conjWirtingerDeriv (fun y ↦ ∏ i ∈ s, f i y) x‖ ≤ (#s * K) * ‖∏ i ∈ s, f i x‖ := by
  classical
  rw [conjWirtingerDeriv_finsetProd hf]
  calc ‖∑ i ∈ s, (∏ j ∈ s.erase i, f j x) • conjWirtingerDeriv (f i) x‖
      ≤ ∑ i ∈ s, ‖(∏ j ∈ s.erase i, f j x) • conjWirtingerDeriv (f i) x‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ s, K * ‖∏ i ∈ s, f i x‖ := by
      refine sum_le_sum fun i hi ↦ ?_
      rw [norm_smul, ← prod_erase_mul s (fun j ↦ f j x) hi, norm_mul]
      calc ‖∏ j ∈ s.erase i, f j x‖ * ‖conjWirtingerDeriv (f i) x‖
          ≤ ‖∏ j ∈ s.erase i, f j x‖ * (K * ‖f i x‖) := by gcongr; exact hK i hi
        _ = K * (‖∏ j ∈ s.erase i, f j x‖ * ‖f i x‖) := by ring
    _ = (#s * K) * ‖∏ i ∈ s, f i x‖ := by rw [sum_const, nsmul_eq_mul, mul_assoc]

end TauCeti
