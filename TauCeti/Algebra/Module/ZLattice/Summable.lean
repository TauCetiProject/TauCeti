/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-!
# Gaussian and power sums over lattices converge

Let `E` be a finite-dimensional real normed space and `L` a discrete `ℤ`-submodule of `E`. For
`0 < c` and any `x : E`, the Gaussian `v ↦ exp (-c ‖x + v‖²)` is summable over `L`
(`ZLattice.summable_exp_neg_mul_norm_add_sq`).

The proof compares the Gaussian with the power `‖x + v‖ ^ r` for `r < -rank L`, whose sum over `L`
converges by Mathlib's `ZLattice.summable_norm_sub_rpow`: the Gaussian decays faster than every
power, and `‖x + v‖ → ∞` along the cofinite filter of `L` because `L` is discrete and closed.

This is the majorant behind the convergence of the theta series of a lattice, a sum of
`exp (π i ‖x + v‖² τ)` over `L` whose terms have norm `exp (-π ‖x + v‖² im τ)`.

For the standard lattice `ℤ^d`, read with the sup norm on `d → ℤ`, the power sum
`∑ n, ‖n‖ ^ r` converges for `r < -card d` (`TauCeti.summable_pi_int_norm_rpow`). This is the
majorant used to sum Fourier coefficients on the torus `(ℝ / ℤ)^d`.

## Main statements

* `ZLattice.summable_exp_neg_mul_norm_add_sq`: `∑ v ∈ L, exp (-c ‖x + v‖²)` converges for
  `0 < c`.
* `ZLattice.summable_one_add_norm_pow_inv`: `∑ ℓ ∈ L, (1 + ‖ℓ‖) ^ (-r)` converges once the
  natural number `r` exceeds the rank of `L`.
* `TauCeti.summable_pi_int_norm_rpow`: `∑ n : d → ℤ, ‖n‖ ^ r` converges for `r < -card d`.
* `TauCeti.summable_pi_int_inv_one_add_norm_pow`: `∑ n : d → ℤ, (1 + ‖n‖) ^ (-(card d + 1))`
  converges.
-/

public section

open Filter Asymptotics Topology

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (L : Submodule ℤ E) [DiscreteTopology L]

/-- For `0 < c`, the Gaussian `v ↦ exp (-c ‖x + v‖²)` is summable over a discrete subgroup `L` of
a finite-dimensional real normed space, for every centre `-x`. -/
theorem summable_exp_neg_mul_norm_add_sq {c : ℝ} (hc : 0 < c) (x : E) :
    Summable fun v : L => Real.exp (-c * ‖x + (v : E)‖ ^ 2) := by
  -- Compare with `‖v - (-x)‖ ^ r` for an exponent `r` below `-rank L`.
  set r : ℝ := -(Module.finrank ℤ L + 1 : ℝ)
  have hr : r < -(Module.finrank ℤ L : ℝ) := by simp [r]
  have hemb : IsClosedEmbedding fun v : L => x + (v : E) :=
    (Homeomorph.addLeft x).isClosedEmbedding.comp
      (L.toAddSubgroup.isClosed_of_discreteTopology.isClosedEmbedding_subtypeVal)
  have htend : Tendsto (fun v : L => ‖x + (v : E)‖) cofinite atTop :=
    tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding hemb
  refine summable_of_isBigO (summable_norm_sub_rpow L r hr (-x)) ?_
  have key := ((rexp_neg_quadratic_isLittleO_rpow_atTop (neg_lt_zero.mpr hc) 0 r).isBigO
    |>.comp_tendsto htend)
  simpa [Function.comp_def, sub_neg_eq_add, add_comm] using key

/-- On a discrete subgroup `L` of a finite-dimensional real normed space, `(1 + ‖ℓ‖) ^ (-r)` is
summable as soon as `r` exceeds the rank of `L`. -/
theorem summable_one_add_norm_pow_inv {r : ℕ} (hr : Module.finrank ℤ L < r) :
    Summable fun ℓ : L ↦ ((1 + ‖(ℓ : E)‖) ^ r)⁻¹ := by
  refine Summable.of_norm_bounded_eventually (summable_norm_pow_inv L r hr) ?_
  -- Away from `0`, `(1 + ‖ℓ‖) ^ (-r) ≤ ‖ℓ‖ ^ (-r)`.
  filter_upwards [Set.Finite.compl_mem_cofinite (Set.finite_singleton (0 : L))] with ℓ hℓ
  have hℓ : 0 < ‖(ℓ : E)‖ := by simpa using hℓ
  rw [norm_inv, norm_pow, Real.norm_of_nonneg (by positivity), ← inv_pow]
  gcongr
  simp

end ZLattice

namespace TauCeti

/-- The sup norms of the integer vectors `n : d → ℤ` satisfy `∑ n, ‖n‖ ^ r < ∞` when
`r < -card d`. Here `‖0‖ ^ r = 0`. -/
theorem summable_pi_int_norm_rpow {d : Type*} [Fintype d] (r : ℝ) (hr : r < -Fintype.card d) :
    Summable fun n : d → ℤ ↦ ‖n‖ ^ r := by
  classical
  set L := Submodule.span ℤ (Set.range (Pi.basisFun ℝ d))
  have hrank : Module.finrank ℤ L = Fintype.card d := by
    rw [ZLattice.rank ℝ L, Module.finrank_fintype_fun_eq_card]
  have hmem (n : d → ℤ) : (fun i ↦ (n i : ℝ)) ∈ L :=
    (Submodule.mem_span_range_iff_exists_fun ℤ).2 ⟨n, by ext i; simp [Pi.single_apply]⟩
  have hinj : Function.Injective fun n : d → ℤ ↦ (⟨_, hmem n⟩ : L) := fun m n h ↦ by
    ext i
    simpa using congr_fun (congrArg Subtype.val h) i
  refine ((ZLattice.summable_norm_rpow L r (hrank ▸ hr)).comp_injective hinj).congr fun n ↦ ?_
  have hn (i : d) : ‖(n i : ℝ)‖₊ = ‖n i‖₊ := NNReal.eq (Int.norm_cast_real _)
  simp [Pi.norm_def, hn]

/-- The series `∑ n, (1 + ‖n‖) ^ (-(card d + 1))` over the integer vectors `n : d → ℤ`, with the
sup norm, converges. -/
theorem summable_pi_int_inv_one_add_norm_pow {d : Type*} [Fintype d] :
    Summable fun n : d → ℤ ↦ ((1 + ‖n‖) ^ (Fintype.card d + 1))⁻¹ := by
  refine Summable.of_norm_bounded_eventually
    (summable_pi_int_norm_rpow (-((Fintype.card d + 1 : ℕ) : ℝ)) (by push_cast; linarith)) ?_
  filter_upwards [(Set.finite_singleton (0 : d → ℤ)).compl_mem_cofinite] with n hn
  have hpos : 0 < ‖n‖ := norm_pos_iff.2 hn
  rw [Real.norm_of_nonneg (by positivity), Real.rpow_neg hpos.le, Real.rpow_natCast]
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hpos.le (by linarith) _)

end TauCeti
