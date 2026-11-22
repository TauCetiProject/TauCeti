/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import TauCeti.Analysis.Normed.Group.Int
import TauCeti.Analysis.SpecialFunctions.Pow.Summable
import TauCeti.LinearAlgebra.Basis.RestrictScalars
import TauCeti.Topology.DiscreteSubset

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

Mathlib's `ZLattice.summable_norm_rpow` (`∑ ℓ ∈ L, ‖ℓ‖ ^ r` converges for `r < -rank L`) is the
common source of the power bounds below: shifting the base by one keeps the sum convergent
(`ZLattice.summable_one_add_norm_rpow`), and the bounds over the integer vectors are read off the
standard lattice.

For a finite index type `d`, the integer vectors `d → ℤ` are the standard lattice
`ℤ^d ⊆ ℝ^d`, so summability over them is summability over that lattice
(`TauCeti.summable_pi_int_iff_summable_span`). Read with the sup norm on `d → ℤ`, the power sum
`∑ n, ‖n‖ ^ r` converges for `r < -card d` (`TauCeti.summable_pi_int_norm_rpow`). This is the
majorant used to sum Fourier coefficients on the torus `(ℝ / ℤ)^d`.

## Main statements

* `ZLattice.summable_exp_neg_mul_norm_add_sq`: `∑ v ∈ L, exp (-c ‖x + v‖²)` converges for
  `0 < c`.
* `ZLattice.discreteTopology_of_summable_exp_neg_mul_norm_add_sq`: the converse, a subgroup `L`
  of a normed group over which some function `v ↦ exp (-c ‖x + v‖²)`, `c : ℝ`, is summable is
  discrete.
* `ZLattice.summable_one_add_norm_rpow`: `∑ ℓ ∈ L, (1 + ‖ℓ‖) ^ r` converges for real
  `r < -rank L`; `ZLattice.summable_one_add_norm_pow_inv` specialises it to `r = -k` for a natural
  number `k` exceeding the rank, written `((1 + ‖ℓ‖) ^ k)⁻¹`.
* `ZLattice.summable_one_add_norm_pow_mul_norm_of_decay`: a function decaying faster than every
  power of `1 + ‖x‖` is summable along `L` against every power of `1 + ‖ℓ‖`.
* `TauCeti.summable_pi_int_iff_summable_span`: for a finite index type `d`, summability over
  `d → ℤ` is summability over the standard lattice `ℤ^d ⊆ ℝ^d`.
* `TauCeti.summable_pi_int_norm_rpow`: `∑ n : d → ℤ, ‖n‖ ^ r` converges for `r < -card d`.
* `TauCeti.summable_pi_int_one_add_norm_rpow`: `∑ n : d → ℤ, (1 + ‖n‖) ^ r` converges for real
  `r < -card d`; `TauCeti.summable_pi_int_one_add_norm_pow_inv` specialises it to `r = -k` for a
  natural number `k` exceeding `card d`, written `((1 + ‖n‖) ^ k)⁻¹`.
-/

public section

open Filter Asymptotics Topology

namespace ZLattice

section Discrete

variable {E : Type*} [NormedAddCommGroup E] (L : Submodule ℤ E)

/-- If `v ↦ exp (-c ‖γ + v‖²)` is summable over a subgroup `L` of a normed group for some
`c : ℝ`, then `L` is discrete. The terms are continuous in `v`, positive at `0` and tend to `0`
along the cofinite filter, so `0` is isolated (`Filter.Tendsto.isOpen_singleton_of_cofinite`). -/
theorem discreteTopology_of_summable_exp_neg_mul_norm_add_sq (γ : E) {c : ℝ}
    (h : Summable fun v : L => Real.exp (-c * ‖γ + (v : E)‖ ^ 2)) : DiscreteTopology L :=
  discreteTopology_of_isOpen_singleton_zero <|
    h.tendsto_cofinite_zero.isOpen_singleton_of_cofinite (by fun_prop) (Real.exp_pos _).ne'

end Discrete

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

/-- On a discrete subgroup `L` of a finite-dimensional real normed space, `(1 + ‖ℓ‖) ^ r` is
summable for every real `r < -rank L`. This shifts the base of Mathlib's
`ZLattice.summable_norm_rpow` by one (`Summable.const_add_rpow`). -/
theorem summable_one_add_norm_rpow (r : ℝ) (hr : r < -Module.finrank ℤ L) :
    Summable fun ℓ : L ↦ (1 + ‖(ℓ : E)‖) ^ r := by
  have h := (summable_norm_rpow L r hr).const_add_rpow
    (hr.le.trans (neg_nonpos.2 (Nat.cast_nonneg _)))
    ((eventually_cofinite_ne 0).mono fun ℓ hℓ ↦ norm_pos_iff.2 hℓ) 1
  simpa only [Submodule.norm_coe] using h

/-- On a discrete subgroup `L` of a finite-dimensional real normed space, `((1 + ‖ℓ‖) ^ r)⁻¹` is
summable as soon as the natural number `r` exceeds the rank of `L`. -/
theorem summable_one_add_norm_pow_inv {r : ℕ} (hr : Module.finrank ℤ L < r) :
    Summable fun ℓ : L ↦ ((1 + ‖(ℓ : E)‖) ^ r)⁻¹ :=
  (summable_one_add_norm_rpow L (-r) (neg_lt_neg (by exact_mod_cast hr))).congr fun ℓ ↦ by
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast]

/-- A function on `E` decaying faster than every power of `1 + ‖x‖` is summable along a discrete
subgroup `L` against every power of `1 + ‖ℓ‖`. -/
theorem summable_one_add_norm_pow_mul_norm_of_decay {F : Type*} [SeminormedAddCommGroup F]
    {f : E → F} (hf : ∀ N : ℕ, ∃ C, ∀ x, (1 + ‖x‖) ^ N * ‖f x‖ ≤ C) (k : ℕ) :
    Summable fun ℓ : L ↦ (1 + ‖(ℓ : E)‖) ^ k * ‖f ℓ‖ := by
  set r := Module.finrank ℤ L + 1
  obtain ⟨C, hC⟩ := hf (k + r)
  have hsum := summable_one_add_norm_pow_inv L (r := r) (by omega)
  refine (hsum.mul_left C).of_nonneg_of_le (fun ℓ ↦ by positivity) fun ℓ ↦ ?_
  have hpos : 0 < (1 + ‖(ℓ : E)‖) ^ r := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hpos, mul_right_comm, ← pow_add]
  exact hC ℓ

end ZLattice

namespace TauCeti

/-- For a finite index type `d`, through `n ↦ (fun i ↦ (n i : ℝ))`, the integer vectors `d → ℤ`
are the standard lattice `ℤ^d ⊆ ℝ^d`, the `ℤ`-span of the standard basis. So a function on `d → ℝ`
is summable over the integer vectors exactly when it is summable over that lattice. The
equivalence is the coordinate map of the integral basis `Module.Basis.restrictScalars ℤ` of the
standard basis (`Module.Basis.coe_restrictScalars_equivFun_symm`). -/
theorem summable_pi_int_iff_summable_span {d : Type*} [Finite d] {α : Type*} [AddCommMonoid α]
    [TopologicalSpace α] {f : (d → ℝ) → α} :
    (Summable fun n : d → ℤ ↦ f fun i ↦ (n i : ℝ)) ↔
      Summable fun ℓ : Submodule.span ℤ (Set.range (Pi.basisFun ℝ d)) ↦ f ℓ := by
  -- The lattice vector with coordinates `n` is the real vector `fun i ↦ (n i : ℝ)`.
  have hcoe (n : d → ℤ) :
      (((Pi.basisFun ℝ d).restrictScalars ℤ).equivFun.symm n : d → ℝ) = fun i ↦ (n i : ℝ) := by
    simp [Module.Basis.coe_restrictScalars_equivFun_symm]
  rw [← ((Pi.basisFun ℝ d).restrictScalars ℤ).equivFun.symm.toEquiv.summable_iff]
  simp only [Function.comp_def, LinearEquiv.coe_toEquiv, hcoe]

/-- The sup norms of the integer vectors `n : d → ℤ` satisfy `∑ n, ‖n‖ ^ r < ∞` when
`r < -card d`. Here `‖0‖ ^ r = 0`. -/
theorem summable_pi_int_norm_rpow {d : Type*} [Fintype d] (r : ℝ) (hr : r < -Fintype.card d) :
    Summable fun n : d → ℤ ↦ ‖n‖ ^ r := by
  have hL := ZLattice.summable_norm_rpow (Submodule.span ℤ (Set.range (Pi.basisFun ℝ d))) r
    (by rwa [ZLattice.rank ℝ, Module.finrank_fintype_fun_eq_card])
  simp only [← Submodule.norm_coe] at hL
  simpa only [pi_norm_intCast_real] using
    (summable_pi_int_iff_summable_span (f := fun x ↦ ‖x‖ ^ r)).2 hL

/-- The series `∑ n, (1 + ‖n‖) ^ r` over the integer vectors `n : d → ℤ`, with the sup norm,
converges for every real `r < -card d`. -/
theorem summable_pi_int_one_add_norm_rpow {d : Type*} [Fintype d] (r : ℝ)
    (hr : r < -Fintype.card d) : Summable fun n : d → ℤ ↦ (1 + ‖n‖) ^ r := by
  have hL := ZLattice.summable_one_add_norm_rpow
    (Submodule.span ℤ (Set.range (Pi.basisFun ℝ d))) r
    (by rwa [ZLattice.rank ℝ, Module.finrank_fintype_fun_eq_card])
  simpa only [pi_norm_intCast_real] using
    (summable_pi_int_iff_summable_span (f := fun x ↦ (1 + ‖x‖) ^ r)).2 hL

/-- The series `∑ n, ((1 + ‖n‖) ^ r)⁻¹` over the integer vectors `n : d → ℤ`, with the sup norm,
converges once the natural number `r` exceeds `card d`. -/
theorem summable_pi_int_one_add_norm_pow_inv {d : Type*} [Fintype d] {r : ℕ}
    (hr : Fintype.card d < r) : Summable fun n : d → ℤ ↦ ((1 + ‖n‖) ^ r)⁻¹ :=
  (summable_pi_int_one_add_norm_rpow (-r) (neg_lt_neg (by exact_mod_cast hr))).congr fun n ↦ by
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast]

end TauCeti
