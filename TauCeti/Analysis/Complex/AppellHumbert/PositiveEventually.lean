/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.AppellHumbert.Positive
import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
# Cone properties and eventual positivity of Appell–Humbert data

Let `D` be an Appell–Humbert datum for a subgroup `L` of a complex normed space `V`
(`TauCeti.AppellHumbertData`). Positive Appell–Humbert data (`TauCeti.AppellHumbertData.IsPositive`)
form a convex cone: they are closed under addition (`TauCeti.AppellHumbertData.IsPositive.add`)
and positive natural scalar multiplication (`TauCeti.AppellHumbertData.IsPositive.nsmul`).
When `V` is finite-dimensional, a positive datum `D` eventually dominates any datum `A`: for all
sufficiently large `m : ℕ`, `m • D - A` is again positive
(`TauCeti.AppellHumbertData.IsPositive.eventually_nsmul_sub`).

## Main results

* `TauCeti.AppellHumbertData.IsPositive.add`: the sum of two positive data is positive.
* `TauCeti.AppellHumbertData.IsPositive.nsmul`: a positive multiple of a positive datum is
  positive.
* `TauCeti.AppellHumbertData.IsPositive.eventually_nsmul_sub`: for `V` finite-dimensional and
  `D` positive, `m • D - A` is positive for all sufficiently large `m : ℕ`.
* `TauCeti.AppellHumbertData.IsPositive.exists_nsmul_sub_isPositive`: existence of `m ≠ 0` with
  `(m • D - A).IsPositive`.

## Provenance

Adapted from `New.ThetaTori.IsAmpleType.eventually_isPosRiemann_smul_sub` (file
`src/Lib/Shimura/GoodReduction/TorsionSizes.lean`) in grh-lean
(https://github.com/lsernau/grh-lean, commit `72fead102f663d5c7a407964a13dc0cf9d977207`,
Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

open Complex Filter
open scoped Real

namespace TauCeti.AppellHumbertData

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {L : Submodule ℤ V}
  {D D' : AppellHumbertData L}

/-- The sum of two positive Appell–Humbert data is positive. -/
theorem IsPositive.add (hD : D.IsPositive) (hD' : D'.IsPositive) : (D + D').IsPositive := by
  refine (D + D').isPositive_iff.mpr fun u hu ↦ ?_
  rw [riemannForm_add, LinearMap.add_apply, LinearMap.add_apply]
  exact add_pos (hD.pos hu) (hD'.pos hu)

/-- A positive natural multiple of a positive Appell–Humbert datum is positive. -/
theorem IsPositive.nsmul (hD : D.IsPositive) {n : ℕ} (hn : n ≠ 0) : (n • D).IsPositive := by
  refine (n • D).isPositive_iff.mpr fun u hu ↦ ?_
  rw [riemannForm_nsmul, LinearMap.smul_apply, LinearMap.smul_apply, nsmul_eq_mul]
  exact mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) (hD.pos hu)

/-- In a finite-dimensional complex normed space, a positive Appell–Humbert datum `D` eventually
dominates any Appell–Humbert datum `A`: for all sufficiently large `m : ℕ`, `m • D - A` has
positive Riemann form. -/
theorem IsPositive.eventually_nsmul_sub [FiniteDimensional ℂ V] (hD : D.IsPositive)
    (A : AppellHumbertData L) :
    ∀ᶠ m : ℕ in atTop, m ≠ 0 ∧ (m • D - A).IsPositive := by
  obtain ⟨c, hc, h_coerc⟩ := hD.exists_pos_mul_sq_le
  have hA_le (u : V) : A.riemannForm (I • u) u ≤ (‖A.form‖ / π) * ‖u‖ ^ 2 := by
    rw [riemannForm_apply, div_eq_mul_inv]
    have h_op (x y : V) : ‖A.form x y‖ ≤ ‖A.form‖ * ‖x‖ * ‖y‖ :=
      ((A.form x).le_opNorm y).trans
        (mul_le_mul_of_nonneg_right (A.form.le_opNorm x) (norm_nonneg y))
    have h2 : ‖A.form u (I • u) - A.form (I • u) u‖ ≤ 2 * ‖A.form‖ * ‖u‖ ^ 2 := by
      calc ‖A.form u (I • u) - A.form (I • u) u‖
          ≤ ‖A.form u (I • u)‖ + ‖A.form (I • u) u‖ := norm_sub_le _ _
        _ ≤ ‖A.form‖ * ‖u‖ * ‖I • u‖ + ‖A.form‖ * ‖I • u‖ * ‖u‖ :=
            add_le_add (h_op u (I • u)) (h_op (I • u) u)
        _ = 2 * ‖A.form‖ * ‖u‖ ^ 2 := by simp [norm_smul, sq]; ring
    calc (A.form u (I • u) - A.form (I • u) u).im * (2 * π)⁻¹
        ≤ (2 * ‖A.form‖ * ‖u‖ ^ 2) * (2 * π)⁻¹ := by
            gcongr; exact (Complex.im_le_norm _).trans h2
      _ = (‖A.form‖ / π) * ‖u‖ ^ 2 := by field_simp
  filter_upwards [eventually_ne_atTop 0,
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (‖A.form‖ / (π * c)))] with
    m hm0 hm
  refine ⟨hm0, (m • D - A).isPositive_iff.mpr fun u hu ↦ ?_⟩
  rw [riemannForm_sub, riemannForm_nsmul, LinearMap.sub_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.smul_apply, nsmul_eq_mul]
  have hmc : ‖A.form‖ / π < (m : ℝ) * c := by
    have hmul := (div_lt_iff₀ (by positivity : (0 : ℝ) < π * c)).mp hm
    rw [div_lt_iff₀ Real.pi_pos]
    linarith
  have hu2 : 0 < ‖u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
  have hD_le := mul_le_mul_of_nonneg_left (h_coerc u) (Nat.cast_nonneg m)
  nlinarith [hA_le u]

/-- In a finite-dimensional complex normed space, for any positive Appell–Humbert datum `D` and
any datum `A`, there exists `m ≠ 0` such that `m • D - A` is positive. -/
theorem IsPositive.exists_nsmul_sub_isPositive [FiniteDimensional ℂ V] (hD : D.IsPositive)
    (A : AppellHumbertData L) :
    ∃ m : ℕ, m ≠ 0 ∧ (m • D - A).IsPositive :=
  (hD.eventually_nsmul_sub A).exists

end TauCeti.AppellHumbertData
