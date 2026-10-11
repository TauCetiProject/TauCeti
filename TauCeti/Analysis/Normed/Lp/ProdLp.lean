/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# The `ℓ^p` product: coordinate bounds and components of indicators

Mathlib bounds each factor of `WithLp p (α × β)` by the whole (`WithLp.norm_fst_le` and
`WithLp.norm_snd_le`) and computes the norm exactly for `p = 1` and `p = 2`.  This file records
the opposite bound, valid for every exponent `1 ≤ p ≤ ∞`: the `ℓ^p` norm of a pair is at most the
sum of the norms of its two components.  For `p = 1` the bound is an identity for every pair.

It also records that taking a component of `WithLp p (α × β)` commutes with `Set.indicator`, as
Mathlib's `norm_indicator_eq_indicator_norm` does for the norm.

## Main statements

* `WithLp.prod_norm_le_norm_fst_add_norm_snd` — the bound `‖x‖ ≤ ‖x.fst‖ + ‖x.snd‖`.
* `TauCeti.snd_lt_one` — a unit vector in `E × ℝ` other than `(0, 1)` has last coordinate
  strictly less than `1`.
* `WithLp.fst_indicator`, `WithLp.snd_indicator` — a component of an indicator is the indicator
  of the component.
-/

public section

open scoped ENNReal

namespace TauCeti

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {α β : Type*} [SeminormedAddCommGroup α]
  [SeminormedAddCommGroup β]

/-- The `ℓ^p` norm of a pair is at most the sum of the norms of its two components. -/
theorem _root_.WithLp.prod_norm_le_norm_fst_add_norm_snd (x : WithLp p (α × β)) :
    ‖x‖ ≤ ‖x.fst‖ + ‖x.snd‖ :=
  calc ‖x‖ = ‖WithLp.idemFst x + WithLp.idemSnd x‖ :=
        congrArg norm ((DFunLike.congr_fun WithLp.idemFst_add_idemSnd x).trans
          (AddMonoid.End.one_apply x)).symm
    _ ≤ ‖WithLp.idemFst x‖ + ‖WithLp.idemSnd x‖ := norm_add_le _ _
    _ = ‖x.fst‖ + ‖x.snd‖ := by
        rw [WithLp.idemFst_apply, WithLp.idemSnd_apply, WithLp.norm_toLp_fst,
          WithLp.norm_toLp_snd]

section Real

variable {E : Type*} [NormedAddCommGroup E]

/-- A unit vector of `E × ℝ` other than the vertical one `(0, 1)` has height less than `1`. -/
theorem snd_lt_one {u : WithLp 2 (E × ℝ)} (hnorm : ‖u‖ = 1)
    (hu : u ≠ WithLp.toLp 2 (0, 1)) : u.snd < 1 := by
  have hle : u.snd ≤ 1 := (le_abs_self _).trans ((WithLp.norm_snd_le (x := u)).trans hnorm.le)
  refine hle.lt_of_ne fun h ↦ hu ((WithLp.ext_iff 2).2 (Prod.ext ?_ (by simpa using h)))
  have hsq := WithLp.prod_norm_sq_eq_of_L2 u
  rw [hnorm, h] at hsq
  simpa using hsq

end Real

section Indicator

variable {p : ℝ≥0∞} {ι α β : Type*} [AddCommGroup α] [AddCommGroup β] {s : Set ι}

/-- The first component of an indicator function is the indicator of the first components. -/
theorem _root_.WithLp.fst_indicator (f : ι → WithLp p (α × β)) (x : ι) :
    (s.indicator f x).fst = s.indicator (fun y => (f y).fst) x :=
  (congr_fun (Set.indicator_comp_of_zero (g := WithLp.fst) WithLp.zero_fst) x).symm

/-- The second component of an indicator function is the indicator of the second components. -/
theorem _root_.WithLp.snd_indicator (f : ι → WithLp p (α × β)) (x : ι) :
    (s.indicator f x).snd = s.indicator (fun y => (f y).snd) x :=
  (congr_fun (Set.indicator_comp_of_zero (g := WithLp.snd) WithLp.zero_snd) x).symm

end Indicator

end TauCeti
