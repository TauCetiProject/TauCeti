/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Ring

/-!
# Differences of powers of asymptotically close functions

If two functions `f` and `g` into a seminormed ring are both `O(ρ)` along a filter and differ by
`o(ρ)`, then their `m`-th powers differ by `o(ρ ^ m)` (`Asymptotics.IsLittleO.pow_sub_pow`). This
is how a leading-order expansion `f = g + o(ρ)` passes through a homogeneous polynomial: a change
of variables `e z = T z + o(‖z‖)` with `T` linear turns the monomial `(e z) ^ m` into
`(T z) ^ m + o(‖z‖ ^ m)`.
-/

public section

open Filter

namespace Asymptotics

/-- **Powers of asymptotically close functions.** If `f - g = o(ρ)` and both `f` and `g` are
`O(ρ)`, then `f ^ m - g ^ m = o(ρ ^ m)` for every `m`. -/
theorem IsLittleO.pow_sub_pow {α R S : Type*} [SeminormedRing R] [NormedRing S] [NormMulClass S]
    [NormOneClass S] {l : Filter α} {f g : α → R} {ρ : α → S}
    (h : (fun x ↦ f x - g x) =o[l] ρ) (hf : f =O[l] ρ) (hg : g =O[l] ρ) (m : ℕ) :
    (fun x ↦ f x ^ m - g x ^ m) =o[l] fun x ↦ ρ x ^ m := by
  induction m with
  | zero => simp only [pow_zero, sub_self]; exact isLittleO_zero _ _
  | succ m ih =>
    -- `f ^ (m + 1) - g ^ (m + 1) = f ^ m (f - g) + (f ^ m - g ^ m) g`
    refine ((((hf.pow m).mul_isLittleO h).add (ih.mul_isBigO hg)).congr_left fun x ↦ ?_).congr_right
      fun x ↦ (pow_succ _ _).symm
    rw [pow_succ, pow_succ, mul_sub, sub_mul]
    abel

end Asymptotics
