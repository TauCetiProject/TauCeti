/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.SeparableClosure

/-!
# Roots of `X ^ N - t X - b` lie in the separable closure

Let `L / K` be a field extension and `N` a natural number that is zero in `K`, as `N = p ^ n` is
in characteristic `p`. For `t ∈ K` nonzero and `b ∈ L` separable over `K`, the polynomial
`X ^ N - t X - b` has derivative `-t`, a unit, so it is separable over the separable closure of
`K` in `L`. Its roots in `L` are therefore separable over `K`.

This is the step that perturbs a purely inseparable element `a`, with `a ^ N` separable, into
nearby separable elements.
-/

public section

open Polynomial

namespace TauCeti

/-- In an extension `L` of a field `K`, a root of `X ^ N - t X - b`, for `N` zero in `K`, `t ∈ K`
nonzero and `b` separable over `K`, is separable over `K`. -/
theorem mem_separableClosure_of_pow_sub_mul_sub_eq_zero {K L : Type*} [Field K] [Field L]
    [Algebra K L] {N : ℕ} (hN : (N : K) = 0) {t : K} (ht : t ≠ 0) {b y : L}
    (hb : b ∈ separableClosure K L) (hy : y ^ N - algebraMap K L t * y - b = 0) :
    y ∈ separableClosure K L := by
  set E := separableClosure K L
  set c := algebraMap K E t
  have hc : c ≠ 0 := (_root_.map_ne_zero _).2 ht
  let g : E[X] := X ^ N - C c * X - C ⟨b, hb⟩
  have hNE : (N : E) = 0 := by simpa using congr(algebraMap K E $hN)
  have hg : g.Separable := by
    simpa [g, sub_eq_add_neg] using
      separable_C_mul_X_pow_add_C_mul_X_add_C (1 : E) (-c) (-⟨b, hb⟩) hNE hc.isUnit.neg
  have hgy : aeval y g = 0 := by simpa [g, c] using hy
  have hsep : IsSeparable E y := hg.of_dvd (minpoly.dvd E y hgy)
  exact mem_separableClosure_iff.2 (IsSeparable.of_algebra_isSeparable_of_isSeparable K hsep)

end TauCeti
