/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.C1Jet.Basic
public import TauCeti.Dynamics.OrderedSimplex.Basic

import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Pointwise `C¹` bounds on the ordered simplex

A complex-valued function `f` on the chart `ℝ^d` satisfies `TauCeti.C1BoundedOn d f K` when it is
`C¹` on the ordered simplex `Δ = TauCeti.orderedSimplex d` and `‖f x‖ + ‖Df(x)‖ ≤ K` at every point
`x ∈ Δ`, where `Df` is the derivative within `Δ`. This is the bound in which the spectral gap of the
transfer operators of the accelerated branches is measured: their iterates, renormalised, converge
exponentially fast in it.

The predicate depends only on the values of `f` on `Δ`, is monotone in `K`, adds bounds under sums
and scales them by `‖c‖` under multiplication by `c`. It is comparable with the norm
`‖f‖_∞ + ‖Df‖_∞` of the Banach space `TauCeti.C1Jet ℂ Δ ℂ` of `C¹` jets on `Δ`: a jet of norm at
most `K` has values satisfying the bound with `K`, and a function satisfying the bound with `K` has
a jet of norm at most `2 K`.

## Main definitions

* `TauCeti.C1BoundedOn d f K`: the pointwise `C¹` bound on the ordered simplex.

## Main results

* `TauCeti.C1BoundedOn.mono`, `TauCeti.C1BoundedOn.congr`, `TauCeti.C1BoundedOn.add`,
  `TauCeti.C1BoundedOn.const_mul`: the bound is monotone, depends only on the values on `Δ`, and
  is subadditive and homogeneous.
* `TauCeti.C1Jet.c1BoundedOn` and `TauCeti.C1BoundedOn.norm_ofContDiffOn_le`: the comparison with
  the jet norm, up to a factor `2`.

## References

* A. Gamburd, M. Magee, R. Ronan, *An asymptotic formula for integer points on Markoff–Hurwitz
  varieties*, Ann. of Math. 190 (2019), §4.2, where the transfer operators act on `C¹` functions on
  the ordered simplex with the norm `‖f‖_∞ + ‖∇f‖_∞`.
-/

public section

open Set

namespace TauCeti

variable {d : ℕ}

/-- The pointwise `C¹` bound on the ordered simplex: `f` is `C¹` on `Δ = orderedSimplex d` and
`‖f x‖ + ‖Df(x)‖ ≤ K` at every point `x ∈ Δ`, where `Df` is the derivative within `Δ`. -/
def C1BoundedOn (d : ℕ) (f : (Fin d → ℝ) → ℂ) (K : ℝ) : Prop :=
  ContDiffOn ℝ 1 f (orderedSimplex d) ∧
    ∀ x ∈ orderedSimplex d, ‖f x‖ + ‖fderivWithin ℝ f (orderedSimplex d) x‖ ≤ K

theorem c1BoundedOn_iff {f : (Fin d → ℝ) → ℂ} {K : ℝ} :
    C1BoundedOn d f K ↔ ContDiffOn ℝ 1 f (orderedSimplex d) ∧
      ∀ x ∈ orderedSimplex d, ‖f x‖ + ‖fderivWithin ℝ f (orderedSimplex d) x‖ ≤ K :=
  Iff.rfl

namespace C1BoundedOn

variable {f g : (Fin d → ℝ) → ℂ} {K L : ℝ}

theorem contDiffOn (h : C1BoundedOn d f K) : ContDiffOn ℝ 1 f (orderedSimplex d) :=
  h.1

theorem norm_add_norm_fderivWithin_le (h : C1BoundedOn d f K) {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) :
    ‖f x‖ + ‖fderivWithin ℝ f (orderedSimplex d) x‖ ≤ K :=
  h.2 x hx

theorem norm_le (h : C1BoundedOn d f K) {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) :
    ‖f x‖ ≤ K :=
  (le_add_of_nonneg_right (norm_nonneg _)).trans (h.2 x hx)

theorem norm_fderivWithin_le (h : C1BoundedOn d f K) {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) : ‖fderivWithin ℝ f (orderedSimplex d) x‖ ≤ K :=
  (le_add_of_nonneg_left (norm_nonneg _)).trans (h.2 x hx)

/-- A bound is nonnegative: the simplex is nonempty. -/
theorem nonneg (h : C1BoundedOn d f K) : 0 ≤ K := by
  obtain ⟨x, hx⟩ := (interior_orderedSimplex_nonempty d).mono interior_subset
  exact (norm_nonneg _).trans (h.norm_le hx)

/-- The bound is monotone in `K`. -/
theorem mono (h : C1BoundedOn d f K) (hKL : K ≤ L) : C1BoundedOn d f L :=
  ⟨h.1, fun x hx ↦ (h.2 x hx).trans hKL⟩

/-- The bound depends only on the values on the simplex. -/
theorem congr (h : C1BoundedOn d f K) (hfg : EqOn f g (orderedSimplex d)) :
    C1BoundedOn d g K := by
  refine ⟨h.1.congr fun x hx ↦ (hfg hx).symm, fun x hx ↦ ?_⟩
  rw [← hfg hx, fderivWithin_congr' (fun y hy ↦ (hfg hy).symm) hx]
  exact h.2 x hx

/-- Bounds add under sums. -/
theorem add (hf : C1BoundedOn d f K) (hg : C1BoundedOn d g L) : C1BoundedOn d (f + g) (K + L) := by
  refine ⟨hf.1.add hg.1, fun x hx ↦ ?_⟩
  rw [fderivWithin_add (uniqueDiffOn_orderedSimplex d x hx)
    (hf.1.differentiableOn one_ne_zero x hx) (hg.1.differentiableOn one_ne_zero x hx),
    Pi.add_apply]
  calc ‖f x + g x‖ + ‖fderivWithin ℝ f (orderedSimplex d) x +
        fderivWithin ℝ g (orderedSimplex d) x‖
      ≤ (‖f x‖ + ‖fderivWithin ℝ f (orderedSimplex d) x‖) +
        (‖g x‖ + ‖fderivWithin ℝ g (orderedSimplex d) x‖) := by
        linarith [norm_add_le (f x) (g x), norm_add_le (fderivWithin ℝ f (orderedSimplex d) x)
          (fderivWithin ℝ g (orderedSimplex d) x)]
    _ ≤ K + L := add_le_add (hf.2 x hx) (hg.2 x hx)

/-- Multiplication by `c` scales the bound by `‖c‖`. -/
theorem const_mul (h : C1BoundedOn d f K) (c : ℂ) :
    C1BoundedOn d (fun x ↦ c * f x) (‖c‖ * K) := by
  refine ⟨contDiffOn_const.mul h.1, fun x hx ↦ ?_⟩
  rw [fderivWithin_const_mul (uniqueDiffOn_orderedSimplex d x hx)
    (h.1.differentiableOn one_ne_zero x hx), norm_mul, norm_smul, ← mul_add]
  exact mul_le_mul_of_nonneg_left (h.2 x hx) (norm_nonneg c)

/-- A function with the pointwise bound `K` has a `C¹` jet of norm at most `2 K`. -/
theorem norm_ofContDiffOn_le (h : C1BoundedOn d f K) :
    ‖C1Jet.ofContDiffOn ℂ (uniqueDiffOn_orderedSimplex d) h.contDiffOn‖ ≤ 2 * K := by
  rw [C1Jet.norm_def, two_mul]
  refine add_le_add ((ContinuousMap.norm_le _ h.nonneg).2 fun x ↦ ?_)
    ((ContinuousMap.norm_le _ h.nonneg).2 fun x ↦ ?_)
  · simpa using h.norm_le x.property
  · simpa using h.norm_fderivWithin_le x.property

end C1BoundedOn

/-- The values of a `C¹` jet of norm at most `K` on the simplex, extended in any way to `ℝ^d`,
satisfy the pointwise bound with `K`. -/
theorem C1Jet.c1BoundedOn (j : C1Jet ℂ (orderedSimplex d) ℂ) {f : (Fin d → ℝ) → ℂ}
    (hf : ∀ x : orderedSimplex d, f x = j.value x) {K : ℝ} (hK : ‖j‖ ≤ K) :
    C1BoundedOn d f K := by
  refine ⟨j.contDiffOn (convex_orderedSimplex d) hf, fun x hx ↦ ?_⟩
  rw [hf ⟨x, hx⟩, j.fderivWithin_eq (convex_orderedSimplex d) (uniqueDiffOn_orderedSimplex d) hf
    ⟨x, hx⟩]
  exact (add_le_add (j.value.norm_coe_le_norm _) (j.deriv.norm_coe_le_norm _)).trans
    ((j.norm_def).symm.le.trans hK)

end TauCeti
