/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.MaximumPrinciple.Parabolic.WholeSpace
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv
import TauCeti.LinearAlgebra.Matrix.ToQuadraticForm

/-!
# The comparison principle for parabolic equations on the whole line

On the slab `[0, T] × ℝ` consider the one-dimensional parabolic operator

`P u = ∂ₜu - a ∂ₓ²u - b ∂ₓu - c u`

with time-dependent coefficients `a b c : ℝ → ℝ → ℝ`. As in
`TauCeti.Analysis.PDE.MaximumPrinciple.Parabolic.WholeSpace`, functions `u : ℝ → ℝ → ℝ` take the
time first, so `u t` is the spatial slice at time `t`. Here the spatial derivatives are the
ordinary ones, `∂ₓu = deriv (u t) x` and `∂ₓ²u = deriv (deriv (u t)) x`.

The coefficients are only required to satisfy, for `0 < t < T`, the growth conditions
`0 ≤ a(t, x) ≤ Λ (1 + x²)`, `|b(t, x)| ≤ β (1 + |x|)` and the upper bound `c(t, x) ≤ γ`; in
particular bounded coefficients with `a ≥ 0` are allowed, and `a` may vanish. Then the comparison
principle holds among classical solutions whose difference is bounded above: if `P u ≤ P v` for
`0 < t < T` and `u(·, 0) ≤ v(·, 0)`, then `u ≤ v` on `[0, T] × ℝ`. Uniqueness for the Cauchy
problem among classical solutions with bounded difference follows.

These are the statements of the whole-space comparison principle for `ℝⁿ = EuclideanSpace ℝ ι`
with `ι = Fin 1`, transported along the identification `EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ`, under
which the Hessian and gradient terms of the `n`-dimensional operator become `a ∂ₓ²u` and `b ∂ₓu`.

## Main declarations

All declarations are in the `TauCeti.PDE` namespace.

* `le_of_deriv_sub_mul_deriv_deriv_add_mul_deriv_add_mul_le_of_le_initial`:
  **the comparison principle** on the whole line.
* `eq_of_deriv_sub_mul_deriv_deriv_add_mul_deriv_add_mul_eq_of_eq_initial`:
  uniqueness for the Cauchy problem among classical solutions with bounded difference.

## References

* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 2, Section 4.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open Set

variable {a b c : ℝ → ℝ → ℝ} {u v : ℝ → ℝ → ℝ} {T Lam β γ : ℝ}

/-- The coordinate of the one-dimensional Euclidean space. -/
private abbrev coord : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ :=
  PiLp.equivOfUnique 2 ℝ fun _ : Fin 1 ↦ ℝ

/-- Pulled back to `EuclideanSpace ℝ (Fin 1)`, the second-order part of the one-dimensional
operator is the second-order part of the `n`-dimensional operator with the `1 × 1` diffusion matrix
`(a)` and the drift vector `(b)`. -/
private theorem sum_mul_fderiv_fderiv_add_fderiv_comp_coord (f : ℝ → ℝ) (A B : ℝ)
    (z : EuclideanSpace ℝ (Fin 1)) :
    ∑ i, ∑ j, Matrix.of (fun _ _ : Fin 1 ↦ A) i j *
        fderiv ℝ (fderiv ℝ (f ∘ coord)) z (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1) +
      fderiv ℝ (f ∘ coord) z (EuclideanSpace.single 0 B) =
      A * deriv (deriv f) (coord z) + B * deriv f (coord z) := by
  rw [coord.comp_right_fderiv]
  simp [coord.fderiv_fderiv_comp_right_apply]

/-- **The comparison principle for parabolic equations on the whole line.** Let
`P u = ∂ₜu - a ∂ₓ²u - b ∂ₓu - c u`, where for `0 < t < T` the coefficients satisfy
`0 ≤ a(t, x) ≤ Λ (1 + x²)`, `|b(t, x)| ≤ β (1 + |x|)` and `c(t, x) ≤ γ`. Let `u` and `v` be
continuous on `[0, T] × ℝ`, `C²` in space and differentiable in time for `0 < t < T`, with `u - v`
bounded above. If `P u ≤ P v` for `0 < t < T` and `u(·, 0) ≤ v(·, 0)`, then `u ≤ v` on
`[0, T] × ℝ`. -/
theorem le_of_deriv_sub_mul_deriv_deriv_add_mul_deriv_add_mul_le_of_le_initial
    (ha : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, 0 ≤ a t x)
    (ha' : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, a t x ≤ Lam * (1 + x ^ 2))
    (hb : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, |b t x| ≤ β * (1 + |x|))
    (hc : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, c t x ≤ γ)
    (hucont : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hvcont : ContinuousOn (Function.uncurry v) (Icc 0 T ×ˢ univ))
    (hbdd : BddAbove (Function.uncurry (u - v) '' Icc 0 T ×ˢ univ))
    (hucd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, ContDiffAt ℝ 2 (u t) x)
    (hvcd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, ContDiffAt ℝ 2 (v t) x)
    (hudiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hvdiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, DifferentiableAt ℝ (fun s ↦ v s x) t)
    (hP : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, deriv (fun s ↦ u s x) t -
      (a t x * deriv (deriv (u t)) x + b t x * deriv (u t) x + c t x * u t x) ≤
      deriv (fun s ↦ v s x) t -
      (a t x * deriv (deriv (v t)) x + b t x * deriv (v t) x + c t x * v t x))
    (hinit : ∀ x, u 0 x ≤ v 0 x) :
    ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ x, u t x ≤ v t x := by
  -- Pull everything back along the coordinate `EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ`.
  have hmaps : MapsTo (Prod.map id coord) (Icc 0 T ×ˢ univ) (Icc 0 T ×ˢ univ) :=
    fun p hp ↦ ⟨hp.1, mem_univ _⟩
  have hcont {w : ℝ → ℝ → ℝ} (hw : ContinuousOn (Function.uncurry w) (Icc 0 T ×ˢ univ)) :
      ContinuousOn (Function.uncurry fun t ↦ w t ∘ coord) (Icc 0 T ×ˢ univ) :=
    hw.comp (continuous_id.prodMap coord.continuous).continuousOn hmaps
  have hnorm (z : EuclideanSpace ℝ (Fin 1)) : ‖z‖ = |coord z| := by
    simp [EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs]
  have hop {w : ℝ → ℝ → ℝ} (t : ℝ) (z : EuclideanSpace ℝ (Fin 1)) :
      deriv (fun s ↦ (w s ∘ coord) z) t -
        (∑ i, ∑ j, Matrix.of (fun _ _ : Fin 1 ↦ a t (coord z)) i j *
            fderiv ℝ (fderiv ℝ (w t ∘ coord)) z (EuclideanSpace.single i 1)
              (EuclideanSpace.single j 1) +
          fderiv ℝ (w t ∘ coord) z (EuclideanSpace.single 0 (b t (coord z))) +
          c t (coord z) * (w t ∘ coord) z) =
      deriv (fun s ↦ w s (coord z)) t - (a t (coord z) * deriv (deriv (w t)) (coord z) +
        b t (coord z) * deriv (w t) (coord z) + c t (coord z) * w t (coord z)) := by
    rw [sum_mul_fderiv_fderiv_add_fderiv_comp_coord]
    rfl
  have h := le_of_deriv_sub_sum_mul_fderiv_fderiv_add_fderiv_add_mul_le_of_le_initial
    (a := fun t z ↦ Matrix.of fun _ _ ↦ a t (coord z))
    (b := fun t z ↦ EuclideanSpace.single 0 (b t (coord z))) (c := fun t z ↦ c t (coord z))
    (u := fun t ↦ u t ∘ coord) (v := fun t ↦ v t ∘ coord) (Lam := Lam) (β := β)
    (fun t ht z ξ ↦ by
      simp only [Matrix.toQuadraticForm'_apply, dotProduct, Matrix.mulVec, Matrix.of_apply,
        Fin.sum_univ_one]
      nlinarith [ha ht (coord z), mul_self_nonneg (ξ 0)])
    (fun t ht z ↦ by simpa [Matrix.trace_fin_one, hnorm] using ha' ht (coord z))
    (fun t ht z ↦ by simpa [hnorm] using hb ht (coord z))
    (fun t ht z ↦ hc ht (coord z)) (hcont hucont) (hcont hvcont)
    (hbdd.mono <| by
      rintro _ ⟨⟨t, z⟩, hp, rfl⟩
      exact ⟨(t, coord z), ⟨hp.1, mem_univ _⟩, rfl⟩)
    (fun t ht z ↦ (hucd ht (coord z)).comp z coord.contDiff.contDiffAt)
    (fun t ht z ↦ (hvcd ht (coord z)).comp z coord.contDiff.contDiffAt)
    (fun t ht z ↦ hudiff ht (coord z)) (fun t ht z ↦ hvdiff ht (coord z))
    (fun t ht z ↦ by simpa only [hop] using hP ht (coord z))
    (fun z ↦ hinit (coord z))
  intro t ht x
  simpa using h ht (coord.symm x)

/-- **Uniqueness for the Cauchy problem on the whole line.** With `a`, `b`, `c` as in
`le_of_deriv_sub_mul_deriv_deriv_add_mul_deriv_add_mul_le_of_le_initial`, two functions that are
continuous on `[0, T] × ℝ` with bounded difference there, `C²` in space and differentiable in time
for `0 < t < T`, with `P u = P v` there and `u(·, 0) = v(·, 0)`, agree on `[0, T] × ℝ`. -/
theorem eq_of_deriv_sub_mul_deriv_deriv_add_mul_deriv_add_mul_eq_of_eq_initial
    (ha : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, 0 ≤ a t x)
    (ha' : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, a t x ≤ Lam * (1 + x ^ 2))
    (hb : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, |b t x| ≤ β * (1 + |x|))
    (hc : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, c t x ≤ γ)
    (hucont : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hvcont : ContinuousOn (Function.uncurry v) (Icc 0 T ×ˢ univ))
    (hbdd : Bornology.IsBounded (Function.uncurry (u - v) '' Icc 0 T ×ˢ univ))
    (hucd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, ContDiffAt ℝ 2 (u t) x)
    (hvcd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, ContDiffAt ℝ 2 (v t) x)
    (hudiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hvdiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, DifferentiableAt ℝ (fun s ↦ v s x) t)
    (hP : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, deriv (fun s ↦ u s x) t -
      (a t x * deriv (deriv (u t)) x + b t x * deriv (u t) x + c t x * u t x) =
      deriv (fun s ↦ v s x) t -
      (a t x * deriv (deriv (v t)) x + b t x * deriv (v t) x + c t x * v t x))
    (hinit : ∀ x, u 0 x = v 0 x) :
    ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ x, u t x = v t x := by
  rw [isBounded_iff_bddBelow_bddAbove] at hbdd
  -- The difference `v - u` is bounded above because `u - v` is bounded below.
  have hbdd' : BddAbove (Function.uncurry (v - u) '' Icc 0 T ×ˢ univ) := by
    obtain ⟨m, hm⟩ := hbdd.1
    refine ⟨-m, ?_⟩
    rintro _ ⟨⟨t, x⟩, hp, rfl⟩
    have h1 : m ≤ u t x - v t x := hm ⟨(t, x), hp, rfl⟩
    simp only [Function.uncurry_apply_pair, Pi.sub_apply]
    linarith
  intro t ht x
  exact le_antisymm
    (le_of_deriv_sub_mul_deriv_deriv_add_mul_deriv_add_mul_le_of_le_initial ha ha' hb hc hucont
      hvcont hbdd.2 hucd hvcd hudiff hvdiff (fun s hs y ↦ (hP hs y).le)
      (fun y ↦ (hinit y).le) ht x)
    (le_of_deriv_sub_mul_deriv_deriv_add_mul_deriv_add_mul_le_of_le_initial ha ha' hb hc hvcont
      hucont hbdd' hvcd hucd hvdiff hudiff (fun s hs y ↦ (hP hs y).ge)
      (fun y ↦ (hinit y).ge) ht x)

end PDE

end TauCeti

end
