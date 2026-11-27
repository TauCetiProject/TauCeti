/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Billiard.ConvexTable
public import TauCeti.Dynamics.Billiard.PeriodicPolygon
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Convex tables in Euclidean coordinates

This file transports a convex table `γ : ℝ → ℂ` along the linear isometry
`Complex.orthonormalBasisOneI.repr`, which sends `z` to its coordinates `(Re z, Im z)`, to the
curve `χ = (Re γ, Im γ)` in `EuclideanSpace ℝ (Fin 2)` (`TauCeti.ConvexTable.toEuclidean`), and
states the hypotheses of a strictly convex planar billiard curve in these coordinates: `χ` is of
the class of `γ`, `ℓ`-periodic, of unit speed and injective on every interval `[a, a + ℓ)`; it is
positively oriented, with the explicit cross product
`χ'₀(s) (χ₁(t) − χ₁(s)) − χ'₁(s) (χ₀(t) − χ₀(s)) > 0` for `t ≢ s`, this being the cross product
`τ(s) × (γ t − γ s)` of the table; and it meets each tangent line `{χ(s) + c χ'(s)}` only at
`χ(s)`. Applying `TauCeti.exists_billiard_periodic_reflection` to `χ`, every convex table has, for
every `N ≥ 2`, closed billiard trajectories with `N` bounces whose least period divides `N`
(`TauCeti.ConvexTable.exists_periodic_reflection`).

## Main declarations

* `TauCeti.ConvexTable.toEuclidean`: the table in Euclidean coordinates.
* `TauCeti.ConvexTable.contDiff_toEuclidean`, `periodic_toEuclidean`,
  `norm_deriv_toEuclidean`, `injOn_Ico_toEuclidean`, `cross_deriv_toEuclidean_pos`,
  `eq_of_toEuclidean_eq_add_smul_deriv`: the hypotheses of a strictly convex planar billiard
  curve, in Euclidean coordinates.
* `TauCeti.ConvexTable.exists_periodic_reflection`: periodic billiard trajectories.
* `TauCeti.ConvexTable.toEuclidean_circle`: the circle of radius `R` is
  `s ↦ (R cos (s / R), R sin (s / R))`.

## References

* M. Bialy and A. E. Mironov, *The Birkhoff–Poritsky conjecture for centrally-symmetric billiard
  tables*, Ann. of Math. 196 (2022), Section 2.
-/

public section

noncomputable section

open Function Set Complex
open scoped ComplexConjugate RealInnerProductSpace

namespace TauCeti

namespace ConvexTable

variable {k : ℕ∞} {ℓ : ℝ} [Fact (0 < ℓ)] (T : ConvexTable k ℓ)

/-- A convex table in Euclidean coordinates: `s ↦ (Re γ(s), Im γ(s))`, the image of the table under
the linear isometry `Complex.orthonormalBasisOneI.repr : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)`. -/
def toEuclidean (s : ℝ) : EuclideanSpace ℝ (Fin 2) := Complex.orthonormalBasisOneI.repr (T s)

theorem toEuclidean_apply (s : ℝ) :
    T.toEuclidean s = Complex.orthonormalBasisOneI.repr (T s) := (rfl)

@[simp]
theorem toEuclidean_apply_zero (s : ℝ) : T.toEuclidean s 0 = (T s).re := (rfl)

@[simp]
theorem toEuclidean_apply_one (s : ℝ) : T.toEuclidean s 1 = (T s).im := (rfl)

theorem contDiff_toEuclidean : ContDiff ℝ k T.toEuclidean :=
  Complex.orthonormalBasisOneI.repr.contDiff.comp T.contDiff

theorem periodic_toEuclidean : Periodic T.toEuclidean ℓ := fun s => by
  simp [toEuclidean_apply]

theorem hasDerivAt_toEuclidean (s : ℝ) :
    HasDerivAt T.toEuclidean (Complex.orthonormalBasisOneI.repr (deriv T s)) s :=
  Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv.hasFDerivAt.comp_hasDerivAt s
    (T.hasDerivAt s)

theorem deriv_toEuclidean (s : ℝ) :
    deriv T.toEuclidean s = Complex.orthonormalBasisOneI.repr (deriv T s) :=
  (T.hasDerivAt_toEuclidean s).deriv

/-- The table has unit speed in Euclidean coordinates. -/
@[simp]
theorem norm_deriv_toEuclidean (s : ℝ) : ‖deriv T.toEuclidean s‖ = 1 := by
  rw [deriv_toEuclidean, LinearIsometryEquiv.norm_map, norm_deriv]

theorem toEuclidean_eq_toEuclidean_iff {s t : ℝ} :
    T.toEuclidean s = T.toEuclidean t ↔ (s : AddCircle ℓ) = t := by
  rw [toEuclidean_apply, toEuclidean_apply, Complex.orthonormalBasisOneI.repr.injective.eq_iff,
    apply_eq_apply_iff]

/-- The table is injective on every interval `[a, a + ℓ)` in Euclidean coordinates. -/
theorem injOn_Ico_toEuclidean (a : ℝ) : InjOn T.toEuclidean (Ico a (a + ℓ)) := fun _ hs _ ht h =>
  T.injOn_Ico a hs ht (Complex.orthonormalBasisOneI.repr.injective h)

/-- **Positive orientation in Euclidean coordinates.** Every point `χ(t)` with `t ≢ s` lies
strictly to the left of the tangent line at `χ(s)`:
`χ'₀(s) (χ₁(t) − χ₁(s)) − χ'₁(s) (χ₀(t) − χ₀(s)) > 0`. -/
theorem cross_deriv_toEuclidean_pos {s t : ℝ} (h : (s : AddCircle ℓ) ≠ t) :
    0 < deriv T.toEuclidean s 0 * (T.toEuclidean t 1 - T.toEuclidean s 1) -
      deriv T.toEuclidean s 1 * (T.toEuclidean t 0 - T.toEuclidean s 0) := by
  have := T.im_conj_deriv_mul_sub_pos h
  simp only [mul_im, conj_re, conj_im, sub_re, sub_im] at this
  simp [deriv_toEuclidean, toEuclidean_apply]
  linarith

/-- **A table meets each tangent line only at the point of tangency**, in Euclidean
coordinates: if `χ(t) = χ(s) + c χ'(s)`, then `χ(t) = χ(s)`. -/
theorem eq_of_toEuclidean_eq_add_smul_deriv {s t c : ℝ}
    (h : T.toEuclidean t = T.toEuclidean s + c • deriv T.toEuclidean s) :
    T.toEuclidean t = T.toEuclidean s := by
  by_contra hne
  have hst : (s : AddCircle ℓ) ≠ t := fun h' => hne ((T.toEuclidean_eq_toEuclidean_iff).2 h'.symm)
  have := T.cross_deriv_toEuclidean_pos hst
  rw [h] at this
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, add_sub_cancel_left] at this
  linarith

/-- **Periodic billiard trajectories in a convex table.** For every `N ≥ 2` there are parameters
`s_k`, `k ∈ ℤ/N`, with consecutive points `γ(s_k) ≠ γ(s_(k+1))` and the equal-angle reflection law
`⟨u_(k−1), τ(s_k)⟩ = ⟨u_k, τ(s_k)⟩` at every vertex, where `u_k` is the unit vector from `γ(s_k)`
to `γ(s_(k+1))`. These are closed billiard trajectories with `N` bounces whose least period
divides `N`: for even `N` the polygon can be a double normal traversed `N / 2` times. This is
`TauCeti.exists_billiard_periodic_reflection` for `TauCeti.ConvexTable.toEuclidean`. -/
theorem exists_periodic_reflection {N : ℕ} (hN : 2 ≤ N) :
    ∃ s : ZMod N → ℝ, ∀ k, T.toEuclidean (s (k + 1)) ≠ T.toEuclidean (s k) ∧
      ⟪‖T.toEuclidean (s k) - T.toEuclidean (s (k - 1))‖⁻¹ •
          (T.toEuclidean (s k) - T.toEuclidean (s (k - 1))), deriv T.toEuclidean (s k)⟫ =
        ⟪‖T.toEuclidean (s (k + 1)) - T.toEuclidean (s k)‖⁻¹ •
          (T.toEuclidean (s (k + 1)) - T.toEuclidean (s k)), deriv T.toEuclidean (s k)⟫ :=
  exists_billiard_periodic_reflection T.periodic_toEuclidean (Fact.out : 0 < ℓ).ne'
    (fun t => norm_ne_zero_iff.1 (by simp)) hN

/-- The circle of radius `R` in Euclidean coordinates is `s ↦ (R cos (s / R), R sin (s / R))`. -/
theorem toEuclidean_circle (R : ℝ) [Fact (0 < 2 * Real.pi * R)] (s : ℝ) :
    (circle R).toEuclidean s = ![R * Real.cos (s / R), R * Real.sin (s / R)] := by
  ext i
  fin_cases i <;> simp [toEuclidean_apply, circleMap, -ofReal_div, exp_ofReal_mul_I_re,
    exp_ofReal_mul_I_im]

end ConvexTable

end TauCeti
