/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Linearization.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import TauCeti.Analysis.Sobolev.Cylinder.Morrey
import TauCeti.Analysis.Calculus.FDeriv.Remainder
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# The quadratic estimate for the Floer operator

Let `(V, ω)` be a finite-dimensional symplectic vector space, `J(z, y)` a domain-dependent family
of endomorphisms and `K = Ks ds + Kt dt` a domain-dependent Hamiltonian perturbation. The Floer
operator `F(u) = ∂s u - X_Ks(u) + J(u)(∂t u - X_Kt(u))` (`TauCeti.SymplecticForm.floerOperator`)
has linearization `D_w` at a map `w` (`TauCeti.SymplecticForm.floerLinearization`), and

`F(w + ξ) = F(w) + D_w ξ + N_w(ξ)`.

Gluing and transversality solve `F(w + ξ) = 0` near an approximate solution `w` by a Newton
iteration: with a right inverse `Q` of `D_w`, a solution is a fixed point of
`ξ ↦ -Q (F(w) + N_w(ξ))`. The iteration contracts once `N_w` is quadratically small in the sense
`‖N_w(ξ₁) - N_w(ξ₂)‖ ≲ (‖ξ₁‖ + ‖ξ₂‖) ‖ξ₁ - ξ₂‖`, which is the hypothesis of the abstract
theorem `TauCeti.exists_mem_range_norm_le_add_add_eq_zero`. This file proves the pointwise form of
that estimate, its `Lᵖ` form, and its `W^{1,p}` form on the cylinder for `p > 2`.

**The remainder depends only on first-order data.** The `∂s` terms of `F` are linear and cancel
from `N_w`, so at a domain point `z` the remainder is a function
`TauCeti.SymplecticForm.floerRemainder ω (J z) (Ks z) (Kt z) y v e d` of the coefficients frozen at
`z`, the value `y = w(z)` and slice velocity `v = ∂t w(z)` of the base map, and the value
`e = ξ(z)` and slice velocity `d = ∂t ξ(z)` of the increment
(`SymplecticForm.floerOperator_add_sub_floerOperator_sub_floerLinearization`). It vanishes for
`e = 0` (`TauCeti.SymplecticForm.floerRemainder_zero`). Being a function of values and slice
velocities, it also makes sense for increments with weak derivatives, and the estimates are
stated for it. The difference of two remainders splits into Taylor remainders of `X_Ks`, `J` and
`X_Kt` at `y`, and differences of `J` multiplied by first-order terms
(`TauCeti.SymplecticForm.floerRemainder_sub_floerRemainder`).

**The estimate.** Let the coefficients `J p`, `Ks p`, `Kt p` depend on a parameter `p` in a normed
space `P`. If `J` is jointly `C²` and `Ks`, `Kt` are jointly `C³` at the points of a compact set
`K` of pairs `(p, y)`, then there are `δ > 0` and `C` such that, whenever `(p, y) ∈ K` and
`‖e₁‖, ‖e₂‖ ≤ δ`,

`‖N(e₁, d₁) - N(e₂, d₂)‖ ≤ C (m (1 + ‖v - X_Kt(y)‖) ‖e₁ - e₂‖ + ‖e₁ - e₂‖ ‖d₁‖ + ‖e₂‖ ‖d₁ - d₂‖)`,

where `m = max ‖e₁‖ ‖e₂‖`
(`TauCeti.SymplecticForm.exists_pos_forall_norm_floerRemainder_sub_le`). Here `v - X_Kt(y)` is the
slice defect of the base map; for a Floer solution with `Ks = 0` and `J² = -1` it is `J ∂s w`.
For maps, and coefficients pulled back to the domain along any `φ : ℝ × ℝ → P`, this bounds
`F(w + ξ₁) - F(w + ξ₂) - D_w(ξ₁ - ξ₂)` at every point where `(φ z, w(z)) ∈ K`
(`exists_pos_forall_norm_floerOperator_sub_floerOperator_sub_floerLinearization_le`),
and for `ξ₂ = 0` it is the quadratic estimate
`‖F(w + ξ) - F(w) - D_w ξ‖ ≤ C (‖ξ‖² (1 + ‖∂t w - X_Kt(w)‖) + ‖ξ‖ ‖∂t ξ‖)`
(`exists_pos_forall_norm_floerOperator_add_sub_floerOperator_sub_floerLinearization_le`).
Taking `φ = id` gives domain-dependent coefficients over a compact part of the domain; taking
`φ z = z.2` gives `t`-dependent coefficients with constants uniform over a whole strip
`ℝ × [0, 1]`, as on the cylindrical ends used in gluing.

**The estimate in `Lᵖ`.** For `J` jointly `C¹` and `Ks`, `Kt` jointly `C²`, the remainder is
jointly continuous in all its arguments (`TauCeti.SymplecticForm.continuous_floerRemainder`), so
it is measurable along measurable fields. For `J` jointly `C²` and `Ks`, `Kt` jointly `C³` the
pointwise bound then integrates. If the increments
satisfy `‖e₁‖, ‖e₂‖ ≤ a ≤ δ` and `‖e₁ - e₂‖ ≤ b`, and the slice defect is at most `A`, almost
everywhere, then for `1 ≤ p`

`‖N(e₁, d₁) - N(e₂, d₂)‖_p ≤ C (a (1 + A) ‖e₁ - e₂‖_p + b ‖d₁‖_p + a ‖d₁ - d₂‖_p)`

on any measure space (`TauCeti.SymplecticForm.exists_pos_forall_eLpNorm_floerRemainder_sub_le`).
Here `e` and `d` are arbitrary measurable fields, such as a Sobolev map and its weak slice
derivative. For maps differentiable on a measurable subset of the domain this is the `Lᵖ` bound on
`F(w + ξ₁) - F(w + ξ₂) - D_w(ξ₁ - ξ₂)`
(`exists_pos_forall_eLpNorm_floerOperator_sub_floerOperator_sub_floerLinearization_le`), and
for `ξ₂ = 0` the `Lᵖ` quadratic estimate
(`exists_pos_forall_eLpNorm_floerOperator_add_sub_floerOperator_sub_floerLinearization_le`).
**The estimate in `W^{1,p}` on the cylinder.** For `p > 2`, Morrey's estimate on the cylinder
(`TauCeti.CylinderSobolev.exists_enorm_le_mul_eLpNorm_jet`) bounds the sup norm of a `C¹` map of
period one in `t` by the `Lᵖ` norm on the strip `ℝ × [0, 1]` of its jet `(ξ, ∂s ξ, ∂t ξ)`, which is
its `W^{1,p}` norm up to a constant. Bounding `a` and `b` this way, the `Lᵖ` estimate on the strip
becomes the `W^{1,p} → Lᵖ` estimate
`‖F(w + ξ₁) - F(w + ξ₂) - D_w(ξ₁ - ξ₂)‖_p ≤ C (1 + A) (‖jet ξ₁‖_p + ‖jet ξ₂‖_p) ‖jet (ξ₁ - ξ₂)‖_p`
for increments with `‖jet ξᵢ‖_p ≤ δ`
(`exists_pos_forall_eLpNorm_floerOperator_sub_floerOperator_sub_floerLinearization_le_jet`). This
is the hypothesis `‖N x - N y‖ ≤ (L / 2) (‖x‖ + ‖y‖) ‖x - y‖` of the Newton iteration, provided the
slice defect `A` of `w` is bounded on the strip.

The constants come from Taylor's theorem and the mean value inequality with uniform constants
over compact parameter sets (`IsCompact.exists_pos_forall_norm_sub_sub_fderiv_sub_le_mul`,
`IsCompact.exists_pos_forall_norm_sub_le_mul_norm_sub`). The domain is a coordinate patch
and the target a vector space. The `W^{1,p}` estimate is stated for `C¹` increments; no Sobolev
space of the cylinder for `p ≠ 2`, and no right inverse of `D_w` on it, is constructed here.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 3.5, on the quadratic estimate and the implicit function theorem, and Chapter 10, on
  gluing.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), on gluing Floer trajectories.
-/

public section

namespace TauCeti.SymplecticForm

open ContinuousLinearMap Metric

universe u

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable (ω : SymplecticForm V)

/-! ### The remainder as a function of first-order data -/

section Remainder

variable (J : V → V →L[ℝ] V) (Ks Kt : V → ℝ)

/-- The nonlinear remainder of the Floer operator with coefficients `J`, `Ks`, `Kt` frozen at a
domain point, as a function of the value `y` and slice velocity `v` of the base map and the value
`e` and slice velocity `d` of the increment: the pointwise Floer operator at `(y + e, v + d)`,
minus its value at `(y, v)`, minus the linearization at `y` applied to `(e, d)`. The `∂s` terms of
the operator are linear and do not appear. -/
noncomputable def floerRemainder (y v e d : V) : V :=
  (-ω.hamiltonianVectorField Ks (y + e) +
      J (y + e) (v + d - ω.hamiltonianVectorField Kt (y + e))) -
    (-ω.hamiltonianVectorField Ks y + J y (v - ω.hamiltonianVectorField Kt y)) -
    (-fderiv ℝ (ω.hamiltonianVectorField Ks) y e +
      fderiv ℝ J y e (v - ω.hamiltonianVectorField Kt y) +
      J y (d - fderiv ℝ (ω.hamiltonianVectorField Kt) y e))

/-- The coordinate expression of the remainder. -/
theorem floerRemainder_def (y v e d : V) :
    ω.floerRemainder J Ks Kt y v e d =
      (-ω.hamiltonianVectorField Ks (y + e) +
          J (y + e) (v + d - ω.hamiltonianVectorField Kt (y + e))) -
        (-ω.hamiltonianVectorField Ks y + J y (v - ω.hamiltonianVectorField Kt y)) -
        (-fderiv ℝ (ω.hamiltonianVectorField Ks) y e +
          fderiv ℝ J y e (v - ω.hamiltonianVectorField Kt y) +
          J y (d - fderiv ℝ (ω.hamiltonianVectorField Kt) y e)) :=
  (rfl)

/-- The remainder vanishes for the zero increment, whatever its slice velocity. -/
@[simp]
theorem floerRemainder_zero (y v d : V) :
    ω.floerRemainder J Ks Kt y v 0 d = 0 := by
  simp only [floerRemainder_def, add_zero, map_zero, zero_apply, sub_zero, map_add, map_sub]
  abel

/-- **The remainder of the Floer operator depends only on first-order data.** For maps `w` and
`ξ` differentiable at `z`, `F(w + ξ) - F(w) - D_w ξ` at `z` is the remainder, with the
coefficients frozen at `z`, at the values and slice velocities `∂t w(z)`, `∂t ξ(z)` of `w`
and `ξ`. -/
theorem floerOperator_add_sub_floerOperator_sub_floerLinearization
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (w ξ : ℝ × ℝ → V) {z : ℝ × ℝ}
    (hw : DifferentiableAt ℝ w z) (hξ : DifferentiableAt ℝ ξ z) :
    ω.floerOperator J Ks Kt (w + ξ) z - ω.floerOperator J Ks Kt w z -
        ω.floerLinearization J Ks Kt w ξ z =
      ω.floerRemainder (J z) (Ks z) (Kt z) (w z) (fderiv ℝ w z stdComplexLineImag) (ξ z)
        (fderiv ℝ ξ z stdComplexLineImag) := by
  simp only [floerOperator_def, floerLinearization_def, floerRemainder_def, fderiv_add hw hξ,
    add_apply, Pi.add_apply]
  abel

/-- **The difference of two remainders.** At a base point `y` with slice velocity `v`, the
difference of the remainders at `(e₁, d₁)` and `(e₂, d₂)` is the sum of

* minus the Taylor remainder of `X_Ks`, plus the Taylor remainder of `J` (applied to the slice
  defect `v - X_Kt(y)`), and minus `J(y)` applied to the Taylor remainder of `X_Kt`, all between
  `y + e₂` and `y + e₁`;
* `J(y + e₁) - J(y + e₂)` applied to `d₁ - (X_Kt(y + e₁) - X_Kt(y))`;
* `J(y + e₂) - J(y)` applied to `d₁ - d₂ - (X_Kt(y + e₁) - X_Kt(y + e₂))`.

Each of these is quadratically small in the increments and their slice velocities. -/
theorem floerRemainder_sub_floerRemainder (y v e₁ e₂ d₁ d₂ : V) :
    ω.floerRemainder J Ks Kt y v e₁ d₁ - ω.floerRemainder J Ks Kt y v e₂ d₂ =
      -(ω.hamiltonianVectorField Ks (y + e₁) - ω.hamiltonianVectorField Ks (y + e₂) -
          fderiv ℝ (ω.hamiltonianVectorField Ks) y (e₁ - e₂)) +
        (J (y + e₁) - J (y + e₂) - fderiv ℝ J y (e₁ - e₂))
          (v - ω.hamiltonianVectorField Kt y) +
        (J (y + e₁) - J (y + e₂))
          (d₁ - (ω.hamiltonianVectorField Kt (y + e₁) - ω.hamiltonianVectorField Kt y)) +
        (J (y + e₂) - J y)
          (d₁ - d₂ - (ω.hamiltonianVectorField Kt (y + e₁) -
            ω.hamiltonianVectorField Kt (y + e₂))) -
        J y (ω.hamiltonianVectorField Kt (y + e₁) -
          ω.hamiltonianVectorField Kt (y + e₂) -
            fderiv ℝ (ω.hamiltonianVectorField Kt) y (e₁ - e₂)) := by
  simp only [floerRemainder_def, sub_apply, map_sub, map_add]
  abel

/-! ### The quadratic estimate -/

/-- The quadratic estimate at one base point, from explicit bounds on the Taylor remainders and
increments of the coefficients. -/
private theorem norm_floerRemainder_sub_le_of_bounds {y v e₁ e₂ d₁ d₂ : V}
    {L Λ M : ℝ} (hL : 0 ≤ L) (hΛ : 0 ≤ Λ) (hM : ‖J y‖ ≤ M)
    (hs : ‖ω.hamiltonianVectorField Ks (y + e₁) - ω.hamiltonianVectorField Ks (y + e₂) -
      fderiv ℝ (ω.hamiltonianVectorField Ks) y (e₁ - e₂)‖ ≤
        L * max ‖e₁‖ ‖e₂‖ * ‖e₁ - e₂‖)
    (hj : ‖J (y + e₁) - J (y + e₂) - fderiv ℝ J y (e₁ - e₂)‖ ≤
      L * max ‖e₁‖ ‖e₂‖ * ‖e₁ - e₂‖)
    (ht : ‖ω.hamiltonianVectorField Kt (y + e₁) - ω.hamiltonianVectorField Kt (y + e₂) -
      fderiv ℝ (ω.hamiltonianVectorField Kt) y (e₁ - e₂)‖ ≤
        L * max ‖e₁‖ ‖e₂‖ * ‖e₁ - e₂‖)
    (hJ₁₂ : ‖J (y + e₁) - J (y + e₂)‖ ≤ Λ * ‖e₁ - e₂‖)
    (hJ₂ : ‖J (y + e₂) - J y‖ ≤ Λ * ‖e₂‖)
    (hX₁ : ‖ω.hamiltonianVectorField Kt (y + e₁) - ω.hamiltonianVectorField Kt y‖ ≤
      Λ * ‖e₁‖)
    (hX₁₂ : ‖ω.hamiltonianVectorField Kt (y + e₁) -
      ω.hamiltonianVectorField Kt (y + e₂)‖ ≤ Λ * ‖e₁ - e₂‖) :
    ‖ω.floerRemainder J Ks Kt y v e₁ d₁ - ω.floerRemainder J Ks Kt y v e₂ d₂‖ ≤
      (L * (1 + M) + 2 * Λ ^ 2 + Λ) *
        (max ‖e₁‖ ‖e₂‖ * (1 + ‖v - ω.hamiltonianVectorField Kt y‖) * ‖e₁ - e₂‖ +
          ‖e₁ - e₂‖ * ‖d₁‖ + ‖e₂‖ * ‖d₁ - d₂‖) := by
  set m := max ‖e₁‖ ‖e₂‖
  set a := ‖v - ω.hamiltonianVectorField Kt y‖
  set δe := ‖e₁ - e₂‖
  have hm₁ : ‖e₁‖ ≤ m := le_max_left _ _
  have hm₂ : ‖e₂‖ ≤ m := le_max_right _ _
  have hmd : 0 ≤ m * δe := mul_nonneg ((norm_nonneg _).trans hm₁) (norm_nonneg _)
  have ha : 0 ≤ a := norm_nonneg _
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  -- Bound the five terms of `floerRemainder_sub_floerRemainder` one by one.
  have h₂ : ‖(J (y + e₁) - J (y + e₂) - fderiv ℝ J y (e₁ - e₂))
      (v - ω.hamiltonianVectorField Kt y)‖ ≤ L * (m * δe) * a :=
    (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (by linarith) ha)
  have h₃ : ‖(J (y + e₁) - J (y + e₂))
      (d₁ - (ω.hamiltonianVectorField Kt (y + e₁) - ω.hamiltonianVectorField Kt y))‖ ≤
        Λ * δe * (‖d₁‖ + Λ * m) := by
    refine (le_opNorm _ _).trans (mul_le_mul hJ₁₂ ((norm_sub_le _ _).trans ?_) (norm_nonneg _)
      (mul_nonneg hΛ (norm_nonneg _)))
    nlinarith
  have h₄ : ‖(J (y + e₂) - J y)
      (d₁ - d₂ - (ω.hamiltonianVectorField Kt (y + e₁) -
        ω.hamiltonianVectorField Kt (y + e₂)))‖ ≤ Λ * ‖e₂‖ * (‖d₁ - d₂‖ + Λ * δe) :=
    (le_opNorm _ _).trans (mul_le_mul hJ₂ ((norm_sub_le _ _).trans (by linarith))
      (norm_nonneg _) (mul_nonneg hΛ (norm_nonneg _)))
  have h₅ : ‖J y (ω.hamiltonianVectorField Kt (y + e₁) -
      ω.hamiltonianVectorField Kt (y + e₂) -
        fderiv ℝ (ω.hamiltonianVectorField Kt) y (e₁ - e₂))‖ ≤ M * (L * (m * δe)) :=
    (le_opNorm _ _).trans (mul_le_mul hM (by linarith) (norm_nonneg _) hM0)
  rw [floerRemainder_sub_floerRemainder]
  have h₁ : ‖-(ω.hamiltonianVectorField Ks (y + e₁) -
      ω.hamiltonianVectorField Ks (y + e₂) -
        fderiv ℝ (ω.hamiltonianVectorField Ks) y (e₁ - e₂))‖ ≤ L * (m * δe) := by
    rw [norm_neg, ← mul_assoc]
    exact hs
  -- Compare each term with its piece of the target, using `‖e₂‖ ≤ m` and `0 ≤ a`.
  have hX : m * δe ≤ m * (1 + a) * δe := by nlinarith [mul_nonneg hmd ha]
  have he₂X : ‖e₂‖ * δe ≤ m * (1 + a) * δe :=
    (mul_le_mul_of_nonneg_right hm₂ (norm_nonneg _)).trans hX
  have hpos : 0 ≤ Λ * (m * (1 + a) * δe) +
      (L * (1 + M) + 2 * Λ ^ 2) * (δe * ‖d₁‖ + ‖e₂‖ * ‖d₁ - d₂‖) :=
    add_nonneg (mul_nonneg hΛ (hmd.trans hX))
      (mul_nonneg (by positivity) (by positivity))
  calc _ ≤ L * (m * δe) + L * (m * δe) * a + Λ * δe * (‖d₁‖ + Λ * m) +
        Λ * ‖e₂‖ * (‖d₁ - d₂‖ + Λ * δe) + M * (L * (m * δe)) :=
      norm_sub_le_of_le (norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le h₁ h₂) h₃) h₄) h₅
    _ = L * (m * (1 + a) * δe) + M * L * (m * δe) + Λ * (δe * ‖d₁‖) + Λ ^ 2 * (m * δe) +
        Λ * (‖e₂‖ * ‖d₁ - d₂‖) + Λ ^ 2 * (‖e₂‖ * δe) := by ring
    _ ≤ L * (m * (1 + a) * δe) + M * L * (m * (1 + a) * δe) + Λ * (δe * ‖d₁‖) +
        Λ ^ 2 * (m * (1 + a) * δe) + Λ * (‖e₂‖ * ‖d₁ - d₂‖) + Λ ^ 2 * (m * (1 + a) * δe) := by
      gcongr
    _ ≤ (L * (1 + M) + 2 * Λ ^ 2 + Λ) * (m * (1 + a) * δe + δe * ‖d₁‖ + ‖e₂‖ * ‖d₁ - d₂‖) := by
      linear_combination hpos

end Remainder

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable {J : P → V → V →L[ℝ] V} {Ks Kt : P → V → ℝ} {K : Set (P × V)}

/-- **The quadratic estimate for the Floer remainder.** Let the coefficients depend on a parameter
`p`, and let `K` be a compact set of pairs `(p, y)` of a parameter and a target point at which `J`
is jointly `C²` and the Hamiltonians `Ks`, `Kt` are jointly `C³`. There are `δ > 0` and `C` such
that for every `(p, y) ∈ K`, every slice velocity `v` and all increments `e₁`, `e₂` of norm at
most `δ` with slice velocities `d₁`, `d₂`, the remainders with coefficients `J p`, `Ks p`, `Kt p`
differ by at most
`C (max ‖e₁‖ ‖e₂‖ (1 + ‖v - X_Kt(y)‖) ‖e₁ - e₂‖ + ‖e₁ - e₂‖ ‖d₁‖ + ‖e₂‖ ‖d₁ - d₂‖)`. -/
theorem exists_pos_forall_norm_floerRemainder_sub_le (hK : IsCompact K)
    (hJ : ∀ q ∈ K, ContDiffAt ℝ 2 (Function.uncurry J) q)
    (hKs : ∀ q ∈ K, ContDiffAt ℝ 3 (Function.uncurry Ks) q)
    (hKt : ∀ q ∈ K, ContDiffAt ℝ 3 (Function.uncurry Kt) q) :
    ∃ δ > 0, ∃ C, ∀ p y, (p, y) ∈ K → ∀ v e₁ e₂ d₁ d₂ : V, ‖e₁‖ ≤ δ → ‖e₂‖ ≤ δ →
      ‖ω.floerRemainder (J p) (Ks p) (Kt p) y v e₁ d₁ -
          ω.floerRemainder (J p) (Ks p) (Kt p) y v e₂ d₂‖ ≤
        C * (max ‖e₁‖ ‖e₂‖ * (1 + ‖v - ω.hamiltonianVectorField (Kt p) y‖) * ‖e₁ - e₂‖ +
          ‖e₁ - e₂‖ * ‖d₁‖ + ‖e₂‖ * ‖d₁ - d₂‖) := by
  -- The coefficients as families over the pairs `q = (p, y)`, based at `y`.
  have hsnd : ContinuousOn (fun q : P × V ↦ q.2) K := continuous_snd.continuousOn
  have hFJ : ∀ q ∈ K,
      ContDiffAt ℝ 2 (Function.uncurry fun (q : P × V) (y : V) ↦ J q.1 y) (q, q.2) :=
    fun q hq ↦ (hJ q hq).comp (q, q.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  have hFS : ∀ q ∈ K, ContDiffAt ℝ 2 (Function.uncurry fun (q : P × V) (y : V) ↦
      ω.hamiltonianVectorField (Ks q.1) y) (q, q.2) :=
    fun q hq ↦ (ω.contDiffAt_hamiltonianVectorField_uncurry (n := 2) (hKs q hq)).comp (q, q.2)
      (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  have hFT : ∀ q ∈ K, ContDiffAt ℝ 2 (Function.uncurry fun (q : P × V) (y : V) ↦
      ω.hamiltonianVectorField (Kt q.1) y) (q, q.2) :=
    fun q hq ↦ (ω.contDiffAt_hamiltonianVectorField_uncurry (n := 2) (hKt q hq)).comp (q, q.2)
      (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  obtain ⟨δJ, hδJ, LJ, hLJ⟩ := hK.exists_pos_forall_norm_sub_sub_fderiv_sub_le_mul hFJ hsnd
  obtain ⟨δS, hδS, LS, hLS⟩ := hK.exists_pos_forall_norm_sub_sub_fderiv_sub_le_mul hFS hsnd
  obtain ⟨δT, hδT, LT, hLT⟩ := hK.exists_pos_forall_norm_sub_sub_fderiv_sub_le_mul hFT hsnd
  obtain ⟨δJ', hδJ', ΛJ, hΛJ⟩ := hK.exists_pos_forall_norm_sub_le_mul_norm_sub
    (fun q hq ↦ (hFJ q hq).of_le (by norm_num)) hsnd
  obtain ⟨δT', hδT', ΛT, hΛT⟩ := hK.exists_pos_forall_norm_sub_le_mul_norm_sub
    (fun q hq ↦ (hFT q hq).of_le (by norm_num)) hsnd
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (continuousOn_of_forall_continuousAt fun q hq ↦ (hJ q hq).continuousAt)
  -- Common radius and constants for the three Taylor remainders and the two Lipschitz bounds.
  set δ := min (min δJ (min δS δT)) (min δJ' δT')
  set L := max (max LJ LS) (max LT 0)
  set Λ := max (max ΛJ ΛT) 0
  have hδ : 0 < δ := lt_min (lt_min hδJ (lt_min hδS hδT)) (lt_min hδJ' hδT')
  have hL : 0 ≤ L := le_max_of_le_right (le_max_right _ _)
  have hΛ : 0 ≤ Λ := le_max_right _ _
  refine ⟨δ, hδ, L * (1 + M) + 2 * Λ ^ 2 + Λ, fun p y hpy v e₁ e₂ d₁ d₂ he₁ he₂ => ?_⟩
  have h₁ : ‖e₁‖ ≤ δ := he₁
  have h₂ : ‖e₂‖ ≤ δ := he₂
  have h0 : ‖(0 : V)‖ ≤ δ := by simpa using hδ.le
  have hδJ₁ : δ ≤ δJ := (min_le_left _ _).trans (min_le_left _ _)
  have hδS₁ : δ ≤ δS := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδT₁ : δ ≤ δT := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδJ₂ : δ ≤ δJ' := (min_le_right _ _).trans (min_le_left _ _)
  have hδT₂ : δ ≤ δT' := (min_le_right _ _).trans (min_le_right _ _)
  have hr : 0 ≤ max ‖e₁‖ ‖e₂‖ * ‖e₁ - e₂‖ :=
    mul_nonneg ((norm_nonneg _).trans (le_max_left _ _)) (norm_nonneg _)
  -- Raise each constant to the common one.
  have hquad {N L₀ : ℝ} (hL₀ : L₀ ≤ L) (hN : N ≤ L₀ * max ‖e₁‖ ‖e₂‖ * ‖e₁ - e₂‖) :
      N ≤ L * max ‖e₁‖ ‖e₂‖ * ‖e₁ - e₂‖ := by
    rw [mul_assoc] at hN ⊢
    exact hN.trans (mul_le_mul_of_nonneg_right hL₀ hr)
  have hlip {N Λ₀ r : ℝ} (hΛ₀ : Λ₀ ≤ Λ) (hr : 0 ≤ r) (hN : N ≤ Λ₀ * r) : N ≤ Λ * r :=
    hN.trans (mul_le_mul_of_nonneg_right hΛ₀ hr)
  have hΛJ₀ : ΛJ ≤ Λ := (le_max_left _ _).trans (le_max_left _ _)
  have hΛT₀ : ΛT ≤ Λ := (le_max_right _ _).trans (le_max_left _ _)
  refine norm_floerRemainder_sub_le_of_bounds ω (J p) (Ks p) (Kt p) hL hΛ (hM (p, y) hpy)
    (hquad ((le_max_right _ _).trans (le_max_left _ _))
      (hLS (p, y) hpy e₁ e₂ (h₁.trans hδS₁) (h₂.trans hδS₁)))
    (hquad ((le_max_left _ _).trans (le_max_left _ _))
      (hLJ (p, y) hpy e₁ e₂ (h₁.trans hδJ₁) (h₂.trans hδJ₁)))
    (hquad ((le_max_left _ _).trans (le_max_right _ _))
      (hLT (p, y) hpy e₁ e₂ (h₁.trans hδT₁) (h₂.trans hδT₁)))
    (hlip hΛJ₀ (norm_nonneg _) (hΛJ (p, y) hpy e₁ e₂ (h₁.trans hδJ₂) (h₂.trans hδJ₂)))
    (hlip hΛJ₀ (norm_nonneg _) (by
      simpa using hΛJ (p, y) hpy e₂ 0 (h₂.trans hδJ₂) (h0.trans hδJ₂)))
    (hlip hΛT₀ (norm_nonneg _) (by
      simpa using hΛT (p, y) hpy e₁ 0 (h₁.trans hδT₂) (h0.trans hδT₂)))
    (hlip hΛT₀ (norm_nonneg _) (hΛT (p, y) hpy e₁ e₂ (h₁.trans hδT₂) (h₂.trans hδT₂)))

/-- **The quadratic estimate for the Floer operator.** Let `K` be a compact set of pairs `(p, y)`
of a parameter and a target point at which `J` is jointly `C²` and the Hamiltonians `Ks`, `Kt`
are jointly `C³`. There are `δ > 0` and `C` such that for every parameter map `φ : ℝ × ℝ → P` and
maps `w`, `ξ₁`, `ξ₂` differentiable at a domain point `z` with `(φ z, w z) ∈ K` and
`‖ξ₁ z‖, ‖ξ₂ z‖ ≤ δ`, the Floer operator with coefficients `J (φ z)`, `Ks (φ z)`, `Kt (φ z)`
satisfies
`‖F(w + ξ₁) - F(w + ξ₂) - D_w(ξ₁ - ξ₂)‖ ≤ C (max ‖ξ₁‖ ‖ξ₂‖ (1 + ‖∂t w - X_Kt(w)‖) ‖ξ₁ - ξ₂‖
  + ‖ξ₁ - ξ₂‖ ‖∂t ξ₁‖ + ‖ξ₂‖ ‖∂t ξ₁ - ∂t ξ₂‖)` at `z`. This is the Lipschitz bound on the
nonlinear part of the Floer operator used by the Newton iteration. -/
theorem exists_pos_forall_norm_floerOperator_sub_floerOperator_sub_floerLinearization_le
    (hK : IsCompact K) (hJ : ∀ q ∈ K, ContDiffAt ℝ 2 (Function.uncurry J) q)
    (hKs : ∀ q ∈ K, ContDiffAt ℝ 3 (Function.uncurry Ks) q)
    (hKt : ∀ q ∈ K, ContDiffAt ℝ 3 (Function.uncurry Kt) q) :
    ∃ δ > 0, ∃ C, ∀ (φ : ℝ × ℝ → P) (w ξ₁ ξ₂ : ℝ × ℝ → V) (z : ℝ × ℝ),
      DifferentiableAt ℝ w z → DifferentiableAt ℝ ξ₁ z → DifferentiableAt ℝ ξ₂ z →
      (φ z, w z) ∈ K → ‖ξ₁ z‖ ≤ δ → ‖ξ₂ z‖ ≤ δ →
      ‖ω.floerOperator (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) (w + ξ₁) z -
          ω.floerOperator (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) (w + ξ₂) z -
          ω.floerLinearization (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) w
            (ξ₁ - ξ₂) z‖ ≤
        C * (max ‖ξ₁ z‖ ‖ξ₂ z‖ *
            (1 + ‖fderiv ℝ w z stdComplexLineImag - ω.hamiltonianVectorField (Kt (φ z)) (w z)‖) *
            ‖ξ₁ z - ξ₂ z‖ +
          ‖ξ₁ z - ξ₂ z‖ * ‖fderiv ℝ ξ₁ z stdComplexLineImag‖ +
          ‖ξ₂ z‖ * ‖fderiv ℝ ξ₁ z stdComplexLineImag - fderiv ℝ ξ₂ z stdComplexLineImag‖) := by
  obtain ⟨δ, hδ, C, hC⟩ := ω.exists_pos_forall_norm_floerRemainder_sub_le hK hJ hKs hKt
  refine ⟨δ, hδ, C, fun φ w ξ₁ ξ₂ z hw hξ₁ hξ₂ hzw hξ₁δ hξ₂δ => ?_⟩
  have h₁ := ω.floerOperator_add_sub_floerOperator_sub_floerLinearization
    (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) w ξ₁ hw hξ₁
  have h₂ := ω.floerOperator_add_sub_floerOperator_sub_floerLinearization
    (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) w ξ₂ hw hξ₂
  rw [floerLinearization_sub ω _ _ _ w ξ₁ ξ₂ z hξ₁ hξ₂]
  convert hC (φ z) (w z) hzw _ (ξ₁ z) (ξ₂ z) _ _ hξ₁δ hξ₂δ using 2
  rw [← h₁, ← h₂]
  abel

/-- **The quadratic estimate for the Floer operator at a map.** Let `K` be a compact set of pairs
`(p, y)` of a parameter and a target point at which `J` is jointly `C²` and the Hamiltonians `Ks`,
`Kt` are jointly `C³`. There are `δ > 0` and `C` such that for every parameter map
`φ : ℝ × ℝ → P` and maps `w`, `ξ` differentiable at a domain point `z` with `(φ z, w z) ∈ K` and
`‖ξ z‖ ≤ δ`, the Floer operator with coefficients `J (φ z)`, `Ks (φ z)`, `Kt (φ z)` satisfies
`‖F(w + ξ) - F(w) - D_w ξ‖ ≤ C (‖ξ‖² (1 + ‖∂t w - X_Kt(w)‖) + ‖ξ‖ ‖∂t ξ‖)` at `z`. -/
theorem exists_pos_forall_norm_floerOperator_add_sub_floerOperator_sub_floerLinearization_le
    (hK : IsCompact K) (hJ : ∀ q ∈ K, ContDiffAt ℝ 2 (Function.uncurry J) q)
    (hKs : ∀ q ∈ K, ContDiffAt ℝ 3 (Function.uncurry Ks) q)
    (hKt : ∀ q ∈ K, ContDiffAt ℝ 3 (Function.uncurry Kt) q) :
    ∃ δ > 0, ∃ C, ∀ (φ : ℝ × ℝ → P) (w ξ : ℝ × ℝ → V) (z : ℝ × ℝ), DifferentiableAt ℝ w z →
      DifferentiableAt ℝ ξ z → (φ z, w z) ∈ K → ‖ξ z‖ ≤ δ →
      ‖ω.floerOperator (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) (w + ξ) z -
          ω.floerOperator (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) w z -
          ω.floerLinearization (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) w ξ z‖ ≤
        C * (‖ξ z‖ ^ 2 *
            (1 + ‖fderiv ℝ w z stdComplexLineImag - ω.hamiltonianVectorField (Kt (φ z)) (w z)‖) +
          ‖ξ z‖ * ‖fderiv ℝ ξ z stdComplexLineImag‖) := by
  obtain ⟨δ, hδ, C, hC⟩ := ω.exists_pos_forall_norm_floerRemainder_sub_le hK hJ hKs hKt
  refine ⟨δ, hδ, C, fun φ w ξ z hw hξ hzw hξδ => ?_⟩
  have h := hC (φ z) (w z) hzw (fderiv ℝ w z stdComplexLineImag) (ξ z) 0
    (fderiv ℝ ξ z stdComplexLineImag) 0 hξδ (by simpa using hδ.le)
  rw [floerRemainder_zero, sub_zero] at h
  rw [ω.floerOperator_add_sub_floerOperator_sub_floerLinearization
    (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) w ξ hw hξ]
  convert h using 2
  simp only [norm_zero, max_eq_left (norm_nonneg _), sub_zero, zero_mul, add_zero]
  ring

/-! ### The quadratic estimate in `Lᵖ` -/

section Lp

open MeasureTheory
open scoped NNReal ENNReal

/-- **Continuity of the remainder.** If `J` is jointly `C¹` and the Hamiltonians `Ks`, `Kt` are
jointly `C²` in the parameter and the target point, then the remainder with coefficients
`J p`, `Ks p`, `Kt p` is jointly continuous in `p`, the base point and slice velocity, and the
increment and its slice velocity. -/
theorem continuous_floerRemainder (hJ : ContDiff ℝ 1 (Function.uncurry J))
    (hKs : ContDiff ℝ 2 (Function.uncurry Ks)) (hKt : ContDiff ℝ 2 (Function.uncurry Kt)) :
    Continuous fun q : P × V × V × V × V ↦
      ω.floerRemainder (J q.1) (Ks q.1) (Kt q.1) q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 := by
  -- The coefficients and their target derivatives are jointly continuous.
  have hS := ω.contDiff_hamiltonianVectorField_uncurry (n := 1) hKs
  have hT := ω.contDiff_hamiltonianVectorField_uncurry (n := 1) hKt
  have hpair : ContDiff ℝ 1 fun w : (P × V) × V ↦ (w.1.1, w.2) :=
    contDiff_fst.fst.prodMk contDiff_snd
  have hdS : Continuous fun w : P × V ↦ fderiv ℝ (ω.hamiltonianVectorField (Ks w.1)) w.2 :=
    Continuous.fderiv_one (hS.comp hpair) continuous_snd
  have hdT : Continuous fun w : P × V ↦ fderiv ℝ (ω.hamiltonianVectorField (Kt w.1)) w.2 :=
    Continuous.fderiv_one (hT.comp hpair) continuous_snd
  have hdJ : Continuous fun w : P × V ↦ fderiv ℝ (J w.1) w.2 :=
    Continuous.fderiv_one (hJ.comp hpair) continuous_snd
  have hp : Continuous fun q : P × V × V × V × V ↦ q.1 := continuous_fst
  have hy : Continuous fun q : P × V × V × V × V ↦ q.2.1 := continuous_snd.fst
  have hv : Continuous fun q : P × V × V × V × V ↦ q.2.2.1 := continuous_snd.snd.fst
  have he : Continuous fun q : P × V × V × V × V ↦ q.2.2.2.1 := continuous_snd.snd.snd.fst
  have hd : Continuous fun q : P × V × V × V × V ↦ q.2.2.2.2 := continuous_snd.snd.snd.snd
  -- Evaluate each coefficient along the parameter and the target points `y` and `y + e`.
  have hye := hy.add he
  have hSy := hS.continuous.comp (hp.prodMk hy)
  have hSye := hS.continuous.comp (hp.prodMk hye)
  have hTy := hT.continuous.comp (hp.prodMk hy)
  have hTye := hT.continuous.comp (hp.prodMk hye)
  have hJy := hJ.continuous.comp (hp.prodMk hy)
  have hJye := hJ.continuous.comp (hp.prodMk hye)
  have hdSy := hdS.comp (hp.prodMk hy)
  have hdTy := hdT.comp (hp.prodMk hy)
  have hdJy := hdJ.comp (hp.prodMk hy)
  simp only [floerRemainder_def]
  exact ((hSye.neg.add (hJye.clm_apply ((hv.add hd).sub hTye))).sub
      (hSy.neg.add (hJy.clm_apply (hv.sub hTy)))).sub
    (((hdSy.clm_apply he).neg.add ((hdJy.clm_apply he).clm_apply (hv.sub hTy))).add
      (hJy.clm_apply (hd.sub (hdTy.clm_apply he))))

/-- The pointwise quadratic estimate, with the norms of the increments, the norm of their
difference and the slice defect bounded by constants. -/
private theorem norm_floerRemainder_sub_le_of_le {j : V → V →L[ℝ] V} {ks kt : V → ℝ}
    {y v e₁ e₂ d₁ d₂ : V} {C a A b : ℝ}
    (hC : ‖ω.floerRemainder j ks kt y v e₁ d₁ - ω.floerRemainder j ks kt y v e₂ d₂‖ ≤
      C * (max ‖e₁‖ ‖e₂‖ * (1 + ‖v - ω.hamiltonianVectorField kt y‖) * ‖e₁ - e₂‖ +
        ‖e₁ - e₂‖ * ‖d₁‖ + ‖e₂‖ * ‖d₁ - d₂‖))
    (h₁ : ‖e₁‖ ≤ a) (h₂ : ‖e₂‖ ≤ a) (hb : ‖e₁ - e₂‖ ≤ b)
    (hA : ‖v - ω.hamiltonianVectorField kt y‖ ≤ A) :
    ‖ω.floerRemainder j ks kt y v e₁ d₁ - ω.floerRemainder j ks kt y v e₂ d₂‖ ≤
      max C 0 * (a * (1 + A) * ‖e₁ - e₂‖ + b * ‖d₁‖ + a * ‖d₁ - d₂‖) := by
  have hS : max ‖e₁‖ ‖e₂‖ * (1 + ‖v - ω.hamiltonianVectorField kt y‖) * ‖e₁ - e₂‖ +
      ‖e₁ - e₂‖ * ‖d₁‖ + ‖e₂‖ * ‖d₁ - d₂‖ ≤ a * (1 + A) * ‖e₁ - e₂‖ + b * ‖d₁‖ + a * ‖d₁ - d₂‖ := by
    have ha0 : 0 ≤ a := (norm_nonneg _).trans h₁
    gcongr
    exact max_le h₁ h₂
  exact hC.trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans
    (mul_le_mul_of_nonneg_left hS (le_max_right _ _)))

/-- **The quadratic estimate for the Floer remainder in `Lᵖ`.** Let `J` be jointly `C²` and the
Hamiltonians `Ks`, `Kt` jointly `C³` in the parameter and the target point, and let `K` be a
compact set of pairs `(p, y)`. There are `δ > 0` and `C` with the following property. Let
`φ`, `y`, `v`, `e₁`, `e₂`, `d₁`, `d₂` be almost everywhere strongly measurable fields of
parameters, base points, base slice velocities, increments and their slice velocities on a measure
space, with `(φ, y) ∈ K`, `‖e₁‖, ‖e₂‖ ≤ a ≤ δ`, `‖e₁ - e₂‖ ≤ b` and slice defect
`‖v - X_Kt(y)‖ ≤ A` almost everywhere. Then for `1 ≤ p` the `Lᵖ` norm of the difference of the
remainders `N(e₁, d₁) - N(e₂, d₂)` is at most
`C (a (1 + A) ‖e₁ - e₂‖_p + b ‖d₁‖_p + a ‖d₁ - d₂‖_p)`.

The fields need not be derivatives: the increments may be Sobolev maps with their weak slice
derivatives. When `a` and `b` are sup norms dominated by a `W^{1,p}` norm, as for `p > 2` on a
two-dimensional domain, this is the hypothesis `‖N x - N y‖ ≤ (L / 2) (‖x‖ + ‖y‖) ‖x - y‖` of
`TauCeti.exists_mem_range_norm_le_add_add_eq_zero`. -/
theorem exists_pos_forall_eLpNorm_floerRemainder_sub_le (hK : IsCompact K)
    (hJ : ContDiff ℝ 2 (Function.uncurry J)) (hKs : ContDiff ℝ 3 (Function.uncurry Ks))
    (hKt : ContDiff ℝ 3 (Function.uncurry Kt)) :
    ∃ δ > 0, ∃ C : ℝ≥0, ∀ {α : Type*} [MeasurableSpace α] (μ : Measure α) {p : ℝ≥0∞},
      1 ≤ p → ∀ {φ : α → P} {y v e₁ e₂ d₁ d₂ : α → V} {a A b : ℝ},
      AEStronglyMeasurable φ μ → AEStronglyMeasurable y μ → AEStronglyMeasurable v μ →
      AEStronglyMeasurable e₁ μ → AEStronglyMeasurable e₂ μ → AEStronglyMeasurable d₁ μ →
      AEStronglyMeasurable d₂ μ → (∀ᵐ x ∂μ, (φ x, y x) ∈ K) → a ≤ δ →
      (∀ᵐ x ∂μ, ‖e₁ x‖ ≤ a) → (∀ᵐ x ∂μ, ‖e₂ x‖ ≤ a) → (∀ᵐ x ∂μ, ‖e₁ x - e₂ x‖ ≤ b) →
      (∀ᵐ x ∂μ, ‖v x - ω.hamiltonianVectorField (Kt (φ x)) (y x)‖ ≤ A) →
      eLpNorm (fun x ↦
          ω.floerRemainder (J (φ x)) (Ks (φ x)) (Kt (φ x)) (y x) (v x) (e₁ x) (d₁ x) -
            ω.floerRemainder (J (φ x)) (Ks (φ x)) (Kt (φ x)) (y x) (v x) (e₂ x) (d₂ x)) p μ ≤
        C * (ENNReal.ofReal (a * (1 + A)) * eLpNorm (e₁ - e₂) p μ +
          ENNReal.ofReal b * eLpNorm d₁ p μ + ENNReal.ofReal a * eLpNorm (d₁ - d₂) p μ) := by
  obtain ⟨δ, hδ, C, hC⟩ := ω.exists_pos_forall_norm_floerRemainder_sub_le hK
    (fun _ _ ↦ hJ.contDiffAt) (fun _ _ ↦ hKs.contDiffAt) (fun _ _ ↦ hKt.contDiffAt)
  refine ⟨δ, hδ, C.toNNReal, ?_⟩
  intro α _ μ p hp φ y v e₁ e₂ d₁ d₂ a A b hφ hy hv he₁ he₂ hd₁ hd₂ hK' haδ ha₁ ha₂ hb hA
  have hR := ω.continuous_floerRemainder (hJ.of_le (by norm_num)) (hKs.of_le (by norm_num))
    (hKt.of_le (by norm_num))
  have hm₁ := hR.comp_aestronglyMeasurable (hφ.prodMk (hy.prodMk (hv.prodMk (he₁.prodMk hd₁))))
  have hm₂ := hR.comp_aestronglyMeasurable (hφ.prodMk (hy.prodMk (hv.prodMk (he₂.prodMk hd₂))))
  -- The three terms of the bound, as real functions.
  set g₁ : α → ℝ := fun x ↦ a * (1 + A) * ‖e₁ x - e₂ x‖ with hg₁
  set g₂ : α → ℝ := fun x ↦ b * ‖d₁ x‖ with hg₂
  set g₃ : α → ℝ := fun x ↦ a * ‖d₁ x - d₂ x‖ with hg₃
  -- The constants are nonnegative wherever the bounds hold.
  have ha0 : ∀ᵐ _ ∂μ, 0 ≤ a := ha₁.mono fun _ h ↦ (norm_nonneg _).trans h
  have hb0 : ∀ᵐ _ ∂μ, 0 ≤ b := hb.mono fun _ h ↦ (norm_nonneg _).trans h
  have hA0 : ∀ᵐ _ ∂μ, 0 ≤ A := hA.mono fun _ h ↦ (norm_nonneg _).trans h
  -- The pointwise estimate, almost everywhere.
  have hpt : ∀ᵐ x ∂μ,
      ‖ω.floerRemainder (J (φ x)) (Ks (φ x)) (Kt (φ x)) (y x) (v x) (e₁ x) (d₁ x) -
        ω.floerRemainder (J (φ x)) (Ks (φ x)) (Kt (φ x)) (y x) (v x) (e₂ x) (d₂ x)‖ ≤
          (C.toNNReal : ℝ) * ‖(g₁ + g₂ + g₃) x‖ := by
    filter_upwards [hK', ha₁, ha₂, hb, hA, ha0, hb0, hA0] with x hx h₁ h₂ hbx hAx ha0 hb0 hA0
    rw [Real.norm_of_nonneg (by simp only [hg₁, hg₂, hg₃, Pi.add_apply]; positivity),
      Real.coe_toNNReal']
    exact ω.norm_floerRemainder_sub_le_of_le (hC (φ x) (y x) hx (v x) (e₁ x) (e₂ x) (d₁ x) (d₂ x)
      (h₁.trans haδ) (h₂.trans haδ)) h₁ h₂ hbx hAx
  -- Each term of the bound is controlled by the corresponding `Lᵖ` norm: scaling a norm by a
  -- constant that is nonnegative almost everywhere scales its `Lᵖ` norm.
  have hscale {c : ℝ} {f : α → V} (hf : AEStronglyMeasurable f μ) (hc : ∀ᵐ _ ∂μ, 0 ≤ c) :
      eLpNorm (fun x ↦ c * ‖f x‖) p μ ≤ ENNReal.ofReal c * eLpNorm f p μ :=
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hf.norm.const_mul c)
      (hc.mono fun _ hc ↦ (Real.norm_of_nonneg (by positivity)).le) p
  have h₁ : eLpNorm g₁ p μ ≤ ENNReal.ofReal (a * (1 + A)) * eLpNorm (e₁ - e₂) p μ :=
    hscale (he₁.sub he₂) (by filter_upwards [ha0, hA0] with _ ha0 hA0; positivity)
  have h₂ : eLpNorm g₂ p μ ≤ ENNReal.ofReal b * eLpNorm d₁ p μ := hscale hd₁ hb0
  have h₃ : eLpNorm g₃ p μ ≤ ENNReal.ofReal a * eLpNorm (d₁ - d₂) p μ := hscale (hd₁.sub hd₂) ha0
  calc _ ≤ ENNReal.ofReal (C.toNNReal : ℝ) * eLpNorm (g₁ + g₂ + g₃) p μ :=
        eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hm₁.sub hm₂) hpt p
    _ ≤ C.toNNReal * (eLpNorm g₁ p μ + eLpNorm g₂ p μ + eLpNorm g₃ p μ) := by
      rw [ENNReal.ofReal_coe_nnreal]
      gcongr
      exact (eLpNorm_add_le hp).trans (add_le_add_left (eLpNorm_add_le hp) _)
    _ ≤ _ := by gcongr

/-- **The quadratic estimate for the Floer operator in `Lᵖ`.** Let `J` be jointly `C²` and the
Hamiltonians `Ks`, `Kt` jointly `C³` in the parameter and the target point, and let `K` be a
compact set of pairs `(p, y)`. There are `δ > 0` and `C` with the following property. Let `μ` be a
measure on `ℝ × ℝ`, `s` a measurable set, `φ : ℝ × ℝ → P` a parameter map, measurable for `μ` on
`s`, and `w`, `ξ₁`, `ξ₂` maps differentiable at every point of `s`, with `(φ, w) ∈ K`,
`‖ξ₁‖, ‖ξ₂‖ ≤ a ≤ δ`, `‖ξ₁ - ξ₂‖ ≤ b` and slice defect `‖∂t w - X_Kt(w)‖ ≤ A` on `s`. Then for
`1 ≤ p` the Floer operator with coefficients `J (φ z)`, `Ks (φ z)`, `Kt (φ z)` satisfies
`‖F(w + ξ₁) - F(w + ξ₂) - D_w(ξ₁ - ξ₂)‖_p ≤ C (a (1 + A) ‖ξ₁ - ξ₂‖_p + b ‖∂t ξ₁‖_p +
  a ‖∂t ξ₁ - ∂t ξ₂‖_p)`, all norms in `Lᵖ(s, μ)`. -/
theorem exists_pos_forall_eLpNorm_floerOperator_sub_floerOperator_sub_floerLinearization_le
    (hK : IsCompact K) (hJ : ContDiff ℝ 2 (Function.uncurry J))
    (hKs : ContDiff ℝ 3 (Function.uncurry Ks)) (hKt : ContDiff ℝ 3 (Function.uncurry Kt)) :
    ∃ δ > 0, ∃ C : ℝ≥0, ∀ (μ : Measure (ℝ × ℝ)) {p : ℝ≥0∞}, 1 ≤ p →
      ∀ {s : Set (ℝ × ℝ)} {φ : ℝ × ℝ → P} {w ξ₁ ξ₂ : ℝ × ℝ → V} {a A b : ℝ}, MeasurableSet s →
      AEStronglyMeasurable φ (μ.restrict s) → (∀ z ∈ s, DifferentiableAt ℝ w z) →
      (∀ z ∈ s, DifferentiableAt ℝ ξ₁ z) → (∀ z ∈ s, DifferentiableAt ℝ ξ₂ z) →
      (∀ z ∈ s, (φ z, w z) ∈ K) → a ≤ δ → (∀ z ∈ s, ‖ξ₁ z‖ ≤ a) → (∀ z ∈ s, ‖ξ₂ z‖ ≤ a) →
      (∀ z ∈ s, ‖ξ₁ z - ξ₂ z‖ ≤ b) →
      (∀ z ∈ s, ‖fderiv ℝ w z stdComplexLineImag -
        ω.hamiltonianVectorField (Kt (φ z)) (w z)‖ ≤ A) →
      eLpNorm (fun z ↦
          ω.floerOperator (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) (w + ξ₁) z -
            ω.floerOperator (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) (w + ξ₂) z -
            ω.floerLinearization (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) w
              (ξ₁ - ξ₂) z) p (μ.restrict s) ≤
        C * (ENNReal.ofReal (a * (1 + A)) * eLpNorm (ξ₁ - ξ₂) p (μ.restrict s) +
          ENNReal.ofReal b * eLpNorm (fun z ↦ fderiv ℝ ξ₁ z stdComplexLineImag) p (μ.restrict s) +
          ENNReal.ofReal a * eLpNorm (fun z ↦ fderiv ℝ ξ₁ z stdComplexLineImag -
            fderiv ℝ ξ₂ z stdComplexLineImag) p (μ.restrict s)) := by
  obtain ⟨δ, hδ, C, hC⟩ := ω.exists_pos_forall_eLpNorm_floerRemainder_sub_le hK hJ hKs hKt
  refine ⟨δ, hδ, C, fun μ p hp s φ w ξ₁ ξ₂ a A b hs hφ hw hξ₁ hξ₂ hK' haδ ha₁ ha₂ hb hA ↦ ?_⟩
  -- Measurability of the maps, which are continuous on `s`, and of their slice velocities.
  borelize V
  have hcont {f : ℝ × ℝ → V} (hf : ∀ z ∈ s, DifferentiableAt ℝ f z) :
      AEStronglyMeasurable f (μ.restrict s) :=
    ContinuousOn.aestronglyMeasurable (fun z hz ↦ (hf z hz).continuousAt.continuousWithinAt) hs
  have hder (f : ℝ × ℝ → V) :
      AEStronglyMeasurable (fun z ↦ fderiv ℝ f z stdComplexLineImag) (μ.restrict s) :=
    (measurable_fderiv_apply_const ℝ f _).aestronglyMeasurable
  have hb' := hC (μ.restrict s) hp hφ (hcont hw) (hder w) (hcont hξ₁) (hcont hξ₂) (hder ξ₁)
    (hder ξ₂) (ae_restrict_of_forall_mem hs hK') haδ (ae_restrict_of_forall_mem hs ha₁)
    (ae_restrict_of_forall_mem hs ha₂) (ae_restrict_of_forall_mem hs hb)
    (ae_restrict_of_forall_mem hs hA)
  refine le_of_eq_of_le (eLpNorm_congr_ae (ae_restrict_of_forall_mem hs fun z hz ↦ ?_)) hb'
  -- On `s` the operator difference is the difference of the remainders.
  have h₁ := ω.floerOperator_add_sub_floerOperator_sub_floerLinearization
    (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) w ξ₁ (hw z hz) (hξ₁ z hz)
  have h₂ := ω.floerOperator_add_sub_floerOperator_sub_floerLinearization
    (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) w ξ₂ (hw z hz) (hξ₂ z hz)
  dsimp only
  rw [floerLinearization_sub ω _ _ _ w ξ₁ ξ₂ z (hξ₁ z hz) (hξ₂ z hz), ← h₁, ← h₂]
  abel

/-- **The quadratic estimate for the Floer operator at a map, in `Lᵖ`.** Let `J` be jointly `C²`
and the Hamiltonians `Ks`, `Kt` jointly `C³` in the parameter and the target point, and let `K` be
a compact set of pairs `(p, y)`. There are `δ > 0` and `C` with the following property. Let `μ` be
a measure on `ℝ × ℝ`, `s` a measurable set, `φ : ℝ × ℝ → P` a parameter map, measurable for `μ` on
`s`, and `w`, `ξ` maps differentiable at every point of `s`, with `(φ, w) ∈ K`, `‖ξ‖ ≤ a ≤ δ` and
slice defect `‖∂t w - X_Kt(w)‖ ≤ A` on `s`. Then for `1 ≤ p` the Floer operator with
coefficients `J (φ z)`, `Ks (φ z)`, `Kt (φ z)` satisfies
`‖F(w + ξ) - F(w) - D_w ξ‖_p ≤ C (a (1 + A) ‖ξ‖_p + a ‖∂t ξ‖_p)`, all norms in `Lᵖ(s, μ)`. -/
theorem exists_pos_forall_eLpNorm_floerOperator_add_sub_floerOperator_sub_floerLinearization_le
    (hK : IsCompact K) (hJ : ContDiff ℝ 2 (Function.uncurry J))
    (hKs : ContDiff ℝ 3 (Function.uncurry Ks)) (hKt : ContDiff ℝ 3 (Function.uncurry Kt)) :
    ∃ δ > 0, ∃ C : ℝ≥0, ∀ (μ : Measure (ℝ × ℝ)) {p : ℝ≥0∞}, 1 ≤ p →
      ∀ {s : Set (ℝ × ℝ)} {φ : ℝ × ℝ → P} {w ξ : ℝ × ℝ → V} {a A : ℝ}, MeasurableSet s →
      AEStronglyMeasurable φ (μ.restrict s) → (∀ z ∈ s, DifferentiableAt ℝ w z) →
      (∀ z ∈ s, DifferentiableAt ℝ ξ z) → (∀ z ∈ s, (φ z, w z) ∈ K) → a ≤ δ →
      (∀ z ∈ s, ‖ξ z‖ ≤ a) →
      (∀ z ∈ s, ‖fderiv ℝ w z stdComplexLineImag -
        ω.hamiltonianVectorField (Kt (φ z)) (w z)‖ ≤ A) →
      eLpNorm (fun z ↦
          ω.floerOperator (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) (w + ξ) z -
            ω.floerOperator (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) w z -
            ω.floerLinearization (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) w ξ z)
          p (μ.restrict s) ≤
        C * (ENNReal.ofReal (a * (1 + A)) * eLpNorm ξ p (μ.restrict s) + ENNReal.ofReal a *
          eLpNorm (fun z ↦ fderiv ℝ ξ z stdComplexLineImag) p (μ.restrict s)) := by
  obtain ⟨δ, hδ, C, hC⟩ :=
    ω.exists_pos_forall_eLpNorm_floerOperator_sub_floerOperator_sub_floerLinearization_le
      hK hJ hKs hKt
  refine ⟨δ, hδ, 2 * C, fun μ p hp s φ w ξ a A hs hφ hw hξ hK' haδ ha hA ↦ ?_⟩
  have h0 : ∀ z ∈ s, DifferentiableAt ℝ (0 : ℝ × ℝ → V) z := fun z _ ↦ differentiableAt_const _
  have ha₀ : ∀ z ∈ s, ‖(0 : ℝ × ℝ → V) z‖ ≤ a := fun z hz ↦ by
    simpa using (norm_nonneg _).trans (ha z hz)
  have hb : ∀ z ∈ s, ‖ξ z - (0 : ℝ × ℝ → V) z‖ ≤ a := fun z hz ↦ by simpa using ha z hz
  have h := hC μ hp hs hφ hw hξ h0 hK' haδ ha ha₀ hb hA
  simp only [add_zero, sub_zero, Pi.zero_apply, fderiv_zero, zero_apply] at h
  refine h.trans ?_
  set P := ENNReal.ofReal (a * (1 + A)) * eLpNorm ξ p (μ.restrict s)
  set Q := ENNReal.ofReal a * eLpNorm (fun z ↦ fderiv ℝ ξ z stdComplexLineImag) p (μ.restrict s)
  -- `P + Q + Q ≤ (P + Q) + (P + Q) = 2 (P + Q)`.
  calc (C : ℝ≥0∞) * (P + Q + Q) ≤ C * (P + Q + (P + Q)) := by
        gcongr
        exact le_add_self
    _ = ((2 * C : ℝ≥0) : ℝ≥0∞) * (P + Q) := by push_cast; ring

end Lp

/-! ### The estimate in `W^{1,p}` on the cylinder -/

section Jet

open MeasureTheory Set
open StripSobolev (jet stripMeasure jet_sub norm_le_norm_jet
  eLpNorm_fderiv_zero_one_le_eLpNorm_jet)
open scoped NNReal ENNReal

omit [FiniteDimensional ℝ V] in
/-- Morrey's estimate on the cylinder with constant `M`, as a bound on the norm by the constant
`M + 1` times the real `Lᵖ` norm of the jet. -/
private theorem norm_le_mul_toReal_eLpNorm_jet {M p : ℝ≥0} {η : ℝ × ℝ → V}
    (hM : ∀ z, ‖η z‖ₑ ≤ M * eLpNorm (jet η) p stripMeasure)
    (hfin : eLpNorm (jet η) p stripMeasure ≠ ∞) (z : ℝ × ℝ) :
    ‖η z‖ ≤ (M + 1 : ℝ≥0) * (eLpNorm (jet η) p stripMeasure).toReal := by
  rw [← toReal_eNorm]
  calc (‖η z‖ₑ).toReal ≤ (M * eLpNorm (jet η) p stripMeasure).toReal :=
        ENNReal.toReal_mono (by finiteness) (hM z)
    _ ≤ (M + 1 : ℝ≥0) * (eLpNorm (jet η) p stripMeasure).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.coe_toReal]
        gcongr
        exact_mod_cast le_add_of_nonneg_right zero_le_one

/-- A multiple of the larger of two finite norms is at most the same multiple of their sum. -/
private theorem ofReal_mul_max_toReal_le {c : ℝ≥0} {E₁ E₂ : ℝ≥0∞} (hE₁ : E₁ ≠ ∞) (hE₂ : E₂ ≠ ∞) :
    ENNReal.ofReal (c * max E₁.toReal E₂.toReal) ≤ c * (E₁ + E₂) := by
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal]
  gcongr
  calc ENNReal.ofReal (max E₁.toReal E₂.toReal) ≤ ENNReal.ofReal (E₁.toReal + E₂.toReal) :=
        ENNReal.ofReal_le_ofReal (max_le (by simp) (by simp))
    _ = E₁ + E₂ := by
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal hE₁, ENNReal.ofReal_toReal hE₂]

/-- The arithmetic combining the three terms of the `Lᵖ` quadratic estimate into a product of
norms of jets. -/
private theorem mul_add_add_le_of_ofReal_le {C c : ℝ≥0} {a b A : ℝ} {E₁ E₂ E T₁ T₂ T₃ : ℝ≥0∞}
    (ha0 : 0 ≤ a) (hA0 : 0 ≤ A) (ha : ENNReal.ofReal a ≤ c * (E₁ + E₂))
    (hb : ENNReal.ofReal b = c * E) (hT₁ : T₁ ≤ E) (hT₂ : T₂ ≤ E₁) (hT₃ : T₃ ≤ E) :
    (C : ℝ≥0∞) * (ENNReal.ofReal (a * (1 + A)) * T₁ + ENNReal.ofReal b * T₂ +
        ENNReal.ofReal a * T₃) ≤
      ((3 * C * c : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (1 + A) * (E₁ + E₂) * E := by
  set X := E₁ + E₂
  set R := ENNReal.ofReal (1 + A)
  have hR : 1 ≤ R := by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have hXR : X ≤ X * R := le_mul_of_one_le_right' hR
  have haA : ENNReal.ofReal (a * (1 + A)) ≤ c * X * R := by
    rw [ENNReal.ofReal_mul ha0]
    gcongr
  calc (C : ℝ≥0∞) * (ENNReal.ofReal (a * (1 + A)) * T₁ + ENNReal.ofReal b * T₂ +
        ENNReal.ofReal a * T₃)
      ≤ C * (c * X * R * E + c * E * (X * R) + c * (X * R) * E) := by
        rw [hb]
        gcongr
        · exact (hT₂.trans le_self_add).trans hXR
        · exact ha.trans (by gcongr)
    _ = ((3 * C * c : ℝ≥0) : ℝ≥0∞) * R * X * E := by push_cast; ring

/-- **The quadratic estimate for the Floer operator in `W^{1,p}` on the cylinder.** Let `J` be
jointly `C²` and the Hamiltonians `Ks`, `Kt` jointly `C³` in the parameter and the target point,
let `K` be a compact set of pairs `(p, y)`, and let `p > 2`. There are `δ > 0` and `C` with the
following property. Let `φ : ℝ × ℝ → P` be a parameter map, measurable on the strip
`ℝ × [0, 1]`, let `w` be differentiable on the strip, with `(φ, w) ∈ K` and slice defect
`‖∂t w - X_Kt(w)‖ ≤ A` there, and let `ξ₁`, `ξ₂` be `C¹` maps of period one in `t` whose jets
`(ξ, ∂s ξ, ∂t ξ)` have `Lᵖ` norm at most `δ` on the strip. Then, all norms on the strip,

`‖F(w + ξ₁) - F(w + ξ₂) - D_w(ξ₁ - ξ₂)‖_p ≤ C (1 + A) (‖jet ξ₁‖_p + ‖jet ξ₂‖_p) ‖jet (ξ₁ - ξ₂)‖_p`,

where `F` is the Floer operator with coefficients `J (φ z)`, `Ks (φ z)`, `Kt (φ z)`. This is the
estimate `‖N x - N y‖ ≤ (L / 2) (‖x‖ + ‖y‖) ‖x - y‖` of
`TauCeti.exists_mem_range_norm_le_add_add_eq_zero` for the remainder `N` of `F` at `w`, in the
`W^{1,p}` norm of the cylinder. It follows from the `Lᵖ` estimate
`exists_pos_forall_eLpNorm_floerOperator_sub_floerOperator_sub_floerLinearization_le` and
Morrey's estimate on the cylinder (`TauCeti.CylinderSobolev.exists_enorm_le_mul_eLpNorm_jet`),
which bounds the sup norms of `ξ₁`, `ξ₂` and `ξ₁ - ξ₂` by the `Lᵖ` norms of their jets. -/
theorem exists_pos_forall_eLpNorm_floerOperator_sub_floerOperator_sub_floerLinearization_le_jet
    (hK : IsCompact K) (hJ : ContDiff ℝ 2 (Function.uncurry J))
    (hKs : ContDiff ℝ 3 (Function.uncurry Ks)) (hKt : ContDiff ℝ 3 (Function.uncurry Kt))
    {p : ℝ≥0} (hp : 2 < p) :
    ∃ δ > 0, ∃ C : ℝ≥0, ∀ {φ : ℝ × ℝ → P} {w ξ₁ ξ₂ : ℝ × ℝ → V} {A : ℝ},
      AEStronglyMeasurable φ stripMeasure →
      (∀ z ∈ (univ : Set ℝ) ×ˢ Icc (0 : ℝ) 1, DifferentiableAt ℝ w z) →
      ContDiff ℝ 1 ξ₁ → ContDiff ℝ 1 ξ₂ →
      (∀ s t, ξ₁ (s, t + 1) = ξ₁ (s, t)) → (∀ s t, ξ₂ (s, t + 1) = ξ₂ (s, t)) →
      (∀ z ∈ (univ : Set ℝ) ×ˢ Icc (0 : ℝ) 1, (φ z, w z) ∈ K) →
      eLpNorm (jet ξ₁) p stripMeasure ≤ ENNReal.ofReal δ →
      eLpNorm (jet ξ₂) p stripMeasure ≤ ENNReal.ofReal δ →
      (∀ z ∈ (univ : Set ℝ) ×ˢ Icc (0 : ℝ) 1, ‖fderiv ℝ w z stdComplexLineImag -
        ω.hamiltonianVectorField (Kt (φ z)) (w z)‖ ≤ A) →
      eLpNorm (fun z ↦
          ω.floerOperator (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) (w + ξ₁) z -
            ω.floerOperator (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) (w + ξ₂) z -
            ω.floerLinearization (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) w
              (ξ₁ - ξ₂) z) p stripMeasure ≤
        C * ENNReal.ofReal (1 + A) *
          (eLpNorm (jet ξ₁) p stripMeasure + eLpNorm (jet ξ₂) p stripMeasure) *
          eLpNorm (jet (ξ₁ - ξ₂)) p stripMeasure := by
  obtain ⟨δ, hδ, C, hC⟩ :=
    ω.exists_pos_forall_eLpNorm_floerOperator_sub_floerOperator_sub_floerLinearization_le
      hK hJ hKs hKt
  obtain ⟨M, hM⟩ := CylinderSobolev.exists_enorm_le_mul_eLpNorm_jet (V := V) hp
  have hc0 : (0 : ℝ) < (M + 1 : ℝ≥0) := by positivity
  refine ⟨δ / (M + 1 : ℝ≥0), by positivity, 3 * C * (M + 1), fun {φ w ξ₁ ξ₂ A} hφ hw hξ₁ hξ₂
    hper₁ hper₂ hK' h₁ h₂ hA ↦ ?_⟩
  have hp1 : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast (one_le_two.trans hp.le)
  have hξ := hξ₁.sub hξ₂
  have hper : ∀ s t, (ξ₁ - ξ₂) (s, t + 1) = (ξ₁ - ξ₂) (s, t) := fun s t ↦ by
    simp [hper₁, hper₂]
  have hE₁ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h₁
  have hE₂ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h₂
  have hE : eLpNorm (jet (ξ₁ - ξ₂)) p stripMeasure ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hE₁, hE₂⟩) ?_
    rw [jet_sub (hξ₁.differentiable one_ne_zero) (hξ₂.differentiable one_ne_zero)]
    exact eLpNorm_sub_le hp1
  -- Morrey's estimate bounds the sup norms by `a` and `b`, the scaled `Lᵖ` norms of the jets.
  set a := (M + 1 : ℝ≥0) * max (eLpNorm (jet ξ₁) p stripMeasure).toReal
    (eLpNorm (jet ξ₂) p stripMeasure).toReal
  have haδ : a ≤ δ := by
    have hδc : 0 ≤ δ / (M + 1 : ℝ≥0) := by positivity
    calc a ≤ (M + 1 : ℝ≥0) * (δ / (M + 1 : ℝ≥0)) := mul_le_mul_of_nonneg_left (max_le
          (ENNReal.toReal_le_of_le_ofReal hδc h₁) (ENNReal.toReal_le_of_le_ofReal hδc h₂)) hc0.le
      _ = δ := mul_div_cancel₀ δ hc0.ne'
  have hQ := hC volume hp1 (MeasurableSet.univ.prod measurableSet_Icc) hφ hw
    (fun z _ ↦ hξ₁.differentiable one_ne_zero z) (fun z _ ↦ hξ₂.differentiable one_ne_zero z) hK'
    haδ (fun z _ ↦ (norm_le_mul_toReal_eLpNorm_jet (hM hξ₁ hper₁) hE₁ z).trans
      (mul_le_mul_of_nonneg_left (le_max_left _ _) hc0.le))
    (fun z _ ↦ (norm_le_mul_toReal_eLpNorm_jet (hM hξ₂ hper₂) hE₂ z).trans
      (mul_le_mul_of_nonneg_left (le_max_right _ _) hc0.le))
    (fun z _ ↦ norm_le_mul_toReal_eLpNorm_jet (hM hξ hper) hE z) hA
  refine hQ.trans (mul_add_add_le_of_ofReal_le (by positivity)
    ((norm_nonneg _).trans (hA (0, 0) ⟨mem_univ _, left_mem_Icc.2 zero_le_one⟩)) ?_ ?_
    (eLpNorm_mono hξ.continuous.aestronglyMeasurable (norm_le_norm_jet _))
    (eLpNorm_fderiv_zero_one_le_eLpNorm_jet ((hξ₁.continuous_fderiv one_ne_zero).clm_apply
      continuous_const).aestronglyMeasurable _) ?_)
  · exact ofReal_mul_max_toReal_le hE₁ hE₂
  · rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal]
    exact congrArg _ (ENNReal.ofReal_toReal hE)
  · -- The difference of the slice velocities is the slice velocity of the difference.
    have h : (fun z ↦ fderiv ℝ ξ₁ z stdComplexLineImag - fderiv ℝ ξ₂ z stdComplexLineImag) =
        fun z ↦ fderiv ℝ (ξ₁ - ξ₂) z stdComplexLineImag := funext fun z ↦ by
      rw [fderiv_sub (hξ₁.differentiable one_ne_zero z) (hξ₂.differentiable one_ne_zero z),
        sub_apply]
    rw [h]
    exact eLpNorm_fderiv_zero_one_le_eLpNorm_jet
      ((hξ.continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable _

end Jet

end TauCeti.SymplecticForm
