/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.AlmostComplex.Rotation
public import TauCeti.Geometry.Symplectic.Hamiltonian.Hessian

/-!
# Periodic orbits of the quadratic Hamiltonians `a ‖x‖²`

Let `ω` be a linear symplectic form on a finite-dimensional real inner product space `V` whose
inner product is the metric of a compatible complex structure `J`, `ω(u, J v) = ⟪u, v⟫`. This file
computes the periodic orbits of the Hamiltonian flows of the quadratic Hamiltonians `a ‖x‖²`,
which are linear at infinity with slope `a` on the unit ball
(`TauCeti.isLinearAtInfinity_mul_norm_sq`) and enter the symplectic homology of the ball.

The Hamiltonian vector field of `a ‖x‖²` is `-2 a J x`
(`TauCeti.SymplecticForm.hamiltonianVectorField_mul_norm_sq`), so its flow is a rotation along the
complex lines of `J` (`TauCeti.AlmostComplexStructure.eq_cos_smul_add_sin_smul_of_hasDerivAt`).
Its integral curves are `cos (2 a t) x - sin (2 a t) J x`
(`TauCeti.SymplecticForm.eq_of_hasDerivAt_hamiltonianVectorField_mul_norm_sq`), and one not
starting at the origin has period `T` exactly when `a T ∈ πℤ`
(`TauCeti.SymplecticForm.periodic_iff_of_hasDerivAt_hamiltonianVectorField_mul_norm_sq`). So
`a ‖x‖²` has a `1`-periodic orbit away from the origin exactly when `a ∈ πℤ`
(`TauCeti.SymplecticForm.exists_periodic_one_ne_zero_hamiltonianVectorField_mul_norm_sq_iff`).
For a slope `a ∉ πℤ` the only `1`-periodic orbit is the constant orbit at the origin
(`TauCeti.SymplecticForm.eq_zero_of_hasDerivAt_hamiltonianVectorField_mul_norm_sq_of_periodic`),
while for `a ∈ πℤ`, such as `a = π`, every orbit is `1`-periodic
(`TauCeti.SymplecticForm.periodic_one_of_hasDerivAt_hamiltonianVectorField_mul_norm_sq`). In
particular the degenerate slopes are the multiples of `π`, not of `2π`.

These are the dynamical inputs of the computation `SH_*(D²ⁿ) = 0`: the slopes `a ∉ πℤ` are the
admissible ones, and for them the only generator of the Floer complex of `a ‖x‖²` is the constant
orbit at the origin. They match the Reeb periods `k π` of the unit sphere
(`TauCeti.SymplecticForm.exists_periodic_reebVectorField_sphereContactForm_iff`).

## Main results

* `TauCeti.SymplecticForm.eq_of_hasDerivAt_hamiltonianVectorField_mul_norm_sq`: the integral
  curves of `X_{a ‖x‖²} = -2 a J x` are the rotations `cos (2 a t) x - sin (2 a t) J x`.
* `TauCeti.SymplecticForm.periodic_iff_of_hasDerivAt_hamiltonianVectorField_mul_norm_sq`: an
  integral curve not starting at the origin has period `T` exactly when `a T ∈ πℤ`.
* `TauCeti.SymplecticForm.exists_periodic_one_ne_zero_hamiltonianVectorField_mul_norm_sq_iff`:
  `a ‖x‖²` has a `1`-periodic orbit away from the origin exactly when `a ∈ πℤ`.

## References

* P. Seidel, *A biased view of symplectic cohomology*, Current Developments in Mathematics 2006,
  Section 3 (the ball and the Hamiltonians linear at infinity).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §3.
-/

public section

noncomputable section

open Function Real
open scoped RealInnerProductSpace

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : AlmostComplexStructure V}

omit [FiniteDimensional ℝ V] in
/-- The rotation `cos (2 a t) x - sin (2 a t) J x` is the rotation by the angle `-2 a t`, the form
in which `TauCeti.AlmostComplexStructure` states the rotations solving `γ' = θ J γ`. -/
private theorem cos_smul_sub_sin_smul_eq (a t : ℝ) (x : V) :
    Real.cos (2 * a * t) • x - Real.sin (2 * a * t) • J x =
      Real.cos (-2 * a * t) • x + Real.sin (-2 * a * t) • J x := by
  simp [neg_mul, Real.cos_neg, Real.sin_neg, sub_eq_add_neg, mul_assoc]

/-- **The flow of a quadratic Hamiltonian is a rotation.** If the inner product of `V` is the
metric `ω(·, J ·)`, the curve `t ↦ cos (2 a t) x - sin (2 a t) J x` is an integral curve of the
Hamiltonian vector field of `y ↦ a ‖y‖²`. -/
theorem hasDerivAt_hamiltonianVectorField_mul_norm_sq (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (a : ℝ)
    (x : V) (t : ℝ) :
    HasDerivAt (fun t ↦ Real.cos (2 * a * t) • x - Real.sin (2 * a * t) • J x)
      (ω.hamiltonianVectorField (fun y ↦ a * ‖y‖ ^ 2)
        (Real.cos (2 * a * t) • x - Real.sin (2 * a * t) • J x)) t := by
  simp only [hamiltonianVectorField_mul_norm_sq hg, cos_smul_sub_sin_smul_eq]
  exact J.hasDerivAt_cos_smul_add_sin_smul (-2 * a) x t

/-- **The integral curves of a quadratic Hamiltonian.** If the inner product of `V` is the metric
`ω(·, J ·)`, every integral curve of the Hamiltonian vector field of `y ↦ a ‖y‖²` is the rotation
`t ↦ cos (2 a t) γ(0) - sin (2 a t) J γ(0)` of its initial value along the complex line of `J`
through it. -/
theorem eq_of_hasDerivAt_hamiltonianVectorField_mul_norm_sq (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    {a : ℝ} {γ : ℝ → V}
    (hγ : ∀ t, HasDerivAt γ (ω.hamiltonianVectorField (fun y ↦ a * ‖y‖ ^ 2) (γ t)) t) (t : ℝ) :
    γ t = Real.cos (2 * a * t) • γ 0 - Real.sin (2 * a * t) • J (γ 0) := by
  simp only [hamiltonianVectorField_mul_norm_sq hg] at hγ
  rw [cos_smul_sub_sin_smul_eq]
  exact J.eq_cos_smul_add_sin_smul_of_hasDerivAt hγ t

/-- **The periods of a quadratic Hamiltonian.** If the inner product of `V` is the metric
`ω(·, J ·)`, an integral curve of the Hamiltonian vector field of `y ↦ a ‖y‖²` has period `T`
exactly when it is the constant orbit at the origin or `a T` is an integer multiple of `π`. -/
theorem periodic_iff_of_hasDerivAt_hamiltonianVectorField_mul_norm_sq
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) {a : ℝ} {γ : ℝ → V}
    (hγ : ∀ t, HasDerivAt γ (ω.hamiltonianVectorField (fun y ↦ a * ‖y‖ ^ 2) (γ t)) t) (T : ℝ) :
    Periodic γ T ↔ γ 0 = 0 ∨ ∃ k : ℤ, a * T = k * π := by
  have hγ' : γ = fun t ↦ Real.cos (-2 * a * t) • γ 0 + Real.sin (-2 * a * t) • J (γ 0) := by
    funext t
    rw [eq_of_hasDerivAt_hamiltonianVectorField_mul_norm_sq hg hγ t, cos_smul_sub_sin_smul_eq]
  obtain ⟨x, hx⟩ : ∃ x, γ 0 = x := ⟨_, rfl⟩
  rw [hx] at hγ' ⊢
  rcases eq_or_ne x 0 with h0 | h0
  · refine iff_of_true (fun t ↦ ?_) (Or.inl h0)
    rw [hγ']
    simp [h0]
  · rw [hγ', J.periodic_cos_smul_add_sin_smul_iff h0, or_iff_right h0]
    -- `-2 a T = k (2 π)` exactly when `a T = (-k) π`.
    exact (Equiv.neg ℤ).exists_congr fun k ↦ by
      rw [Equiv.neg_apply, Int.cast_neg]
      constructor <;> intro hk <;> linarith

/-- **The degenerate slopes are the multiples of `π`.** If `V` is nonzero and its inner product is
the metric `ω(·, J ·)`, the Hamiltonian `y ↦ a ‖y‖²` has a `1`-periodic orbit through a nonzero
point exactly when `a` is an integer multiple of `π`. (For `a = 0` such an orbit is constant.) -/
theorem exists_periodic_one_ne_zero_hamiltonianVectorField_mul_norm_sq_iff [Nontrivial V]
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (a : ℝ) :
    (∃ γ : ℝ → V, (∀ t, HasDerivAt γ (ω.hamiltonianVectorField (fun y ↦ a * ‖y‖ ^ 2) (γ t)) t) ∧
      Periodic γ 1 ∧ γ 0 ≠ 0) ↔ ∃ k : ℤ, a = k * π := by
  constructor
  · rintro ⟨γ, hγ, hper, h0⟩
    simpa [h0] using (periodic_iff_of_hasDerivAt_hamiltonianVectorField_mul_norm_sq hg hγ 1).1 hper
  · rintro ⟨k, hk⟩
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have hγ := hasDerivAt_hamiltonianVectorField_mul_norm_sq hg a x
    refine ⟨_, hγ, ?_, by simpa using hx⟩
    exact (periodic_iff_of_hasDerivAt_hamiltonianVectorField_mul_norm_sq hg hγ 1).2
      (Or.inr ⟨k, by rw [mul_one, hk]⟩)

/-- **Admissible slopes have only the constant orbit.** If the inner product of `V` is the metric
`ω(·, J ·)` and `a` is not an integer multiple of `π`, the only `1`-periodic integral curve of the
Hamiltonian vector field of `y ↦ a ‖y‖²` is the constant orbit at the origin. -/
theorem eq_zero_of_hasDerivAt_hamiltonianVectorField_mul_norm_sq_of_periodic
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) {a : ℝ} (ha : ∀ k : ℤ, a ≠ k * π) {γ : ℝ → V}
    (hγ : ∀ t, HasDerivAt γ (ω.hamiltonianVectorField (fun y ↦ a * ‖y‖ ^ 2) (γ t)) t)
    (hper : Periodic γ 1) : γ = 0 := by
  have h0 : γ 0 = 0 := by
    simpa [ha] using (periodic_iff_of_hasDerivAt_hamiltonianVectorField_mul_norm_sq hg hγ 1).1 hper
  funext t
  rw [eq_of_hasDerivAt_hamiltonianVectorField_mul_norm_sq hg hγ t, h0]
  simp

/-- **At a degenerate slope every orbit is periodic.** If the inner product of `V` is the metric
`ω(·, J ·)` and `a` is an integer multiple of `π`, for instance `a = π`, every integral curve of
the Hamiltonian vector field of `y ↦ a ‖y‖²` is `1`-periodic. -/
theorem periodic_one_of_hasDerivAt_hamiltonianVectorField_mul_norm_sq
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) {a : ℝ} {k : ℤ} (ha : a = k * π) {γ : ℝ → V}
    (hγ : ∀ t, HasDerivAt γ (ω.hamiltonianVectorField (fun y ↦ a * ‖y‖ ^ 2) (γ t)) t) :
    Periodic γ 1 :=
  (periodic_iff_of_hasDerivAt_hamiltonianVectorField_mul_norm_sq hg hγ 1).2
    (Or.inr ⟨k, by rw [mul_one, ha]⟩)

end TauCeti.SymplecticForm
