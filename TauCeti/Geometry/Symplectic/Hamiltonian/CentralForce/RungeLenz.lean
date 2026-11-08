/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Integrable

/-!
# Independent Runge–Lenz integrals

The planar Kepler problem has three functionally independent first integrals on a dense
subset of its four-dimensional punctured phase space: the energy, angular momentum, and
one component of the Runge–Lenz vector. The component may depend on the point. Its
independence follows by evaluating differentials on the rotation field: this field kills
the energy and angular momentum but rotates the Runge–Lenz vector.

The existing conservation theorem
`stdSymplecticForm_poissonBracket_inner_rungeLenz` supplies the first-integral property.
Here `exists_linearIndependent_fderiv_kepler_of_rungeLenz_ne_zero` supplies independence
wherever the Runge–Lenz
vector is nonzero, and `dense_setOf_exists_linearIndependent_fderiv_kepler` gives density.
All derivatives are evaluated on the ambient phase space at noncollision points, so they
also describe the restricted functions on the open punctured phase space. No continuation
through collisions or global action-angle chart is asserted.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Sections 8 and 15.
* H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., Section 3.9.
-/

public noncomputable section

open Function Set
open scoped InnerProductSpace ContDiff Manifold

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- For nonzero mass and coupling, the Runge–Lenz vector is nonzero on a dense subset
of the punctured phase space. -/
theorem dense_setOf_rungeLenz_ne_zero {m κ : ℝ} (hm : m ≠ 0) (hκ : κ ≠ 0) :
    Dense {x : puncturedPhaseSpace V | rungeLenz m κ (x : V × V) ≠ 0} := by
  refine dense_setOf_inner_ne_zero.mono fun x hx hA ↦ ?_
  have h := inner_rungeLenz_snd m κ (x : V × V)
  rw [hA, inner_zero_left] at h
  exact (mul_ne_zero (neg_ne_zero.2 (div_ne_zero (mul_ne_zero hm hκ)
    (norm_ne_zero_iff.2 (mem_puncturedPhaseSpace.1 x.2)))) hx) h.symm

variable (b : OrthonormalBasis (Fin 2) ℝ V)

/-- A nonzero Runge–Lenz vector rules out a circular critical point of the planar
Kepler energy–momentum map. No sign assumption on mass or coupling is needed. -/
theorem isRegularPoint_centralForceEnergyMomentum_kepler_of_rungeLenz_ne_zero
    {m κ : ℝ} (hm : m ≠ 0)
    {x : V × V} (hq : x.1 ≠ 0) (hA : rungeLenz m κ x ≠ 0) :
    IsRegularPoint 𝓘(ℝ, V × V) 𝓘(ℝ, Fin 2 → ℝ)
      (centralForceEnergyMomentum b m (fun r ↦ -κ / r)) x := by
  have hr : ‖x.1‖ ≠ 0 := norm_ne_zero_iff.2 hq
  have hU := hasDerivAt_kepler_potential κ hr
  refine (isRegularPoint_centralForceEnergyMomentum_iff b hm hU hq).2 fun ⟨hqp, hc⟩ ↦ hA ?_
  have hL := sq_angularMomentum b x
  rw [hqp, zero_pow two_ne_zero, sub_zero] at hL
  have hp : ‖x.2‖ ^ 2 = m * κ / ‖x.1‖ := by
    rw [eq_div_iff hr]
    have hc' := (div_eq_div_iff (pow_ne_zero 2 hr)
      (mul_ne_zero hm (pow_ne_zero 3 hr))).1 hc
    rw [hL] at hc'
    have hcancel : ‖x.1‖ ^ 3 * (‖x.2‖ ^ 2 * ‖x.1‖ - m * κ) = 0 := by
      linear_combination -hc'
    exact sub_eq_zero.1 ((mul_eq_zero.1 hcancel).resolve_left (pow_ne_zero 3 hr))
  obtain ⟨q, p⟩ := x
  rw [rungeLenz_apply, hqp, zero_smul, sub_zero, hp, sub_self]

/-- The rotation field of the angular momentum acts on the Runge–Lenz component along
`⟪A, b 0⟫ • b 1 - ⟪A, b 1⟫ • b 0` by `‖A‖²`, where `A` is the Runge–Lenz vector at the point. -/
private theorem fderiv_inner_rungeLenz_hamiltonianVectorField_angularMomentum
    [FiniteDimensional ℝ V] {m κ : ℝ} {x : V × V} (hq : x.1 ≠ 0) :
    fderiv ℝ (fun y ↦ ⟪rungeLenz m κ y, ⟪rungeLenz m κ x, b 0⟫_ℝ • b 1 -
        ⟪rungeLenz m κ x, b 1⟫_ℝ • b 0⟫_ℝ) x
      ((stdSymplecticForm (V := V)).hamiltonianVectorField (angularMomentum (b 0) (b 1)) x) =
    ‖rungeLenz m κ x‖ ^ 2 := by
  set A := rungeLenz m κ x
  set e := ⟪A, b 0⟫_ℝ • b 1 - ⟪A, b 1⟫_ℝ • b 0
  rw [← SymplecticForm.poissonBracket_eq_fderiv,
    stdSymplecticForm_poissonBracket_inner_rungeLenz_angularMomentum m κ (b 0) (b 1) e hq]
  have hb : ∀ i j, ⟪b i, b j⟫_ℝ = if i = j then 1 else 0 :=
    orthonormal_iff_ite.1 b.orthonormal
  have hnorm : ‖A‖ ^ 2 = ⟪A, b 0⟫_ℝ ^ 2 + ⟪A, b 1⟫_ℝ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner A A, Fin.sum_univ_two]
    simp only [real_inner_comm (b 0) A, real_inner_comm (b 1) A, pow_two]
  have he0 : ⟪b 0, e⟫_ℝ = -⟪A, b 1⟫_ℝ := by
    simp [e, inner_sub_right, real_inner_smul_right, hb]
  have he1 : ⟪b 1, e⟫_ℝ = ⟪A, b 0⟫_ℝ := by
    simp [e, inner_sub_right, real_inner_smul_right, hb]
  rw [he0, he1]
  have halg (a c : ℝ) : a * a - c * (-c) = a ^ 2 + c ^ 2 := by ring
  exact (halg _ _).trans hnorm.symm

/-- At every noncollision point with nonzero Runge–Lenz vector, one component of that
vector is independent of the Kepler energy and planar angular momentum. Each of these
three functions is a first integral of the Kepler Hamiltonian. -/
theorem exists_linearIndependent_fderiv_kepler_of_rungeLenz_ne_zero
    {m κ : ℝ} (hm : m ≠ 0)
    {x : V × V} (hq : x.1 ≠ 0) (hA : rungeLenz m κ x ≠ 0) :
    ∃ e : V, LinearIndependent ℝ ![
      fderiv ℝ (centralForceHamiltonian m (fun r ↦ -κ / r)) x,
      fderiv ℝ (angularMomentum (b 0) (b 1)) x,
      fderiv ℝ (fun y ↦ ⟪rungeLenz m κ y, e⟫_ℝ) x] := by
  let : FiniteDimensional ℝ V := b.toBasis.finiteDimensional_of_finite
  let A := rungeLenz m κ x
  let e := ⟪A, b 0⟫_ℝ • b 1 - ⟪A, b 1⟫_ℝ • b 0
  let H : V × V → ℝ := centralForceHamiltonian m (fun r ↦ -κ / r)
  let L := angularMomentum (b 0) (b 1)
  let G := fun y ↦ ⟪rungeLenz m κ y, e⟫_ℝ
  let R := (stdSymplecticForm (V := V)).hamiltonianVectorField L x
  have hU := hasDerivAt_kepler_potential κ (norm_ne_zero_iff.2 hq)
  have hH := hasFDerivAt_centralForceHamiltonian (m := m) hU hq
  have hL := hasFDerivAt_angularMomentum (b 0) (b 1) x
  -- Rotation kills the first two integrals and detects the component of `A` along its rotation.
  have hHrot : fderiv ℝ H x R = 0 := by
    rw [← SymplecticForm.poissonBracket_eq_fderiv]
    exact stdSymplecticForm_poissonBracket_centralForceHamiltonian_angularMomentum hU hq _ _
  have hLrot : fderiv ℝ L x R = 0 := by
    rw [← SymplecticForm.poissonBracket_eq_fderiv]
    exact SymplecticForm.poissonBracket_self _ _ _
  have hGrot : fderiv ℝ G x R = ‖A‖ ^ 2 :=
    fderiv_inner_rungeLenz_hamiltonianVectorField_angularMomentum b hq
  -- The existing central-force regularity criterion supplies independence of `dH` and `dL`.
  have hsurj : Surjective (ContinuousLinearMap.pi ![fderiv ℝ H x, fderiv ℝ L x]) := by
    have hreg :=
      isRegularPoint_centralForceEnergyMomentum_kepler_of_rungeLenz_ne_zero b hm hq hA
    rw [isRegularPoint_iff_surjective_fderiv,
      (hasFDerivAt_centralForceEnergyMomentum b hU hq).fderiv] at hreg
    simpa only [H, L, hH.fderiv, hL.fderiv] using hreg
  -- Evaluate a vanishing linear combination first on rotation, then on lifts of `ℝ²`.
  refine ⟨e, Fintype.linearIndependent_iff.2 fun c hc ↦ ?_⟩
  have heval (v : V × V) :
      c 0 * fderiv ℝ H x v + c 1 * fderiv ℝ L x v + c 2 * fderiv ℝ G x v = 0 := by
    have h := DFunLike.congr_fun hc v
    simpa [Fin.sum_univ_three] using h
  have hc2 : c 2 = 0 := by
    have h := heval R
    rw [hHrot, hLrot, hGrot, mul_zero, mul_zero, zero_add, zero_add] at h
    exact (mul_eq_zero.1 h).resolve_right (pow_ne_zero 2 (norm_ne_zero_iff.2 hA))
  have hcoeff (r s : ℝ) : c 0 * r + c 1 * s = 0 := by
    obtain ⟨v, hv⟩ := hsurj ![r, s]
    have hv0 := congrFun hv 0
    have hv1 := congrFun hv 1
    simp only [ContinuousLinearMap.pi_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hv0 hv1
    simpa only [hc2, zero_mul, add_zero, hv0, hv1] using heval v
  have hc0 : c 0 = 0 := by simpa only [mul_one, mul_zero, add_zero] using hcoeff 1 0
  have hc1 : c 1 = 0 := by simpa only [mul_one, mul_zero, zero_add] using hcoeff 0 1
  intro i
  fin_cases i
  · exact hc0
  · exact hc1
  · exact hc2

/-- The planar Kepler problem has three independent first integrals on a dense subset
of its punctured phase space: energy, angular momentum, and a Runge–Lenz component.
The component is allowed to depend on the point. -/
theorem dense_setOf_exists_linearIndependent_fderiv_kepler {m κ : ℝ}
    (hm : m ≠ 0) (hκ : κ ≠ 0) :
    Dense {x : puncturedPhaseSpace V | ∃ e : V, LinearIndependent ℝ ![
      fderiv ℝ (centralForceHamiltonian m (fun r ↦ -κ / r)) (x : V × V),
      fderiv ℝ (angularMomentum (b 0) (b 1)) (x : V × V),
      fderiv ℝ (fun y ↦ ⟪rungeLenz m κ y, e⟫_ℝ) (x : V × V)]} :=
  (dense_setOf_rungeLenz_ne_zero hm hκ).mono fun x hA ↦
    exists_linearIndependent_fderiv_kepler_of_rungeLenz_ne_zero b hm
      (mem_puncturedPhaseSpace.1 x.2) hA

end TauCeti
