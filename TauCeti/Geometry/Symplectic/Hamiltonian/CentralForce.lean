/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Standard
public import TauCeti.Analysis.InnerProductSpace.NormPow
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# Central forces and the Kepler problem

Let `V` be a finite-dimensional real inner product space, with phase space `V × V` of positions
`q` and momenta `p` and standard symplectic form `ω₀ = Σ dqᵢ ∧ dpᵢ`. A particle of mass `m` in a
central potential `U` has Hamiltonian `H(q, p) = ‖p‖² / (2m) + U(‖q‖)`
(`TauCeti.centralForceHamiltonian`). Away from the collision set `q = 0`, Hamilton's equations
read `q' = p / m`, `p' = -(U'(‖q‖) / ‖q‖) q`.

The angular momentum in the plane of `u, w ∈ V` is `L(q, p) = ⟪q, u⟫⟪p, w⟫ - ⟪q, w⟫⟪p, u⟫`
(`TauCeti.angularMomentum`); for `V = ℝ²` and the standard basis it is `q₁p₂ - q₂p₁`. Its
Hamiltonian vector field is `(R q, R p)` for the infinitesimal rotation
`R z = ⟪z, u⟫ w - ⟪z, w⟫ u`, acting on positions and momenta alike: `L` is the Hamiltonian
generating the rotations in that plane. It Poisson-commutes with every central-force Hamiltonian.

For the Kepler potential `U(r) = -κ / r`, the **Runge–Lenz vector**
`A(q, p) = ‖p‖² q - ⟪q, p⟫ p - (m κ / ‖q‖) q` (`TauCeti.rungeLenz`) is an additional conserved
quantity: every component of `A` Poisson-commutes with `H`. Its length is determined by the
energy and the angular momentum, `‖A‖² = (m κ)² + 2 m H (‖q‖² ‖p‖² - ⟪q, p⟫²)`, where
`‖q‖² ‖p‖² - ⟪q, p⟫²` is the squared length of the angular momentum bivector `q ∧ p`. In the
plane this is `L²`, and the components of `A` in an orthonormal basis are
`(p₂ L - m κ q₁ / ‖q‖, -p₁ L - m κ q₂ / ‖q‖)`.

The radial component `⟪A, q⟫ = ℓ² - m κ ‖q‖`, with `ℓ² = ‖q‖² ‖p‖² - ⟪q, p⟫²`, gives the orbit
equation: if `φ` is the angle between `A` and `q`, then `‖q‖ (m κ + ‖A‖ cos φ) = ℓ²`. For an
attractive potential and `ℓ ≠ 0` this is the conic `‖q‖ = ℓ² / (m κ (1 + e cos φ))` with
eccentricity `e = ‖A‖ / (m κ) = √(1 + 2 H ℓ² / (m κ²))`. The same identity bounds the distance from
the origin between `ℓ² / (m κ + ‖A‖)` and, when `‖A‖ < m κ`, `ℓ² / (m κ - ‖A‖)`; for `ℓ ≠ 0` the
inequality `‖A‖ < m κ` holds exactly when `H < 0`. On the collision set `ℓ = 0`,
`A = -(m κ / ‖q‖) q`.

The statements about Hamiltonian vector fields and Poisson brackets are pointwise on the punctured
phase space `q ≠ 0`, the cotangent bundle of the punctured configuration space; the Poisson
bracket at a point only depends on germs there.

## Main declarations

* `TauCeti.stdSymplecticForm_hamiltonianVectorField_centralForceHamiltonian`: Hamilton's
  equations for a central force.
* `TauCeti.stdSymplecticForm_hamiltonianVectorField_angularMomentum`: angular momentum generates
  rotations.
* `TauCeti.stdSymplecticForm_poissonBracket_centralForceHamiltonian_angularMomentum`:
  conservation of angular momentum, `{H, L} = 0`.
* `TauCeti.stdSymplecticForm_poissonBracket_inner_rungeLenz`: conservation of the Runge–Lenz
  vector, `{⟪A, e⟫, H} = 0`.
* `TauCeti.norm_rungeLenz_sq`: `‖A‖² = (m κ)² + 2 m H (‖q‖² ‖p‖² - ⟪q, p⟫²)`.
* `TauCeti.norm_rungeLenz_sq_of_orthonormalBasis`: in the plane, `‖A‖² = (m κ)² + 2 m H L²`.
* `TauCeti.norm_fst_mul_add_norm_rungeLenz_mul_cos_angle`: the orbit equation
  `‖q‖ (m κ + ‖A‖ cos φ) = ℓ²`.
* `TauCeti.norm_rungeLenz_eq_abs_mul_sqrt`: `‖A‖ = |m κ| √(1 + 2 H ℓ² / (m κ²))`.
* `TauCeti.norm_fst_eq_div_one_add_sqrt_mul_cos_angle`: Kepler orbits are conics,
  `‖q‖ = ℓ² / (m κ (1 + e cos φ))`.
* `TauCeti.norm_rungeLenz_lt_iff_centralForceHamiltonian_neg`: the eccentricity is less than one
  exactly when the energy is negative.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Sections 8 and 15.
* H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., Addison-Wesley, 2002,
  Section 3.9.
-/

public section

namespace TauCeti

open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V]

/-- The Hamiltonian `‖p‖² / (2m) + U(‖q‖)` of a particle of mass `m` moving in the central
potential `U` on the phase space `V × V` of positions `q` and momenta `p`. -/
noncomputable def centralForceHamiltonian (m : ℝ) (U : ℝ → ℝ) (x : V × V) : ℝ :=
  ‖x.2‖ ^ 2 / (2 * m) + U ‖x.1‖

@[simp]
theorem centralForceHamiltonian_apply (m : ℝ) (U : ℝ → ℝ) (q p : V) :
    centralForceHamiltonian m U (q, p) = ‖p‖ ^ 2 / (2 * m) + U ‖q‖ :=
  (rfl)

variable [InnerProductSpace ℝ V]

/-- The angular momentum `⟪q, u⟫⟪p, w⟫ - ⟪q, w⟫⟪p, u⟫` in the plane of `u` and `w`, the pairing
of the bivector `q ∧ p` with `u ∧ w`. For `V = ℝ²` and the standard basis it is `q₁p₂ - q₂p₁`. -/
noncomputable def angularMomentum (u w : V) (x : V × V) : ℝ :=
  ⟪x.1, u⟫_ℝ * ⟪x.2, w⟫_ℝ - ⟪x.1, w⟫_ℝ * ⟪x.2, u⟫_ℝ

@[simp]
theorem angularMomentum_apply (u w q p : V) :
    angularMomentum u w (q, p) = ⟪q, u⟫_ℝ * ⟪p, w⟫_ℝ - ⟪q, w⟫_ℝ * ⟪p, u⟫_ℝ :=
  (rfl)

/-- The Runge–Lenz vector `‖p‖² q - ⟪q, p⟫ p - (m κ / ‖q‖) q` of the Kepler problem with mass `m`
and potential `-κ / ‖q‖`. In an orthonormal basis of a plane its components are
`(p₂ L - m κ q₁ / ‖q‖, -p₁ L - m κ q₂ / ‖q‖)`, where `L = q₁p₂ - q₂p₁` is the angular momentum. -/
noncomputable def rungeLenz (m κ : ℝ) (x : V × V) : V :=
  ‖x.2‖ ^ 2 • x.1 - ⟪x.1, x.2⟫_ℝ • x.2 - (m * κ / ‖x.1‖) • x.1

@[simp]
theorem rungeLenz_apply (m κ : ℝ) (q p : V) :
    rungeLenz m κ (q, p) = ‖p‖ ^ 2 • q - ⟪q, p⟫_ℝ • p - (m * κ / ‖q‖) • q :=
  (rfl)

/-- The partial gradients of the angular momentum are `∇_q L = ⟪p, w⟫ u - ⟪p, u⟫ w` and
`∇_p L = ⟪q, u⟫ w - ⟪q, w⟫ u`. -/
theorem hasFDerivAt_angularMomentum (u w : V) (x : V × V) :
    HasFDerivAt (angularMomentum u w)
      ((innerSL ℝ (⟪x.2, w⟫_ℝ • u - ⟪x.2, u⟫_ℝ • w)).coprod
        (innerSL ℝ (⟪x.1, u⟫_ℝ • w - ⟪x.1, w⟫_ℝ • u))) x := by
  have hq (a : V) : HasFDerivAt (fun y : V × V ↦ ⟪y.1, a⟫_ℝ)
      ((innerSL ℝ a).comp (ContinuousLinearMap.fst ℝ V V)) x :=
    ((innerSL ℝ a).comp (ContinuousLinearMap.fst ℝ V V)).hasFDerivAt.congr_of_eventuallyEq
      (.of_forall fun y ↦ by simp [real_inner_comm])
  have hp (a : V) : HasFDerivAt (fun y : V × V ↦ ⟪y.2, a⟫_ℝ)
      ((innerSL ℝ a).comp (ContinuousLinearMap.snd ℝ V V)) x :=
    ((innerSL ℝ a).comp (ContinuousLinearMap.snd ℝ V V)).hasFDerivAt.congr_of_eventuallyEq
      (.of_forall fun y ↦ by simp [real_inner_comm])
  refine (((hq u).mul (hp w)).sub ((hq w).mul (hp u))).congr_fderiv
    (ContinuousLinearMap.ext fun v ↦ ?_)
  simp [real_inner_comm]
  ring

/-- Away from the collision set, the partial gradients of a central-force Hamiltonian are
`∇_q H = (U'(‖q‖) / ‖q‖) q` and `∇_p H = p / m`. -/
theorem hasFDerivAt_centralForceHamiltonian {m : ℝ} {U : ℝ → ℝ} {U' : ℝ} {x : V × V}
    (hU : HasDerivAt U U' ‖x.1‖) (hq : x.1 ≠ 0) :
    HasFDerivAt (centralForceHamiltonian m U)
      ((innerSL ℝ ((U' / ‖x.1‖) • x.1)).coprod (innerSL ℝ (m⁻¹ • x.2))) x := by
  have hp := ((hasFDerivAt_snd (p := x)).norm_sq).mul_const (2 * m)⁻¹
  have hn := hU.comp_hasFDerivAt x ((hasFDerivAt_norm_of_ne hq).comp x hasFDerivAt_fst)
  refine ((hp.add hn).congr_of_eventuallyEq (.of_forall fun y ↦ ?_)).congr_fderiv
    (ContinuousLinearMap.ext fun v ↦ ?_)
  · simp [centralForceHamiltonian, div_eq_mul_inv]
  · simp [div_eq_mul_inv]
    ring

/-- Away from the collision set, the partial gradients of the component `⟪A, e⟫` of the
Runge–Lenz vector are
`∇_q = ‖p‖² e - ⟪p, e⟫ p - (m κ / ‖q‖) e + (m κ ⟪q, e⟫ / ‖q‖³) q` and
`∇_p = 2 ⟪q, e⟫ p - ⟪p, e⟫ q - ⟪q, p⟫ e`. -/
theorem hasFDerivAt_inner_rungeLenz (m κ : ℝ) (e : V) {x : V × V} (hq : x.1 ≠ 0) :
    HasFDerivAt (fun y ↦ ⟪rungeLenz m κ y, e⟫_ℝ)
      ((innerSL ℝ (‖x.2‖ ^ 2 • e - ⟪x.2, e⟫_ℝ • x.2 - (m * κ / ‖x.1‖) • e +
          (m * κ * ⟪x.1, e⟫_ℝ / ‖x.1‖ ^ 3) • x.1)).coprod
        (innerSL ℝ ((2 * ⟪x.1, e⟫_ℝ) • x.2 - ⟪x.2, e⟫_ℝ • x.1 - ⟪x.1, x.2⟫_ℝ • e))) x := by
  have h1 := (hasFDerivAt_fst (p := x)).inner ℝ (hasFDerivAt_const e x)
  have h2 := (hasFDerivAt_snd (p := x)).inner ℝ (hasFDerivAt_const e x)
  have h12 := (hasFDerivAt_fst (p := x)).inner ℝ (hasFDerivAt_snd (p := x))
  have hn := (hasDerivAt_inv (norm_ne_zero_iff.2 hq)).comp_hasFDerivAt x
    ((hasFDerivAt_norm_of_ne hq).comp x hasFDerivAt_fst)
  have h := (((hasFDerivAt_snd (p := x)).norm_sq.mul h1).sub (h12.mul h2)).sub
    ((hn.mul h1).const_mul (m * κ))
  refine (h.congr_of_eventuallyEq (.of_forall fun y ↦ ?_)).congr_fderiv
    (ContinuousLinearMap.ext fun v ↦ ?_)
  · simp [rungeLenz, inner_sub_left, real_inner_smul_left, div_eq_mul_inv]
    ring
  · have hr : ‖x.1‖ ≠ 0 := norm_ne_zero_iff.2 hq
    simp [real_inner_comm]
    field_simp
    ring

/-- **The length of the Runge–Lenz vector.** Away from the collision set,
`‖A‖² = (m κ)² + 2 m H (‖q‖² ‖p‖² - ⟪q, p⟫²)` for the Kepler Hamiltonian
`H = ‖p‖² / (2m) - κ / ‖q‖`, where `‖q‖² ‖p‖² - ⟪q, p⟫²` is the squared length of the angular
momentum bivector `q ∧ p`. -/
theorem norm_rungeLenz_sq {m : ℝ} (hm : m ≠ 0) (κ : ℝ) {x : V × V} (hq : x.1 ≠ 0) :
    ‖rungeLenz m κ x‖ ^ 2 = (m * κ) ^ 2 + 2 * m * centralForceHamiltonian m (fun r ↦ -κ / r) x *
      (‖x.1‖ ^ 2 * ‖x.2‖ ^ 2 - ⟪x.1, x.2⟫_ℝ ^ 2) := by
  have hr : ‖x.1‖ ≠ 0 := norm_ne_zero_iff.2 hq
  rw [← real_inner_self_eq_norm_sq]
  simp only [rungeLenz, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [real_inner_self_eq_norm_sq x.1, real_inner_self_eq_norm_sq x.2, real_inner_comm x.2 x.1,
    centralForceHamiltonian]
  field_simp
  ring

section Plane

variable (b : OrthonormalBasis (Fin 2) ℝ V)

/-- In the plane, the squared angular momentum is the squared length
`‖q‖² ‖p‖² - ⟪q, p⟫²` of the bivector `q ∧ p`. -/
theorem sq_angularMomentum (x : V × V) :
    angularMomentum (b 0) (b 1) x ^ 2 = ‖x.1‖ ^ 2 * ‖x.2‖ ^ 2 - ⟪x.1, x.2⟫_ℝ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner x.1,
    ← b.sum_inner_mul_inner x.2, ← b.sum_inner_mul_inner x.1 x.2]
  simp only [angularMomentum, Fin.sum_univ_two, real_inner_comm x.1, real_inner_comm x.2]
  ring

/-- In the plane, the length of the Runge–Lenz vector is `‖A‖² = (m κ)² + 2 m H L²`. -/
theorem norm_rungeLenz_sq_of_orthonormalBasis {m : ℝ} (hm : m ≠ 0) (κ : ℝ) {x : V × V}
    (hq : x.1 ≠ 0) :
    ‖rungeLenz m κ x‖ ^ 2 = (m * κ) ^ 2 + 2 * m * centralForceHamiltonian m (fun r ↦ -κ / r) x *
      angularMomentum (b 0) (b 1) x ^ 2 := by
  rw [norm_rungeLenz_sq hm κ hq, sq_angularMomentum]

/-- The first planar component of the Runge–Lenz vector is `p₂ L - m κ q₁ / ‖q‖`. -/
theorem inner_rungeLenz_orthonormalBasis_zero (m κ : ℝ) (x : V × V) :
    ⟪rungeLenz m κ x, b 0⟫_ℝ =
      ⟪x.2, b 1⟫_ℝ * angularMomentum (b 0) (b 1) x - m * κ * ⟪x.1, b 0⟫_ℝ / ‖x.1‖ := by
  simp only [rungeLenz, angularMomentum, inner_sub_left, real_inner_smul_left]
  rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner x.2 x.2,
    ← b.sum_inner_mul_inner x.1 x.2]
  simp only [Fin.sum_univ_two, real_inner_comm x.2]
  ring

/-- The second planar component of the Runge–Lenz vector is `-p₁ L - m κ q₂ / ‖q‖`. -/
theorem inner_rungeLenz_orthonormalBasis_one (m κ : ℝ) (x : V × V) :
    ⟪rungeLenz m κ x, b 1⟫_ℝ =
      -⟪x.2, b 0⟫_ℝ * angularMomentum (b 0) (b 1) x - m * κ * ⟪x.1, b 1⟫_ℝ / ‖x.1‖ := by
  simp only [rungeLenz, angularMomentum, inner_sub_left, real_inner_smul_left]
  rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner x.2 x.2,
    ← b.sum_inner_mul_inner x.1 x.2]
  simp only [Fin.sum_univ_two, real_inner_comm x.2]
  ring

end Plane

section KeplerOrbit

open InnerProductGeometry

/-- The radial component of the Runge–Lenz vector:
`⟪A, q⟫ = ‖q‖² ‖p‖² - ⟪q, p⟫² - m κ ‖q‖`. This holds everywhere, including on the collision set
`q = 0`, where both sides vanish. -/
theorem inner_rungeLenz_fst (m κ : ℝ) (x : V × V) :
    ⟪rungeLenz m κ x, x.1⟫_ℝ =
      ‖x.1‖ ^ 2 * ‖x.2‖ ^ 2 - ⟪x.1, x.2⟫_ℝ ^ 2 - m * κ * ‖x.1‖ := by
  rcases eq_or_ne x.1 0 with hq | hq
  · simp [rungeLenz, hq]
  · have hr : ‖x.1‖ ≠ 0 := norm_ne_zero_iff.2 hq
    simp only [rungeLenz, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      real_inner_comm x.2 x.1]
    field_simp

/-- **The Kepler orbit equation.** With `φ` the angle between the Runge–Lenz vector `A` and the
position `q`, `‖q‖ (m κ + ‖A‖ cos φ) = ‖q‖² ‖p‖² - ⟪q, p⟫²`. Since `A` and the angular momentum
are conserved, this is the equation of a conic with a focus at the origin and axis along `A`.
When `A = 0` it reads `m κ ‖q‖ = ℓ²`. -/
theorem norm_fst_mul_add_norm_rungeLenz_mul_cos_angle (m κ : ℝ) (x : V × V) :
    ‖x.1‖ * (m * κ + ‖rungeLenz m κ x‖ * Real.cos (angle (rungeLenz m κ x) x.1)) =
      ‖x.1‖ ^ 2 * ‖x.2‖ ^ 2 - ⟪x.1, x.2⟫_ℝ ^ 2 := by
  linear_combination (cos_angle_mul_norm_mul_norm (rungeLenz m κ x) x.1).trans
    (inner_rungeLenz_fst m κ x)

/-- **The eccentricity of a Kepler orbit.** Away from the collision set, the length of the
Runge–Lenz vector is `|m κ| e` for the eccentricity `e = √(1 + 2 H ℓ² / (m κ²))`, where
`ℓ² = ‖q‖² ‖p‖² - ⟪q, p⟫²` is the squared angular momentum and `H` the Kepler Hamiltonian. -/
theorem norm_rungeLenz_eq_abs_mul_sqrt {m κ : ℝ} (hm : m ≠ 0) (hκ : κ ≠ 0) {x : V × V}
    (hq : x.1 ≠ 0) :
    ‖rungeLenz m κ x‖ = |m * κ| * √(1 + 2 * centralForceHamiltonian m (fun r ↦ -κ / r) x *
      (‖x.1‖ ^ 2 * ‖x.2‖ ^ 2 - ⟪x.1, x.2⟫_ℝ ^ 2) / (m * κ ^ 2)) := by
  have h : (m * κ) ^ 2 * (1 + 2 * centralForceHamiltonian m (fun r ↦ -κ / r) x *
      (‖x.1‖ ^ 2 * ‖x.2‖ ^ 2 - ⟪x.1, x.2⟫_ℝ ^ 2) / (m * κ ^ 2)) = ‖rungeLenz m κ x‖ ^ 2 := by
    rw [norm_rungeLenz_sq hm κ hq]
    field_simp
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg _), h, Real.sqrt_sq (norm_nonneg _)]

/-- **Kepler orbits are conics.** For an attractive potential (`m, κ > 0`) and nonzero angular
momentum, `‖q‖ = ℓ² / (m κ (1 + e cos φ))`, where `ℓ² = ‖q‖² ‖p‖² - ⟪q, p⟫²`,
`e = √(1 + 2 H ℓ² / (m κ²))` is the eccentricity and `φ` is the angle between the position and
the Runge–Lenz vector. The hypothesis `ℓ² ≠ 0` excludes the collision set `q = 0`. -/
theorem norm_fst_eq_div_one_add_sqrt_mul_cos_angle {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ)
    {x : V × V} (hℓ : ‖x.1‖ ^ 2 * ‖x.2‖ ^ 2 - ⟪x.1, x.2⟫_ℝ ^ 2 ≠ 0) :
    ‖x.1‖ = (‖x.1‖ ^ 2 * ‖x.2‖ ^ 2 - ⟪x.1, x.2⟫_ℝ ^ 2) /
      (m * κ * (1 + √(1 + 2 * centralForceHamiltonian m (fun r ↦ -κ / r) x *
        (‖x.1‖ ^ 2 * ‖x.2‖ ^ 2 - ⟪x.1, x.2⟫_ℝ ^ 2) / (m * κ ^ 2)) *
          Real.cos (angle (rungeLenz m κ x) x.1))) := by
  have hq : x.1 ≠ 0 := by
    rintro hq
    simp [hq] at hℓ
  have h := norm_fst_mul_add_norm_rungeLenz_mul_cos_angle m κ x
  rw [norm_rungeLenz_eq_abs_mul_sqrt hm.ne' hκ.ne' hq, abs_of_pos (mul_pos hm hκ)] at h
  rw [eq_div_iff fun h0 ↦ hℓ (by rw [← h]; linear_combination ‖x.1‖ * h0)]
  linear_combination h

/-- **The collision set.** When the angular momentum vanishes, that is `⟪q, p⟫² = ‖q‖² ‖p‖²`,
the Runge–Lenz vector reduces to its radial term `-(m κ / ‖q‖) q`. -/
theorem rungeLenz_eq_neg_smul_of_inner_sq_eq (m κ : ℝ) {x : V × V}
    (hℓ : ⟪x.1, x.2⟫_ℝ ^ 2 = ‖x.1‖ ^ 2 * ‖x.2‖ ^ 2) :
    rungeLenz m κ x = -((m * κ / ‖x.1‖) • x.1) := by
  have h : ‖‖x.2‖ ^ 2 • x.1 - ⟪x.1, x.2⟫_ℝ • x.2‖ ^ 2 =
      ‖x.2‖ ^ 2 * (‖x.1‖ ^ 2 * ‖x.2‖ ^ 2 - ⟪x.1, x.2⟫_ℝ ^ 2) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_self_eq_norm_sq x.1, real_inner_self_eq_norm_sq x.2, real_inner_comm x.2 x.1]
    ring
  rw [hℓ, sub_self, mul_zero, sq_eq_zero_iff, norm_eq_zero] at h
  rw [rungeLenz, h, zero_sub]

/-- **Perihelion bound.** `‖q‖² ‖p‖² - ⟪q, p⟫² ≤ ‖q‖ (m κ + ‖A‖)`. Hence at a point with
nonzero angular momentum `ℓ`, the distance `‖q‖` is at least `ℓ² / (m κ + ‖A‖) > 0`; as `ℓ` and
`A` are conserved, such orbits stay away from the collision set. -/
theorem sq_sub_inner_sq_le_norm_fst_mul_add_norm_rungeLenz (m κ : ℝ) (x : V × V) :
    ‖x.1‖ ^ 2 * ‖x.2‖ ^ 2 - ⟪x.1, x.2⟫_ℝ ^ 2 ≤ ‖x.1‖ * (m * κ + ‖rungeLenz m κ x‖) := by
  have h := (abs_le.1 (abs_real_inner_le_norm (rungeLenz m κ x) x.1)).2
  rw [inner_rungeLenz_fst] at h
  linear_combination h

/-- **Aphelion bound.** `‖q‖ (m κ - ‖A‖) ≤ ‖q‖² ‖p‖² - ⟪q, p⟫²`. When `‖A‖ < m κ`, an orbit
stays at distance at most `ℓ² / (m κ - ‖A‖)` from the origin. -/
theorem norm_fst_mul_sub_norm_rungeLenz_le_sq_sub_inner_sq (m κ : ℝ) (x : V × V) :
    ‖x.1‖ * (m * κ - ‖rungeLenz m κ x‖) ≤ ‖x.1‖ ^ 2 * ‖x.2‖ ^ 2 - ⟪x.1, x.2⟫_ℝ ^ 2 := by
  have h := (abs_le.1 (abs_real_inner_le_norm (rungeLenz m κ x) x.1)).1
  rw [inner_rungeLenz_fst] at h
  linear_combination h

/-- **Bound states are ellipses.** For an attractive potential and nonzero angular momentum, the
eccentricity `‖A‖ / (m κ)` is less than one exactly when the energy is negative. -/
theorem norm_rungeLenz_lt_iff_centralForceHamiltonian_neg {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ)
    {x : V × V} (hℓ : ‖x.1‖ ^ 2 * ‖x.2‖ ^ 2 - ⟪x.1, x.2⟫_ℝ ^ 2 ≠ 0) :
    ‖rungeLenz m κ x‖ < m * κ ↔ centralForceHamiltonian m (fun r ↦ -κ / r) x < 0 := by
  have hq : x.1 ≠ 0 := by
    rintro hq
    simp [hq] at hℓ
  have hpos : 0 < ‖x.1‖ ^ 2 * ‖x.2‖ ^ 2 - ⟪x.1, x.2⟫_ℝ ^ 2 := by
    refine lt_of_le_of_ne ?_ hℓ.symm
    have := real_inner_mul_inner_self_le x.1 x.2
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at this
    linear_combination this
  rw [← sq_lt_sq₀ (norm_nonneg _) (mul_pos hm hκ).le, norm_rungeLenz_sq hm.ne' κ hq]
  constructor <;> intro h <;> nlinarith [mul_pos hm hpos]

omit [InnerProductSpace ℝ V] in
/-- **Negative-energy orbits are bounded.** If the Kepler energy `H` is negative, then
`‖q‖ ≤ κ / (-H)`. This includes the collision orbits with zero angular momentum. -/
theorem norm_fst_le_div_neg_centralForceHamiltonian {m κ : ℝ} (hm : 0 ≤ m) {x : V × V}
    (hH : centralForceHamiltonian m (fun r ↦ -κ / r) x < 0) :
    ‖x.1‖ ≤ κ / -centralForceHamiltonian m (fun r ↦ -κ / r) x := by
  have hp : 0 ≤ ‖x.2‖ ^ 2 / (2 * m) := by positivity
  have hr : 0 < ‖x.1‖ := by
    refine (norm_nonneg _).lt_of_ne fun h ↦ ?_
    rw [centralForceHamiltonian, ← h, div_zero, add_zero] at hH
    linarith
  rw [le_div_iff₀ (neg_pos.2 hH), centralForceHamiltonian]
  rw [centralForceHamiltonian] at hH
  have hk : -κ / ‖x.1‖ * ‖x.1‖ = -κ := div_mul_cancel₀ _ hr.ne'
  nlinarith

end KeplerOrbit

variable [FiniteDimensional ℝ V]

/-- **Hamilton's equations for a central force.** Away from the collision set, the Hamiltonian
vector field of `‖p‖² / (2m) + U(‖q‖)` is `(p / m, -(U'(‖q‖) / ‖q‖) q)`. -/
theorem stdSymplecticForm_hamiltonianVectorField_centralForceHamiltonian {m : ℝ} {U : ℝ → ℝ}
    {U' : ℝ} {x : V × V} (hU : HasDerivAt U U' ‖x.1‖) (hq : x.1 ≠ 0) :
    (stdSymplecticForm (V := V)).hamiltonianVectorField (centralForceHamiltonian m U) x =
      (m⁻¹ • x.2, -((U' / ‖x.1‖) • x.1)) :=
  stdSymplecticForm_hamiltonianVectorField (hasFDerivAt_centralForceHamiltonian hU hq)

/-- **Angular momentum generates rotations.** The Hamiltonian vector field of the angular momentum
in the plane of `u` and `w` is `(R q, R p)` for the infinitesimal rotation
`R z = ⟪z, u⟫ w - ⟪z, w⟫ u`. -/
theorem stdSymplecticForm_hamiltonianVectorField_angularMomentum (u w : V) (x : V × V) :
    (stdSymplecticForm (V := V)).hamiltonianVectorField (angularMomentum u w) x =
      (⟪x.1, u⟫_ℝ • w - ⟪x.1, w⟫_ℝ • u, ⟪x.2, u⟫_ℝ • w - ⟪x.2, w⟫_ℝ • u) := by
  rw [stdSymplecticForm_hamiltonianVectorField (hasFDerivAt_angularMomentum u w x), neg_sub]

/-- **Conservation of angular momentum.** Away from the collision set, every component of the
angular momentum Poisson-commutes with a central-force Hamiltonian. -/
theorem stdSymplecticForm_poissonBracket_centralForceHamiltonian_angularMomentum {m : ℝ}
    {U : ℝ → ℝ} {U' : ℝ} {x : V × V} (hU : HasDerivAt U U' ‖x.1‖) (hq : x.1 ≠ 0) (u w : V) :
    (stdSymplecticForm (V := V)).poissonBracket (centralForceHamiltonian m U)
      (angularMomentum u w) x = 0 := by
  rw [stdSymplecticForm_poissonBracket (hasFDerivAt_centralForceHamiltonian hU hq)
    (hasFDerivAt_angularMomentum u w x)]
  simp [inner_sub_right, real_inner_smul_right, real_inner_comm]
  ring

/-- **Conservation of the Runge–Lenz vector.** Away from the collision set, every component of the
Runge–Lenz vector Poisson-commutes with the Kepler Hamiltonian `‖p‖² / (2m) - κ / ‖q‖`. -/
theorem stdSymplecticForm_poissonBracket_inner_rungeLenz {m : ℝ} (hm : m ≠ 0) (κ : ℝ) (e : V)
    {x : V × V} (hq : x.1 ≠ 0) :
    (stdSymplecticForm (V := V)).poissonBracket (fun y ↦ ⟪rungeLenz m κ y, e⟫_ℝ)
      (centralForceHamiltonian m fun r ↦ -κ / r) x = 0 := by
  have hr : ‖x.1‖ ≠ 0 := norm_ne_zero_iff.2 hq
  have hU : HasDerivAt (fun r ↦ -κ / r) (κ / ‖x.1‖ ^ 2) ‖x.1‖ := by
    simpa [div_eq_mul_inv] using (hasDerivAt_inv hr).const_mul (-κ)
  rw [stdSymplecticForm_poissonBracket (hasFDerivAt_inner_rungeLenz m κ e hq)
    (hasFDerivAt_centralForceHamiltonian hU hq)]
  simp [inner_sub_left, inner_add_left, real_inner_smul_right, real_inner_comm]
  field_simp
  ring

end TauCeti
