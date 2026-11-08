/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Integrable
public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Radial
public import TauCeti.Geometry.Symplectic.Prod.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic

import TauCeti.Analysis.InnerProductSpace.Orthonormal.Sum

/-!
# Polar canonical coordinates for planar central forces

Let `u, w` be an orthonormal pair in a real inner product space `V`, spanning a plane with polar
coordinates `q = r (cos θ u + sin θ w)`. The unit vectors of these coordinates are
`e_r = cos θ u + sin θ w` (`TauCeti.polarRadialUnit`) and `e_θ = -sin θ u + cos θ w`
(`TauCeti.polarAngularUnit`). The cotangent lift of polar coordinates is the map

`(r, p_r, θ, L) ↦ (r e_r, p_r e_r + (L / r) e_θ)`

(`TauCeti.polarCanonical`) to the phase space `V × V`: its momentum is the covector with
`p(∂_r q) = p_r` and `p(∂_θ q) = L`. Its source is `(ℝ × ℝ) × (ℝ × ℝ)`, grouped as the two
canonical pairs `((r, p_r), (θ, L))`. For `r ≠ 0`:

* it pulls the Liouville form `⟪p, dq⟫` back to `p_r dr + L dθ`
  (`TauCeti.inner_snd_polarCanonical_fderiv_fst`);
* hence it pulls the standard form `ω₀ = Σ dqᵢ ∧ dpᵢ` back to `dr ∧ dp_r + dθ ∧ dL`, the direct sum
  of the standard forms of the two canonical planes
  (`TauCeti.stdSymplecticForm_fderiv_polarCanonical`);
* the angular momentum `q₁ p₂ - q₂ p₁` in the frame `(u, w)` is `L`
  (`TauCeti.angularMomentum_polarCanonical`); if moreover `r > 0`, then `‖q‖ = r` and the radial
  momentum `⟪q, p⟫ / ‖q‖` is `p_r` (`TauCeti.norm_fst_polarCanonical`,
  `TauCeti.radialMomentum_polarCanonical`).

So `(r, θ, p_r, L)` are canonical coordinates in which a central-force Hamiltonian
`H = ‖p‖² / (2m) + U(‖q‖)` becomes `p_r² / (2m) + U_L(r)`, with the effective potential
`U_L(r) = L² / (2 m r²) + U(r)` (`TauCeti.centralForceHamiltonian_polarCanonical`). Its Hamiltonian
vector field in these coordinates is `(r', p_r', θ', L') = (p_r / m, -U_L'(r), L / (m r²), 0)`: the
derivative of the parametrization carries this field to the Hamiltonian vector field of `H`
(`TauCeti.fderiv_polarCanonical_apply_eq_hamiltonianVectorField`). So a curve whose derivative
at `t` is given by these polar Hamilton equations is carried to a curve whose derivative at `t` is
the Hamiltonian vector field of `H` (`TauCeti.hasDerivAt_polarCanonical_comp`). Since `(r, p_r)` is
the radial projection `(‖q‖, ⟪q, p⟫ / ‖q‖)` of the point, the reduction at a fixed angular momentum
`L = ℓ` to the reduced Hamiltonian `p_r² / (2m) + U_ℓ(r)` on the half-line `r > 0` is the radial
reduction `TauCeti.hasDerivAt_radialProjection_comp`: in the plane of an orthonormal basis, its
squared angular momentum `‖q‖² ‖p‖² - ⟪q, p⟫²` is `L²` (`TauCeti.sq_angularMomentum`).

The parametrization is `2π`-periodic in `θ`. The angle `θ ∈ ℝ / 2πℤ` of a nonzero position in the
plane of `u` and `w` is `TauCeti.polarAngle u w`. For an orthonormal basis `b` of a plane `V`, it is
Mathlib's oriented angle from `b₀` for the orientation of `b` (`TauCeti.polarAngle_eq_oangle`), and
the polar coordinates `(r, p_r, θ, L)`, with `r > 0` and `θ ∈ ℝ / 2πℤ`, put
`(0, ∞) × ℝ × (ℝ / 2πℤ) × ℝ` in bijection with the punctured phase space `{(q, p) | q ≠ 0}`
(`TauCeti.polarCanonicalEquiv`).

## Main definitions

* `TauCeti.polarRadialUnit`, `TauCeti.polarAngularUnit`: the polar unit vectors `e_r`, `e_θ`.
* `TauCeti.polarCanonical`: the cotangent lift `(r, p_r, θ, L) ↦ (r e_r, p_r e_r + (L / r) e_θ)`.
* `TauCeti.polarAngle`: the angle of a position, in `Real.Angle = ℝ / 2πℤ`.
* `TauCeti.polarCanonicalEquiv`: the global polar canonical coordinates, a bijection onto the
  punctured phase space of the plane.

## Main results

* `TauCeti.contDiffAt_polarCanonical`: the parametrization is smooth off `r = 0`.
* `TauCeti.inner_snd_polarCanonical_fderiv_fst`: `λ = p_r dr + L dθ`.
* `TauCeti.stdSymplecticForm_fderiv_polarCanonical`: `ω₀ = dr ∧ dp_r + dθ ∧ dL`.
* `TauCeti.centralForceHamiltonian_polarCanonical`: `H = p_r² / (2m) + U_L(r)`.
* `TauCeti.fderiv_polarCanonical_apply_eq_hamiltonianVectorField`,
  `TauCeti.hasDerivAt_polarCanonical_comp`: Hamilton's equations in polar coordinates.
* `TauCeti.polarCanonical_eq_polarCanonical_iff`: for `r, r' > 0` two points agree exactly when
  their coordinates agree, with the angles compared modulo `2π`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 8 (motion in a central field, in polar coordinates).
* H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., Addison-Wesley, 2002,
  Chapters 3 and 8 (the central-force problem, and its Hamiltonian in polar coordinates).
-/

public section

open Real
open scoped InnerProductSpace

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ### The polar unit vectors -/

/-- The radial unit vector `e_r = cos θ u + sin θ w` of polar coordinates in the plane of `u`
and `w`. -/
noncomputable def polarRadialUnit (u w : V) (θ : ℝ) : V :=
  Real.cos θ • u + Real.sin θ • w

/-- The angular unit vector `e_θ = -sin θ u + cos θ w` of polar coordinates in the plane of `u`
and `w`, the derivative of `e_r` in `θ`. -/
noncomputable def polarAngularUnit (u w : V) (θ : ℝ) : V :=
  -Real.sin θ • u + Real.cos θ • w

/-- The defining formula of the radial unit vector. -/
theorem polarRadialUnit_apply (u w : V) (θ : ℝ) :
    polarRadialUnit u w θ = Real.cos θ • u + Real.sin θ • w :=
  (rfl)

/-- The defining formula of the angular unit vector. -/
theorem polarAngularUnit_apply (u w : V) (θ : ℝ) :
    polarAngularUnit u w θ = -Real.sin θ • u + Real.cos θ • w :=
  (rfl)

/-- The radial unit vector turns at unit speed in the angular direction: `de_r / dθ = e_θ`. -/
theorem hasDerivAt_polarRadialUnit (u w : V) (θ : ℝ) :
    HasDerivAt (polarRadialUnit u w) (polarAngularUnit u w θ) θ := by
  have h := ((Real.hasDerivAt_cos θ).smul_const u).add ((Real.hasDerivAt_sin θ).smul_const w)
  refine h.congr_deriv ?_
  simp only [polarAngularUnit, neg_smul]

/-- The angular unit vector turns at unit speed towards the origin: `de_θ / dθ = -e_r`. -/
theorem hasDerivAt_polarAngularUnit (u w : V) (θ : ℝ) :
    HasDerivAt (polarAngularUnit u w) (-polarRadialUnit u w θ) θ := by
  have h := ((Real.hasDerivAt_sin θ).neg.smul_const u).add ((Real.hasDerivAt_cos θ).smul_const w)
  refine h.congr_deriv ?_
  simp only [polarRadialUnit, neg_smul, neg_add]

/-- The radial unit vector is a smooth function of the angle. -/
theorem contDiff_polarRadialUnit (u w : V) {n : WithTop ℕ∞} :
    ContDiff ℝ n (polarRadialUnit u w) := by
  unfold polarRadialUnit
  fun_prop

/-- The angular unit vector is a smooth function of the angle. -/
theorem contDiff_polarAngularUnit (u w : V) {n : WithTop ℕ∞} :
    ContDiff ℝ n (polarAngularUnit u w) := by
  unfold polarAngularUnit
  fun_prop

/-- The radial unit vector `e_r` only depends on `θ` modulo `2π`. -/
theorem polarRadialUnit_eq_of_coe_eq (u w : V) {θ θ' : ℝ} (h : (θ : Real.Angle) = θ') :
    polarRadialUnit u w θ = polarRadialUnit u w θ' := by
  rw [polarRadialUnit, polarRadialUnit, ← Real.Angle.cos_coe, ← Real.Angle.sin_coe, h,
    Real.Angle.cos_coe, Real.Angle.sin_coe]

/-- The angular unit vector `e_θ` only depends on `θ` modulo `2π`. -/
theorem polarAngularUnit_eq_of_coe_eq (u w : V) {θ θ' : ℝ} (h : (θ : Real.Angle) = θ') :
    polarAngularUnit u w θ = polarAngularUnit u w θ' := by
  rw [polarAngularUnit, polarAngularUnit, ← Real.Angle.cos_coe, ← Real.Angle.sin_coe, h,
    Real.Angle.cos_coe, Real.Angle.sin_coe]

section Orthonormal

variable {u w : V} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (huw : ⟪u, w⟫_ℝ = 0)
include hu hw huw

/-- The polar unit vectors form an orthonormal pair: `⟪e_r, e_r⟫ = 1`. -/
theorem inner_polarRadialUnit_self (θ : ℝ) :
    ⟪polarRadialUnit u w θ, polarRadialUnit u w θ⟫_ℝ = 1 := by
  simp only [polarRadialUnit, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, huw, real_inner_comm u w]
  simp only [real_inner_self_eq_norm_sq, hu, hw]
  linear_combination cos_sq_add_sin_sq θ

/-- The polar unit vectors form an orthonormal pair: `⟪e_θ, e_θ⟫ = 1`. -/
theorem inner_polarAngularUnit_self (θ : ℝ) :
    ⟪polarAngularUnit u w θ, polarAngularUnit u w θ⟫_ℝ = 1 := by
  simp only [polarAngularUnit, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, huw, real_inner_comm u w]
  simp only [real_inner_self_eq_norm_sq, hu, hw]
  linear_combination sin_sq_add_cos_sq θ

/-- The polar unit vectors form an orthonormal pair: `⟪e_r, e_θ⟫ = 0`. -/
@[simp]
theorem inner_polarRadialUnit_polarAngularUnit (θ : ℝ) :
    ⟪polarRadialUnit u w θ, polarAngularUnit u w θ⟫_ℝ = 0 := by
  simp only [polarRadialUnit, polarAngularUnit, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, huw, real_inner_comm u w]
  simp only [real_inner_self_eq_norm_sq, hu, hw]
  ring

@[simp]
theorem inner_polarAngularUnit_polarRadialUnit (θ : ℝ) :
    ⟪polarAngularUnit u w θ, polarRadialUnit u w θ⟫_ℝ = 0 := by
  rw [real_inner_comm, inner_polarRadialUnit_polarAngularUnit hu hw huw]

/-- The polar unit vectors have unit length: `‖e_r‖ = 1`. -/
@[simp]
theorem norm_polarRadialUnit (θ : ℝ) : ‖polarRadialUnit u w θ‖ = 1 := by
  have h := inner_polarRadialUnit_self hu hw huw θ
  rwa [real_inner_self_eq_norm_sq, pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero] at h

/-- The polar unit vectors have unit length: `‖e_θ‖ = 1`. -/
@[simp]
theorem norm_polarAngularUnit (θ : ℝ) : ‖polarAngularUnit u w θ‖ = 1 := by
  have h := inner_polarAngularUnit_self hu hw huw θ
  rwa [real_inner_self_eq_norm_sq, pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero] at h

/-- In the frame `(e_r, e_θ)`, the inner product of `a e_r + b e_θ` and `c e_r + d e_θ` is
`a c + b d`. -/
private theorem inner_polar_smul_add_smul (θ a b c d : ℝ) :
    ⟪a • polarRadialUnit u w θ + b • polarAngularUnit u w θ,
        c • polarRadialUnit u w θ + d • polarAngularUnit u w θ⟫_ℝ = a * c + b * d := by
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    inner_polarRadialUnit_self hu hw huw, inner_polarAngularUnit_self hu hw huw,
    inner_polarRadialUnit_polarAngularUnit hu hw huw,
    inner_polarAngularUnit_polarRadialUnit hu hw huw]
  ring

end Orthonormal

/-! ### The polar canonical parametrization -/

/-- The **polar canonical parametrization** `(r, p_r, θ, L) ↦ (r e_r, p_r e_r + (L / r) e_θ)` of
the phase space `V × V` over the plane of `u` and `w`, the cotangent lift of the polar
coordinates `(r, θ) ↦ r e_r`. Its source is grouped as the two canonical pairs
`((r, p_r), (θ, L))`. -/
noncomputable def polarCanonical (u w : V) (x : (ℝ × ℝ) × (ℝ × ℝ)) : V × V :=
  (x.1.1 • polarRadialUnit u w x.2.1,
    x.1.2 • polarRadialUnit u w x.2.1 + (x.2.2 / x.1.1) • polarAngularUnit u w x.2.1)

@[simp]
theorem polarCanonical_apply (u w : V) (r pᵣ θ L : ℝ) :
    polarCanonical u w ((r, pᵣ), (θ, L)) =
      (r • polarRadialUnit u w θ, pᵣ • polarRadialUnit u w θ + (L / r) • polarAngularUnit u w θ) :=
  (rfl)

/-- The position of the polar canonical parametrization is Mathlib's inverse polar coordinates
`(r, θ) ↦ (r cos θ, r sin θ)` (`polarCoord.symm`), read in the frame `(u, w)`. -/
theorem fst_polarCanonical (u w : V) (x : (ℝ × ℝ) × (ℝ × ℝ)) :
    (polarCanonical u w x).1 =
      (polarCoord.symm (x.1.1, x.2.1)).1 • u + (polarCoord.symm (x.1.1, x.2.1)).2 • w := by
  simp [polarCanonical, polarCoord_symm_apply, polarRadialUnit, smul_add, smul_smul]

/-- The polar canonical parametrization only depends on the angle modulo `2π`. -/
theorem polarCanonical_eq_of_coe_eq (u w : V) {θ θ' : ℝ} (h : (θ : Real.Angle) = θ')
    (r pᵣ L : ℝ) :
    polarCanonical u w ((r, pᵣ), (θ, L)) = polarCanonical u w ((r, pᵣ), (θ', L)) := by
  rw [polarCanonical_apply, polarCanonical_apply, polarRadialUnit_eq_of_coe_eq u w h,
    polarAngularUnit_eq_of_coe_eq u w h]

/-- The polar canonical parametrization is smooth off the collision set `r = 0`. -/
theorem contDiffAt_polarCanonical (u w : V) {n : WithTop ℕ∞} {x : (ℝ × ℝ) × (ℝ × ℝ)}
    (hr : x.1.1 ≠ 0) : ContDiffAt ℝ n (polarCanonical u w) x := by
  have hE := contDiff_polarRadialUnit u w (n := n)
  have hE' := contDiff_polarAngularUnit u w (n := n)
  unfold polarCanonical
  fun_prop (disch := exact hr)

/-- The derivative of the polar canonical parametrization at a point with `r ≠ 0`: it sends
`((δr, δp_r), (δθ, δL))` to the pair
`(δr e_r + r δθ e_θ, (δp_r - L δθ / r) e_r + (p_r δθ + δL / r - L δr / r²) e_θ)`. -/
theorem fderiv_polarCanonical_apply (u w : V) {x : (ℝ × ℝ) × (ℝ × ℝ)} (hr : x.1.1 ≠ 0)
    (δ : (ℝ × ℝ) × (ℝ × ℝ)) :
    fderiv ℝ (polarCanonical u w) x δ =
      (δ.1.1 • polarRadialUnit u w x.2.1 + (x.1.1 * δ.2.1) • polarAngularUnit u w x.2.1,
        (δ.1.2 - x.2.2 * δ.2.1 / x.1.1) • polarRadialUnit u w x.2.1 +
          (x.1.2 * δ.2.1 + δ.2.2 / x.1.1 - x.2.2 * δ.1.1 / x.1.1 ^ 2) •
            polarAngularUnit u w x.2.1) := by
  -- Compare the derivative of the parametrization along the line `t ↦ x + t δ` with the
  -- derivative computed one coordinate at a time.
  have hdiff := (contDiffAt_polarCanonical u w (n := 1) hr).differentiableAt one_ne_zero
  have hline : HasDerivAt (fun t : ℝ ↦ x + t • δ) δ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const δ).const_add x
  have h₁ := hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  have hcoord (a b : ℝ) : HasDerivAt (fun t : ℝ ↦ a + t * b) b 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const b).const_add a
  have hr₀ := hcoord x.1.1 δ.1.1
  have hθ₀ := hcoord x.2.1 δ.2.1
  have he := (hasDerivAt_polarRadialUnit u w x.2.1).scomp_of_eq (0 : ℝ) hθ₀ (by simp)
  have he' := (hasDerivAt_polarAngularUnit u w x.2.1).scomp_of_eq (0 : ℝ) hθ₀ (by simp)
  have h₂ := (hr₀.smul he).prodMk (((hcoord x.1.2 δ.1.2).smul he).add
    (((hcoord x.2.2 δ.2.2).div hr₀ (by simpa using hr)).smul he'))
  rw [h₁.unique (h₂.congr_of_eventuallyEq (.of_forall fun t ↦ ?_))]
  · simp only [Pi.div_apply, zero_mul, add_zero, Function.comp_apply]
    ext
    · simp only [smul_smul]
      module
    · simp only [smul_neg, smul_smul]
      match_scalars <;> field_simp <;> ring
  · simp [polarCanonical]

section Orthonormal

variable {u w : V} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (huw : ⟪u, w⟫_ℝ = 0)
include hu hw huw

/-! ### Polar coordinates are canonical -/

/-- **The Liouville form in polar coordinates is `p_r dr + L dθ`.** At a point with `r ≠ 0`, the
Liouville form `⟪p, dq⟫` of `V × V` pulls back along the polar canonical parametrization to the
one-form sending `((δr, δp_r), (δθ, δL))` to `p_r δr + L δθ`. -/
theorem inner_snd_polarCanonical_fderiv_fst {x : (ℝ × ℝ) × (ℝ × ℝ)} (hr : x.1.1 ≠ 0)
    (δ : (ℝ × ℝ) × (ℝ × ℝ)) :
    ⟪(polarCanonical u w x).2, (fderiv ℝ (polarCanonical u w) x δ).1⟫_ℝ =
      x.1.2 * δ.1.1 + x.2.2 * δ.2.1 := by
  rw [fderiv_polarCanonical_apply u w hr, polarCanonical,
    inner_polar_smul_add_smul hu hw huw]
  field_simp

/-- **Polar coordinates are canonical.** At a point with `r ≠ 0`, the polar canonical
parametrization pulls the standard form `ω₀ = Σ dqᵢ ∧ dpᵢ` of `V × V` back to
`dr ∧ dp_r + dθ ∧ dL`, the direct sum of the standard forms of the canonical planes `(r, p_r)` and
`(θ, L)`. -/
theorem stdSymplecticForm_fderiv_polarCanonical {x : (ℝ × ℝ) × (ℝ × ℝ)} (hr : x.1.1 ≠ 0)
    (δ δ' : (ℝ × ℝ) × (ℝ × ℝ)) :
    stdSymplecticForm (fderiv ℝ (polarCanonical u w) x δ) (fderiv ℝ (polarCanonical u w) x δ') =
      ((stdSymplecticForm (V := ℝ)).prod (stdSymplecticForm (V := ℝ))) δ δ' := by
  rw [stdSymplecticForm_apply, fderiv_polarCanonical_apply u w hr,
    fderiv_polarCanonical_apply u w hr, inner_polar_smul_add_smul hu hw huw,
    inner_polar_smul_add_smul hu hw huw, SymplecticForm.prod_apply, stdSymplecticForm_apply,
    stdSymplecticForm_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  field_simp
  ring

/-! ### Recovering the coordinates -/

/-- The position of the point with polar coordinates `(r, p_r, θ, L)` has length `|r|`. -/
@[simp]
theorem norm_fst_polarCanonical (x : (ℝ × ℝ) × (ℝ × ℝ)) :
    ‖(polarCanonical u w x).1‖ = |x.1.1| := by
  rw [polarCanonical, norm_smul, norm_polarRadialUnit hu hw huw, mul_one, Real.norm_eq_abs]

/-- The radial momentum `⟪q, p⟫ / ‖q‖` of the point with polar coordinates `(r, p_r, θ, L)`,
`r > 0`, is `p_r`. -/
@[simp]
theorem radialMomentum_polarCanonical {x : (ℝ × ℝ) × (ℝ × ℝ)} (hr : 0 < x.1.1) :
    radialMomentum (polarCanonical u w x) = x.1.2 := by
  rw [radialMomentum_def, norm_fst_polarCanonical hu hw huw, abs_of_pos hr]
  have h := inner_polar_smul_add_smul hu hw huw x.2.1 x.1.1 0 x.1.2 (x.2.2 / x.1.1)
  rw [zero_smul, add_zero] at h
  rw [polarCanonical, h]
  field_simp
  ring

/-- The angular momentum `q₁ p₂ - q₂ p₁` in the frame `(u, w)` of the point with polar coordinates
`(r, p_r, θ, L)`, `r ≠ 0`, is `L`. -/
@[simp]
theorem angularMomentum_polarCanonical {x : (ℝ × ℝ) × (ℝ × ℝ)} (hr : x.1.1 ≠ 0) :
    angularMomentum u w (polarCanonical u w x) = x.2.2 := by
  have hwu : ⟪w, u⟫_ℝ = 0 := by rwa [real_inner_comm]
  simp only [angularMomentum_apply, polarCanonical, polarRadialUnit, polarAngularUnit,
    inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hu, hw, huw, hwu]
  field_simp
  linear_combination x.2.2 * cos_sq_add_sin_sq x.2.1

/-- **The central-force Hamiltonian in polar coordinates.** At the point with polar coordinates
`(r, p_r, θ, L)`, `r > 0`, the energy `‖p‖² / (2m) + U(‖q‖)` is `p_r² / (2m) + U_L(r)`, with the
effective potential `U_L(r) = L² / (2 m r²) + U(r)`. -/
theorem centralForceHamiltonian_polarCanonical (m : ℝ) (U : ℝ → ℝ) {x : (ℝ × ℝ) × (ℝ × ℝ)}
    (hr : 0 < x.1.1) :
    centralForceHamiltonian m U (polarCanonical u w x) =
      x.1.2 ^ 2 / (2 * m) + effectivePotential m x.2.2 U x.1.1 := by
  rw [← Prod.mk.eta (p := polarCanonical u w x), centralForceHamiltonian_apply,
    norm_fst_polarCanonical hu hw huw, abs_of_pos hr,
    effectivePotential_apply, ← real_inner_self_eq_norm_sq, polarCanonical,
    inner_polar_smul_add_smul hu hw huw]
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · field_simp
    ring

/-! ### Hamilton's equations in polar coordinates -/

variable [FiniteDimensional ℝ V]

/-- **Hamilton's equations in polar coordinates.** At a point with `r > 0` where the potential
has derivative `U'`, the derivative of the polar canonical parametrization carries
`(r', p_r', θ', L') = (p_r / m, L² / (m r³) - U'(r), L / (m r²), 0)` to the Hamiltonian vector field
of the central-force Hamiltonian. These components are `∂H/∂p_r`, `-∂H/∂r`, `∂H/∂L` and
`-∂H/∂θ` for `H = p_r² / (2m) + U_L(r)`, using `U_L'(r) = U'(r) - L² / (m r³)`
(`TauCeti.hasDerivAt_effectivePotential`). -/
theorem fderiv_polarCanonical_apply_eq_hamiltonianVectorField {m : ℝ} {U : ℝ → ℝ} {U' : ℝ}
    {x : (ℝ × ℝ) × (ℝ × ℝ)} (hr : 0 < x.1.1) (hU : HasDerivAt U U' x.1.1) :
    fderiv ℝ (polarCanonical u w) x
        ((x.1.2 / m, x.2.2 ^ 2 / (m * x.1.1 ^ 3) - U'), (x.2.2 / (m * x.1.1 ^ 2), 0)) =
      (stdSymplecticForm (V := V)).hamiltonianVectorField (centralForceHamiltonian m U)
        (polarCanonical u w x) := by
  have hq : (polarCanonical u w x).1 ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_fst_polarCanonical hu hw huw]
    exact (abs_pos.2 hr.ne').ne'
  rw [stdSymplecticForm_hamiltonianVectorField_centralForceHamiltonian (U' := U')
      (by rwa [norm_fst_polarCanonical hu hw huw, abs_of_pos hr]) hq,
    norm_fst_polarCanonical hu hw huw, abs_of_pos hr, fderiv_polarCanonical_apply u w hr.ne',
    polarCanonical]
  rcases eq_or_ne m 0 with rfl | hm
  · ext <;> simp [smul_smul, div_mul_cancel₀ _ hr.ne']
  ext
  · simp only [smul_add, smul_smul]
    match_scalars <;> field_simp
  · simp only [smul_smul]
    match_scalars <;> field_simp <;> ring

/-- **Hamilton's equations in polar coordinates, along a curve.** Let `γ = ((r, p_r), (θ, L))` be a
curve with `r > 0` at time `t`, whose derivative at `t` is given by the polar Hamilton equations
`r' = p_r / m`, `p_r' = L² / (m r³) - U'(r)`, `θ' = L / (m r²)` and `L' = 0`. Then
`polarCanonical ∘ γ` has derivative at `t` equal to the Hamiltonian vector field of the
central-force Hamiltonian. This statement only concerns the single time `t`; the reduction of
the radial motion `(r, p_r)` at a fixed angular momentum is
`TauCeti.hasDerivAt_radialProjection_comp`. -/
theorem hasDerivAt_polarCanonical_comp {m : ℝ} {U U' : ℝ → ℝ} {γ : ℝ → (ℝ × ℝ) × (ℝ × ℝ)}
    {t : ℝ} (hr : 0 < (γ t).1.1) (hU : HasDerivAt U (U' (γ t).1.1) (γ t).1.1)
    (hγ : HasDerivAt γ (((γ t).1.2 / m, (γ t).2.2 ^ 2 / (m * (γ t).1.1 ^ 3) - U' (γ t).1.1),
      ((γ t).2.2 / (m * (γ t).1.1 ^ 2), 0)) t) :
    HasDerivAt (fun s ↦ polarCanonical u w (γ s))
      ((stdSymplecticForm (V := V)).hamiltonianVectorField (centralForceHamiltonian m U)
        (polarCanonical u w (γ t))) t := by
  rw [← fderiv_polarCanonical_apply_eq_hamiltonianVectorField hu hw huw hr hU]
  exact ((contDiffAt_polarCanonical u w (n := 1) hr.ne').differentiableAt
    one_ne_zero).hasFDerivAt.comp_hasDerivAt t hγ

end Orthonormal

/-! ### The polar angle and global polar coordinates -/

section Angle

/-- The **polar angle** of a position `q` in the frame `(u, w)`, a point of
`Real.Angle = ℝ / 2πℤ`: the argument of `⟪q, u⟫ + i ⟪q, w⟫`. It is `0` at the origin. -/
noncomputable def polarAngle (u w : V) (q : V) : Real.Angle :=
  Complex.arg ⟨⟪q, u⟫_ℝ, ⟪q, w⟫_ℝ⟩

theorem polarAngle_apply (u w : V) (q : V) :
    polarAngle u w q = (Complex.arg ⟨⟪q, u⟫_ℝ, ⟪q, w⟫_ℝ⟩ : Real.Angle) :=
  (rfl)

/-- The polar angle of the origin is `0`. -/
@[simp]
theorem polarAngle_zero (u w : V) : polarAngle u w 0 = 0 := by
  have h : (⟨⟪(0 : V), u⟫_ℝ, ⟪(0 : V), w⟫_ℝ⟩ : ℂ) = 0 :=
    Complex.ext (by simp) (by simp)
  rw [polarAngle, h, Complex.arg_zero, Real.Angle.coe_zero]

/-- For an orthonormal basis `b` of a plane, the polar angle in the frame `(b₀, b₁)` is the
argument of the complex coordinate of `q` given by `Complex.isometryOfOrthonormal b`. -/
theorem polarAngle_eq_arg_isometryOfOrthonormal_symm (b : OrthonormalBasis (Fin 2) ℝ V) (q : V) :
    polarAngle (b 0) (b 1) q = Complex.arg ((Complex.isometryOfOrthonormal b).symm q) := by
  rw [polarAngle, Complex.isometryOfOrthonormal_symm_apply_eq_mk]

/-- For an orthonormal basis `b` of an oriented plane, the polar angle in the frame `(b₀, b₁)` is
Mathlib's oriented angle from `b₀` to `q` for the orientation of `b`. -/
theorem polarAngle_eq_oangle [Fact (Module.finrank ℝ V = 2)] (b : OrthonormalBasis (Fin 2) ℝ V)
    (q : V) : polarAngle (b 0) (b 1) q = b.toBasis.orientation.oangle (b 0) q := by
  set e := Complex.isometryOfOrthonormal b
  have he : Orientation.map (Fin 2) e.symm.toLinearEquiv b.toBasis.orientation =
      Complex.orientation := by
    rw [← Module.Basis.orientation_map, Complex.orientation]
    congr 1
    ext i
    fin_cases i <;>
      simp [e, Complex.isometryOfOrthonormal_symm_apply_eq_mk, Complex.ext_iff, b.inner_eq_ite]
  rw [Orientation.oangle_map_complex _ e.symm he, polarAngle_eq_arg_isometryOfOrthonormal_symm]
  congr 2
  simp [e, Complex.isometryOfOrthonormal_symm_apply_eq_mk, Complex.ext_iff, b.inner_eq_ite]

/-- For an orthonormal basis `b` of a plane, `‖q‖ cos θ = ⟪q, b₀⟫`, where `θ` is the polar angle
of `q` in the frame `(b₀, b₁)`. -/
theorem norm_mul_cos_polarAngle (b : OrthonormalBasis (Fin 2) ℝ V) (q : V) :
    ‖q‖ * Real.Angle.cos (polarAngle (b 0) (b 1) q) = ⟪q, b 0⟫_ℝ := by
  rw [← (Complex.isometryOfOrthonormal b).symm.norm_map q,
    polarAngle_eq_arg_isometryOfOrthonormal_symm, Real.Angle.cos_coe, Complex.norm_mul_cos_arg,
    Complex.isometryOfOrthonormal_symm_apply_eq_mk]

/-- For an orthonormal basis `b` of a plane, `‖q‖ sin θ = ⟪q, b₁⟫`, where `θ` is the polar angle
of `q` in the frame `(b₀, b₁)`. -/
theorem norm_mul_sin_polarAngle (b : OrthonormalBasis (Fin 2) ℝ V) (q : V) :
    ‖q‖ * Real.Angle.sin (polarAngle (b 0) (b 1) q) = ⟪q, b 1⟫_ℝ := by
  rw [← (Complex.isometryOfOrthonormal b).symm.norm_map q,
    polarAngle_eq_arg_isometryOfOrthonormal_symm, Real.Angle.sin_coe, Complex.norm_mul_sin_arg,
    Complex.isometryOfOrthonormal_symm_apply_eq_mk]

section Orthonormal

variable {u w : V} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (huw : ⟪u, w⟫_ℝ = 0)
include hu hw huw

/-- The angle of the point with polar coordinates `(r, p_r, θ, L)`, `r > 0`, is `θ` modulo
`2π`. -/
@[simp]
theorem polarAngle_polarCanonical {x : (ℝ × ℝ) × (ℝ × ℝ)} (hr : 0 < x.1.1) :
    polarAngle u w (polarCanonical u w x).1 = x.2.1 := by
  have hwu : ⟪w, u⟫_ℝ = 0 := by rwa [real_inner_comm]
  have h : (⟨⟪(polarCanonical u w x).1, u⟫_ℝ, ⟪(polarCanonical u w x).1, w⟫_ℝ⟩
      : ℂ) = (x.1.1 : ℂ) * (Real.Angle.cos x.2.1 + Real.Angle.sin x.2.1 * Complex.I) := by
    apply Complex.ext <;>
      simp [polarCanonical, polarRadialUnit, inner_add_left, real_inner_smul_left,
        hu, hw, huw, hwu, Real.Angle.cos_coe, Real.Angle.sin_coe, Complex.cos_ofReal_re,
        Complex.sin_ofReal_re]
  rw [polarAngle, h, Complex.arg_mul_cos_add_sin_mul_I_coe_angle hr]

/-- **Polar coordinates determine the point, with the angle taken modulo `2π`.** Two points with
`r, r' > 0` have the same image under the polar canonical parametrization exactly when their
radial pairs `(r, p_r)` and angular momenta agree and their angles agree modulo `2π`. -/
theorem polarCanonical_eq_polarCanonical_iff {x x' : (ℝ × ℝ) × (ℝ × ℝ)} (hr : 0 < x.1.1)
    (hr' : 0 < x'.1.1) :
    polarCanonical u w x = polarCanonical u w x' ↔
      x.1 = x'.1 ∧ (x.2.1 : Real.Angle) = x'.2.1 ∧ x.2.2 = x'.2.2 := by
  refine ⟨fun h ↦ ⟨Prod.ext ?_ ?_, ?_, ?_⟩, fun ⟨h₁, h₂, h₃⟩ ↦ ?_⟩
  · rw [← abs_of_pos hr, ← abs_of_pos hr', ← norm_fst_polarCanonical hu hw huw,
      ← norm_fst_polarCanonical hu hw huw x', h]
  · rw [← radialMomentum_polarCanonical hu hw huw hr,
      ← radialMomentum_polarCanonical hu hw huw hr', h]
  · rw [← polarAngle_polarCanonical hu hw huw hr, ← polarAngle_polarCanonical hu hw huw hr', h]
  · rw [← angularMomentum_polarCanonical hu hw huw hr.ne',
      ← angularMomentum_polarCanonical hu hw huw hr'.ne', h]
  · obtain ⟨⟨r, pᵣ⟩, ⟨θ, L⟩⟩ := x
    obtain ⟨⟨r', pᵣ'⟩, ⟨θ', L'⟩⟩ := x'
    simp only [Prod.mk.injEq] at h₁ h₃
    obtain ⟨rfl, rfl⟩ := h₁
    subst h₃
    exact polarCanonical_eq_of_coe_eq _ _ h₂ _ _ _

end Orthonormal

variable (b : OrthonormalBasis (Fin 2) ℝ V)

/-- **Every point off the collision set is the image of its polar coordinates**: for `q ≠ 0` and
every lift `θ` of the polar angle of `q`, the point with polar coordinates
`(‖q‖, p_r, θ, L)`, where `p_r` is the radial momentum and `L` the angular momentum of `(q, p)`, is
`(q, p)`. -/
theorem polarCanonical_polarAngle {q : V} (p : V) (hq : q ≠ 0) {θ : ℝ}
    (hθ : (θ : Real.Angle) = polarAngle (b 0) (b 1) q) :
    polarCanonical (b 0) (b 1)
        ((‖q‖, radialMomentum (q, p)), (θ, angularMomentum (b 0) (b 1) (q, p))) = (q, p) := by
  have hn : ‖q‖ ^ 2 = ⟪q, b 0⟫_ℝ ^ 2 + ⟪q, b 1⟫_ℝ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, b.real_inner_fin_two, sq, sq]
  have hq0 : ‖q‖ ≠ 0 := norm_ne_zero_iff.2 hq
  have hcos : Real.cos θ = ⟪q, b 0⟫_ℝ / ‖q‖ := by
    rw [eq_div_iff hq0, ← Real.Angle.cos_coe, hθ, mul_comm, norm_mul_cos_polarAngle]
  have hsin : Real.sin θ = ⟪q, b 1⟫_ℝ / ‖q‖ := by
    rw [eq_div_iff hq0, ← Real.Angle.sin_coe, hθ, mul_comm, norm_mul_sin_polarAngle]
  have hrepr (v : V) : v = ⟪v, b 0⟫_ℝ • b 0 + ⟪v, b 1⟫_ℝ • b 1 := by
    conv_lhs => rw [← (Complex.isometryOfOrthonormal b).apply_symm_apply v,
      Complex.isometryOfOrthonormal_apply, Complex.isometryOfOrthonormal_symm_apply_eq_mk]
  rw [polarCanonical_apply, polarRadialUnit, polarAngularUnit, hcos, hsin, radialMomentum_apply,
    b.real_inner_fin_two q p, angularMomentum_apply]
  conv_rhs => rw [hrepr q, hrepr p]
  ext
  · simp only [smul_add, smul_smul]
    match_scalars <;> field_simp
  · simp only [smul_add, smul_smul, neg_smul]
    match_scalars
    · field_simp
      linear_combination -⟪p, b 0⟫_ℝ * hn
    · field_simp
      linear_combination -⟪p, b 1⟫_ℝ * hn

/-- **Global polar canonical coordinates.** For an orthonormal basis `b` of a plane `V`, the polar
canonical parametrization identifies `(0, ∞) × ℝ × (ℝ / 2πℤ) × ℝ`, with coordinates
`((r, p_r), (θ, L))`, with the punctured phase space `{(q, p) | q ≠ 0}`. The inverse sends
`(q, p)` to its length `‖q‖`, radial momentum, polar angle and angular momentum. -/
noncomputable def polarCanonicalEquiv :
    {x : (ℝ × ℝ) × (Real.Angle × ℝ) // 0 < x.1.1} ≃ puncturedPhaseSpace V where
  toFun x := ⟨polarCanonical (b 0) (b 1) (x.1.1, (x.1.2.1.toReal, x.1.2.2)), by
    rw [mem_puncturedPhaseSpace, ← norm_ne_zero_iff,
      norm_fst_polarCanonical (b.norm_eq_one 0) (b.norm_eq_one 1)
        (b.inner_eq_zero (by decide))]
    exact (abs_pos.2 x.2.ne').ne'⟩
  invFun y := ⟨((‖y.1.1‖, radialMomentum y.1), (polarAngle (b 0) (b 1) y.1.1,
    angularMomentum (b 0) (b 1) y.1)), norm_pos_iff.2 (mem_puncturedPhaseSpace.1 y.2)⟩
  left_inv x := by
    obtain ⟨⟨⟨r, pᵣ⟩, ⟨θ, L⟩⟩, hr⟩ := x
    have h0 := b.norm_eq_one 0
    have h1 := b.norm_eq_one 1
    have h01 : ⟪b 0, b 1⟫_ℝ = 0 := b.inner_eq_zero (by decide)
    have hr' : 0 < ((r, pᵣ), (θ.toReal, L)).1.1 := hr
    simp only [Subtype.mk.injEq, Prod.mk.injEq]
    refine ⟨⟨?_, radialMomentum_polarCanonical h0 h1 h01 hr'⟩, ?_,
      angularMomentum_polarCanonical h0 h1 h01 hr'.ne'⟩
    · rw [norm_fst_polarCanonical h0 h1 h01, abs_of_pos hr]
    · rw [polarAngle_polarCanonical h0 h1 h01 hr', Real.Angle.coe_toReal]
  right_inv y := by
    obtain ⟨⟨q, p⟩, hq⟩ := y
    exact Subtype.ext (polarCanonical_polarAngle b p (mem_puncturedPhaseSpace.1 hq)
      (Real.Angle.coe_toReal _))

/-- The polar canonical coordinates `((r, p_r), (θ, L))` with `θ ∈ ℝ / 2πℤ` name the image of
`((r, p_r), (θ', L))` under the polar canonical parametrization, for every lift `θ'` of `θ`. -/
theorem coe_polarCanonicalEquiv_apply (x : {x : (ℝ × ℝ) × (Real.Angle × ℝ) // 0 < x.1.1})
    {θ : ℝ} (hθ : (θ : Real.Angle) = x.1.2.1) :
    (polarCanonicalEquiv b x : V × V) = polarCanonical (b 0) (b 1) (x.1.1, (θ, x.1.2.2)) :=
  polarCanonical_eq_of_coe_eq _ _ (by rw [Real.Angle.coe_toReal, hθ]) _ _ _

/-- The polar canonical coordinates of `(q, p)`, `q ≠ 0`, are its length `‖q‖`, radial momentum,
polar angle and angular momentum. -/
@[simp]
theorem coe_polarCanonicalEquiv_symm_apply (y : puncturedPhaseSpace V) :
    ((polarCanonicalEquiv b).symm y : (ℝ × ℝ) × (Real.Angle × ℝ)) =
      ((‖y.1.1‖, radialMomentum y.1),
        (polarAngle (b 0) (b 1) y.1.1, angularMomentum (b 0) (b 1) y.1)) :=
  (rfl)

end Angle

end TauCeti
