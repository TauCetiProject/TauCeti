/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.SphericalPendulum.Integrable
public import TauCeti.Geometry.Symplectic.Hamiltonian.SphericalPendulum.TurningPoint
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import TauCeti.Analysis.Calculus.FDeriv.Pi.Lp
import TauCeti.Analysis.SpecialFunctions.Integrals.SqrtQuadratic
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds
import TauCeti.Geometry.Manifold.IntegralCurve.Basic
import TauCeti.MeasureTheory.Function.Jacobian.OneDim

/-!
# The equations of motion of the spherical pendulum

The phase space of the spherical pendulum is `T*S² = {(q, p) : ‖q‖ = 1, ⟪q, p⟫ = 0}` inside
`ℝ³ × ℝ³`, with the restriction of the standard symplectic form
(`TauCeti.sphericalPendulumSymplecticForm`) and the energy `H(q, p) = ‖p‖² / 2 + q₃`. This file
computes the Hamiltonian vector field of `H` on the phase space and derives from it the time
quadratures of the height `z = q₃`.

**Hamilton's equations.** The ambient Hamiltonian vector field `(p, -e₃)` of `H` is not tangent to
the phase space, so the dynamics is not its restriction. Instead, on the phase space `H` agrees with
the polynomial `H - ((q₃ - ‖p‖²) / 2) (‖q‖² - 1)`, which subtracts the constraint `‖q‖² = 1` with a
Lagrange multiplier chosen to make the ambient Hamiltonian vector field tangent along the phase
space. Hence the Hamiltonian vector field of `H` on the phase space is

`(q, p) ↦ (p, (q₃ - ‖p‖²) q - e₃)`

(`TauCeti.sphericalPendulumVectorField`,
`mfderiv_coe_sphericalPendulumPhaseSpace_hamiltonianVectorField_sphericalPendulumHamiltonian`):
gravity `-e₃` plus the constraint force `(q₃ - ‖p‖²) q` normal to the sphere. Every motion of the
pendulum, an integral curve of this field on the phase space, therefore solves `q' = p`,
`p' = (q₃ - ‖p‖²) q - e₃` in `ℝ³ × ℝ³` (`TauCeti.isIntegralCurveOn_sphericalPendulumVectorField`),
and conserves the energy and the vertical angular momentum
(`TauCeti.sphericalPendulumEnergyMomentum_eq_of_isMIntegralCurveOn`).

**The height quadrature.** Along a motion with energy `h` and vertical angular momentum `j` the
height moves with velocity `z' = p₃`, and `p₃² = 2 (h - z) (1 - z²) - j²`. While the radicand is
positive `p₃` does not vanish, so `z` is monotone and `dt = dz / √(2 (h - z) (1 - z²) - j²)`. Hence
the time the height takes to run between two heights `z₁`, `z₂`, strictly between which it stays,
is `∫_{z₁}^{z₂} dz / √(2 (h - z) (1 - z²) - j²)`
(`TauCeti.sub_eq_integral_inv_sqrt_of_isMIntegralCurveOn_sphericalPendulum`). Above the curve of
relative equilibria the height oscillates between the turning points `z₋ < z₊`, and a full
oscillation, from `z₋` up to `z₊` and back, takes the **period**

`T(h, j) = 2 ∫_{z₋}^{z₊} dz / √(2 (h - z) (1 - z²) - j²)`

(`TauCeti.sphericalPendulumPeriod`, `TauCeti.sub_eq_sphericalPendulumPeriod_of_isMIntegralCurveOn`),
the companion of the rotation angle `TauCeti.sphericalPendulumRotationAngle`.

## Main declarations

* `TauCeti.sphericalPendulumVectorField`: the vector field `(q, p) ↦ (p, (q₃ - ‖p‖²) q - e₃)`.
* `mfderiv_coe_sphericalPendulumPhaseSpace_hamiltonianVectorField_sphericalPendulumHamiltonian`:
  it is the Hamiltonian vector field of the energy on the phase space.
* `TauCeti.isIntegralCurveOn_sphericalPendulumVectorField`: the motions of the pendulum solve the
  equations of motion in `ℝ³ × ℝ³`.
* `TauCeti.sphericalPendulumEnergyMomentum_eq_of_isMIntegralCurveOn`: conservation of `(H, J)`.
* `TauCeti.integral_comp_eq_integral_div_sqrt_of_isMIntegralCurveOn_sphericalPendulum`: time
  integrals of functions of the height along a passage are height quadratures.
* `TauCeti.sub_eq_integral_inv_sqrt_of_isMIntegralCurveOn_sphericalPendulum`: the time between two
  heights is the height quadrature.
* `TauCeti.sphericalPendulumPeriod`, `TauCeti.sub_eq_sphericalPendulumPeriod_of_isMIntegralCurveOn`:
  the period of the height.
* `TauCeti.intervalIntegrable_inv_sqrt_two_mul_sub_mul_one_sub_sq_sub_sq`,
  `TauCeti.sphericalPendulumPeriod_pos`: the period integrand is integrable between the turning
  points, and the period is positive.
* `TauCeti.sphericalPendulumPeriod_eq_integral_sin`,
  `TauCeti.two_mul_pi_div_sqrt_le_sphericalPendulumPeriod`,
  `TauCeti.continuousOn_sphericalPendulumPeriod`: after the sine substitution the period is the
  integral of a continuous positive function, so it is bounded below by `2π / √(2 (h + 3))` and
  continuous in `(h, j)` above the curve of relative equilibria.

## References

* R. H. Cushman and L. M. Bates, *Global Aspects of Classical Integrable Systems*, 2nd ed.,
  Birkhäuser, 2015, Chapter IV (the spherical pendulum as a constrained system in `ℝ³ × ℝ³`).
-/

public section

open Function Set MeasureTheory
open scoped InnerProductSpace Manifold ContDiff

namespace TauCeti

/-! ### The Hamiltonian vector field of the energy -/

/-- The **vector field of the spherical pendulum** on `ℝ³ × ℝ³`,
`(q, p) ↦ (p, (q₃ - ‖p‖²) q - e₃)`. On the phase space it is the Hamiltonian vector field of the
energy: the position moves with velocity `p`, and the momentum changes by the gravitational force
`-e₃` plus the normal constraint force `(q₃ - ‖p‖²) q` that keeps the pendulum on the sphere. -/
noncomputable def sphericalPendulumVectorField
    (x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) :=
  (x.2, (x.1 2 - ‖x.2‖ ^ 2) • x.1 - EuclideanSpace.single 2 1)

theorem sphericalPendulumVectorField_def
    (x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
    sphericalPendulumVectorField x =
      (x.2, (x.1 2 - ‖x.2‖ ^ 2) • x.1 - EuclideanSpace.single 2 1) :=
  (rfl)

@[simp]
theorem sphericalPendulumVectorField_apply (q p : EuclideanSpace ℝ (Fin 3)) :
    sphericalPendulumVectorField (q, p) = (p, (q 2 - ‖p‖ ^ 2) • q - EuclideanSpace.single 2 1) :=
  (rfl)

/-- A polynomial extension of the energy from the phase space to `ℝ³ × ℝ³`, whose ambient
Hamiltonian vector field is tangent to the phase space: it subtracts from the energy the constraint
`‖q‖² - 1` with the multiplier `(q₃ - ‖p‖²) / 2`. -/
private noncomputable def extendedEnergy
    (x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) : ℝ :=
  2⁻¹ * (‖x.2‖ ^ 2 + 2 * x.1 2 - (x.1 2 - ‖x.2‖ ^ 2) * (‖x.1‖ ^ 2 - 1))

/-- The extended energy agrees with the energy on the phase space. -/
private theorem extendedEnergy_eq {x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ sphericalPendulumPhaseSpace) :
    extendedEnergy x = sphericalPendulumHamiltonian x := by
  obtain ⟨q, p⟩ := x
  rw [extendedEnergy, sphericalPendulumHamiltonian_apply, (mem_sphericalPendulumPhaseSpace.1 hx).1]
  ring

/-- At a point of the phase space, the extended energy has partial gradients
`∇_q = e₃ - (q₃ - ‖p‖²) q` and `∇_p = p`. -/
private theorem hasFDerivAt_extendedEnergy
    {x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ sphericalPendulumPhaseSpace) :
    HasFDerivAt extendedEnergy ((innerSL ℝ (EuclideanSpace.single 2 1 -
      (x.1 2 - ‖x.2‖ ^ 2) • x.1)).coprod (innerSL ℝ x.2)) x := by
  obtain ⟨hq, -⟩ := mem_sphericalPendulumPhaseSpace.1 hx
  have hz := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 x.1 2).comp x (hasFDerivAt_fst (𝕜 := ℝ) (p := x))
  have hp := hasFDerivAt_snd (𝕜 := ℝ) (p := x) |>.norm_sq
  have hq2 := hasFDerivAt_fst (𝕜 := ℝ) (p := x) |>.norm_sq
  refine (((hp.add (hz.const_mul 2)).sub ((hz.sub hp).mul (hq2.sub_const 1))).const_mul
    2⁻¹).congr_fderiv (ContinuousLinearMap.ext fun v ↦ ?_)
  simp only [Fin.isValue, Pi.sub_apply, comp_apply, hq, one_pow, sub_self, zero_smul, add_zero,
    smul_apply, sub_apply, add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd',
    coe_innerSL_apply, nsmul_eq_mul, Nat.cast_ofNat, ContinuousLinearMap.coe_fst', PiLp.proj_apply,
    smul_eq_mul, map_sub, map_smul, ContinuousLinearMap.coprod_apply,
    EuclideanSpace.inner_single_left, conj_trivial, one_mul]
  ring

/-- At a point of the phase space, the ambient Hamiltonian vector field of the extended energy is
the vector field of the spherical pendulum. -/
private theorem hamiltonianVectorField_extendedEnergy
    {x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ sphericalPendulumPhaseSpace) :
    (stdSymplecticForm (V := EuclideanSpace ℝ (Fin 3))).hamiltonianVectorField extendedEnergy x =
      sphericalPendulumVectorField x := by
  rw [stdSymplecticForm_hamiltonianVectorField (hasFDerivAt_extendedEnergy hx),
    sphericalPendulumVectorField_def, neg_sub]

/-- The vector field of the spherical pendulum is tangent to the phase space: at a point of the
phase space it lies in the kernel of the differential of the constraint map
`(q, p) ↦ (‖q‖², ⟪q, p⟫)`. -/
theorem sphericalPendulumVectorField_mem_ker_fderiv_sphericalPendulumConstraint
    {x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ sphericalPendulumPhaseSpace) :
    sphericalPendulumVectorField x ∈ (fderiv ℝ sphericalPendulumConstraint x).ker := by
  obtain ⟨hq, hqp⟩ := mem_sphericalPendulumPhaseSpace.1 hx
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, fderiv_sphericalPendulumConstraint_apply]
  simp [sphericalPendulumVectorField_def, inner_sub_right, inner_smul_right,
    EuclideanSpace.inner_single_right, hq, hqp]

/-- **Hamilton's equations of the spherical pendulum.** The Hamiltonian vector field of the energy
`H = ‖p‖² / 2 + q₃` on the phase space `T*S²` is the vector field
`(q, p) ↦ (p, (q₃ - ‖p‖²) q - e₃)`: the differential of the inclusion of the phase space in
`ℝ³ × ℝ³` carries the one to the other. -/
theorem mfderiv_coe_sphericalPendulumPhaseSpace_hamiltonianVectorField_sphericalPendulumHamiltonian
    (x : sphericalPendulumPhaseSpace) :
    mfderiv 𝓘(ℝ, Fin 4 → ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))
        Subtype.val x (sphericalPendulumSymplecticForm.hamiltonianVectorField
          (fun y ↦ sphericalPendulumHamiltonian y) x) =
      sphericalPendulumVectorField x := by
  -- The energy is the restriction of the extended energy, whose ambient Hamiltonian vector is
  -- tangent to the phase space.
  have hE : (fun y : sphericalPendulumPhaseSpace ↦ sphericalPendulumHamiltonian y) =
      extendedEnergy ∘ Subtype.val :=
    funext fun y ↦ (extendedEnergy_eq y.property).symm
  have hd : DifferentiableAt ℝ extendedEnergy x :=
      (hasFDerivAt_extendedEnergy x.property).differentiableAt
  have hk : (SymplecticForm.constSmooth stdSymplecticForm).hamiltonianVectorField extendedEnergy
      x ∈ (mfderiv 𝓘(ℝ, Fin 4 → ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))
        Subtype.val x).range := by
    rw [range_mfderiv_coe_sphericalPendulumPhaseSpace,
      SymplecticForm.hamiltonianVectorField_constSmooth, hamiltonianVectorField_extendedEnergy
          x.property]
    exact sphericalPendulumVectorField_mem_ker_fderiv_sphericalPendulumConstraint x.property
  rw [hE, ← hamiltonianVectorField_extendedEnergy x.property]
  simpa only [SymplecticForm.hamiltonianVectorField_constSmooth] using
    isSymplectic_sphericalPendulumSymplecticForm.isNondegenerate
      |>.mfderiv_hamiltonianVectorField_comp_of_mem_range
        (SymplecticForm.isNondegenerate_constSmooth _)
        isSmoothEmbedding_coe_sphericalPendulumPhaseSpace.contMDiff
        sphericalPendulumSymplecticForm_def.symm hd.mdifferentiableAt hk

/-! ### Motions of the pendulum -/

section Motion

variable {γ : ℝ → sphericalPendulumPhaseSpace} {s : Set ℝ} {t : ℝ}

/-- **The motions of the spherical pendulum solve its equations of motion.** An integral curve of
the Hamiltonian vector field of the energy on the phase space, read in `ℝ³ × ℝ³`, is an integral
curve of the vector field `(q, p) ↦ (p, (q₃ - ‖p‖²) q - e₃)`: `q' = p` and
`p' = (q₃ - ‖p‖²) q - e₃`. -/
theorem isIntegralCurveOn_sphericalPendulumVectorField
    (hγ : IsMIntegralCurveOn γ (sphericalPendulumSymplecticForm.hamiltonianVectorField
      fun y ↦ sphericalPendulumHamiltonian y) s) :
    IsIntegralCurveOn (fun t ↦ (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)))
      (fun _ ↦ sphericalPendulumVectorField) s :=
  TauCeti.isMIntegralCurveOn_iff_isIntegralCurveOn.1 <|
    hγ.map_of_mfderiv_eq (f := Subtype.val) (W := fun x ↦ sphericalPendulumVectorField x)
      (fun t _ ↦ (isSmoothEmbedding_coe_sphericalPendulumPhaseSpace.contMDiff
        (γ t)).mdifferentiableAt (by simp))
      fun t _ ↦
        mfderiv_coe_sphericalPendulumPhaseSpace_hamiltonianVectorField_sphericalPendulumHamiltonian
          (γ t)

/-- **Conservation of energy and vertical angular momentum.** Along a motion of the spherical
pendulum on an interval of times (or any preconnected set of times), the energy–momentum map
`F = (H, J)` is constant. -/
theorem sphericalPendulumEnergyMomentum_eq_of_isMIntegralCurveOn (hs : IsPreconnected s)
    (hγ : IsMIntegralCurveOn γ (sphericalPendulumSymplecticForm.hamiltonianVectorField
      fun y ↦ sphericalPendulumHamiltonian y) s) {t₀ : ℝ} (ht₀ : t₀ ∈ s) (ht : t ∈ s) :
    sphericalPendulumEnergyMomentum (γ t) = sphericalPendulumEnergyMomentum (γ t₀) := by
  have hI := isIntegrableSystem_sphericalPendulumEnergyMomentumVec
  have hH : (fun x ↦ sphericalPendulumEnergyMomentumVec x 0) =
      fun y : sphericalPendulumPhaseSpace ↦ sphericalPendulumHamiltonian y :=
    funext sphericalPendulumEnergyMomentumVec_apply_zero
  -- Each component of `F` is a first integral of the energy, and is smooth.
  have h (i : Fin 2) := (hH ▸ hI.isFirstIntegral 0 i).apply_eq_of_isMIntegralCurveOn hs hγ
    (fun u _ ↦ ((contMDiff_pi_module_iff.1 hI.contMDiff i) (γ u)).mdifferentiableAt (by simp))
    ht₀ ht
  exact Prod.ext (by simpa using h 0) (by simpa using h 1)

/-- Along a motion of the spherical pendulum, the height `q₃` moves with velocity `p₃`. -/
theorem hasDerivWithinAt_fst_apply_two_of_isMIntegralCurveOn_sphericalPendulum
    (hγ : IsMIntegralCurveOn γ (sphericalPendulumSymplecticForm.hamiltonianVectorField
      fun y ↦ sphericalPendulumHamiltonian y) s) (ht : t ∈ s) :
    HasDerivWithinAt (fun t ↦ (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2)
      ((γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).2 2) s t := by
  simpa [Function.comp_def, sphericalPendulumVectorField_def] using
    ((ContinuousLinearMap.fst ℝ _ _).hasFDerivAt.comp_hasDerivWithinAt t
      (isIntegralCurveOn_sphericalPendulumVectorField hγ t ht)).piLp_apply 2

/-- Along a motion of the spherical pendulum, the vertical momentum `p₃` changes with velocity
`(q₃ - ‖p‖²) q₃ - 1`, the vertical component of the gravitational and constraint forces. -/
theorem hasDerivWithinAt_snd_apply_two_of_isMIntegralCurveOn_sphericalPendulum
    (hγ : IsMIntegralCurveOn γ (sphericalPendulumSymplecticForm.hamiltonianVectorField
      fun y ↦ sphericalPendulumHamiltonian y) s) (ht : t ∈ s) :
    HasDerivWithinAt (fun t ↦ (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).2 2)
      (((γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 -
        ‖(γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).2‖ ^ 2) *
          (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 - 1) s t := by
  simpa [Function.comp_def, sphericalPendulumVectorField_def] using
    ((ContinuousLinearMap.snd ℝ _ _).hasFDerivAt.comp_hasDerivWithinAt t
      (isIntegralCurveOn_sphericalPendulumVectorField hγ t ht)).piLp_apply 2

/-- **Time integrals along a passage are height quadratures.** Let a motion of the spherical
pendulum on `[t₁, t₂]` have energy `h` and vertical angular momentum `j`, and suppose its height
`z = q₃` moves from one of `z₁`, `z₂` to the other and stays strictly between them meanwhile, where
the radicand `2 (h - z) (1 - z²) - j²` is positive. Then for every function `g` of the height,

`∫_{t₁}^{t₂} g(z(t)) dt = ∫_{z₁}^{z₂} g(z) dz / √(2 (h - z) (1 - z²) - j²)`. -/
theorem integral_comp_eq_integral_div_sqrt_of_isMIntegralCurveOn_sphericalPendulum
    {t₁ t₂ z₁ z₂ h j : ℝ} (ht : t₁ ≤ t₂)
    (hγ : IsMIntegralCurveOn γ (sphericalPendulumSymplecticForm.hamiltonianVectorField
      fun y ↦ sphericalPendulumHamiltonian y) (Icc t₁ t₂))
    (hF : sphericalPendulumEnergyMomentum (γ t₁) = (h, j))
    (hpos : ∀ z ∈ Ioo z₁ z₂, 0 < 2 * (h - z) * (1 - z ^ 2) - j ^ 2)
    (hends : (γ t₁ : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 = z₁ ∧
        (γ t₂ : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 = z₂ ∨
      (γ t₁ : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 = z₂ ∧
        (γ t₂ : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 = z₁)
    (hmem : ∀ t ∈ Ioo t₁ t₂,
      (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 ∈ Ioo z₁ z₂)
    (g : ℝ → ℝ) :
    ∫ t in t₁..t₂, g ((γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2) =
      ∫ z in z₁..z₂, g z / √(2 * (h - z) * (1 - z ^ 2) - j ^ 2) := by
  set z : ℝ → ℝ := fun t ↦ (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2
  have hIoo : Ioo t₁ t₂ ⊆ Icc t₁ t₂ := Ioo_subset_Icc_self
  have hzd (t : ℝ) (ht : t ∈ Icc t₁ t₂) :=
    hasDerivWithinAt_fst_apply_two_of_isMIntegralCurveOn_sphericalPendulum hγ ht
  -- On the fibre over `(h, j)` the vertical momentum satisfies `p₃² = 2 (h - z) (1 - z²) - j²`, so
  -- it does not vanish strictly between `z₁` and `z₂`.
  have hp (t : ℝ) (htI : t ∈ Ioo t₁ t₂) :
      |(γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).2 2| =
          √(2 * (h - z t) * (1 - z t ^ 2) - j ^ 2) ∧
        (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).2 2 ≠ 0 := by
    have hsq := sq_snd_two_eq_of_mem_sphericalPendulumPhaseSpace (γ t).property
    rw [sphericalPendulumEnergyMomentum_eq_of_isMIntegralCurveOn isPreconnected_Icc hγ
      (left_mem_Icc.2 ht) (hIoo htI), hF] at hsq
    have hR := hpos _ (hmem t htI)
    rw [← hsq] at hR
    refine ⟨?_, fun h0 ↦ by simp [h0] at hR⟩
    rw [← hsq, Real.sqrt_sq_eq_abs]
  rw [intervalIntegral.integral_eq_integral_Ioo_abs_deriv_smul_of_ne_zero ht
      (fun t ht ↦ (hzd t ht).continuousWithinAt) (fun t ht ↦ (hzd t (hIoo ht)).mono hIoo)
      (fun t ht ↦ (hp t ht).2) hends hmem,
    intervalIntegral.integral_of_le ht, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht ↦ ?_
  rw [smul_eq_mul, (hp t ht).1, mul_div_cancel₀ _ (Real.sqrt_ne_zero'.2 (hpos _ (hmem t ht)))]

/-- **The time between two heights is the height quadrature.** Let a motion of the spherical
pendulum on `[t₁, t₂]` have energy `h` and vertical angular momentum `j`, and suppose its height
`z = q₃` moves from one of `z₁`, `z₂` to the other and stays strictly between them meanwhile, where
the radicand `2 (h - z) (1 - z²) - j²` is positive. Then the elapsed time is

`t₂ - t₁ = ∫_{z₁}^{z₂} dz / √(2 (h - z) (1 - z²) - j²)`. -/
theorem sub_eq_integral_inv_sqrt_of_isMIntegralCurveOn_sphericalPendulum {t₁ t₂ z₁ z₂ h j : ℝ}
    (ht : t₁ ≤ t₂)
    (hγ : IsMIntegralCurveOn γ (sphericalPendulumSymplecticForm.hamiltonianVectorField
      fun y ↦ sphericalPendulumHamiltonian y) (Icc t₁ t₂))
    (hF : sphericalPendulumEnergyMomentum (γ t₁) = (h, j))
    (hpos : ∀ z ∈ Ioo z₁ z₂, 0 < 2 * (h - z) * (1 - z ^ 2) - j ^ 2)
    (hends : (γ t₁ : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 = z₁ ∧
        (γ t₂ : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 = z₂ ∨
      (γ t₁ : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 = z₂ ∧
        (γ t₂ : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 = z₁)
    (hmem : ∀ t ∈ Ioo t₁ t₂,
      (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 ∈ Ioo z₁ z₂) :
    t₂ - t₁ = ∫ z in z₁..z₂, (√(2 * (h - z) * (1 - z ^ 2) - j ^ 2))⁻¹ := by
  simpa [one_div] using
    integral_comp_eq_integral_div_sqrt_of_isMIntegralCurveOn_sphericalPendulum ht hγ hF hpos hends
      hmem fun _ ↦ 1

end Motion

/-! ### The period of the height -/

/-- The **period** `T(h, j) = 2 ∫ dz / √(2 (h - z) (1 - z²) - j²)` of the height of the spherical
pendulum at energy `h` and vertical angular momentum `j`. The integral runs over `(-1, 1)`, but the
integrand vanishes at every height `z` with `2 (h - z) (1 - z²) ≤ j²`, so above the curve of
relative equilibria (`j ≠ 0` and `h` above the minimum of the effective potential
`TauCeti.sphericalPendulumEffectivePotential j`) it is the integral between the two turning points
of the height (`TauCeti.sphericalPendulumPeriod_eq_integral`). -/
noncomputable def sphericalPendulumPeriod (h j : ℝ) : ℝ :=
  2 * ∫ z in (-1)..1, (√(2 * (h - z) * (1 - z ^ 2) - j ^ 2))⁻¹

theorem sphericalPendulumPeriod_def (h j : ℝ) :
    sphericalPendulumPeriod h j = 2 * ∫ z in (-1)..1, (√(2 * (h - z) * (1 - z ^ 2) - j ^ 2))⁻¹ :=
  (rfl)

section Regular

variable {h j z₀ : ℝ}

/-- Above the curve of relative equilibria, the period is twice the integral of
`1 / √(2 (h - z) (1 - z²) - j²)` between the turning points `z₋ < z₊`. -/
theorem sphericalPendulumPeriod_eq_integral (hj : j ≠ 0) (hz₀ : z₀ ∈ Ioo (-1) 1)
    (hV : sphericalPendulumEffectivePotential j z₀ < h) :
    sphericalPendulumPeriod h j =
      2 * ∫ z in (sphericalPendulumLowerTurningPoint h j)..(sphericalPendulumUpperTurningPoint h j),
        (√(2 * (h - z) * (1 - z ^ 2) - j ^ 2))⁻¹ := by
  rw [sphericalPendulumPeriod_def]
  simpa only [one_div] using congrArg (2 * ·)
    (integral_div_sqrt_two_mul_sub_mul_one_sub_sq_sub_sq_eq hj hz₀ hV fun _ ↦ 1)

/-- Above the curve of relative equilibria, the period integrand
`1 / √(2 (h - z) (1 - z²) - j²)` is integrable between the turning points `z₋ < z₊`: they are simple
roots of the radicand, so it is `1 / √((z - z₋) (z₊ - z))` times a function continuous on
`[z₋, z₊]`. -/
theorem intervalIntegrable_inv_sqrt_two_mul_sub_mul_one_sub_sq_sub_sq (hj : j ≠ 0)
    (hz₀ : z₀ ∈ Ioo (-1) 1) (hV : sphericalPendulumEffectivePotential j z₀ < h) :
    IntervalIntegrable (fun z ↦ (√(2 * (h - z) * (1 - z ^ 2) - j ^ 2))⁻¹) volume
      (sphericalPendulumLowerTurningPoint h j) (sphericalPendulumUpperTurningPoint h j) := by
  have hab := sphericalPendulumLowerTurningPoint_lt_sphericalPendulumUpperTurningPoint hj hz₀ hV
  have hb := sphericalPendulumUpperTurningPoint_lt_one hj hz₀ hV
  have hc := one_lt_sub_sphericalPendulumLowerTurningPoint_sub_sphericalPendulumUpperTurningPoint
    hj hz₀ hV
  have hfac := two_mul_sub_mul_one_sub_sq_sub_sq_eq hj hz₀ hV
  set a := sphericalPendulumLowerTurningPoint h j
  set b := sphericalPendulumUpperTurningPoint h j
  have hg : ContinuousOn (fun z ↦ (√(2 * (h - a - b - z)))⁻¹) (uIcc a b) := by
    refine ContinuousOn.inv₀ (by fun_prop) fun z hz ↦ ?_
    rw [uIcc_of_le hab.le] at hz
    exact (Real.sqrt_pos.2 (by linarith [hz.2])).ne'
  refine (intervalIntegrable_one_div_sqrt_mul_sub_mul_sub.continuousOn_mul hg).congr_ae <|
    (ae_restrict_mem measurableSet_uIoc).mono fun z hz ↦ ?_
  rw [uIoc_of_le hab.le] at hz
  beta_reduce
  -- On `[z₋, z₊]` the radicand is `2 (z₃ - z) · (z - z₋) (z₊ - z)` with both factors nonnegative.
  rw [hfac z,
    show 2 * (z - a) * (b - z) * (h - a - b - z) = 2 * (h - a - b - z) * ((z - a) * (b - z)) by
      ring, Real.sqrt_mul (show 0 ≤ 2 * (h - a - b - z) by linarith [hz.2]), mul_inv, one_div]

/-- Above the curve of relative equilibria, the period of the height is positive. -/
theorem sphericalPendulumPeriod_pos (hj : j ≠ 0) (hz₀ : z₀ ∈ Ioo (-1) 1)
    (hV : sphericalPendulumEffectivePotential j z₀ < h) : 0 < sphericalPendulumPeriod h j := by
  rw [sphericalPendulumPeriod_eq_integral hj hz₀ hV]
  exact mul_pos two_pos <| intervalIntegral.intervalIntegral_pos_of_pos_on
    (intervalIntegrable_inv_sqrt_two_mul_sub_mul_one_sub_sq_sub_sq hj hz₀ hV)
    (fun z hz ↦ inv_pos.2 (Real.sqrt_pos.2 (two_mul_sub_mul_one_sub_sq_sub_sq_pos hj hz₀ hV hz)))
    (sphericalPendulumLowerTurningPoint_lt_sphericalPendulumUpperTurningPoint hj hz₀ hV)

/-- On the domain of distinct nonpolar turning points, the period of the height is positive. -/
theorem sphericalPendulumPeriod_pos_of_mem
    (hc : (h, j) ∈ sphericalPendulumTurningPointDomain) : 0 < sphericalPendulumPeriod h j :=
  let ⟨hj, _, hz₀, hV⟩ := mem_sphericalPendulumTurningPointDomain_iff.1 hc
  sphericalPendulumPeriod_pos hj hz₀ hV

/-- **The period as a regular integral.** Above the curve of relative equilibria, the substitution
`z = (z₋ + z₊) / 2 + (z₊ - z₋) / 2 · sin θ` between the turning points `z₋ < z₊` turns the period
into the integral `T(h, j) = 2 ∫_{-π/2}^{π/2} dθ / √(2 (z₃ - z))`, where `z₃ = h - z₋ - z₊ > 1` is
the third root of the radicand. Its integrand is continuous and positive. -/
theorem sphericalPendulumPeriod_eq_integral_sin (hj : j ≠ 0) (hz₀ : z₀ ∈ Ioo (-1) 1)
    (hV : sphericalPendulumEffectivePotential j z₀ < h) :
    sphericalPendulumPeriod h j =
      2 * ∫ θ in (-(Real.pi / 2))..(Real.pi / 2),
        (√(2 * (h - sphericalPendulumLowerTurningPoint h j -
          sphericalPendulumUpperTurningPoint h j -
          ((sphericalPendulumLowerTurningPoint h j + sphericalPendulumUpperTurningPoint h j) / 2 +
            (sphericalPendulumUpperTurningPoint h j - sphericalPendulumLowerTurningPoint h j) /
              2 * Real.sin θ))))⁻¹ := by
  rw [sphericalPendulumPeriod_def]
  simpa only [one_div] using congrArg (2 * ·)
    (integral_div_sqrt_two_mul_sub_mul_one_sub_sq_sub_sq_eq_integral_sin hj hz₀ hV fun _ ↦ 1)

/-- **A lower bound for the period.** Above the curve of relative equilibria, the period of the
height is at least `2π / √(2 (h + 3))`: after the sine substitution, the integrand
`1 / √(2 (z₃ - z))` is at least `1 / √(2 (h + 3))`, since `z₋, z₊, z > -1`. -/
theorem two_mul_pi_div_sqrt_le_sphericalPendulumPeriod (hj : j ≠ 0) (hz₀ : z₀ ∈ Ioo (-1) 1)
    (hV : sphericalPendulumEffectivePotential j z₀ < h) :
    2 * Real.pi / √(2 * (h + 3)) ≤ sphericalPendulumPeriod h j := by
  have hab := sphericalPendulumLowerTurningPoint_lt_sphericalPendulumUpperTurningPoint hj hz₀ hV
  have ha := neg_one_lt_sphericalPendulumLowerTurningPoint hj hz₀ hV
  have hpos := two_mul_sub_sub_sub_add_mul_sin_pos hj hz₀ hV
  rw [sphericalPendulumPeriod_eq_integral_sin hj hz₀ hV]
  set a := sphericalPendulumLowerTurningPoint h j
  set b := sphericalPendulumUpperTurningPoint h j
  -- The substituted height `z` lies in `[z₋, z₊]`, so `0 < z₃ - z < h + 3`.
  have hu (θ : ℝ) := mem_Icc_add_mul_sin hab.le θ
  have hcont : Continuous fun θ ↦ (√(2 * (h - a - b - ((a + b) / 2 + (b - a) / 2 *
      Real.sin θ))))⁻¹ :=
    Continuous.inv₀ (by fun_prop) fun θ ↦ (Real.sqrt_pos.2 (hpos θ)).ne'
  have hle := intervalIntegral.integral_mono_on
    (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ Real.pi / 2)
    intervalIntegrable_const (hcont.intervalIntegrable (μ := volume) _ _) fun θ _ ↦
      inv_anti₀ (Real.sqrt_pos.2 (hpos θ)) (Real.sqrt_le_sqrt (by linarith [(hu θ).1]) :
        √(2 * (h - a - b - ((a + b) / 2 + (b - a) / 2 * Real.sin θ))) ≤ √(2 * (h + 3)))
  rw [intervalIntegral.integral_const, smul_eq_mul] at hle
  calc 2 * Real.pi / √(2 * (h + 3))
      _ = 2 * ((Real.pi / 2 - -(Real.pi / 2)) * (√(2 * (h + 3)))⁻¹) := by ring
      _ ≤ _ := by gcongr

/-- **The period is even in the vertical angular momentum.** -/
@[simp]
theorem sphericalPendulumPeriod_neg_right (h j : ℝ) :
    sphericalPendulumPeriod h (-j) = sphericalPendulumPeriod h j := by
  simp only [sphericalPendulumPeriod_def, neg_sq]

/-- **Continuity of the period.** The period `T(h, j)` of the height is continuous on the values
`(h, j)` with `j ≠ 0` lying strictly above the curve of relative equilibria, that is, with
`V_j(z) < h` for some height `z ∈ (-1, 1)`. -/
theorem continuousOn_sphericalPendulumPeriod :
    ContinuousOn (fun c : ℝ × ℝ ↦ sphericalPendulumPeriod c.1 c.2)
      sphericalPendulumTurningPointDomain :=
  ((continuousOn_const (c := (2 : ℝ))).mul
    (continuousOn_integral_div_sqrt_two_mul_sub_mul_one_sub_sq_sub_sq
    (g := fun _ _ ↦ 1) continuousOn_const)).congr fun c _ ↦ by
      simp only [sphericalPendulumPeriod_def, one_div, Pi.mul_apply]

/-- **The period of the height of the spherical pendulum.** Above the curve of relative
equilibria, let a motion of the spherical pendulum with energy `h` and vertical angular momentum
`j` start at the lower turning point `z₋` at time `t₁`, reach the upper turning point `z₊` at time
`t₂` and return to `z₋` at time `t₃`, with its height strictly between the turning points at all
other times. Then the elapsed time `t₃ - t₁` is the period `T(h, j)`. -/
theorem sub_eq_sphericalPendulumPeriod_of_isMIntegralCurveOn {γ : ℝ → sphericalPendulumPhaseSpace}
    {t₁ t₂ t₃ : ℝ} (hj : j ≠ 0) (hz₀ : z₀ ∈ Ioo (-1) 1)
    (hV : sphericalPendulumEffectivePotential j z₀ < h) (ht₁₂ : t₁ ≤ t₂) (ht₂₃ : t₂ ≤ t₃)
    (hγ : IsMIntegralCurveOn γ (sphericalPendulumSymplecticForm.hamiltonianVectorField
      fun y ↦ sphericalPendulumHamiltonian y) (Icc t₁ t₃))
    (hF : sphericalPendulumEnergyMomentum (γ t₁) = (h, j))
    (h₁ : (γ t₁ : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 =
      sphericalPendulumLowerTurningPoint h j)
    (h₂ : (γ t₂ : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 =
      sphericalPendulumUpperTurningPoint h j)
    (h₃ : (γ t₃ : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 =
      sphericalPendulumLowerTurningPoint h j)
    (hmem : ∀ t ∈ Ioo t₁ t₂ ∪ Ioo t₂ t₃,
      (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 ∈
        Ioo (sphericalPendulumLowerTurningPoint h j) (sphericalPendulumUpperTurningPoint h j)) :
    t₃ - t₁ = sphericalPendulumPeriod h j := by
  have hpos := fun z ↦ two_mul_sub_mul_one_sub_sq_sub_sq_pos (z := z) hj hz₀ hV
  have hF₂ : sphericalPendulumEnergyMomentum (γ t₂) = (h, j) :=
    (sphericalPendulumEnergyMomentum_eq_of_isMIntegralCurveOn isPreconnected_Icc hγ
      (left_mem_Icc.2 (ht₁₂.trans ht₂₃)) ⟨ht₁₂, ht₂₃⟩).trans hF
  have hup := sub_eq_integral_inv_sqrt_of_isMIntegralCurveOn_sphericalPendulum ht₁₂
    (hγ.mono (Icc_subset_Icc_right ht₂₃)) hF hpos (Or.inl ⟨h₁, h₂⟩)
    fun t ht ↦ hmem t (Or.inl ht)
  have hdown := sub_eq_integral_inv_sqrt_of_isMIntegralCurveOn_sphericalPendulum ht₂₃
    (hγ.mono (Icc_subset_Icc_left ht₁₂)) hF₂ hpos (Or.inr ⟨h₂, h₃⟩)
    fun t ht ↦ hmem t (Or.inr ht)
  rw [sphericalPendulumPeriod_eq_integral hj hz₀ hV]
  linarith

end Regular

end TauCeti
