/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.SphericalPendulum.Integrable
public import TauCeti.Geometry.Symplectic.Hamiltonian.SphericalPendulum.RotationAngle
import TauCeti.Geometry.Manifold.IntegralCurve.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.MeasureTheory.Function.Jacobian.OneDim

/-!
# The equations of motion of the spherical pendulum and its period and rotation quadratures

On the phase space `T*S² = {(q, p) : ‖q‖ = 1, ⟪q, p⟫ = 0}` of the spherical pendulum, with the
restriction of the standard symplectic form of `ℝ³ × ℝ³`, the Hamiltonian vector field of the
energy `H(q, p) = ‖p‖² / 2 + q₃` is

`q' = p`,  `p' = (q₃ - ‖p‖²) q - e₃`

(`TauCeti.mfderiv_coe_hamiltonianVectorField_sphericalPendulumHamiltonian`).
The force is the weight `-e₃` plus the reaction `(q₃ - ‖p‖²) q` of the sphere, which is normal to
it and keeps the motion on the phase space. Unlike the ambient Hamiltonian vector field
`(p, -e₃)` of `H`, this field is tangent to the phase space, and it is the unique tangent vector
`v` with `ω₀(v, w) = dH(w)` for every tangent vector `w`
(`TauCeti.SmoothTwoForm.IsNondegenerate.mfderiv_hamiltonianVectorField_comp_eq_of_eval₂`).
So the integral curves of the energy are the solutions in the phase space of these equations
(`TauCeti.hasDerivAt_coe_sphericalPendulumPhaseSpace_of_isMIntegralCurve`), along which the
energy `H` and the vertical angular momentum `J = q₁ p₂ - q₂ p₁` are conserved
(`TauCeti.sphericalPendulumEnergyMomentum_eq_of_hasDerivAt`).

Along such a motion at the value `(h, j)` of `(H, J)`, the height `z = q₃` moves with velocity
`z' = p₃`, where `p₃² = 2 (h - z) (1 - z²) - j²`, and, away from the vertical axis, the azimuth
`θ` of the horizontal position `(q₁, q₂) = √(1 - z²) (cos θ, sin θ)` turns with angular velocity
`θ' = j / (1 - z²)` (`TauCeti.hasDerivAt_of_sphericalPendulum_polar`). These give the classical
quadratures. While the height
moves monotonically between two heights `z₁ < z₂` at which the radicand is positive in between,
the elapsed time and the azimuth swept are

`t₂ - t₁ = ∫_{z₁}^{z₂} dz / √(2 (h - z) (1 - z²) - j²)`,
`θ(t₂) - θ(t₁) = ∫_{z₁}^{z₂} j dz / ((1 - z²) √(2 (h - z) (1 - z²) - j²))`

(`TauCeti.sub_eq_integral_one_div_sqrt_of_sphericalPendulum`,
`TauCeti.sub_eq_integral_div_mul_sqrt_of_sphericalPendulum`). For `(h, j)` with `j ≠ 0` strictly
above the curve of relative equilibria, the height oscillates between the turning points
`z₋ < z₊`. A full oscillation of the height, from one turning point to the other and back, lasts
the **period**

`T(h, j) = 2 ∫_{z₋}^{z₊} dz / √(2 (h - z) (1 - z²) - j²)`

(`TauCeti.sphericalPendulumPeriod`, `TauCeti.sub_eq_sphericalPendulumPeriod`), and during it the
azimuth turns by the rotation angle `Θ(h, j)`
(`TauCeti.sub_eq_sphericalPendulumRotationAngle`). These are the period and rotation integrals of
the Liouville tori of the pendulum, which enter its rotation number and its Hamiltonian monodromy
around the focus–focus value `(1, 0)`. The statements take the oscillation of the height between
its turning points as a hypothesis on the motion; that every motion on a regular fibre oscillates
in this way is not proved here.

## Main declarations

* `TauCeti.sphericalPendulumVectorField`: the vector field `(q, p) ↦ (p, (q₃ - ‖p‖²) q - e₃)`.
* `TauCeti.mfderiv_coe_hamiltonianVectorField_sphericalPendulumHamiltonian`:
  it is the Hamiltonian vector field of the energy on the phase space.
* `TauCeti.hasDerivAt_coe_sphericalPendulumPhaseSpace_of_isMIntegralCurve`: integral curves of
  the energy solve the equations of motion.
* `TauCeti.sphericalPendulumEnergyMomentum_eq_of_hasDerivAt`: conservation of `(H, J)`.
* `TauCeti.hasDerivAt_of_sphericalPendulum_polar`: the azimuthal equation `θ' = j / (1 - z²)`.
* `TauCeti.sphericalPendulumPeriod`: the period `T(h, j)`, with
  `TauCeti.sphericalPendulumPeriod_eq_integral_turningPoint`.
* `TauCeti.sub_eq_integral_one_div_sqrt_of_sphericalPendulum`,
  `TauCeti.sub_eq_integral_div_mul_sqrt_of_sphericalPendulum`: time and azimuth between two
  heights.
* `TauCeti.sub_eq_sphericalPendulumPeriod`, `TauCeti.sub_eq_sphericalPendulumRotationAngle`: a
  full oscillation of the height lasts `T(h, j)` and turns the azimuth by `Θ(h, j)`.

## References

* R. H. Cushman and L. M. Bates, *Global Aspects of Classical Integrable Systems*, 2nd ed.,
  Birkhäuser, 2015, Chapter IV (the spherical pendulum).
* L. D. Landau and E. M. Lifshitz, *Mechanics*, 3rd ed., Pergamon, 1976, Section 14, Problem 1
  (the spherical pendulum).
-/

public section

open Function Set Filter MeasureTheory Real intervalIntegral
open scoped InnerProductSpace Manifold ContDiff Topology

namespace TauCeti

/-! ### The equations of motion -/

/-- The **equations of motion** of the spherical pendulum, as a vector field on `ℝ³ × ℝ³`:
`(q, p) ↦ (p, (q₃ - ‖p‖²) q - e₃)`. The momentum is the velocity, and the force is the weight
`-e₃` plus the reaction `(q₃ - ‖p‖²) q` of the sphere. On the phase space it is the Hamiltonian
vector field of the energy
(`TauCeti.mfderiv_coe_hamiltonianVectorField_sphericalPendulumHamiltonian`). -/
noncomputable def sphericalPendulumVectorField
    (x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) :=
  (x.2, (x.1 2 - ‖x.2‖ ^ 2) • x.1 - EuclideanSpace.single 2 1)

@[simp]
theorem sphericalPendulumVectorField_apply (q p : EuclideanSpace ℝ (Fin 3)) :
    sphericalPendulumVectorField (q, p) =
      (p, (q 2 - ‖p‖ ^ 2) • q - EuclideanSpace.single 2 1) :=
  (rfl)

@[simp]
theorem fst_sphericalPendulumVectorField
    (x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
    (sphericalPendulumVectorField x).1 = x.2 :=
  (rfl)

@[simp]
theorem snd_sphericalPendulumVectorField
    (x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
    (sphericalPendulumVectorField x).2 = (x.1 2 - ‖x.2‖ ^ 2) • x.1 - EuclideanSpace.single 2 1 :=
  (rfl)

/-- The equations of motion are tangent to the phase space: the reaction `(q₃ - ‖p‖²) q` is the
normal force keeping `‖q‖² = 1` and `⟪q, p⟫ = 0`. -/
theorem sphericalPendulumVectorField_mem_ker_fderiv_sphericalPendulumConstraint
    {x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ sphericalPendulumPhaseSpace) :
    sphericalPendulumVectorField x ∈ (fderiv ℝ sphericalPendulumConstraint x).ker := by
  obtain ⟨q, p⟩ := x
  obtain ⟨hq, hqp⟩ := mem_sphericalPendulumPhaseSpace.1 hx
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, fderiv_sphericalPendulumConstraint_apply]
  simp only [sphericalPendulumVectorField_apply, inner_sub_right, inner_smul_right,
    real_inner_self_eq_norm_sq, hq, hqp, EuclideanSpace.inner_single_right, Prod.mk_eq_zero]
  simp

/-- **The Hamiltonian vector field of the energy on the phase space** of the spherical pendulum is
the field of its equations of motion, `(q, p) ↦ (p, (q₃ - ‖p‖²) q - e₃)`: the differential of the
inclusion of the phase space carries it to `TauCeti.sphericalPendulumVectorField`. -/
theorem mfderiv_coe_hamiltonianVectorField_sphericalPendulumHamiltonian
    (x : sphericalPendulumPhaseSpace) :
    mfderiv 𝓘(ℝ, Fin 4 → ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))
        Subtype.val x (sphericalPendulumSymplecticForm.hamiltonianVectorField
          (fun y ↦ sphericalPendulumHamiltonian y) x) =
      sphericalPendulumVectorField x := by
  have hH : HasFDerivAt sphericalPendulumHamiltonian
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
        (fderiv ℝ sphericalPendulumEnergyMomentum (x : _ × _))) (x : _ × _) := by
    convert ((contDiff_sphericalPendulumEnergyMomentum (n := 1)).differentiable one_ne_zero
      (x : _ × _)).hasFDerivAt.fst using 1
    exact funext fun y ↦ (fst_sphericalPendulumEnergyMomentum y).symm
  have hk := range_mfderiv_coe_sphericalPendulumPhaseSpace x
  refine isSymplectic_sphericalPendulumSymplecticForm.isNondegenerate
    |>.mfderiv_hamiltonianVectorField_comp_eq_of_eval₂
      isSmoothEmbedding_coe_sphericalPendulumPhaseSpace.contMDiff
      sphericalPendulumSymplecticForm_def.symm (g := sphericalPendulumHamiltonian)
      hH.differentiableAt.mdifferentiableAt
      (by
        rw [hk]
        exact sphericalPendulumVectorField_mem_ker_fderiv_sphericalPendulumConstraint x.2)
      fun u ↦ ?_
  -- A tangent vector `(a, b)` has `⟪q, a⟫ = 0`, so `ω₀((p, λ q - e₃), (a, b)) = ⟪p, b⟫ + a₃`.
  obtain ⟨⟨q, p⟩, hx⟩ := x
  have hu : fderiv ℝ sphericalPendulumConstraint (q, p) (mfderiv 𝓘(ℝ, Fin 4 → ℝ)
      𝓘(ℝ, EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) Subtype.val ⟨(q, p), hx⟩ u) = 0 :=
    hk.le ⟨u, rfl⟩
  rw [mvfderiv_eq_fderiv_apply, hH.fderiv]
  generalize mfderiv 𝓘(ℝ, Fin 4 → ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))
    Subtype.val ⟨(q, p), hx⟩ u = w at hu ⊢
  obtain ⟨a, b⟩ := w
  rw [fderiv_sphericalPendulumConstraint_apply, Prod.mk_eq_zero] at hu
  have hqa : ⟪q, a⟫_ℝ = 0 := by simpa using hu.1
  refine (SymplecticForm.fromTangentSpace_constSmooth_apply _ _ _ _).trans ?_
  rw [NormedSpace.fromTangentSpace_apply (𝕜 := ℝ) (q, p) (sphericalPendulumVectorField (q, p)),
    NormedSpace.fromTangentSpace_apply (𝕜 := ℝ) (q, p) (a, b), ContinuousLinearMap.comp_apply,
    fderiv_sphericalPendulumEnergyMomentum_apply]
  simp [inner_sub_left, inner_smul_left, hqa, EuclideanSpace.inner_single_left]

/-! ### Motions -/

/-- **Integral curves of the energy solve the equations of motion.** If `γ` is an integral curve of
the Hamiltonian vector field of the energy on the phase space, then the curve `γ` in `ℝ³ × ℝ³`
satisfies `q' = p`, `p' = (q₃ - ‖p‖²) q - e₃`. -/
theorem hasDerivAt_coe_sphericalPendulumPhaseSpace_of_isMIntegralCurve
    {γ : ℝ → sphericalPendulumPhaseSpace}
    (hγ : IsMIntegralCurve γ (sphericalPendulumSymplecticForm.hamiltonianVectorField
      fun y ↦ sphericalPendulumHamiltonian y)) (t : ℝ) :
    HasDerivAt (fun s ↦ (γ s : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)))
      (sphericalPendulumVectorField (γ t)) t := by
  have h : IsMIntegralCurveOn (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)))
      (Subtype.val ∘ γ) (fun y ↦ sphericalPendulumVectorField y) univ :=
    (hγ.isMIntegralCurveOn univ).map_of_mfderiv_eq
      (fun s _ ↦ (isSmoothEmbedding_coe_sphericalPendulumPhaseSpace.contMDiff
        (γ s)).mdifferentiableAt (by simp))
      fun s _ ↦ mfderiv_coe_hamiltonianVectorField_sphericalPendulumHamiltonian (γ s)
  exact (isMIntegralCurveOn_iff_isIntegralCurveOn.1 h t (mem_univ t)).hasDerivAt univ_mem

section Motion

variable {c : ℝ → EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)} {t t₁ t₂ : ℝ}

/-- Along a solution of the equations of motion, each position coordinate `qᵢ` has velocity `pᵢ`. -/
private theorem hasDerivAt_fst_apply
    (hc : HasDerivAt c (sphericalPendulumVectorField (c t)) t) (i : Fin 3) :
    HasDerivAt (fun s ↦ (c s).1 i) ((c t).2 i) t :=
  ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).comp
    (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)))).hasFDerivAt
    |>.comp_hasDerivAt t hc

/-- Along a solution of the equations of motion in the phase space, the energy–momentum map has
derivative zero. -/
private theorem hasDerivAt_sphericalPendulumEnergyMomentum_comp
    (hmem : c t ∈ sphericalPendulumPhaseSpace)
    (hc : HasDerivAt c (sphericalPendulumVectorField (c t)) t) :
    HasDerivAt (fun s ↦ sphericalPendulumEnergyMomentum (c s)) 0 t := by
  have h := ((contDiff_sphericalPendulumEnergyMomentum (n := 1)).differentiable one_ne_zero
    (c t)).hasFDerivAt.comp_hasDerivAt t hc
  refine h.congr_deriv ?_
  obtain ⟨-, hqp⟩ := mem_sphericalPendulumPhaseSpace.1 hmem
  rw [fderiv_sphericalPendulumEnergyMomentum_apply]
  simp only [fst_sphericalPendulumVectorField, snd_sphericalPendulumVectorField, inner_sub_right,
    inner_smul_right, real_inner_comm (c t).1 (c t).2, hqp, EuclideanSpace.inner_single_right]
  simp
  ring

/-- **Conservation of energy and vertical angular momentum.** Along a solution of the equations of
motion of the spherical pendulum in its phase space, the energy `H` and the vertical angular
momentum `J` are constant. -/
theorem sphericalPendulumEnergyMomentum_eq_of_hasDerivAt
    (hmem : ∀ t ∈ Icc t₁ t₂, c t ∈ sphericalPendulumPhaseSpace)
    (hc : ∀ t ∈ Icc t₁ t₂, HasDerivAt c (sphericalPendulumVectorField (c t)) t) :
    ∀ t ∈ Icc t₁ t₂,
      sphericalPendulumEnergyMomentum (c t) = sphericalPendulumEnergyMomentum (c t₁) :=
  constant_of_has_deriv_right_zero
    (fun t ht ↦ (hasDerivAt_sphericalPendulumEnergyMomentum_comp (hmem t ht)
      (hc t ht)).continuousAt.continuousWithinAt)
    fun t ht ↦ (hasDerivAt_sphericalPendulumEnergyMomentum_comp (hmem t (Ico_subset_Icc_self ht))
      (hc t (Ico_subset_Icc_self ht))).hasDerivWithinAt

/-- **The azimuthal equation of motion.** Let `c` solve the equations of motion at `t`, off the
vertical axis, `q₃² < 1`. If near `t` its horizontal position is
`(q₁, q₂) = √(1 - q₃²) (cos θ, sin θ)` for a function `θ` differentiable at `t`, then the azimuth
`θ` turns with angular velocity `θ' = J / (1 - q₃²)`, where `J = q₁ p₂ - q₂ p₁` is the vertical
angular momentum. -/
theorem hasDerivAt_of_sphericalPendulum_polar {θ : ℝ → ℝ}
    (hc : HasDerivAt c (sphericalPendulumVectorField (c t)) t) (hz : (c t).1 2 ^ 2 < 1)
    (hpolar : ∀ᶠ s in 𝓝 t, (c s).1 0 = √(1 - (c s).1 2 ^ 2) * cos (θ s) ∧
      (c s).1 1 = √(1 - (c s).1 2 ^ 2) * sin (θ s))
    (hθ : DifferentiableAt ℝ θ t) :
    HasDerivAt θ ((sphericalPendulumEnergyMomentum (c t)).2 / (1 - (c t).1 2 ^ 2)) t := by
  set ρ : ℝ → ℝ := fun s ↦ √(1 - (c s).1 2 ^ 2)
  have hz' : 0 < 1 - (c t).1 2 ^ 2 := by linarith
  -- The derivative of the radius `ρ = √(1 - q₃²)` of the horizontal circle.
  obtain ⟨ρ', hρ⟩ : ∃ ρ', HasDerivAt ρ ρ' t :=
    ⟨_, (((hasDerivAt_fst_apply hc 2).pow 2).const_sub 1).sqrt hz'.ne'⟩
  have hθ' := hθ.hasDerivAt
  -- Differentiating `q₁ = ρ cos θ` and `q₂ = ρ sin θ` computes the horizontal velocity.
  have h₀ := (hasDerivAt_fst_apply hc 0).unique
    ((hρ.mul (hθ'.cos)).congr_of_eventuallyEq (hpolar.mono fun s hs ↦ hs.1))
  have h₁ := (hasDerivAt_fst_apply hc 1).unique
    ((hρ.mul (hθ'.sin)).congr_of_eventuallyEq (hpolar.mono fun s hs ↦ hs.2))
  obtain ⟨hp₀, hp₁⟩ : (c t).1 0 = ρ t * cos (θ t) ∧ (c t).1 1 = ρ t * sin (θ t) :=
    hpolar.self_of_nhds
  have hρ2 : ρ t ^ 2 = 1 - (c t).1 2 ^ 2 := Real.sq_sqrt hz'.le
  have hJ : (sphericalPendulumEnergyMomentum (c t)).2 =
      (c t).1 0 * (c t).2 1 - (c t).1 1 * (c t).2 0 :=
    congrArg Prod.snd (sphericalPendulumEnergyMomentum_apply (c t).1 (c t).2)
  convert hθ' using 1
  rw [hJ, h₀, h₁, hp₀, hp₁, div_eq_iff hz'.ne', ← hρ2]
  linear_combination (ρ t ^ 2 * deriv θ t) * (sin_sq_add_cos_sq (θ t))

/-! ### Time and azimuth between two heights -/

variable {h j z₁ z₂ : ℝ}

/-- The hypotheses shared by the time and azimuth formulas along a monotone stretch of the height
give `z₁ ≤ z₂`, the vertical momentum `|p₃| = √(2 (h - z) (1 - z²) - j²) ≠ 0` in between, and the
change of variables from time to height. -/
private theorem leg_data (ht : t₁ ≤ t₂)
    (hmem : ∀ t ∈ Icc t₁ t₂, c t ∈ sphericalPendulumPhaseSpace)
    (hc : ∀ t ∈ Icc t₁ t₂, HasDerivAt c (sphericalPendulumVectorField (c t)) t)
    (hF : sphericalPendulumEnergyMomentum (c t₁) = (h, j))
    (hpos : ∀ z ∈ Ioo z₁ z₂, 0 < 2 * (h - z) * (1 - z ^ 2) - j ^ 2)
    (hends : (c t₁).1 2 = z₁ ∧ (c t₂).1 2 = z₂ ∨ (c t₁).1 2 = z₂ ∧ (c t₂).1 2 = z₁)
    (hbetween : ∀ t ∈ Ioo t₁ t₂, (c t).1 2 ∈ Ioo z₁ z₂) :
    z₁ ≤ z₂ ∧
      (∀ t ∈ Ioo t₁ t₂, |(c t).2 2| = √(2 * (h - (c t).1 2) * (1 - (c t).1 2 ^ 2) - j ^ 2) ∧
        (c t).2 2 ≠ 0) ∧
      ∀ g : ℝ → ℝ, ∫ z in Ioo z₁ z₂, g z = ∫ t in Ioo t₁ t₂, |(c t).2 2| * g ((c t).1 2) := by
  have hIoo : Ioo t₁ t₂ ⊆ Icc t₁ t₂ := Ioo_subset_Icc_self
  have hFt := sphericalPendulumEnergyMomentum_eq_of_hasDerivAt hmem hc
  -- On the level `(h, j)`, `p₃² = 2 (h - z) (1 - z²) - j² > 0` strictly between the heights.
  have hp (t : ℝ) (htI : t ∈ Ioo t₁ t₂) :
      |(c t).2 2| = √(2 * (h - (c t).1 2) * (1 - (c t).1 2 ^ 2) - j ^ 2) ∧ (c t).2 2 ≠ 0 := by
    have hsq := sq_snd_two_eq_of_mem_sphericalPendulumPhaseSpace (hmem t (hIoo htI))
    rw [hFt t (hIoo htI), hF] at hsq
    refine ⟨by rw [← hsq, Real.sqrt_sq_eq_abs], fun h0 ↦ ?_⟩
    have := hpos _ (hbetween t htI)
    rw [← hsq, h0] at this
    simp at this
  have hzc : ContinuousOn (fun t ↦ (c t).1 2) (Icc t₁ t₂) :=
    fun t ht ↦ (hasDerivAt_fst_apply (hc t ht) 2).continuousAt.continuousWithinAt
  have himage : (fun t ↦ (c t).1 2) '' Ioo t₁ t₂ = Ioo z₁ z₂ := by
    refine (MapsTo.image_subset hbetween).antisymm ?_
    rcases hends with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · simpa only [h₁, h₂] using intermediate_value_Ioo ht hzc
    · simpa only [h₁, h₂] using intermediate_value_Ioo' ht hzc
  have h₁₂ : z₁ ≤ z₂ := by
    rcases ht.eq_or_lt with rfl | ht'
    · rcases hends with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> linarith
    · obtain ⟨h₁, h₂⟩ := hbetween _ ⟨left_lt_add_div_two.2 ht', add_div_two_lt_right.2 ht'⟩
      exact (h₁.trans h₂).le
  refine ⟨h₁₂, hp, fun g ↦ ?_⟩
  rw [← himage, integral_image_eq_integral_abs_deriv_smul_of_ne_zero (convex_Ioo t₁ t₂)
    (fun t htI ↦ (hasDerivAt_fst_apply (hc t (hIoo htI)) 2).hasDerivWithinAt)
    (fun t htI ↦ (hp t htI).2) g]
  simp only [smul_eq_mul]

/-- **The time between two heights.** Let `c` solve the equations of motion of the spherical
pendulum in its phase space on `[t₁, t₂]`, at the value `(h, j)` of the energy and the vertical
angular momentum. Suppose the height `z = q₃` moves from one of `z₁`, `z₂` to the other, staying
strictly between them meanwhile, where the radicand `2 (h - z) (1 - z²) - j²` is positive. Then
the elapsed time is

`t₂ - t₁ = ∫_{z₁}^{z₂} dz / √(2 (h - z) (1 - z²) - j²)`. -/
theorem sub_eq_integral_one_div_sqrt_of_sphericalPendulum (ht : t₁ ≤ t₂)
    (hmem : ∀ t ∈ Icc t₁ t₂, c t ∈ sphericalPendulumPhaseSpace)
    (hc : ∀ t ∈ Icc t₁ t₂, HasDerivAt c (sphericalPendulumVectorField (c t)) t)
    (hF : sphericalPendulumEnergyMomentum (c t₁) = (h, j))
    (hpos : ∀ z ∈ Ioo z₁ z₂, 0 < 2 * (h - z) * (1 - z ^ 2) - j ^ 2)
    (hends : (c t₁).1 2 = z₁ ∧ (c t₂).1 2 = z₂ ∨ (c t₁).1 2 = z₂ ∧ (c t₂).1 2 = z₁)
    (hbetween : ∀ t ∈ Ioo t₁ t₂, (c t).1 2 ∈ Ioo z₁ z₂) :
    t₂ - t₁ = ∫ z in z₁..z₂, 1 / √(2 * (h - z) * (1 - z ^ 2) - j ^ 2) := by
  obtain ⟨h₁₂, hp, hcov⟩ := leg_data ht hmem hc hF hpos hends hbetween
  rw [integral_of_le h₁₂, integral_Ioc_eq_integral_Ioo, hcov,
    setIntegral_congr_fun measurableSet_Ioo (g := fun _ ↦ (1 : ℝ)) fun t htI ↦ ?_,
    setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Ioo_of_le ht]
  rw [← (hp t htI).1, mul_one_div, div_self (abs_ne_zero.2 (hp t htI).2)]

/-- **The azimuth swept between two heights.** Under the hypotheses of
`TauCeti.sub_eq_integral_one_div_sqrt_of_sphericalPendulum`, let the horizontal position be
`(q₁, q₂) = √(1 - z²) (cos θ, sin θ)` on `[t₁, t₂]`, for an azimuth `θ` continuous on `[t₁, t₂]`
and differentiable on `(t₁, t₂)`. Then the azimuth swept is

`θ(t₂) - θ(t₁) = ∫_{z₁}^{z₂} j dz / ((1 - z²) √(2 (h - z) (1 - z²) - j²))`. -/
theorem sub_eq_integral_div_mul_sqrt_of_sphericalPendulum (ht : t₁ ≤ t₂)
    (hmem : ∀ t ∈ Icc t₁ t₂, c t ∈ sphericalPendulumPhaseSpace)
    (hc : ∀ t ∈ Icc t₁ t₂, HasDerivAt c (sphericalPendulumVectorField (c t)) t)
    (hF : sphericalPendulumEnergyMomentum (c t₁) = (h, j))
    (hpos : ∀ z ∈ Ioo z₁ z₂, 0 < 2 * (h - z) * (1 - z ^ 2) - j ^ 2)
    (hends : (c t₁).1 2 = z₁ ∧ (c t₂).1 2 = z₂ ∨ (c t₁).1 2 = z₂ ∧ (c t₂).1 2 = z₁)
    (hbetween : ∀ t ∈ Ioo t₁ t₂, (c t).1 2 ∈ Ioo z₁ z₂) {θ : ℝ → ℝ}
    (hpolar : ∀ t ∈ Icc t₁ t₂, (c t).1 0 = √(1 - (c t).1 2 ^ 2) * cos (θ t) ∧
      (c t).1 1 = √(1 - (c t).1 2 ^ 2) * sin (θ t))
    (hθc : ContinuousOn θ (Icc t₁ t₂)) (hθd : ∀ t ∈ Ioo t₁ t₂, DifferentiableAt ℝ θ t) :
    θ t₂ - θ t₁ = ∫ z in z₁..z₂, j / ((1 - z ^ 2) * √(2 * (h - z) * (1 - z ^ 2) - j ^ 2)) := by
  obtain ⟨h₁₂, hp, hcov⟩ := leg_data ht hmem hc hF hpos hends hbetween
  have hIoo : Ioo t₁ t₂ ⊆ Icc t₁ t₂ := Ioo_subset_Icc_self
  have hFt := sphericalPendulumEnergyMomentum_eq_of_hasDerivAt hmem hc
  rcases eq_or_ne j 0 with rfl | hj
  · -- For `j = 0` the azimuth is constant, since the radicand `2 (h - z) (1 - z²)` is positive
    -- and so `z² < 1` in between.
    have hθ0 (t : ℝ) (htI : t ∈ Ioo t₁ t₂) : HasDerivAt θ 0 t := by
      have hzt := hpos _ (hbetween t htI)
      have hz := apply_two_mem_Icc_of_mem_sphericalPendulumPhaseSpace (hmem t (hIoo htI))
      have h1 : 0 ≤ 1 - (c t).1 2 ^ 2 := by nlinarith [hz.1, hz.2]
      have h2 : 1 - (c t).1 2 ^ 2 ≠ 0 := fun h0 ↦ by simp [h0] at hzt
      have h := hasDerivAt_of_sphericalPendulum_polar (hc t (hIoo htI))
        (by linarith [lt_of_le_of_ne h1 h2.symm])
        (eventually_of_mem (Icc_mem_nhds htI.1 htI.2) hpolar) (hθd t htI)
      rwa [hFt t (hIoo htI), hF, zero_div] at h
    rw [← integral_eq_sub_of_hasDerivAt_of_le ht hθc hθ0 intervalIntegrable_const]
    simp
  -- Off the vertical axis, since `J = j ≠ 0`.
  have hz (t : ℝ) (ht : t ∈ Icc t₁ t₂) : 0 < 1 - (c t).1 2 ^ 2 := by
    have hJ : (sphericalPendulumEnergyMomentum (c t)).2 ≠ 0 := by rwa [hFt t ht, hF]
    have := apply_two_mem_Ioo_of_snd_sphericalPendulumEnergyMomentum_ne_zero (hmem t ht) hJ
    nlinarith [this.1, this.2]
  -- The azimuth turns with angular velocity `j / (1 - z²)`.
  have hθ (t : ℝ) (htI : t ∈ Ioo t₁ t₂) : HasDerivAt θ (j / (1 - (c t).1 2 ^ 2)) t := by
    have h := hasDerivAt_of_sphericalPendulum_polar (hc t (hIoo htI))
      (by linarith [hz t (hIoo htI)])
      (eventually_of_mem (Icc_mem_nhds htI.1 htI.2) hpolar) (hθd t htI)
    rwa [hFt t (hIoo htI), hF] at h
  have hcont : ContinuousOn (fun t ↦ j / (1 - (c t).1 2 ^ 2)) (Icc t₁ t₂) := fun t ht ↦
    (continuousAt_const.div (continuousAt_const.sub
      ((hasDerivAt_fst_apply (hc t ht) 2).continuousAt.pow 2))
      (hz t ht).ne').continuousWithinAt
  rw [← integral_eq_sub_of_hasDerivAt_of_le ht hθc hθ (hcont.intervalIntegrable_of_Icc ht),
    integral_of_le h₁₂, integral_Ioc_eq_integral_Ioo, hcov, integral_of_le ht,
    integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun t htI ↦ ?_
  have hz' := (hz t (hIoo htI)).ne'
  rw [← (hp t htI).1]
  field_simp [abs_ne_zero.2 (hp t htI).2]

end Motion

/-! ### The period and a full oscillation of the height -/

/-- The **period** `T(h, j) = 2 ∫ dz / √(2 (h - z) (1 - z²) - j²)` of the height of the spherical
pendulum at energy `h` and vertical angular momentum `j`. The integral runs over `(-1, 1)`, but
the integrand vanishes at every height `z` with `2 (h - z) (1 - z²) ≤ j²`, so for a regular value
it is twice the integral between the two turning points of the height
(`TauCeti.sphericalPendulumPeriod_eq_integral_turningPoint`). It is the duration of a full
oscillation of the height (`TauCeti.sub_eq_sphericalPendulumPeriod`). -/
noncomputable def sphericalPendulumPeriod (h j : ℝ) : ℝ :=
  2 * ∫ z in (-1)..1, 1 / √(2 * (h - z) * (1 - z ^ 2) - j ^ 2)

theorem sphericalPendulumPeriod_def (h j : ℝ) :
    sphericalPendulumPeriod h j = 2 * ∫ z in (-1)..1, 1 / √(2 * (h - z) * (1 - z ^ 2) - j ^ 2) :=
  (rfl)

/-- The period is even in the angular momentum. -/
@[simp]
theorem sphericalPendulumPeriod_neg_right (h j : ℝ) :
    sphericalPendulumPeriod h (-j) = sphericalPendulumPeriod h j := by
  simp only [sphericalPendulumPeriod_def, neg_sq]

/-- **The period between the turning points.** For `(h, j)` with `j ≠ 0` strictly above the curve
of relative equilibria, the period is twice the integral between the turning points `z₋ < z₊`:
`T(h, j) = 2 ∫_{z₋}^{z₊} dz / √(2 (h - z) (1 - z²) - j²)`. -/
theorem sphericalPendulumPeriod_eq_integral_turningPoint {h j : ℝ}
    (hc : (h, j) ∈ sphericalPendulumTurningPointDomain) :
    sphericalPendulumPeriod h j =
      2 * ∫ z in sphericalPendulumLowerTurningPoint h j..sphericalPendulumUpperTurningPoint h j,
        1 / √(2 * (h - z) * (1 - z ^ 2) - j ^ 2) := by
  rw [sphericalPendulumPeriod_def,
    integral_neg_one_one_eq_integral_sphericalPendulumTurningPoint hc fun z hz ↦ by
      rw [Real.sqrt_eq_zero'.2 hz, div_zero]]

section Oscillation

variable {c : ℝ → EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)} {t₁ t₂ t₃ h j : ℝ}

/-- Strictly between the turning points the radicand is positive. -/
private theorem radicand_pos_of_mem_Ioo (hc : (h, j) ∈ sphericalPendulumTurningPointDomain) :
    ∀ z ∈ Ioo (sphericalPendulumLowerTurningPoint h j) (sphericalPendulumUpperTurningPoint h j),
      0 < 2 * (h - z) * (1 - z ^ 2) - j ^ 2 := by
  obtain ⟨hj, z₀, hz₀, hV⟩ := mem_sphericalPendulumTurningPointDomain_iff.1 hc
  have hb := sphericalPendulumUpperTurningPoint_lt_one hj hz₀ hV
  have hc₃ := one_lt_sub_sphericalPendulumLowerTurningPoint_sub_sphericalPendulumUpperTurningPoint
    hj hz₀ hV
  intro z hz
  rw [two_mul_sub_mul_one_sub_sq_sub_sq_eq hj hz₀ hV z]
  have := mul_pos (mul_pos (sub_pos.2 hz.1) (sub_pos.2 hz.2))
    (by linarith [hz.2] : (0 : ℝ) < h - sphericalPendulumLowerTurningPoint h j -
      sphericalPendulumUpperTurningPoint h j - z)
  linarith

/-- **A full oscillation of the height lasts one period.** Let `c` solve the equations of motion
of the spherical pendulum in its phase space on `[t₁, t₃]`, at a value `(h, j)` of the energy and
the vertical angular momentum with `j ≠ 0` strictly above the curve of relative equilibria. Suppose
the height moves from one turning point `z₋`, `z₊` to the other during `[t₁, t₂]` and back during
`[t₂, t₃]`, staying strictly between them except at these times. Then `t₃ - t₁ = T(h, j)`. -/
theorem sub_eq_sphericalPendulumPeriod (ht₁₂ : t₁ ≤ t₂) (ht₂₃ : t₂ ≤ t₃)
    (hmem : ∀ t ∈ Icc t₁ t₃, c t ∈ sphericalPendulumPhaseSpace)
    (hc : ∀ t ∈ Icc t₁ t₃, HasDerivAt c (sphericalPendulumVectorField (c t)) t)
    (hF : sphericalPendulumEnergyMomentum (c t₁) = (h, j))
    (hD : (h, j) ∈ sphericalPendulumTurningPointDomain)
    (hends : (c t₁).1 2 = sphericalPendulumLowerTurningPoint h j ∧
        (c t₂).1 2 = sphericalPendulumUpperTurningPoint h j ∨
      (c t₁).1 2 = sphericalPendulumUpperTurningPoint h j ∧
        (c t₂).1 2 = sphericalPendulumLowerTurningPoint h j)
    (h₃ : (c t₃).1 2 = (c t₁).1 2)
    (hbetween₁₂ : ∀ t ∈ Ioo t₁ t₂, (c t).1 2 ∈
      Ioo (sphericalPendulumLowerTurningPoint h j) (sphericalPendulumUpperTurningPoint h j))
    (hbetween₂₃ : ∀ t ∈ Ioo t₂ t₃, (c t).1 2 ∈
      Ioo (sphericalPendulumLowerTurningPoint h j) (sphericalPendulumUpperTurningPoint h j)) :
    t₃ - t₁ = sphericalPendulumPeriod h j := by
  have hsub₁ : Icc t₁ t₂ ⊆ Icc t₁ t₃ := Icc_subset_Icc_right ht₂₃
  have hsub₂ : Icc t₂ t₃ ⊆ Icc t₁ t₃ := Icc_subset_Icc_left ht₁₂
  have hF₂ := (sphericalPendulumEnergyMomentum_eq_of_hasDerivAt hmem hc t₂ ⟨ht₁₂, ht₂₃⟩).trans hF
  have h₁ := sub_eq_integral_one_div_sqrt_of_sphericalPendulum ht₁₂ (fun t ht ↦ hmem t (hsub₁ ht))
    (fun t ht ↦ hc t (hsub₁ ht)) hF (radicand_pos_of_mem_Ioo hD) hends hbetween₁₂
  have h₂ := sub_eq_integral_one_div_sqrt_of_sphericalPendulum ht₂₃ (fun t ht ↦ hmem t (hsub₂ ht))
    (fun t ht ↦ hc t (hsub₂ ht)) hF₂ (radicand_pos_of_mem_Ioo hD) (by rw [h₃]; tauto)
    hbetween₂₃
  rw [sphericalPendulumPeriod_eq_integral_turningPoint hD]
  linarith

/-- **A full oscillation of the height turns the azimuth by the rotation angle.** Under the
hypotheses of `TauCeti.sub_eq_sphericalPendulumPeriod`, let the horizontal position be
`(q₁, q₂) = √(1 - z²) (cos θ, sin θ)` on `[t₁, t₃]`, for an azimuth `θ` continuous on `[t₁, t₃]`
and differentiable on `(t₁, t₃)`. Then `θ(t₃) - θ(t₁) = Θ(h, j)`. -/
theorem sub_eq_sphericalPendulumRotationAngle (ht₁₂ : t₁ ≤ t₂) (ht₂₃ : t₂ ≤ t₃)
    (hmem : ∀ t ∈ Icc t₁ t₃, c t ∈ sphericalPendulumPhaseSpace)
    (hc : ∀ t ∈ Icc t₁ t₃, HasDerivAt c (sphericalPendulumVectorField (c t)) t)
    (hF : sphericalPendulumEnergyMomentum (c t₁) = (h, j))
    (hD : (h, j) ∈ sphericalPendulumTurningPointDomain)
    (hends : (c t₁).1 2 = sphericalPendulumLowerTurningPoint h j ∧
        (c t₂).1 2 = sphericalPendulumUpperTurningPoint h j ∨
      (c t₁).1 2 = sphericalPendulumUpperTurningPoint h j ∧
        (c t₂).1 2 = sphericalPendulumLowerTurningPoint h j)
    (h₃ : (c t₃).1 2 = (c t₁).1 2)
    (hbetween₁₂ : ∀ t ∈ Ioo t₁ t₂, (c t).1 2 ∈
      Ioo (sphericalPendulumLowerTurningPoint h j) (sphericalPendulumUpperTurningPoint h j))
    (hbetween₂₃ : ∀ t ∈ Ioo t₂ t₃, (c t).1 2 ∈
      Ioo (sphericalPendulumLowerTurningPoint h j) (sphericalPendulumUpperTurningPoint h j))
    {θ : ℝ → ℝ}
    (hpolar : ∀ t ∈ Icc t₁ t₃, (c t).1 0 = √(1 - (c t).1 2 ^ 2) * cos (θ t) ∧
      (c t).1 1 = √(1 - (c t).1 2 ^ 2) * sin (θ t))
    (hθc : ContinuousOn θ (Icc t₁ t₃)) (hθd : ∀ t ∈ Ioo t₁ t₃, DifferentiableAt ℝ θ t) :
    θ t₃ - θ t₁ = sphericalPendulumRotationAngle h j := by
  have hsub₁ : Icc t₁ t₂ ⊆ Icc t₁ t₃ := Icc_subset_Icc_right ht₂₃
  have hsub₂ : Icc t₂ t₃ ⊆ Icc t₁ t₃ := Icc_subset_Icc_left ht₁₂
  have hIoo₁ : Ioo t₁ t₂ ⊆ Ioo t₁ t₃ := Ioo_subset_Ioo_right ht₂₃
  have hIoo₂ : Ioo t₂ t₃ ⊆ Ioo t₁ t₃ := Ioo_subset_Ioo_left ht₁₂
  have hF₂ := (sphericalPendulumEnergyMomentum_eq_of_hasDerivAt hmem hc t₂ ⟨ht₁₂, ht₂₃⟩).trans hF
  have h₁ := sub_eq_integral_div_mul_sqrt_of_sphericalPendulum ht₁₂
    (fun t ht ↦ hmem t (hsub₁ ht)) (fun t ht ↦ hc t (hsub₁ ht)) hF
    (radicand_pos_of_mem_Ioo hD) hends hbetween₁₂ (fun t ht ↦ hpolar t (hsub₁ ht))
    (hθc.mono hsub₁) fun t ht ↦ hθd t (hIoo₁ ht)
  have h₂ := sub_eq_integral_div_mul_sqrt_of_sphericalPendulum ht₂₃
    (fun t ht ↦ hmem t (hsub₂ ht)) (fun t ht ↦ hc t (hsub₂ ht)) hF₂
    (radicand_pos_of_mem_Ioo hD) (by rw [h₃]; tauto) hbetween₂₃
    (fun t ht ↦ hpolar t (hsub₂ ht)) (hθc.mono hsub₂) fun t ht ↦ hθd t (hIoo₂ ht)
  rw [sphericalPendulumRotationAngle_eq_integral_turningPoint hD]
  linarith

end Oscillation

end TauCeti
