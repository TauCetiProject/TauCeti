/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Darboux.Basis
public import TauCeti.Geometry.Symplectic.Hamiltonian.Elliptic
public import TauCeti.Geometry.Symplectic.Hamiltonian.SphericalPendulum.FocusFocus
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import TauCeti.Analysis.Calculus.FDeriv.Norm
import TauCeti.Analysis.Calculus.Morse.NormSq
import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson.Nondegenerate

/-!
# The stable equilibrium of the spherical pendulum is an elliptic–elliptic point

The phase space of the spherical pendulum is `T*S² = {(q, p) : ‖q‖ = 1, ⟪q, p⟫ = 0}` inside
`ℝ³ × ℝ³` (`TauCeti.sphericalPendulumPhaseSpace`), with the symplectic form restricted from
`ω₀((a, b), (a', b')) = ⟪a, b'⟫ - ⟪b, a'⟫`, and the energy–momentum map is `F = (H, J)`,
`H(q, p) = ‖p‖² / 2 + q₃` and `J(q, p) = q₁ p₂ - q₂ p₁`
(`TauCeti.sphericalPendulumEnergyMomentum`). This file shows that the stable equilibrium, the
pendulum at rest at the south pole `(q, p) = (-e₃, 0)`, is a nondegenerate rank-zero point of `F`
of elliptic–elliptic type. The unstable equilibrium at the north pole is a focus–focus point
(`TauCeti.Geometry.Symplectic.Hamiltonian.SphericalPendulum.FocusFocus`).

Over a point `x` of the open unit disc, the point of the lower hemisphere is
`q(x) = (x₁, x₂, -√(1 - ‖x‖²))`, and a covector `ξ` on the disc is lifted to the tangent vector
`p = (ξ, 0) - ⟪ξ, x⟫ q(x)` at `q(x)`, the one with `⟪p, dq_x v⟫ = ⟪ξ, v⟫`. The map
`(x, ξ) ↦ (q(x), p)` (`TauCeti.sphericalPendulumLowerParam`) is the cotangent lift of the graph
parametrization of the lower hemisphere. It is the canonical chart of the north pole,
`TauCeti.sphericalPendulumUpperParam`, followed by the reflection `(q, p) ↦ (σ q, σ p)` in the
horizontal plane, `σ(q₁, q₂, q₃) = (q₁, q₂, -q₃)`. That reflection preserves the phase space and the
symplectic form and exchanges the two hemispheres, so the chart maps the open set `{‖x‖ < 1}`
bijectively onto the points of the phase space with `q₃ < 0`
(`TauCeti.bijOn_sphericalPendulumLowerParam`), is smooth there, and pulls `ω₀` back to the standard
form `⟪x, ξ'⟫ - ⟪ξ, x'⟫` of `ℝ² × ℝ²`
(`TauCeti.stdSymplecticForm_fderiv_sphericalPendulumLowerParam`): it is a Darboux parametrization
of a neighbourhood of the south pole, with `(0, 0) ↦ (-e₃, 0)`.

The reflection fixes `J` and turns the height `q₃` into `-q₃`, so the energy–momentum maps read
in the two charts differ by `(2 √(1 - ‖x‖²), 0)`
(`TauCeti.sphericalPendulumEnergyMomentum_sphericalPendulumLowerParam`). In the lower chart
`H = (‖ξ‖² - ⟪ξ, x⟫²) / 2 - √(1 - ‖x‖²)` and `J = x₁ ξ₂ - x₂ ξ₁`, the origin is a critical point
of `F`, and the Hessians there are `‖ξ‖² + ‖x‖²` and `2 (x₁ ξ₂ - x₂ ξ₁)`. In the Darboux
coordinates

`Q₁ = (x₁ - ξ₂) / √2`, `P₁ = (x₂ + ξ₁) / √2`, `Q₂ = (x₁ + ξ₂) / √2`, `P₂ = (ξ₁ - x₂) / √2`

the two Hessians are `(Q₁² + P₁²) + (Q₂² + P₂²)` and `(Q₂² + P₂²) - (Q₁² + P₁²)`, so they span the
same space as the two elliptic blocks `(Qₖ² + Pₖ²) / 2`
(`TauCeti.exists_isDarbouxBasis_span_hessian_sphericalPendulumLowerParam_eq_span_elliptic`). The
elliptic blocks span a Cartan subalgebra of `sp(4, ℝ)`
(`TauCeti.SymplecticForm.IsDarbouxBasis.isNondegenerateQuadraticFamily_elliptic`), hence the origin
is a nondegenerate rank-zero point of `F` read in these coordinates
(`isNondegenerateRankZeroPoint_sphericalPendulumEnergyMomentum_comp_sphericalPendulumLowerParam`),
of elliptic–elliptic type in Williamson's classification. At the north pole the energy Hessian is
`‖ξ‖² - ‖x‖²` instead, and the type is focus–focus.

## Main results

* `TauCeti.sphericalPendulumLowerParam`: canonical coordinates on the cotangent bundle of the lower
  hemisphere.
* `TauCeti.bijOn_sphericalPendulumLowerParam`: they parametrize the points of the phase space with
  `q₃ < 0` bijectively.
* `TauCeti.stdSymplecticForm_fderiv_sphericalPendulumLowerParam`: they are symplectic.
* `TauCeti.hessianQuadraticForm_sphericalPendulumHamiltonian_comp_sphericalPendulumLowerParam_zero`,
  `TauCeti.hessianQuadraticForm_angularMomentum_comp_sphericalPendulumLowerParam_zero`: the
  Hessians of `H` and `J` at the south pole in these coordinates.
* `TauCeti.exists_isDarbouxBasis_span_hessian_sphericalPendulumLowerParam_eq_span_elliptic`: the
  Hessians span the space of the two elliptic blocks of a Darboux basis.
* `isNondegenerateRankZeroPoint_sphericalPendulumEnergyMomentum_comp_sphericalPendulumLowerParam`:
  the south pole equilibrium is a nondegenerate rank-zero point.

## References

* R. H. Cushman and L. M. Bates, *Global Aspects of Classical Integrable Systems*, 2nd ed.,
  Birkhäuser, 2015, Chapter IV (the spherical pendulum and its equilibria).
* A. V. Bolsinov and A. T. Fomenko, *Integrable Hamiltonian Systems: Geometry, Topology,
  Classification*, Chapman & Hall/CRC, 2004, Chapter 1 (nondegenerate singular points and their
  elliptic and focus–focus types).
-/

public section

open Set
open scoped InnerProductSpace

namespace TauCeti

/-! ### Canonical coordinates near the south pole -/

/-- Canonical coordinates on the cotangent bundle of the lower unit hemisphere, as a map into the
phase space `T*S² ⊆ ℝ³ × ℝ³` of the spherical pendulum: `(x, ξ)` is sent to the point
`q = (x₁, x₂, -√(1 - ‖x‖²))` of the sphere and the momentum `p = (ξ, 0) - ⟪ξ, x⟫ q`, the tangent
vector at `q` whose pairing with `dq_x v` is `⟪ξ, v⟫`. It is the cotangent lift of the graph
parametrization of the hemisphere. -/
noncomputable def sphericalPendulumLowerParam
    (z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) :=
  let q : EuclideanSpace ℝ (Fin 3) :=
    z.1 0 • EuclideanSpace.single 0 1 + z.1 1 • EuclideanSpace.single 1 1 -
      √(1 - ‖z.1‖ ^ 2) • EuclideanSpace.single 2 1
  (q, z.2 0 • EuclideanSpace.single 0 1 + z.2 1 • EuclideanSpace.single 1 1 - ⟪z.2, z.1⟫_ℝ • q)

variable (z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))

/-- The position `q = (x₁, x₂, -√(1 - ‖x‖²))` in the canonical coordinates `(x, ξ)`. -/
theorem sphericalPendulumLowerParam_fst : (sphericalPendulumLowerParam z).1 =
    z.1 0 • EuclideanSpace.single 0 1 + z.1 1 • EuclideanSpace.single 1 1 -
      √(1 - ‖z.1‖ ^ 2) • EuclideanSpace.single 2 1 :=
  (rfl)

/-- The momentum `p = (ξ, 0) - ⟪ξ, x⟫ q` in the canonical coordinates `(x, ξ)`. -/
theorem sphericalPendulumLowerParam_snd : (sphericalPendulumLowerParam z).2 =
    z.2 0 • EuclideanSpace.single 0 1 + z.2 1 • EuclideanSpace.single 1 1 -
      ⟪z.2, z.1⟫_ℝ • (sphericalPendulumLowerParam z).1 :=
  (rfl)

/-- The first coordinate of the position is `x₁`. -/
@[simp]
theorem sphericalPendulumLowerParam_fst_apply_zero :
    (sphericalPendulumLowerParam z).1 0 = z.1 0 := by
  simp [sphericalPendulumLowerParam_fst]

/-- The second coordinate of the position is `x₂`. -/
@[simp]
theorem sphericalPendulumLowerParam_fst_apply_one :
    (sphericalPendulumLowerParam z).1 1 = z.1 1 := by
  simp [sphericalPendulumLowerParam_fst]

/-- The height of the position is `-√(1 - ‖x‖²)`. -/
@[simp]
theorem sphericalPendulumLowerParam_fst_apply_two :
    (sphericalPendulumLowerParam z).1 2 = -√(1 - ‖z.1‖ ^ 2) := by
  simp [sphericalPendulumLowerParam_fst]

/-- The first coordinate of the momentum is `ξ₁ - ⟪ξ, x⟫ x₁`. -/
@[simp]
theorem sphericalPendulumLowerParam_snd_apply_zero :
    (sphericalPendulumLowerParam z).2 0 = z.2 0 - ⟪z.2, z.1⟫_ℝ * z.1 0 := by
  simp [sphericalPendulumLowerParam_snd, sphericalPendulumLowerParam_fst]

/-- The second coordinate of the momentum is `ξ₂ - ⟪ξ, x⟫ x₂`. -/
@[simp]
theorem sphericalPendulumLowerParam_snd_apply_one :
    (sphericalPendulumLowerParam z).2 1 = z.2 1 - ⟪z.2, z.1⟫_ℝ * z.1 1 := by
  simp [sphericalPendulumLowerParam_snd, sphericalPendulumLowerParam_fst]

/-- The vertical coordinate of the momentum is `⟪ξ, x⟫ √(1 - ‖x‖²)`. -/
@[simp]
theorem sphericalPendulumLowerParam_snd_apply_two :
    (sphericalPendulumLowerParam z).2 2 = ⟪z.2, z.1⟫_ℝ * √(1 - ‖z.1‖ ^ 2) := by
  simp [sphericalPendulumLowerParam_snd, sphericalPendulumLowerParam_fst]

/-- The origin of the canonical coordinates is the stable equilibrium: the pendulum at rest at the
south pole. -/
@[simp]
theorem sphericalPendulumLowerParam_zero :
    sphericalPendulumLowerParam 0 = (-EuclideanSpace.single 2 1, 0) := by
  simp [sphericalPendulumLowerParam]

/-! ### The reflection in the horizontal plane -/

/-- The reflection `σ(q₁, q₂, q₃) = (q₁, q₂, -q₃)` of `ℝ³` in the horizontal plane. -/
private noncomputable abbrev horizontalReflection :
    EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (ℝ ∙ EuclideanSpace.single (2 : Fin 3) (1 : ℝ))ᗮ.reflection

private theorem horizontalReflection_apply (v : EuclideanSpace ℝ (Fin 3)) :
    horizontalReflection v = v - (2 * v 2) • EuclideanSpace.single 2 1 := by
  rw [Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply]
  have hn : ‖EuclideanSpace.single (2 : Fin 3) (1 : ℝ)‖ = 1 := by
    simp [EuclideanSpace.single, PiLp.norm_single]
  simp only [EuclideanSpace.inner_single_left, hn, map_one, one_mul]
  module

@[simp]
private theorem horizontalReflection_apply_zero (v : EuclideanSpace ℝ (Fin 3)) :
    horizontalReflection v 0 = v 0 := by
  simp [horizontalReflection_apply]

@[simp]
private theorem horizontalReflection_apply_one (v : EuclideanSpace ℝ (Fin 3)) :
    horizontalReflection v 1 = v 1 := by
  simp [horizontalReflection_apply]

@[simp]
private theorem horizontalReflection_apply_two (v : EuclideanSpace ℝ (Fin 3)) :
    horizontalReflection v 2 = -v 2 := by
  simp [horizontalReflection_apply]
  ring

/-- The reflection `(q, p) ↦ (σ q, σ p)` of `ℝ³ × ℝ³`. -/
private noncomputable abbrev horizontalReflectionPair :
    (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) →L[ℝ]
      EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) :=
  (horizontalReflection.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin 3) →L[ℝ] _).prodMap
    (horizontalReflection.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin 3) →L[ℝ] _)

/-- The lower chart is the upper chart followed by the reflection in the horizontal plane. -/
private theorem sphericalPendulumLowerParam_eq_comp :
    sphericalPendulumLowerParam = horizontalReflectionPair ∘ sphericalPendulumUpperParam := by
  funext z
  refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;> simp

/-- The reflection preserves the standard symplectic form of `ℝ³ × ℝ³`. -/
private theorem stdSymplecticForm_horizontalReflectionPair
    (u w : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
    stdSymplecticForm (horizontalReflectionPair u) (horizontalReflectionPair w) =
      stdSymplecticForm u w := by
  simp [LinearIsometryEquiv.inner_map_map]

/-- The reflection maps the upper half `q₃ > 0` of the phase space onto the lower half. -/
private theorem bijOn_horizontalReflectionPair :
    BijOn horizontalReflectionPair (sphericalPendulumPhaseSpace ∩ {y | 0 < y.1 2})
      (sphericalPendulumPhaseSpace ∩ {y | y.1 2 < 0}) := by
  have hinv : ∀ y, horizontalReflectionPair (horizontalReflectionPair y) = y := fun y ↦
    Prod.ext (Submodule.reflection_reflection _ _) (Submodule.reflection_reflection _ _)
  refine InvOn.bijOn (f' := horizontalReflectionPair) ⟨fun y _ ↦ hinv y, fun y _ ↦ hinv y⟩ ?_ ?_
  all_goals
    rintro y ⟨hy, hy₂⟩
    rw [mem_sphericalPendulumPhaseSpace] at hy
    refine ⟨mem_sphericalPendulumPhaseSpace.2 ⟨?_, ?_⟩, ?_⟩
    · simpa using hy.1
    · simpa [LinearIsometryEquiv.inner_map_map] using hy.2
    · simpa using hy₂

/-! ### Properties of the chart -/

/-- Over the closed unit disc the canonical coordinates take values in the phase space. -/
theorem sphericalPendulumLowerParam_mem_sphericalPendulumPhaseSpace {z} (hz : ‖z.1‖ ≤ 1) :
    sphericalPendulumLowerParam z ∈ sphericalPendulumPhaseSpace := by
  have h := sphericalPendulumUpperParam_mem_sphericalPendulumPhaseSpace hz
  rw [sphericalPendulumLowerParam_eq_comp, Function.comp_apply]
  rw [mem_sphericalPendulumPhaseSpace] at h ⊢
  simpa [LinearIsometryEquiv.inner_map_map] using h

/-- **The canonical coordinates are a bijection onto the lower half of the phase space.** Over the
open unit disc they parametrize exactly the points of the phase space over the open lower
hemisphere `q₃ < 0`, each one once. -/
theorem bijOn_sphericalPendulumLowerParam :
    BijOn sphericalPendulumLowerParam {z | ‖z.1‖ < 1}
      (sphericalPendulumPhaseSpace ∩ {y | y.1 2 < 0}) := by
  rw [sphericalPendulumLowerParam_eq_comp]
  exact bijOn_horizontalReflectionPair.comp bijOn_sphericalPendulumUpperParam

/-- The canonical coordinates are smooth over the open unit disc. -/
theorem contDiffAt_sphericalPendulumLowerParam {n : WithTop ℕ∞} {z} (hz : ‖z.1‖ < 1) :
    ContDiffAt ℝ n sphericalPendulumLowerParam z := by
  rw [sphericalPendulumLowerParam_eq_comp]
  exact horizontalReflectionPair.contDiff.contDiffAt.comp z
    (contDiffAt_sphericalPendulumUpperParam hz)

/-- **The canonical coordinates are symplectic.** Over the open unit disc, the derivative of
`(x, ξ) ↦ (q, p)` pulls the symplectic form `ω₀((a, b), (a', b')) = ⟪a, b'⟫ - ⟪b, a'⟫` of
`ℝ³ × ℝ³`, whose restriction is the symplectic form of the spherical pendulum, back to the
standard symplectic form `⟪x, ξ'⟫ - ⟪ξ, x'⟫` of `ℝ² × ℝ²`. -/
theorem stdSymplecticForm_fderiv_sphericalPendulumLowerParam {z} (hz : ‖z.1‖ < 1)
    (u w : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :
    stdSymplecticForm (fderiv ℝ sphericalPendulumLowerParam z u)
      (fderiv ℝ sphericalPendulumLowerParam z w) = stdSymplecticForm u w := by
  have hd : DifferentiableAt ℝ sphericalPendulumUpperParam z :=
    (contDiffAt_sphericalPendulumUpperParam (n := 1) hz).differentiableAt one_ne_zero
  rw [sphericalPendulumLowerParam_eq_comp,
    (horizontalReflectionPair.hasFDerivAt.comp z hd.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  exact (stdSymplecticForm_horizontalReflectionPair _ _).trans
    (stdSymplecticForm_fderiv_sphericalPendulumUpperParam hz u w)

/-! ### Energy and angular momentum in the canonical coordinates -/

/-- Read in the two canonical charts at the same `(x, ξ)`, the energies differ by twice the height
`√(1 - ‖x‖²)` of the hemispheres, and the vertical angular momenta agree. -/
theorem sphericalPendulumEnergyMomentum_sphericalPendulumLowerParam :
    sphericalPendulumEnergyMomentum (sphericalPendulumLowerParam z) =
      sphericalPendulumEnergyMomentum (sphericalPendulumUpperParam z) -
        (2 * √(1 - ‖z.1‖ ^ 2), 0) := by
  have h₂ := sphericalPendulumUpperParam_fst_apply_two z
  rw [sphericalPendulumLowerParam_eq_comp, Function.comp_apply]
  generalize sphericalPendulumUpperParam z = y at h₂ ⊢
  obtain ⟨q, p⟩ := y
  simp only [ContinuousLinearMap.coe_prodMap', Prod.map_apply,
    sphericalPendulumEnergyMomentum_apply] at h₂ ⊢
  ext
  · simp [h₂]
    ring
  · simp

/-- The energy in the canonical coordinates over the closed unit disc:
`H = (‖ξ‖² - ⟪ξ, x⟫²) / 2 - √(1 - ‖x‖²)`. -/
theorem sphericalPendulumHamiltonian_sphericalPendulumLowerParam {z} (hz : ‖z.1‖ ≤ 1) :
    sphericalPendulumHamiltonian (sphericalPendulumLowerParam z) =
      (‖z.2‖ ^ 2 - ⟪z.2, z.1⟫_ℝ ^ 2) / 2 - √(1 - ‖z.1‖ ^ 2) := by
  have h := congrArg Prod.fst (sphericalPendulumEnergyMomentum_sphericalPendulumLowerParam z)
  simp only [fst_sphericalPendulumEnergyMomentum, Prod.fst_sub] at h
  rw [h, sphericalPendulumHamiltonian_sphericalPendulumUpperParam hz]
  ring

/-- The vertical angular momentum in the canonical coordinates: `J = x₁ ξ₂ - x₂ ξ₁`. -/
theorem angularMomentum_sphericalPendulumLowerParam :
    angularMomentum (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)
      (sphericalPendulumLowerParam z) = z.1 0 * z.2 1 - z.1 1 * z.2 0 := by
  have h := congrArg Prod.snd (sphericalPendulumEnergyMomentum_sphericalPendulumLowerParam z)
  simp only [snd_sphericalPendulumEnergyMomentum, Prod.snd_sub, sub_zero] at h
  rw [h, angularMomentum_sphericalPendulumUpperParam]

/-- In the canonical coordinates, the south pole equilibrium is a critical point of the
energy–momentum map. -/
theorem fderiv_sphericalPendulumEnergyMomentum_comp_sphericalPendulumLowerParam_zero :
    fderiv ℝ (sphericalPendulumEnergyMomentum ∘ sphericalPendulumLowerParam) 0 = 0 := by
  -- The energy–momentum map in the lower chart is that of the upper chart minus
  -- `(2 √(1 - ‖x‖²), 0)`, whose derivative vanishes at the origin.
  have hF : HasFDerivAt (sphericalPendulumEnergyMomentum ∘ sphericalPendulumUpperParam)
      (0 : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ × ℝ) 0 := by
    have hd : DifferentiableAt ℝ (sphericalPendulumEnergyMomentum ∘ sphericalPendulumUpperParam)
        0 :=
      ((contDiff_sphericalPendulumEnergyMomentum (n := 1)).contDiffAt.comp 0
        (contDiffAt_sphericalPendulumUpperParam (by simp))).differentiableAt one_ne_zero
    simpa [fderiv_sphericalPendulumEnergyMomentum_comp_sphericalPendulumUpperParam_zero] using
      hd.hasFDerivAt
  have hs : HasFDerivAt
      (fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦ √(1 - ‖z.1‖ ^ 2))
      (0 : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) 0 := by
    convert (hasFDerivAt_sqrt_sub_norm_sq (a := 1) (x := (0 : EuclideanSpace ℝ (Fin 2)))
      (by simp)).comp (0 : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))
      (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 2))
        (EuclideanSpace ℝ (Fin 2))).hasFDerivAt using 1
    · -- The first projection is `Prod.fst` by definition.
      rfl
    · rw [map_zero, smul_zero, ContinuousLinearMap.zero_comp]
  have hg := (hs.const_mul 2).prodMk
    (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) (0 : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)))
  have h : sphericalPendulumEnergyMomentum ∘ sphericalPendulumLowerParam =
      (sphericalPendulumEnergyMomentum ∘ sphericalPendulumUpperParam) -
        fun z ↦ ((2 * √(1 - ‖z.1‖ ^ 2), 0) : ℝ × ℝ) := by
    funext z
    exact sphericalPendulumEnergyMomentum_sphericalPendulumLowerParam z
  rw [h, (hF.sub hg).fderiv]
  ext <;> simp

/-! ### The Hessians at the south pole -/

/-- The Hessian of the energy at the south pole, in the canonical coordinates:
`‖ξ‖² + ‖x‖²`. -/
theorem hessianQuadraticForm_sphericalPendulumHamiltonian_comp_sphericalPendulumLowerParam_zero
    (v : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :
    hessianQuadraticForm (sphericalPendulumHamiltonian ∘ sphericalPendulumLowerParam) 0 v =
      ‖v.2‖ ^ 2 + ‖v.1‖ ^ 2 := by
  -- The energy in the lower chart is that of the upper chart minus twice the height
  -- `√(1 - ‖x‖²)`, read on the first factor.
  let φ : EuclideanSpace ℝ (Fin 2) → ℝ := fun x ↦ √(1 - ‖x‖ ^ 2)
  let L := ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2))
  have h : sphericalPendulumHamiltonian ∘ sphericalPendulumLowerParam =
      sphericalPendulumHamiltonian ∘ sphericalPendulumUpperParam + (-2 : ℝ) • (φ ∘ L) := by
    funext z
    have := congrArg Prod.fst (sphericalPendulumEnergyMomentum_sphericalPendulumLowerParam z)
    simp only [fst_sphericalPendulumEnergyMomentum, Prod.fst_sub] at this
    simp only [Function.comp_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, this, φ, L,
      ContinuousLinearMap.coe_fst']
    ring
  have hφ : ContDiffAt ℝ 2 φ (L 0) :=
    (contDiffAt_const.sub (contDiff_norm_sq ℝ).contDiffAt).sqrt (by simp [L])
  have hH : ContDiffAt ℝ 2 (sphericalPendulumHamiltonian ∘ sphericalPendulumUpperParam) 0 := by
    have : ContDiff ℝ 2 sphericalPendulumHamiltonian := by
      simpa only [fst_sphericalPendulumEnergyMomentum] using
        contDiff_sphericalPendulumEnergyMomentum.fst
    exact this.contDiffAt.comp 0 (contDiffAt_sphericalPendulumUpperParam (by simp))
  have hφL : ContDiffAt ℝ 2 ((-2 : ℝ) • (φ ∘ L)) 0 :=
    (hφ.comp 0 L.contDiff.contDiffAt).const_smul (-2 : ℝ)
  rw [h, hessianQuadraticForm_add hH hφL,
    hessianQuadraticForm_smul, L.hessianQuadraticForm_comp hφ]
  simp only [add_apply, smul_apply, QuadraticMap.comp_apply,
    hessianQuadraticForm_sphericalPendulumHamiltonian_comp_sphericalPendulumUpperParam_zero,
    ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_fst', smul_eq_mul, L, φ, Prod.fst_zero,
    hessianQuadraticForm_sqrt_sub_norm_sq_zero one_pos, Real.sqrt_one, div_one]
  ring

/-- The Hessian of the vertical angular momentum at the south pole, in the canonical coordinates:
`2 (x₁ ξ₂ - x₂ ξ₁)`. -/
theorem hessianQuadraticForm_angularMomentum_comp_sphericalPendulumLowerParam_zero
    (v : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :
    hessianQuadraticForm (angularMomentum (EuclideanSpace.single 0 1)
      (EuclideanSpace.single 1 1) ∘ sphericalPendulumLowerParam) 0 v =
      2 * (v.1 0 * v.2 1 - v.1 1 * v.2 0) := by
  -- The two charts have the same vertical angular momentum.
  have h : angularMomentum (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1) ∘
      sphericalPendulumLowerParam = angularMomentum (EuclideanSpace.single 0 1)
        (EuclideanSpace.single 1 1) ∘ sphericalPendulumUpperParam := by
    funext z
    rw [Function.comp_apply, Function.comp_apply, angularMomentum_sphericalPendulumLowerParam,
      angularMomentum_sphericalPendulumUpperParam]
  rw [h, hessianQuadraticForm_angularMomentum_comp_sphericalPendulumUpperParam_zero]

/-! ### The south pole is an elliptic–elliptic point -/

/-- The vectors `(q₁, p₁, q₂, p₂)` dual to the Darboux coordinates
`Q₁ = (x₁ - ξ₂) / √2`, `P₁ = (x₂ + ξ₁) / √2`, `Q₂ = (x₁ + ξ₂) / √2`, `P₂ = (ξ₁ - x₂) / √2`. -/
private noncomputable def ellipticDarbouxVectors :
    Fin 2 × Fin 2 → EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) :=
  let c : ℝ := (√2)⁻¹
  fun i ↦ ![![(EuclideanSpace.single 0 c, EuclideanSpace.single 1 (-c)),
      (EuclideanSpace.single 1 c, EuclideanSpace.single 0 c)],
    ![(EuclideanSpace.single 0 c, EuclideanSpace.single 1 c),
      (EuclideanSpace.single 1 (-c), EuclideanSpace.single 0 c)]] i.1 i.2

private theorem inv_sqrt_two_sq : (√2)⁻¹ ^ 2 = (1 / 2 : ℝ) := by
  rw [inv_pow, Real.sq_sqrt zero_le_two, one_div]

private theorem exists_isDarbouxBasis_coe_eq_ellipticDarbouxVectors :
    ∃ b : Module.Basis (Fin 2 × Fin 2) ℝ (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)),
      (stdSymplecticForm (V := EuclideanSpace ℝ (Fin 2))).IsDarbouxBasis b ∧
        ⇑b = ellipticDarbouxVectors := by
  have hc : (√2)⁻¹ * (√2)⁻¹ = (1 / 2 : ℝ) := by rw [← sq, inv_sqrt_two_sq]
  refine SymplecticForm.exists_isDarbouxBasis_coe_eq (by simp) (fun i j ↦ ?_) (fun i j ↦ ?_)
    (fun i j ↦ ?_) <;>
  fin_cases i <;> fin_cases j <;>
  simp [ellipticDarbouxVectors, stdSymplecticForm_apply, EuclideanSpace.inner_single_left] <;>
  linarith

/-- **The Hessians at the south pole are elliptic–elliptic.** There is a Darboux basis of
`ℝ² × ℝ²` whose two elliptic blocks `(Qₖ² + Pₖ²) / 2` span the same space as the Hessians of the
energy and of the vertical angular momentum at the south pole, read in the canonical coordinates:
in the Darboux coordinates `Q₁ = (x₁ - ξ₂) / √2`, `P₁ = (x₂ + ξ₁) / √2`, `Q₂ = (x₁ + ξ₂) / √2` and
`P₂ = (ξ₁ - x₂) / √2`, the Hessians are `(Q₁² + P₁²) + (Q₂² + P₂²)` and
`(Q₂² + P₂²) - (Q₁² + P₁²)`. -/
-- `hessian` stands for `hessianQuadraticForm` here, as in the names of the Hessian theorems
-- of `TauCeti.Geometry.Symplectic.Hamiltonian.SphericalPendulum.FocusFocus`.
theorem exists_isDarbouxBasis_span_hessian_sphericalPendulumLowerParam_eq_span_elliptic :
    ∃ b : Module.Basis (Fin 2 × Fin 2) ℝ (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)),
      (stdSymplecticForm (V := EuclideanSpace ℝ (Fin 2))).IsDarbouxBasis b ∧
        Submodule.span ℝ (range ![
          hessianQuadraticForm (sphericalPendulumHamiltonian ∘ sphericalPendulumLowerParam) 0,
          hessianQuadraticForm (angularMomentum (EuclideanSpace.single 0 1)
            (EuclideanSpace.single 1 1) ∘ sphericalPendulumLowerParam) 0]) =
          Submodule.span ℝ (range (SymplecticForm.elliptic b)) := by
  obtain ⟨b, hb, hbv⟩ := exists_isDarbouxBasis_coe_eq_ellipticDarbouxVectors
  refine ⟨b, hb, ?_⟩
  set QH := hessianQuadraticForm (sphericalPendulumHamiltonian ∘ sphericalPendulumLowerParam) 0
  set QJ := hessianQuadraticForm (angularMomentum (EuclideanSpace.single 0 1)
    (EuclideanSpace.single 1 1) ∘ sphericalPendulumLowerParam) 0
  -- The elliptic blocks are `(QH - QJ) / 4` and `(QH + QJ) / 4`.
  have he (k : Fin 2) : SymplecticForm.elliptic b k =
      (4⁻¹ : ℝ) • QH + ((if k = 0 then -4⁻¹ else 4⁻¹ : ℝ)) • QJ := by
    ext z
    rw [SymplecticForm.elliptic_apply, ← hb.apply_fst, ← neg_neg (b.repr z (k, 0)),
      ← hb.apply_snd, hbv]
    simp only [add_apply, smul_apply, smul_eq_mul, QH, QJ,
      hessianQuadraticForm_sphericalPendulumHamiltonian_comp_sphericalPendulumLowerParam_zero,
      hessianQuadraticForm_angularMomentum_comp_sphericalPendulumLowerParam_zero,
      EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    fin_cases k <;>
    simp [ellipticDarbouxVectors, stdSymplecticForm_apply, EuclideanSpace.inner_single_left] <;>
    ring_nf <;>
    simp only [inv_sqrt_two_sq] <;>
    ring
  have he₀ := he 0
  have he₁ := he 1
  simp only [Fin.isValue, ↓reduceIte, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one] at he₀ he₁
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · -- `QH = 2 (e₀ + e₁)` and `QJ = 2 (e₁ - e₀)`.
    rintro _ ⟨i, rfl⟩
    have h₀ := Submodule.subset_span (R := ℝ) (mem_range_self (f := SymplecticForm.elliptic b) 0)
    have h₁ := Submodule.subset_span (R := ℝ) (mem_range_self (f := SymplecticForm.elliptic b) 1)
    have hQH : QH = (2 : ℝ) • (SymplecticForm.elliptic b 0 + SymplecticForm.elliptic b 1) := by
      rw [he₀, he₁]
      module
    have hQJ : QJ = (2 : ℝ) • (SymplecticForm.elliptic b 1 - SymplecticForm.elliptic b 0) := by
      rw [he₀, he₁]
      module
    fin_cases i
    · simpa [hQH] using Submodule.smul_mem _ (2 : ℝ) (Submodule.add_mem _ h₀ h₁)
    · simpa [hQJ] using Submodule.smul_mem _ (2 : ℝ) (Submodule.sub_mem _ h₁ h₀)
  · rintro _ ⟨k, rfl⟩
    have hH := Submodule.subset_span (R := ℝ) (mem_range_self (f := ![QH, QJ]) 0)
    have hJ := Submodule.subset_span (R := ℝ) (mem_range_self (f := ![QH, QJ]) 1)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hH hJ
    rw [he k]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hH) (Submodule.smul_mem _ _ hJ)

/-- **The stable equilibrium of the spherical pendulum is a nondegenerate rank-zero point.**
Read in the canonical coordinates `TauCeti.sphericalPendulumLowerParam`, a symplectic
parametrization of the phase space near the south pole `(-e₃, 0)`, the energy–momentum map
`F = (H, J)` has a nondegenerate rank-zero point at the origin: its differential vanishes and the
Hessians of `H` and `J` span a Cartan subalgebra of `sp(4, ℝ)`. Its type is elliptic–elliptic: by
`TauCeti.exists_isDarbouxBasis_span_hessian_sphericalPendulumLowerParam_eq_span_elliptic`, the
Hessians span the space of the two elliptic blocks of a Darboux basis. -/
theorem
    isNondegenerateRankZeroPoint_sphericalPendulumEnergyMomentum_comp_sphericalPendulumLowerParam :
    (stdSymplecticForm (V := EuclideanSpace ℝ (Fin 2))).IsNondegenerateRankZeroPoint
      (sphericalPendulumEnergyMomentum ∘ sphericalPendulumLowerParam) 0 := by
  have hF : ContDiffAt ℝ 2 (sphericalPendulumEnergyMomentum ∘ sphericalPendulumLowerParam) 0 :=
    contDiff_sphericalPendulumEnergyMomentum.contDiffAt.comp 0
      (contDiffAt_sphericalPendulumLowerParam (by simp))
  obtain ⟨b, hb, hspan⟩ :=
    exists_isDarbouxBasis_span_hessian_sphericalPendulumLowerParam_eq_span_elliptic
  rw [SymplecticForm.isNondegenerateRankZeroPoint_iff_of_span_eq (Q := SymplecticForm.elliptic b)
    fun hF _ ↦ by
      rw [span_range_hessianQuadraticForm_prod hF, ← hspan]
      simp only [Function.comp_def, fst_sphericalPendulumEnergyMomentum,
        snd_sphericalPendulumEnergyMomentum]]
  exact ⟨hF, fderiv_sphericalPendulumEnergyMomentum_comp_sphericalPendulumLowerParam_zero,
    hb.isNondegenerateQuadraticFamily_elliptic⟩

end TauCeti
