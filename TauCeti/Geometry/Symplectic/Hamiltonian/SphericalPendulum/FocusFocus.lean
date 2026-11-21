/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.FocusFocus
public import TauCeti.Geometry.Symplectic.Hamiltonian.SphericalPendulum
public import TauCeti.Geometry.Symplectic.StandardCompatible
import TauCeti.Analysis.Calculus.Bilinear
import TauCeti.Analysis.Calculus.FDeriv.Norm
import TauCeti.Analysis.Calculus.Morse.NormSq
import TauCeti.Analysis.Calculus.Morse.Prod
import TauCeti.Analysis.Calculus.Morse.ScalarComposition

/-!
# The unstable equilibrium of the spherical pendulum is a focus–focus point

The phase space of the spherical pendulum is `T*S² = {(q, p) : ‖q‖ = 1, ⟪q, p⟫ = 0}` inside
`ℝ³ × ℝ³` (`TauCeti.sphericalPendulumPhaseSpace`), with the symplectic form restricted from
`ω₀((a, b), (a', b')) = ⟪a, b'⟫ - ⟪b, a'⟫`, and the energy–momentum map is `F = (H, J)`,
`H(q, p) = ‖p‖² / 2 + q₃` and `J(q, p) = q₁ p₂ - q₂ p₁`
(`TauCeti.sphericalPendulumEnergyMomentum`). This file shows that the unstable equilibrium, the
pendulum at rest at the north pole `(q, p) = (e₃, 0)`, is a nondegenerate rank-zero point of `F`
of focus–focus type.

Nondegeneracy is a statement about the Hessians in symplectic coordinates, so we first build
canonical coordinates near the north pole. Over a point `x` of the open unit disc, the point of
the upper hemisphere is `q(x) = (x₁, x₂, √(1 - ‖x‖²))`, and a covector `ξ` on the disc is lifted to
the unique tangent vector `p` at `q(x)` with `⟪p, dq_x v⟫ = ⟪ξ, v⟫`, namely the projection
`p = (ξ, 0) - ⟪ξ, x⟫ q(x)` of `(ξ, 0)` onto `q(x)^⊥`. The map
`(x, ξ) ↦ (q(x), p)` (`TauCeti.sphericalPendulumUpperParam`) is the cotangent lift of the graph
parametrization of the upper hemisphere. It maps the open set `{‖x‖ < 1}` bijectively onto the
points of the phase space with `q₃ > 0` (`TauCeti.bijOn_sphericalPendulumUpperParam`), it is
smooth there, and it is symplectic: it pulls
`ω₀` back to the standard form `⟪x, ξ'⟫ - ⟪ξ, x'⟫` of `ℝ² × ℝ²`
(`TauCeti.stdSymplecticForm_fderiv_sphericalPendulumUpperParam`). So it is a Darboux
parametrization of a neighbourhood of the north pole in `(T*S², ω₀)`, with `(0, 0) ↦ (e₃, 0)`.

In these coordinates `H = (‖ξ‖² - ⟪ξ, x⟫²) / 2 + √(1 - ‖x‖²)` and `J = x₁ ξ₂ - x₂ ξ₁`, so the
Hessians at the origin are `‖ξ‖² - ‖x‖²` and `2 (x₁ ξ₂ - x₂ ξ₁)`. Their Hamiltonian endomorphisms
are `(x, ξ) ↦ 2 (ξ, x)`, a hyperbolic map with square `4`, and twice the quarter turn of both
planes, an elliptic map with square `-4`, and they commute
(`hamiltonianEnd_hessian_sphericalPendulumHamiltonian_comp_sphericalPendulumUpperParam_mul_self`,
`hamiltonianEnd_hessianQuadraticForm_angularMomentum_comp_sphericalPendulumUpperParam_mul_self`,
`quadraticPoissonBracket_hessianQuadraticForm_comp_sphericalPendulumUpperParam_eq_zero`). By the
focus–focus criterion
`TauCeti.SymplecticForm.isNondegenerateQuadraticFamily_of_mul_self_eq_one_of_mul_self_eq_neg_one`,
the Hessians span a Cartan subalgebra of `sp(4, ℝ)`: the origin is a nondegenerate rank-zero
point of `F` read in these coordinates
(`isNondegenerateRankZeroPoint_sphericalPendulumEnergyMomentum_comp_sphericalPendulumUpperParam`),
and the linearized flows of the two integrals are one hyperbolic and one elliptic generator, the
focus–focus block of Williamson's classification. Its value `F(e₃, 0) = (1, 0)` is the isolated
critical value of `F` (`TauCeti.eventually_isRegularValue_sphericalPendulumEnergyMomentum_nhdsNE`).

## Main results

* `TauCeti.sphericalPendulumUpperParam`: canonical coordinates on the cotangent bundle of the upper
  hemisphere.
* `TauCeti.bijOn_sphericalPendulumUpperParam`: they parametrize the points of the phase space with
  `q₃ > 0` bijectively.
* `TauCeti.stdSymplecticForm_fderiv_sphericalPendulumUpperParam`: they are symplectic.
* `TauCeti.hessianQuadraticForm_sphericalPendulumHamiltonian_comp_sphericalPendulumUpperParam_zero`,
  `TauCeti.hessianQuadraticForm_angularMomentum_comp_sphericalPendulumUpperParam_zero`: the
  Hessians of `H` and `J` at the north pole in these coordinates.
* `hamiltonianEnd_hessian_sphericalPendulumHamiltonian_comp_sphericalPendulumUpperParam_mul_self`,
  `hamiltonianEnd_hessianQuadraticForm_angularMomentum_comp_sphericalPendulumUpperParam_mul_self`,
  `quadraticPoissonBracket_hessianQuadraticForm_comp_sphericalPendulumUpperParam_eq_zero`: the
  focus–focus type of the Hessians, one hyperbolic and one elliptic commuting generator.
* `isNondegenerateRankZeroPoint_sphericalPendulumEnergyMomentum_comp_sphericalPendulumUpperParam`:
  the north pole equilibrium is a nondegenerate rank-zero point.

## References

* R. H. Cushman and L. M. Bates, *Global Aspects of Classical Integrable Systems*, 2nd ed.,
  Birkhäuser, 2015, Chapter IV (the spherical pendulum and its unstable equilibrium).
* A. V. Bolsinov and A. T. Fomenko, *Integrable Hamiltonian Systems: Geometry, Topology,
  Classification*, Chapman & Hall/CRC, 2004, Chapter 1 (nondegenerate singular points and the
  focus–focus type).
-/

public section

open Set Filter
open scoped InnerProductSpace Topology

namespace TauCeti

/-! ### Canonical coordinates near the north pole -/

/-- Canonical coordinates on the cotangent bundle of the upper unit hemisphere, as a map into the
phase space `T*S² ⊆ ℝ³ × ℝ³` of the spherical pendulum: `(x, ξ)` is sent to the point
`q = (x₁, x₂, √(1 - ‖x‖²))` of the sphere and the momentum `p = (ξ, 0) - ⟪ξ, x⟫ q`, the tangent
vector at `q` whose pairing with `dq_x v` is `⟪ξ, v⟫`. It is the cotangent lift of the graph
parametrization of the hemisphere. -/
noncomputable def sphericalPendulumUpperParam
    (z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) :=
  let q : EuclideanSpace ℝ (Fin 3) :=
    z.1 0 • EuclideanSpace.single 0 1 + z.1 1 • EuclideanSpace.single 1 1 +
      √(1 - ‖z.1‖ ^ 2) • EuclideanSpace.single 2 1
  (q, z.2 0 • EuclideanSpace.single 0 1 + z.2 1 • EuclideanSpace.single 1 1 - ⟪z.2, z.1⟫_ℝ • q)

variable (z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))

/-- Over the closed unit disc the squared height of the hemisphere is `1 - x₁² - x₂²`. -/
private theorem sqrt_one_sub_norm_sq_sq {x : EuclideanSpace ℝ (Fin 2)} (hx : ‖x‖ ≤ 1) :
    √(1 - ‖x‖ ^ 2) ^ 2 = 1 - (x 0 ^ 2 + x 1 ^ 2) := by
  rw [Real.sq_sqrt (by nlinarith [norm_nonneg x]), EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_two]

/-- The position `q = (x₁, x₂, √(1 - ‖x‖²))` in the canonical coordinates `(x, ξ)`. -/
theorem sphericalPendulumUpperParam_fst : (sphericalPendulumUpperParam z).1 =
    z.1 0 • EuclideanSpace.single 0 1 + z.1 1 • EuclideanSpace.single 1 1 +
      √(1 - ‖z.1‖ ^ 2) • EuclideanSpace.single 2 1 :=
  (rfl)

/-- The momentum `p = (ξ, 0) - ⟪ξ, x⟫ q` in the canonical coordinates `(x, ξ)`. -/
theorem sphericalPendulumUpperParam_snd : (sphericalPendulumUpperParam z).2 =
    z.2 0 • EuclideanSpace.single 0 1 + z.2 1 • EuclideanSpace.single 1 1 -
      ⟪z.2, z.1⟫_ℝ • (sphericalPendulumUpperParam z).1 :=
  (rfl)

/-- The first coordinate of the position is `x₁`. -/
@[simp]
theorem sphericalPendulumUpperParam_fst_apply_zero :
    (sphericalPendulumUpperParam z).1 0 = z.1 0 := by
  simp [sphericalPendulumUpperParam_fst]

/-- The second coordinate of the position is `x₂`. -/
@[simp]
theorem sphericalPendulumUpperParam_fst_apply_one :
    (sphericalPendulumUpperParam z).1 1 = z.1 1 := by
  simp [sphericalPendulumUpperParam_fst]

/-- The height of the position is `√(1 - ‖x‖²)`. -/
@[simp]
theorem sphericalPendulumUpperParam_fst_apply_two :
    (sphericalPendulumUpperParam z).1 2 = √(1 - ‖z.1‖ ^ 2) := by
  simp [sphericalPendulumUpperParam_fst]

/-- The first coordinate of the momentum is `ξ₁ - ⟪ξ, x⟫ x₁`. -/
@[simp]
theorem sphericalPendulumUpperParam_snd_apply_zero :
    (sphericalPendulumUpperParam z).2 0 = z.2 0 - ⟪z.2, z.1⟫_ℝ * z.1 0 := by
  simp [sphericalPendulumUpperParam_snd, sphericalPendulumUpperParam_fst]

/-- The second coordinate of the momentum is `ξ₂ - ⟪ξ, x⟫ x₂`. -/
@[simp]
theorem sphericalPendulumUpperParam_snd_apply_one :
    (sphericalPendulumUpperParam z).2 1 = z.2 1 - ⟪z.2, z.1⟫_ℝ * z.1 1 := by
  simp [sphericalPendulumUpperParam_snd, sphericalPendulumUpperParam_fst]

/-- The vertical coordinate of the momentum is `-⟪ξ, x⟫ √(1 - ‖x‖²)`. -/
@[simp]
theorem sphericalPendulumUpperParam_snd_apply_two :
    (sphericalPendulumUpperParam z).2 2 = -(⟪z.2, z.1⟫_ℝ * √(1 - ‖z.1‖ ^ 2)) := by
  simp [sphericalPendulumUpperParam_snd, sphericalPendulumUpperParam_fst]

/-- The origin of the canonical coordinates is the unstable equilibrium: the pendulum at rest at
the north pole. -/
@[simp]
theorem sphericalPendulumUpperParam_zero :
    sphericalPendulumUpperParam 0 = (EuclideanSpace.single 2 1, 0) := by
  simp [sphericalPendulumUpperParam]

/-- Over the closed unit disc the canonical coordinates take values in the phase space. -/
theorem sphericalPendulumUpperParam_mem_sphericalPendulumPhaseSpace {z} (hz : ‖z.1‖ ≤ 1) :
    sphericalPendulumUpperParam z ∈ sphericalPendulumPhaseSpace := by
  have hs := sqrt_one_sub_norm_sq_sq hz
  rw [mem_sphericalPendulumPhaseSpace, ← sq_eq_sq₀ (norm_nonneg _) zero_le_one, one_pow,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp only [PiLp.inner_apply, Fin.sum_univ_three, Fin.sum_univ_two, RCLike.inner_apply,
    conj_trivial, sphericalPendulumUpperParam_fst_apply_zero,
    sphericalPendulumUpperParam_fst_apply_one, sphericalPendulumUpperParam_fst_apply_two,
    sphericalPendulumUpperParam_snd_apply_zero, sphericalPendulumUpperParam_snd_apply_one,
    sphericalPendulumUpperParam_snd_apply_two]
  constructor
  · linear_combination hs
  · linear_combination (-(z.1 0 * z.2 0 + z.1 1 * z.2 1)) * hs

private theorem injOn_sphericalPendulumUpperParam :
    InjOn sphericalPendulumUpperParam {z | ‖z.1‖ < 1} := by
  intro z hz z' _ h
  have h₀ := congrArg (fun y ↦ y.1 0) h
  have h₁ := congrArg (fun y ↦ y.1 1) h
  simp only [sphericalPendulumUpperParam_fst_apply_zero,
    sphericalPendulumUpperParam_fst_apply_one] at h₀ h₁
  have hx : z.1 = z'.1 := by
    ext i
    fin_cases i
    exacts [h₀, h₁]
  -- The vertical momentum `-⟪ξ, x⟫ √(1 - ‖x‖²)` recovers `⟪ξ, x⟫`, since the height is positive.
  have hc : ⟪z.2, z.1⟫_ℝ = ⟪z'.2, z.1⟫_ℝ := by
    have h₂ := congrArg (fun y ↦ y.2 2) h
    simp only [sphericalPendulumUpperParam_snd_apply_two, ← hx] at h₂
    exact mul_right_cancel₀ (sqrt_one_sub_norm_sq_pos hz).ne' (neg_inj.1 h₂)
  have h₃ := congrArg (fun y ↦ y.2 0) h
  have h₄ := congrArg (fun y ↦ y.2 1) h
  simp only [sphericalPendulumUpperParam_snd_apply_zero,
    sphericalPendulumUpperParam_snd_apply_one, ← hx] at h₃ h₄
  rw [hc, sub_left_inj] at h₃ h₄
  refine Prod.ext hx ?_
  ext i
  fin_cases i
  exacts [h₃, h₄]

private theorem surjOn_sphericalPendulumUpperParam :
    SurjOn sphericalPendulumUpperParam {z | ‖z.1‖ < 1}
      (sphericalPendulumPhaseSpace ∩ {y | 0 < y.1 2}) := by
  rintro ⟨q, p⟩ ⟨hy, hq⟩
  rw [mem_sphericalPendulumPhaseSpace, ← sq_eq_sq₀ (norm_nonneg _) zero_le_one, one_pow,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, PiLp.inner_apply, Fin.sum_univ_three]
    at hy
  simp only [RCLike.inner_apply, conj_trivial] at hy
  obtain ⟨hn, hi⟩ := hy
  rw [Set.mem_ofPred] at hq
  -- The preimage is `x = (q₁, q₂)` and `ξ = (p₁, p₂) - (p₃ / q₃) x`.
  let x : EuclideanSpace ℝ (Fin 2) := q 0 • EuclideanSpace.single 0 1 +
    q 1 • EuclideanSpace.single 1 1
  let ξ : EuclideanSpace ℝ (Fin 2) := (p 0 - p 2 / q 2 * q 0) • EuclideanSpace.single 0 1 +
    (p 1 - p 2 / q 2 * q 1) • EuclideanSpace.single 1 1
  have hx₀ : x 0 = q 0 := by simp [x]
  have hx₁ : x 1 = q 1 := by simp [x]
  have hξ₀ : ξ 0 = p 0 - p 2 / q 2 * q 0 := by simp [ξ]
  have hξ₁ : ξ 1 = p 1 - p 2 / q 2 * q 1 := by simp [ξ]
  have hxn : ‖x‖ ^ 2 = 1 - q 2 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, hx₀, hx₁]
    linear_combination hn
  have hs : √(1 - ‖x‖ ^ 2) = q 2 := by
    rw [hxn, sub_sub_cancel, Real.sqrt_sq hq.le]
  have hc : ⟪ξ, x⟫_ℝ = -(p 2 / q 2) := by
    simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial, hξ₀, hξ₁,
      hx₀, hx₁]
    field_simp
    linear_combination q 2 * hi - p 2 * hn
  refine ⟨(x, ξ), ?_, Prod.ext ?_ ?_⟩
  · rw [Set.mem_ofPred]
    nlinarith [norm_nonneg x]
  · ext i
    fin_cases i
    · simp [sphericalPendulumUpperParam_fst_apply_zero, hx₀]
    · simp [sphericalPendulumUpperParam_fst_apply_one, hx₁]
    · simp [sphericalPendulumUpperParam_fst_apply_two, hs]
  · ext i
    fin_cases i
    · simp only [Fin.zero_eta, sphericalPendulumUpperParam_snd_apply_zero, hc, hξ₀, hx₀]
      ring
    · simp only [Fin.mk_one, sphericalPendulumUpperParam_snd_apply_one, hc, hξ₁, hx₁]
      ring
    · simp only [Fin.reduceFinMk, sphericalPendulumUpperParam_snd_apply_two, hc, hs]
      field_simp

/-- **The canonical coordinates are a bijection onto the upper half of the phase space.** Over the
open unit disc they parametrize exactly the points of the phase space over the open upper
hemisphere `q₃ > 0`, each one once. -/
theorem bijOn_sphericalPendulumUpperParam :
    BijOn sphericalPendulumUpperParam {z | ‖z.1‖ < 1}
      (sphericalPendulumPhaseSpace ∩ {y | 0 < y.1 2}) := by
  refine ⟨fun z hz ↦ ?_, injOn_sphericalPendulumUpperParam, surjOn_sphericalPendulumUpperParam⟩
  exact ⟨sphericalPendulumUpperParam_mem_sphericalPendulumPhaseSpace (le_of_lt hz),
    by simpa [sphericalPendulumUpperParam_fst_apply_two] using sqrt_one_sub_norm_sq_pos hz⟩

/-- The canonical coordinates are smooth over the open unit disc. -/
theorem contDiffAt_sphericalPendulumUpperParam {n : WithTop ℕ∞} {z} (hz : ‖z.1‖ < 1) :
    ContDiffAt ℝ n sphericalPendulumUpperParam z := by
  have hpos : 1 - ‖z.1‖ ^ 2 ≠ 0 := (Real.sqrt_pos.1 (sqrt_one_sub_norm_sq_pos hz)).ne'
  have hcoord (i : Fin 2) : ContDiffAt ℝ n
      (fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦ z.1 i) z :=
    ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp
      contDiff_fst).contDiffAt
  have hcoord' (i : Fin 2) : ContDiffAt ℝ n
      (fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦ z.2 i) z :=
    ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp
      contDiff_snd).contDiffAt
  have hs : ContDiffAt ℝ n
      (fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦ √(1 - ‖z.1‖ ^ 2)) z :=
    (contDiffAt_const.sub ((contDiff_norm_sq ℝ).comp contDiff_fst).contDiffAt).sqrt hpos
  have hq : ContDiffAt ℝ n (fun z ↦ (sphericalPendulumUpperParam z).1) z :=
    (((hcoord 0).smul (contDiffAt_const (c := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)))).add
      ((hcoord 1).smul (contDiffAt_const (c := EuclideanSpace.single (1 : Fin 3) (1 : ℝ))))).add
      (hs.smul (contDiffAt_const (c := EuclideanSpace.single (2 : Fin 3) (1 : ℝ))))
  have hc : ContDiffAt ℝ n
      (fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦ ⟪z.2, z.1⟫_ℝ) z :=
    (contDiff_snd.inner ℝ contDiff_fst).contDiffAt
  exact hq.prodMk ((((hcoord' 0).smul
    (contDiffAt_const (c := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)))).add
    ((hcoord' 1).smul (contDiffAt_const (c := EuclideanSpace.single (1 : Fin 3) (1 : ℝ))))).sub
    (hc.smul hq))

/-! ### The canonical coordinates are symplectic -/

/-- The derivative of the position `x ↦ (x₁, x₂, √(1 - ‖x‖²))` over the open unit disc. -/
private noncomputable def positionFDeriv (x : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (EuclideanSpace.proj 0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).smulRight
      (EuclideanSpace.single 0 1) +
    (EuclideanSpace.proj 1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).smulRight
      (EuclideanSpace.single 1 1) +
    ((-(√(1 - ‖x‖ ^ 2))⁻¹) • innerSL ℝ x).smulRight (EuclideanSpace.single 2 1)

private theorem hasFDerivAt_position {z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)}
    (hz : ‖z.1‖ < 1) :
    HasFDerivAt (fun z ↦ (sphericalPendulumUpperParam z).1)
      ((positionFDeriv z.1).comp (ContinuousLinearMap.fst ℝ _ _)) z := by
  have hsq := hasFDerivAt_sqrt_sub_norm_sq (a := 1)
    (Real.sqrt_pos.1 (sqrt_one_sub_norm_sq_pos hz)).ne'
  exact ((((EuclideanSpace.proj 0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).hasFDerivAt.smul_const _).add
    ((EuclideanSpace.proj 1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).hasFDerivAt.smul_const _)).add
    (hsq.smul_const _)).comp z hasFDerivAt_fst

/-- The derivative of the canonical coordinates over the open unit disc, assembled from the
derivatives of the position, of the horizontal momentum `(ξ, 0)` and of `⟪ξ, x⟫`. -/
private theorem hasFDerivAt_sphericalPendulumUpperParam
    {z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)} (hz : ‖z.1‖ < 1) :
    HasFDerivAt sphericalPendulumUpperParam
      (((positionFDeriv z.1).comp (ContinuousLinearMap.fst ℝ _ _)).prod
        ((((EuclideanSpace.proj 0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).comp
            (ContinuousLinearMap.snd ℝ _ _)).smulRight (EuclideanSpace.single 0 1) +
          ((EuclideanSpace.proj 1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).comp
            (ContinuousLinearMap.snd ℝ _ _)).smulRight (EuclideanSpace.single 1 1)) -
          (⟪z.2, z.1⟫_ℝ • (positionFDeriv z.1).comp (ContinuousLinearMap.fst ℝ _ _) +
            ((fderivInnerCLM ℝ (z.2, z.1)).comp ((ContinuousLinearMap.snd ℝ _ _).prod
              (ContinuousLinearMap.fst ℝ _ _))).smulRight (sphericalPendulumUpperParam z).1)))
      z := by
  have hι := (((EuclideanSpace.proj 0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).hasFDerivAt.comp z
    (hasFDerivAt_snd (p := z))).smul_const (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))).add
    (((EuclideanSpace.proj 1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).hasFDerivAt.comp z
      (hasFDerivAt_snd (p := z))).smul_const (EuclideanSpace.single (1 : Fin 3) (1 : ℝ)))
  have hc := (hasFDerivAt_snd (p := z)).inner ℝ (hasFDerivAt_fst (p := z))
  exact (hasFDerivAt_position hz).prodMk (hι.sub (hc.smul (hasFDerivAt_position hz)))

/-- **The canonical coordinates are symplectic.** Over the open unit disc, the derivative of
`(x, ξ) ↦ (q, p)` pulls the symplectic form `ω₀((a, b), (a', b')) = ⟪a, b'⟫ - ⟪b, a'⟫` of
`ℝ³ × ℝ³`, whose restriction is the symplectic form of the spherical pendulum, back to the
standard symplectic form `⟪x, ξ'⟫ - ⟪ξ, x'⟫` of `ℝ² × ℝ²`. -/
theorem stdSymplecticForm_fderiv_sphericalPendulumUpperParam {z} (hz : ‖z.1‖ < 1)
    (u w : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :
    stdSymplecticForm (fderiv ℝ sphericalPendulumUpperParam z u)
      (fderiv ℝ sphericalPendulumUpperParam z w) = stdSymplecticForm u w := by
  have hs := (sqrt_one_sub_norm_sq_pos hz).ne'
  rw [(hasFDerivAt_sphericalPendulumUpperParam hz).fderiv]
  simp only [positionFDeriv, Fin.isValue, neg_smul, ContinuousLinearMap.add_comp,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_two, smul_add,
    sphericalPendulumUpperParam_fst, ContinuousLinearMap.prod_apply, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.smulRight_apply, PiLp.proj_apply, neg_apply, smul_apply, coe_innerSL_apply,
    smul_eq_mul, sub_apply, ContinuousLinearMap.coe_snd', smul_neg, fderivInnerCLM_apply,
    stdSymplecticForm_apply, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, mul_ite, mul_one,
    mul_zero, PiLp.neg_apply, PiLp.sub_apply, Fin.sum_univ_three, ↓reduceIte, zero_ne_one,
    add_zero, Fin.reduceEq, neg_zero, one_ne_zero, zero_add, zero_sub, neg_add_rev, neg_neg,
    mul_neg, neg_mul]
  field_simp
  ring

/-! ### Energy and angular momentum in the canonical coordinates -/

/-- The energy in the canonical coordinates over the closed unit disc:
`H = (‖ξ‖² - ⟪ξ, x⟫²) / 2 + √(1 - ‖x‖²)`. -/
theorem sphericalPendulumHamiltonian_sphericalPendulumUpperParam {z} (hz : ‖z.1‖ ≤ 1) :
    sphericalPendulumHamiltonian (sphericalPendulumUpperParam z) =
      (‖z.2‖ ^ 2 - ⟪z.2, z.1⟫_ℝ ^ 2) / 2 + √(1 - ‖z.1‖ ^ 2) := by
  have hs := sqrt_one_sub_norm_sq_sq hz
  rw [← Prod.mk.eta (p := sphericalPendulumUpperParam z), sphericalPendulumHamiltonian_apply,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_two, sphericalPendulumUpperParam_fst_apply_two,
    sphericalPendulumUpperParam_snd_apply_zero, sphericalPendulumUpperParam_snd_apply_one,
    sphericalPendulumUpperParam_snd_apply_two]
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial]
  linear_combination ((z.2 0 * z.1 0 + z.2 1 * z.1 1) ^ 2 / 2) * hs

/-- The vertical angular momentum in the canonical coordinates: `J = x₁ ξ₂ - x₂ ξ₁`. -/
theorem angularMomentum_sphericalPendulumUpperParam :
    angularMomentum (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)
      (sphericalPendulumUpperParam z) = z.1 0 * z.2 1 - z.1 1 * z.2 0 := by
  rw [← Prod.mk.eta (p := sphericalPendulumUpperParam z), angularMomentum_apply]
  simp only [EuclideanSpace.inner_single_right, sphericalPendulumUpperParam_fst_apply_zero,
    sphericalPendulumUpperParam_fst_apply_one, sphericalPendulumUpperParam_snd_apply_zero,
    sphericalPendulumUpperParam_snd_apply_one, one_mul, conj_trivial]
  ring

/-- In the canonical coordinates, the north pole equilibrium is a critical point of the
energy–momentum map. -/
theorem fderiv_sphericalPendulumEnergyMomentum_comp_sphericalPendulumUpperParam_zero :
    fderiv ℝ (sphericalPendulumEnergyMomentum ∘ sphericalPendulumUpperParam) 0 = 0 := by
  have hz : ‖(0 : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)).1‖ < 1 := by simp
  rw [fderiv_comp _ ((contDiff_sphericalPendulumEnergyMomentum (n := 1)).differentiable
    one_ne_zero _) (hasFDerivAt_sphericalPendulumUpperParam hz).differentiableAt,
    (hasFDerivAt_sphericalPendulumUpperParam hz).fderiv]
  refine ContinuousLinearMap.ext fun u ↦ ?_
  rw [ContinuousLinearMap.comp_apply, fderiv_sphericalPendulumEnergyMomentum_apply]
  simp [positionFDeriv]

/-! ### The Hessians at the north pole -/

private theorem hessianQuadraticForm_inner_sq
    (v : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :
    hessianQuadraticForm
      (fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦ ⟪z.2, z.1⟫_ℝ ^ 2 / 2) 0 v =
      0 := by
  have hg : ContDiffAt ℝ 2
      (fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦ ⟪z.2, z.1⟫_ℝ) 0 :=
    (contDiff_snd.inner ℝ contDiff_fst).contDiffAt
  have hc : fderiv ℝ
      (fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦ ⟪z.2, z.1⟫_ℝ) 0 = 0 := by
    rw [((hasFDerivAt_snd (p := 0)).inner ℝ hasFDerivAt_fst).fderiv]
    refine ContinuousLinearMap.ext fun v ↦ ?_
    simp [fderivInnerCLM_apply]
  have h : (fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦ ⟪z.2, z.1⟫_ℝ ^ 2 / 2) =
      (fun t : ℝ ↦ t ^ 2 / 2) ∘
        fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦ ⟪z.2, z.1⟫_ℝ := rfl
  rw [h, hessianQuadraticForm_scalar_comp (by fun_prop) hg hc]
  simp

/-- The Hessian of the energy at the north pole, in the canonical coordinates:
`‖ξ‖² - ‖x‖²`. -/
theorem hessianQuadraticForm_sphericalPendulumHamiltonian_comp_sphericalPendulumUpperParam_zero
    (v : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :
    hessianQuadraticForm (sphericalPendulumHamiltonian ∘ sphericalPendulumUpperParam) 0 v =
      ‖v.2‖ ^ 2 - ‖v.1‖ ^ 2 := by
  have hU : {z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) | ‖z.1‖ < 1} ∈ 𝓝 0 :=
    (isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).mem_nhds (by simp)
  -- Near the north pole, `H` is the separated sum of the height `√(1 - ‖x‖²)` and the kinetic
  -- energy `‖ξ‖² / 2`, corrected by `-⟪ξ, x⟫² / 2`.
  have heq : sphericalPendulumHamiltonian ∘ sphericalPendulumUpperParam =ᶠ[𝓝 0]
      ((fun x : EuclideanSpace ℝ (Fin 2) ↦ √(1 - ‖x‖ ^ 2)) ∘ Prod.fst +
        ((1 / 2 : ℝ) • fun ξ : EuclideanSpace ℝ (Fin 2) ↦ ‖ξ‖ ^ 2) ∘ Prod.snd) +
        -fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦ ⟪z.2, z.1⟫_ℝ ^ 2 / 2 := by
    filter_upwards [hU] with z hz
    rw [Function.comp_apply, sphericalPendulumHamiltonian_sphericalPendulumUpperParam hz.le]
    simp only [Pi.add_apply, Pi.neg_apply, Function.comp_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hφ : ContDiffAt ℝ 2 (fun x : EuclideanSpace ℝ (Fin 2) ↦ √(1 - ‖x‖ ^ 2)) 0 :=
    (contDiffAt_const.sub (contDiff_norm_sq ℝ).contDiffAt).sqrt (by simp)
  have hψ : ContDiffAt ℝ 2 ((1 / 2 : ℝ) • fun ξ : EuclideanSpace ℝ (Fin 2) ↦ ‖ξ‖ ^ 2) 0 :=
    (contDiff_const.smul (contDiff_norm_sq ℝ)).contDiffAt
  have hι : ContDiffAt ℝ 2
      (-fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦ ⟪z.2, z.1⟫_ℝ ^ 2 / 2) 0 :=
    ((contDiff_snd.inner ℝ contDiff_fst).pow 2 |>.div_const 2).contDiffAt.neg
  have hsum : ContDiffAt ℝ 2 ((fun x : EuclideanSpace ℝ (Fin 2) ↦ √(1 - ‖x‖ ^ 2)) ∘ Prod.fst +
      ((1 / 2 : ℝ) • fun ξ : EuclideanSpace ℝ (Fin 2) ↦ ‖ξ‖ ^ 2) ∘ Prod.snd) 0 :=
    (hφ.comp (f := Prod.fst) 0 contDiffAt_fst).add (hψ.comp (f := Prod.snd) 0 contDiffAt_snd)
  rw [hessianQuadraticForm_congr_of_eventuallyEq heq, hessianQuadraticForm_add hsum hι,
    ← Prod.mk_zero_zero, hessianQuadraticForm_comp_fst_add_comp_snd hφ hψ, Prod.mk_zero_zero,
    hessianQuadraticForm_neg, hessianQuadraticForm_smul]
  simp only [add_apply, neg_apply, QuadraticMap.prod_apply, smul_apply, smul_eq_mul,
    hessianQuadraticForm_sqrt_sub_norm_sq_zero one_pos, Real.sqrt_one, div_one,
    hessianQuadraticForm_norm_sq, hessianQuadraticForm_inner_sq]
  ring

/-- The Hessian of the vertical angular momentum at the north pole, in the canonical coordinates:
`2 (x₁ ξ₂ - x₂ ξ₁)`. -/
theorem hessianQuadraticForm_angularMomentum_comp_sphericalPendulumUpperParam_zero
    (v : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :
    hessianQuadraticForm (angularMomentum (EuclideanSpace.single 0 1)
      (EuclideanSpace.single 1 1) ∘ sphericalPendulumUpperParam) 0 v =
      2 * (v.1 0 * v.2 1 - v.1 1 * v.2 0) := by
  -- In the canonical coordinates `J` is the quadratic form `z ↦ B z z` of the bilinear form
  -- `B z w = x₁(z) ξ₂(w) - x₂(z) ξ₁(w)`.
  let ℓ (i j : Fin 2) : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
    (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).comp
      (if i = 0 then ContinuousLinearMap.fst ℝ _ _ else ContinuousLinearMap.snd ℝ _ _)
  let B := (ℓ 0 0).smulRight (ℓ 1 1) - (ℓ 0 1).smulRight (ℓ 1 0)
  have h : angularMomentum (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1) ∘
      sphericalPendulumUpperParam = fun z ↦ B z z := by
    funext z
    simp [B, ℓ, angularMomentum_sphericalPendulumUpperParam]
  rw [h, hessianQuadraticForm_apply, B.fderiv_fderiv_apply_self]
  simp only [Fin.isValue, ↓reduceIte, one_ne_zero, add_apply, sub_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', PiLp.proj_apply, ContinuousLinearMap.flip_apply, smul_apply,
    ContinuousLinearMap.coe_snd', smul_eq_mul, B, ℓ]
  ring

/-! ### The north pole is a focus–focus point -/

/-- The swap `(x, ξ) ↦ (ξ, x)`. -/
private noncomputable def swapEnd :
    Module.End ℝ (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :=
  (LinearMap.snd ℝ _ _).prod (LinearMap.fst ℝ _ _)

/-- The quarter turn `(a₁, a₂) ↦ (-a₂, a₁)` of the plane, applied to both factors. -/
private noncomputable def rotEnd :
    Module.End ℝ (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :=
  let R : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    (-(EuclideanSpace.proj 1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)).smulRight
        (EuclideanSpace.single 0 1) +
      (EuclideanSpace.proj 0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).smulRight
        (EuclideanSpace.single 1 1)
  (R.prodMap R).toLinearMap

private theorem swapEnd_mul_self : swapEnd * swapEnd = 1 := by
  ext v <;> simp [swapEnd]

private theorem rotEnd_mul_self : rotEnd * rotEnd = -1 := by
  refine LinearMap.ext fun v ↦ Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;> simp [rotEnd]

private theorem commute_swapEnd_rotEnd : Commute swapEnd rotEnd := by
  refine LinearMap.ext fun v ↦ Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;>
    simp [rotEnd, swapEnd]

private theorem hamiltonianEnd_hessianQuadraticForm_hamiltonian :
    (stdSymplecticForm (V := EuclideanSpace ℝ (Fin 2))).hamiltonianEnd
      (hessianQuadraticForm (sphericalPendulumHamiltonian ∘ sphericalPendulumUpperParam) 0) =
      (2 : ℝ) • swapEnd := by
  refine ((stdSymplecticForm.eq_hamiltonianEnd_iff).2 fun v w ↦ ?_).symm
  simp only [QuadraticMap.polar,
    hessianQuadraticForm_sphericalPendulumHamiltonian_comp_sphericalPendulumUpperParam_zero]
  simp only [swapEnd, LinearMap.smul_apply, LinearMap.prod_apply, LinearMap.coe_snd,
    LinearMap.coe_fst, Function.prod_apply, Prod.smul_mk, stdSymplecticForm_apply,
    PiLp.inner_apply, PiLp.smul_apply, smul_eq_mul, RCLike.inner_apply, conj_trivial,
    Fin.sum_univ_two, Fin.isValue, Prod.snd_add, EuclideanSpace.real_norm_sq_eq, PiLp.add_apply,
    Prod.fst_add]
  ring

private theorem hamiltonianEnd_hessianQuadraticForm_angularMomentum :
    (stdSymplecticForm (V := EuclideanSpace ℝ (Fin 2))).hamiltonianEnd
      (hessianQuadraticForm (angularMomentum (EuclideanSpace.single 0 1)
        (EuclideanSpace.single 1 1) ∘ sphericalPendulumUpperParam) 0) = (2 : ℝ) • rotEnd := by
  refine ((stdSymplecticForm.eq_hamiltonianEnd_iff).2 fun v w ↦ ?_).symm
  simp only [QuadraticMap.polar,
    hessianQuadraticForm_angularMomentum_comp_sphericalPendulumUpperParam_zero]
  simp only [rotEnd, Fin.isValue, ContinuousLinearMap.coe_prodMap,
    ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.coe_smulRight,
    ContinuousLinearMap.toLinearMap_neg, LinearMap.smul_apply, LinearMap.prodMap_apply,
    LinearMap.add_apply, LinearMap.coe_smulRight, LinearMap.neg_apply, ContinuousLinearMap.coe_coe,
    PiLp.proj_apply, neg_smul, Prod.smul_mk, smul_add, smul_neg, stdSymplecticForm_apply,
    PiLp.inner_apply, PiLp.add_apply, PiLp.neg_apply, PiLp.smul_apply, PiLp.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero, RCLike.inner_apply, conj_trivial, Fin.sum_univ_two,
    ↓reduceIte, zero_ne_one, add_zero, mul_neg, one_ne_zero, neg_zero, zero_add, Prod.fst_add,
    Prod.snd_add]
  ring

/-- **The energy Hessian at the north pole is hyperbolic.** In the canonical coordinates, the
Hamiltonian endomorphism of the Hessian of `H` at the origin is `(x, ξ) ↦ 2 (ξ, x)`, whose square
is `4`. -/
-- `hessian` stands for `hessianQuadraticForm` here: the full name would be 106 characters, more
-- than the 100-character line limit allows.
theorem
    hamiltonianEnd_hessian_sphericalPendulumHamiltonian_comp_sphericalPendulumUpperParam_mul_self :
    (stdSymplecticForm (V := EuclideanSpace ℝ (Fin 2))).hamiltonianEnd
        (hessianQuadraticForm (sphericalPendulumHamiltonian ∘ sphericalPendulumUpperParam) 0) *
      (stdSymplecticForm (V := EuclideanSpace ℝ (Fin 2))).hamiltonianEnd
        (hessianQuadraticForm (sphericalPendulumHamiltonian ∘ sphericalPendulumUpperParam) 0) =
      4 := by
  rw [hamiltonianEnd_hessianQuadraticForm_hamiltonian, smul_mul_smul, swapEnd_mul_self]
  norm_num [ofNat_smul_eq_nsmul (R := ℝ)]

/-- **The angular momentum Hessian at the north pole is elliptic.** In the canonical coordinates,
the Hamiltonian endomorphism of the Hessian of `J` at the origin is twice the quarter turn of both
planes, whose square is `-4`. -/
theorem
    hamiltonianEnd_hessianQuadraticForm_angularMomentum_comp_sphericalPendulumUpperParam_mul_self :
    (stdSymplecticForm (V := EuclideanSpace ℝ (Fin 2))).hamiltonianEnd
        (hessianQuadraticForm (angularMomentum (EuclideanSpace.single 0 1)
          (EuclideanSpace.single 1 1) ∘ sphericalPendulumUpperParam) 0) *
      (stdSymplecticForm (V := EuclideanSpace ℝ (Fin 2))).hamiltonianEnd
        (hessianQuadraticForm (angularMomentum (EuclideanSpace.single 0 1)
          (EuclideanSpace.single 1 1) ∘ sphericalPendulumUpperParam) 0) =
      -4 := by
  rw [hamiltonianEnd_hessianQuadraticForm_angularMomentum, smul_mul_smul, rotEnd_mul_self]
  norm_num [ofNat_smul_eq_nsmul (R := ℝ)]

/-- In the canonical coordinates, the Hessians of `H` and `J` at the north pole Poisson-commute:
their Hamiltonian endomorphisms commute. -/
theorem quadraticPoissonBracket_hessianQuadraticForm_comp_sphericalPendulumUpperParam_eq_zero :
    (stdSymplecticForm (V := EuclideanSpace ℝ (Fin 2))).quadraticPoissonBracket
      (hessianQuadraticForm (sphericalPendulumHamiltonian ∘ sphericalPendulumUpperParam) 0)
      (hessianQuadraticForm (angularMomentum (EuclideanSpace.single 0 1)
        (EuclideanSpace.single 1 1) ∘ sphericalPendulumUpperParam) 0) = 0 := by
  rw [SymplecticForm.quadraticPoissonBracket_eq_zero_iff,
    hamiltonianEnd_hessianQuadraticForm_hamiltonian,
    hamiltonianEnd_hessianQuadraticForm_angularMomentum]
  exact (commute_swapEnd_rotEnd.smul_left _).smul_right _

/-- The halved coordinate functionals of `ℝ × ℝ` span its dual. -/
private theorem span_range_half_fst_half_snd :
    Submodule.span ℝ (range ![(1 / 2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ,
      (1 / 2 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ]) = ⊤ := by
  refine eq_top_iff.2 fun ℓ _ ↦ (Submodule.mem_span_range_iff_exists_fun ℝ).2
    ⟨![2 * ℓ (1, 0), 2 * ℓ (0, 1)], ?_⟩
  ext <;>
  simp only [one_div, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.fst_comp_inl, ContinuousLinearMap.snd_comp_inl,
    ContinuousLinearMap.fst_comp_inr, ContinuousLinearMap.snd_comp_inr, smul_zero, add_zero,
    zero_add, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, mul_one,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.inr_apply] <;>
  ring

/-- **The unstable equilibrium of the spherical pendulum is a nondegenerate rank-zero point.**
Read in the canonical coordinates `TauCeti.sphericalPendulumUpperParam`, a symplectic
parametrization of the phase space near the north pole `(e₃, 0)`, the energy–momentum map
`F = (H, J)` has a nondegenerate rank-zero point at the origin: its differential vanishes and the
Hessians of `H` and `J` span a Cartan subalgebra of `sp(4, ℝ)`. Its type is focus–focus: by
`hamiltonianEnd_hessian_sphericalPendulumHamiltonian_comp_sphericalPendulumUpperParam_mul_self`,
`hamiltonianEnd_hessianQuadraticForm_angularMomentum_comp_sphericalPendulumUpperParam_mul_self` and
`quadraticPoissonBracket_hessianQuadraticForm_comp_sphericalPendulumUpperParam_eq_zero`, the
Hamiltonian endomorphisms of the Hessians have squares `4` and `-4` and commute: one hyperbolic
and one elliptic commuting generator, the focus–focus block. -/
theorem
    isNondegenerateRankZeroPoint_sphericalPendulumEnergyMomentum_comp_sphericalPendulumUpperParam :
    (stdSymplecticForm (V := EuclideanSpace ℝ (Fin 2))).IsNondegenerateRankZeroPoint
      (sphericalPendulumEnergyMomentum ∘ sphericalPendulumUpperParam) 0 := by
  have hF : ContDiffAt ℝ 2 (sphericalPendulumEnergyMomentum ∘ sphericalPendulumUpperParam) 0 :=
    contDiff_sphericalPendulumEnergyMomentum.contDiffAt.comp 0
      (contDiffAt_sphericalPendulumUpperParam (by simp))
  set QH := hessianQuadraticForm (sphericalPendulumHamiltonian ∘ sphericalPendulumUpperParam) 0
  set QJ := hessianQuadraticForm (angularMomentum (EuclideanSpace.single 0 1)
    (EuclideanSpace.single 1 1) ∘ sphericalPendulumUpperParam) 0
  -- The Hessians of `ℓ ∘ F` for all functionals `ℓ` span the same space as `½ QH` and `½ QJ`,
  -- the Hessians of `(½ fst) ∘ F` and `(½ snd) ∘ F`.
  let L : Fin 2 → ℝ × ℝ →L[ℝ] ℝ :=
    ![(1 / 2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ, (1 / 2 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ]
  have hL : Submodule.span ℝ (range L) = ⊤ := span_range_half_fst_half_snd
  have hQ : (fun i ↦ hessianQuadraticForm (L i ∘ (sphericalPendulumEnergyMomentum ∘
      sphericalPendulumUpperParam)) 0) = ![(1 / 2 : ℝ) • QH, (1 / 2 : ℝ) • QJ] := by
    funext i
    fin_cases i <;>
    · simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, QH, QJ]
      rw [← hessianQuadraticForm_smul]
      congr 1
      funext z
      simp [L]
  rw [SymplecticForm.isNondegenerateRankZeroPoint_iff_of_span_eq
    (Q := ![(1 / 2 : ℝ) • QH, (1 / 2 : ℝ) • QJ])
    fun hF _ ↦ by rw [span_range_hessianQuadraticForm_comp_left hF hL, hQ]]
  refine ⟨hF, fderiv_sphericalPendulumEnergyMomentum_comp_sphericalPendulumUpperParam_zero, ?_⟩
  -- `½ A_H` and `½ A_J` are commuting square roots of `1` and `-1`: a focus–focus pair.
  have h4 : (4 : Module.End ℝ (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))) =
      (4 : ℝ) • 1 := by
    norm_num [ofNat_smul_eq_nsmul (R := ℝ)]
  refine SymplecticForm.isNondegenerateQuadraticFamily_of_mul_self_eq_one_of_mul_self_eq_neg_one
    (by simp) ?_ ?_ ?_
  · rw [map_smul, smul_mul_smul,
      hamiltonianEnd_hessian_sphericalPendulumHamiltonian_comp_sphericalPendulumUpperParam_mul_self,
      h4, smul_smul]
    norm_num
  · rw [map_smul, smul_mul_smul,
      hamiltonianEnd_hessianQuadraticForm_angularMomentum_comp_sphericalPendulumUpperParam_mul_self,
      h4, smul_neg, smul_smul]
    norm_num
  · rw [SymplecticForm.quadraticPoissonBracket_eq_zero_iff, map_smul, map_smul]
    exact ((SymplecticForm.quadraticPoissonBracket_eq_zero_iff _).1
      quadraticPoissonBracket_hessianQuadraticForm_comp_sphericalPendulumUpperParam_eq_zero)
      |>.smul_left _ |>.smul_right _

end TauCeti
