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
import TauCeti.Analysis.Calculus.Morse.NormSq
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
planes, an elliptic map with square `-4`, and they commute. By the focus–focus criterion
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
* `isNondegenerateRankZeroPoint_sphericalPendulumEnergyMomentum_comp_sphericalPendulumUpperParam`:
  the north pole equilibrium is a nondegenerate rank-zero point of focus–focus type.

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

/-- The position `q = (x₁, x₂, √(1 - ‖x‖²))` in the canonical coordinates `(x, ξ)`. -/
theorem fst_sphericalPendulumUpperParam : (sphericalPendulumUpperParam z).1 =
    z.1 0 • EuclideanSpace.single 0 1 + z.1 1 • EuclideanSpace.single 1 1 +
      √(1 - ‖z.1‖ ^ 2) • EuclideanSpace.single 2 1 :=
  (rfl)

/-- The momentum `p = (ξ, 0) - ⟪ξ, x⟫ q` in the canonical coordinates `(x, ξ)`. -/
theorem snd_sphericalPendulumUpperParam : (sphericalPendulumUpperParam z).2 =
    z.2 0 • EuclideanSpace.single 0 1 + z.2 1 • EuclideanSpace.single 1 1 -
      ⟪z.2, z.1⟫_ℝ • (sphericalPendulumUpperParam z).1 :=
  (rfl)

private theorem fst_apply_zero : (sphericalPendulumUpperParam z).1 0 = z.1 0 := by
  simp [fst_sphericalPendulumUpperParam]

private theorem fst_apply_one : (sphericalPendulumUpperParam z).1 1 = z.1 1 := by
  simp [fst_sphericalPendulumUpperParam]

private theorem fst_apply_two : (sphericalPendulumUpperParam z).1 2 = √(1 - ‖z.1‖ ^ 2) := by
  simp [fst_sphericalPendulumUpperParam]

private theorem snd_apply_zero :
    (sphericalPendulumUpperParam z).2 0 = z.2 0 - ⟪z.2, z.1⟫_ℝ * z.1 0 := by
  simp [snd_sphericalPendulumUpperParam, fst_sphericalPendulumUpperParam]

private theorem snd_apply_one :
    (sphericalPendulumUpperParam z).2 1 = z.2 1 - ⟪z.2, z.1⟫_ℝ * z.1 1 := by
  simp [snd_sphericalPendulumUpperParam, fst_sphericalPendulumUpperParam]

private theorem snd_apply_two :
    (sphericalPendulumUpperParam z).2 2 = -(⟪z.2, z.1⟫_ℝ * √(1 - ‖z.1‖ ^ 2)) := by
  simp [snd_sphericalPendulumUpperParam, fst_sphericalPendulumUpperParam]

/-- The origin of the canonical coordinates is the unstable equilibrium: the pendulum at rest at
the north pole. -/
@[simp]
theorem sphericalPendulumUpperParam_zero :
    sphericalPendulumUpperParam 0 = (EuclideanSpace.single 2 1, 0) := by
  simp [sphericalPendulumUpperParam]

/-- Over the closed unit disc the canonical coordinates take values in the phase space. -/
theorem sphericalPendulumUpperParam_mem_sphericalPendulumPhaseSpace {z} (hz : ‖z.1‖ ≤ 1) :
    sphericalPendulumUpperParam z ∈ sphericalPendulumPhaseSpace := by
  have hs : √(1 - ‖z.1‖ ^ 2) ^ 2 = 1 - (z.1 0 ^ 2 + z.1 1 ^ 2) := by
    rw [Real.sq_sqrt (by nlinarith [norm_nonneg z.1]), EuclideanSpace.real_norm_sq_eq,
      Fin.sum_univ_two]
  rw [mem_sphericalPendulumPhaseSpace, ← sq_eq_sq₀ (norm_nonneg _) zero_le_one, one_pow,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp only [PiLp.inner_apply, Fin.sum_univ_three, Fin.sum_univ_two, RCLike.inner_apply,
    conj_trivial, fst_apply_zero, fst_apply_one, fst_apply_two, snd_apply_zero, snd_apply_one,
    snd_apply_two]
  constructor
  · linear_combination hs
  · linear_combination (-(z.1 0 * z.2 0 + z.1 1 * z.2 1)) * hs

private theorem injOn_sphericalPendulumUpperParam :
    InjOn sphericalPendulumUpperParam {z | ‖z.1‖ < 1} := by
  intro z hz z' _ h
  have h₀ := congrArg (fun y ↦ y.1 0) h
  have h₁ := congrArg (fun y ↦ y.1 1) h
  simp only [fst_apply_zero, fst_apply_one] at h₀ h₁
  have hx : z.1 = z'.1 := by
    ext i
    fin_cases i
    exacts [h₀, h₁]
  -- The vertical momentum `-⟪ξ, x⟫ √(1 - ‖x‖²)` recovers `⟪ξ, x⟫`, since the height is positive.
  have hc : ⟪z.2, z.1⟫_ℝ = ⟪z'.2, z.1⟫_ℝ := by
    have h₂ := congrArg (fun y ↦ y.2 2) h
    simp only [snd_apply_two, ← hx] at h₂
    exact mul_right_cancel₀
      (Real.sqrt_pos.2 (by nlinarith [norm_nonneg z.1, show ‖z.1‖ < 1 from hz])).ne'
      (neg_inj.1 h₂)
  have h₃ := congrArg (fun y ↦ y.2 0) h
  have h₄ := congrArg (fun y ↦ y.2 1) h
  simp only [snd_apply_zero, snd_apply_one, ← hx] at h₃ h₄
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
    · simp [fst_apply_zero, hx₀]
    · simp [fst_apply_one, hx₁]
    · simp [fst_apply_two, hs]
  · ext i
    fin_cases i
    · simp only [Fin.zero_eta, snd_apply_zero, hc, hξ₀, hx₀]
      ring
    · simp only [Fin.mk_one, snd_apply_one, hc, hξ₁, hx₁]
      ring
    · simp only [Fin.reduceFinMk, snd_apply_two, hc, hs]
      field_simp

/-- **The canonical coordinates are a bijection onto the upper half of the phase space.** Over the
open unit disc they parametrize exactly the points of the phase space over the open upper
hemisphere `q₃ > 0`, each one once. -/
theorem bijOn_sphericalPendulumUpperParam :
    BijOn sphericalPendulumUpperParam {z | ‖z.1‖ < 1}
      (sphericalPendulumPhaseSpace ∩ {y | 0 < y.1 2}) := by
  refine ⟨fun z hz ↦ ?_, injOn_sphericalPendulumUpperParam, surjOn_sphericalPendulumUpperParam⟩
  have hpos : 0 < 1 - ‖z.1‖ ^ 2 := by nlinarith [norm_nonneg z.1, show ‖z.1‖ < 1 from hz]
  exact ⟨sphericalPendulumUpperParam_mem_sphericalPendulumPhaseSpace (le_of_lt hz),
    by simpa [fst_apply_two] using Real.sqrt_pos.2 hpos⟩

/-- The canonical coordinates are smooth over the open unit disc. -/
theorem contDiffAt_sphericalPendulumUpperParam {n : WithTop ℕ∞} {z} (hz : ‖z.1‖ < 1) :
    ContDiffAt ℝ n sphericalPendulumUpperParam z := by
  have hpos : 1 - ‖z.1‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg z.1]
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
  have hpos : 0 < 1 - ‖z.1‖ ^ 2 := by nlinarith [norm_nonneg z.1]
  have hsq : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 2) ↦ √(1 - ‖y‖ ^ 2))
      ((-(√(1 - ‖z.1‖ ^ 2))⁻¹) • innerSL ℝ z.1) z.1 := by
    convert ((hasStrictFDerivAt_norm_sq z.1).hasFDerivAt.const_sub 1).sqrt hpos.ne' using 1
    have hs : √(1 - ‖z.1‖ ^ 2) ≠ 0 := (Real.sqrt_pos.2 (by nlinarith [norm_nonneg z.1])).ne'
    ext v
    simp
    field_simp
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
  have hs : √(1 - ‖z.1‖ ^ 2) ≠ 0 := (Real.sqrt_pos.2 (by nlinarith [norm_nonneg z.1])).ne'
  rw [(hasFDerivAt_sphericalPendulumUpperParam hz).fderiv]
  simp [positionFDeriv, fst_sphericalPendulumUpperParam, PiLp.inner_apply, Fin.sum_univ_three,
    Fin.sum_univ_two]
  field_simp
  ring

/-! ### Energy and angular momentum in the canonical coordinates -/

/-- The energy in the canonical coordinates over the closed unit disc:
`H = (‖ξ‖² - ⟪ξ, x⟫²) / 2 + √(1 - ‖x‖²)`. -/
theorem sphericalPendulumHamiltonian_sphericalPendulumUpperParam {z} (hz : ‖z.1‖ ≤ 1) :
    sphericalPendulumHamiltonian (sphericalPendulumUpperParam z) =
      (‖z.2‖ ^ 2 - ⟪z.2, z.1⟫_ℝ ^ 2) / 2 + √(1 - ‖z.1‖ ^ 2) := by
  have hs : √(1 - ‖z.1‖ ^ 2) ^ 2 = 1 - (z.1 0 ^ 2 + z.1 1 ^ 2) := by
    rw [Real.sq_sqrt (by nlinarith [norm_nonneg z.1]), EuclideanSpace.real_norm_sq_eq,
      Fin.sum_univ_two]
  rw [show sphericalPendulumUpperParam z =
      ((sphericalPendulumUpperParam z).1, (sphericalPendulumUpperParam z).2) from rfl,
    sphericalPendulumHamiltonian_apply, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, fst_apply_two, snd_apply_zero,
    snd_apply_one, snd_apply_two]
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial]
  linear_combination ((z.2 0 * z.1 0 + z.2 1 * z.1 1) ^ 2 / 2) * hs

/-- The vertical angular momentum in the canonical coordinates: `J = x₁ ξ₂ - x₂ ξ₁`. -/
theorem angularMomentum_sphericalPendulumUpperParam :
    angularMomentum (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)
      (sphericalPendulumUpperParam z) = z.1 0 * z.2 1 - z.1 1 * z.2 0 := by
  rw [show sphericalPendulumUpperParam z =
      ((sphericalPendulumUpperParam z).1, (sphericalPendulumUpperParam z).2) from rfl,
    angularMomentum_apply]
  simp only [EuclideanSpace.inner_single_right, fst_apply_zero, fst_apply_one, snd_apply_zero,
    snd_apply_one, one_mul, conj_trivial]
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

private theorem hessianQuadraticForm_kinetic
    (v : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :
    hessianQuadraticForm
      (fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦ ‖z.2‖ ^ 2 / 2) 0 v =
      ‖v.2‖ ^ 2 := by
  have h : (fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦ ‖z.2‖ ^ 2 / 2) =
      ((1 / 2 : ℝ) • fun y : EuclideanSpace ℝ (Fin 2) ↦ ‖y‖ ^ 2) ∘
        ContinuousLinearMap.snd ℝ _ _ := by
    funext z
    simp only [Function.comp_apply, ContinuousLinearMap.coe_snd', Pi.smul_apply, smul_eq_mul]
    ring
  have hf : ContDiffAt ℝ 2 ((1 / 2 : ℝ) • fun y : EuclideanSpace ℝ (Fin 2) ↦ ‖y‖ ^ 2)
      (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) 0) :=
    (contDiff_const.smul (contDiff_norm_sq ℝ)).contDiffAt
  rw [h, ContinuousLinearMap.hessianQuadraticForm_comp _ hf, QuadraticMap.comp_apply,
    hessianQuadraticForm_smul, smul_apply, hessianQuadraticForm_norm_sq]
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_snd', smul_eq_mul]
  ring

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

private theorem hessianQuadraticForm_height
    (v : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :
    hessianQuadraticForm
      (fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦ √(1 - ‖z.1‖ ^ 2)) 0 v =
      -‖v.1‖ ^ 2 := by
  have hn : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin 2) ↦ ‖y‖ ^ 2) 0 :=
    (contDiff_norm_sq ℝ).contDiffAt
  have hc : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) ↦ ‖y‖ ^ 2) 0 = 0 := by
    simp
  have hd : HasDerivAt (fun t : ℝ ↦ √(1 - t)) (-(1 / 2)) 0 := by
    have h := ((hasDerivAt_id' (0 : ℝ)).const_sub 1).sqrt (by norm_num)
    rw [sub_zero, Real.sqrt_one, mul_one] at h
    convert h using 1
    ring
  have hs : ContDiffAt ℝ 2 (fun t : ℝ ↦ √(1 - t)) (‖(0 : EuclideanSpace ℝ (Fin 2))‖ ^ 2) := by
    rw [norm_zero, zero_pow two_ne_zero]
    exact (Real.contDiffAt_sqrt (by norm_num)).comp 0 (contDiffAt_const.sub contDiffAt_id)
  -- `√(1 - ‖x‖²)` is `t ↦ √(1 - t)` after the critical function `‖x‖²`, read on the first factor.
  have hφ := hessianQuadraticForm_scalar_comp (φ := fun t : ℝ ↦ √(1 - t))
    (f := fun y : EuclideanSpace ℝ (Fin 2) ↦ ‖y‖ ^ 2) hs hn hc
  have h : (fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦ √(1 - ‖z.1‖ ^ 2)) =
      ((fun t : ℝ ↦ √(1 - t)) ∘ fun y : EuclideanSpace ℝ (Fin 2) ↦ ‖y‖ ^ 2) ∘
        ContinuousLinearMap.fst ℝ _ _ := rfl
  have hcomp : ContDiffAt ℝ 2
      ((fun t : ℝ ↦ √(1 - t)) ∘ fun y : EuclideanSpace ℝ (Fin 2) ↦ ‖y‖ ^ 2)
      (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) 0) :=
    ContDiffAt.comp (f := fun y : EuclideanSpace ℝ (Fin 2) ↦ ‖y‖ ^ 2) 0 hs hn
  rw [h, ContinuousLinearMap.hessianQuadraticForm_comp _ hcomp, map_zero, hφ,
    QuadraticMap.comp_apply, smul_apply, norm_zero, zero_pow two_ne_zero, hd.deriv,
    ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_fst', hessianQuadraticForm_norm_sq,
    smul_eq_mul]
  ring

/-- The Hessian of the energy at the north pole, in the canonical coordinates:
`‖ξ‖² - ‖x‖²`. -/
theorem hessianQuadraticForm_sphericalPendulumHamiltonian_comp_sphericalPendulumUpperParam_zero
    (v : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :
    hessianQuadraticForm (sphericalPendulumHamiltonian ∘ sphericalPendulumUpperParam) 0 v =
      ‖v.2‖ ^ 2 - ‖v.1‖ ^ 2 := by
  have hU : {z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) | ‖z.1‖ < 1} ∈ 𝓝 0 :=
    (isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).mem_nhds (by simp)
  have heq : sphericalPendulumHamiltonian ∘ sphericalPendulumUpperParam =ᶠ[𝓝 0]
      ((fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦ ‖z.2‖ ^ 2 / 2) +
        -fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦ ⟪z.2, z.1⟫_ℝ ^ 2 / 2) +
        fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦ √(1 - ‖z.1‖ ^ 2) := by
    filter_upwards [hU] with z hz
    rw [Function.comp_apply, sphericalPendulumHamiltonian_sphericalPendulumUpperParam hz.le]
    simp only [Pi.add_apply, Pi.neg_apply]
    ring
  have h₁ : ContDiffAt ℝ 2
      (fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦ ‖z.2‖ ^ 2 / 2) 0 :=
    ((contDiff_norm_sq ℝ).comp contDiff_snd |>.div_const 2).contDiffAt
  have h₂ : ContDiffAt ℝ 2
      (-fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦ ⟪z.2, z.1⟫_ℝ ^ 2 / 2) 0 :=
    ((contDiff_snd.inner ℝ contDiff_fst).pow 2 |>.div_const 2).contDiffAt.neg
  have h₁₂ : ContDiffAt ℝ 2
      ((fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦ ‖z.2‖ ^ 2 / 2) +
        -fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦ ⟪z.2, z.1⟫_ℝ ^ 2 / 2) 0 :=
    h₁.add h₂
  have h₃ : ContDiffAt ℝ 2
      (fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦ √(1 - ‖z.1‖ ^ 2)) 0 :=
    (contDiffAt_const.sub ((contDiff_norm_sq ℝ).comp contDiff_fst).contDiffAt).sqrt (by simp)
  rw [hessianQuadraticForm_congr_of_eventuallyEq heq, hessianQuadraticForm_add h₁₂ h₃,
    hessianQuadraticForm_add h₁ h₂, hessianQuadraticForm_neg]
  simp only [add_apply, neg_apply, hessianQuadraticForm_kinetic, hessianQuadraticForm_inner_sq,
    hessianQuadraticForm_height]
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
  simp [B, ℓ]
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
  ext v <;> rfl

private theorem rotEnd_mul_self : rotEnd * rotEnd = -1 := by
  refine LinearMap.ext fun v ↦ Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;> simp [rotEnd]

private theorem commute_swapEnd_rotEnd : Commute swapEnd rotEnd := by
  refine LinearMap.ext fun v ↦ Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;>
    simp [rotEnd, swapEnd]

private theorem hamiltonianEnd_hessian_hamiltonian :
    (stdSymplecticForm (V := EuclideanSpace ℝ (Fin 2))).hamiltonianEnd
      (hessianQuadraticForm (sphericalPendulumHamiltonian ∘ sphericalPendulumUpperParam) 0) =
      (2 : ℝ) • swapEnd := by
  refine ((stdSymplecticForm.eq_hamiltonianEnd_iff).2 fun v w ↦ ?_).symm
  simp only [QuadraticMap.polar,
    hessianQuadraticForm_sphericalPendulumHamiltonian_comp_sphericalPendulumUpperParam_zero]
  simp [swapEnd, EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply, Fin.sum_univ_two]
  ring

private theorem hamiltonianEnd_hessian_angularMomentum :
    (stdSymplecticForm (V := EuclideanSpace ℝ (Fin 2))).hamiltonianEnd
      (hessianQuadraticForm (angularMomentum (EuclideanSpace.single 0 1)
        (EuclideanSpace.single 1 1) ∘ sphericalPendulumUpperParam) 0) = (2 : ℝ) • rotEnd := by
  refine ((stdSymplecticForm.eq_hamiltonianEnd_iff).2 fun v w ↦ ?_).symm
  simp only [QuadraticMap.polar,
    hessianQuadraticForm_angularMomentum_comp_sphericalPendulumUpperParam_zero]
  simp [rotEnd, PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- **The unstable equilibrium of the spherical pendulum is a focus–focus point.** Read in the
canonical coordinates `TauCeti.sphericalPendulumUpperParam`, a symplectic parametrization of the
phase space near the north pole `(e₃, 0)`, the energy–momentum map `F = (H, J)` has a
nondegenerate rank-zero point at the origin: its differential vanishes and the Hessians of `H`
and `J` span a Cartan subalgebra of `sp(4, ℝ)`. With the Hessians
`TauCeti.hessianQuadraticForm_sphericalPendulumHamiltonian_comp_sphericalPendulumUpperParam_zero`
and `TauCeti.hessianQuadraticForm_angularMomentum_comp_sphericalPendulumUpperParam_zero`, the
Hamiltonian endomorphisms are `(x, ξ) ↦ 2 (ξ, x)`, with square `4`, and twice the quarter turn of
both planes, with square `-4`: one hyperbolic and one elliptic commuting generator, the
focus–focus block. -/
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
  have hL : Submodule.span ℝ (range L) = ⊤ := by
    refine eq_top_iff.2 fun ℓ _ ↦ (Submodule.mem_span_range_iff_exists_fun ℝ).2
      ⟨![2 * ℓ (1, 0), 2 * ℓ (0, 1)], ?_⟩
    ext <;> simp [L, Fin.sum_univ_two] <;> ring
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
  refine SymplecticForm.isNondegenerateQuadraticFamily_of_mul_self_eq_one_of_mul_self_eq_neg_one
    (by simp) ?_ ?_ ?_
  · rw [map_smul, hamiltonianEnd_hessian_hamiltonian, smul_smul, smul_mul_smul, swapEnd_mul_self]
    norm_num
  · rw [map_smul, hamiltonianEnd_hessian_angularMomentum, smul_smul, smul_mul_smul,
      rotEnd_mul_self]
    norm_num
  · rw [SymplecticForm.quadraticPoissonBracket_eq_zero_iff, map_smul, map_smul,
      hamiltonianEnd_hessian_hamiltonian, hamiltonianEnd_hessian_angularMomentum]
    exact ((commute_swapEnd_rotEnd.smul_left _).smul_right _).smul_left _ |>.smul_right _

end TauCeti
