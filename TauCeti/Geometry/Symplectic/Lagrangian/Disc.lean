/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Complex.Line
public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Rigidity
public import TauCeti.Geometry.Symplectic.Liouville.Radial
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.MeasureTheory.Integral.CircleIntegral
import TauCeti.Geometry.Symplectic.Area.PuncturedDisc
import TauCeti.Geometry.Symplectic.Duality
import TauCeti.Geometry.Symplectic.TameMetric

/-!
# Boundary periods of holomorphic discs and exact Lagrangians

Let `ω` be a linear symplectic form on a finite-dimensional real vector space `V`, with its radial
primitive `λₓ(v) = ω(x, v) / 2` (`TauCeti.SymplecticForm.radialPrimitive`), so that `dλ = ω`.
For a disc `u`, `C²` on the open disc and `C¹` up to its boundary circle, Stokes' formula says
that the symplectic area of `u` is the line integral of `λ` around the boundary loop of `u`
(`TauCeti.SymplecticForm.integral_fderiv_apply_ball_eq_pathIntegral_radialPrimitive`):

`∫_D u^* ω = ∮_{∂D} u^* λ`.

If `u` is holomorphic for an almost complex structure tamed by `ω`, its area density is
nonnegative, and it vanishes identically only when `u` is constant. So the boundary action of a
tame holomorphic disc is nonnegative, and it is zero exactly when the disc is constant
(`TauCeti.SymplecticForm.pathIntegral_radialPrimitive_circleMap_nonneg`,
`TauCeti.SymplecticForm.pathIntegral_radialPrimitive_circleMap_eq_zero_iff`).

Now let the boundary of `u` lie on a submanifold, parametrized by a map `i : N → V`, and lift the
boundary circle to a loop `c` in `N`, so that `u(z₀ + b e^{iθ}) = i(c(θ))`. Then the boundary
action is the period of the pulled-back one-form `i^* λ` along `c`
(`TauCeti.SymplecticForm.pathIntegral_mpullback_radialPrimitive_eq_integral`), and for a
nonconstant tame holomorphic disc this period is positive
(`TauCeti.SymplecticForm.pathIntegral_mpullback_radialPrimitive_pos`). In particular `i^* λ` is
not exact. Equivalently, if `i^* λ = dh` for a `C¹` function `h` on `N`, for instance when `i` is an
exact Lagrangian embedding, then every tame holomorphic disc with boundary on `i` along a closed
loop is constant
(`TauCeti.SymplecticForm.exists_eqOn_const_of_mpullback_radialPrimitive_eq_mextDeriv`).
This is the step by which Gromov's theorem, that a compact Lagrangian submanifold of `ℂⁿ` bounds a
nonconstant holomorphic disc, shows that `ℂⁿ` contains no compact exact Lagrangian submanifold.

On `ℂ` with its standard area form, the radial primitive is `(x dy - y dx) / 2`, and around the
unit circle its integral is `π`, the area of the unit disc
(`TauCeti.pathIntegral_radialPrimitive_stdComplexSymplecticForm_circleMap`).

## Main results

In the namespace `TauCeti.SymplecticForm`:

* `integral_fderiv_apply_ball_eq_pathIntegral_radialPrimitive`: Stokes' formula
  `∫_D u^* ω = ∮_{∂D} u^* λ`.
* `pathIntegral_radialPrimitive_circleMap_nonneg`,
  `pathIntegral_radialPrimitive_circleMap_eq_zero_iff`: the boundary action of a tame holomorphic
  disc is nonnegative, and zero exactly for constant discs.
* `pathIntegral_mpullback_radialPrimitive_eq_integral`,
  `pathIntegral_mpullback_radialPrimitive_pos`: along a lift of the boundary loop, the period of
  `i^* λ` is the area of the disc, positive for a nonconstant tame holomorphic disc.
* `exists_eqOn_const_of_mpullback_radialPrimitive_eq_mextDeriv`: a tame holomorphic disc with
  boundary on a map `i` with exact `i^* λ` is constant.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. **82** (1985),
  307–347 (compact Lagrangian submanifolds of `ℂⁿ` and exactness).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, §4.1 (area and exactness).
-/

public section

open Complex MeasureTheory Metric Set
open scoped Real Manifold

namespace TauCeti

namespace SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Stokes' formula for the radial primitive.** For a map `u` which is `C²` on the open disc
`‖z - z₀‖ < b` and `C¹` up to its boundary circle, the symplectic area of `u` is the line integral
of the radial primitive `λ` around the boundary loop `θ ↦ u(z₀ + b e^{iθ})`. -/
theorem integral_fderiv_apply_ball_eq_pathIntegral_radialPrimitive (ω : SymplecticForm V)
    {u : ℂ → V} (z₀ : ℂ) {b : ℝ} (hb : 0 < b) (hu : ∀ z ∈ ball z₀ b, ContDiffAt ℝ 2 u z)
    (hu₁ : ContDiffOn ℝ 1 u (closedBall z₀ b)) :
    (∫ z in ball z₀ b, ω (fderiv ℝ u z 1) (fderiv ℝ u z I)) =
      pathIntegral ω.radialPrimitive.1 (fun θ ↦ u (circleMap z₀ b θ)) (-π) π := by
  rw [ω.integral_fderiv_apply_ball_of_contDiffOn z₀ hb hu hu₁, pathIntegral_radialPrimitive]
  norm_num

variable {ω : SymplecticForm V} {u : ℂ → V} {z₀ : ℂ} {b : ℝ}
  {J : V → AlmostComplexStructure V}

/-- The boundary action of a holomorphic disc whose target structure is tamed by `ω` along its
image is nonnegative: it is the symplectic area of the disc. -/
theorem pathIntegral_radialPrimitive_circleMap_nonneg (hb : 0 < b)
    (hu : ∀ z ∈ ball z₀ b, ContDiffAt ℝ 2 u z) (hu₁ : ContDiffOn ℝ 1 u (closedBall z₀ b))
    (hhol : ∀ z ∈ ball z₀ b,
      IsJHolomorphicAt (fun _ ↦ AlmostComplexStructure.ofComplexModule ℂ) J u z)
    (htame : ∀ z ∈ ball z₀ b, ω.Tames (J (u z))) :
    0 ≤ pathIntegral ω.radialPrimitive.1 (fun θ ↦ u (circleMap z₀ b θ)) (-π) π := by
  rw [← ω.integral_fderiv_apply_ball_eq_pathIntegral_radialPrimitive z₀ hb hu hu₁]
  refine setIntegral_nonneg measurableSet_ball fun z hz ↦ ?_
  have hCR : fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1) := by
    simpa [AlmostComplexStructure.ofComplexModule_apply] using
      (hhol z hz).fderiv_apply_commute (v := 1)
  rw [hCR]
  exact (htame z hz).symplecticForm_apply_apply_self_nonneg (fderiv ℝ u z 1)

/-- A holomorphic disc whose target structure is tamed by `ω` along its image has zero boundary
action exactly when it is constant on the closed disc. -/
theorem pathIntegral_radialPrimitive_circleMap_eq_zero_iff (hb : 0 < b)
    (hu : ∀ z ∈ ball z₀ b, ContDiffAt ℝ 2 u z) (hu₁ : ContDiffOn ℝ 1 u (closedBall z₀ b))
    (hhol : ∀ z ∈ ball z₀ b,
      IsJHolomorphicAt (fun _ ↦ AlmostComplexStructure.ofComplexModule ℂ) J u z)
    (htame : ∀ z ∈ ball z₀ b, ω.Tames (J (u z))) :
    pathIntegral ω.radialPrimitive.1 (fun θ ↦ u (circleMap z₀ b θ)) (-π) π = 0 ↔
      ∃ x, EqOn u (fun _ ↦ x) (closedBall z₀ b) := by
  constructor
  · intro hzero
    rw [← ω.integral_fderiv_apply_ball_eq_pathIntegral_radialPrimitive z₀ hb hu hu₁] at hzero
    have hcont : ContinuousOn (fun z ↦ ω (fderiv ℝ u z 1) (fderiv ℝ u z I)) (ball z₀ b) :=
      fun z hz ↦ by
        have hd := (hu z hz).continuousAt_fderiv (by norm_num)
        exact (ω.continuous_apply_comp continuous_fst continuous_snd).continuousAt.comp
          ((hd.clm_apply continuousAt_const).prodMk (hd.clm_apply continuousAt_const))
          |>.continuousWithinAt
    -- Zero area forces the disc to be constant inside, hence on its closure by continuity.
    obtain ⟨x, hx⟩ := exists_eqOn_const_of_integral_eq_zero_of_continuousOn (ν := volume)
      isOpen_ball (convex_ball z₀ b).isPreconnected hhol htame hcont
      (ω.integrableOn_fderiv_apply_ball_of_contDiffOn z₀ hu₁) hzero
    refine ⟨x, hx.of_subset_closure hu₁.continuousOn continuousOn_const ball_subset_closedBall ?_⟩
    rw [closure_ball z₀ hb.ne']
  · rintro ⟨x, hx⟩
    have hβ : (fun θ ↦ u (circleMap z₀ b θ)) = fun _ ↦ x := funext fun θ ↦
      hx (sphere_subset_closedBall (circleMap_mem_sphere z₀ hb.le θ))
    rw [hβ, pathIntegral_radialPrimitive]
    simp

section LiftedBoundary

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  {i : N → V} {c : ℝ → N}

/-- **The boundary period of a disc.** If the boundary loop `θ ↦ u(z₀ + b e^{iθ})` of a disc `u`
lifts along `i : N → V` to a curve `c` in `N`, then the integral of `i^* λ` along `c` over one
turn is the symplectic area of `u`. -/
theorem pathIntegral_mpullback_radialPrimitive_eq_integral (hb : 0 < b)
    (hu : ∀ z ∈ ball z₀ b, ContDiffAt ℝ 2 u z) (hu₁ : ContDiffOn ℝ 1 u (closedBall z₀ b))
    (hi : ∀ θ, MDifferentiableAt I' 𝓘(ℝ, V) i (c θ))
    (hc : ∀ θ, MDifferentiableAt 𝓘(ℝ, ℝ) I' c θ)
    (hbd : ∀ θ, u (circleMap z₀ b θ) = i (c θ)) :
    pathIntegral (mpullback I' 𝓘(ℝ, V) i ω.radialPrimitive.1) c (-π) π =
      ∫ z in ball z₀ b, ω (fderiv ℝ u z 1) (fderiv ℝ u z I) := by
  rw [pathIntegral_mpullback _ (fun θ _ ↦ hi θ) (fun θ _ ↦ hc θ),
    ω.integral_fderiv_apply_ball_eq_pathIntegral_radialPrimitive z₀ hb hu hu₁]
  congr 1
  exact funext fun θ ↦ (hbd θ).symm

/-- **Nonconstant holomorphic discs have positive boundary period.** If a nonconstant
holomorphic disc, with target structure tamed by `ω` along its image, has its boundary loop
lifted along `i : N → V` to a curve `c` in `N`, then the integral of `i^* λ` along `c` over one
turn is positive. In particular `i^* λ` is not the differential of a function on `N`. -/
theorem pathIntegral_mpullback_radialPrimitive_pos (hb : 0 < b)
    (hu : ∀ z ∈ ball z₀ b, ContDiffAt ℝ 2 u z) (hu₁ : ContDiffOn ℝ 1 u (closedBall z₀ b))
    (hhol : ∀ z ∈ ball z₀ b,
      IsJHolomorphicAt (fun _ ↦ AlmostComplexStructure.ofComplexModule ℂ) J u z)
    (htame : ∀ z ∈ ball z₀ b, ω.Tames (J (u z)))
    (hi : ∀ θ, MDifferentiableAt I' 𝓘(ℝ, V) i (c θ))
    (hc : ∀ θ, MDifferentiableAt 𝓘(ℝ, ℝ) I' c θ)
    (hbd : ∀ θ, u (circleMap z₀ b θ) = i (c θ))
    (hne : ¬∃ x, EqOn u (fun _ ↦ x) (closedBall z₀ b)) :
    0 < pathIntegral (mpullback I' 𝓘(ℝ, V) i ω.radialPrimitive.1) c (-π) π := by
  rw [pathIntegral_mpullback_radialPrimitive_eq_integral hb hu hu₁ hi hc hbd,
    ω.integral_fderiv_apply_ball_eq_pathIntegral_radialPrimitive z₀ hb hu hu₁]
  exact (pathIntegral_radialPrimitive_circleMap_nonneg hb hu hu₁ hhol htame).lt_of_ne
    fun h ↦ hne ((pathIntegral_radialPrimitive_circleMap_eq_zero_iff hb hu hu₁ hhol htame).mp
      h.symm)

/-- **Holomorphic discs with boundary on an exact Lagrangian are constant.** Let `i : N → V`
pull the radial primitive back to the differential of a `C¹` function `h` on `N`, `i^* λ = dh`,
for instance an exact Lagrangian map. If the boundary loop of a holomorphic disc,
with target structure tamed by `ω` along its image, lifts along `i` to a `C¹` curve `c` in `N`
with `c(-π) = c(π)`, then the disc is constant on the closed disc. -/
theorem exists_eqOn_const_of_mpullback_radialPrimitive_eq_mextDeriv (hb : 0 < b)
    (hu : ∀ z ∈ ball z₀ b, ContDiffAt ℝ 2 u z) (hu₁ : ContDiffOn ℝ 1 u (closedBall z₀ b))
    (hhol : ∀ z ∈ ball z₀ b,
      IsJHolomorphicAt (fun _ ↦ AlmostComplexStructure.ofComplexModule ℂ) J u z)
    (htame : ∀ z ∈ ball z₀ b, ω.Tames (J (u z)))
    {h : N → ℝ} (hi : MDifferentiable I' 𝓘(ℝ, V) i) (hh : ContMDiff I' 𝓘(ℝ, ℝ) 1 h)
    (hexact : mpullback I' 𝓘(ℝ, V) i ω.radialPrimitive.1 = mextDeriv (RoughForm.ofFunction I' h))
    (hc : ContMDiff 𝓘(ℝ, ℝ) I' 1 c) (hloop : c (-π) = c π)
    (hbd : ∀ θ, u (circleMap z₀ b θ) = i (c θ)) :
    ∃ x, EqOn u (fun _ ↦ x) (closedBall z₀ b) := by
  refine (pathIntegral_radialPrimitive_circleMap_eq_zero_iff hb hu hu₁ hhol htame).mp ?_
  rw [show (fun θ ↦ u (circleMap z₀ b θ)) = i ∘ c from funext hbd,
    pathIntegral_comp_eq_sub_of_mpullback_eq hi hh hexact hc, hloop, sub_self]

end LiftedBoundary

end SymplecticForm

/-- **The boundary period of the unit disc.** For the standard area form of `ℂ`, whose radial
primitive is `(x dy - y dx) / 2`, the line integral around the unit circle is `π`, the area of the
unit disc. -/
theorem pathIntegral_radialPrimitive_stdComplexSymplecticForm_circleMap :
    pathIntegral stdComplexSymplecticForm.radialPrimitive.1 (circleMap 0 1) (-π) π = π := by
  rw [SymplecticForm.pathIntegral_radialPrimitive]
  have h (θ : ℝ) : stdComplexSymplecticForm (circleMap 0 1 θ) (deriv (circleMap 0 1) θ) = 1 := by
    simp [deriv_circleMap, circleMap, Complex.exp_re, Complex.exp_im]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  simp only [h, intervalIntegral.integral_const, smul_eq_mul, mul_one]
  ring

end TauCeti
