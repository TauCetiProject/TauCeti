/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.HomologyPeriod
public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Disc
public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Integral
public import TauCeti.Geometry.Symplectic.Lagrangian.Exact
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.Analysis.Calculus.FDeriv.Integrable
import TauCeti.Geometry.Symplectic.Area.PuncturedDisc
import TauCeti.Geometry.Symplectic.CompatibleMetric
import TauCeti.Geometry.Symplectic.Duality

/-!
# The energy of a disc with a forcing term

Let `ω` be a linear symplectic form on a finite-dimensional real vector space `V`, invariant under
a linear complex structure `J`, with the associated form `|v|² = ω(v, J v)`, and let `u` be a map
which is `C²` on the open disc `D = {‖z - z₀‖ < b}` of `ℂ = {s + i t}` and `C¹` up to its boundary
circle. Its Cauchy–Riemann defect is `∂ₛu + J ∂ₜu`: the map is `J`-holomorphic when the defect
vanishes, and it solves the forced equation `∂ₛu + J ∂ₜu = G` with forcing term `G`, for instance
the inhomogeneous Cauchy–Riemann equation `∂ₛu + i ∂ₜu = ∇_w H(z, u)` on `ℂⁿ` for a Hamiltonian
`H`.

Completing the square gives `|∂ₛu|² + |∂ₜu|² = 2 ω(∂ₛu, ∂ₜu) + |∂ₛu + J ∂ₜu|²` pointwise
(`TauCeti.SymplecticForm.Invariant.associatedBilinForm_add_apply_self`), and Stokes' formula turns
the symplectic area of `u` into the boundary period of the radial primitive `λ` of `ω`, `dλ = ω`.
So the energy of the disc is

`E(u) = (1/2) ∫_D |du|² = ∮_{∂D} u^* λ + (1/2) ∫_D |∂ₛu + J ∂ₜu|²`

(`TauCeti.SymplecticForm.integral_associatedBilinForm_fderiv_ball_eq`). The symplectic area is
signed here: it can be negative for a solution of a forced equation. For a compatible pair the
energy `TauCeti.SymplecticForm.stdComplexLineEnergy`, the integral of the nonnegative energy
density, is this real integral (`TauCeti.SymplecticForm.stdComplexLineEnergy_ball_eq`). A forcing
term with `|G|² ≤ C` on the disc therefore bounds the energy by the boundary period plus
`π b² C / 2` (`TauCeti.SymplecticForm.stdComplexLineEnergy_ball_le`).

The boundary period vanishes when the boundary of the disc lies on an isotropic submanifold and
bounds there in homology. Let `i : N → V` be a smooth map with isotropic tangent images, such as a
Lagrangian embedding, and let the boundary loop of `u` lift along `i` to a `C¹` curve `c` in `N`
tracing a loop whose class in `H₁(N; ℤ)` vanishes, for instance a null-homotopic loop. Then `i^* λ`
is closed, its periods factor through `H₁(N; ℤ)`, and so the boundary period of `u` is zero
(`TauCeti.SymplecticForm.pathIntegral_radialPrimitive_circleMap_eq_zero_of_loopClass_eq_zero`).
For such a disc the energy is bounded by the forcing alone,
`E(u) ≤ π b² C / 2` (`TauCeti.SymplecticForm.stdComplexLineEnergy_ball_le_of_loopClass_eq_zero`),
and a holomorphic disc with such boundary, for a target structure tamed by `ω`, is constant
(`TauCeti.SymplecticForm.exists_eqOn_const_of_loopClass_eq_zero`).

These are the energy estimates of Gromov's proof that a compact Lagrangian submanifold of `ℂⁿ`
bounds a nonconstant holomorphic disc: the solutions of a forced equation whose boundary loops bound
on the Lagrangian have energy bounded by the forcing, and at zero forcing they are constant.

## Main results

In the namespace `TauCeti.SymplecticForm`:

* `integral_associatedBilinForm_fderiv_ball_eq`: the energy identity
  `(1/2) ∫_D |du|² = ∮_{∂D} u^* λ + (1/2) ∫_D |∂ₛu + J ∂ₜu|²`.
* `stdComplexLineEnergy_ball_eq`: the same identity for the energy `stdComplexLineEnergy`.
* `stdComplexLineEnergy_ball_le`: the energy bound for a bounded Cauchy–Riemann defect.
* `pathIntegral_radialPrimitive_circleMap_eq_zero_of_loopClass_eq_zero`: the boundary period of a
  disc vanishes when its boundary lifts to a loop on an isotropic submanifold bounding in `H₁`.
* `stdComplexLineEnergy_ball_le_of_loopClass_eq_zero`: such a disc has energy at most
  `π b² C / 2`.
* `exists_eqOn_const_of_loopClass_eq_zero`: such a holomorphic disc is constant.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. **82** (1985),
  307–347 (compact Lagrangian submanifolds of `ℂⁿ` bound holomorphic discs).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, §2.2 (the energy identity).
-/

public section

open Complex MeasureTheory Metric Set
open scoped Real Manifold

namespace TauCeti

namespace SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : AlmostComplexStructure V} {u : ℂ → V} {z₀ : ℂ} {b : ℝ}

/-- The squared length `ω(L du, J L du)` of a continuous function `L` of the derivative of a map
which is `C¹` on a closed disc is integrable on the open disc. -/
private theorem integrableOn_associatedBilinForm_comp_fderiv_ball {L : (ℂ →L[ℝ] V) → V}
    (hL : Continuous L) (hu₁ : ContDiffOn ℝ 1 u (closedBall z₀ b)) :
    IntegrableOn (fun z ↦ ω.associatedBilinForm J (L (fderiv ℝ u z)) (L (fderiv ℝ u z)))
      (ball z₀ b) := by
  refine integrableOn_ball_comp_fderiv_of_contDiffOn (F := fun A ↦ ω.associatedBilinForm J (L A)
    (L A)) ?_ hu₁
  simpa [associatedBilinForm_apply] using
    ω.continuous_apply_comp hL (J.toLinearMap.continuous_of_finiteDimensional.comp hL)

/-- **The energy identity for a disc with a forcing term.** For a `J`-invariant `ω` and a map `u`
which is `C²` on the open disc `D = {‖z - z₀‖ < b}` and `C¹` up to its boundary circle,
`(1/2) ∫_D (|∂ₛu|² + |∂ₜu|²) = ∮_{∂D} u^* λ + (1/2) ∫_D |∂ₛu + J ∂ₜu|²`, where `|v|² = ω(v, J v)`
and `λ` is the radial primitive of `ω`. -/
theorem integral_associatedBilinForm_fderiv_ball_eq (hinv : ω.Invariant J) (hb : 0 ≤ b)
    (hu : ∀ z ∈ ball z₀ b, ContDiffAt ℝ 2 u z) (hu₁ : ContDiffOn ℝ 1 u (closedBall z₀ b)) :
    (∫ z in ball z₀ b, (ω.associatedBilinForm J (fderiv ℝ u z 1) (fderiv ℝ u z 1) +
        ω.associatedBilinForm J (fderiv ℝ u z I) (fderiv ℝ u z I))) / 2 =
      pathIntegral ω.radialPrimitive.val (fun θ ↦ u (circleMap z₀ b θ)) (-π) π +
        (∫ z in ball z₀ b, ω.associatedBilinForm J (fderiv ℝ u z 1 + J (fderiv ℝ u z I))
          (fderiv ℝ u z 1 + J (fderiv ℝ u z I))) / 2 := by
  have hdefect := integrableOn_associatedBilinForm_comp_fderiv_ball (ω := ω) (J := J)
    (L := fun A ↦ A 1 + J (A I)) (by fun_prop) hu₁
  have harea := ω.integrableOn_fderiv_apply_ball_of_contDiffOn z₀ hu₁
  have hsq (a c : V) : ω.associatedBilinForm J a a + ω.associatedBilinForm J c c =
      2 * ω a c + ω.associatedBilinForm J (a + J c) (a + J c) := by
    rw [hinv.associatedBilinForm_add_apply_self]
    ring
  simp_rw [hsq]
  rw [← ω.integral_fderiv_apply_ball_eq_pathIntegral_radialPrimitive z₀ hb hu hu₁,
    integral_add (harea.const_mul 2) hdefect, integral_const_mul]
  ring

/-- **The energy of a disc with a forcing term.** For a compatible pair `(ω, J)` and a map `u`
which is `C²` on the open disc `D = {‖z - z₀‖ < b}` and `C¹` up to its boundary circle, the energy
of `u` on `D`, read in the real coordinates `ℝ × ℝ` of `ℂ`, is
`∮_{∂D} u^* λ + (1/2) ∫_D |∂ₛu + J ∂ₜu|²`. Since the energy density is nonnegative and integrable,
the energy is finite and equal to the real integral of
`TauCeti.SymplecticForm.integral_associatedBilinForm_fderiv_ball_eq`. -/
theorem stdComplexLineEnergy_ball_eq (hcompat : ω.Compatible J) (hb : 0 ≤ b)
    (hu : ∀ z ∈ ball z₀ b, ContDiffAt ℝ 2 u z) (hu₁ : ContDiffOn ℝ 1 u (closedBall z₀ b)) :
    ω.stdComplexLineEnergy J
        (fun z ↦ ((fderiv ℝ u z).comp (equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ) :
          (ℝ × ℝ) →ₗ[ℝ] V))
        (volume.restrict (ball z₀ b)) =
      ENNReal.ofReal (pathIntegral ω.radialPrimitive.val (fun θ ↦ u (circleMap z₀ b θ)) (-π) π +
        (∫ z in ball z₀ b, ω.associatedBilinForm J (fderiv ℝ u z 1 + J (fderiv ℝ u z I))
          (fderiv ℝ u z 1 + J (fderiv ℝ u z I))) / 2) := by
  have hs := integrableOn_associatedBilinForm_comp_fderiv_ball (ω := ω) (J := J)
    (L := fun A ↦ A 1) (by fun_prop) hu₁
  have ht := integrableOn_associatedBilinForm_comp_fderiv_ball (ω := ω) (J := J)
    (L := fun A ↦ A I) (by fun_prop) hu₁
  have hint : IntegrableOn (fun z ↦ (ω.associatedBilinForm J (fderiv ℝ u z 1) (fderiv ℝ u z 1) +
      ω.associatedBilinForm J (fderiv ℝ u z I) (fderiv ℝ u z I)) / 2) (ball z₀ b) :=
    (hs.add ht).div_const 2
  rw [← integral_associatedBilinForm_fderiv_ball_eq hcompat.invariant hb hu hu₁,
    ← integral_div, ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ fun z ↦ div_nonneg (add_nonneg
        (hcompat.associatedBilinForm_self_nonneg _) (hcompat.associatedBilinForm_self_nonneg _))
        zero_le_two),
    stdComplexLineEnergy_def]
  simp [stdComplexLineEnergyDensity_def]

/-- **Bounded forcing bounds the energy.** For a compatible pair `(ω, J)` and a map `u` which is
`C²` on the open disc `D = {‖z - z₀‖ < b}` and `C¹` up to its boundary circle, if the
Cauchy–Riemann defect satisfies `|∂ₛu + J ∂ₜu|² ≤ C` on `D`, then the energy of `u` on `D` is at
most `∮_{∂D} u^* λ + π b² C / 2`. -/
theorem stdComplexLineEnergy_ball_le (hcompat : ω.Compatible J)
    (hu : ∀ z ∈ ball z₀ b, ContDiffAt ℝ 2 u z) (hu₁ : ContDiffOn ℝ 1 u (closedBall z₀ b))
    {C : ℝ} (hC : ∀ z ∈ ball z₀ b, ω.associatedBilinForm J (fderiv ℝ u z 1 + J (fderiv ℝ u z I))
      (fderiv ℝ u z 1 + J (fderiv ℝ u z I)) ≤ C) :
    ω.stdComplexLineEnergy J
        (fun z ↦ ((fderiv ℝ u z).comp (equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ) :
          (ℝ × ℝ) →ₗ[ℝ] V))
        (volume.restrict (ball z₀ b)) ≤
      ENNReal.ofReal (pathIntegral ω.radialPrimitive.val (fun θ ↦ u (circleMap z₀ b θ)) (-π) π +
        π * b ^ 2 * C / 2) := by
  rcases lt_or_ge b 0 with hb | hb
  · -- A disc of negative radius is empty, so the energy vanishes.
    simp [ball_eq_empty.mpr hb.le]
  rw [stdComplexLineEnergy_ball_eq hcompat hb hu hu₁]
  refine ENNReal.ofReal_le_ofReal ((add_le_add_iff_left _).2
    (div_le_div_of_nonneg_right ?_ zero_le_two))
  have hdefect := integrableOn_associatedBilinForm_comp_fderiv_ball (ω := ω) (J := J)
    (L := fun A ↦ A 1 + J (A I)) (by fun_prop) hu₁
  refine (setIntegral_mono_on hdefect (integrableOn_const measure_ball_lt_top.ne)
    measurableSet_ball hC).trans_eq ?_
  -- The disc has area `π b²`.
  rw [setIntegral_const, measureReal_def, Complex.volume_ball]
  simp only [smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hb,
    ENNReal.coe_toReal, NNReal.coe_real_pi]
  ring

section IsotropicBoundary

/- The scoped `ContDiff` notation makes `ω` a notation, so the symplectic form is called `σ` in
this section. -/
open scoped ContDiff
open TauCeti.HurewiczOne

variable {σ : SymplecticForm V} {E' H' : Type*} {N : Type} [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace N] [ChartedSpace H' N] [T2Space N] [IsManifold I' ∞ N] {i : N → V} {c : ℝ → N}

/-- **Boundaries bounding on an isotropic submanifold have zero period.** Let `i : N → V` be a
smooth map with isotropic tangent images, and let the boundary loop of a disc `u` lift along `i` to
a `C¹` curve `c` in `N`, `u(z₀ + b e^{iθ}) = i(c(θ))` for `θ ∈ [-π, π]`, which traces a loop `γ`
whose class in `H₁(N; ℤ)` vanishes. Then the boundary period `∮ u^* λ` of the radial primitive
vanishes. -/
theorem pathIntegral_radialPrimitive_circleMap_eq_zero_of_loopClass_eq_zero
    (hi : ContMDiff I' 𝓘(ℝ, V) ∞ i) (hiso : (isNondegenerate_constSmooth σ).IsIsotropicMap I' i)
    (hc : ContMDiff 𝓘(ℝ, ℝ) I' 1 c) (hbd : ∀ θ ∈ uIcc (-π) π, u (circleMap z₀ b θ) = i (c θ))
    {x : N} {γ : Path x x} (hγ : ∀ t : unitInterval, γ t = c (2 * π * t - π))
    (h0 : H₁AddEquivHomology ℤ (.of N) (loopClass ℤ (X := .of N) γ) = 0) :
    pathIntegral σ.radialPrimitive.val (fun θ ↦ u (circleMap z₀ b θ)) (-π) π = 0 := by
  have hclosed := σ.isClosed_mpullback_radialPrimitive hi hiso
  rw [SmoothForm.isClosed_def, SmoothForm.coe_mpullback] at hclosed
  rw [pathIntegral_congr_of_eqOn_uIoo (γ' := i ∘ c) fun θ hθ ↦ hbd θ (uIoo_subset_uIcc_self hθ),
    ← pathIntegral_mpullback _ (fun θ _ ↦ (hi (c θ)).mdifferentiableAt (by simp))
      fun θ _ ↦ (hc θ).mdifferentiableAt one_ne_zero]
  refine pathIntegral_eq_zero_of_loopClass_eq_zero ?_ hclosed hc (fun t ↦ ?_) h0
  · rw [← SmoothForm.coe_mpullback i hi]
    exact (SmoothForm.mpullback i hi σ.radialPrimitive).isSmoothForm.of_le (by simp)
  · rw [hγ t]
    ring_nf

/-- **The energy of a disc bounding on an isotropic submanifold.** For a compatible pair
`(σ, J)`, let `u` be `C²` on the open disc `D = {‖z - z₀‖ < b}` and `C¹` up to its boundary circle,
with Cauchy–Riemann defect `|∂ₛu + J ∂ₜu|² ≤ C` on `D`. If the boundary loop of `u` lifts along a
smooth isotropic map `i : N → V` to a `C¹` curve tracing a loop whose class in `H₁(N; ℤ)` vanishes,
then the energy of `u` on `D` is at most `π b² C / 2`. -/
theorem stdComplexLineEnergy_ball_le_of_loopClass_eq_zero (hcompat : σ.Compatible J)
    (hu : ∀ z ∈ ball z₀ b, ContDiffAt ℝ 2 u z) (hu₁ : ContDiffOn ℝ 1 u (closedBall z₀ b))
    {C : ℝ} (hC : ∀ z ∈ ball z₀ b, σ.associatedBilinForm J (fderiv ℝ u z 1 + J (fderiv ℝ u z I))
      (fderiv ℝ u z 1 + J (fderiv ℝ u z I)) ≤ C)
    (hi : ContMDiff I' 𝓘(ℝ, V) ∞ i) (hiso : (isNondegenerate_constSmooth σ).IsIsotropicMap I' i)
    (hc : ContMDiff 𝓘(ℝ, ℝ) I' 1 c) (hbd : ∀ θ ∈ uIcc (-π) π, u (circleMap z₀ b θ) = i (c θ))
    {x : N} {γ : Path x x} (hγ : ∀ t : unitInterval, γ t = c (2 * π * t - π))
    (h0 : H₁AddEquivHomology ℤ (.of N) (loopClass ℤ (X := .of N) γ) = 0) :
    σ.stdComplexLineEnergy J
        (fun z ↦ ((fderiv ℝ u z).comp (equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ) :
          (ℝ × ℝ) →ₗ[ℝ] V))
        (volume.restrict (ball z₀ b)) ≤
      ENNReal.ofReal (π * b ^ 2 * C / 2) := by
  simpa [pathIntegral_radialPrimitive_circleMap_eq_zero_of_loopClass_eq_zero hi hiso hc hbd hγ h0]
    using stdComplexLineEnergy_ball_le hcompat hu hu₁ hC

/-- **Holomorphic discs bounding on an isotropic submanifold are constant.** Let `u` be a
holomorphic disc, `C²` on the open disc `‖z - z₀‖ < b` and `C¹` up to its boundary circle, whose
target structure is tamed by `σ` along its image. If its boundary loop lifts along a smooth
isotropic map `i : N → V` to a `C¹` curve tracing a loop whose class in `H₁(N; ℤ)` vanishes, then
`u` is constant on the closed disc. -/
theorem exists_eqOn_const_of_loopClass_eq_zero {J : V → AlmostComplexStructure V}
    (hu : ∀ z ∈ ball z₀ b, ContDiffAt ℝ 2 u z) (hu₁ : ContDiffOn ℝ 1 u (closedBall z₀ b))
    (hhol : ∀ z ∈ ball z₀ b,
      IsJHolomorphicAt (fun _ ↦ AlmostComplexStructure.ofComplexModule ℂ) J u z)
    (htame : ∀ z ∈ ball z₀ b, σ.Tames (J (u z)))
    (hi : ContMDiff I' 𝓘(ℝ, V) ∞ i) (hiso : (isNondegenerate_constSmooth σ).IsIsotropicMap I' i)
    (hc : ContMDiff 𝓘(ℝ, ℝ) I' 1 c) (hbd : ∀ θ ∈ uIcc (-π) π, u (circleMap z₀ b θ) = i (c θ))
    {x : N} {γ : Path x x} (hγ : ∀ t : unitInterval, γ t = c (2 * π * t - π))
    (h0 : H₁AddEquivHomology ℤ (.of N) (loopClass ℤ (X := .of N) γ) = 0) :
    ∃ x, EqOn u (fun _ ↦ x) (closedBall z₀ b) := by
  rcases le_or_gt b 0 with hb | hb
  · -- A closed disc of nonpositive radius is at most a point.
    exact (Function.IsConstOn.of_subsingleton (subsingleton_closedBall z₀ hb) u).exists_eqOn_const
  exact (pathIntegral_radialPrimitive_circleMap_eq_zero_iff hb.le hu hu₁ hhol htame).mp
    (pathIntegral_radialPrimitive_circleMap_eq_zero_of_loopClass_eq_zero hi hiso hc hbd hγ h0)

end IsotropicBoundary

end SymplecticForm

end TauCeti
