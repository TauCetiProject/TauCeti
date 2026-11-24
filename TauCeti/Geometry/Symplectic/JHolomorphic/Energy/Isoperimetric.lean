/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Isoperimetric
import TauCeti.Analysis.RCLike.OperatorNorm
import TauCeti.Analysis.SpecialFunctions.Complex.CircleMap
import TauCeti.Topology.MetricSpace.Annulus
import TauCeti.Analysis.Calculus.ContDiff.Differentiable
import TauCeti.Analysis.Calculus.TangentCone.Basic
import TauCeti.Geometry.Symplectic.Duality

/-!
# Boundary control of energy on annuli and half-annuli

A solution of `∂ₜu = J(u) ∂ₛu` on a closed annulus has its real-direction energy bounded by
its two boundary-loop energies, provided a constant symplectic form uniformly tames `J` along
its image. The norm is measured in a fixed compatible inner product, not a metric varying
with `J`. No regularity of `J` beyond the equation and the quantitative taming bound is needed.

The estimate combines the annular Stokes formula with the symplectic isoperimetric inequality.
It does not assume an extension over the inner disc. In a punctured-disc argument, sending the
inner radius to zero and controlling the inner boundary term gives the boundary-energy bound
used to prove energy decay. This file supplies the annular estimate, not that limiting argument
or removal of singularities.

Along a circle, the equation and a bound `‖J(u)‖ ≤ M` bound the angular energy of the boundary
loop by `(1 + M)² r²` times the circle integral of `‖∂ₛu‖²`
(`TauCeti.integral_norm_deriv_comp_circleMap_sq_le`). Combined with the annular estimate, this
bounds the energy of the annulus by the boundary densities of its two circles
(`TauCeti.SymplecticForm.two_mul_mul_integral_norm_fderiv_one_sq_annulus_le`).

The same bound holds on the closed upper half of an annulus about a point of the real axis, for a
solution that is `C²` up to the axis and maps it into a subspace on which the taming form
vanishes, with derivatives taken within the closed upper half-plane and the boundary densities of
the two half-circles in place of those of the circles
(`TauCeti.SymplecticForm.two_mul_mul_integral_norm_fderivWithin_one_sq_upperHalfAnnulus_le`,
with the angular bound `TauCeti.integral_norm_apply_circleMap_sq_le` on the arc `[0, π]`). No
reflection across the axis is used: the boundary half-circles are arcs with endpoints in the
subspace, to which the isoperimetric inequality for such arcs applies.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Sections 4.4 and 4.5.
-/

public section

open Complex MeasureTheory Set
open scoped Real RealInnerProductSpace

namespace TauCeti

section Angular

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {u : ℂ → V} {J : V → V →L[ℝ] V} {z₀ : ℂ} {M : ℝ}

/-- The angular energy of the arc `θ ↦ z₀ + r e^{iθ}`, `α ≤ θ ≤ β`, measured by a family `D` of
derivatives along it, is at most `(1 + M)² r²` times the arc integral of `‖D 1‖²`, when
`D I = J(u) (D 1)` along it with `‖J(u)‖ ≤ M`. For `D` the derivative of `u`, or its derivative
within a closed half-plane, this bounds boundary energies by the boundary densities of radial
energy integrals. -/
theorem integral_norm_apply_circleMap_sq_le {D : ℂ → ℂ →L[ℝ] V} {r α β : ℝ} (hr : 0 ≤ r)
    (hαβ : α ≤ β) (hD : ContinuousOn (fun θ ↦ D (circleMap z₀ r θ)) (Icc α β))
    (hCR : ∀ θ ∈ Icc α β,
      D (circleMap z₀ r θ) I = J (u (circleMap z₀ r θ)) (D (circleMap z₀ r θ) 1))
    (hJ : ∀ θ ∈ Icc α β, ‖J (u (circleMap z₀ r θ))‖ ≤ M) :
    (∫ θ in α..β, ‖D (circleMap z₀ r θ) (circleMap 0 r θ * I)‖ ^ 2) ≤
      (1 + M) ^ 2 * r ^ 2 * ∫ θ in α..β, ‖D (circleMap z₀ r θ) 1‖ ^ 2 := by
  have hcont : ContinuousOn (fun θ ↦ ‖D (circleMap z₀ r θ) (circleMap 0 r θ * I)‖ ^ 2) (Icc α β) :=
    (hD.clm_apply ((continuous_circleMap 0 r).mul continuous_const).continuousOn).norm.pow 2
  have hbcont : ContinuousOn (fun θ ↦ ‖D (circleMap z₀ r θ) 1‖ ^ 2) (Icc α β) :=
    (hD.clm_apply continuousOn_const).norm.pow 2
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hαβ (hcont.intervalIntegrable_of_Icc hαβ)
    ((hbcont.const_mul _).intervalIntegrable_of_Icc hαβ)
  intro θ hθ
  have hs : ‖D (circleMap z₀ r θ) (circleMap 0 r θ * I)‖ ≤
      (1 + M) * r * ‖D (circleMap z₀ r θ) 1‖ := by
    calc _ ≤ ‖D (circleMap z₀ r θ)‖ * ‖circleMap 0 r θ * I‖ := (D (circleMap z₀ r θ)).le_opNorm _
      _ ≤ ((1 + M) * ‖D (circleMap z₀ r θ) 1‖) * r := by
          rw [norm_mul, norm_I, mul_one, norm_circleMap_zero, abs_of_nonneg hr]
          gcongr
          exact (D (circleMap z₀ r θ)).norm_le_of_apply_I_eq (hCR θ hθ) (hJ θ hθ) le_rfl
      _ = _ := by ring
  calc
    _ ≤ ((1 + M) * r * ‖D (circleMap z₀ r θ) 1‖) ^ 2 := by
      gcongr
    _ = _ := by ring

/-- The angular energy of the loop `θ ↦ u (z₀ + r e^{iθ})` is at most `(1 + M)² r²` times the
circle integral of `‖∂ₛu‖²`, for a solution of `∂ₜu = J(u) ∂ₛu` along the circle with
`‖J(u)‖ ≤ M`. This converts the boundary-loop energies of the isoperimetric estimates into the
boundary densities of radial energy integrals. -/
theorem integral_norm_deriv_comp_circleMap_sq_le {r : ℝ} (hr : 0 ≤ r)
    (hu : ∀ θ, ContDiffAt ℝ 1 u (circleMap z₀ r θ))
    (hCR : ∀ θ, fderiv ℝ u (circleMap z₀ r θ) I =
      J (u (circleMap z₀ r θ)) (fderiv ℝ u (circleMap z₀ r θ) 1))
    (hJ : ∀ θ, ‖J (u (circleMap z₀ r θ))‖ ≤ M) :
    (∫ θ in -π..π, ‖deriv (fun θ ↦ u (circleMap z₀ r θ)) θ‖ ^ 2) ≤
      (1 + M) ^ 2 * r ^ 2 *
        ∫ θ in -π..π, ‖fderiv ℝ u (circleMap z₀ r θ) 1‖ ^ 2 := by
  have hdu : Continuous (fun θ ↦ fderiv ℝ u (circleMap z₀ r θ)) :=
    continuous_iff_continuousAt.mpr fun θ ↦
      (hu θ).continuousAt_fderiv (by norm_num) |>.comp
        (continuous_circleMap z₀ r).continuousAt
  have heq (θ : ℝ) : deriv (fun θ ↦ u (circleMap z₀ r θ)) θ =
      fderiv ℝ u (circleMap z₀ r θ) (circleMap 0 r θ * I) :=
    ((hu θ).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt θ
      (hasDerivAt_circleMap z₀ r θ) |>.deriv
  simp_rw [heq]
  exact integral_norm_apply_circleMap_sq_le hr (by linarith [Real.pi_pos]) hdu.continuousOn
    (fun θ _ ↦ hCR θ) (fun θ _ ↦ hJ θ)

end Angular

namespace SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}

/-- For a uniformly tamed solution of `∂ₜu = J(u) ∂ₛu` on an annulus, the integral of
`‖∂ₛu‖²` is at most the sum of the two boundary-loop energies divided by twice the taming
constant. Both loops are parametrized counterclockwise on `[-π, π]`.

The inner product is the fixed compatible metric of `(ω, J₀)`, while `J` may vary with the
target point. Smoothness is required only near the closed annulus, not in its hole. -/
theorem integral_norm_fderiv_one_sq_annulus_le {u : ℂ → V} {J : V → V →L[ℝ] V}
    (z₀ : ℂ) {a b c : ℝ} (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫)
    (ha : 0 ≤ a) (hab : a ≤ b) (hc : 0 < c)
    (hu : ∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ContDiffAt ℝ 2 u z)
    (hCR : ∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b},
      fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (htame : ∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ∀ v : V,
      c * ‖v‖ ^ 2 ≤ ω v (J (u z) v)) :
    (∫ z in {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ‖fderiv ℝ u z 1‖ ^ 2) ≤
      ((∫ θ in -π..π, ‖deriv (fun θ ↦ u (circleMap z₀ b θ)) θ‖ ^ 2) +
        ∫ θ in -π..π, ‖deriv (fun θ ↦ u (circleMap z₀ a θ)) θ‖ ^ 2) / (2 * c) := by
  let A := {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}
  have hcompact : IsCompact A := isCompact_setOf_le_norm_sub_le z₀ a b
  have hDu : ContinuousOn (fderiv ℝ u) A := fun z hz ↦
    ((hu z hz).continuousAt_fderiv (by norm_num)).continuousWithinAt
  have hE : IntegrableOn (fun z ↦ c * ‖fderiv ℝ u z 1‖ ^ 2) A :=
    (continuousOn_const.mul ((hDu.clm_apply continuousOn_const).norm.pow 2)).integrableOn_compact
      hcompact
  have harea := ω.integrableOn_fderiv_apply_of_contDiffAt hcompact fun z hz ↦
    (hu z hz).of_le one_le_two
  have hmono := setIntegral_mono_on hE harea hcompact.measurableSet fun z hz ↦ by
    rw [hCR z hz]
    exact htame z hz (fderiv ℝ u z 1)
  rw [integral_const_mul] at hmono
  have hbound := ω.abs_integral_fderiv_apply_annulus_le z₀ hg ha hab hu
  have h := hmono.trans ((le_abs_self _).trans hbound)
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- **Boundary control of the energy of an annulus.** For a uniformly tamed solution of
`∂ₜu = J(u) ∂ₛu` on the annulus `a ≤ |z - z₀| ≤ b` with `‖J(u)‖ ≤ M`, twice the taming constant
times the energy `∫ ‖∂ₛu‖²` is at most `(1 + M)²` times the sum of the boundary densities
`r (r ∫ ‖∂ₛu(z₀ + r e^{iθ})‖² dθ)` of the two boundary circles. The inner product is the fixed
compatible metric of `(ω, J₀)`. -/
theorem two_mul_mul_integral_norm_fderiv_one_sq_annulus_le {u : ℂ → V} {J : V → V →L[ℝ] V}
    {z₀ : ℂ} {a b c M : ℝ} (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫) (hc : 0 < c) (ha : 0 ≤ a) (hab : a ≤ b)
    (hu : ∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ContDiffAt ℝ 2 u z)
    (hCR : ∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b},
      fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (htame : ∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ∀ v : V,
      c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (hJ : ∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ‖J (u z)‖ ≤ M) :
    2 * c * (∫ z in {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ‖fderiv ℝ u z 1‖ ^ 2) ≤
      (1 + M) ^ 2 * (b * (b * ∫ θ in -π..π, ‖fderiv ℝ u (circleMap z₀ b θ) 1‖ ^ 2) +
        a * (a * ∫ θ in -π..π, ‖fderiv ℝ u (circleMap z₀ a θ) 1‖ ^ 2)) := by
  have hmem (r : ℝ) (hr : r ∈ Icc a b) (θ : ℝ) :=
    circleMap_mem_setOf_le_norm_sub_le (z₀ := z₀) ha hr θ
  have hbound := ω.integral_norm_fderiv_one_sq_annulus_le z₀ hg ha hab hc hu hCR htame
  have hb := integral_norm_deriv_comp_circleMap_sq_le (ha.trans hab)
    (fun θ ↦ (hu _ (hmem b ⟨hab, le_rfl⟩ θ)).of_le one_le_two)
    (fun θ ↦ hCR _ (hmem b ⟨hab, le_rfl⟩ θ)) (fun θ ↦ hJ _ (hmem b ⟨hab, le_rfl⟩ θ))
  have ha' := integral_norm_deriv_comp_circleMap_sq_le ha
    (fun θ ↦ (hu _ (hmem a ⟨le_rfl, hab⟩ θ)).of_le one_le_two)
    (fun θ ↦ hCR _ (hmem a ⟨le_rfl, hab⟩ θ)) (fun θ ↦ hJ _ (hmem a ⟨le_rfl, hab⟩ θ))
  rw [le_div_iff₀ (by positivity)] at hbound
  nlinarith

/-- **Boundary control of the energy of an upper half-annulus.** Let `u` solve
`∂ₜu = J(u) ∂ₛu` on the closed upper half `S` of the annulus of radii `0 ≤ a ≤ b` about a point
`x₀` of the real axis, with derivatives taken within the closed upper half-plane. Suppose that `u`
is `C²` on `{z | 0 ≤ z.im} ∩ O` for an open set `O` containing `S`, maps the points of `O` on the
real axis into a subspace `L` on which `ω` vanishes, is uniformly tamed by `ω` with
constant `c` and satisfies `‖J(u)‖ ≤ M` on `S`. Then twice the taming constant times the energy
`∫_S ‖∂ₛu‖²` is at most `(1 + M)²` times the sum of the boundary densities
`r (r ∫₀^π ‖∂ₛu(x₀ + r e^{iθ})‖² dθ)` of the two boundary half-circles. The inner product is the
fixed compatible metric of `(ω, J₀)`. -/
theorem two_mul_mul_integral_norm_fderivWithin_one_sq_upperHalfAnnulus_le {u : ℂ → V}
    {J : V → V →L[ℝ] V} {x₀ : ℂ} {O : Set ℂ} {L : Submodule ℝ V} {a b c M : ℝ}
    (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫) (ha : 0 ≤ a) (hab : a ≤ b) (hx₀ : x₀.im = 0)
    (hO : IsOpen O) (hSO : {z : ℂ | 0 ≤ z.im ∧ a ≤ ‖z - x₀‖ ∧ ‖z - x₀‖ ≤ b} ⊆ O)
    (hu : ContDiffOn ℝ 2 u ({z : ℂ | 0 ≤ z.im} ∩ O))
    (hCR : ∀ z ∈ {z : ℂ | 0 ≤ z.im ∧ a ≤ ‖z - x₀‖ ∧ ‖z - x₀‖ ≤ b},
      fderivWithin ℝ u {z | 0 ≤ z.im} z I = J (u z) (fderivWithin ℝ u {z | 0 ≤ z.im} z 1))
    (htame : ∀ z ∈ {z : ℂ | 0 ≤ z.im ∧ a ≤ ‖z - x₀‖ ∧ ‖z - x₀‖ ≤ b}, ∀ v : V,
      c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (hJ : ∀ z ∈ {z : ℂ | 0 ≤ z.im ∧ a ≤ ‖z - x₀‖ ∧ ‖z - x₀‖ ≤ b}, ‖J (u z)‖ ≤ M)
    (hLω : ∀ v ∈ L, ∀ w ∈ L, ω v w = 0)
    (huL : ∀ z ∈ O, z.im = 0 → u z ∈ L) :
    2 * c * (∫ z in {z : ℂ | 0 ≤ z.im ∧ a ≤ ‖z - x₀‖ ∧ ‖z - x₀‖ ≤ b},
        ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖ ^ 2) ≤
      (1 + M) ^ 2 * (b * (b * ∫ θ in 0..π,
          ‖fderivWithin ℝ u {z | 0 ≤ z.im} (circleMap x₀ b θ) 1‖ ^ 2) +
        a * (a * ∫ θ in 0..π, ‖fderivWithin ℝ u {z | 0 ≤ z.im} (circleMap x₀ a θ) 1‖ ^ 2)) := by
  set S := {z : ℂ | 0 ≤ z.im ∧ a ≤ ‖z - x₀‖ ∧ ‖z - x₀‖ ≤ b}
  set H : Set ℂ := {z | 0 ≤ z.im}
  set Du := fderivWithin ℝ u H
  have hSc : IsCompact S :=
    (isCompact_setOf_le_norm_sub_le x₀ a b).of_isClosed_subset
      (by simpa only [hx₀] using isClosed_upperHalfAnnulus x₀ a b) fun z hz ↦ hz.2
  have hDu : ContinuousOn Du S :=
    (hu.continuousOn_fderivWithin_of_inter (uniqueDiffOn_setOfPred_le_im _) hO
      (by norm_num)).mono fun z hz ↦ ⟨hz.1, hSO hz⟩
  -- The taming bound compares the energy with the symplectic area.
  have hE : IntegrableOn (fun z ↦ c * ‖Du z 1‖ ^ 2) S :=
    (continuousOn_const.mul ((hDu.clm_apply continuousOn_const).norm.pow 2)).integrableOn_compact
      hSc
  have harea : IntegrableOn (fun z ↦ ω (Du z 1) (Du z I)) S :=
    (ω.continuousOn_apply_comp (hDu.clm_apply continuousOn_const)
      (hDu.clm_apply continuousOn_const)).integrableOn_compact hSc
  have hmono := setIntegral_mono_on hE harea hSc.measurableSet fun z hz ↦ by
    rw [hCR z hz]
    exact htame z hz (Du z 1)
  rw [integral_const_mul] at hmono
  -- The isoperimetric bound for the half-annulus, with boundary on `L`.
  have hbound := ω.abs_integral_fderivWithin_apply_upperHalfAnnulus_le hg x₀ hO ha hab
    (by rwa [hx₀]) (by rwa [hx₀]) hLω (by rwa [hx₀])
  rw [hx₀] at hbound
  -- The boundary energies are bounded by the boundary densities.
  have hmem (r : ℝ) (hr : r ∈ Icc a b) (θ : ℝ) (hθ : θ ∈ Icc 0 π) : circleMap x₀ r θ ∈ S := by
    simpa only [S, hx₀] using circleMap_mem_upperHalfAnnulus (z₀ := x₀) ha hr hθ
  have hdens (r : ℝ) (hr : r ∈ Icc a b) :=
    integral_norm_apply_circleMap_sq_le (u := u) (J := J) (M := M) (ha.trans hr.1)
      Real.pi_pos.le
      (hDu.comp (continuous_circleMap x₀ r).continuousOn (hmem r hr))
      (fun θ hθ ↦ hCR _ (hmem r hr θ hθ)) (fun θ hθ ↦ hJ _ (hmem r hr θ hθ))
  have hb := hdens b ⟨hab, le_rfl⟩
  have ha' := hdens a ⟨le_rfl, hab⟩
  have h := hmono.trans ((le_abs_self _).trans hbound)
  nlinarith

end SymplecticForm

end TauCeti
