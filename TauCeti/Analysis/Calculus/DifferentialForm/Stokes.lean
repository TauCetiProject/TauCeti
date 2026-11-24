/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Analysis.Calculus.DifferentialForm.CylinderHomotopy
import TauCeti.Analysis.Calculus.DifferentialForm.Plane
import TauCeti.Analysis.Calculus.DifferentialForm.Regularity
import TauCeti.Analysis.Calculus.ContDiff.ContinuousAlternatingMap
public import TauCeti.MeasureTheory.Integral.PolarCoord
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import TauCeti.MeasureTheory.Integral.DominatedConvergence
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.InterBall
import TauCeti.Analysis.SpecialFunctions.Complex.CircleMap

/-!
# Stokes' formula for one-forms on rectangles and annuli

The integral of the exterior derivative of a vector-valued real one-form over a rectangle or
closed annulus is its positively oriented boundary integral. Zero inner radius gives the disc
formula. Only C¹ regularity near the region of integration is required; in the annular
case no regularity on the missing inner disc is needed. On a rectangle it suffices that the form
be continuous on the closed rectangle and differentiable inside, with integrable exterior
derivative (`TauCeti.integral_prod_Icc_eq_of_extDeriv_eq`). This gives the formula on a
closed upper half-annulus for forms that are only regular up to its diameter, such as forms built
from one-sided derivatives of maps on a half-plane, in terms of a continuous extension of the
exterior derivative to the closed half-annulus
(`TauCeti.integral_upperHalfAnnulus_eq_of_extDeriv_eq`); its boundary consists of two half-circles
and two segments of the diameter. On a rectangle the formula is stated both
for the set integral over `Icc a b` (`TauCeti.integral_extDeriv_prod_Icc`) and for the iterated
integral over oriented intervals (`TauCeti.integral2_extDeriv`). For a scalar one-form
`f_s ds + f_t dt` it is Green's theorem `TauCeti.integral_fderiv_sub_fderiv_Icc`, written in
terms of the partial derivatives `∂_s f_t - ∂_t f_s`.

One dimension up, the integral of a closed two-form over the boundary of a cube vanishes: its
integrals over the top and bottom faces differ by the signed integrals over the four side faces
(`TauCeti.integral2_slice_sub_eq_sides`). This follows from the rectangle formula applied to the
cylinder homotopy operator `TauCeti.cylinderHomotopy`, a primitive of the difference of the top
and bottom slices of a closed form. Pulled back along a homotopy of maps into a manifold, it gives
the homotopy invariance of integrals of closed two-forms over cylinders.

Unlike the bilinear-pairing version of Green's formula, these results apply to arbitrary
one-forms, including pullbacks of Liouville forms from exact symplectic manifolds. They
provide the area calculation used to exclude holomorphic discs with exact Lagrangian boundary.

The proofs use Mathlib's rectangular divergence theorem, naturality of the exterior
derivative, and the polar change of variables. Applying the rectangle formula to the polar
pullback gives the annulus formula: the seam edges cancel, and the radial Jacobian is given by
`extDeriv_pullback_polarCoord_symm_apply`. On an open disc, a one-form which is `C¹` inside and
only continuous up to the boundary circle still satisfies Stokes' formula when its exterior
derivative is integrable (`TauCeti.integral_extDeriv_ball`): apply the closed-disc formula on the
concentric discs of radius `s < r` and let `s` tend to `r`. The bilinear Green formulas in
`TauCeti.MeasureTheory.Integral.DivergenceTheorem` are special cases.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 16 (Stokes' theorem).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Section 4.1 (symplectic area and exactness).
-/

public section

open MeasureTheory Set Complex
open scoped Real

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Stokes' formula on a rectangle for a one-form `ω` that is continuous on the closed rectangle
and differentiable in its interior, where its exterior derivative on `((1, 0), (0, 1))` agrees with
a function `dω` integrable on the closed rectangle. The right and bottom edges have positive signs;
the left and top edges have negative signs. -/
theorem integral_prod_Icc_eq_of_extDeriv_eq
    {ω : (ℝ × ℝ) → (ℝ × ℝ) [⋀^Fin 1]→L[ℝ] F} {dω : ℝ × ℝ → F} {a b : ℝ × ℝ} (hab : a ≤ b)
    (hc : ContinuousOn ω (Icc a b))
    (hd : ∀ z ∈ Ioo a.1 b.1 ×ˢ Ioo a.2 b.2,
      DifferentiableAt ℝ ω z ∧ extDeriv ω z ![(1, 0), (0, 1)] = dω z)
    (hi : IntegrableOn dω (Icc a b)) :
    (∫ z in Icc a b, dω z) =
      ((∫ t in a.2..b.2, ω (b.1, t) (fun _ ↦ (0, 1))) -
        ∫ t in a.2..b.2, ω (a.1, t) (fun _ ↦ (0, 1))) -
      ((∫ s in a.1..b.1, ω (s, b.2) (fun _ ↦ (1, 0))) -
        ∫ s in a.1..b.1, ω (s, a.2) (fun _ ↦ (1, 0))) := by
  let f := fun z ↦ ω z (fun _ ↦ (0, 1))
  let g := fun z ↦ -ω z (fun _ ↦ (1, 0))
  set U : Set (ℝ × ℝ) := Ioo a.1 b.1 ×ˢ Ioo a.2 b.2
  have hU : MeasurableSet U := measurableSet_Ioo.prod measurableSet_Ioo
  have hf z (hz : z ∈ U) := (hd z hz).1.hasFDerivAt.continuousAlternatingMap_apply_const
    (fun _ ↦ ((0, 1) : ℝ × ℝ))
  have hg z (hz : z ∈ U) : HasFDerivAt g
      (-(fderiv ℝ ω z).flipAlternating fun _ ↦ ((1, 0) : ℝ × ℝ)) z :=
    ((hd z hz).1.hasFDerivAt.continuousAlternatingMap_apply_const
      (fun _ ↦ ((1, 0) : ℝ × ℝ))).neg
  have hcurl z (hz : z ∈ U) :
      fderiv ℝ f z (1, 0) + fderiv ℝ g z (0, 1) = dω z := by
    rw [← (hd z hz).2]
    simp [f, g, extDeriv_apply_pair_of_differentiableAt (hd z hz).1, sub_eq_add_neg]
  -- The boundary of the rectangle is null, so only the interior matters.
  have hIoo : U =ᵐ[volume] Icc a b := by
    rw [Icc_prod_eq, Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc
  have hi' : IntegrableOn (fun z ↦ fderiv ℝ f z (1, 0) + fderiv ℝ g z (0, 1)) (Icc a b) :=
    (((hi.congr_set_ae hIoo).congr_fun (fun z hz ↦ (hcurl z hz).symm) hU)).congr_set_ae
      hIoo.symm
  have h := integral_divergence_prod_Icc_of_hasFDerivAt_of_le f g (fderiv ℝ f) (fderiv ℝ g) a b
    hab ((ContinuousAlternatingMap.apply ℝ _ F _).continuous.comp_continuousOn hc)
    ((ContinuousAlternatingMap.apply ℝ _ F _).continuous.comp_continuousOn hc).neg
    (fun z hz ↦ (hf z hz).differentiableAt.hasFDerivAt)
    (fun z hz ↦ (hg z hz).differentiableAt.hasFDerivAt) hi'
  rw [setIntegral_congr_set hIoo.symm, setIntegral_congr_fun hU hcurl,
    setIntegral_congr_set hIoo] at h
  simp only [f, g, intervalIntegral.integral_neg] at h
  rw [h]
  abel

/-- Stokes' formula on a rectangle for a one-form that is C¹ near the closed rectangle.
The right and bottom edges have positive signs; the left and top edges have negative signs. -/
theorem integral_extDeriv_prod_Icc
    {ω : (ℝ × ℝ) → (ℝ × ℝ) [⋀^Fin 1]→L[ℝ] F} {a b : ℝ × ℝ}
    (hab : a ≤ b) (hω : ∀ z ∈ Icc a b, ContDiffAt ℝ 1 ω z) :
    (∫ z in Icc a b, extDeriv ω z ![(1, 0), (0, 1)]) =
      ((∫ t in a.2..b.2, ω (b.1, t) (fun _ ↦ (0, 1))) -
        ∫ t in a.2..b.2, ω (a.1, t) (fun _ ↦ (0, 1))) -
      ((∫ s in a.1..b.1, ω (s, b.2) (fun _ ↦ (1, 0))) -
        ∫ s in a.1..b.1, ω (s, a.2) (fun _ ↦ (1, 0))) := by
  have hsub : Ioo a.1 b.1 ×ˢ Ioo a.2 b.2 ⊆ Icc a b := by
    rw [Icc_prod_eq]
    exact prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  exact integral_prod_Icc_eq_of_extDeriv_eq hab
    (fun z hz ↦ (hω z hz).continuousAt.continuousWithinAt)
    (fun z hz ↦ ⟨(hω z (hsub hz)).differentiableAt one_ne_zero, rfl⟩)
    ((continuousOn_of_forall_continuousAt fun z hz ↦
      continuousAt_extDeriv_apply (hω z hz) _).integrableOn_compact isCompact_Icc)

section Green

variable {U : Set (ℝ × ℝ)} {fs ft : ℝ × ℝ → ℝ} {a b : ℝ × ℝ}

/-- The exterior derivative `∂_s f_t - ∂_t f_s` of a one-form `f_s ds + f_t dt` that is `C¹` over
an open neighbourhood of a rectangle is integrable over the rectangle. -/
theorem integrableOn_fderiv_sub_fderiv_Icc (hU : IsOpen U) (hfs : ContDiffOn ℝ 1 fs U)
    (hft : ContDiffOn ℝ 1 ft U) (habU : Icc a b ⊆ U) :
    IntegrableOn (fun z ↦ fderiv ℝ ft z (1, 0) - fderiv ℝ fs z (0, 1)) (Icc a b) :=
  ((((hft.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const).sub
    ((hfs.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const)).mono
      habU).integrableOn_compact isCompact_Icc

/-- **Green's theorem on a rectangle.** For a one-form `f_s ds + f_t dt` that is `C¹` over an
open neighbourhood of a rectangle `[a₁, b₁] × [a₂, b₂]`, the integral of its exterior derivative
`∂_s f_t - ∂_t f_s` over the rectangle is its integral over the positively oriented boundary. -/
theorem integral_fderiv_sub_fderiv_Icc (hU : IsOpen U) (hfs : ContDiffOn ℝ 1 fs U)
    (hft : ContDiffOn ℝ 1 ft U) (hab : a ≤ b) (habU : Icc a b ⊆ U) :
    ∫ z in Icc a b, (fderiv ℝ ft z (1, 0) - fderiv ℝ fs z (0, 1)) =
      (∫ s in a.1..b.1, fs (s, a.2)) + (∫ t in a.2..b.2, ft (b.1, t)) -
        (∫ s in a.1..b.1, fs (s, b.2)) - ∫ t in a.2..b.2, ft (a.1, t) := by
  -- Stokes' formula for the one-form `f_s dx + f_t dy`.
  have hω (z) (hz : z ∈ Icc a b) :
      ContDiffAt ℝ 1 (fun z ↦ fs z • Prod.realPlaneDx z + ft z • Prod.realPlaneDy z) z :=
    ((hfs.contDiffAt (hU.mem_nhds (habU hz))).smul Prod.contDiff_realPlaneDx.contDiffAt).add
      ((hft.contDiffAt (hU.mem_nhds (habU hz))).smul Prod.contDiff_realPlaneDy.contDiffAt)
  have h := integral_extDeriv_prod_Icc hab hω
  rw [setIntegral_congr_fun measurableSet_Icc fun z hz ↦
    extDeriv_apply_pair_of_differentiableAt ((hω z hz).differentiableAt one_ne_zero) _ _] at h
  simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
    Prod.realPlaneDx_apply, Prod.realPlaneDy_apply, smul_eq_mul, mul_zero, mul_one, add_zero,
    zero_add] at h
  rw [h]
  ring

end Green

/-- Stokes' formula on a rectangle, as an iterated integral over oriented intervals, for a one-form
that is C¹ near the closed rectangle. The corners may come in either order. -/
theorem integral2_extDeriv
    {ω : (ℝ × ℝ) → (ℝ × ℝ) [⋀^Fin 1]→L[ℝ] F} {a₁ a₂ b₁ b₂ : ℝ}
    (hω : ∀ z ∈ uIcc a₁ b₁ ×ˢ uIcc a₂ b₂, ContDiffAt ℝ 1 ω z) :
    (∫ s in a₁..b₁, ∫ t in a₂..b₂, extDeriv ω (s, t) ![(1, 0), (0, 1)]) =
      ((∫ t in a₂..b₂, ω (b₁, t) (fun _ ↦ (0, 1))) -
        ∫ t in a₂..b₂, ω (a₁, t) (fun _ ↦ (0, 1))) -
      ((∫ s in a₁..b₁, ω (s, b₂) (fun _ ↦ (1, 0))) -
        ∫ s in a₁..b₁, ω (s, a₂) (fun _ ↦ (1, 0))) := by
  let f := fun z ↦ ω z (fun _ ↦ (0, 1))
  let g := fun z ↦ -ω z (fun _ ↦ (1, 0))
  have hf z hz := ((hω z hz).differentiableAt one_ne_zero).hasFDerivAt
    |>.continuousAlternatingMap_apply_const (fun _ ↦ (0, 1))
  have hg z hz := (((hω z hz).differentiableAt one_ne_zero).hasFDerivAt
    |>.continuousAlternatingMap_apply_const (fun _ ↦ (1, 0))).neg
  have hcurl z (hz : z ∈ uIcc a₁ b₁ ×ˢ uIcc a₂ b₂) :
      fderiv ℝ f z (1, 0) + fderiv ℝ g z (0, 1) =
        extDeriv ω z ![(1, 0), (0, 1)] := by
    simp [f, g, extDeriv_apply_pair_of_differentiableAt
      ((hω z hz).differentiableAt one_ne_zero), sub_eq_add_neg]
  have hcont : ContinuousOn (fun z ↦ extDeriv ω z ![(1, 0), (0, 1)])
      (uIcc a₁ b₁ ×ˢ uIcc a₂ b₂) :=
    fun z hz ↦ (continuousAt_extDeriv_apply (hω z hz) _).continuousWithinAt
  have hsub : Ioo (min a₁ b₁) (max a₁ b₁) ×ˢ Ioo (min a₂ b₂) (max a₂ b₂) \ ∅ ⊆
      uIcc a₁ b₁ ×ˢ uIcc a₂ b₂ := by
    rw [sdiff_empty]
    exact prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  have h := integral2_divergence_prod_of_hasFDerivAt_off_countable f g
    (fderiv ℝ f) (fderiv ℝ g) a₁ a₂ b₁ b₂ ∅ countable_empty
    (fun z hz ↦ (hf z hz).continuousAt.continuousWithinAt)
    (fun z hz ↦ (hg z hz).continuousAt.continuousWithinAt)
    (fun z hz ↦ (hf z (hsub hz)).differentiableAt.hasFDerivAt)
    (fun z hz ↦ (hg z (hsub hz)).differentiableAt.hasFDerivAt)
    ((hcont.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).congr_fun
      (fun z hz ↦ (hcurl z hz).symm) (measurableSet_uIcc.prod measurableSet_uIcc))
  have hinner : ∀ s ∈ uIcc a₁ b₁, (∫ t in a₂..b₂, fderiv ℝ f (s, t) (1, 0) +
      fderiv ℝ g (s, t) (0, 1)) = ∫ t in a₂..b₂, extDeriv ω (s, t) ![(1, 0), (0, 1)] :=
    fun s hs ↦ intervalIntegral.integral_congr fun t ht ↦ hcurl (s, t) ⟨hs, ht⟩
  rw [intervalIntegral.integral_congr hinner] at h
  simp only [f, g, intervalIntegral.integral_neg] at h
  rw [h]
  abel

/-- **Stokes' formula on the boundary of a cube** for a closed two-form `ψ` that is C¹ on
`(ℝ × ℝ) × ℝ`: its integrals over the top and bottom faces `[a, b] × {1}` and `[a, b] × {0}`
differ by the signed sum of its integrals over the four side faces, each parametrized by the
direction of its edge followed by the last coordinate. All integrals are iterated integrals over
oriented intervals, so the corners `a` and `b` may come in either order.

The proof applies Stokes' formula on the rectangle to the cylinder homotopy `h ψ`, whose exterior
derivative is the difference of the top and bottom slices of the closed form `ψ`. -/
theorem integral2_slice_sub_eq_sides
    {ψ : (ℝ × ℝ) × ℝ → ((ℝ × ℝ) × ℝ) [⋀^Fin 2]→L[ℝ] F} (hψ : ContDiff ℝ 1 ψ)
    (hdψ : extDeriv ψ = 0) (a b : ℝ × ℝ) :
    ((∫ s in a.1..b.1, ∫ t in a.2..b.2, ψ ((s, t), 1) ![((1, 0), 0), ((0, 1), 0)]) -
        ∫ s in a.1..b.1, ∫ t in a.2..b.2, ψ ((s, t), 0) ![((1, 0), 0), ((0, 1), 0)]) =
      ((∫ t in a.2..b.2, ∫ c in (0 : ℝ)..1, ψ ((a.1, t), c) ![((0, 1), 0), (0, 1)]) -
          ∫ t in a.2..b.2, ∫ c in (0 : ℝ)..1, ψ ((b.1, t), c) ![((0, 1), 0), (0, 1)]) -
        ((∫ s in a.1..b.1, ∫ c in (0 : ℝ)..1, ψ ((s, a.2), c) ![((1, 0), 0), (0, 1)]) -
          ∫ s in a.1..b.1, ∫ c in (0 : ℝ)..1, ψ ((s, b.2), c) ![((1, 0), 0), (0, 1)]) := by
  by_cases hF : CompleteSpace F
  swap
  · -- Without completeness every Bochner integral is `0`.
    simp [intervalIntegral, MeasureTheory.integral_of_not_completeSpace hF]
  -- The cylinder homotopy `β = h ψ` is a primitive of `ι₁^* ψ - ι₀^* ψ`.
  let β := cylinderHomotopy ψ
  have hβ : ContDiff ℝ 1 β := contDiff_cylinderHomotopy hψ
  have hdβ (z : ℝ × ℝ) : extDeriv β z = (ψ (z, 1)).compContinuousLinearMap (.inl ℝ (ℝ × ℝ) ℝ) -
      (ψ (z, 0)).compContinuousLinearMap (.inl ℝ (ℝ × ℝ) ℝ) := by
    have h := extDeriv_cylinderHomotopy_add_cylinderHomotopy_extDeriv hψ z
    rwa [hdψ, cylinderHomotopy_zero, Pi.zero_apply, add_zero] at h
  -- On an edge direction `v`, `β` is minus the integral of `ψ(v, ∂_c)` over `c ∈ [0, 1]`.
  have hβv (z v : ℝ × ℝ) :
      β z (fun _ ↦ v) = -∫ c in (0 : ℝ)..1, ψ (z, c) ![(v, 0), (0, 1)] := by
    rw [cylinderHomotopy_apply_apply
      ((hψ.continuous.comp (Continuous.prodMk_right z)).intervalIntegrable _ _),
      ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun c _ ↦ ?_
    have h := (ψ (z, c)).toAlternatingMap.map_swap (v := ![(v, 0), (0, 1)]) (i := 0) (j := 1)
      (by decide)
    have hv : (![(v, 0), (0, 1)] ∘ Equiv.swap (0 : Fin 2) 1 : Fin 2 → (ℝ × ℝ) × ℝ) =
        Fin.cons (0, 1) fun _ ↦ (v, 0) := by
      funext i
      fin_cases i <;> rfl
    exact (congrArg (ψ (z, c)) hv).symm.trans h
  -- The difference of the top and bottom faces is the integral of `dβ`.
  have hd (s t : ℝ) : extDeriv β (s, t) ![(1, 0), (0, 1)] =
      ψ ((s, t), 1) ![((1, 0), 0), ((0, 1), 0)] - ψ ((s, t), 0) ![((1, 0), 0), ((0, 1), 0)] := by
    rw [hdβ, ContinuousAlternatingMap.sub_apply,
      ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousAlternatingMap.compContinuousLinearMap_apply]
    congr 2 <;> funext i <;> fin_cases i <;> rfl
  have hcont (c : ℝ) : Continuous fun z : ℝ × ℝ ↦ ψ (z, c) ![((1, 0), 0), ((0, 1), 0)] :=
    (ContinuousAlternatingMap.apply ℝ ((ℝ × ℝ) × ℝ) F _).continuous.comp
      (hψ.continuous.comp (Continuous.prodMk_left c))
  have hin (c s : ℝ) : IntervalIntegrable
      (fun t ↦ ψ ((s, t), c) ![((1, 0), 0), ((0, 1), 0)]) volume a.2 b.2 :=
    ((hcont c).comp (Continuous.prodMk_right s)).intervalIntegrable _ _
  have hout (c : ℝ) : IntervalIntegrable
      (fun s ↦ ∫ t in a.2..b.2, ψ ((s, t), c) ![((1, 0), 0), ((0, 1), 0)]) volume a.1 b.1 :=
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun s t ↦ ψ ((s, t), c) ![((1, 0), 0), ((0, 1), 0)]) (hcont c) _ _).intervalIntegrable
      _ _
  have htop : ((∫ s in a.1..b.1, ∫ t in a.2..b.2, ψ ((s, t), 1) ![((1, 0), 0), ((0, 1), 0)]) -
        ∫ s in a.1..b.1, ∫ t in a.2..b.2, ψ ((s, t), 0) ![((1, 0), 0), ((0, 1), 0)]) =
      ∫ s in a.1..b.1, ∫ t in a.2..b.2, extDeriv β (s, t) ![(1, 0), (0, 1)] := by
    rw [← intervalIntegral.integral_sub (hout 1) (hout 0)]
    refine intervalIntegral.integral_congr fun s _ ↦ ?_
    simp only [hd]
    exact (intervalIntegral.integral_sub (hin 1 s) (hin 0 s)).symm
  rw [htop, integral2_extDeriv fun z _ ↦ hβ.contDiffAt]
  simp only [hβv, intervalIntegral.integral_neg]
  abel

/-- The exterior derivative of a one-form pulled back by the translated polar map,
evaluated on the standard pair, includes exactly the radial Jacobian. -/
theorem extDeriv_pullback_polarCoord_symm_apply
    {ω : ℂ → ℂ [⋀^Fin 1]→L[ℝ] F} (z₀ : ℂ) (p : ℝ × ℝ)
    (hω : DifferentiableAt ℝ ω (z₀ + Complex.polarCoord.symm p)) :
    extDeriv (fun q ↦ (ω (z₀ + Complex.polarCoord.symm q)).compContinuousLinearMap
      (fderiv ℝ (fun q ↦ z₀ + Complex.polarCoord.symm q) q)) p ![(1, 0), (0, 1)] =
      p.1 • extDeriv ω (z₀ + Complex.polarCoord.symm p) ![1, I] := by
  rw [extDeriv_pullback (f := fun q ↦ z₀ + Complex.polarCoord.symm q) hω
    (contDiff_add_polarCoord_symm z₀ (n := 2)).contDiffAt (by norm_num),
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  have hvec : (fun i ↦ fderiv ℝ (fun q ↦ z₀ + Complex.polarCoord.symm q) p
      (![(1, 0), (0, 1)] i)) = ![exp (p.2 * I), circleMap 0 p.1 p.2 * I] := by
    funext i
    rw [(hasFDerivAt_add_polarCoord_symm p z₀).fderiv]
    fin_cases i <;> simp [equivRealProd_symm_fderivPolarCoordSymm_apply_one_zero,
      equivRealProd_symm_fderivPolarCoordSymm_apply_zero_one]
  simp only [Function.comp_def, hvec]
  -- Convert the derivative of the one-form to a bilinear map for the polar Jacobian identity.
  let C : (ℂ [⋀^Fin 1]→L[ℝ] F) →L[ℝ] ℂ →L[ℝ] F :=
    (ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)).symm.toContinuousLinearEquiv
      |>.toContinuousLinearMap
  let B := C.comp (fderiv ℝ ω (z₀ + Complex.polarCoord.symm p))
  have hB v w : B v w = (fderiv ℝ ω (z₀ + Complex.polarCoord.symm p) v) (fun _ ↦ w) := by
    simp [B, C, ContinuousAlternatingMap.ofSubsingletonLIE_symm_apply]
  simpa only [extDeriv_apply_pair, ContinuousLinearMap.toLinearMap₁₂_apply,
    LinearMap.comp_apply, ContinuousLinearMap.coeLMₛₗ_apply,
    ContinuousLinearMap.coe_coe, LinearMap.id_apply, hB] using
    B.toLinearMap₁₂.apply_exp_circleMap_sub_swap (LinearMap.id) p.1 p.2

/-- The pullback of a one-form on `ℂ` along the translated inverse polar map
`p ↦ z₀ + p.1 e^{i p.2}`. -/
private noncomputable def polarPullback (ω : ℂ → ℂ [⋀^Fin 1]→L[ℝ] F) (z₀ : ℂ) :
    ℝ × ℝ → (ℝ × ℝ) [⋀^Fin 1]→L[ℝ] F :=
  fun p ↦ (ω (z₀ + Complex.polarCoord.symm p)).compContinuousLinearMap
    (fderiv ℝ (fun q ↦ z₀ + Complex.polarCoord.symm q) p)

/-- The polar pullback on the radial vector is the form on the unit radial vector `e^{iθ}`. -/
private theorem polarPullback_apply_radial (ω : ℂ → ℂ [⋀^Fin 1]→L[ℝ] F) (z₀ : ℂ) (r θ : ℝ) :
    polarPullback ω z₀ (r, θ) (fun _ ↦ (1, 0)) = ω (circleMap z₀ r θ) (fun _ ↦ exp (θ * I)) := by
  have hd : fderiv ℝ (fun q ↦ z₀ + Complex.polarCoord.symm q) (r, θ) (1, 0) = exp (θ * I) := by
    simp only [(hasFDerivAt_add_polarCoord_symm (r, θ) z₀).fderiv, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, equivRealProd_symm_fderivPolarCoordSymm_apply_one_zero]
  simp only [polarPullback, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    Function.comp_def, hd]
  rw [add_polarCoord_symm_eq_circleMap]

/-- The polar pullback on the angular vector is the form on the circle velocity. -/
private theorem polarPullback_apply_angular (ω : ℂ → ℂ [⋀^Fin 1]→L[ℝ] F) (z₀ : ℂ) (r θ : ℝ) :
    polarPullback ω z₀ (r, θ) (fun _ ↦ (0, 1)) =
      ω (circleMap z₀ r θ) (fun _ ↦ circleMap 0 r θ * I) := by
  have hd : fderiv ℝ (fun q ↦ z₀ + Complex.polarCoord.symm q) (r, θ) (0, 1) =
      circleMap 0 r θ * I := by
    simp only [(hasFDerivAt_add_polarCoord_symm (r, θ) z₀).fderiv, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, equivRealProd_symm_fderivPolarCoordSymm_apply_zero_one]
  simp only [polarPullback, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    Function.comp_def, hd]
  rw [add_polarCoord_symm_eq_circleMap]

/-- Stokes' formula for a real one-form near a closed annulus. Both circles are traversed
counterclockwise; the inner circle is subtracted. The inner radius may be zero. -/
theorem integral_extDeriv_annulus
    {ω : ℂ → ℂ [⋀^Fin 1]→L[ℝ] F} (z₀ : ℂ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hω : ∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ContDiffAt ℝ 1 ω z) :
    (∫ z in {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, extDeriv ω z ![1, I]) =
      (∫ θ in -π..π, ω (circleMap z₀ b θ) (fun _ ↦ circleMap 0 b θ * I)) -
        ∫ θ in -π..π, ω (circleMap z₀ a θ) (fun _ ↦ circleMap 0 a θ * I) := by
  -- Pull back to a polar rectangle. The pullback is C¹ even at radius zero.
  have hmem (p : ℝ × ℝ) (hp : p ∈ Icc (a, -π) (b, π)) :
      z₀ + Complex.polarCoord.symm p ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b} :=
    add_polarCoord_symm_mem_annulus z₀ ha ⟨hp.1.1, hp.2.1⟩
  have hη p (hp : p ∈ Icc (a, -π) (b, π)) : ContDiffAt ℝ 1 (polarPullback ω z₀) p :=
    (contDiff_add_polarCoord_symm z₀).contDiffAt.differentialForm_pullback (hω _ (hmem p hp))
  have hgreen := integral_extDeriv_prod_Icc
    (a := (a, -π)) (b := (b, π)) ⟨hab, by linarith [Real.pi_pos]⟩ hη
  -- Naturality and the polar Jacobian convert the interior integral back to the annulus.
  have harea : (∫ p in Icc (a, -π) (b, π), extDeriv (polarPullback ω z₀) p ![(1, 0), (0, 1)]) =
      ∫ z in {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, extDeriv ω z ![1, I] := by
    rw [← Complex.integral_comp_polarCoord_symm_Icc _ z₀ ha]
    exact setIntegral_congr_fun measurableSet_Icc fun p hp ↦
      extDeriv_pullback_polarCoord_symm_apply z₀ p
        ((hω _ (hmem p hp)).differentiableAt one_ne_zero)
  -- The radial edges give the two circles; the angular seam edges cancel.
  have hseam : (∫ r in a..b, polarPullback ω z₀ (r, π) (fun _ ↦ (1, 0))) =
      ∫ r in a..b, polarPullback ω z₀ (r, -π) (fun _ ↦ (1, 0)) := by
    refine intervalIntegral.integral_congr fun r _ ↦ ?_
    simp [polarPullback_apply_radial, circleMap, Complex.exp_mul_I]
  simp only [polarPullback_apply_angular] at hgreen
  rw [harea, hseam, sub_self, sub_zero] at hgreen
  exact hgreen

/-- Stokes' formula on a closed disc. The tangent vector in the boundary integral is the
derivative of the counterclockwise circle parametrization. -/
theorem integral_extDeriv_closedBall
    {ω : ℂ → ℂ [⋀^Fin 1]→L[ℝ] F} {z₀ : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hω : ∀ z ∈ Metric.closedBall z₀ r, ContDiffAt ℝ 1 ω z) :
    (∫ z in Metric.closedBall z₀ r, extDeriv ω z ![1, I]) =
      ∫ θ in -π..π, ω (circleMap z₀ r θ) (fun _ ↦ circleMap 0 r θ * I) := by
  have hset : {z : ℂ | 0 ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ r} = Metric.closedBall z₀ r := by
    ext z
    simp [Metric.mem_closedBall, dist_eq_norm]
  have h := integral_extDeriv_annulus z₀ le_rfl hr (hset.symm ▸ hω)
  rw [hset] at h
  have hz : (fun θ : ℝ ↦ ω (circleMap z₀ 0 θ)
      (fun _ ↦ circleMap 0 0 θ * I)) = fun _ ↦ (0 : F) := by
    funext θ
    simp only [circleMap_zero_radius, Function.const_apply, zero_mul]
    exact (ω z₀).map_coord_zero 0 rfl
  rw [hz, intervalIntegral.integral_zero, sub_zero] at h
  exact h

/-- Stokes' formula on an open disc, for a one-form which is `C¹` inside the disc and only
continuous up to its boundary circle, with integrable exterior derivative. -/
theorem integral_extDeriv_ball
    {ω : ℂ → ℂ [⋀^Fin 1]→L[ℝ] F} {z₀ : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hω : ∀ z ∈ Metric.ball z₀ r, ContDiffAt ℝ 1 ω z)
    (hωc : ContinuousOn ω (Metric.closedBall z₀ r))
    (hint : IntegrableOn (fun z ↦ extDeriv ω z ![1, I]) (Metric.ball z₀ r)) :
    (∫ z in Metric.ball z₀ r, extDeriv ω z ![1, I]) =
      ∫ θ in -π..π, ω (circleMap z₀ r θ) (fun _ ↦ circleMap 0 r θ * I) := by
  rcases hr.eq_or_lt with rfl | hr
  · have h0 : (ω z₀ fun _ ↦ 0) = 0 := (ω z₀).map_coord_zero 0 rfl
    simp [h0]
  -- Stokes' formula holds on the smaller closed discs, which lie inside the open disc.
  have hsmall : ∀ s ∈ Ioo 0 r, (∫ z in Metric.ball z₀ s, extDeriv ω z ![1, I]) =
      ∫ θ in -π..π, ω (circleMap z₀ s θ) (fun _ ↦ circleMap 0 s θ * I) := fun s hs ↦ by
    rw [setIntegral_congr_set (volume.addHaar_closedBall_ae_eq_ball z₀ s).symm]
    exact integral_extDeriv_closedBall hs.1.le fun z hz ↦
      hω z (Metric.closedBall_subset_ball hs.2 hz)
  -- The boundary integrals depend continuously on the radius, up to the boundary circle.
  have hcont : ContinuousOn
      (fun s ↦ ∫ θ in -π..π, ω (circleMap z₀ s θ) (fun _ ↦ circleMap 0 s θ * I)) (Icc 0 r) :=
    continuousOn_parametric_intervalIntegral_of_continuousOn <|
      (hωc.comp (continuous_circleMap_uncurry z₀).continuousOn
        fun (p : ℝ × ℝ) (hp : p ∈ Icc 0 r ×ˢ uIcc (-π) π) ↦
        Metric.closedBall_subset_closedBall hp.1.2
        (circleMap_mem_closedBall z₀ hp.1.1 p.2)).eval
        (continuous_pi fun _ ↦ (continuous_circleMap_uncurry 0).mul continuous_const).continuousOn
  exact tendsto_nhds_unique_of_eventuallyEq hint.tendsto_integral_ball_nhdsLT
    ((hcont r ⟨hr.le, le_rfl⟩).tendsto.mono_left
      (nhdsWithin_le_of_mem (Filter.mem_of_superset (Ioo_mem_nhdsLT hr) Ioo_subset_Icc_self)))
    (by filter_upwards [Ioo_mem_nhdsLT hr] with s hs using hsmall s hs)

/-- **Stokes' formula on a closed upper half-annulus.** Let `S` be the closed upper half
`{z | z₀.im ≤ z.im}` of the annulus of radii `0 ≤ a ≤ b` about `z₀`. If a one-form `ω` is continuous
on `S` and differentiable at its interior points, where its exterior derivative on `(1, I)` agrees
with a function `dω` continuous on `S`, then the integral of `dω` over `S` is the integral of `ω`
over the positively oriented boundary of `S`: the outer half-circle minus the inner half-circle,
both traversed from the angle `0` to `π`, plus the two segments of the diameter, both traversed
towards increasing real part. -/
theorem integral_upperHalfAnnulus_eq_of_extDeriv_eq {ω : ℂ → ℂ [⋀^Fin 1]→L[ℝ] F} {dω : ℂ → F}
    (z₀ : ℂ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hω : ContinuousOn ω {z | z₀.im ≤ z.im ∧ a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b})
    (hdω : ContinuousOn dω {z | z₀.im ≤ z.im ∧ a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b})
    (hd : ∀ z, z₀.im < z.im → a < ‖z - z₀‖ → ‖z - z₀‖ < b →
      DifferentiableAt ℝ ω z ∧ extDeriv ω z ![1, I] = dω z) :
    ∫ z in {z | z₀.im ≤ z.im ∧ a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, dω z =
      (∫ θ in 0..π, ω (circleMap z₀ b θ) (fun _ ↦ circleMap 0 b θ * I)) -
        (∫ θ in 0..π, ω (circleMap z₀ a θ) (fun _ ↦ circleMap 0 a θ * I)) +
        (∫ r in a..b, ω (z₀ + r) (fun _ ↦ 1)) + ∫ r in a..b, ω (z₀ - r) (fun _ ↦ 1) := by
  set S : Set ℂ := {z | z₀.im ≤ z.im ∧ a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}
  set P : ℝ × ℝ → ℂ := fun p ↦ z₀ + Complex.polarCoord.symm p
  set U : Set (ℝ × ℝ) := Ioo a b ×ˢ Ioo 0 π
  have hP : ContDiff ℝ 2 P := contDiff_add_polarCoord_symm z₀
  have hmem (p : ℝ × ℝ) (hp : p ∈ Icc (a, 0) (b, π)) : P p ∈ S :=
    add_polarCoord_symm_mem_upperHalfAnnulus z₀ ha hp
  have hmemU (p : ℝ × ℝ) (hp : p ∈ U) := add_polarCoord_symm_mem_openUpperHalfAnnulus z₀ ha hp
  have hCLM := ContinuousAlternatingMap.contDiff_compContinuousLinearMapCLM
    (𝕜 := ℝ) (E := ℝ × ℝ) (F := ℂ) (G := F) (ι := Fin 1) 1 (by simp)
  have hηc : ContinuousOn (polarPullback ω z₀) (Icc (a, 0) (b, π)) :=
    ((hCLM.continuous.comp (hP.continuous_fderiv (by norm_num))).continuousOn).clm_apply
      (hω.comp hP.continuous.continuousOn hmem)
  have hηd (p : ℝ × ℝ) (hp : p ∈ U) : DifferentiableAt ℝ (polarPullback ω z₀) p ∧
      extDeriv (polarPullback ω z₀) p ![(1, 0), (0, 1)] = p.1 • dω (P p) := by
    obtain ⟨h₁, h₂, h₃⟩ := hmemU p hp
    have hdP' : DifferentiableAt ℝ (fderiv ℝ P) p :=
      ((hP.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero).differentiableAt
    refine ⟨((hCLM.differentiable one_ne_zero).differentiableAt.comp p hdP').clm_apply
      ((hd _ h₁ h₂ h₃).1.comp p (hP.differentiable (by norm_num)).differentiableAt), ?_⟩
    rw [← (hd _ h₁ h₂ h₃).2]
    exact extDeriv_pullback_polarCoord_symm_apply z₀ p (hd _ h₁ h₂ h₃).1
  have hcont : ContinuousOn (fun p : ℝ × ℝ ↦ p.1 • dω (P p)) (Icc (a, 0) (b, π)) :=
    continuous_fst.continuousOn.smul (hdω.comp hP.continuous.continuousOn hmem)
  have hgreen := integral_prod_Icc_eq_of_extDeriv_eq
    (a := (a, 0)) (b := (b, π)) ⟨hab, Real.pi_pos.le⟩ hηc hηd
    (hcont.integrableOn_compact isCompact_Icc)
  -- The interior integral is the integral of `dω` over the half-annulus.
  rw [Complex.integral_comp_polarCoord_symm_Icc_zero_pi _ z₀ ha] at hgreen
  -- The angular edges are the two half-circles, the radial edges the two segments.
  have hneg (z : ℂ) : ω z (fun _ ↦ (-1 : ℂ)) = -ω z (fun _ ↦ 1) := by
    simpa using (ω z).map_smul_univ (fun _ ↦ (-1 : ℝ)) (fun _ ↦ (1 : ℂ))
  have hbot : (∫ r in a..b, polarPullback ω z₀ (r, 0) (fun _ ↦ (1, 0))) =
      ∫ r in a..b, ω (z₀ + r) (fun _ ↦ 1) :=
    intervalIntegral.integral_congr fun r _ ↦ by simp [polarPullback_apply_radial, circleMap]
  have htop : (∫ r in a..b, polarPullback ω z₀ (r, π) (fun _ ↦ (1, 0))) =
      -∫ r in a..b, ω (z₀ - r) (fun _ ↦ 1) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun r _ ↦ ?_
    simp [polarPullback_apply_radial, circleMap, Complex.exp_mul_I, ← hneg, sub_eq_add_neg]
  simp only [polarPullback_apply_angular] at hgreen
  rw [hgreen, hbot, htop]
  abel

end TauCeti
