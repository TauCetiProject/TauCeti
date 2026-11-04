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
public import TauCeti.MeasureTheory.Integral.PolarCoord
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Stokes' formula for one-forms on rectangles and annuli

The integral of the exterior derivative of a vector-valued real one-form over a rectangle or
closed annulus is its positively oriented boundary integral. Zero inner radius gives the disc
formula. Only C¹ regularity near the region of integration is required; in the annular
case no regularity on the missing inner disc is needed. On a rectangle the formula is stated both
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
`extDeriv_pullback_polarCoord_symm_apply`. The bilinear Green formulas in
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
  let f := fun z ↦ ω z (fun _ ↦ (0, 1))
  let g := fun z ↦ -ω z (fun _ ↦ (1, 0))
  have hf z hz := ((hω z hz).differentiableAt one_ne_zero).hasFDerivAt
    |>.continuousAlternatingMap_apply_const (fun _ ↦ (0, 1))
  have hg z hz := (((hω z hz).differentiableAt one_ne_zero).hasFDerivAt
    |>.continuousAlternatingMap_apply_const (fun _ ↦ (1, 0))).neg
  have hcurl z (hz : z ∈ Icc a b) :
      fderiv ℝ f z (1, 0) + fderiv ℝ g z (0, 1) =
        extDeriv ω z ![(1, 0), (0, 1)] := by
    simp [f, g, extDeriv_apply_pair_of_differentiableAt
      ((hω z hz).differentiableAt one_ne_zero), sub_eq_add_neg]
  have hcont : ContinuousOn (fun z ↦ extDeriv ω z ![(1, 0), (0, 1)]) (Icc a b) :=
    fun z hz ↦ (continuousAt_extDeriv_apply (hω z hz) _).continuousWithinAt
  have hsub : Ioo a.1 b.1 ×ˢ Ioo a.2 b.2 ⊆ Icc a b := by
    rw [Icc_prod_eq]
    exact prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  have h := integral_divergence_prod_Icc_of_hasFDerivAt_of_le f g
    (fderiv ℝ f) (fderiv ℝ g) a b hab
    (fun z hz ↦ (hf z hz).continuousAt.continuousWithinAt)
    (fun z hz ↦ (hg z hz).continuousAt.continuousWithinAt)
    (fun z hz ↦ (hf z (hsub hz)).differentiableAt.hasFDerivAt)
    (fun z hz ↦ (hg z (hsub hz)).differentiableAt.hasFDerivAt)
    ((hcont.integrableOn_compact isCompact_Icc).congr_fun
      (fun z hz ↦ (hcurl z hz).symm) measurableSet_Icc)
  rw [setIntegral_congr_fun measurableSet_Icc hcurl] at h
  simp only [f, g, intervalIntegral.integral_neg] at h
  rw [h]
  abel

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
theorem integral2_slice_sub_eq_sides [CompleteSpace F]
    {ψ : (ℝ × ℝ) × ℝ → ((ℝ × ℝ) × ℝ) [⋀^Fin 2]→L[ℝ] F} (hψ : ContDiff ℝ 1 ψ)
    (hdψ : extDeriv ψ = 0) (a b : ℝ × ℝ) :
    ((∫ s in a.1..b.1, ∫ t in a.2..b.2, ψ ((s, t), 1) ![((1, 0), 0), ((0, 1), 0)]) -
        ∫ s in a.1..b.1, ∫ t in a.2..b.2, ψ ((s, t), 0) ![((1, 0), 0), ((0, 1), 0)]) =
      ((∫ t in a.2..b.2, ∫ c in (0 : ℝ)..1, ψ ((a.1, t), c) ![((0, 1), 0), (0, 1)]) -
          ∫ t in a.2..b.2, ∫ c in (0 : ℝ)..1, ψ ((b.1, t), c) ![((0, 1), 0), (0, 1)]) -
        ((∫ s in a.1..b.1, ∫ c in (0 : ℝ)..1, ψ ((s, a.2), c) ![((1, 0), 0), (0, 1)]) -
          ∫ s in a.1..b.1, ∫ c in (0 : ℝ)..1, ψ ((s, b.2), c) ![((1, 0), 0), (0, 1)]) := by
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
  let P : ℝ × ℝ → ℂ := fun p ↦ z₀ + Complex.polarCoord.symm p
  let η := fun p ↦ (ω (P p)).compContinuousLinearMap (fderiv ℝ P p)
  have hP : ContDiff ℝ 2 P := contDiff_add_polarCoord_symm z₀
  have hmem (p : ℝ × ℝ) (hp : p ∈ Icc (a, -π) (b, π)) :
      P p ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b} :=
    add_polarCoord_symm_mem_annulus z₀ ha ⟨hp.1.1, hp.2.1⟩
  have hη p (hp : p ∈ Icc (a, -π) (b, π)) : ContDiffAt ℝ 1 η p :=
    hP.contDiffAt.differentialForm_pullback (hω _ (hmem p hp))
  have hgreen := integral_extDeriv_prod_Icc
    (a := (a, -π)) (b := (b, π)) ⟨hab, by linarith [Real.pi_pos]⟩ hη
  have hd p : fderiv ℝ P p =
      Complex.equivRealProdCLM.symm.toContinuousLinearMap.comp (fderivPolarCoordSymm p) :=
    (hasFDerivAt_add_polarCoord_symm p z₀).fderiv
  have hdr p : fderiv ℝ P p (1, 0) = exp (p.2 * I) := by
    simp only [hd, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      equivRealProd_symm_fderivPolarCoordSymm_apply_one_zero]
  have hdt p : fderiv ℝ P p (0, 1) = circleMap 0 p.1 p.2 * I := by
    simp only [hd, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      equivRealProd_symm_fderivPolarCoordSymm_apply_zero_one]
  -- Naturality and the polar Jacobian convert the interior integral back to the annulus.
  have harea : (∫ p in Icc (a, -π) (b, π), extDeriv η p ![(1, 0), (0, 1)]) =
      ∫ z in {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, extDeriv ω z ![1, I] := by
    rw [← Complex.integral_comp_polarCoord_symm_Icc _ z₀ ha]
    exact setIntegral_congr_fun measurableSet_Icc fun p hp ↦
      extDeriv_pullback_polarCoord_symm_apply z₀ p
        ((hω _ (hmem p hp)).differentiableAt one_ne_zero)
  -- The radial edges give the two circles; the angular seam edges cancel.
  have hPc (r θ : ℝ) : P (r, θ) = circleMap z₀ r θ :=
    add_polarCoord_symm_eq_circleMap z₀ (r, θ)
  have hcircle r : (∫ θ in -π..π, η (r, θ) (fun _ ↦ (0, 1))) =
      ∫ θ in -π..π, ω (circleMap z₀ r θ) (fun _ ↦ circleMap 0 r θ * I) := by
    simp [η, ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def,
      hdt, hPc]
  have hseam : (∫ r in a..b, η (r, π) (fun _ ↦ (1, 0))) =
      ∫ r in a..b, η (r, -π) (fun _ ↦ (1, 0)) := by
    apply intervalIntegral.integral_congr
    intro r _
    simp only [η, ContinuousAlternatingMap.compContinuousLinearMap_apply,
      Function.comp_def, hdr]
    simp [P, Complex.polarCoord_symm_apply, Complex.exp_mul_I]
  rw [harea, hcircle, hcircle, hseam, sub_self, sub_zero] at hgreen
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

end TauCeti
