/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.NormalModel.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.LineDeriv.IntegrationByParts
import TauCeti.Analysis.PDE.Vortex.Gauge.ComplexStructure
import TauCeti.Analysis.PDE.Vortex.SpectralGap
import TauCeti.Topology.Algebra.Support

/-!
# The energy identity of the normal model with base dependence

Near a pseudoholomorphic curve, Taubes's rescaled large-parameter Seiberg–Witten solutions are
modelled on `ℂ_base × ℂ_normal` by a plane vortex `x` in the normal factor, and the linearized
equations at such a model act on a *normal family* `Ξ` and a *paired family* `Η` of plane fields
over the base (`TauCeti.Analysis.PDE.SeibergWitten.NormalModel.Basic`). Writing `w = s + i t` for
the base coordinate and `D_w` for the derivative along the base, the operator is given by the two
rows

`N = L_x Ξ (w, ·) + normalBaseCoupling (D_w Η)`,  `P = L_x* Η (w, ·) + pairedBaseCoupling (D_w Ξ)`,

where `L_x` and `L_x*` (`TauCeti.Vortex.gaugeFixedOperator`, `TauCeti.Vortex.gaugeFixedAdjoint`)
act on the normal slices, and the couplings are `D 1 - J' (D i)` and `D 1 + J (D i)` for the
complex structures `J'` on the target and `J` on variations of `L_x`
(`TauCeti.Vortex.targetComplexStructure`, `TauCeti.Vortex.variationComplexStructure`). This file
proves that the base dependence contributes exactly the energy of the families along the base: for
compactly supported `C²` families and a continuous field `x`,

`∫ (|N|² + |P|²) = ∫ (|L_x Ξ|² + |L_x* Η|² + |∂_s Ξ|² + |∂_t Ξ|² + |∂_s Η|² + |∂_t Η|²)`

(`TauCeti.SeibergWitten.integral_norm_sq_add_norm_sq_familyNormalModel`), for any additive Haar
measures on the two factors. After a Fourier transform along the base, at base frequency `ξ` the
right side is `|L_x Ξ̂|² + |L_x* Η̂|² + |ξ|² (|Ξ̂|² + |Η̂|²)`.

Expanding the squares leaves three kinds of cross terms, each of which integrates to zero.

* `⟪L_x Ξ, ∂_s Η⟫ + ⟪L_x* Η, ∂_s Ξ⟫`. The coefficients of `L_x` do not depend on the base, so
  `L_x` commutes with the derivatives along the base, by the symmetry of second derivatives; this
  needs no regularity of `x` beyond continuity, since only line derivatives along the base are
  taken. Integrating by parts along the base and then, by Fubini, along each normal slice
  (`TauCeti.Vortex.integral_inner_gaugeFixedOperator`) turns the first pairing into minus the
  second.
* `-⟪L_x Ξ, J' ∂_t Η⟫ + ⟪L_x* Η, J ∂_t Ξ⟫`. The operator is complex linear,
  `L_x (J y) = J' (L_x y)` (`TauCeti.Vortex.gaugeFixedOperator_variationComplexStructure`), and
  `J'` is skew, so this is the previous cross term along `t` for the family `J Ξ`.
* `-⟪∂_s Η, J' ∂_t Η⟫` and `⟪∂_s Ξ, J ∂_t Ξ⟫`. Since `J'` and `J` are skew, these are alternating
  forms evaluated on two derivatives of a compactly supported map, which integrate to zero
  (`TauCeti.integral_bilinForm_fderiv_apply_eq_zero_of_isAlt`).

Consequently the energy of the families along the base is bounded by `∫ (|N|² + |P|²)`
(`integral_norm_sq_fderiv_le_integral_norm_sq_add_norm_sq_familyNormalModel`), and a lower
bound `c ∫ |η|² ≤ ∫ |L_x* η|²` on the normal plane gives
`c ∫ |Η|² ≤ ∫ (|N|² + |P|²)` for the paired family
(`mul_integral_norm_sq_le_integral_norm_sq_add_norm_sq_familyNormalModel`). At a plane vortex
with `|α| → 1` the spectral gap of `L_x L_x*` supplies such a bound
(`exists_pos_mul_integral_norm_sq_le_integral_norm_sq_add_norm_sq_familyNormalModel`).
The normal family is not controlled in this way: at a vortex of degree `m ≥ 1`, `L_x` has a
kernel of dimension `2m`.

## Main results

All in the namespace `TauCeti.SeibergWitten`:

* `integral_norm_sq_add_norm_sq_familyNormalModel`: the energy identity.
* `integral_norm_sq_fderiv_le_integral_norm_sq_add_norm_sq_familyNormalModel`: the bound on the
  energy along the base.
* `mul_integral_norm_sq_le_integral_norm_sq_add_norm_sq_familyNormalModel` and
  `exists_pos_mul_integral_norm_sq_le_integral_norm_sq_add_norm_sq_familyNormalModel`: coercivity
  of the paired family.

## References

* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

namespace TauCeti.SeibergWitten

open Filter MeasureTheory Complex
open scoped Topology
open scoped RealInnerProductSpace InnerProductSpace

/-! ### The base couplings through the complex structures -/

section Twist

private theorem normalBaseCoupling_eq (D : ℂ →L[ℝ] EuclideanSpace ℝ (Fin 4)) :
    normalBaseCoupling D = D 1 + Vortex.targetComplexStructure.symm (D I) := by
  ext i
  fin_cases i <;> simp <;> ring

private theorem pairedBaseCoupling_eq (D : ℂ →L[ℝ] EuclideanSpace ℝ (Fin 4)) :
    pairedBaseCoupling D = D 1 + Vortex.variationComplexStructure (D I) := by
  ext i
  fin_cases i <;> simp <;> ring

end Twist

/-! ### Slices of families of plane fields -/

section Slice

variable {Φ : ℂ × ℂ → EuclideanSpace ℝ (Fin 4)} {p : ℂ × ℂ}

/-- A coordinate of the derivative of a normal slice is read off the derivative of the family. -/
private theorem fderiv_slice_snd_apply_coord (hΦ : DifferentiableAt ℝ Φ p) (u : ℂ) (i : Fin 4) :
    fderiv ℝ (fun z ↦ Φ (p.1, z) i) p.2 u = fderiv ℝ Φ p (0, u) i := by
  have h := (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp p.2 hΦ.hasFDerivAt_slice_snd
  rw [show (fun z ↦ Φ (p.1, z) i) = EuclideanSpace.proj (𝕜 := ℝ) i ∘ fun z ↦ Φ (p.1, z) from rfl,
    h.fderiv]
  simp

/-- The derivative of a base slice is read off the derivative of the family. -/
private theorem fderiv_slice_fst_apply (hΦ : DifferentiableAt ℝ Φ p) (v : ℂ) :
    fderiv ℝ (fun w ↦ Φ (w, p.2)) p.1 v = fderiv ℝ Φ p (v, 0) := by
  rw [hΦ.hasFDerivAt_slice_fst.fderiv]
  simp

/-- The gradients of the four coordinates of the normal slice, as a linear function of the
derivative `D` of a family at a point: the gradient of the coordinate `j` is dual to
`u ↦ D (0, u) j`. -/
private def sliceGradients : (ℂ × ℂ →L[ℝ] EuclideanSpace ℝ (Fin 4)) →L[ℝ] (Fin 4 → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun D j := (InnerProductSpace.toDual ℝ ℂ).symm
        ((EuclideanSpace.proj j).comp (D.comp (ContinuousLinearMap.inr ℝ ℂ ℂ)))
      map_add' D D' := by
        funext j; simp [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
      map_smul' c D := by
        funext j; simp [ContinuousLinearMap.smul_comp] }

/-- The gauge-fixed operator on the normal slices, as a linear function of the first jet `(D, c)`
of a family at a point, for the field value `a`: the first-order part
`TauCeti.Vortex.gaugeFixedFirstOrder` on the gradients of the slice coordinates plus the
zeroth-order part `TauCeti.Vortex.gaugeFixedZerothOrder a c`. -/
private def jetOperator (a : EuclideanSpace ℝ (Fin 4)) :
    ((ℂ × ℂ →L[ℝ] EuclideanSpace ℝ (Fin 4)) × EuclideanSpace ℝ (Fin 4)) →L[ℝ]
      EuclideanSpace ℝ (Fin 4) :=
  Vortex.gaugeFixedFirstOrder ∘L sliceGradients ∘L ContinuousLinearMap.fst ℝ _ _ +
    Vortex.gaugeFixedZerothOrder a ∘L ContinuousLinearMap.snd ℝ _ _

/-- The adjoint `L_x*` on the normal slices, as a linear function of the first jet. -/
private def jetAdjoint (a : EuclideanSpace ℝ (Fin 4)) :
    ((ℂ × ℂ →L[ℝ] EuclideanSpace ℝ (Fin 4)) × EuclideanSpace ℝ (Fin 4)) →L[ℝ]
      EuclideanSpace ℝ (Fin 4) :=
  LinearMap.toContinuousLinearMap
    { toFun q := !₂[-q.1 (0, 1) 0 - q.1 (0, I) 1 + a 2 * q.2 3 - a 3 * q.2 2,
        -q.1 (0, I) 0 + q.1 (0, 1) 1 - a 2 * q.2 2 - a 3 * q.2 3,
        -q.1 (0, 1) 2 - q.1 (0, I) 3 - a 1 * q.2 2 + a 0 * q.2 3 - a 3 * q.2 0 + a 2 * q.2 1,
        -q.1 (0, 1) 3 + q.1 (0, I) 2 - a 0 * q.2 2 - a 1 * q.2 3 + a 2 * q.2 0 + a 3 * q.2 1]
      map_add' q r := by ext i; fin_cases i <;> simp <;> ring
      map_smul' c q := by ext i; fin_cases i <;> simp <;> ring }

private theorem sliceGradients_apply (D : ℂ × ℂ →L[ℝ] EuclideanSpace ℝ (Fin 4)) (j : Fin 4) :
    sliceGradients D j = (InnerProductSpace.toDual ℝ ℂ).symm
      ((EuclideanSpace.proj j).comp (D.comp (ContinuousLinearMap.inr ℝ ℂ ℂ))) :=
  (rfl)

private theorem jetOperator_apply (a : EuclideanSpace ℝ (Fin 4))
    (q : (ℂ × ℂ →L[ℝ] EuclideanSpace ℝ (Fin 4)) × EuclideanSpace ℝ (Fin 4)) :
    jetOperator a q =
      Vortex.gaugeFixedFirstOrder (sliceGradients q.1) + Vortex.gaugeFixedZerothOrder a q.2 :=
  (rfl)

private theorem jetAdjoint_apply (a : EuclideanSpace ℝ (Fin 4))
    (q : (ℂ × ℂ →L[ℝ] EuclideanSpace ℝ (Fin 4)) × EuclideanSpace ℝ (Fin 4)) :
    jetAdjoint a q = !₂[-q.1 (0, 1) 0 - q.1 (0, I) 1 + a 2 * q.2 3 - a 3 * q.2 2,
        -q.1 (0, I) 0 + q.1 (0, 1) 1 - a 2 * q.2 2 - a 3 * q.2 3,
        -q.1 (0, 1) 2 - q.1 (0, I) 3 - a 1 * q.2 2 + a 0 * q.2 3 - a 3 * q.2 0 + a 2 * q.2 1,
        -q.1 (0, 1) 3 + q.1 (0, I) 2 - a 0 * q.2 2 - a 1 * q.2 3 + a 2 * q.2 0 + a 3 * q.2 1] :=
  (rfl)

variable (x : ℂ → EuclideanSpace ℝ (Fin 4))

/-- On the normal slice through a point, `L_x` is the jet operator of the family there. -/
private theorem gaugeFixedOperator_slice_eq_jetOperator (hΦ : DifferentiableAt ℝ Φ p) :
    Vortex.gaugeFixedOperator x (fun z ↦ Φ (p.1, z)) p.2 =
      jetOperator (x p.2) (fderiv ℝ Φ p, Φ p) := by
  rw [Vortex.gaugeFixedOperator_eq_gaugeFixedFirstOrder_add, jetOperator_apply]
  congr 2
  funext j
  rw [gradient, sliceGradients_apply]
  congr 1
  ext u
  simpa using fderiv_slice_snd_apply_coord hΦ u j

/-- On the normal slice through a point, `L_x*` is the jet adjoint of the family there. -/
private theorem gaugeFixedAdjoint_slice_eq_jetAdjoint (hΦ : DifferentiableAt ℝ Φ p) :
    Vortex.gaugeFixedAdjoint x (fun z ↦ Φ (p.1, z)) p.2 =
      jetAdjoint (x p.2) (fderiv ℝ Φ p, Φ p) := by
  ext i
  fin_cases i <;> simp [jetAdjoint_apply, fderiv_slice_snd_apply_coord hΦ]

variable {x}

/-- The jet adjoint is jointly continuous in the field value and the jet. -/
private theorem continuous_jetAdjoint :
    Continuous fun r : EuclideanSpace ℝ (Fin 4) ×
        ((ℂ × ℂ →L[ℝ] EuclideanSpace ℝ (Fin 4)) × EuclideanSpace ℝ (Fin 4)) ↦
      jetAdjoint r.1 r.2 := by
  simp only [jetAdjoint_apply]
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i ↦ by
    fin_cases i <;>
      simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.mk_one,
        Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;>
      fun_prop)

/-- `L_x` on the normal slices of a `C¹` family is jointly continuous. -/
private theorem continuous_gaugeFixedOperator_slice (hx : Continuous x) (hΦ : ContDiff ℝ 1 Φ) :
    Continuous fun p : ℂ × ℂ ↦ Vortex.gaugeFixedOperator x (fun z ↦ Φ (p.1, z)) p.2 := by
  have h : (fun p : ℂ × ℂ ↦ Vortex.gaugeFixedOperator x (fun z ↦ Φ (p.1, z)) p.2) =
      fun p ↦ jetOperator (x p.2) (fderiv ℝ Φ p, Φ p) :=
    funext fun p ↦ gaugeFixedOperator_slice_eq_jetOperator x (hΦ.differentiable one_ne_zero p)
  have hc := hΦ.continuous
  simp only [h, jetOperator_apply]
  fun_prop

/-- `L_x*` on the normal slices of a `C¹` family is jointly continuous. -/
private theorem continuous_gaugeFixedAdjoint_slice (hx : Continuous x) (hΦ : ContDiff ℝ 1 Φ) :
    Continuous fun p : ℂ × ℂ ↦ Vortex.gaugeFixedAdjoint x (fun z ↦ Φ (p.1, z)) p.2 := by
  have h : (fun p : ℂ × ℂ ↦ Vortex.gaugeFixedAdjoint x (fun z ↦ Φ (p.1, z)) p.2) =
      fun p ↦ jetAdjoint (x p.2) (fderiv ℝ Φ p, Φ p) :=
    funext fun p ↦ gaugeFixedAdjoint_slice_eq_jetAdjoint x (hΦ.differentiable one_ne_zero p)
  rw [h]
  exact continuous_jetAdjoint.comp ((hx.comp continuous_snd).prodMk
    ((hΦ.continuous_fderiv one_ne_zero).prodMk hΦ.continuous))

/-- `L_x` on the normal slices vanishes off the support of a differentiable family. -/
private theorem gaugeFixedOperator_slice_eq_zero (hΦ : Differentiable ℝ Φ) (hp : p ∉ tsupport Φ) :
    Vortex.gaugeFixedOperator x (fun z ↦ Φ (p.1, z)) p.2 = 0 := by
  rw [gaugeFixedOperator_slice_eq_jetOperator x (hΦ p), fderiv_of_notMem_tsupport ℝ hp,
    image_eq_zero_of_notMem_tsupport hp, Prod.mk_zero_zero, map_zero]

/-- `L_x*` on the normal slices vanishes off the support of a differentiable family. -/
private theorem gaugeFixedAdjoint_slice_eq_zero (hΦ : Differentiable ℝ Φ) (hp : p ∉ tsupport Φ) :
    Vortex.gaugeFixedAdjoint x (fun z ↦ Φ (p.1, z)) p.2 = 0 := by
  rw [gaugeFixedAdjoint_slice_eq_jetAdjoint x (hΦ p), fderiv_of_notMem_tsupport ℝ hp,
    image_eq_zero_of_notMem_tsupport hp, Prod.mk_zero_zero, map_zero]

/-- **`L_x` commutes with derivatives along the base.** For a `C²` family `Φ` and a base direction
`v`, the line derivative along `(v, 0)` of `L_x` applied to the normal slices of `Φ` is `L_x`
applied to the normal slices of the base derivative `∂_v Φ`. -/
private theorem hasLineDerivAt_gaugeFixedOperator_slice (hΦ : ContDiff ℝ 2 Φ) (p : ℂ × ℂ)
    (v : ℂ) :
    HasLineDerivAt ℝ (fun q : ℂ × ℂ ↦ Vortex.gaugeFixedOperator x (fun z ↦ Φ (q.1, z)) q.2)
      (Vortex.gaugeFixedOperator x (fun z ↦ fderiv ℝ Φ (p.1, z) (v, 0)) p.2) p (v, 0) := by
  set a : ℂ × ℂ := (v, 0)
  have hd : Differentiable ℝ Φ := hΦ.differentiable (by norm_num)
  have hD : Differentiable ℝ (fderiv ℝ Φ) := (hΦ.fderiv_right (m := 1) (by norm_num)).differentiable
    one_ne_zero
  -- Along the line `t ↦ p + t a` the normal coordinate is constant.
  have hline (t : ℝ) : (p + t • a).2 = p.2 := by simp [a]
  have hℓ : HasDerivAt (fun t : ℝ ↦ p + t • a) a 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const a).const_add p
  have h₁ : HasDerivAt (fun t : ℝ ↦ fderiv ℝ Φ (p + t • a)) (fderiv ℝ (fderiv ℝ Φ) p a) 0 :=
    (hD p).hasFDerivAt.comp_hasDerivAt_of_eq 0 hℓ (by simp)
  have h₂ : HasDerivAt (fun t : ℝ ↦ Φ (p + t • a)) (fderiv ℝ Φ p a) 0 :=
    (hd p).hasFDerivAt.comp_hasDerivAt_of_eq 0 hℓ (by simp)
  have h₃ := (jetOperator (x p.2)).hasFDerivAt.comp_hasDerivAt 0 (HasDerivAt.prodMk h₁ h₂)
  -- The base derivative of the first jet is the first jet of the base derivative, by the symmetry
  -- of the second derivative.
  have hsymm : fderiv ℝ (fun q ↦ fderiv ℝ Φ q a) p = fderiv ℝ (fderiv ℝ Φ) p a := by
    refine ContinuousLinearMap.ext fun b ↦ ?_
    rw [fderiv_clm_apply (hD p) (differentiableAt_const _)]
    simpa using (hΦ.contDiffAt.isSymmSndFDerivAt (by simp)) b a
  have hΨ : DifferentiableAt ℝ (fun q ↦ fderiv ℝ Φ q a) p :=
    (hD p).clm_apply (differentiableAt_const _)
  rw [HasLineDerivAt, gaugeFixedOperator_slice_eq_jetOperator (Φ := fun q ↦ fderiv ℝ Φ q a) x hΨ,
    hsymm]
  convert h₃ using 1
  funext t
  rw [Function.comp_apply, ← hline t, gaugeFixedOperator_slice_eq_jetOperator x (hd _)]

end Slice

/-! ### The cross terms -/

section Cross

variable {μ ν : Measure ℂ} [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
  {x : ℂ → EuclideanSpace ℝ (Fin 4)} {Ξ Η : ℂ × ℂ → EuclideanSpace ℝ (Fin 4)}

/-- **Integration by parts along the base.** For a `C²` family `Ξ`, a compactly supported `C¹`
family `Η` and a base direction `v`, `∫ ⟪L_x Ξ, ∂_v Η⟫ = -∫ ⟪L_x (∂_v Ξ), Η⟫`. -/
private theorem integral_inner_gaugeFixedOperator_slice_fderiv_apply (hx : Continuous x)
    (hΞ : ContDiff ℝ 2 Ξ) (hΗ : ContDiff ℝ 1 Η) (hΗc : HasCompactSupport Η) (v : ℂ) :
    ∫ p, ⟪Vortex.gaugeFixedOperator x (fun z ↦ Ξ (p.1, z)) p.2, fderiv ℝ Η p (v, 0)⟫ ∂μ.prod ν =
      -∫ p, ⟪Vortex.gaugeFixedOperator x (fun z ↦ fderiv ℝ Ξ (p.1, z) (v, 0)) p.2, Η p⟫
        ∂μ.prod ν := by
  have hΨ : ContDiff ℝ 1 fun q ↦ fderiv ℝ Ξ q (v, 0) :=
    (hΞ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hLΞ := continuous_gaugeFixedOperator_slice hx (hΞ.of_le (by norm_num))
  have hLΨ := continuous_gaugeFixedOperator_slice hx hΨ
  have hc := hΗ.continuous
  exact integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable (B := innerSL ℝ)
    (Continuous.integrable_of_hasCompactSupport (by fun_prop) <|
      HasCompactSupport.intro hΗc.isCompact fun q hq ↦ by
        simp [image_eq_zero_of_notMem_tsupport hq])
    (Continuous.integrable_of_hasCompactSupport (by fun_prop) <|
      HasCompactSupport.intro hΗc.isCompact fun q hq ↦ by
        simp [fderiv_of_notMem_tsupport ℝ hq])
    (Continuous.integrable_of_hasCompactSupport (by fun_prop) <|
      HasCompactSupport.intro hΗc.isCompact fun q hq ↦ by
        simp [image_eq_zero_of_notMem_tsupport hq])
    (fun q _ ↦ hasLineDerivAt_gaugeFixedOperator_slice hΞ q v)
    (fun q _ ↦ ((hΗ.differentiable one_ne_zero) q).hasFDerivAt.hasLineDerivAt (v, 0))

/-- **Integration by parts along the normal slices.** For a `C¹` family `Ψ` and a compactly
supported `C¹` family `Η`, `∫ ⟪L_x Ψ, Η⟫ = ∫ ⟪Ψ, L_x* Η⟫` over `ℂ × ℂ`, by Fubini and the
integration by parts `TauCeti.Vortex.integral_inner_gaugeFixedOperator` on each normal slice. -/
private theorem integral_inner_gaugeFixedOperator_slice (hx : Continuous x)
    {Ψ : ℂ × ℂ → EuclideanSpace ℝ (Fin 4)} (hΨ : ContDiff ℝ 1 Ψ) (hΗ : ContDiff ℝ 1 Η)
    (hΗc : HasCompactSupport Η) :
    ∫ p, ⟪Vortex.gaugeFixedOperator x (fun z ↦ Ψ (p.1, z)) p.2, Η p⟫ ∂μ.prod ν =
      ∫ p, ⟪Ψ p, Vortex.gaugeFixedAdjoint x (fun z ↦ Η (p.1, z)) p.2⟫ ∂μ.prod ν := by
  have hLΨ := continuous_gaugeFixedOperator_slice hx hΨ
  have hAΗ := continuous_gaugeFixedAdjoint_slice hx hΗ
  have hc := hΗ.continuous
  have hcΨ := hΨ.continuous
  rw [integral_prod _ (Continuous.integrable_of_hasCompactSupport (by fun_prop) <|
      HasCompactSupport.intro hΗc.isCompact fun q hq ↦ by
        simp [image_eq_zero_of_notMem_tsupport hq]),
    integral_prod _ (Continuous.integrable_of_hasCompactSupport (by fun_prop) <|
      HasCompactSupport.intro hΗc.isCompact fun q hq ↦ by
        simp [gaugeFixedAdjoint_slice_eq_zero (x := x) (hΗ.differentiable one_ne_zero) hq])]
  exact integral_congr_ae (.of_forall fun w ↦ Vortex.integral_inner_gaugeFixedOperator (μ := ν)
    (hΨ.comp (contDiff_const.prodMk contDiff_id)) (hΗ.comp (contDiff_const.prodMk contDiff_id))
    (Or.inr (HasCompactSupport.comp_of_forall_mem_imp_mem
      (hΗc.isCompact.image continuous_snd) (fun z hz ↦ ⟨_, hz, rfl⟩)
      fun _ hq ↦ image_eq_zero_of_notMem_tsupport hq)))

/-- **The cross term along a base direction.** For `C²` families `Ξ`, `Η`, with `Η` compactly
supported, and a base direction `v`, the pairing of `L_x Ξ` with `∂_v Η` and the pairing of
`L_x* Η` with `∂_v Ξ` integrate to opposite values. -/
private theorem integral_inner_gaugeFixedOperator_slice_add_inner_gaugeFixedAdjoint_slice
    (hx : Continuous x) (hΞ : ContDiff ℝ 2 Ξ) (hΗ : ContDiff ℝ 2 Η) (hΗc : HasCompactSupport Η)
    (v : ℂ) :
    ∫ p, (⟪Vortex.gaugeFixedOperator x (fun z ↦ Ξ (p.1, z)) p.2, fderiv ℝ Η p (v, 0)⟫ +
        ⟪Vortex.gaugeFixedAdjoint x (fun z ↦ Η (p.1, z)) p.2, fderiv ℝ Ξ p (v, 0)⟫) ∂μ.prod ν =
      0 := by
  have hΞ₁ : ContDiff ℝ 1 Ξ := hΞ.of_le (by norm_num)
  have hΗ₁ : ContDiff ℝ 1 Η := hΗ.of_le (by norm_num)
  have hΨ : ContDiff ℝ 1 fun q ↦ fderiv ℝ Ξ q (v, 0) :=
    (hΞ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hLΞ := continuous_gaugeFixedOperator_slice hx hΞ₁
  have hAΗ := continuous_gaugeFixedAdjoint_slice hx hΗ₁
  rw [integral_add
      (Continuous.integrable_of_hasCompactSupport (by fun_prop) <|
        HasCompactSupport.intro hΗc.isCompact fun q hq ↦ by
          simp [fderiv_of_notMem_tsupport ℝ hq])
      (Continuous.integrable_of_hasCompactSupport (by fun_prop) <|
        HasCompactSupport.intro hΗc.isCompact fun q hq ↦ by
          simp [gaugeFixedAdjoint_slice_eq_zero (x := x) (hΗ₁.differentiable one_ne_zero) hq]),
    integral_inner_gaugeFixedOperator_slice_fderiv_apply hx hΞ hΗ₁ hΗc v,
    integral_inner_gaugeFixedOperator_slice hx hΨ hΗ₁ hΗc, neg_add_eq_zero]
  exact integral_congr_ae (.of_forall fun p ↦ real_inner_comm _ _)

end Cross

/-! ### The energy identity -/

section Energy

variable {μ ν : Measure ℂ} [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
  {x : ℂ → EuclideanSpace ℝ (Fin 4)} {Ξ Η : ℂ × ℂ → EuclideanSpace ℝ (Fin 4)}

/-- The pairing `⟪u, J'⁻¹ w⟫` of `normalBaseCoupling` is alternating, as `J'` is skew. -/
private theorem isAlt_compl₂_targetComplexStructure_symm :
    ((innerₗ (EuclideanSpace ℝ (Fin 4))).compl₂
      Vortex.targetComplexStructure.symm.toLinearEquiv.toLinearMap).IsAlt :=
  fun u ↦ by
    have h := Vortex.inner_targetComplexStructure_left u u
    rw [real_inner_comm] at h
    simp only [LinearMap.compl₂_apply, innerₗ_apply_apply, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv, Vortex.targetComplexStructure_symm_apply,
      inner_neg_right]
    linarith

/-- The pairing `⟪u, J w⟫` of `pairedBaseCoupling` is alternating, as `J` is skew. -/
private theorem isAlt_compl₂_variationComplexStructure :
    ((innerₗ (EuclideanSpace ℝ (Fin 4))).compl₂
      Vortex.variationComplexStructure.toLinearEquiv.toLinearMap).IsAlt :=
  fun u ↦ by
    have h := Vortex.inner_variationComplexStructure_left u u
    rw [real_inner_comm] at h
    simp only [LinearMap.compl₂_apply, innerₗ_apply_apply, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv]
    linarith

/-- The right side of the energy identity is integrable. -/
private theorem integrable_energy_familyNormalModel (hx : Continuous x) (hΞ : ContDiff ℝ 1 Ξ)
    (hΗ : ContDiff ℝ 1 Η) (hΞc : HasCompactSupport Ξ) (hΗc : HasCompactSupport Η) :
    Integrable (fun p ↦ ‖Vortex.gaugeFixedOperator x (fun z ↦ Ξ (p.1, z)) p.2‖ ^ 2 +
      ‖Vortex.gaugeFixedAdjoint x (fun z ↦ Η (p.1, z)) p.2‖ ^ 2 +
      ‖fderiv ℝ (fun w ↦ Ξ (w, p.2)) p.1 1‖ ^ 2 + ‖fderiv ℝ (fun w ↦ Ξ (w, p.2)) p.1 I‖ ^ 2 +
      ‖fderiv ℝ (fun w ↦ Η (w, p.2)) p.1 1‖ ^ 2 + ‖fderiv ℝ (fun w ↦ Η (w, p.2)) p.1 I‖ ^ 2)
      (μ.prod ν) := by
  have hdΞ := hΞ.differentiable one_ne_zero
  have hdΗ := hΗ.differentiable one_ne_zero
  have hcLΞ := continuous_gaugeFixedOperator_slice hx hΞ
  have hcAΗ := continuous_gaugeFixedAdjoint_slice hx hΗ
  simp_rw [fun p ↦ fderiv_slice_fst_apply (hdΞ p), fun p ↦ fderiv_slice_fst_apply (hdΗ p)]
  refine Continuous.integrable_of_hasCompactSupport (by fun_prop) <|
    HasCompactSupport.intro (hΞc.isCompact.union hΗc.isCompact) fun p hp ↦ ?_
  have hpΞ : p ∉ tsupport Ξ := fun h ↦ hp (Or.inl h)
  have hpΗ : p ∉ tsupport Η := fun h ↦ hp (Or.inr h)
  simp [gaugeFixedOperator_slice_eq_zero hdΞ hpΞ, gaugeFixedAdjoint_slice_eq_zero hdΗ hpΗ,
    fderiv_of_notMem_tsupport ℝ hpΞ, fderiv_of_notMem_tsupport ℝ hpΗ]

/-- The pairing of `L_x Ξ` with `∂_v Η` plus that of `L_x* Η` with `∂_v Ξ` is integrable. -/
private theorem integrable_inner_gaugeFixedOperator_slice_add_inner_gaugeFixedAdjoint_slice
    (hx : Continuous x) (hΞ : ContDiff ℝ 1 Ξ) (hΗ : ContDiff ℝ 1 Η) (hΗc : HasCompactSupport Η)
    (v : ℂ) :
    Integrable (fun p ↦
      ⟪Vortex.gaugeFixedOperator x (fun z ↦ Ξ (p.1, z)) p.2, fderiv ℝ Η p (v, 0)⟫ +
        ⟪Vortex.gaugeFixedAdjoint x (fun z ↦ Η (p.1, z)) p.2, fderiv ℝ Ξ p (v, 0)⟫) (μ.prod ν) := by
  have hdΗ := hΗ.differentiable one_ne_zero
  have hcLΞ := continuous_gaugeFixedOperator_slice hx hΞ
  have hcAΗ := continuous_gaugeFixedAdjoint_slice hx hΗ
  exact Continuous.integrable_of_hasCompactSupport (by fun_prop) <|
    HasCompactSupport.intro hΗc.isCompact fun p hp ↦ by
      simp [fderiv_of_notMem_tsupport ℝ hp, gaugeFixedAdjoint_slice_eq_zero hdΗ hp]

/-- The pairing `⟪∂_s Φ, T (∂_t Φ)⟫` of two base derivatives of a compactly supported `C¹` family
is integrable. -/
private theorem integrable_inner_fderiv_apply {Φ : ℂ × ℂ → EuclideanSpace ℝ (Fin 4)}
    (hΦ : ContDiff ℝ 1 Φ) (hΦc : HasCompactSupport Φ)
    (T : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)) :
    Integrable (fun p ↦ ⟪fderiv ℝ Φ p (1, 0), T (fderiv ℝ Φ p (I, 0))⟫) (μ.prod ν) := by
  have hT := T.continuous
  exact Continuous.integrable_of_hasCompactSupport (by fun_prop) <|
    HasCompactSupport.intro hΦc.isCompact fun p hp ↦ by simp [fderiv_of_notMem_tsupport ℝ hp]

/-- **The pointwise expansion of the two rows of the normal model.** The squared rows are the
squared normal operators plus the energy along the base, up to twice four cross terms: the
pairings of `L_x Ξ` with `∂_s Η` and of `L_x* Η` with `∂_s Ξ`, the same along `t` for the family
`J Ξ`, and the pairings `⟪∂_s Η, J'⁻¹ ∂_t Η⟫`, `⟪∂_s Ξ, J ∂_t Ξ⟫`. -/
private theorem norm_sq_add_norm_sq_familyNormalModel_eq (hΞ : Differentiable ℝ Ξ)
    (hΗ : Differentiable ℝ Η) (p : ℂ × ℂ) :
    ‖Vortex.gaugeFixedOperator x (fun z ↦ Ξ (p.1, z)) p.2 +
          normalBaseCoupling (fderiv ℝ (fun w ↦ Η (w, p.2)) p.1)‖ ^ 2 +
        ‖Vortex.gaugeFixedAdjoint x (fun z ↦ Η (p.1, z)) p.2 +
          pairedBaseCoupling (fderiv ℝ (fun w ↦ Ξ (w, p.2)) p.1)‖ ^ 2 =
      (‖Vortex.gaugeFixedOperator x (fun z ↦ Ξ (p.1, z)) p.2‖ ^ 2 +
        ‖Vortex.gaugeFixedAdjoint x (fun z ↦ Η (p.1, z)) p.2‖ ^ 2 +
        ‖fderiv ℝ (fun w ↦ Ξ (w, p.2)) p.1 1‖ ^ 2 + ‖fderiv ℝ (fun w ↦ Ξ (w, p.2)) p.1 I‖ ^ 2 +
        ‖fderiv ℝ (fun w ↦ Η (w, p.2)) p.1 1‖ ^ 2 + ‖fderiv ℝ (fun w ↦ Η (w, p.2)) p.1 I‖ ^ 2) +
      2 * ((⟪Vortex.gaugeFixedOperator x (fun z ↦ Ξ (p.1, z)) p.2, fderiv ℝ Η p (1, 0)⟫ +
          ⟪Vortex.gaugeFixedAdjoint x (fun z ↦ Η (p.1, z)) p.2, fderiv ℝ Ξ p (1, 0)⟫) +
        (⟪Vortex.gaugeFixedOperator x (fun z ↦ Vortex.variationComplexStructure (Ξ (p.1, z)))
            p.2, fderiv ℝ Η p (I, 0)⟫ +
          ⟪Vortex.gaugeFixedAdjoint x (fun z ↦ Η (p.1, z)) p.2,
            fderiv ℝ (fun q ↦ Vortex.variationComplexStructure (Ξ q)) p (I, 0)⟫) +
        ⟪fderiv ℝ Η p (1, 0), Vortex.targetComplexStructure.symm (fderiv ℝ Η p (I, 0))⟫ +
        ⟪fderiv ℝ Ξ p (1, 0), Vortex.variationComplexStructure (fderiv ℝ Ξ p (I, 0))⟫) := by
  have hdΞ' : fderiv ℝ (fun q ↦ Vortex.variationComplexStructure (Ξ q)) p (I, 0) =
      Vortex.variationComplexStructure (fderiv ℝ Ξ p (I, 0)) :=
    congrArg (fun L ↦ L (I, 0)) (Vortex.variationComplexStructure.comp_fderiv (f := Ξ))
  rw [normalBaseCoupling_eq, pairedBaseCoupling_eq,
    Vortex.gaugeFixedOperator_variationComplexStructure, hdΞ', fderiv_slice_fst_apply (hΞ p),
    fderiv_slice_fst_apply (hΞ p), fderiv_slice_fst_apply (hΗ p), fderiv_slice_fst_apply (hΗ p)]
  simp only [norm_add_sq_real, LinearIsometryEquiv.norm_map, norm_neg, inner_add_right,
    Vortex.targetComplexStructure_symm_apply, inner_neg_right,
    Vortex.inner_targetComplexStructure_left]
  ring

/-- **The energy identity of the normal model with base dependence.** Let `x` be a continuous
plane field and `Ξ`, `Η : ℂ × ℂ → ℝ⁴` compactly supported `C²` families of plane fields over the
base, the normal and the paired block of the normal model. Write `N` and `P` for its two rows,
`N = L_x Ξ (w, ·) + normalBaseCoupling (D_w Η)` and
`P = L_x* Η (w, ·) + pairedBaseCoupling (D_w Ξ)`, with `D_w` the derivative along the base. Then,
for any additive Haar measures `μ` on the base and
`ν` on the normal plane,

`∫ (|N|² + |P|²) = ∫ (|L_x Ξ|² + |L_x* Η|² + |∂_s Ξ|² + |∂_t Ξ|² + |∂_s Η|² + |∂_t Η|²)`,

where `w = s + i t`: the base couplings contribute exactly the energy of the families along the
base, with no cross terms. -/
theorem integral_norm_sq_add_norm_sq_familyNormalModel (hx : Continuous x)
    (hΞ : ContDiff ℝ 2 Ξ) (hΗ : ContDiff ℝ 2 Η) (hΞc : HasCompactSupport Ξ)
    (hΗc : HasCompactSupport Η) :
    ∫ p, (‖Vortex.gaugeFixedOperator x (fun z ↦ Ξ (p.1, z)) p.2 +
          normalBaseCoupling (fderiv ℝ (fun w ↦ Η (w, p.2)) p.1)‖ ^ 2 +
        ‖Vortex.gaugeFixedAdjoint x (fun z ↦ Η (p.1, z)) p.2 +
          pairedBaseCoupling (fderiv ℝ (fun w ↦ Ξ (w, p.2)) p.1)‖ ^ 2) ∂μ.prod ν =
      ∫ p, (‖Vortex.gaugeFixedOperator x (fun z ↦ Ξ (p.1, z)) p.2‖ ^ 2 +
        ‖Vortex.gaugeFixedAdjoint x (fun z ↦ Η (p.1, z)) p.2‖ ^ 2 +
        ‖fderiv ℝ (fun w ↦ Ξ (w, p.2)) p.1 1‖ ^ 2 + ‖fderiv ℝ (fun w ↦ Ξ (w, p.2)) p.1 I‖ ^ 2 +
        ‖fderiv ℝ (fun w ↦ Η (w, p.2)) p.1 1‖ ^ 2 + ‖fderiv ℝ (fun w ↦ Η (w, p.2)) p.1 I‖ ^ 2)
        ∂μ.prod ν := by
  have hΞ₁ : ContDiff ℝ 1 Ξ := hΞ.of_le (by norm_num)
  have hΗ₁ : ContDiff ℝ 1 Η := hΗ.of_le (by norm_num)
  -- The family `J Ξ` carries the cross term along `t`.
  have hΞ' : ContDiff ℝ 2 fun q ↦ Vortex.variationComplexStructure (Ξ q) :=
    Vortex.variationComplexStructure.contDiff.comp hΞ
  -- Each of the four cross terms is integrable and integrates to zero.
  have i₁ := integrable_inner_gaugeFixedOperator_slice_add_inner_gaugeFixedAdjoint_slice
    (μ := μ) (ν := ν) hx hΞ₁ hΗ₁ hΗc 1
  have i₂ := integrable_inner_gaugeFixedOperator_slice_add_inner_gaugeFixedAdjoint_slice
    (μ := μ) (ν := ν) hx (hΞ'.of_le (by norm_num)) hΗ₁ hΗc I
  have i₃ := integrable_inner_fderiv_apply (μ := μ) (ν := ν) hΗ₁ hΗc
    Vortex.targetComplexStructure.symm
  have i₄ := integrable_inner_fderiv_apply (μ := μ) (ν := ν) hΞ₁ hΞc
    Vortex.variationComplexStructure
  have h₁ := integral_inner_gaugeFixedOperator_slice_add_inner_gaugeFixedAdjoint_slice
    (μ := μ) (ν := ν) hx hΞ hΗ hΗc 1
  have h₂ := integral_inner_gaugeFixedOperator_slice_add_inner_gaugeFixedAdjoint_slice
    (μ := μ) (ν := ν) hx hΞ' hΗ hΗc I
  have h₃ : ∫ p, ⟪fderiv ℝ Η p (1, 0), Vortex.targetComplexStructure.symm (fderiv ℝ Η p (I, 0))⟫
      ∂μ.prod ν = 0 := by
    simpa only [LinearMap.compl₂_apply, innerₗ_apply_apply, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv] using
      integral_bilinForm_fderiv_apply_eq_zero_of_isAlt (μ := μ.prod ν)
        isAlt_compl₂_targetComplexStructure_symm hΗ hΗc (1, 0) (I, 0)
  have h₄ : ∫ p, ⟪fderiv ℝ Ξ p (1, 0), Vortex.variationComplexStructure (fderiv ℝ Ξ p (I, 0))⟫
      ∂μ.prod ν = 0 := by
    simpa only [LinearMap.compl₂_apply, innerₗ_apply_apply, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv] using
      integral_bilinForm_fderiv_apply_eq_zero_of_isAlt (μ := μ.prod ν)
        isAlt_compl₂_variationComplexStructure hΞ hΞc (1, 0) (I, 0)
  rw [integral_congr_ae (.of_forall (norm_sq_add_norm_sq_familyNormalModel_eq
      (hΞ₁.differentiable one_ne_zero) (hΗ₁.differentiable one_ne_zero))),
    integral_add (integrable_energy_familyNormalModel hx hΞ₁ hΗ₁ hΞc hΗc) ?_, integral_const_mul,
    integral_add ?_ i₄, integral_add ?_ i₃, integral_add i₁ i₂, h₁, h₂, h₃, h₄]
  all_goals first
    | exact i₁.add i₂ | exact (i₁.add i₂).add i₃ | exact (((i₁.add i₂).add i₃).add i₄).const_mul 2
    | norm_num

/-- **The base energy is controlled by the normal model.** For a continuous plane field `x` and
compactly supported `C²` families `Ξ`, `Η`, the energy of the families along the base is at most
the squared `L²` norm `∫ (|N|² + |P|²)` of the two rows of the normal model. -/
theorem integral_norm_sq_fderiv_le_integral_norm_sq_add_norm_sq_familyNormalModel
    (hx : Continuous x) (hΞ : ContDiff ℝ 2 Ξ) (hΗ : ContDiff ℝ 2 Η) (hΞc : HasCompactSupport Ξ)
    (hΗc : HasCompactSupport Η) :
    ∫ p, (‖fderiv ℝ (fun w ↦ Ξ (w, p.2)) p.1 1‖ ^ 2 + ‖fderiv ℝ (fun w ↦ Ξ (w, p.2)) p.1 I‖ ^ 2 +
        ‖fderiv ℝ (fun w ↦ Η (w, p.2)) p.1 1‖ ^ 2 + ‖fderiv ℝ (fun w ↦ Η (w, p.2)) p.1 I‖ ^ 2)
        ∂μ.prod ν ≤
      ∫ p, (‖Vortex.gaugeFixedOperator x (fun z ↦ Ξ (p.1, z)) p.2 +
          normalBaseCoupling (fderiv ℝ (fun w ↦ Η (w, p.2)) p.1)‖ ^ 2 +
        ‖Vortex.gaugeFixedAdjoint x (fun z ↦ Η (p.1, z)) p.2 +
          pairedBaseCoupling (fderiv ℝ (fun w ↦ Ξ (w, p.2)) p.1)‖ ^ 2) ∂μ.prod ν := by
  rw [integral_norm_sq_add_norm_sq_familyNormalModel hx hΞ hΗ hΞc hΗc]
  refine integral_mono_of_nonneg (.of_forall fun p ↦ by positivity)
    (integrable_energy_familyNormalModel hx (hΞ.of_le (by norm_num)) (hΗ.of_le (by norm_num)) hΞc
      hΗc) (.of_forall fun p ↦ ?_)
  dsimp only
  nlinarith [sq_nonneg ‖Vortex.gaugeFixedOperator x (fun z ↦ Ξ (p.1, z)) p.2‖,
    sq_nonneg ‖Vortex.gaugeFixedAdjoint x (fun z ↦ Η (p.1, z)) p.2‖]

/-- **Coercivity of the paired block.** Suppose that `L_x*` is bounded below on the normal plane,
`c ∫ |η|² ≤ ∫ |L_x* η|²` for every compactly supported `C²` field `η`. Then the same constant
bounds the paired family of the normal model: `c ∫ |Η|² ≤ ∫ (|N|² + |P|²)`. -/
theorem mul_integral_norm_sq_le_integral_norm_sq_add_norm_sq_familyNormalModel
    (hx : Continuous x) (hΞ : ContDiff ℝ 2 Ξ) (hΗ : ContDiff ℝ 2 Η) (hΞc : HasCompactSupport Ξ)
    (hΗc : HasCompactSupport Η) {c : ℝ}
    (hgap : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
      c * ∫ z, ‖η z‖ ^ 2 ∂ν ≤ ∫ z, ‖Vortex.gaugeFixedAdjoint x η z‖ ^ 2 ∂ν) :
    c * ∫ p, ‖Η p‖ ^ 2 ∂μ.prod ν ≤
      ∫ p, (‖Vortex.gaugeFixedOperator x (fun z ↦ Ξ (p.1, z)) p.2 +
          normalBaseCoupling (fderiv ℝ (fun w ↦ Η (w, p.2)) p.1)‖ ^ 2 +
        ‖Vortex.gaugeFixedAdjoint x (fun z ↦ Η (p.1, z)) p.2 +
          pairedBaseCoupling (fderiv ℝ (fun w ↦ Ξ (w, p.2)) p.1)‖ ^ 2) ∂μ.prod ν := by
  have hΗ₁ : ContDiff ℝ 1 Η := hΗ.of_le (by norm_num)
  have hR := integrable_energy_familyNormalModel (μ := μ) (ν := ν) hx (hΞ.of_le (by norm_num)) hΗ₁
    hΞc hΗc
  have hΗi : Integrable (fun p ↦ ‖Η p‖ ^ 2) (μ.prod ν) :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop)
      (hΗc.comp_left (g := fun v : EuclideanSpace ℝ (Fin 4) ↦ ‖v‖ ^ 2) (by simp))
  -- The squared norm of `L_x* Η` is dominated by the right side of the energy identity.
  have hle (p : ℂ × ℂ) : ‖Vortex.gaugeFixedAdjoint x (fun z ↦ Η (p.1, z)) p.2‖ ^ 2 ≤
      ‖Vortex.gaugeFixedOperator x (fun z ↦ Ξ (p.1, z)) p.2‖ ^ 2 +
        ‖Vortex.gaugeFixedAdjoint x (fun z ↦ Η (p.1, z)) p.2‖ ^ 2 +
        ‖fderiv ℝ (fun w ↦ Ξ (w, p.2)) p.1 1‖ ^ 2 + ‖fderiv ℝ (fun w ↦ Ξ (w, p.2)) p.1 I‖ ^ 2 +
        ‖fderiv ℝ (fun w ↦ Η (w, p.2)) p.1 1‖ ^ 2 + ‖fderiv ℝ (fun w ↦ Η (w, p.2)) p.1 I‖ ^ 2 := by
    have := sq_nonneg ‖Vortex.gaugeFixedOperator x (fun z ↦ Ξ (p.1, z)) p.2‖
    have := sq_nonneg ‖fderiv ℝ (fun w ↦ Ξ (w, p.2)) p.1 1‖
    have := sq_nonneg ‖fderiv ℝ (fun w ↦ Ξ (w, p.2)) p.1 I‖
    have := sq_nonneg ‖fderiv ℝ (fun w ↦ Η (w, p.2)) p.1 1‖
    have := sq_nonneg ‖fderiv ℝ (fun w ↦ Η (w, p.2)) p.1 I‖
    linarith
  have hAi : Integrable (fun p ↦ ‖Vortex.gaugeFixedAdjoint x (fun z ↦ Η (p.1, z)) p.2‖ ^ 2)
      (μ.prod ν) :=
    hR.mono' ((continuous_gaugeFixedAdjoint_slice hx hΗ₁).norm.pow 2).aestronglyMeasurable
      (.of_forall fun p ↦ by rw [Real.norm_of_nonneg (by positivity)]; exact hle p)
  rw [integral_norm_sq_add_norm_sq_familyNormalModel hx hΞ hΗ hΞc hΗc]
  refine le_trans ?_ (integral_mono hAi hR hle)
  -- Integrate the gap along each normal slice.
  rw [integral_prod _ hΗi, integral_prod _ hAi, ← integral_const_mul]
  exact integral_mono (hΗi.integral_prod_left.const_mul c) hAi.integral_prod_left fun w ↦
    hgap _ (hΗ.comp (contDiff_const.prodMk contDiff_id))
      (HasCompactSupport.comp_of_forall_mem_imp_mem (hΗc.isCompact.image continuous_snd)
        (fun z hz ↦ ⟨_, hz, rfl⟩) fun _ hq ↦ image_eq_zero_of_notMem_tsupport hq)

/-- **Coercivity of the paired block at a plane vortex.** At a `C¹` plane vortex `x` whose
section has modulus tending to one at infinity there is `c > 0` such that every pair of compactly
supported `C²` families satisfies `c ∫ |Η|² ≤ ∫ (|N|² + |P|²)`, by the spectral gap of `L_x L_x*`
(`TauCeti.Vortex.exists_pos_mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedAdjoint`). -/
theorem exists_pos_mul_integral_norm_sq_le_integral_norm_sq_add_norm_sq_familyNormalModel
    (hx : ContDiff ℝ 1 x) (hsol : ∀ z, Vortex.equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    ∃ c > 0, ∀ Ξ Η : ℂ × ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 Ξ → ContDiff ℝ 2 Η →
      HasCompactSupport Ξ → HasCompactSupport Η →
      c * ∫ p, ‖Η p‖ ^ 2 ∂μ.prod ν ≤
        ∫ p, (‖Vortex.gaugeFixedOperator x (fun z ↦ Ξ (p.1, z)) p.2 +
            normalBaseCoupling (fderiv ℝ (fun w ↦ Η (w, p.2)) p.1)‖ ^ 2 +
          ‖Vortex.gaugeFixedAdjoint x (fun z ↦ Η (p.1, z)) p.2 +
            pairedBaseCoupling (fderiv ℝ (fun w ↦ Ξ (w, p.2)) p.1)‖ ^ 2) ∂μ.prod ν := by
  obtain ⟨c, hc, hgap⟩ :=
    Vortex.exists_pos_mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedAdjoint (μ := ν) hx hsol
      hlim
  exact ⟨c, hc, fun Ξ Η hΞ hΗ hΞc hΗc ↦
    mul_integral_norm_sq_le_integral_norm_sq_add_norm_sq_familyNormalModel hx.continuous hΞ hΗ hΞc
      hΗc hgap⟩

end Energy

end TauCeti.SeibergWitten
