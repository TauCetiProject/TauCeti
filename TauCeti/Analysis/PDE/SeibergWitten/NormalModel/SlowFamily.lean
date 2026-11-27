/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.NormalModel.Basic
public import TauCeti.Analysis.PDE.Vortex.Kernel.Tangent
import Mathlib.Analysis.Complex.Conformal
import TauCeti.Analysis.Calculus.ParametricIntegral.CompactSupport
import TauCeti.Topology.Algebra.Support

/-!
# The slow family of the frozen normal model is `∂bar`

Near a pseudoholomorphic curve, Taubes's rescaled large-parameter Seiberg–Witten solutions are
modelled on `ℂ_base × ℂ_normal` by a plane vortex `x` in the normal factor. The linearized
equations at such a frozen model act on a normal family `Ξ` and a paired family `Η` of plane fields
over the base, through the two rows
(`TauCeti.Analysis.PDE.SeibergWitten.NormalModel.Basic`)

`N = L_x Ξ (w, ·) + normalBaseCoupling (D_w Η)`,  `P = L_x* Η (w, ·) + pairedBaseCoupling (D_w Ξ)`,

where `L_x` is the gauge-fixed vortex operator, `D_w` the derivative along the base `w = s + i t`
and `pairedBaseCoupling D = D 1 + J (D i)` for the complex structure `J` of variations
(`TauCeti.SeibergWitten.pairedBaseCoupling_apply`). At a vortex of degree `m`, `L_x` is onto with
a kernel `K` of real dimension `2m`, so `L_x*` is injective with range orthogonal to `K`. The
*slow* variable of the model is the `K`-component of `Ξ`, and the *slow* equation the
`K`-component of `P`; the other components are governed by the invertible fast blocks. This file
computes the pairings of the paired row with `C¹` fields `κ` with `L_x κ = 0`, which only involve
`Ξ`, and shows that in the divisor coordinates of `K` the base-coupling term of the paired row of
a kernel-valued family, which is the whole paired row when `Η = 0`, is the kernel field whose
coordinates are `2 ∂bar` of the coordinates of the family.

**Pairing the paired row with the kernel.** For a continuous field `x`, compactly supported
`C¹` families `Ξ`, `Η` and a `C¹` field `κ` with `L_x κ = 0`, pairing the paired row with `κ` over
the normal plane gives

`∫ ⟪κ, P (w, ·)⟫ = ∂_s ∫ ⟪κ, Ξ (w, ·)⟫ - ∂_t ∫ ⟪J κ, Ξ (w, ·)⟫`

(`TauCeti.SeibergWitten.integral_inner_gaugeFixedAdjoint_add_pairedBaseCoupling`). The paired
family drops out, since `∫ ⟪κ, L_x* η⟫ = ∫ ⟪L_x κ, η⟫ = 0`. Informally, as `J` preserves `K`
(`TauCeti.Vortex.variationComplexStructure_comp_mem_gaugeFixedKernel`) and is an isometry, letting
`κ` range over an orthonormal basis of `K` reads this identity as saying that the `K`-component of
`P` is `∂_s k + J ∂_t k` for the `K`-component `k` of `Ξ`; this file does not define these
components or the projection onto `K`.

**Divisor coordinates.** At a smooth field with `∂bar_a α = 0`, `|α| → 1` at infinity and zero
divisor `D ∈ Sym^m ℂ`, for instance a smooth framed degree-`m` vortex, the divisor variation
identifies `K` with the tangent space `ℂ[X]_{<m}` of `Sym^m ℂ`
(`TauCeti.Vortex.gaugeFixedKernelEquivDegreeLT`), complex linearly for `J`
(`TauCeti.Vortex.gaugeFixedKernelEquivDegreeLT_gaugeFixedKernelAlmostComplexStructure`). Composed
with the coefficients of polynomials of degree less than `m`, this is the real-linear isomorphism
`TauCeti.Vortex.gaugeFixedKernelEquivCoeff : K ≃ ℂ^m`, with `J` corresponding to `i`. A map
`c : ℂ → ℂ^m` from the base to these coordinates gives the kernel-valued normal family
`Ξ (w, z) = (E⁻¹ (c w)) z`, on which `L_x Ξ (w, ·) = 0` and

`pairedBaseCoupling (D_w Ξ) = E⁻¹ (∂_s c + i ∂_t c) = E⁻¹ (2 ∂bar c)`

(`TauCeti.SeibergWitten.pairedBaseCoupling_fderiv_gaugeFixedKernelEquivCoeff_symm`). So with
`Η = 0` the linearized flat limiting equations vanish on the normal model of this family at every
point over `w` exactly when `c` satisfies the Cauchy–Riemann equation at `w`
(`flatDeformation_familyNormalModel_gaugeFixedKernelEquivCoeff_symm_eq_zero_iff`),
and at every point of `ℂ_base × ℂ_normal` exactly when `c` is holomorphic
(`flatDeformation_familyNormalModel_gaugeFixedKernelEquivCoeff_symm_eq_zero_iff_differentiable`):
the kernel-valued solutions of the frozen model are the holomorphic maps from the base to the
tangent space of the divisor space.

The model is frozen: the vortex `x` does not move with the base point. Along a curve the vortex
varies with a divisor `σ (w)`, and the slow block acquires the derivatives of the moving kernel
projections, which are not treated here.

## Main results

* `TauCeti.SeibergWitten.integral_inner_gaugeFixedAdjoint_add_pairedBaseCoupling`: pairing the
  paired row with a `C¹` field `κ` with `L_x κ = 0` gives `∂_s ⟨κ, Ξ⟩ - ∂_t ⟨J κ, Ξ⟩`; the paired
  family drops out.
* `TauCeti.SeibergWitten.pairedBaseCoupling_fderiv_gaugeFixedKernelEquivCoeff_symm`: on a
  kernel-valued family in divisor coordinates `c`, the base-coupling term of the paired row (the
  whole paired row when `Η = 0`) is the kernel field `E⁻¹ (∂_s c + i ∂_t c)`.
* `flatDeformation_familyNormalModel_gaugeFixedKernelEquivCoeff_symm_eq_zero_iff_differentiable`:
  such a family solves the frozen model exactly when `c` is holomorphic.

## References

* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
* T. M. Samols, *Vortex scattering*, Comm. Math. Phys. 145 (1992), 149–179.
-/

public section

noncomputable section

namespace TauCeti.SeibergWitten

open CliffordAlgebra Filter MeasureTheory Module Polynomial Set Complex
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

/-! ### The kernel component of the paired row -/

section KernelComponent

variable {x κ : ℂ → EuclideanSpace ℝ (Fin 4)} {Ξ Η : ℂ × ℂ → EuclideanSpace ℝ (Fin 4)}
  {ν : Measure ℂ} [ν.IsAddHaarMeasure]

/-- **The pairing of the paired row of the frozen normal model with the kernel.** Let `x` be a
continuous plane field, `Ξ` and `Η` compactly supported `C¹` families of plane fields over the
base, and `κ` a `C¹` field with `L_x κ = 0`. Pairing the paired row
`P = L_x* Η (w, ·) + pairedBaseCoupling (D_w Ξ)` of the normal model with `κ` over the normal plane
gives

`∫ ⟪κ, P (w, ·)⟫ = ∂_s ∫ ⟪κ, Ξ (w, ·)⟫ - ∂_t ∫ ⟪J κ, Ξ (w, ·)⟫`,

with `w = s + i t` and `J` the complex structure of variations. The paired family `Η` does not
contribute. -/
theorem integral_inner_gaugeFixedAdjoint_add_pairedBaseCoupling (hx : Continuous x)
    (hΞ : ContDiff ℝ 1 Ξ) (hΞc : HasCompactSupport Ξ) (hΗ : ContDiff ℝ 1 Η)
    (hΗc : HasCompactSupport Η) (hκ : ContDiff ℝ 1 κ)
    (hLκ : ∀ z, Vortex.gaugeFixedOperator x κ z = 0) (w : ℂ) :
    ∫ z, ⟪κ z, Vortex.gaugeFixedAdjoint x (fun z' ↦ Η (w, z')) z +
        pairedBaseCoupling (fderiv ℝ (fun w' ↦ Ξ (w', z)) w)⟫ ∂ν =
      fderiv ℝ (fun w' ↦ ∫ z, ⟪κ z, Ξ (w', z)⟫ ∂ν) w 1 -
        fderiv ℝ (fun w' ↦ ∫ z, ⟪Vortex.variationComplexStructure (κ z), Ξ (w', z)⟫ ∂ν) w I := by
  have hJκ : ContDiff ℝ 1 fun z ↦ Vortex.variationComplexStructure (κ z) :=
    Vortex.variationComplexStructure.contDiff.comp hκ
  have hΗw : ContDiff ℝ 1 fun z' ↦ Η (w, z') := hΗ.comp (contDiff_prodMk_right w)
  have hintL := Vortex.integrable_inner_gaugeFixedAdjoint (μ := ν) hx hκ.continuous hΗw
    (hΗc.comp_prodMk_right w)
  have hL := Vortex.integral_inner_gaugeFixedAdjoint_eq_zero (μ := ν) hκ hΗw
    (.inr (hΗc.comp_prodMk_right w)) hLκ
  have hint₁ := integrable_inner_fderiv_apply_of_contDiff_of_hasCompactSupport (ν := ν) hΞ hΞc
    hκ.continuous w 1
  have hintI := integrable_inner_fderiv_apply_of_contDiff_of_hasCompactSupport (ν := ν) hΞ hΞc
    hJκ.continuous w I
  -- `pairedBaseCoupling D = D 1 + J (D i)` and `⟪κ, J u⟫ = -⟪J κ, u⟫`.
  have hpt (z : ℂ) : ⟪κ z, Vortex.gaugeFixedAdjoint x (fun z' ↦ Η (w, z')) z +
      pairedBaseCoupling (fderiv ℝ (fun w' ↦ Ξ (w', z)) w)⟫ =
      ⟪κ z, Vortex.gaugeFixedAdjoint x (fun z' ↦ Η (w, z')) z⟫ +
        (⟪κ z, fderiv ℝ (fun w' ↦ Ξ (w', z)) w 1⟫ -
          ⟪Vortex.variationComplexStructure (κ z), fderiv ℝ (fun w' ↦ Ξ (w', z)) w I⟫) := by
    rw [pairedBaseCoupling_apply, inner_add_right, inner_add_right,
      Vortex.inner_variationComplexStructure_left (κ z)]
    ring
  simp_rw [hpt]
  rw [integral_add hintL (hint₁.sub' hintI), integral_sub hint₁ hintI, hL, zero_add,
    fderiv_integral_inner_apply_of_contDiff_of_hasCompactSupport hΞ hΞc hκ.continuous,
    fderiv_integral_inner_apply_of_contDiff_of_hasCompactSupport hΞ hΞc hJκ.continuous]

end KernelComponent

/-! ### Kernel-valued families in divisor coordinates -/

section DivisorCoordinates

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)} {m : ℕ} {D : Sym ℂ m}
  (hx : ContDiff ℝ ∞ x) (hhol : ∀ w, Vortex.equation x w 1 = 0 ∧ Vortex.equation x w 2 = 0)
  (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
  (hD : IsZeroMultiplicity (Vortex.sectionValue x) fun z ↦ (D : Multiset ℂ).count z)

include hx hhol hlim hD in
/-- The values of the kernel field with divisor coordinates `v`, a continuous real-linear map of
`v`. -/
private theorem exists_hasFDerivAt_gaugeFixedKernelEquivCoeff_symm_apply {c : ℂ → Fin m → ℂ} {w : ℂ}
    (hc : DifferentiableAt ℝ c w) (z : ℂ) :
    ∃ L : (Fin m → ℂ) →L[ℝ] EuclideanSpace ℝ (Fin 4),
      (∀ v, L v = ((Vortex.gaugeFixedKernelEquivCoeff hx hhol hlim hD).symm v :
        ℂ → EuclideanSpace ℝ (Fin 4)) z) ∧
      HasFDerivAt (fun w' ↦ ((Vortex.gaugeFixedKernelEquivCoeff hx hhol hlim hD).symm (c w') :
        ℂ → EuclideanSpace ℝ (Fin 4)) z) (L.comp (fderiv ℝ c w)) w := by
  set L₀ : (Fin m → ℂ) →ₗ[ℝ] EuclideanSpace ℝ (Fin 4) :=
    (LinearMap.proj z).comp ((Vortex.gaugeFixedKernel x).subtype.comp
      (Vortex.gaugeFixedKernelEquivCoeff hx hhol hlim hD).symm.toLinearMap)
  exact ⟨LinearMap.toContinuousLinearMap L₀, fun v ↦ by simp [L₀],
    (LinearMap.toContinuousLinearMap L₀).hasFDerivAt.comp w hc.hasFDerivAt⟩

include hx hhol hlim hD in
/-- **The base coupling of a kernel-valued family is `E⁻¹ (∂_s c + i ∂_t c)`.** At a smooth
field `x` with `∂bar_a α = 0`, `|α|² → 1` at infinity and zero divisor `D ∈ Sym^m ℂ`, let
`E : ker L_x ≃ ℂ^m` be the divisor coordinates of the kernel of `L_x`
(`TauCeti.Vortex.gaugeFixedKernelEquivCoeff`). For a map `c` from the base to `ℂ^m`, real
differentiable at `w`, the base coupling of the paired rows applied to the base derivative of the
kernel-valued family `(w', z) ↦ (E⁻¹ (c w')) z` is the kernel field with divisor coordinates
`∂_s c + i ∂_t c = 2 ∂bar c`, where `w = s + i t`. -/
theorem pairedBaseCoupling_fderiv_gaugeFixedKernelEquivCoeff_symm {c : ℂ → Fin m → ℂ} {w : ℂ}
    (hc : DifferentiableAt ℝ c w) (z : ℂ) :
    pairedBaseCoupling (fderiv ℝ (fun w' ↦
        ((Vortex.gaugeFixedKernelEquivCoeff hx hhol hlim hD).symm (c w') :
          ℂ → EuclideanSpace ℝ (Fin 4)) z) w) =
      ((Vortex.gaugeFixedKernelEquivCoeff hx hhol hlim hD).symm
        (fderiv ℝ c w 1 + I • fderiv ℝ c w I) : ℂ → EuclideanSpace ℝ (Fin 4)) z := by
  obtain ⟨L, hL, hder⟩ :=
    exists_hasFDerivAt_gaugeFixedKernelEquivCoeff_symm_apply hx hhol hlim hD hc z
  rw [hder.fderiv, pairedBaseCoupling_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ← hL, map_add, hL (I • _),
    Vortex.gaugeFixedKernelEquivCoeff_symm_I_smul,
    Vortex.coe_gaugeFixedKernelAlmostComplexStructure_apply, ← hL]

include hx hhol hlim hD in
/-- The kernel-valued family with divisor coordinates `c` is differentiable wherever `c` is. -/
private theorem differentiableAt_gaugeFixedKernelEquivCoeff_symm {c : ℂ → Fin m → ℂ} {w : ℂ}
    (hc : DifferentiableAt ℝ c w) (z : ℂ) :
    DifferentiableAt ℝ (fun p : ℂ × ℂ ↦
      ((Vortex.gaugeFixedKernelEquivCoeff hx hhol hlim hD).symm (c p.1) :
        ℂ → EuclideanSpace ℝ (Fin 4)) p.2) (w, z) := by
  set E := Vortex.gaugeFixedKernelEquivCoeff hx hhol hlim hD
  let b := Module.finBasis ℝ (Fin m → ℂ)
  -- Expand `c` in a real basis of `ℂ^m`: the family is a finite sum of products.
  have h : (fun p : ℂ × ℂ ↦ (E.symm (c p.1) : ℂ → EuclideanSpace ℝ (Fin 4)) p.2) =
      fun p ↦ ∑ i, b.coord i (c p.1) • (E.symm (b i) : ℂ → EuclideanSpace ℝ (Fin 4)) p.2 := by
    funext p
    conv_lhs => rw [← b.sum_repr (c p.1)]
    simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
      Pi.smul_apply, Basis.coord_apply]
  rw [h]
  refine DifferentiableAt.fun_sum fun i _ ↦ DifferentiableAt.fun_smul ?_ ?_
  · exact (LinearMap.toContinuousLinearMap (b.coord i)).differentiableAt.comp (w, z)
      (hc.comp (w, z) differentiableAt_fst)
  · exact ((Vortex.mem_gaugeFixedKernel.1 (E.symm (b i)).property).1.differentiable
      (by norm_num) z).comp (w, z) differentiableAt_snd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {Q : QuadraticForm ℝ V} {o : Orientation ℝ V (Fin 4)}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
  {e : OrthonormalBasis (Fin 4) ℝ V} {J : AlmostComplexStructure V}

-- The dimension `Fact` makes the oriented four-space finite-dimensional.
attribute [local instance] finiteDimensional_of_finrank_four

variable [Fact (finrank ℝ V = 4)] (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o)
  [FiniteDimensional ℂ W] (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3) (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
  {u₀ : positiveHalfSpinors o ρ} (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀)

include hx hhol hlim hD hQ hkl he h₀ h₂ hρ hu₀ in
/-- At a point `y` over the base point `w`, the three rows of the linearized flat limiting
equations vanish on the normal model of the kernel-valued normal family `Ξ` with divisor
coordinates `c`, and paired family zero, exactly when the kernel field with divisor coordinates
`∂_s c + i ∂_t c` vanishes at the normal coordinate of `y`. -/
private theorem flatDeformation_familyNormalModel_eq_zero_iff_of_baseCoord_eq
    {c : ℂ → Fin m → ℂ} {w : ℂ} (hc : DifferentiableAt ℝ c w) (hu₀₁ : ‖u₀‖ = 1)
    {Ξ : ℂ × ℂ → EuclideanSpace ℝ (Fin 4)}
    (hΞ : Ξ = fun p ↦ ((Vortex.gaugeFixedKernelEquivCoeff hx hhol hlim hD).symm (c p.1) :
      ℂ → EuclideanSpace ℝ (Fin 4)) p.2) {y : V} (hy : baseCoord e y = w) :
    (flatDeformationGauge e (familyNormalModelConnection e Ξ 0) (normalModelSpinor e u₀ x 0)
        (familyNormalModelSpinor e u₀ Ξ 0) y = 0 ∧
      flatDeformationCurvature o ρ hkl (familyNormalModelConnection e Ξ 0)
        (normalModelSpinor e u₀ x 0) (familyNormalModelSpinor e u₀ Ξ 0) y = 0 ∧
      flatDeformationDirac e (normalModelConnection e x 0) (familyNormalModelConnection e Ξ 0)
        (normalModelSpinor e u₀ x 0) (familyNormalModelSpinor e u₀ Ξ 0) y = 0) ↔
      ((Vortex.gaugeFixedKernelEquivCoeff hx hhol hlim hD).symm
        (fderiv ℝ c w 1 + I • fderiv ℝ c w I) : ℂ → EuclideanSpace ℝ (Fin 4)) (normalCoord e y) =
        0 := by
  set E := Vortex.gaugeFixedKernelEquivCoeff hx hhol hlim hD
  subst hΞ hy
  have hL : Vortex.gaugeFixedOperator x
      (fun z ↦ (E.symm (c (baseCoord e y)) : ℂ → EuclideanSpace ℝ (Fin 4)) z)
      (normalCoord e y) = 0 :=
    (Vortex.mem_gaugeFixedKernel.1 (E.symm (c (baseCoord e y))).property).2.2 _
  have hA : Vortex.gaugeFixedAdjoint x (fun z ↦ (0 : ℂ × ℂ → EuclideanSpace ℝ (Fin 4))
      (baseCoord e y, z)) (normalCoord e y) = 0 :=
    Vortex.gaugeFixedAdjoint_eq_zero_of_notMem_tsupport (by simp)
  rw [flatDeformation_familyNormalModel_eq_zero_iff hkl he hQ h₀ h₂ hρ hu₀ x (Η := 0) hu₀₁
    (differentiableAt_gaugeFixedKernelEquivCoeff_symm hx hhol hlim hD hc _)
    (differentiableAt_const 0), hL, hA,
    pairedBaseCoupling_fderiv_gaugeFixedKernelEquivCoeff_symm hx hhol hlim hD hc]
  simp [E]

include hx hhol hlim hD hQ hkl he h₀ h₂ hρ hu₀ in
/-- **The frozen normal model on a kernel-valued family is the Cauchy–Riemann operator.** At a
smooth field `x` with `∂bar_a α = 0`, `|α|² → 1` at infinity and zero divisor `D ∈ Sym^m ℂ`, let
`c` be a map from the base to the divisor coordinates `ℂ^m` of the kernel of `L_x`
(`TauCeti.Vortex.gaugeFixedKernelEquivCoeff`), real differentiable at `w`. The three rows of the
linearized flat limiting equations at the pullback of `x` vanish on the normal model of the
kernel-valued normal family `(w', z) ↦ (E⁻¹ (c w')) z`, with paired family zero, at every point
over the base point `w` exactly when `c` satisfies the Cauchy–Riemann equation
`∂_t c = i ∂_s c` at `w`. -/
theorem flatDeformation_familyNormalModel_gaugeFixedKernelEquivCoeff_symm_eq_zero_iff
    {c : ℂ → Fin m → ℂ} {w : ℂ} (hc : DifferentiableAt ℝ c w) (hu₀₁ : ‖u₀‖ = 1) :
    (∀ y : V, baseCoord e y = w →
      flatDeformationGauge e (familyNormalModelConnection e (fun p ↦
            ((Vortex.gaugeFixedKernelEquivCoeff hx hhol hlim hD).symm (c p.1) :
              ℂ → EuclideanSpace ℝ (Fin 4)) p.2) 0) (normalModelSpinor e u₀ x 0)
          (familyNormalModelSpinor e u₀ (fun p ↦
            ((Vortex.gaugeFixedKernelEquivCoeff hx hhol hlim hD).symm (c p.1) :
              ℂ → EuclideanSpace ℝ (Fin 4)) p.2) 0) y = 0 ∧
        flatDeformationCurvature o ρ hkl (familyNormalModelConnection e (fun p ↦
            ((Vortex.gaugeFixedKernelEquivCoeff hx hhol hlim hD).symm (c p.1) :
              ℂ → EuclideanSpace ℝ (Fin 4)) p.2) 0) (normalModelSpinor e u₀ x 0)
          (familyNormalModelSpinor e u₀ (fun p ↦
            ((Vortex.gaugeFixedKernelEquivCoeff hx hhol hlim hD).symm (c p.1) :
              ℂ → EuclideanSpace ℝ (Fin 4)) p.2) 0) y = 0 ∧
        flatDeformationDirac e (normalModelConnection e x 0)
          (familyNormalModelConnection e (fun p ↦
            ((Vortex.gaugeFixedKernelEquivCoeff hx hhol hlim hD).symm (c p.1) :
              ℂ → EuclideanSpace ℝ (Fin 4)) p.2) 0) (normalModelSpinor e u₀ x 0)
          (familyNormalModelSpinor e u₀ (fun p ↦
            ((Vortex.gaugeFixedKernelEquivCoeff hx hhol hlim hD).symm (c p.1) :
              ℂ → EuclideanSpace ℝ (Fin 4)) p.2) 0) y = 0) ↔
      fderiv ℝ c w I = I • fderiv ℝ c w 1 := by
  set E := Vortex.gaugeFixedKernelEquivCoeff hx hhol hlim hD
  have hrow (y : V) (hy : baseCoord e y = w) :=
    flatDeformation_familyNormalModel_eq_zero_iff_of_baseCoord_eq hx hhol hlim hD hkl he hQ h₀ h₂
      hρ hu₀ hc hu₀₁ rfl hy
  constructor
  · intro h
    have hzero : E.symm (fderiv ℝ c w 1 + I • fderiv ℝ c w I) = 0 := by
      refine Subtype.ext (funext fun z ↦ ?_)
      obtain ⟨y, hy⟩ := (baseNormalCoordHomeomorph e).surjective (w, z)
      rw [baseNormalCoordHomeomorph_apply, Prod.mk.injEq] at hy
      have := (hrow y hy.1).1 (h y hy.1)
      rwa [hy.2] at this
    have hsum := congrArg (I • ·) (E.symm.map_eq_zero_iff.1 hzero)
    simp only [smul_add, smul_smul, I_mul_I, neg_one_smul, smul_zero] at hsum
    exact (add_neg_eq_zero.1 hsum).symm
  · intro h y hy
    rw [hrow y hy, h, smul_smul, I_mul_I, neg_one_smul, add_neg_cancel, map_zero,
      ZeroMemClass.coe_zero, Pi.zero_apply]

include hx hhol hlim hD hQ hkl he h₀ h₂ hρ hu₀ in
/-- **The kernel-valued solutions of the frozen normal model are holomorphic.** At a smooth field
`x` with `∂bar_a α = 0`, `|α|² → 1` at infinity and zero divisor `D ∈ Sym^m ℂ`, let `c` be a real
differentiable map from the base to the divisor coordinates `ℂ^m` of the kernel of `L_x`. The
linearized flat limiting equations at the pullback of `x` vanish everywhere on
`ℂ_base × ℂ_normal` on the normal model of the kernel-valued normal family
`(w, z) ↦ (E⁻¹ (c w)) z`, with paired family zero, exactly when `c` is holomorphic: the
kernel-valued solutions of the frozen model are the holomorphic maps from the base to the tangent
space of the divisor space. -/
theorem flatDeformation_familyNormalModel_gaugeFixedKernelEquivCoeff_symm_eq_zero_iff_differentiable
    {c : ℂ → Fin m → ℂ} (hc : Differentiable ℝ c) (hu₀₁ : ‖u₀‖ = 1) :
    (∀ y : V,
      flatDeformationGauge e (familyNormalModelConnection e (fun p ↦
            ((Vortex.gaugeFixedKernelEquivCoeff hx hhol hlim hD).symm (c p.1) :
              ℂ → EuclideanSpace ℝ (Fin 4)) p.2) 0) (normalModelSpinor e u₀ x 0)
          (familyNormalModelSpinor e u₀ (fun p ↦
            ((Vortex.gaugeFixedKernelEquivCoeff hx hhol hlim hD).symm (c p.1) :
              ℂ → EuclideanSpace ℝ (Fin 4)) p.2) 0) y = 0 ∧
        flatDeformationCurvature o ρ hkl (familyNormalModelConnection e (fun p ↦
            ((Vortex.gaugeFixedKernelEquivCoeff hx hhol hlim hD).symm (c p.1) :
              ℂ → EuclideanSpace ℝ (Fin 4)) p.2) 0) (normalModelSpinor e u₀ x 0)
          (familyNormalModelSpinor e u₀ (fun p ↦
            ((Vortex.gaugeFixedKernelEquivCoeff hx hhol hlim hD).symm (c p.1) :
              ℂ → EuclideanSpace ℝ (Fin 4)) p.2) 0) y = 0 ∧
        flatDeformationDirac e (normalModelConnection e x 0)
          (familyNormalModelConnection e (fun p ↦
            ((Vortex.gaugeFixedKernelEquivCoeff hx hhol hlim hD).symm (c p.1) :
              ℂ → EuclideanSpace ℝ (Fin 4)) p.2) 0) (normalModelSpinor e u₀ x 0)
          (familyNormalModelSpinor e u₀ (fun p ↦
            ((Vortex.gaugeFixedKernelEquivCoeff hx hhol hlim hD).symm (c p.1) :
              ℂ → EuclideanSpace ℝ (Fin 4)) p.2) 0) y = 0) ↔
      Differentiable ℂ c := by
  refine ⟨fun h w ↦ differentiableAt_complex_iff_differentiableAt_real.2 ⟨hc w, ?_⟩,
    fun h y ↦ ?_⟩
  · exact (flatDeformation_familyNormalModel_gaugeFixedKernelEquivCoeff_symm_eq_zero_iff hx hhol
      hlim hD hkl he hQ h₀ h₂ hρ hu₀ (hc w) hu₀₁).1 fun y _ ↦ h y
  · exact (flatDeformation_familyNormalModel_gaugeFixedKernelEquivCoeff_symm_eq_zero_iff hx hhol
      hlim hD hkl he hQ h₀ h₂ hρ hu₀ (hc _) hu₀₁).2
      (differentiableAt_complex_iff_differentiableAt_real.1 (h _)).2 y rfl

end DivisorCoordinates

end TauCeti.SeibergWitten
