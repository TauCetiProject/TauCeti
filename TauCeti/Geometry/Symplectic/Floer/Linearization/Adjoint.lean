/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Linearization.Basic
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import TauCeti.Analysis.Calculus.LineDeriv.IntegrationByParts
import TauCeti.Topology.Compactness.Normed
import TauCeti.Topology.Constructions.SumProd

/-!
# The formal adjoint of the linearized Floer operator

Let `u : ℝ × ℝ → V` be a map into a finite-dimensional symplectic vector space, and let
`D ξ = ∂s ξ + J(z, u z) ∂t ξ + C(z) ξ` be the linearized Floer operator along `u`
(`TauCeti.SymplecticForm.floerLinearization`), written with its zeroth-order part
`C = TauCeti.SymplecticForm.floerLinearizationCoeff` (`floerLinearization_eq_add`). The
coefficients `J(z, u z)` and `C(z)` depend on the domain point, through `z` and through `u`.

Cokernel elements of `D` are fields `η : ℝ × ℝ → V →L[ℝ] ℝ` of covectors annihilating its range
for the duality pairing `∫ η(D ξ) ds dt`. This is the form in which the transversality arguments
of `TauCeti.Geometry.Symplectic.Floer.Perturbation.Basic` and
`TauCeti.Geometry.Symplectic.Floer.Transversality.AlmostComplexVariation` take them: Hamiltonian
variations of the perturbation, and variations of the almost complex structure at injective
points, force such an `η` to vanish on an open set. The pairing uses no metric on `V`, so no
compatibility of `J` with `ω` is needed in this file (the `ω`-form below only asks that `J`
preserve `ω`), and `J` need not square to `-1`.

Integrating by parts against this pairing gives the **formal adjoint**

`D^* η = -∂s η - ∂t (η ∘ J(z, u z)) + η ∘ C(z)`

(`TauCeti.SymplecticForm.floerLinearizationAdjoint`), again a field of covectors.

* **Cauchy–Riemann form.** Expanding `∂t (η ∘ J)`, the adjoint is
  `D^* η = -(∂s η + (∂t η) ∘ J + η ∘ (∂t J - C))`
  (`floerLinearizationAdjoint_eq_neg`), where `∂t J` is the `t`-derivative of `z ↦ J(z, u z)`.
  So `D^* η = 0` is a first-order real Cauchy–Riemann equation for `η` with leading coefficient
  `θ ↦ θ ∘ J`, which is again a complex structure, on the dual space, when `J` is one: this is the
  equation on which unique continuation for cokernel elements acts. Written through `ω` as the
  vector field `ζ = ω♭⁻¹ ∘ η` (`fderiv_flatEquiv_symm_apply`), at a point where `J` preserves `ω`
  the adjoint is `-ω♭` of `∂s ζ - J ∂t ζ + Aᵀ ζ`, a Cauchy–Riemann operator for `-J`, with
  `A = ∂t J - C` and `ᵀ` the `ω`-transpose (`floerLinearizationAdjoint_eq_neg_flatEquiv`); for a
  constant structure `J₀` and the zero perturbation, `A = 0`
  (`floerLinearizationAdjoint_const_eq_neg_flatEquiv`). From
  the first form, two adjoints differ on `η` by at most `‖J - J₁‖ ‖∂t η‖ + ‖A - A₁‖ ‖η‖`
  (`norm_floerLinearizationAdjoint_sub_floerLinearizationAdjoint_le`), and translating the data,
  the map and `η` translates the adjoint (`floerLinearizationAdjoint_comp_add_right`).
* **Weights.** Multiplying `η` by a function `β(s)` gives `β D^* η - β' η`
  (`floerLinearizationAdjoint_smul_fst`); for a function `f` of both variables the derivative of
  `f` in `t` also enters, through `η ∘ J` (`floerLinearizationAdjoint_fun_smul`), so
  `‖D^* (f η)‖ ≤ |f| ‖D^* η‖ + ‖df‖ (1 + ‖J‖) ‖η‖`
  (`norm_floerLinearizationAdjoint_fun_smul_le`), and for `|f| ≤ 1`, `‖df‖ ≤ M` and `‖J‖ ≤ B`,
  `‖D^* (f η)‖² ≤ 2 ‖D^* η‖² + 2 (M (1 + B))² ‖η‖²`
  (`norm_floerLinearizationAdjoint_fun_smul_sq_le`). In particular the weight `e^{δ s}` shifts
  the adjoint by `-δ` (`floerLinearizationAdjoint_exp_smul`). Since
  `D (e^{-δ s} ξ) = e^{-δ s} (D - δ) ξ`
  (`TauCeti.SymplecticForm.floerLinearization_exp_smul`), this is the weight dual to `e^{-δ s}`:
  both conjugated operators are `D - δ` and its adjoint `D^* - δ`. Integrated against a
  continuous weight `w ≥ 0`, a cutoff `β` with values in `[0, 1]` costs
  `∫ w ‖D^* (β η)‖² ≤ 2 ∫ w ‖D^* η‖² + C ∫_K ‖η‖²`, with `K` a compact set off which `dβ`
  vanishes (`exists_integral_mul_norm_floerLinearizationAdjoint_smul_sq_le`, the weighted adjoint
  counterpart of `exists_integral_norm_floerLinearization_smul_sq_le`); the weighted square norm
  of `D^* η` is integrable for `η` of compact support in an open set on which the data and the
  weight are regular (`integrable_mul_norm_floerLinearizationAdjoint_sq`).
* **Green's formula.** Pointwise,
  `η(D ξ) = (D^* η)(ξ) + ∂s (η(ξ)) + ∂t ((η ∘ J)(ξ))`
  (`apply_floerLinearization_eq_floerLinearizationAdjoint_apply_add`). Integrated, when the
  common support of `η` and `ξ` is compact and `η`, `ξ` and the data are `C¹` (Hamiltonians `C²`)
  on it, `∫ η(D ξ) = ∫ (D^* η)(ξ)` over the plane
  (`integral_apply_floerLinearization_eq_integral_floerLinearizationAdjoint_apply`). Over a closed
  rectangle, with regularity only on the rectangle, the same identity holds when `η(ξ)` takes
  equal values on the two vertical sides and `(η ∘ J)(ξ)` on the two horizontal sides
  (`setIntegral_apply_floerLinearization_eq_setIntegral_floerLinearizationAdjoint_apply`, by the
  divergence theorem); on `[a, b] × [0, 1]` this covers `ξ` vanishing at `s = a, b` with `η`, `ξ`
  and `J(·, u ·)` of period one in `t`.
* **Classical cokernel elements.** If `η` is `C¹` on an open set `U`, then it annihilates `D ξ` for
  every smooth `ξ` compactly supported in `U` exactly when `D^* η = 0` on `U`
  (`forall_integral_apply_floerLinearization_eq_zero_iff`). This is the fundamental lemma of
  the calculus of variations (`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`), applied to
  Green's formula with test maps `φ v`.

For the cylindrical datum `(J_t, 0, H_t)`, the zeroth-order coefficient `∂t J - C` at `z` is a
continuous function `cylindricalAdjointCoeff (t, w z, ∂t w z)` of the time, the value and the slice
velocity of the map (`fderiv_sub_floerLinearizationCoeff_eq_cylindricalAdjointCoeff`,
`continuous_cylindricalAdjointCoeff`), uniformly continuous near the curve of a stationary
cylinder (`exists_pos_forall_norm_cylindricalAdjointCoeff_sub_le`). This is how the coefficients
of the adjoint along maps close to an orbit in `C¹` are compared with those at the orbit.

For `t`-dependent data along a stationary map, the metric version of this adjoint, for the pairing
`∫ ω(·, J_t ·)`, is `TauCeti.Floer.stationaryCylinderAdjoint`. The regularity of weak (`L²`)
cokernel elements, which makes them `C¹`, is not treated here.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 3.1 and Appendix C.1, on the formal adjoint of a real
  Cauchy–Riemann operator and the cokernel in transversality arguments.
* A. Floer, H. Hofer and D. Salamon, *Transversality in elliptic Morse theory for the symplectic
  action*, Duke Math. J. 80 (1995), 251–292.
-/

public section

open Set Filter MeasureTheory Topology ContinuousLinearMap

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ}
  {u ξ : ℝ × ℝ → V} {η η₁ η₂ : ℝ × ℝ → V →L[ℝ] ℝ} {z : ℝ × ℝ}

/-- The **formal adjoint** of the linearized Floer operator along `u`, for the duality pairing
`∫ η(ξ) ds dt` between covector fields `η` and maps `ξ`:

`D^* η = -∂s η - ∂t (η ∘ J(z, u z)) + η ∘ C(z)`,

with `C = floerLinearizationCoeff` the zeroth-order part of `floerLinearization`. -/
noncomputable def floerLinearizationAdjoint (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V)
    (η : ℝ × ℝ → V →L[ℝ] ℝ) (z : ℝ × ℝ) : V →L[ℝ] ℝ :=
  -fderiv ℝ η z stdComplexLineReal -
      fderiv ℝ (fun w ↦ (η w).comp (J w (u w))) z stdComplexLineImag +
    (η z).comp (ω.floerLinearizationCoeff J Ks Kt u z)

/-- The coordinate expression of the formal adjoint. -/
theorem floerLinearizationAdjoint_def (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V)
    (η : ℝ × ℝ → V →L[ℝ] ℝ) (z : ℝ × ℝ) :
    ω.floerLinearizationAdjoint J Ks Kt u η z =
      -fderiv ℝ η z stdComplexLineReal -
          fderiv ℝ (fun w ↦ (η w).comp (J w (u w))) z stdComplexLineImag +
        (η z).comp (ω.floerLinearizationCoeff J Ks Kt u z) :=
  (rfl)

/-! ### Linearity and locality -/

/-- The formal adjoint sends the zero covector field to zero. -/
@[simp]
theorem floerLinearizationAdjoint_zero (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ω.floerLinearizationAdjoint J Ks Kt u 0 z = 0 := by
  simp [floerLinearizationAdjoint_def]

/-- The formal adjoint respects real scaling. -/
@[simp]
theorem floerLinearizationAdjoint_smul (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V)
    (η : ℝ × ℝ → V →L[ℝ] ℝ) (z : ℝ × ℝ) (c : ℝ) :
    ω.floerLinearizationAdjoint J Ks Kt u (c • η) z =
      c • ω.floerLinearizationAdjoint J Ks Kt u η z := by
  have h : (fun w ↦ ((c • η) w).comp (J w (u w))) = c • fun w ↦ (η w).comp (J w (u w)) := by
    ext w
    simp
  rw [floerLinearizationAdjoint_def, floerLinearizationAdjoint_def, h,
    fderiv_const_smul_field (𝕜 := ℝ) (f := η) c,
    fderiv_const_smul_field (𝕜 := ℝ) (f := fun w ↦ (η w).comp (J w (u w))) c]
  simp only [Pi.smul_apply, smul_apply, smul_comp, smul_add, smul_sub, smul_neg]

/-- The formal adjoint is additive on covector fields differentiable at the domain point, when
`w ↦ J(w, u w)` is differentiable there. -/
@[simp]
theorem floerLinearizationAdjoint_add (hη₁ : DifferentiableAt ℝ η₁ z)
    (hη₂ : DifferentiableAt ℝ η₂ z) (hJu : DifferentiableAt ℝ (fun w ↦ J w (u w)) z) :
    ω.floerLinearizationAdjoint J Ks Kt u (η₁ + η₂) z =
      ω.floerLinearizationAdjoint J Ks Kt u η₁ z + ω.floerLinearizationAdjoint J Ks Kt u η₂ z := by
  have h : (fun w ↦ ((η₁ + η₂) w).comp (J w (u w))) =
      (fun w ↦ (η₁ w).comp (J w (u w))) + fun w ↦ (η₂ w).comp (J w (u w)) := by
    ext w
    simp
  rw [floerLinearizationAdjoint_def, floerLinearizationAdjoint_def, floerLinearizationAdjoint_def,
    h, fderiv_add hη₁ hη₂, fderiv_add (hη₁.clm_comp hJu) (hη₂.clm_comp hJu)]
  simp only [add_apply, Pi.add_apply, add_comp]
  abel

/-- The formal adjoint is subtractive on covector fields differentiable at the domain point, when
`w ↦ J(w, u w)` is differentiable there. -/
@[simp]
theorem floerLinearizationAdjoint_sub (hη₁ : DifferentiableAt ℝ η₁ z)
    (hη₂ : DifferentiableAt ℝ η₂ z) (hJu : DifferentiableAt ℝ (fun w ↦ J w (u w)) z) :
    ω.floerLinearizationAdjoint J Ks Kt u (η₁ - η₂) z =
      ω.floerLinearizationAdjoint J Ks Kt u η₁ z - ω.floerLinearizationAdjoint J Ks Kt u η₂ z := by
  have h : (fun w ↦ ((η₁ - η₂) w).comp (J w (u w))) =
      (fun w ↦ (η₁ w).comp (J w (u w))) - fun w ↦ (η₂ w).comp (J w (u w)) := by
    ext w
    simp
  rw [floerLinearizationAdjoint_def, floerLinearizationAdjoint_def, floerLinearizationAdjoint_def,
    h, fderiv_sub hη₁ hη₂, fderiv_sub (hη₁.clm_comp hJu) (hη₂.clm_comp hJu)]
  simp only [sub_apply, Pi.sub_apply, sub_comp]
  abel

/-- The formal adjoint at `z` depends only on the germ of the covector field at `z`. -/
theorem floerLinearizationAdjoint_congr_of_eventuallyEq (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) {z : ℝ × ℝ}
    (h : η₁ =ᶠ[𝓝 z] η₂) :
    ω.floerLinearizationAdjoint J Ks Kt u η₁ z = ω.floerLinearizationAdjoint J Ks Kt u η₂ z := by
  have hc : (fun w ↦ (η₁ w).comp (J w (u w))) =ᶠ[𝓝 z] fun w ↦ (η₂ w).comp (J w (u w)) :=
    h.mono fun w hw ↦ by simp only [hw]
  rw [floerLinearizationAdjoint_def, floerLinearizationAdjoint_def, h.fderiv_eq, hc.fderiv_eq,
    h.eq_of_nhds]

/-- The formal adjoint at `z` depends on the structures `J` only near `z`, through the
`t`-derivative of `w ↦ η w ∘ J(w, u w)`, and on the perturbation `Ks`, `Kt` only at `z`, through
the zeroth-order coefficient. -/
theorem floerLinearizationAdjoint_congr_data (ω : SymplecticForm V)
    {J J' : ℝ × ℝ → V → V →L[ℝ] V} {Ks Ks' Kt Kt' : ℝ × ℝ → V → ℝ} (u : ℝ × ℝ → V)
    (η : ℝ × ℝ → V →L[ℝ] ℝ) {z : ℝ × ℝ} (hJ : J =ᶠ[𝓝 z] J') (hKs : Ks z = Ks' z)
    (hKt : Kt z = Kt' z) :
    ω.floerLinearizationAdjoint J Ks Kt u η z = ω.floerLinearizationAdjoint J' Ks' Kt' u η z := by
  have hc : (fun w ↦ (η w).comp (J w (u w))) =ᶠ[𝓝 z] fun w ↦ (η w).comp (J' w (u w)) :=
    hJ.mono fun w hw ↦ by simp only [hw]
  rw [floerLinearizationAdjoint_def, floerLinearizationAdjoint_def, hc.fderiv_eq,
    ω.floerLinearizationCoeff_congr_data u hJ.eq_of_nhds hKs hKt]

/-- **Translation invariance of the formal adjoint.** Translating the data, the map and the
covector field by `v` translates the formal adjoint by `v`, as for the linearized operator
(`floerLinearization_comp_add_right`). -/
theorem floerLinearizationAdjoint_comp_add_right (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V)
    (η : ℝ × ℝ → V →L[ℝ] ℝ) (v z : ℝ × ℝ) :
    ω.floerLinearizationAdjoint (fun w ↦ J (w + v)) (fun w ↦ Ks (w + v)) (fun w ↦ Kt (w + v))
        (fun w ↦ u (w + v)) (fun w ↦ η (w + v)) z =
      ω.floerLinearizationAdjoint J Ks Kt u η (z + v) := by
  simp only [floerLinearizationAdjoint_def, fderiv_comp_add_right,
    fderiv_comp_add_right (f := fun w ↦ (η w).comp (J w (u w)))]
  congr 2
  ext y
  simp only [floerLinearizationCoeff_apply, fderiv_comp_add_right]

/-- The formal adjoint vanishes off the topological support of the covector field. -/
theorem floerLinearizationAdjoint_of_notMem_tsupport (hz : z ∉ tsupport η) :
    ω.floerLinearizationAdjoint J Ks Kt u η z = 0 := by
  rw [floerLinearizationAdjoint_congr_of_eventuallyEq ω J Ks Kt u
    (notMem_tsupport_iff_eventuallyEq.1 hz), floerLinearizationAdjoint_zero]

/-! ### The Cauchy–Riemann form and weights -/

/-- **The formal adjoint as a Cauchy–Riemann operator.** For a covector field `η` and
`w ↦ J(w, u w)` differentiable at `z`,
`D^* η = -(∂s η + (∂t η) ∘ J + η ∘ (∂t J - C))`, where `∂t J` is the `t`-derivative of
`w ↦ J(w, u w)` and `C = floerLinearizationCoeff`. -/
theorem floerLinearizationAdjoint_eq_neg (hη : DifferentiableAt ℝ η z)
    (hJu : DifferentiableAt ℝ (fun w ↦ J w (u w)) z) :
    ω.floerLinearizationAdjoint J Ks Kt u η z =
      -(fderiv ℝ η z stdComplexLineReal + (fderiv ℝ η z stdComplexLineImag).comp (J z (u z)) +
        (η z).comp (fderiv ℝ (fun w ↦ J w (u w)) z stdComplexLineImag -
          ω.floerLinearizationCoeff J Ks Kt u z)) := by
  rw [floerLinearizationAdjoint_def, fderiv_clm_comp hη hJu]
  simp only [add_apply, comp_apply, compL_apply, flip_apply, comp_sub]
  abel

/-- **The formal adjoint through `ω`.** Write a covector field as `η = ω♭ ∘ ζ`, where
`ω♭ v = ω(v, ·)`. At a point where `J(z, u z)` preserves `ω`, the formal adjoint is `-ω♭` of

`∂s ζ - J(z, u z) ∂t ζ + Aᵀ ζ`,

where `A = ∂t J - C` is the zeroth-order coefficient of `floerLinearizationAdjoint_eq_neg` and `ᵀ`
is the `ω`-transpose. This is a Cauchy–Riemann operator for `-J`, which is compatible with `-ω`
when `J` is compatible with `ω`. -/
theorem floerLinearizationAdjoint_eq_neg_flatEquiv (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    {η : ℝ × ℝ → V →L[ℝ] ℝ} {z : ℝ × ℝ} (hη : DifferentiableAt ℝ η z)
    (hJu : DifferentiableAt ℝ (fun w ↦ (J w (u w)).toLinearMap.toContinuousLinearMap) z)
    (hc : ω.Invariant (J z (u z))) :
    ω.floerLinearizationAdjoint (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η
        z =
      -ω.flatEquiv (fderiv ℝ (fun w ↦ ω.flatEquiv.symm (η w)) z stdComplexLineReal +
        (-J z (u z)) (fderiv ℝ (fun w ↦ ω.flatEquiv.symm (η w)) z stdComplexLineImag) +
        ω.leftAdjointL (fderiv ℝ (fun w ↦ (J w (u w)).toLinearMap.toContinuousLinearMap) z
            stdComplexLineImag -
          ω.floerLinearizationCoeff (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt
            u z) (ω.flatEquiv.symm (η z))) := by
  rw [floerLinearizationAdjoint_eq_neg hη hJu, fderiv_flatEquiv_symm_apply,
    fderiv_flatEquiv_symm_apply]
  ext w
  simp only [ContinuousLinearMap.comp_apply, map_neg,
    flatEquiv_apply, map_add, apply_leftAdjointL_apply, apply_flatEquiv_symm_apply, neg_apply,
    add_apply, AlmostComplexStructure.neg_apply, hc.apply_apply_eq_neg,
    LinearMap.coe_toContinuousLinearMap']
  ring

/-- **The formal adjoint of constant data.** For a constant `ω`-invariant structure `J₀` and the
zero perturbation, the formal adjoint along any map is `-ω♭ (∂s ζ - J₀ ∂t ζ)` for `ζ = ω♭⁻¹ ∘ η`:
a Cauchy–Riemann operator for `-J₀`. -/
theorem floerLinearizationAdjoint_const_eq_neg_flatEquiv (ω : SymplecticForm V)
    {J₀ : AlmostComplexStructure V} (u : ℝ × ℝ → V) {η : ℝ × ℝ → V →L[ℝ] ℝ} {z : ℝ × ℝ}
    (hη : DifferentiableAt ℝ η z) (h : ω.Invariant J₀) :
    ω.floerLinearizationAdjoint (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun _ _ ↦ 0) u η z =
      -ω.flatEquiv (fderiv ℝ (fun w ↦ ω.flatEquiv.symm (η w)) z stdComplexLineReal +
        (-J₀) (fderiv ℝ (fun w ↦ ω.flatEquiv.symm (η w)) z stdComplexLineImag)) := by
  rw [ω.floerLinearizationAdjoint_eq_neg_flatEquiv (J := fun _ _ ↦ J₀) hη
    (differentiableAt_const _) h,
    ω.floerLinearizationCoeff_eq_zero_of_eq_base u (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)]
  simp

/-- **Comparing two formal adjoints.** At a point where `w ↦ J(w, u w)` and
`w ↦ J₁(w, u₁ w)` are differentiable, the formal adjoints along two data sets differ on `η` by at
most `‖J(z, u z) - J₁(z, u₁ z)‖ ‖∂t η‖ + ‖A(z) - A₁(z)‖ ‖η‖`, where `A = ∂t J - C` is the
zeroth-order coefficient of the Cauchy–Riemann form `floerLinearizationAdjoint_eq_neg`. This is the
adjoint counterpart of `norm_floerLinearization_sub_floerLinearization_le`. -/
theorem norm_floerLinearizationAdjoint_sub_floerLinearizationAdjoint_le
    {J₁ : ℝ × ℝ → V → V →L[ℝ] V} {Ks₁ Kt₁ : ℝ × ℝ → V → ℝ} {u₁ : ℝ × ℝ → V}
    (hη : DifferentiableAt ℝ η z) (hJu : DifferentiableAt ℝ (fun w ↦ J w (u w)) z)
    (hJu₁ : DifferentiableAt ℝ (fun w ↦ J₁ w (u₁ w)) z) :
    ‖ω.floerLinearizationAdjoint J Ks Kt u η z - ω.floerLinearizationAdjoint J₁ Ks₁ Kt₁ u₁ η z‖ ≤
      ‖J z (u z) - J₁ z (u₁ z)‖ * ‖fderiv ℝ η z stdComplexLineImag‖ +
        ‖(fderiv ℝ (fun w ↦ J w (u w)) z stdComplexLineImag -
              ω.floerLinearizationCoeff J Ks Kt u z) -
            (fderiv ℝ (fun w ↦ J₁ w (u₁ w)) z stdComplexLineImag -
              ω.floerLinearizationCoeff J₁ Ks₁ Kt₁ u₁ z)‖ * ‖η z‖ := by
  rw [floerLinearizationAdjoint_eq_neg hη hJu, floerLinearizationAdjoint_eq_neg hη hJu₁,
    show ∀ a b c b' c' : V →L[ℝ] ℝ, -(a + b + c) - -(a + b' + c') = -((b - b') + (c - c')) by
      intro a b c b' c'; abel, norm_neg, ← comp_sub, ← comp_sub]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;>
    exact (opNorm_comp_le _ _).trans_eq (mul_comm _ _)

/-- **Multiplying by a function.** If `f` and `η` are differentiable at `z`, the formal adjoint
sends `f η` to `f D^* η - (∂s f) η - (∂t f) (η ∘ J(z, u z))`: the leading terms `-∂s η` and
`-∂t (η ∘ J)` differentiate the factor. This is the adjoint counterpart of
`floerLinearization_fun_smul`. -/
theorem floerLinearizationAdjoint_fun_smul {f : ℝ × ℝ → ℝ} (hf : DifferentiableAt ℝ f z)
    (hη : DifferentiableAt ℝ η z) (hJu : DifferentiableAt ℝ (fun w ↦ J w (u w)) z) :
    ω.floerLinearizationAdjoint J Ks Kt u (fun w ↦ f w • η w) z =
      f z • ω.floerLinearizationAdjoint J Ks Kt u η z - fderiv ℝ f z stdComplexLineReal • η z -
        fderiv ℝ f z stdComplexLineImag • (η z).comp (J z (u z)) := by
  have hd : HasFDerivAt (fun w ↦ f w • η w) _ z := hf.hasFDerivAt.smul hη.hasFDerivAt
  have hc : (fun w ↦ (f w • η w).comp (J w (u w))) = fun w ↦ f w • (η w).comp (J w (u w)) := by
    ext w
    simp
  have hdc : HasFDerivAt (fun w ↦ f w • (η w).comp (J w (u w))) _ z :=
    hf.hasFDerivAt.smul (hη.clm_comp hJu).hasFDerivAt
  rw [floerLinearizationAdjoint_def, hd.fderiv, hc, hdc.fderiv, floerLinearizationAdjoint_def]
  simp only [add_apply, smul_apply, smulRight_apply, smul_comp]
  module

/-- **Multiplying by a function of `s`.** If `β` has derivative `β'` at `s`, the formal adjoint at
`z = (s, t)` sends `β(s) η` to `β(s) D^* η - β' η`: the factor only differentiates in the `s`
direction, where the adjoint has the leading term `-∂s`. This is the case `f(s, t) = β(s)` of
`floerLinearizationAdjoint_fun_smul`. -/
theorem floerLinearizationAdjoint_smul_fst {β : ℝ → ℝ} {β' : ℝ} (hβ : HasDerivAt β β' z.1)
    (hη : DifferentiableAt ℝ η z) (hJu : DifferentiableAt ℝ (fun w ↦ J w (u w)) z) :
    ω.floerLinearizationAdjoint J Ks Kt u (fun w ↦ β w.1 • η w) z =
      β z.1 • ω.floerLinearizationAdjoint J Ks Kt u η z - β' • η z := by
  have hb : HasFDerivAt (fun w : ℝ × ℝ ↦ β w.1) _ z := hβ.hasFDerivAt.comp z hasFDerivAt_fst
  rw [floerLinearizationAdjoint_fun_smul hb.differentiableAt hη hJu, hb.fderiv]
  simp [stdComplexLineReal_fst, stdComplexLineImag_fst]

/-- **The adjoint on a cut-off covector field, pointwise.** At a point where `f`, `η` and
`w ↦ J(w, u w)` are differentiable, `‖D^* (f η)‖ ≤ |f| ‖D^* η‖ + ‖df‖ (1 + ‖J‖) ‖η‖`. -/
theorem norm_floerLinearizationAdjoint_fun_smul_le {f : ℝ × ℝ → ℝ} (hf : DifferentiableAt ℝ f z)
    (hη : DifferentiableAt ℝ η z) (hJu : DifferentiableAt ℝ (fun w ↦ J w (u w)) z) :
    ‖ω.floerLinearizationAdjoint J Ks Kt u (fun w ↦ f w • η w) z‖ ≤
      |f z| * ‖ω.floerLinearizationAdjoint J Ks Kt u η z‖ +
        ‖fderiv ℝ f z‖ * (1 + ‖J z (u z)‖) * ‖η z‖ := by
  have hre : ‖fderiv ℝ f z stdComplexLineReal‖ ≤ ‖fderiv ℝ f z‖ :=
    (le_opNorm _ _).trans (by simp [stdComplexLineReal])
  have him : ‖fderiv ℝ f z stdComplexLineImag‖ ≤ ‖fderiv ℝ f z‖ :=
    (le_opNorm _ _).trans (by simp [stdComplexLineImag])
  have hJ : ‖(η z).comp (J z (u z))‖ ≤ ‖J z (u z)‖ * ‖η z‖ :=
    (opNorm_comp_le _ _).trans_eq (mul_comm _ _)
  rw [floerLinearizationAdjoint_fun_smul hf hη hJu, sub_sub]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs]
  have h := norm_add_le (fderiv ℝ f z stdComplexLineReal • η z)
    (fderiv ℝ f z stdComplexLineImag • (η z).comp (J z (u z)))
  rw [norm_smul, norm_smul] at h
  have h₁ := mul_le_mul_of_nonneg_right hre (norm_nonneg (η z))
  have h₂ := mul_le_mul hJ him (norm_nonneg _) (by positivity)
  nlinarith [norm_nonneg (fderiv ℝ f z), norm_nonneg (η z), norm_nonneg (J z (u z))]

/-- **The formal adjoint on a cut-off covector field, pointwise.** If `|f| ≤ 1`, `‖df‖ ≤ M` and
`‖J‖ ≤ B` at `z`, then `‖D^* (f η)‖² ≤ 2 ‖D^* η‖² + 2 (M (1 + B))² ‖η‖²` at `z`. This is the
adjoint counterpart of `norm_floerLinearization_fun_smul_sq_le`. -/
theorem norm_floerLinearizationAdjoint_fun_smul_sq_le {f : ℝ × ℝ → ℝ}
    (hf : DifferentiableAt ℝ f z) (hη : DifferentiableAt ℝ η z)
    (hJu : DifferentiableAt ℝ (fun w ↦ J w (u w)) z) (hf₁ : |f z| ≤ 1) {M B : ℝ}
    (hM : ‖fderiv ℝ f z‖ ≤ M) (hB : ‖J z (u z)‖ ≤ B) :
    ‖ω.floerLinearizationAdjoint J Ks Kt u (fun w ↦ f w • η w) z‖ ^ 2 ≤
      2 * ‖ω.floerLinearizationAdjoint J Ks Kt u η z‖ ^ 2 + 2 * (M * (1 + B)) ^ 2 * ‖η z‖ ^ 2 := by
  have hM₀ : 0 ≤ M := (norm_nonneg _).trans hM
  have h₁ : ‖fderiv ℝ f z stdComplexLineReal • η z‖ ≤ M * ‖η z‖ := by
    rw [norm_smul]
    gcongr
    exact (le_opNorm _ _).trans (by simp [stdComplexLineReal, hM])
  have h₂ : ‖fderiv ℝ f z stdComplexLineImag • (η z).comp (J z (u z))‖ ≤ M * (B * ‖η z‖) := by
    rw [norm_smul]
    gcongr
    · exact (le_opNorm _ _).trans (by simp [stdComplexLineImag, hM])
    · exact (opNorm_comp_le _ _).trans (by rw [mul_comm]; gcongr)
  rw [floerLinearizationAdjoint_fun_smul hf hη hJu, sub_eq_add_neg, sub_eq_add_neg]
  exact norm_smul_add_add_sq_le hf₁ ((norm_neg _).trans_le h₁) ((norm_neg _).trans_le h₂)

/-- **Conjugating the formal adjoint by an exponential weight.** On covector fields of the form
`e^{δ s} η`, the formal adjoint acts as `e^{δ s} (D^* - δ) η`. This is the dual of
`floerLinearization_exp_smul`, where the weight `e^{-δ s}` turns `D` into `D - δ`. -/
theorem floerLinearizationAdjoint_exp_smul (δ : ℝ) (hη : DifferentiableAt ℝ η z)
    (hJu : DifferentiableAt ℝ (fun w ↦ J w (u w)) z) :
    ω.floerLinearizationAdjoint J Ks Kt u (fun w ↦ Real.exp (δ * w.1) • η w) z =
      Real.exp (δ * z.1) • (ω.floerLinearizationAdjoint J Ks Kt u η z - δ • η z) := by
  have hβ : HasDerivAt (fun s ↦ Real.exp (δ * s)) (Real.exp (δ * z.1) * δ) z.1 := by
    simpa using ((hasDerivAt_id z.1).const_mul δ).exp
  rw [floerLinearizationAdjoint_smul_fst hβ hη hJu, smul_sub, smul_smul]

/-! ### Green's formula -/

/-- **The pointwise Green identity.** For a map `ξ`, a covector field `η` and `w ↦ J(w, u w)`
differentiable at `z`,
`η(D ξ) = (D^* η)(ξ) + ∂s (η(ξ)) + ∂t ((η ∘ J)(ξ))`. -/
theorem apply_floerLinearization_eq_floerLinearizationAdjoint_apply_add
    (hξ : DifferentiableAt ℝ ξ z) (hη : DifferentiableAt ℝ η z)
    (hJu : DifferentiableAt ℝ (fun w ↦ J w (u w)) z) :
    η z (ω.floerLinearization J Ks Kt u ξ z) =
      ω.floerLinearizationAdjoint J Ks Kt u η z (ξ z) +
        fderiv ℝ (fun w ↦ η w (ξ w)) z stdComplexLineReal +
        fderiv ℝ (fun w ↦ (η w).comp (J w (u w)) (ξ w)) z stdComplexLineImag := by
  rw [fderiv_clm_apply hη hξ, fderiv_clm_apply (hη.clm_comp hJu) hξ,
    floerLinearization_eq_add, floerLinearizationAdjoint_def]
  simp only [map_add, add_apply, sub_apply, neg_apply, comp_apply, flip_apply]
  abel

/-- **Continuity of the formal adjoint.** Let `u` and the covector field `η` be `C¹` at `z`, and
let the coefficients `J` be `C¹` and the Hamiltonians `K_s`, `K_t` be `C²` at `(z, u z)`. Then the
formal adjoint `D^* η` is continuous at `z`. -/
theorem continuousAt_floerLinearizationAdjoint
    (hJ : ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z)) (hu : ContDiffAt ℝ 1 u z)
    (hη : ContDiffAt ℝ 1 η z) :
    ContinuousAt (ω.floerLinearizationAdjoint J Ks Kt u η) z := by
  have hA : ContDiffAt ℝ 1 (fun w ↦ (η w).comp (J w (u w))) z :=
    hη.clm_comp (hJ.comp₂ contDiffAt_id hu)
  rw [show ω.floerLinearizationAdjoint J Ks Kt u η = _ from
    funext (ω.floerLinearizationAdjoint_def J Ks Kt u η)]
  exact (((hη.continuousAt_fderiv one_ne_zero).clm_apply continuousAt_const).neg.sub
    ((hA.continuousAt_fderiv one_ne_zero).clm_apply continuousAt_const)).add
    (hη.continuousAt.clm_comp (ω.continuousAt_floerLinearizationCoeff hJ hKs hKt hu))

/-- **Global continuity of the formal adjoint.** Let `u` be `C¹` and the covector field `η` be
`C¹`, and let the coefficients `J` be `C¹` and the Hamiltonians `K_s`, `K_t` be `C²` at every point
`(z, u z)`. Then the formal adjoint `D^* η` is continuous. This is the adjoint counterpart of
`continuous_floerLinearization`. -/
theorem continuous_floerLinearizationAdjoint
    (hJ : ∀ z, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z)) (hu : ContDiff ℝ 1 u)
    (hη : ContDiff ℝ 1 η) : Continuous (ω.floerLinearizationAdjoint J Ks Kt u η) :=
  continuous_iff_continuousAt.2 fun z ↦
    continuousAt_floerLinearizationAdjoint (hJ z) (hKs z) (hKt z) hu.contDiffAt hη.contDiffAt

/-- The formal adjoint on a covector field `η` supported in a set `U` is continuous when `η` is
`C¹` and the data are regular along `u` on `U`. This is the adjoint counterpart of
`continuous_floerLinearization_of_tsupport_subset`. -/
theorem continuous_floerLinearizationAdjoint_of_tsupport_subset {U : Set (ℝ × ℝ)}
    (hJ : ∀ z ∈ U, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z ∈ U, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ U, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z))
    (hu : ∀ z ∈ U, ContDiffAt ℝ 1 u z) (hη : ContDiff ℝ 1 η) (hηU : tsupport η ⊆ U) :
    Continuous (ω.floerLinearizationAdjoint J Ks Kt u η) := by
  refine continuous_iff_continuousAt.2 fun z ↦ ?_
  by_cases hz : z ∈ U
  · exact continuousAt_floerLinearizationAdjoint (hJ z hz) (hKs z hz) (hKt z hz) (hu z hz)
      hη.contDiffAt
  · have h : ω.floerLinearizationAdjoint J Ks Kt u η =ᶠ[𝓝 z] fun _ ↦ 0 :=
      Filter.mem_of_superset ((isClosed_tsupport η).isOpen_compl.mem_nhds fun h ↦ hz (hηU h))
        fun w hw ↦ floerLinearizationAdjoint_of_notMem_tsupport hw
    exact continuousAt_const.congr h.symm

/-- For a `C¹` covector field `θ` supported in the support of a covector field `η` with compact
support in an open set `S`, on which the data are regular along `u`, and a weight `w` continuous on
`S`, the `w`-weighted square norm of `D^* θ` is integrable. For `θ = η` the right side
`∫ w ‖D^* η‖²` of a weighted semi-Fredholm estimate of the formal adjoint is finite. -/
theorem integrable_mul_norm_floerLinearizationAdjoint_sq (ω : SymplecticForm V)
    {S : Set (ℝ × ℝ)} (hS : IsOpen S)
    (hJ : ∀ z ∈ S, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z ∈ S, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ S, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z))
    (hu : ∀ z ∈ S, ContDiffAt ℝ 1 u z) {w : ℝ × ℝ → ℝ} (hwc : ContinuousOn w S)
    {θ : ℝ × ℝ → V →L[ℝ] ℝ} (hθ : ContDiff ℝ 1 θ) (hθη : tsupport θ ⊆ tsupport η)
    (hηc : HasCompactSupport η) (hηS : tsupport η ⊆ S) :
    Integrable fun z ↦ w z * ‖ω.floerLinearizationAdjoint J Ks Kt u θ z‖ ^ 2 := by
  have hg : Continuous fun z ↦ ‖ω.floerLinearizationAdjoint J Ks Kt u θ z‖ ^ 2 :=
    (continuous_floerLinearizationAdjoint_of_tsupport_subset hJ hKs hKt hu hθ
      (hθη.trans hηS)).norm.pow 2
  -- The integrand vanishes off the compact set `tsupport η ⊆ S`.
  have hzero (z : ℝ × ℝ) (hz : z ∉ tsupport η) :
      w z * ‖ω.floerLinearizationAdjoint J Ks Kt u θ z‖ ^ 2 = 0 := by
    simp [floerLinearizationAdjoint_of_notMem_tsupport fun h ↦ hz (hθη h)]
  have hsupp :
      Function.support (fun z ↦ w z * ‖ω.floerLinearizationAdjoint J Ks Kt u θ z‖ ^ 2) ⊆
        tsupport η := fun z hz ↦ by_contra fun h ↦ hz (hzero z h)
  exact (ContinuousOn.continuous_of_tsupport_subset (hwc.mul hg.continuousOn) hS
    ((closure_minimal hsupp (isClosed_tsupport η)).trans hηS)).integrable_of_hasCompactSupport
    (HasCompactSupport.intro hηc.isCompact hzero)

/-- **The cost of a cutoff for the formal adjoint.** Let `w ≥ 0` be a continuous weight and `β` a
`C¹` function with values in `[0, 1]` whose derivative vanishes off a compact set `K`. Then
multiplying a `C¹` covector field `η` of compact support by `β` gives a field whose formal adjoint
has `w`-weighted squared `L²` norm at most twice that of `D^* η` plus a multiple of the squared
`L²` norm of `η` over `K`:
`∫ w ‖D^* (β η)‖² ≤ 2 ∫ w ‖D^* η‖² + C ∫_K ‖η‖²`. This is the weighted adjoint counterpart of
`exists_integral_norm_floerLinearization_smul_sq_le`. -/
theorem exists_integral_mul_norm_floerLinearizationAdjoint_smul_sq_le (ω : SymplecticForm V)
    (hJ : ∀ z, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z)) (hu : ContDiff ℝ 1 u)
    {w : ℝ × ℝ → ℝ} (hw : ∀ z, 0 ≤ w z) (hwc : Continuous w) {β : ℝ × ℝ → ℝ}
    (hβ : ContDiff ℝ 1 β) (hβ1 : ∀ z, β z ∈ Icc 0 1) {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hβK : ∀ z ∉ K, fderiv ℝ β z = 0) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 1 η → HasCompactSupport η →
      ∫ z, w z * ‖ω.floerLinearizationAdjoint J Ks Kt u (fun z ↦ β z • η z) z‖ ^ 2 ≤
        2 * (∫ z, w z * ‖ω.floerLinearizationAdjoint J Ks Kt u η z‖ ^ 2) +
          C * ∫ z in K, ‖η z‖ ^ 2 := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (continuous_comp_prodMk_of_continuousAt
    (fun z ↦ (hJ z).continuousAt) hu.continuous).continuousOn
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hβ.continuous_fderiv one_ne_zero).continuousOn
  obtain ⟨Λ, hΛ⟩ := hK.exists_bound_of_continuousOn hwc.continuousOn
  refine ⟨2 * (max M 0 * (1 + max B 0)) ^ 2 * max Λ 0, by positivity, fun η hη hηc ↦ ?_⟩
  have hint {θ : ℝ × ℝ → V →L[ℝ] ℝ} (hθ : ContDiff ℝ 1 θ) (hθη : tsupport θ ⊆ tsupport η) :
      Integrable fun z ↦ w z * ‖ω.floerLinearizationAdjoint J Ks Kt u θ z‖ ^ 2 :=
    ω.integrable_mul_norm_floerLinearizationAdjoint_sq isOpen_univ (fun z _ ↦ hJ z)
      (fun z _ ↦ hKs z) (fun z _ ↦ hKt z) (fun z _ ↦ hu.contDiffAt) hwc.continuousOn hθ hθη hηc
      (subset_univ _)
  refine integral_mul_norm_fun_smul_sq_le (D := ω.floerLinearizationAdjoint J Ks Kt u)
    (S := univ) (f := β) (b := fun z ↦ ‖J z (u z)‖) (ξ := η) hw hK
    (fun z _ h ↦ by_contra fun hz ↦ h (hβK z hz)) (fun z hz ↦ (hM z hz).trans (le_max_left _ _))
    (fun z hz ↦ (hB z hz).trans (le_max_left _ _)) (le_max_right _ _)
    (fun z hz ↦ (Real.le_norm_self _).trans ((hΛ z hz).trans (le_max_left _ _))) hη.continuous
    (fun z _ _ _ hM' hB' ↦ ?_) (fun z hz ↦ (hz (mem_univ z)).elim) (hint hη subset_rfl)
    (hint (hβ.smul hη) (tsupport_smul_subset_right _ _))
  exact norm_floerLinearizationAdjoint_fun_smul_sq_le (hβ.differentiable one_ne_zero z)
    (hη.differentiable one_ne_zero z)
    (((hJ z).differentiableAt one_ne_zero).comp (f := fun w ↦ (w, u w)) z
      (differentiableAt_id.prodMk ((hu.differentiable one_ne_zero) z)))
    (abs_le.2 ⟨by linarith [(hβ1 z).1], (hβ1 z).2⟩) hM' hB'

/-- Off the common topological support of `η` and `ξ`, the pairings `η(D ξ)`, `(D^* η)(ξ)`,
`η(ξ)` and `(η ∘ J)(ξ)` all vanish near the point. -/
private theorem eventually_notMem_tsupport_inter (hz : z ∉ tsupport η ∩ tsupport ξ) :
    ∀ᶠ w in 𝓝 z, η w (ω.floerLinearization J Ks Kt u ξ w) = 0 ∧
      ω.floerLinearizationAdjoint J Ks Kt u η w (ξ w) = 0 ∧ η w (ξ w) = 0 ∧
        (η w).comp (J w (u w)) (ξ w) = 0 := by
  filter_upwards [((isClosed_tsupport η).inter (isClosed_tsupport ξ)).isOpen_compl.mem_nhds hz]
    with w hw
  rcases not_and_or.1 hw with h | h
  · simp [floerLinearizationAdjoint_of_notMem_tsupport (ω := ω) (J := J) (Ks := Ks) (Kt := Kt)
      (u := u) h, image_eq_zero_of_notMem_tsupport h]
  · rw [ω.floerLinearization_congr_of_eventuallyEq J Ks Kt u
      (notMem_tsupport_iff_eventuallyEq.1 h)]
    simp [image_eq_zero_of_notMem_tsupport h]

/-- **Green's formula over the plane.** Let the common topological support of the covector field
`η` and the map `ξ` be compact, and on it let `u`, `η` and `ξ` be `C¹`, the coefficients `J` be
`C¹` and the Hamiltonians `K_s`, `K_t` be `C²` (at `(z, u z)` for the coefficients). Then
`∫ η(D ξ) = ∫ (D^* η)(ξ)` over the whole plane. This covers both a compactly supported `ξ` paired
with any `η` that is `C¹` near its support, and a compactly supported `η` paired with any `ξ` that
is `C¹` near the support of `η`. -/
theorem integral_apply_floerLinearization_eq_integral_floerLinearizationAdjoint_apply
    (hJ : ∀ z ∈ tsupport η ∩ tsupport ξ, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z ∈ tsupport η ∩ tsupport ξ, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ tsupport η ∩ tsupport ξ, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z))
    (hu : ∀ z ∈ tsupport η ∩ tsupport ξ, ContDiffAt ℝ 1 u z)
    (hη : ∀ z ∈ tsupport η ∩ tsupport ξ, ContDiffAt ℝ 1 η z)
    (hξ : ∀ z ∈ tsupport η ∩ tsupport ξ, ContDiffAt ℝ 1 ξ z)
    (hc : IsCompact (tsupport η ∩ tsupport ξ)) :
    ∫ z, η z (ω.floerLinearization J Ks Kt u ξ z) =
      ∫ z, ω.floerLinearizationAdjoint J Ks Kt u η z (ξ z) := by
  set K := tsupport η ∩ tsupport ξ
  have hK : IsClosed K := (isClosed_tsupport η).inter (isClosed_tsupport ξ)
  have hev {z : ℝ × ℝ} (hz : z ∉ K) :=
    eventually_notMem_tsupport_inter (ω := ω) (J := J) (Ks := Ks) (Kt := Kt) (u := u) hz
  have hJu (z : ℝ × ℝ) (hz : z ∈ K) : ContDiffAt ℝ 1 (fun w ↦ J w (u w)) z :=
    (hJ z hz).comp₂ contDiffAt_id (hu z hz)
  -- The two divergence terms of the pointwise Green formula are derivatives of compactly
  -- supported `C¹` functions, so they integrate to zero.
  set F : ℝ × ℝ → ℝ := fun w ↦ η w (ξ w)
  set G : ℝ × ℝ → ℝ := fun w ↦ (η w).comp (J w (u w)) (ξ w)
  have hF : ContDiff ℝ 1 F := contDiff_iff_contDiffAt.2 fun z ↦ by
    by_cases hz : z ∈ K
    · exact (hη z hz).clm_apply (hξ z hz)
    · exact contDiffAt_const.congr_of_eventuallyEq ((hev hz).mono fun _ hw ↦ hw.2.2.1)
  have hG : ContDiff ℝ 1 G := contDiff_iff_contDiffAt.2 fun z ↦ by
    by_cases hz : z ∈ K
    · exact ((hη z hz).clm_comp (hJu z hz)).clm_apply (hξ z hz)
    · exact contDiffAt_const.congr_of_eventuallyEq ((hev hz).mono fun _ hw ↦ hw.2.2.2)
  have hFc : HasCompactSupport F := .intro' hc hK fun _ hz ↦ (hev hz).self_of_nhds.2.2.1
  have hGc : HasCompactSupport G := .intro' hc hK fun _ hz ↦ (hev hz).self_of_nhds.2.2.2
  -- The term `(D^* η)(ξ)` is continuous with compact support.
  have hT : Integrable fun z ↦ ω.floerLinearizationAdjoint J Ks Kt u η z (ξ z) := by
    refine Continuous.integrable_of_hasCompactSupport (continuous_iff_continuousAt.2 fun z ↦ ?_)
      (.intro' hc hK fun _ hz ↦ (hev hz).self_of_nhds.2.1)
    by_cases hz : z ∈ K
    · exact (continuousAt_floerLinearizationAdjoint (hJ z hz) (hKs z hz) (hKt z hz) (hu z hz)
        (hη z hz)).clm_apply (hξ z hz).continuousAt
    · exact continuousAt_const.congr ((hev hz).mono fun _ hw ↦ hw.2.1.symm)
  -- The pointwise Green formula holds everywhere.
  have hpt (z : ℝ × ℝ) : η z (ω.floerLinearization J Ks Kt u ξ z) =
      ω.floerLinearizationAdjoint J Ks Kt u η z (ξ z) + fderiv ℝ F z stdComplexLineReal +
        fderiv ℝ G z stdComplexLineImag := by
    by_cases hz : z ∈ K
    · exact apply_floerLinearization_eq_floerLinearizationAdjoint_apply_add
        ((hξ z hz).differentiableAt one_ne_zero) ((hη z hz).differentiableAt one_ne_zero)
        ((hJu z hz).differentiableAt one_ne_zero)
    · have hF0 : F =ᶠ[𝓝 z] fun _ ↦ 0 := (hev hz).mono fun _ hw ↦ hw.2.2.1
      have hG0 : G =ᶠ[𝓝 z] fun _ ↦ 0 := (hev hz).mono fun _ hw ↦ hw.2.2.2
      rw [(hev hz).self_of_nhds.1, (hev hz).self_of_nhds.2.1, hF0.fderiv_eq, hG0.fderiv_eq]
      simp
  simp_rw [hpt]
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  have hdF : Integrable fun z ↦ fderiv ℝ F z stdComplexLineReal :=
    integrable_fderiv_apply_of_hasCompactSupport (μ := volume) hF hFc _
  have hdG : Integrable fun z ↦ fderiv ℝ G z stdComplexLineImag :=
    integrable_fderiv_apply_of_hasCompactSupport (μ := volume) hG hGc _
  rw [integral_add (hT.fun_add hdF) hdG, integral_add hT hdF,
    integral_fderiv_apply_eq_zero_of_hasCompactSupport (μ := volume) hF hFc,
    integral_fderiv_apply_eq_zero_of_hasCompactSupport (μ := volume) hG hGc, add_zero, add_zero]

/-- **Green's formula on a rectangle.** On the closed rectangle `R = [a₁, b₁] × [a₂, b₂]` let `u`,
the covector field `η` and the map `ξ` be `C¹`, the coefficients `J` be `C¹` and the Hamiltonians
`K_s`, `K_t` be `C²` (at `(z, u z)` for the coefficients). If the pairing `η(ξ)` takes equal values
on the vertical sides `s = a₁` and `s = b₁`, and `(η ∘ J)(ξ)` takes equal values on the horizontal
sides `t = a₂` and `t = b₂`, then `∫ η(D ξ) = ∫ (D^* η)(ξ)` over `R`. On the fundamental domain
`[a, b] × [0, 1]` of the cylinder, both side conditions hold when `ξ` vanishes at `s = a, b` and
`η`, `ξ` and `J(·, u ·)` have period one in `t`. -/
theorem setIntegral_apply_floerLinearization_eq_setIntegral_floerLinearizationAdjoint_apply
    {a₁ b₁ a₂ b₂ : ℝ}
    (hJ : ∀ z ∈ Icc a₁ b₁ ×ˢ Icc a₂ b₂, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z ∈ Icc a₁ b₁ ×ˢ Icc a₂ b₂, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ Icc a₁ b₁ ×ˢ Icc a₂ b₂, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z))
    (hu : ∀ z ∈ Icc a₁ b₁ ×ˢ Icc a₂ b₂, ContDiffAt ℝ 1 u z)
    (hη : ∀ z ∈ Icc a₁ b₁ ×ˢ Icc a₂ b₂, ContDiffAt ℝ 1 η z)
    (hξ : ∀ z ∈ Icc a₁ b₁ ×ˢ Icc a₂ b₂, ContDiffAt ℝ 1 ξ z)
    (hvert : ∀ t ∈ Icc a₂ b₂, η (b₁, t) (ξ (b₁, t)) = η (a₁, t) (ξ (a₁, t)))
    (hhor : ∀ s ∈ Icc a₁ b₁, η (s, b₂) (J (s, b₂) (u (s, b₂)) (ξ (s, b₂))) =
      η (s, a₂) (J (s, a₂) (u (s, a₂)) (ξ (s, a₂)))) :
    ∫ z in Icc a₁ b₁ ×ˢ Icc a₂ b₂, η z (ω.floerLinearization J Ks Kt u ξ z) =
      ∫ z in Icc a₁ b₁ ×ˢ Icc a₂ b₂, ω.floerLinearizationAdjoint J Ks Kt u η z (ξ z) := by
  rcases lt_or_ge b₁ a₁ with h₁ | h₁
  · simp [Icc_eq_empty_of_lt h₁]
  rcases lt_or_ge b₂ a₂ with h₂ | h₂
  · simp [Icc_eq_empty_of_lt h₂]
  set R := Icc a₁ b₁ ×ˢ Icc a₂ b₂
  have hR : IsCompact R := isCompact_Icc.prod isCompact_Icc
  have hJu (z : ℝ × ℝ) (hz : z ∈ R) : ContDiffAt ℝ 1 (fun w ↦ J w (u w)) z :=
    (hJ z hz).comp₂ contDiffAt_id (hu z hz)
  set F : ℝ × ℝ → ℝ := fun w ↦ η w (ξ w)
  set G : ℝ × ℝ → ℝ := fun w ↦ (η w).comp (J w (u w)) (ξ w)
  have hF (z : ℝ × ℝ) (hz : z ∈ R) : ContDiffAt ℝ 1 F z := (hη z hz).clm_apply (hξ z hz)
  have hG (z : ℝ × ℝ) (hz : z ∈ R) : ContDiffAt ℝ 1 G z :=
    ((hη z hz).clm_comp (hJu z hz)).clm_apply (hξ z hz)
  have hT : ContinuousOn (fun z ↦ ω.floerLinearizationAdjoint J Ks Kt u η z (ξ z)) R :=
    fun z hz ↦ ((continuousAt_floerLinearizationAdjoint (hJ z hz) (hKs z hz) (hKt z hz)
      (hu z hz) (hη z hz)).clm_apply (hξ z hz).continuousAt).continuousWithinAt
  have hdiv : ContinuousOn
      (fun z ↦ fderiv ℝ F z stdComplexLineReal + fderiv ℝ G z stdComplexLineImag) R :=
    fun z hz ↦ ((((hF z hz).continuousAt_fderiv one_ne_zero).clm_apply continuousAt_const).add
      (((hG z hz).continuousAt_fderiv one_ne_zero).clm_apply continuousAt_const)).continuousWithinAt
  -- By the divergence theorem, the divergence terms integrate to the differences of the values on
  -- opposite sides, which vanish.
  have hint :
      ∫ z in R, (fderiv ℝ F z stdComplexLineReal + fderiv ℝ G z stdComplexLineImag) = 0 := by
    have hRI : R = Icc (a₁, a₂) (b₁, b₂) := Icc_prod_Icc a₁ b₁ a₂ b₂
    have hsub : Ioo a₁ b₁ ×ˢ Ioo a₂ b₂ ⊆ R := prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
    rw [hRI] at hR hdiv ⊢
    rw [stdComplexLineReal_eq, stdComplexLineImag_eq,
      integral_divergence_prod_Icc_of_hasFDerivAt_of_le F G (fderiv ℝ F) (fderiv ℝ G) _ _ ⟨h₁, h₂⟩
        (fun z hz ↦ (hF z (hRI ▸ hz)).continuousAt.continuousWithinAt)
        (fun z hz ↦ (hG z (hRI ▸ hz)).continuousAt.continuousWithinAt)
        (fun z hz ↦ ((hF z (hsub hz)).differentiableAt one_ne_zero).hasFDerivAt)
        (fun z hz ↦ ((hG z (hsub hz)).differentiableAt one_ne_zero).hasFDerivAt)
        (hdiv.integrableOn_compact hR)]
    dsimp only
    rw [intervalIntegral.integral_congr (f := fun s ↦ G (s, b₂)) (g := fun s ↦ G (s, a₂))
        fun s hs ↦ hhor s (uIcc_of_le h₁ ▸ hs),
      intervalIntegral.integral_congr (f := fun t ↦ F (b₁, t)) (g := fun t ↦ F (a₁, t))
        fun t ht ↦ hvert t (uIcc_of_le h₂ ▸ ht)]
    simp
  rw [setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc) fun z hz ↦
      (apply_floerLinearization_eq_floerLinearizationAdjoint_apply_add
        ((hξ z hz).differentiableAt one_ne_zero) ((hη z hz).differentiableAt one_ne_zero)
        ((hJu z hz).differentiableAt one_ne_zero)).trans (add_assoc _ _ _),
    integral_add (hT.integrableOn_compact hR) (hdiv.integrableOn_compact hR), hint, add_zero]

/-! ### Classical cokernel elements -/

/-- **`C¹` cokernel elements solve the adjoint equation.** Let `U` be open, and let `u` and the
covector field `η` be `C¹`, the coefficients `J` be `C¹` and the Hamiltonians `K_s`, `K_t` be `C²`,
at each point of `U` (at `(z, u z)` for the coefficients). Then `η` annihilates `D ξ`, for the
pairing `∫ η(D ξ)`, for every smooth map `ξ` compactly supported in `U`, exactly when
`D^* η = 0` on `U`. No compatibility of `J` with `ω` is needed. -/
theorem forall_integral_apply_floerLinearization_eq_zero_iff {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hJ : ∀ z ∈ U, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z ∈ U, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ U, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z))
    (hu : ∀ z ∈ U, ContDiffAt ℝ 1 u z) (hη : ∀ z ∈ U, ContDiffAt ℝ 1 η z) :
    (∀ ξ : ℝ × ℝ → V, ContDiff ℝ (⊤ : ℕ∞) ξ → HasCompactSupport ξ → tsupport ξ ⊆ U →
      ∫ z, η z (ω.floerLinearization J Ks Kt u ξ z) = 0) ↔
      EqOn (ω.floerLinearizationAdjoint J Ks Kt u η) 0 U := by
  set f := ω.floerLinearizationAdjoint J Ks Kt u η
  have hGreen (ξ : ℝ × ℝ → V) (hξ : ContDiff ℝ (⊤ : ℕ∞) ξ) (hξc : HasCompactSupport ξ)
      (hξU : tsupport ξ ⊆ U) :
      ∫ z, η z (ω.floerLinearization J Ks Kt u ξ z) = ∫ z, f z (ξ z) :=
    integral_apply_floerLinearization_eq_integral_floerLinearizationAdjoint_apply
      (fun z hz ↦ hJ z (hξU hz.2)) (fun z hz ↦ hKs z (hξU hz.2)) (fun z hz ↦ hKt z (hξU hz.2))
      (fun z hz ↦ hu z (hξU hz.2)) (fun z hz ↦ hη z (hξU hz.2))
      (fun _ _ ↦ (hξ.of_le (by simp)).contDiffAt) (hξc.isCompact.inter_left (isClosed_tsupport η))
  refine ⟨fun h ↦ ?_, fun h ξ hξ hξc hξU ↦ ?_⟩
  · have hf : ContinuousOn f U := fun z hz ↦
      (continuousAt_floerLinearizationAdjoint (hJ z hz) (hKs z hz) (hKt z hz) (hu z hz)
        (hη z hz)).continuousWithinAt
    -- Testing against `ξ = φ v` shows that each component `(D^* η)(v)` vanishes on `U`.
    have hv (v : V) : EqOn (fun z ↦ f z v) 0 U := by
      have hF : ContinuousOn (fun z ↦ f z v) U := hf.clm_apply continuousOn_const
      have hae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
        (hF.locallyIntegrableOn hU.measurableSet) fun φ hφ hφc hφU ↦ by
          have hξ : ContDiff ℝ (⊤ : ℕ∞) fun z ↦ φ z • v := hφ.smul contDiff_const
          have hξc : HasCompactSupport fun z ↦ φ z • v := hφc.smul_right (f' := fun _ ↦ v)
          have hξU : tsupport (fun z ↦ φ z • v) ⊆ U :=
            (tsupport_smul_subset_left φ fun _ ↦ v).trans hφU
          have h₀ := h _ hξ hξc hξU
          rw [hGreen _ hξ hξc hξU] at h₀
          simpa [smul_eq_mul] using h₀
      exact Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' hU.measurableSet).2 hae) hU
        hF continuousOn_const
    exact fun z hz ↦ ContinuousLinearMap.ext fun v ↦ hv v hz
  · rw [hGreen ξ hξ hξc hξU]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun z ↦ ?_)
    by_cases hz : z ∈ tsupport ξ
    · simp [h (hξU hz)]
    · simp [image_eq_zero_of_notMem_tsupport hz]

/-! ### The zeroth-order coefficient for cylindrical data -/

/-- The zeroth-order coefficient `A = ∂t J - C` of the Cauchy–Riemann form
`floerLinearizationAdjoint_eq_neg` of the formal adjoint, for the cylindrical datum
`(J_t, 0, H_t)`, as a function of the time `t`, the value `y = w(z)` and the slice velocity
`d = ∂t w(z)` of the map:

`A(t, y, d) = dJ_{(t, y)}(1, d) - (dJ_t(y) (·)) (d - X_{H_t}(y)) + J_t(y) dX_{H_t}(y)`. -/
noncomputable def cylindricalAdjointCoeff (ω : SymplecticForm V) (J : ℝ → V → V →L[ℝ] V)
    (H : ℝ → V → ℝ) (p : ℝ × V × V) : V →L[ℝ] V :=
  fderiv ℝ (Function.uncurry J) (p.1, p.2.1) (1, p.2.2) -
    ((fderiv ℝ (J p.1) p.2.1).flip (p.2.2 - ω.hamiltonianVectorField (H p.1) p.2.1) -
      (J p.1 p.2.1).comp (fderiv ℝ (ω.hamiltonianVectorField (H p.1)) p.2.1))

/-- The coordinate expression of `cylindricalAdjointCoeff`. -/
theorem cylindricalAdjointCoeff_def (ω : SymplecticForm V) (J : ℝ → V → V →L[ℝ] V)
    (H : ℝ → V → ℝ) (p : ℝ × V × V) :
    ω.cylindricalAdjointCoeff J H p =
      fderiv ℝ (Function.uncurry J) (p.1, p.2.1) (1, p.2.2) -
        ((fderiv ℝ (J p.1) p.2.1).flip (p.2.2 - ω.hamiltonianVectorField (H p.1) p.2.1) -
          (J p.1 p.2.1).comp (fderiv ℝ (ω.hamiltonianVectorField (H p.1)) p.2.1)) :=
  (rfl)

/-- For the cylindrical datum `(J_t, 0, H_t)`, the zeroth-order coefficient `∂t J - C` of the
formal adjoint along `w` at `z` is `cylindricalAdjointCoeff` at `(t, w z, ∂t w z)`. -/
theorem fderiv_sub_floerLinearizationCoeff_eq_cylindricalAdjointCoeff (ω : SymplecticForm V)
    {J : ℝ → V → V →L[ℝ] V} {H : ℝ → V → ℝ} (hJ : Differentiable ℝ (Function.uncurry J))
    {w : ℝ × ℝ → V} {z : ℝ × ℝ} (hw : DifferentiableAt ℝ w z) :
    fderiv ℝ (fun p ↦ J p.2 (w p)) z stdComplexLineImag -
        ω.floerLinearizationCoeff (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) w z =
      ω.cylindricalAdjointCoeff J H (z.2, w z, fderiv ℝ w z stdComplexLineImag) := by
  have hd := (hJ (z.2, w z)).hasFDerivAt.comp z (hasFDerivAt_snd.prodMk hw.hasFDerivAt)
  rw [show (fun p : ℝ × ℝ ↦ J p.2 (w p)) = Function.uncurry J ∘ fun p ↦ (p.2, w p) from
    funext fun p ↦ (Function.uncurry_apply_pair J p.2 (w p)).symm, hd.fderiv,
    cylindricalAdjointCoeff_def]
  congr 1
  ext y
  simp [floerLinearizationCoeff_apply]

/-- `cylindricalAdjointCoeff` is continuous for `C¹` structures and `C²` Hamiltonians. -/
theorem continuous_cylindricalAdjointCoeff (ω : SymplecticForm V) {J : ℝ → V → V →L[ℝ] V}
    {H : ℝ → V → ℝ} (hJ : ContDiff ℝ 1 (Function.uncurry J))
    (hH : ContDiff ℝ 2 (Function.uncurry H)) :
    Continuous (ω.cylindricalAdjointCoeff J H) := by
  have hX := ω.contDiff_hamiltonianVectorField_uncurry (n := 1) hH
  have hg : Continuous fun p : ℝ × V × V ↦ (p.1, p.2.1) :=
    continuous_fst.prodMk continuous_snd.fst
  have hdJ : Continuous fun p : ℝ × V × V ↦ fderiv ℝ (J p.1) p.2.1 :=
    (ContDiff.fderiv (f := fun p : ℝ × V × V ↦ J p.1) (g := fun p ↦ p.2.1) (n := 0)
      (hJ.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd.fst (by simp)).continuous
  have hdX : Continuous fun p : ℝ × V × V ↦ fderiv ℝ (ω.hamiltonianVectorField (H p.1)) p.2.1 :=
    (ContDiff.fderiv (f := fun (p : ℝ × V × V) y ↦ ω.hamiltonianVectorField (H p.1) y)
      (g := fun p ↦ p.2.1) (n := 0) (hX.comp (contDiff_fst.fst.prodMk contDiff_snd))
      contDiff_snd.fst (by simp)).continuous
  have hXp : Continuous fun p : ℝ × V × V ↦ ω.hamiltonianVectorField (H p.1) p.2.1 :=
    hX.continuous.comp hg
  have hJp : Continuous fun p : ℝ × V × V ↦ J p.1 p.2.1 := hJ.continuous.comp hg
  rw [show ω.cylindricalAdjointCoeff J H = _ from funext (ω.cylindricalAdjointCoeff_def J H)]
  exact (((hJ.continuous_fderiv one_ne_zero).comp hg).clm_apply
    (continuous_const.prodMk continuous_snd.snd)).sub
    ((((flipₗᵢ ℝ V V V).continuous.comp hdJ).clm_apply (continuous_snd.snd.sub hXp)).sub
      (hJp.clm_comp hdX))

/-- Near the curve `t ↦ (x t, X_{H_t}(x t))`, `t ∈ [0, 1]`, of the stationary cylinder over `x`,
the values of `J_t` and of `cylindricalAdjointCoeff` are uniformly continuous: for `ε > 0` there
is `δ > 0` such that two points `δ`-close to the curve over the same `t` have `ε`-close values. -/
theorem exists_pos_forall_norm_cylindricalAdjointCoeff_sub_le (ω : SymplecticForm V)
    {J : ℝ → V → V →L[ℝ] V} {H : ℝ → V → ℝ} {x : ℝ → V}
    (hJ : ContDiff ℝ 1 (Function.uncurry J)) (hH : ContDiff ℝ 2 (Function.uncurry H))
    (hx : Continuous x) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, ∀ q q' : V × V,
      ‖q - (x t, ω.hamiltonianVectorField (H t) (x t))‖ ≤ δ →
      ‖q' - (x t, ω.hamiltonianVectorField (H t) (x t))‖ ≤ δ →
      ‖J t q.1 - J t q'.1‖ ≤ ε ∧
        ‖ω.cylindricalAdjointCoeff J H (t, q) - ω.cylindricalAdjointCoeff J H (t, q')‖ ≤ ε := by
  have hc : Continuous fun t ↦ (x t, ω.hamiltonianVectorField (H t) (x t)) :=
    hx.prodMk ((ω.contDiff_hamiltonianVectorField_uncurry (n := 1) hH).continuous.comp
      (continuous_id.prodMk hx))
  -- Both values at once, as the pair `(J_t, cylindricalAdjointCoeff)` in the product space.
  have hΦ : Continuous fun p : ℝ × V × V ↦ (J p.1 p.2.1, ω.cylindricalAdjointCoeff J H p) :=
    (hJ.continuous.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk
      (ω.continuous_cylindricalAdjointCoeff hJ hH)
  obtain ⟨δ, hδ, h⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_pos_forall_norm_sub_le
    hc.continuousOn (fun _ _ ↦ hΦ.continuousAt) (half_pos hε)
  refine ⟨δ, hδ, fun t ht q q' hq hq' ↦ ?_⟩
  have hb := h t ht q' hq'
  rw [norm_sub_rev] at hb
  simpa using norm_prod_le_iff.1
    ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add (h t ht q hq) hb))

end TauCeti.SymplecticForm
