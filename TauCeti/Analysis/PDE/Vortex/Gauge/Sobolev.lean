/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.EquationMap
import TauCeti.MeasureTheory.Function.Lp.Basic

/-!
# The deformation complex of the plane vortex equation on the Sobolev scale

A field `x = (b₁, b₂, p, q)` of the affine space `A_m^(k+1) = x_m + H^(k+1)(ℂ)⁴`
(`TauCeti.Vortex.framedFieldSpace`) represents the connection `a = i (b₁ ds + b₂ dt)` and the
section `α = 2 (p + i q)`. Its deformation complex consists of the infinitesimal action
`d₀ = TauCeti.Vortex.gaugeDirection x` of the gauge group, sending a real phase `g` to
`(-∂₁ g, -∂₂ g, -q g, p g)`, and the linearized equation `d₁ = TauCeti.Vortex.linearizedEquation x`,
and the gauge-fixed operator `L_x = d₀* ⊕ d₁` (`TauCeti.Vortex.gaugeFixedOperator x`) puts the
formal adjoint `d₀* = TauCeti.Vortex.gaugeAdjoint x` in front of `d₁`.
`TauCeti.Analysis.PDE.Vortex.EquationMap` realizes `d₁` as a bounded operator
`TauCeti.Vortex.sobolevLinearizedEquation : H^(k+1)(ℂ)⁴ → H^k(ℂ)³` on the complexified coordinates
of variations. This file realizes the rest of the complex, for every integer `k ≥ 1`:

* `sobolevGaugeDirection f m hk y : H^(k+2)(ℂ) → H^(k+1)(ℂ)⁴`, the infinitesimal gauge action at
  `x_m + y`. Its zeroth-order part multiplies by the coordinates of `x_m + y` without losing a
  derivative (`TauCeti.Vortex.fieldMulOrderPreservingCLM`), because `H^(k+1)(ℂ)` is an algebra.
* `sobolevGaugeAdjoint f m hk y : H^(k+1)(ℂ)⁴ → H^k(ℂ)`, its formal adjoint.
* `sobolevScaleGaugeFixedOperator f m hk y : H^(k+1)(ℂ)⁴ → H^k(ℂ)⁴`, the gauge-fixed operator
  `d₀* ⊕ d₁`. This is not `TauCeti.Vortex.sobolevGaugeFixedOperator` of
  `TauCeti.Analysis.PDE.Vortex.SobolevRealization`, the realization `H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` with an
  `L∞` coefficient whose kernel is finite-dimensional with closed range at a vortex; no such
  Fredholm property is proved here for the operator on the Sobolev scale.

On complexified coordinates of real fields these compute the pointwise operators almost everywhere
(`coeFn_inclusionLp_sobolevGaugeDirection_ae_eq`, `coeFn_inclusionLp_sobolevGaugeAdjoint_ae_eq`,
`coeFn_inclusionLp_sobolevScaleGaugeFixedOperator_ae_eq`), as `sobolevLinearizedEquation` does.

**The complex.** At a vortex the two maps compose to zero: if the coordinates `y` of a `C¹` field
`x_m + y` are a zero of the Sobolev equation map `TauCeti.Vortex.sobolevEquation`, then
`d₁ ∘ d₀ = 0` as an operator `H^(k+2)(ℂ) → H^k(ℂ)³`
(`sobolevLinearizedEquation_comp_sobolevGaugeDirection_eq_zero`). Both sides are continuous, so it
suffices to test real Schwartz phases, where this is the pointwise identity
`TauCeti.Vortex.linearizedEquation_gaugeDirection_eq_zero`. So at every such vortex
`H^(k+2)(ℂ) → H^(k+1)(ℂ)⁴ → H^k(ℂ)³` is a complex, the infinitesimal gauge directions lie in the
kernel of the linearized equation. The composite `d₀* d₀` is almost everywhere the gauge Laplacian
`-Δ + (p² + q²)` (`coeFn_inclusionLp_sobolevGaugeAdjoint_sobolevGaugeDirection_ae_eq`), the
Schrödinger operator that linearizes the Coulomb condition `d₀* (u · x - x) = 0` at the identity
of the gauge group.

The hypotheses ask for `C¹` components wherever an operator differentiates them, because the
comparison with the pointwise operators goes through classical derivatives; no Leibniz rule for
products in `H^(k+1)(ℂ)` is used.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open BesselPotentialSpace Complex ContinuousLinearMap MeasureTheory
open scoped BesselPotentialSpace ContDiff Laplacian SchwartzMap

variable {f : ContDiffBump (0 : ℝ)} {m k : ℕ}

/-! ### The infinitesimal gauge action -/

variable (f m) in
/-- **The infinitesimal gauge action between Sobolev spaces.** For `k ≥ 1` and complexified
coordinates `y ∈ H^(k+1)(ℂ)⁴`, the complexified infinitesimal gauge action `d₀`
(`TauCeti.Vortex.gaugeDirection`) at `x_m + y`, as a bounded operator
`H^(k+2)(ℂ) → H^(k+1)(ℂ)⁴`: a phase `g` goes to `(-∂₁ g, -∂₂ g, -(x_m + y)₃ g, (x_m + y)₂ g)`.
On real phases it computes the pointwise action
(`coeFn_inclusionLp_sobolevGaugeDirection_ae_eq`). -/
def sobolevGaugeDirection (hk : 1 ≤ k) (y : Fin 4 → H^{(k : ℝ) + 1}(ℂ)) :
    H^{(k : ℝ) + 1 + 1}(ℂ) →L[ℂ] (Fin 4 → H^{(k : ℝ) + 1}(ℂ)) :=
  let D (v : ℂ) : H^{(k : ℝ) + 1 + 1}(ℂ) →L[ℂ] H^{(k : ℝ) + 1}(ℂ) :=
    lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top v
  let X (a : Fin 4) : H^{(k : ℝ) + 1 + 1}(ℂ) →L[ℂ] H^{(k : ℝ) + 1}(ℂ) :=
    (fieldMulOrderPreservingCLM f m hk y a).comp (inclusion (lt_add_one _).le)
  pi ![-D 1, -D I, -X 3, X 2]

section apply

variable (hk : 1 ≤ k) (y : Fin 4 → H^{(k : ℝ) + 1}(ℂ)) (v : H^{(k : ℝ) + 1 + 1}(ℂ))

/-- The first connection component of `sobolevGaugeDirection`. -/
@[simp]
theorem sobolevGaugeDirection_apply_zero :
    sobolevGaugeDirection f m hk y v 0 =
      -lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top 1 v :=
  (rfl)

/-- The second connection component of `sobolevGaugeDirection`. -/
@[simp]
theorem sobolevGaugeDirection_apply_one :
    sobolevGaugeDirection f m hk y v 1 =
      -lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top I v :=
  (rfl)

/-- The real section component of `sobolevGaugeDirection`. -/
@[simp]
theorem sobolevGaugeDirection_apply_two :
    sobolevGaugeDirection f m hk y v 2 =
      -fieldMulOrderPreservingCLM f m hk y 3 (inclusion (lt_add_one _).le v) :=
  (rfl)

/-- The imaginary section component of `sobolevGaugeDirection`. -/
@[simp]
theorem sobolevGaugeDirection_apply_three :
    sobolevGaugeDirection f m hk y v 3 =
      fieldMulOrderPreservingCLM f m hk y 2 (inclusion (lt_add_one _).le v) :=
  (rfl)

end apply

/-- **The Sobolev gauge action computes the pointwise one.** If the coordinates of `u` are almost
everywhere those of the real field `y`, and `v` is almost everywhere the real `C¹` phase `g`, then
`sobolevGaugeDirection f m hk u v` is almost everywhere the infinitesimal gauge action
`gaugeDirection (x_m + y) g`. -/
theorem coeFn_inclusionLp_sobolevGaugeDirection_ae_eq (hk : 1 ≤ k)
    {u : Fin 4 → H^{(k : ℝ) + 1}(ℂ)} {y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hu : ∀ a, ⇑(inclusionLp (by positivity) (u a)) =ᵐ[volume] fun z ↦ (y z a : ℂ))
    {v : H^{(k : ℝ) + 1 + 1}(ℂ)} {g : ℂ → ℝ}
    (hv : ⇑(inclusionLp (by positivity) v) =ᵐ[volume] fun z ↦ (g z : ℂ)) (hg : ContDiff ℝ 1 g)
    (a : Fin 4) :
    ⇑(inclusionLp (by positivity) (sobolevGaugeDirection f m hk u v a)) =ᵐ[volume]
      fun z ↦ (gaugeDirection (referenceField f m + y) g z a : ℂ) := by
  have h₁ : (0 : ℝ) ≤ k + 1 := by positivity
  have hd (w : ℂ) := coeFn_inclusionLp_lineDerivCLM_ae_eq ENNReal.one_lt_two
    ENNReal.ofNat_ne_top h₁ hg hv w
  have hv' : ⇑(inclusionLp h₁ (inclusion (lt_add_one _).le v)) =ᵐ[volume]
      fun z ↦ (g z : ℂ) := by
    rwa [inclusionLp_inclusion]
  have hX (b : Fin 4) :=
    coeFn_inclusionLp_fieldMulOrderPreservingCLM_ae_eq (f := f) (m := m) hk hu b hv'
  fin_cases a
  · rw [Fin.zero_eta, sobolevGaugeDirection_apply_zero, map_neg]
    filter_upwards [Lp.coeFn_neg_ae_eq_of_ae_eq (hd 1)] with z hz
    rw [hz]
    simp
  · rw [Fin.mk_one, sobolevGaugeDirection_apply_one, map_neg]
    filter_upwards [Lp.coeFn_neg_ae_eq_of_ae_eq (hd I)] with z hz
    rw [hz]
    simp
  · simp only [Fin.reduceFinMk]
    rw [sobolevGaugeDirection_apply_two, map_neg]
    filter_upwards [Lp.coeFn_neg_ae_eq_of_ae_eq (hX 3)] with z hz
    rw [hz]
    simp [mul_comm]
  · simp only [Fin.reduceFinMk]
    rw [sobolevGaugeDirection_apply_three]
    filter_upwards [hX 2] with z hz
    rw [hz]
    simp [mul_comm]

/-! ### The adjoint of the gauge action and the gauge-fixed operator -/

variable (f m) in
/-- **The adjoint of the gauge action between Sobolev spaces.** For `k ≥ 1` and complexified
coordinates `y ∈ H^(k+1)(ℂ)⁴`, the complexified formal adjoint `d₀*`
(`TauCeti.Vortex.gaugeAdjoint`) of the infinitesimal gauge action at `x_m + y`, as a bounded
operator `H^(k+1)(ℂ)⁴ → H^k(ℂ)`: a variation `h` goes to
`∂₁ h₀ + ∂₂ h₁ + (x_m + y)₂ h₃ - (x_m + y)₃ h₂`. -/
def sobolevGaugeAdjoint (hk : 1 ≤ k) (y : Fin 4 → H^{(k : ℝ) + 1}(ℂ)) :
    (Fin 4 → H^{(k : ℝ) + 1}(ℂ)) →L[ℂ] H^{(k : ℝ)}(ℂ) :=
  let D (v : ℂ) (b : Fin 4) : (Fin 4 → H^{(k : ℝ) + 1}(ℂ)) →L[ℂ] H^{(k : ℝ)}(ℂ) :=
    (lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top v).comp (proj b)
  let X (a b : Fin 4) : (Fin 4 → H^{(k : ℝ) + 1}(ℂ)) →L[ℂ] H^{(k : ℝ)}(ℂ) :=
    (fieldMulCLM f m hk y a).comp (proj b)
  D 1 0 + D I 1 + X 2 3 - X 3 2

/-- The defining formula of `sobolevGaugeAdjoint`. -/
@[simp]
theorem sobolevGaugeAdjoint_apply (hk : 1 ≤ k) (y h : Fin 4 → H^{(k : ℝ) + 1}(ℂ)) :
    sobolevGaugeAdjoint f m hk y h =
      lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top 1 (h 0) +
        lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top I (h 1) +
        fieldMulCLM f m hk y 2 (h 3) - fieldMulCLM f m hk y 3 (h 2) :=
  (rfl)

/-- **The Sobolev adjoint gauge action computes the pointwise one.** If the coordinates of `u`
and `w` are almost everywhere those of the real fields `y` and `h`, with the connection components
`h₀` and `h₁` of class `C¹`, then `sobolevGaugeAdjoint f m hk u w` is almost everywhere
`gaugeAdjoint (x_m + y) h`. -/
theorem coeFn_inclusionLp_sobolevGaugeAdjoint_ae_eq (hk : 1 ≤ k)
    {u w : Fin 4 → H^{(k : ℝ) + 1}(ℂ)} {y h : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hu : ∀ a, ⇑(inclusionLp (by positivity) (u a)) =ᵐ[volume] fun z ↦ (y z a : ℂ))
    (hw : ∀ a, ⇑(inclusionLp (by positivity) (w a)) =ᵐ[volume] fun z ↦ (h z a : ℂ))
    (hh₀ : ContDiff ℝ 1 fun z ↦ h z 0) (hh₁ : ContDiff ℝ 1 fun z ↦ h z 1) :
    ⇑(inclusionLp (k.cast_nonneg : (0 : ℝ) ≤ k) (sobolevGaugeAdjoint f m hk u w))
      =ᵐ[volume] fun z ↦ (gaugeAdjoint (referenceField f m + y) h z : ℂ) := by
  have hd₀ := coeFn_inclusionLp_lineDerivCLM_ae_eq ENNReal.one_lt_two ENNReal.ofNat_ne_top
    k.cast_nonneg hh₀ (hw 0) 1
  have hd₁ := coeFn_inclusionLp_lineDerivCLM_ae_eq ENNReal.one_lt_two ENNReal.ofNat_ne_top
    k.cast_nonneg hh₁ (hw 1) I
  have hX (a b : Fin 4) := coeFn_inclusionLp_fieldMulCLM_ae_eq (f := f) (m := m) hk hu a (hw b)
  rw [sobolevGaugeAdjoint_apply, map_sub, map_add, map_add]
  filter_upwards [Lp.coeFn_sub_ae_eq_of_ae_eq (Lp.coeFn_add_ae_eq_of_ae_eq
    (Lp.coeFn_add_ae_eq_of_ae_eq hd₀ hd₁) (hX 2 3)) (hX 3 2)] with z hz
  rw [hz]
  simp only [Pi.add_apply, Pi.sub_apply, gaugeAdjoint_def, Complex.ofReal_add,
    Complex.ofReal_sub]

variable (f m) in
/-- **The gauge-fixed vortex operator between Sobolev spaces.** For `k ≥ 1` and complexified
coordinates `y ∈ H^(k+1)(ℂ)⁴`, the complexified gauge-fixed operator `L_x = d₀* ⊕ d₁`
(`TauCeti.Vortex.gaugeFixedOperator`) at `x_m + y`, as a bounded operator
`H^(k+1)(ℂ)⁴ → H^k(ℂ)⁴`: the gauge-fixing row `sobolevGaugeAdjoint` followed by the three rows of
`sobolevLinearizedEquation`. It acts on complexified coordinates and is distinct from the
realization `TauCeti.Vortex.sobolevGaugeFixedOperator : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` with an `L∞`
coefficient; no Fredholm property is proved for it here. -/
def sobolevScaleGaugeFixedOperator (hk : 1 ≤ k) (y : Fin 4 → H^{(k : ℝ) + 1}(ℂ)) :
    (Fin 4 → H^{(k : ℝ) + 1}(ℂ)) →L[ℂ] (Fin 4 → H^{(k : ℝ)}(ℂ)) :=
  pi ![sobolevGaugeAdjoint f m hk y, (proj 0).comp (sobolevLinearizedEquation f m hk y),
    (proj 1).comp (sobolevLinearizedEquation f m hk y),
    (proj 2).comp (sobolevLinearizedEquation f m hk y)]

section apply

variable (hk : 1 ≤ k) (y h : Fin 4 → H^{(k : ℝ) + 1}(ℂ))

/-- The gauge-fixing row of `sobolevScaleGaugeFixedOperator`. -/
@[simp]
theorem sobolevScaleGaugeFixedOperator_apply_zero :
    sobolevScaleGaugeFixedOperator f m hk y h 0 = sobolevGaugeAdjoint f m hk y h :=
  (rfl)

/-- The curvature row of `sobolevScaleGaugeFixedOperator`. -/
@[simp]
theorem sobolevScaleGaugeFixedOperator_apply_one :
    sobolevScaleGaugeFixedOperator f m hk y h 1 = sobolevLinearizedEquation f m hk y h 0 :=
  (rfl)

/-- The real `∂bar` row of `sobolevScaleGaugeFixedOperator`. -/
@[simp]
theorem sobolevScaleGaugeFixedOperator_apply_two :
    sobolevScaleGaugeFixedOperator f m hk y h 2 = sobolevLinearizedEquation f m hk y h 1 :=
  (rfl)

/-- The imaginary `∂bar` row of `sobolevScaleGaugeFixedOperator`. -/
@[simp]
theorem sobolevScaleGaugeFixedOperator_apply_three :
    sobolevScaleGaugeFixedOperator f m hk y h 3 = sobolevLinearizedEquation f m hk y h 2 :=
  (rfl)

end apply

/-- **The Sobolev gauge-fixed operator computes the pointwise one.** If the coordinates of `u`
and `w` are almost everywhere those of the real fields `y` and `h`, with `h` of class `C¹`, then
`sobolevScaleGaugeFixedOperator f m hk u w` is almost everywhere the gauge-fixed operator
`gaugeFixedOperator (x_m + y) h`. -/
theorem coeFn_inclusionLp_sobolevScaleGaugeFixedOperator_ae_eq (hk : 1 ≤ k)
    {u w : Fin 4 → H^{(k : ℝ) + 1}(ℂ)} {y h : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hu : ∀ a, ⇑(inclusionLp (by positivity) (u a)) =ᵐ[volume] fun z ↦ (y z a : ℂ))
    (hw : ∀ a, ⇑(inclusionLp (by positivity) (w a)) =ᵐ[volume] fun z ↦ (h z a : ℂ))
    (hh : ContDiff ℝ 1 h) (a : Fin 4) :
    ⇑(inclusionLp (k.cast_nonneg : (0 : ℝ) ≤ k) (sobolevScaleGaugeFixedOperator f m hk u w a))
      =ᵐ[volume] fun z ↦ (gaugeFixedOperator (referenceField f m + y) h z a : ℂ) := by
  have hd (i : Fin 3) :=
    coeFn_inclusionLp_sobolevLinearizedEquation_ae_eq (f := f) (m := m) hk hu hw hh i
  fin_cases a
  · simpa using coeFn_inclusionLp_sobolevGaugeAdjoint_ae_eq (f := f) (m := m) hk hu hw
      (contDiff_euclidean.1 hh 0) (contDiff_euclidean.1 hh 1)
  · simpa using hd 0
  · simpa using hd 1
  · simpa using hd 2

/-! ### Dependence on the field -/

/-- **The infinitesimal gauge action depends analytically on the field.** -/
theorem contDiff_sobolevGaugeDirection (hk : 1 ≤ k) :
    ContDiff ℂ ω (sobolevGaugeDirection f m hk) := by
  let T : (Fin 4 → H^{(k : ℝ) + 1 + 1}(ℂ) →L[ℂ] H^{(k : ℝ) + 1}(ℂ)) →L[ℂ]
      H^{(k : ℝ) + 1 + 1}(ℂ) →L[ℂ] (Fin 4 → H^{(k : ℝ) + 1}(ℂ)) :=
    (piEquivL ℂ _ _ : _ ≃L[ℂ] _).toContinuousLinearMap
  let D (v : ℂ) : H^{(k : ℝ) + 1 + 1}(ℂ) →L[ℂ] H^{(k : ℝ) + 1}(ℂ) :=
    lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top v
  let X (y : Fin 4 → H^{(k : ℝ) + 1}(ℂ)) (a : Fin 4) :
      H^{(k : ℝ) + 1 + 1}(ℂ) →L[ℂ] H^{(k : ℝ) + 1}(ℂ) :=
    (fieldMulOrderPreservingCLM f m hk y a).comp (inclusion (lt_add_one _).le)
  -- The operator is `T` applied to its four components, of which only the last two vary.
  have hT : sobolevGaugeDirection f m hk = fun y ↦ T ![-D 1, -D I, -X y 3, X y 2] := by
    funext y
    ext v i : 2
    fin_cases i <;> simp [T, D, X]
  rw [hT]
  refine T.contDiff.comp (contDiff_pi' fun i ↦ ?_)
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
  · exact contDiff_const
  · exact contDiff_const
  · exact ((contDiff_fieldMulOrderPreservingCLM hk 3).clm_comp contDiff_const).neg
  · exact (contDiff_fieldMulOrderPreservingCLM hk 2).clm_comp contDiff_const

/-- **The adjoint gauge action depends analytically on the field.** -/
theorem contDiff_sobolevGaugeAdjoint (hk : 1 ≤ k) : ContDiff ℂ ω (sobolevGaugeAdjoint f m hk) := by
  let D (v : ℂ) (b : Fin 4) : (Fin 4 → H^{(k : ℝ) + 1}(ℂ)) →L[ℂ] H^{(k : ℝ)}(ℂ) :=
    (lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top v).comp (proj b)
  let X (y : Fin 4 → H^{(k : ℝ) + 1}(ℂ)) (a b : Fin 4) :
      (Fin 4 → H^{(k : ℝ) + 1}(ℂ)) →L[ℂ] H^{(k : ℝ)}(ℂ) :=
    (fieldMulCLM f m hk y a).comp (proj b)
  -- The derivative terms do not depend on the field; the multiplication terms do.
  have hA : sobolevGaugeAdjoint f m hk = fun y ↦ D 1 0 + D I 1 + X y 2 3 - X y 3 2 := by
    funext y
    ext h
    simp [D, X]
  have hX (a b : Fin 4) : ContDiff ℂ ω fun y ↦ X y a b :=
    (contDiff_fieldMulCLM hk a).clm_comp contDiff_const
  rw [hA]
  exact ((contDiff_const.add contDiff_const).add (hX 2 3)).sub (hX 3 2)

/-- **The gauge-fixed operator depends analytically on the field.** As a map from the
coordinates `y ∈ H^(k+1)(ℂ)⁴` of `x_m + y` to the bounded operators `H^(k+1)(ℂ)⁴ → H^k(ℂ)⁴`,
`sobolevScaleGaugeFixedOperator` is analytic. -/
theorem contDiff_sobolevScaleGaugeFixedOperator (hk : 1 ≤ k) :
    ContDiff ℂ ω (sobolevScaleGaugeFixedOperator f m hk) := by
  have hL := contDiff_sobolevLinearizedEquation (f := f) (m := m) hk
  let T : (Fin 4 → (Fin 4 → H^{(k : ℝ) + 1}(ℂ)) →L[ℂ] H^{(k : ℝ)}(ℂ)) →L[ℂ]
      (Fin 4 → H^{(k : ℝ) + 1}(ℂ)) →L[ℂ] (Fin 4 → H^{(k : ℝ)}(ℂ)) :=
    (piEquivL ℂ _ _ : _ ≃L[ℂ] _).toContinuousLinearMap
  let P (i : Fin 3) : (Fin 3 → H^{(k : ℝ)}(ℂ)) →L[ℂ] H^{(k : ℝ)}(ℂ) := proj i
  -- The operator is `T` applied to its four rows.
  have hT : sobolevScaleGaugeFixedOperator f m hk = fun y ↦
      T ![sobolevGaugeAdjoint f m hk y, (P 0).comp (sobolevLinearizedEquation f m hk y),
        (P 1).comp (sobolevLinearizedEquation f m hk y),
        (P 2).comp (sobolevLinearizedEquation f m hk y)] := by
    funext y
    ext h i : 2
    fin_cases i <;> simp [T, P, -sobolevGaugeAdjoint_apply]
  rw [hT]
  refine T.contDiff.comp (contDiff_pi' fun i ↦ ?_)
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
  · exact contDiff_sobolevGaugeAdjoint hk
  · exact contDiff_const.clm_comp hL
  · exact contDiff_const.clm_comp hL
  · exact contDiff_const.clm_comp hL

/-! ### The deformation complex -/

/-- **The deformation complex of a plane vortex.** Let `k ≥ 1` and let the coordinates of
`u : Fin 4 → H^(k+1)(ℂ)` be almost everywhere those of a real `C¹` field `y`, so that
`x = x_m + y ∈ A_m^(k+1)`. If `x` is a vortex, that is, `sobolevEquation f m hk u = 0`, then the
infinitesimal gauge action followed by the linearized equation vanishes:
`d₁ ∘ d₀ = 0` as an operator `H^(k+2)(ℂ) → H^k(ℂ)³`. -/
theorem sobolevLinearizedEquation_comp_sobolevGaugeDirection_eq_zero (hk : 1 ≤ k)
    {u : Fin 4 → H^{(k : ℝ) + 1}(ℂ)} {y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hu : ∀ a, ⇑(inclusionLp (by positivity) (u a)) =ᵐ[volume] fun z ↦ (y z a : ℂ))
    (hy : ContDiff ℝ 1 y) (hsol : sobolevEquation f m hk u = 0) :
    (sobolevLinearizedEquation f m hk u).comp (sobolevGaugeDirection f m hk u) = 0 := by
  set x := referenceField f m + y with hxdef
  have hx : ContDiff ℝ 1 x := ((contDiff_referenceField f m).of_le (by simp)).add hy
  have hE : equation x = 0 := by
    refine (sobolevEquation_eq_zero_iff hk (fun a ↦ ?_) hx).1 hsol
    simpa [hxdef] using hu a
  -- On a real Schwartz phase `ψ`, `d₁ (d₀ ψ)` computes the pointwise identity `d₁ d₀ = 0`.
  have hreal (ψ : 𝓢(ℂ, ℝ)) : sobolevLinearizedEquation f m hk u (sobolevGaugeDirection f m hk u
      (SchwartzMap.toBesselPotentialSpaceCLM _ 2
        (ψ.postcompCLM ofRealCLM))) = 0 := by
    have hψ : ContDiff ℝ ∞ ψ := ψ.smooth ⊤
    have hcomp (b : Fin 4) : ContDiff ℝ 1 fun z ↦ x z b := contDiff_euclidean.1 hx b
    -- The real Schwartz phase is, as an element of `H^(k+2)(ℂ)`, almost everywhere `ψ`.
    have hv : ⇑(inclusionLp (by positivity) (SchwartzMap.toBesselPotentialSpaceCLM
        ((k : ℝ) + 1 + 1) 2 (ψ.postcompCLM ofRealCLM))) =ᵐ[volume] fun z ↦ (ψ z : ℂ) := by
      rw [inclusionLp_toBesselPotentialSpaceCLM]
      filter_upwards [SchwartzMap.coeFn_toLp (ψ.postcompCLM ofRealCLM) 2] with z hz
      simp [hz]
    funext i
    refine inclusionLp_injective (k.cast_nonneg : (0 : ℝ) ≤ k) (Lp.ext ?_)
    rw [Pi.zero_apply, map_zero]
    refine (coeFn_inclusionLp_sobolevLinearizedEquation_ae_eq hk hu
      (coeFn_inclusionLp_sobolevGaugeDirection_ae_eq hk hu hv (hψ.of_le (by simp)))
      (contDiff_gaugeDirection hx (hψ.of_le (by simp))) i).trans ?_
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure ℂ)] with z hz
    rw [hz, ← hxdef, linearizedEquation_gaugeDirection_eq_zero
      ((hcomp 2).differentiable one_ne_zero z) ((hcomp 3).differentiable one_ne_zero z)
      (hψ.of_le (by simp)).contDiffAt (congrFun hE z)]
    simp
  -- Both sides are continuous and complex linear, so real Schwartz phases suffice.
  refine continuousLinearMap_ext_real ENNReal.ofNat_ne_top fun ψ ↦ ?_
  simp only [comp_apply, zero_apply, hreal]

/-- **`d₀* d₀` is the gauge Laplacian.** If the coordinates of `u` are almost everywhere those of
the real field `y`, and `v` is almost everywhere the real `C²` phase `g`, then
`sobolevGaugeAdjoint f m hk u (sobolevGaugeDirection f m hk u v)` is almost everywhere
`-Δg + (p² + q²) g`, where `p` and `q` are the section coordinates of `x_m + y`. -/
theorem coeFn_inclusionLp_sobolevGaugeAdjoint_sobolevGaugeDirection_ae_eq (hk : 1 ≤ k)
    {u : Fin 4 → H^{(k : ℝ) + 1}(ℂ)} {y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hu : ∀ a, ⇑(inclusionLp (by positivity) (u a)) =ᵐ[volume] fun z ↦ (y z a : ℂ))
    {v : H^{(k : ℝ) + 1 + 1}(ℂ)} {g : ℂ → ℝ}
    (hv : ⇑(inclusionLp (by positivity) v) =ᵐ[volume] fun z ↦ (g z : ℂ)) (hg : ContDiff ℝ 2 g) :
    ⇑(inclusionLp (k.cast_nonneg : (0 : ℝ) ≤ k)
        (sobolevGaugeAdjoint f m hk u (sobolevGaugeDirection f m hk u v))) =ᵐ[volume]
      fun z ↦ ((-Δ g z +
        ((referenceField f m + y) z 2 ^ 2 + (referenceField f m + y) z 3 ^ 2) * g z : ℝ) : ℂ) := by
  -- The connection components of `d₀ g` are `-∂₁ g` and `-∂₂ g`, of class `C¹`.
  have hdg (w : ℂ) : ContDiff ℝ 1 fun z ↦ -fderiv ℝ g z w :=
    ((hg.fderiv_right (by norm_num)).clm_apply contDiff_const).neg
  filter_upwards [coeFn_inclusionLp_sobolevGaugeAdjoint_ae_eq hk hu
    (coeFn_inclusionLp_sobolevGaugeDirection_ae_eq hk hu hv (hg.of_le (by norm_num)))
    (by simpa using hdg 1) (by simpa using hdg I)] with z hz
  rw [hz, gaugeAdjoint_gaugeDirection _ hg.contDiffAt]

end TauCeti.Vortex
