/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Energy
public import TauCeti.Geometry.Symplectic.Hamiltonian.Variation
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Topology.Constructions.SumProd

/-!
# Local-coordinate linearization of the inhomogeneous Floer equation

The nonlinear operator is `∂s u - X_Ks + J(z,u)(∂t u - X_Kt)`. For the cylindrical datum
`K = H_t dt` and `J_t` independent of `s` it commutes with translations in `s`
(`floerOperator_comp_sub`). We differentiate it along
jointly `C²` families of maps and Hamiltonians and differentiable families of endomorphisms.
The formula includes the target derivative of `J`, both Hamiltonian linearizations, and the
independent parameter variations of `K` and `J`. Domain dependence of the coefficients is
allowed; the derivative is at a fixed domain point. Along a line `J + q Y` of endomorphism fields
the derivative is `Y(u)(∂t u - X_Kt)` (`hasDerivAt_floerOperator_add_smul`).

`floerLinearization` is the map-direction operator with coefficients fixed. For a constant almost
complex structure `J` and `K = H dt`, with `H` allowed to depend on the domain point, it is
`∂s ξ + J (∂t ξ - dX_H(u) ξ)` (`floerLinearization_const_eq`), so it vanishes at a point exactly
when `∂s ξ = -J ∂t ξ + J dX_H(u) ξ` there (`floerLinearization_const_eq_zero_iff`), and on a
direction `(s, t) ↦ ζ(s)` it is `ζ' - J dX_H(u) ζ` (`floerLinearization_comp_fst`). On a direction
multiplied by a function `f` of both variables it acts as `f D ξ + (∂s f) ξ + (∂t f) J ξ`
(`floerLinearization_fun_smul`), a case of the same rule
for any operator `∂s + J ∂t + A` (`TauCeti.cauchyRiemann_fun_smul` in
`TauCeti.Geometry.Symplectic.JHolomorphic.Line`), so that
`‖D (f ξ)‖² ≤ 2 ‖D ξ‖² + 2 (M (1 + B))² ‖ξ‖²` where `|f| ≤ 1`, `‖df‖ ≤ M` and `‖J‖ ≤ B`
(`norm_floerLinearization_fun_smul_sq_le`). On a direction multiplied by a cutoff `β(s)` it acts as
`β D ξ + β' ξ` (`floerLinearization_smul_fst`), the corresponding case of the general operator
(`TauCeti.cauchyRiemann_smul_fst`); in particular, conjugated by an exponential weight `e^{κ(s)}`
it becomes `floerLinearization - κ'` (`floerLinearization_exp_neg_smul`;
`floerLinearization_exp_smul` for `κ(s) = δ s`). Its value at a point depends only on the germ of
the direction there (`floerLinearization_congr_of_eventuallyEq`), so it vanishes off the support of
the direction (`floerLinearization_of_notMem_tsupport`) and its support lies in that of the
direction (`tsupport_floerLinearization_subset`), and on the Floer data only through their values at
that point (`floerLinearization_congr_data`). For `C¹` coefficients `J` and `C²` Hamiltonians it is
continuous wherever the map and the direction are `C¹` (`continuousAt_floerLinearization`), and
continuous everywhere when they are so everywhere (`continuous_floerLinearization`), or when the
direction is supported in an open set on which the data are regular
(`continuous_floerLinearization_of_tsupport_subset`), so its `L²` norms over compact sets are
finite. A compactly supported direction has a compactly supported image
(`hasCompactSupport_floerLinearization`), whose square norm is then integrable
(`integrable_norm_floerLinearization_sq`). Multiplying a direction of compact support by a cutoff
`β` with values in `[0, 1]` bounds `‖D_u (β ξ)‖²` in `L²` by `2 ‖D_u ξ‖²` plus a multiple of `‖ξ‖²`
over a compact set off which `dβ` vanishes (`exists_integral_norm_floerLinearization_smul_sq_le`,
and `exists_integral_norm_floerLinearization_smul_sq_le_of_tsupport_subset` for data regular on a
set containing the direction's support); the integration step is shared with the formal adjoint and
other operators satisfying the same pointwise bound on a set `S`
(`TauCeti.integral_mul_norm_fun_smul_sq_le`).
It is `∂s ξ + J(z, u z) ∂t ξ` plus a zeroth-order term `floerLinearizationCoeff`
(`floerLinearization_eq_add`), whose coefficient is continuous in `z` where the data are `C¹`
(`continuousAt_floerLinearizationCoeff`, `continuousOn_floerLinearizationCoeff`), and `Cⁿ` where
`J` and `u` are `Cⁿ⁺¹` and the Hamiltonians `Cⁿ⁺²` (`contDiffAt_floerLinearizationCoeff`); so two
linearized operators differ pointwise by the differences of their coefficients
(`norm_floerLinearization_sub_floerLinearization_le`). For a family of data that is `Cⁿ⁺¹` (with
`Cⁿ⁺²` Hamiltonians) jointly in a parameter, the coefficient is `Cⁿ` jointly in the parameter and
`z` (`contDiffAt_floerLinearizationCoeff_family`), in particular continuous for `C¹` data
(`continuousAt_floerLinearizationCoeff_family`). Translating the data and the direction
translates the operator (`floerLinearization_comp_add_right`).
For jointly continuous `J` and jointly `C¹` Hamiltonians, the Floer operator of an almost
everywhere strongly measurable map is almost everywhere strongly measurable
(`aestronglyMeasurable_floerOperator`), so its `Lᵖ` norms are defined.
The universal variation theorem identifies its direction field with the actual parameter derivative
of the map, using equality of mixed derivatives rather than assuming it. The endomorphism field need
not square to minus one for differentiation. For an almost complex structure the zero equation
agrees with complex linearity of the existing perturbed derivative. The parameter calculation
extends the unforced formula `TauCeti.fderiv_cauchyRiemannOperator_apply`.

These are local formulas for a constant symplectic form, not an intrinsic connection formula,
a Sobolev operator, or a Fredholm or regularity assertion. See McDuff–Salamon, *J-holomorphic
Curves and Symplectic Topology*, Sections 3.1 and 8.1, for the geometric linearization and
Hamiltonian perturbations.
-/

public section

namespace TauCeti

/-- **The arithmetic of a Leibniz bound.** If `|r| ≤ 1`, `‖b‖ ≤ M y` and `‖c‖ ≤ M (B y)`, then
`‖r a + b + c‖² ≤ 2 ‖a‖² + 2 (M (1 + B))² y²`. This is the estimate shared by the linearized Floer
operator and its formal adjoint on a field multiplied by a cutoff, where `r a` is the cut-off
operator term and `b`, `c` are the terms differentiating the cutoff. -/
theorem norm_smul_add_add_sq_le {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {r M B y : ℝ} {a b c : E} (hr : |r| ≤ 1) (hb : ‖b‖ ≤ M * y) (hc : ‖c‖ ≤ M * (B * y)) :
    ‖r • a + b + c‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * (M * (1 + B)) ^ 2 * y ^ 2 := by
  have ha : ‖r • a‖ ≤ ‖a‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) hr
  have hsum : ‖r • a + b + c‖ ≤ ‖a‖ + M * (1 + B) * y := by
    refine norm_add₃_le.trans ?_
    linarith
  calc _ ≤ (‖a‖ + M * (1 + B) * y) ^ 2 := by gcongr
    _ ≤ _ := by nlinarith [sq_nonneg (‖a‖ - M * (1 + B) * y)]

open MeasureTheory Set in
/-- **The weighted `L²` norm of an operator on a cut-off field.** Let `f` have derivative supported,
at the points of a set `S`, in a compact set `K`, and bounded by `M` there, let `b ≤ B` and the
weight `w ≥ 0` satisfy `w ≤ Λ` on `K`. If an operator `D` vanishes on `f ξ` off `S` and, at each
point of `S` where `‖df‖ ≤ M'` and `b ≤ B'`, satisfies
`‖D (f ξ)‖² ≤ 2 ‖D ξ‖² + 2 (M' (1 + B'))² ‖ξ‖²`, then
`∫ w ‖D (f ξ)‖² ≤ 2 ∫ w ‖D ξ‖² + 2 (M (1 + B))² Λ ∫_K ‖ξ‖²`. This is shared by the linearized
Floer operator `D_u` and its formal adjoint, on the whole plane (`S = univ`) and on punctured
domains. -/
theorem integral_mul_norm_fun_smul_sq_le {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] {D : (ℝ × ℝ → E) → ℝ × ℝ → F} {S : Set (ℝ × ℝ)}
    {w : ℝ × ℝ → ℝ} (hw : ∀ z, 0 ≤ w z) {K : Set (ℝ × ℝ)} (hK : IsCompact K) {f : ℝ × ℝ → ℝ}
    (hfK : ∀ z ∈ S, fderiv ℝ f z ≠ 0 → z ∈ K) {b : ℝ × ℝ → ℝ}
    {M B Λ : ℝ} (hM : ∀ z ∈ K, ‖fderiv ℝ f z‖ ≤ M) (hB : ∀ z ∈ K, b z ≤ B) (hΛ₀ : 0 ≤ Λ)
    (hΛ : ∀ z ∈ K, w z ≤ Λ) {ξ : ℝ × ℝ → E} (hξ : Continuous ξ)
    (hD : ∀ z ∈ S, ∀ M' B' : ℝ, ‖fderiv ℝ f z‖ ≤ M' → b z ≤ B' →
      ‖D (fun w ↦ f w • ξ w) z‖ ^ 2 ≤
        2 * ‖D ξ z‖ ^ 2 + 2 * (M' * (1 + B')) ^ 2 * ‖ξ z‖ ^ 2)
    (hD₀ : ∀ z ∉ S, D (fun w ↦ f w • ξ w) z = 0)
    (hξi : Integrable fun z ↦ w z * ‖D ξ z‖ ^ 2)
    (hfξi : Integrable fun z ↦ w z * ‖D (fun w ↦ f w • ξ w) z‖ ^ 2) :
    ∫ z, w z * ‖D (fun w ↦ f w • ξ w) z‖ ^ 2 ≤
      2 * (∫ z, w z * ‖D ξ z‖ ^ 2) + 2 * (M * (1 + B)) ^ 2 * Λ * ∫ z in K, ‖ξ z‖ ^ 2 := by
  have hind : Integrable (K.indicator fun z ↦ ‖ξ z‖ ^ 2) :=
    ((hξ.norm.pow 2).continuousOn.integrableOn_compact hK).integrable_indicator hK.measurableSet
  set c := M * (1 + B)
  calc _ ≤ ∫ z, (2 * (w z * ‖D ξ z‖ ^ 2) + 2 * c ^ 2 * Λ * K.indicator (fun z ↦ ‖ξ z‖ ^ 2) z) := by
        refine integral_mono hfξi ((hξi.const_mul 2).add (hind.const_mul _)) fun z ↦ ?_
        have hind₀ : 0 ≤ K.indicator (fun z ↦ ‖ξ z‖ ^ 2) z :=
          indicator_nonneg (fun _ _ ↦ sq_nonneg _) z
        by_cases hzS : z ∈ S
        · by_cases hz : fderiv ℝ f z = 0
          · have h := hD z hzS 0 (b z) (by simp [hz]) le_rfl
            simp only [zero_mul, zero_pow two_ne_zero, mul_zero, add_zero] at h
            nlinarith [mul_nonneg (mul_nonneg (sq_nonneg c) hΛ₀) hind₀,
              mul_le_mul_of_nonneg_left h (hw z)]
          · have hzK := hfK z hzS hz
            have h := hD z hzS M B (hM z hzK) (hB z hzK)
            rw [indicator_of_mem hzK]
            nlinarith [mul_le_mul_of_nonneg_left h (hw z), mul_le_mul_of_nonneg_right (hΛ z hzK)
              (mul_nonneg (sq_nonneg c) (sq_nonneg ‖ξ z‖))]
        · rw [hD₀ z hzS, norm_zero, zero_pow two_ne_zero, mul_zero]
          have := hw z
          positivity
    _ = _ := by
        rw [integral_add (hξi.const_mul 2) (hind.const_mul _), integral_const_mul,
          integral_const_mul, integral_indicator hK.measurableSet]

end TauCeti

namespace TauCeti.SymplecticForm

open ContinuousLinearMap

variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The local inhomogeneous Floer operator, with convention `ι_X ω = dH`. Its zeros are
`∂s u - X_Ks + J(z,u)(∂t u - X_Kt) = 0`. -/
noncomputable def floerOperator (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (u : ℝ × ℝ → V) (z : ℝ × ℝ) : V :=
  fderiv ℝ u z stdComplexLineReal - ω.hamiltonianVectorField (Ks z) (u z) +
    J z (u z) (fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z))

/-- The coordinate expression of the nonlinear Floer operator. -/
theorem floerOperator_def (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (u : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ω.floerOperator J Ks Kt u z =
      fderiv ℝ u z stdComplexLineReal - ω.hamiltonianVectorField (Ks z) (u z) +
        J z (u z) (fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z)) :=
  (rfl)

/-- The Floer operator commutes with translations of the domain: translating the map and the
data by `v` translates the Floer operator by `v`. -/
theorem floerOperator_comp_add_right (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) (v z : ℝ × ℝ) :
    ω.floerOperator (fun w ↦ J (w + v)) (fun w ↦ Ks (w + v)) (fun w ↦ Kt (w + v))
        (fun w ↦ u (w + v)) z =
      ω.floerOperator J Ks Kt u (z + v) := by
  simp only [floerOperator_def, fderiv_comp_add_right]

/-- The Floer operator is `P(∂s) + J P(∂t)` for the perturbed derivative `P = du - X_K`. -/
theorem floerOperator_eq_perturbedFDeriv (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (u : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ω.floerOperator J Ks Kt u z =
      ω.perturbedFDeriv Ks Kt u z stdComplexLineReal +
        J z (u z) (ω.perturbedFDeriv Ks Kt u z stdComplexLineImag) := by
  rw [floerOperator_def, perturbedFDeriv_apply_stdComplexLineReal,
    perturbedFDeriv_apply_stdComplexLineImag]

/-- For almost complex coefficients, vanishing is complex linearity of `du - X_K`. -/
theorem floerOperator_eq_zero_iff (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → AlmostComplexStructure V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (u : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ω.floerOperator (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u z = 0 ↔
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] V) := by
  rw [floerOperator_def, ω.isComplexLinearMap_perturbedFDeriv_iff]
  -- The linear and continuous-linear coercions of `J` have the same underlying function.
  rfl

/-- **The difference of two Floer operators.** At a point where `u` and `v` are differentiable,
with `w = u - v`, the difference of their Floer operators is the Cauchy–Riemann operator
`∂ₛw + J(z, u) ∂ₜw` of `w` for the structure along `u`, corrected by the differences of the
Hamiltonian vector fields and of the structures at the two values:
`F(u) - F(v) = ∂ₛw + J(z, u) ∂ₜw - (X_{K_s}(u) - X_{K_s}(v)) - J(z, u) (X_{K_t}(u) - X_{K_t}(v))
  + (J(z, u) - J(z, v)) (∂ₜv - X_{K_t}(v))`. -/
theorem floerOperator_sub_floerOperator (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ)
    {u v : ℝ × ℝ → V} {z : ℝ × ℝ} (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) :
    ω.floerOperator J Ks Kt u z - ω.floerOperator J Ks Kt v z =
      fderiv ℝ (u - v) z stdComplexLineReal + J z (u z) (fderiv ℝ (u - v) z stdComplexLineImag) -
        (ω.hamiltonianVectorField (Ks z) (u z) - ω.hamiltonianVectorField (Ks z) (v z)) -
        J z (u z) (ω.hamiltonianVectorField (Kt z) (u z) - ω.hamiltonianVectorField (Kt z) (v z)) +
        (J z (u z) - J z (v z))
          (fderiv ℝ v z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (v z)) := by
  simp only [floerOperator_def, fderiv_sub hu hv, _root_.sub_apply, map_sub]
  abel

/-- **Translation invariance of the Floer operator.** For the cylindrical datum `K = H_t dt` and a
structure `J_t` independent of `s`, the Floer operator of the translate `w ↦ f(w - (R, 0))` at `z`
is the Floer operator of `f` at `z - (R, 0)`. -/
theorem floerOperator_comp_sub (ω : SymplecticForm V) (J : ℝ → V → V →L[ℝ] V) (H : ℝ → V → ℝ)
    (f : ℝ × ℝ → V) (R : ℝ) (z : ℝ × ℝ) :
    ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) (fun w ↦ f (w - (R, 0))) z =
      ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) f (z - (R, 0)) := by
  simp only [floerOperator_def, fderiv_comp_sub, Prod.snd_sub, sub_zero]

/-- **The `J`-direction derivative of the Floer operator.** Along the line `J + q Y` of
endomorphism fields, the coordinate Floer operator has derivative `Y(u)(∂t u - X_Kt)` at every
parameter `q`. The fields may depend on the domain point. -/
theorem hasDerivAt_floerOperator_add_smul (ω : SymplecticForm V)
    (J Y : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (u : ℝ × ℝ → V) (z : ℝ × ℝ) (q : ℝ) :
    HasDerivAt (fun q : ℝ ↦ ω.floerOperator (fun w x ↦ J w x + q • Y w x) Ks Kt u z)
      (Y z (u z) (fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z))) q := by
  set ξ := fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z)
  have h (q : ℝ) : ω.floerOperator (fun w x ↦ J w x + q • Y w x) Ks Kt u z =
      ω.floerOperator J Ks Kt u z + q • Y z (u z) ξ := by
    simp only [floerOperator_def, _root_.add_apply, _root_.smul_apply, ξ]
    abel
  simp only [h]
  simpa using
    ((hasDerivAt_id q).smul_const (Y z (u z) ξ)).const_add (ω.floerOperator J Ks Kt u z)

/-- The map-direction linearization with `J` and `K` fixed. Both Hamiltonian derivatives and
the target derivative of `J` are retained, including along constant maps. -/
noncomputable def floerLinearization (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (u ξ : ℝ × ℝ → V) (z : ℝ × ℝ) : V :=
  fderiv ℝ ξ z stdComplexLineReal -
      fderiv ℝ (ω.hamiltonianVectorField (Ks z)) (u z) (ξ z) +
    fderiv ℝ (J z) (u z) (ξ z)
      (fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z)) +
    J z (u z) (fderiv ℝ ξ z stdComplexLineImag -
      fderiv ℝ (ω.hamiltonianVectorField (Kt z)) (u z) (ξ z))

/-- The coordinate expression of the map-direction linearization. -/
theorem floerLinearization_def (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (u ξ : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ω.floerLinearization J Ks Kt u ξ z =
      fderiv ℝ ξ z stdComplexLineReal -
          fderiv ℝ (ω.hamiltonianVectorField (Ks z)) (u z) (ξ z) +
        fderiv ℝ (J z) (u z) (ξ z)
          (fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z)) +
        J z (u z) (fderiv ℝ ξ z stdComplexLineImag -
          fderiv ℝ (ω.hamiltonianVectorField (Kt z)) (u z) (ξ z)) :=
  (rfl)

/-- **The linearized Floer operator for a constant structure and `K = H dt`.** For a constant
almost complex structure `J` and Hamiltonians `H_z` depending on the domain point, the linearized
Floer operator of `K = H dt` along `u` is `D ξ = ∂s ξ + J (∂t ξ - dX_{H_z}(u) ξ)`. -/
theorem floerLinearization_const_eq (ω : SymplecticForm V) (J : AlmostComplexStructure V)
    (H : ℝ × ℝ → V → ℝ) (u ξ : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ω.floerLinearization (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) H u ξ z =
      fderiv ℝ ξ z (1, 0) +
        J (fderiv ℝ ξ z (0, 1) - fderiv ℝ (ω.hamiltonianVectorField (H z)) (u z) (ξ z)) := by
  simp [floerLinearization_def, hamiltonianVectorField_const, stdComplexLineReal_eq,
    stdComplexLineImag_eq]

/-- **The zero equation for a constant structure and `K = H dt`.** Along any map `u`, the linearized
Floer operator of `K = H dt` with the constant structure `J` vanishes at the point `z` exactly when
`∂s ξ = -J ∂t ξ + J dX_{H_z}(u) ξ` holds at `z`. The partial derivatives are Mathlib's totalized
`fderiv`, so neither side asserts that `ξ` is differentiable at `z`. -/
theorem floerLinearization_const_eq_zero_iff (ω : SymplecticForm V) (J : AlmostComplexStructure V)
    (H : ℝ × ℝ → V → ℝ) {u ξ : ℝ × ℝ → V} {z : ℝ × ℝ} :
    ω.floerLinearization (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) H u ξ z =
        0 ↔
      fderiv ℝ ξ z (1, 0) =
        -J (fderiv ℝ ξ z (0, 1)) + J (fderiv ℝ (ω.hamiltonianVectorField (H z)) (u z) (ξ z)) := by
  rw [floerLinearization_const_eq, map_sub]
  constructor <;> intro h <;> linear_combination (norm := module) h

/-- **The linearized operator on directions that do not depend on `t`.** Along any map `u`, the
linearized Floer operator of `K = H dt` with the constant structure `J`, applied to the direction
`(s, t) ↦ ζ(s)`, is `ζ'(s) - J dX_{H_z}(u(z)) ζ(s)` at `z = (s, t)`. Here `ζ'` is Mathlib's
totalized `deriv`, so no differentiability of `ζ` is assumed. -/
theorem floerLinearization_comp_fst (ω : SymplecticForm V) (J : AlmostComplexStructure V)
    (H : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) (ζ : ℝ → V) (z : ℝ × ℝ) :
    ω.floerLinearization (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) H u
        (fun w ↦ ζ w.1) z =
      deriv ζ z.1 - J (fderiv ℝ (ω.hamiltonianVectorField (H z)) (u z) (ζ z.1)) := by
  rw [floerLinearization_const_eq, fderiv_comp_fst]
  simp [sub_eq_add_neg]

/-- The linearization is additive on directions differentiable at the domain point. -/
@[simp]
theorem floerLinearization_add (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (u ξ η : ℝ × ℝ → V) (z : ℝ × ℝ) (hξ : DifferentiableAt ℝ ξ z)
    (hη : DifferentiableAt ℝ η z) :
    ω.floerLinearization J Ks Kt u (ξ + η) z =
      ω.floerLinearization J Ks Kt u ξ z + ω.floerLinearization J Ks Kt u η z := by
  simp only [floerLinearization_def, fderiv_add hξ hη, add_apply, Pi.add_apply, map_add,
    map_sub]
  abel

/-- The linearization is subtractive on directions differentiable at the domain point. -/
@[simp]
theorem floerLinearization_sub (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (u ξ η : ℝ × ℝ → V) (z : ℝ × ℝ) (hξ : DifferentiableAt ℝ ξ z)
    (hη : DifferentiableAt ℝ η z) :
    ω.floerLinearization J Ks Kt u (ξ - η) z =
      ω.floerLinearization J Ks Kt u ξ z - ω.floerLinearization J Ks Kt u η z := by
  simp only [floerLinearization_def, fderiv_sub hξ hη, sub_apply, Pi.sub_apply, map_sub]
  abel

/-- The linearization respects real scaling. -/
@[simp]
theorem floerLinearization_smul (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (u ξ : ℝ × ℝ → V) (z : ℝ × ℝ) (c : ℝ) :
    ω.floerLinearization J Ks Kt u (c • ξ) z = c • ω.floerLinearization J Ks Kt u ξ z := by
  simp only [floerLinearization_def, fderiv_const_smul_field c, smul_apply, Pi.smul_apply,
    map_smul, map_sub, smul_sub, smul_add]

/-- The linearization sends the zero direction to zero. -/
@[simp]
theorem floerLinearization_zero (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (u : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ω.floerLinearization J Ks Kt u 0 z = 0 := by
  simp [floerLinearization_def]

/-- The linearization at `z` depends only on the germ of the direction at `z`. -/
theorem floerLinearization_congr_of_eventuallyEq (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (u : ℝ × ℝ → V) {ξ η : ℝ × ℝ → V} {z : ℝ × ℝ} (h : ξ =ᶠ[nhds z] η) :
    ω.floerLinearization J Ks Kt u ξ z = ω.floerLinearization J Ks Kt u η z := by
  rw [floerLinearization_def, floerLinearization_def, h.fderiv_eq, h.eq_of_nhds]

/-- The linearized Floer operator vanishes off the support of the direction. -/
theorem floerLinearization_of_notMem_tsupport (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) {ξ : ℝ × ℝ → V}
    {z : ℝ × ℝ} (hz : z ∉ tsupport ξ) : ω.floerLinearization J Ks Kt u ξ z = 0 := by
  rw [ω.floerLinearization_congr_of_eventuallyEq J Ks Kt u
    (notMem_tsupport_iff_eventuallyEq.1 hz)]
  exact ω.floerLinearization_zero J Ks Kt u z

/-- The support of the linearization is contained in the support of the direction. -/
theorem tsupport_floerLinearization_subset (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u ξ : ℝ × ℝ → V) :
    tsupport (ω.floerLinearization J Ks Kt u ξ) ⊆ tsupport ξ :=
  closure_minimal (fun _ hz ↦ by_contra fun h ↦
    hz (ω.floerLinearization_of_notMem_tsupport J Ks Kt u h)) (isClosed_tsupport ξ)

/-- **The linearized operator of a translate.** The linearized Floer operator of the data
`w ↦ (J, K_s, K_t, u) (w + v)` in the direction `w ↦ ξ (w + v)` at `z` is the linearized operator of
the data `(J, K_s, K_t, u)` in the direction `ξ` at `z + v`. -/
theorem floerLinearization_comp_add_right (ω : SymplecticForm V) (J : ℝ × ℝ → V → V →L[ℝ] V)
    (Ks Kt : ℝ × ℝ → V → ℝ) (u ξ : ℝ × ℝ → V) (v z : ℝ × ℝ) :
    ω.floerLinearization (fun w ↦ J (w + v)) (fun w ↦ Ks (w + v)) (fun w ↦ Kt (w + v))
        (fun w ↦ u (w + v)) (fun w ↦ ξ (w + v)) z =
      ω.floerLinearization J Ks Kt u ξ (z + v) := by
  simp only [floerLinearization_def, fderiv_comp_add_right]

/-- The linearization at `z` depends on the Floer data `J`, `Ks`, `Kt` only through their values
at `z`, as functions of the target point. -/
theorem floerLinearization_congr_data (ω : SymplecticForm V)
    {J J' : ℝ × ℝ → V → V →L[ℝ] V} {Ks Ks' Kt Kt' : ℝ × ℝ → V → ℝ} (u ξ : ℝ × ℝ → V)
    {z : ℝ × ℝ} (hJ : J z = J' z) (hKs : Ks z = Ks' z) (hKt : Kt z = Kt' z) :
    ω.floerLinearization J Ks Kt u ξ z = ω.floerLinearization J' Ks' Kt' u ξ z := by
  rw [floerLinearization_def, floerLinearization_def, hJ, hKs, hKt]

/-- The linearization in the direction `ξ` depends on the Floer data `J`, `Ks`, `Kt` only through
their values on the support of `ξ`: off the support both linearizations vanish. -/
theorem floerLinearization_congr_data_of_tsupport (ω : SymplecticForm V)
    {J J' : ℝ × ℝ → V → V →L[ℝ] V} {Ks Ks' Kt Kt' : ℝ × ℝ → V → ℝ} (u ξ : ℝ × ℝ → V)
    (h : ∀ z ∈ tsupport ξ, J z = J' z ∧ Ks z = Ks' z ∧ Kt z = Kt' z) :
    ω.floerLinearization J Ks Kt u ξ = ω.floerLinearization J' Ks' Kt' u ξ := by
  funext z
  by_cases hz : z ∈ tsupport ξ
  · obtain ⟨hJ, hKs, hKt⟩ := h z hz
    exact ω.floerLinearization_congr_data u ξ hJ hKs hKt
  · rw [ω.floerLinearization_of_notMem_tsupport J Ks Kt u hz,
      ω.floerLinearization_of_notMem_tsupport J' Ks' Kt' u hz]

/-- The zeroth-order part `ξ ↦ (dJ(u) ξ)(∂t u - X_Kt(u)) - dX_Ks(u) ξ - J(u) dX_Kt(u) ξ` of the
linearized Floer operator at the domain point `z`. -/
noncomputable def floerLinearizationCoeff (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) (z : ℝ × ℝ) :
    V →L[ℝ] V :=
  (fderiv ℝ (J z) (u z)).flip
      (fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z)) -
    fderiv ℝ (ω.hamiltonianVectorField (Ks z)) (u z) -
    (J z (u z)).comp (fderiv ℝ (ω.hamiltonianVectorField (Kt z)) (u z))

/-- The zeroth-order part of the linearized operator at `z` depends on the Floer data `J`, `Ks`,
`Kt` only through their values at `z`, as functions of the target point. -/
theorem floerLinearizationCoeff_congr_data (ω : SymplecticForm V)
    {J J' : ℝ × ℝ → V → V →L[ℝ] V} {Ks Ks' Kt Kt' : ℝ × ℝ → V → ℝ} (u : ℝ × ℝ → V)
    {z : ℝ × ℝ} (hJ : J z = J' z) (hKs : Ks z = Ks' z) (hKt : Kt z = Kt' z) :
    ω.floerLinearizationCoeff J Ks Kt u z = ω.floerLinearizationCoeff J' Ks' Kt' u z := by
  rw [floerLinearizationCoeff, floerLinearizationCoeff, hJ, hKs, hKt]

/-- The zeroth-order part of the linearized Floer operator, evaluated on a vector. -/
theorem floerLinearizationCoeff_apply (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) (z : ℝ × ℝ) (v : V) :
    ω.floerLinearizationCoeff J Ks Kt u z v =
      fderiv ℝ (J z) (u z) v
          (fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z)) -
        fderiv ℝ (ω.hamiltonianVectorField (Ks z)) (u z) v -
        J z (u z) (fderiv ℝ (ω.hamiltonianVectorField (Kt z)) (u z) v) :=
  (rfl)

/-- Where the structures are a fixed `J₀`, independent of the target point, and the Hamiltonian
perturbations vanish, the zeroth-order part of the linearized Floer operator vanishes. -/
theorem floerLinearizationCoeff_eq_zero_of_eq_base (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} (u : ℝ × ℝ → V) {z : ℝ × ℝ}
    {J₀ : V →L[ℝ] V} (hJ₀ : ∀ y, J z y = J₀) (hKs₀ : ∀ y, Ks z y = 0)
    (hKt₀ : ∀ y, Kt z y = 0) :
    ω.floerLinearizationCoeff J Ks Kt u z = 0 := by
  have hJ : J z = fun _ ↦ J₀ := funext hJ₀
  have hKs : Ks z = fun _ ↦ 0 := funext hKs₀
  have hKt : Kt z = fun _ ↦ 0 := funext hKt₀
  ext v
  simp [floerLinearizationCoeff_apply, hJ, hKs, hKt, hamiltonianVectorField_const]

/-- The linearized Floer operator is `∂s ξ + J(z, u z) ∂t ξ` plus its zeroth-order part
`floerLinearizationCoeff`. -/
theorem floerLinearization_eq_add (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u ξ : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ω.floerLinearization J Ks Kt u ξ z =
      fderiv ℝ ξ z stdComplexLineReal + J z (u z) (fderiv ℝ ξ z stdComplexLineImag) +
        ω.floerLinearizationCoeff J Ks Kt u z (ξ z) := by
  simp only [floerLinearization_def, floerLinearizationCoeff_apply, map_sub]
  abel

/-- **Comparing two linearized operators at a point.** The linearized Floer operators
`∂s ξ + J(z, u z) ∂t ξ + C(z) ξ` of two data sets differ at `z` by at most
`‖J(z, u z) - J₁(z, u₁ z)‖ ‖∂t ξ‖ + ‖C(z) - C₁(z)‖ ‖ξ‖`, where `C = floerLinearizationCoeff`. -/
theorem norm_floerLinearization_sub_floerLinearization_le (ω : SymplecticForm V)
    (J J₁ : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt Ks₁ Kt₁ : ℝ × ℝ → V → ℝ) (u u₁ ξ : ℝ × ℝ → V)
    (z : ℝ × ℝ) :
    ‖ω.floerLinearization J Ks Kt u ξ z - ω.floerLinearization J₁ Ks₁ Kt₁ u₁ ξ z‖ ≤
      ‖J z (u z) - J₁ z (u₁ z)‖ * ‖fderiv ℝ ξ z stdComplexLineImag‖ +
        ‖ω.floerLinearizationCoeff J Ks Kt u z - ω.floerLinearizationCoeff J₁ Ks₁ Kt₁ u₁ z‖ *
          ‖ξ z‖ := by
  rw [floerLinearization_eq_add, floerLinearization_eq_add,
    show ∀ a b c b' c' : V, a + b + c - (a + b' + c') = (b - b') + (c - c') by
      intro a b c b' c'; abel, ← sub_apply, ← sub_apply]
  exact (norm_add_le _ _).trans (add_le_add (le_opNorm _ _) (le_opNorm _ _))

/-- **Multiplying by a function.** If `f` and `ξ` are differentiable at `z`, the linearized Floer
operator at `z` sends `f ξ` to `f D ξ + (∂s f) ξ + (∂t f) J ξ`. -/
theorem floerLinearization_fun_smul (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u ξ : ℝ × ℝ → V) {z : ℝ × ℝ}
    {f : ℝ × ℝ → ℝ} (hf : DifferentiableAt ℝ f z) (hξ : DifferentiableAt ℝ ξ z) :
    ω.floerLinearization J Ks Kt u (fun w ↦ f w • ξ w) z =
      f z • ω.floerLinearization J Ks Kt u ξ z + fderiv ℝ f z stdComplexLineReal • ξ z +
        fderiv ℝ f z stdComplexLineImag • J z (u z) (ξ z) := by
  simp only [floerLinearization_eq_add]
  rw [cauchyRiemann_fun_smul (fun z ↦ J z (u z)) (ω.floerLinearizationCoeff J Ks Kt u) hf hξ,
    map_smul]

/-- **The operator on a cut-off direction, pointwise.** If `|f| ≤ 1`, `‖df‖ ≤ M` and `‖J‖ ≤ B` at
`z`, then `‖D (f ξ)‖² ≤ 2 ‖D ξ‖² + 2 (M (1 + B))² ‖ξ‖²` at `z`. -/
theorem norm_floerLinearization_fun_smul_sq_le (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u ξ : ℝ × ℝ → V) {z : ℝ × ℝ}
    {f : ℝ × ℝ → ℝ} (hf : DifferentiableAt ℝ f z) (hξ : DifferentiableAt ℝ ξ z)
    (hf₁ : |f z| ≤ 1) {M B : ℝ} (hM : ‖fderiv ℝ f z‖ ≤ M) (hB : ‖J z (u z)‖ ≤ B) :
    ‖ω.floerLinearization J Ks Kt u (fun w ↦ f w • ξ w) z‖ ^ 2 ≤
      2 * ‖ω.floerLinearization J Ks Kt u ξ z‖ ^ 2 + 2 * (M * (1 + B)) ^ 2 * ‖ξ z‖ ^ 2 := by
  have hM₀ : 0 ≤ M := (norm_nonneg _).trans hM
  have h₁ : ‖fderiv ℝ f z stdComplexLineReal • ξ z‖ ≤ M * ‖ξ z‖ := by
    rw [norm_smul]
    gcongr
    exact (ContinuousLinearMap.le_opNorm _ _).trans (by simp [stdComplexLineReal, hM])
  have h₂ : ‖fderiv ℝ f z stdComplexLineImag • J z (u z) (ξ z)‖ ≤ M * (B * ‖ξ z‖) := by
    rw [norm_smul]
    gcongr
    · exact (ContinuousLinearMap.le_opNorm _ _).trans (by simp [stdComplexLineImag, hM])
    · exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr)
  rw [ω.floerLinearization_fun_smul J Ks Kt u ξ hf hξ]
  exact norm_smul_add_add_sq_le hf₁ h₁ h₂

/-- **Multiplying by a cutoff in `s`.** If `β` has derivative `β'` at `s`, the linearization at
`z = (s, t)` sends `β(s) ξ` to `β(s) D ξ + β' ξ`: the factor only differentiates in the `s`
direction, where the operator has the leading term `∂s`. -/
theorem floerLinearization_smul_fst (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (u ξ : ℝ × ℝ → V) {z : ℝ × ℝ} {β : ℝ → ℝ} {β' : ℝ} (hβ : HasDerivAt β β' z.1)
    (hξ : DifferentiableAt ℝ ξ z) :
    ω.floerLinearization J Ks Kt u (fun w ↦ β w.1 • ξ w) z =
      β z.1 • ω.floerLinearization J Ks Kt u ξ z + β' • ξ z := by
  simp only [floerLinearization_eq_add]
  exact cauchyRiemann_smul_fst (fun z ↦ J z (u z)) (ω.floerLinearizationCoeff J Ks Kt u) hβ hξ

/-- **Conjugating the linearization by an exponential weight.** If the weight `κ` has derivative
`κ'` at `s`, then on maps of the form `e^{-κ(s)} ξ` the linearized Floer operator acts at
`z = (s, t)` as `e^{-κ(s)} (D ξ - κ' ξ)`: this is the case `β = e^{-κ}` of
`floerLinearization_smul_fst`. So `D - κ'` is `D` conjugated by the weight `e^{κ(s)}`. -/
theorem floerLinearization_exp_neg_smul (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (u ξ : ℝ × ℝ → V) {z : ℝ × ℝ} {κ : ℝ → ℝ} {κ' : ℝ} (hκ : HasDerivAt κ κ' z.1)
    (hξ : DifferentiableAt ℝ ξ z) :
    ω.floerLinearization J Ks Kt u (fun w ↦ Real.exp (-κ w.1) • ξ w) z =
      Real.exp (-κ z.1) • (ω.floerLinearization J Ks Kt u ξ z - κ' • ξ z) := by
  rw [floerLinearization_smul_fst ω J Ks Kt u ξ (β := fun s ↦ Real.exp (-κ s)) hκ.neg.exp hξ]
  module

/-- **Conjugating the linearization by a linear exponential weight.** On maps of the form
`e^{-δ s} ξ`, the linearized Floer operator acts as `e^{-δ s} (D - δ) ξ`: this is the case
`κ(s) = δ s` of `floerLinearization_exp_neg_smul`. -/
theorem floerLinearization_exp_smul (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (u ξ : ℝ × ℝ → V) {z : ℝ × ℝ} (δ : ℝ) (hξ : DifferentiableAt ℝ ξ z) :
    ω.floerLinearization J Ks Kt u (fun w ↦ Real.exp (-(δ * w.1)) • ξ w) z =
      Real.exp (-(δ * z.1)) • (ω.floerLinearization J Ks Kt u ξ z - δ • ξ z) := by
  simpa only [mul_one] using
    ω.floerLinearization_exp_neg_smul J Ks Kt u ξ ((hasDerivAt_id' z.1).const_mul δ) hξ

/-- **Smoothness of the zeroth-order part along a family of data.** For a family of data
`(J_μ, K_{s,μ}, K_{t,μ})` with parameter `μ ∈ P`, the zeroth-order part of the linearized Floer
operator of the data at `μ` along `u`, at `z`, is `Cⁿ` jointly in `(μ, z)` at `p` when `J` is
`Cⁿ⁺¹` and the Hamiltonians `Cⁿ⁺²` jointly in `μ`, `z` and the target point at `(p, u p.2)`, and
`u` is `Cⁿ⁺¹` at `p.2`. -/
theorem contDiffAt_floerLinearizationCoeff_family (ω : SymplecticForm V)
    {J : P × (ℝ × ℝ) → V → V →L[ℝ] V} {Ks Kt : P × (ℝ × ℝ) → V → ℝ} {u : ℝ × ℝ → V}
    {p : P × (ℝ × ℝ)} {n : WithTop ℕ∞} (hJ : ContDiffAt ℝ (n + 1) (Function.uncurry J) (p, u p.2))
    (hKs : ContDiffAt ℝ (n + 2) (Function.uncurry Ks) (p, u p.2))
    (hKt : ContDiffAt ℝ (n + 2) (Function.uncurry Kt) (p, u p.2))
    (hu : ContDiffAt ℝ (n + 1) u p.2) :
    ContDiffAt ℝ n (fun q : P × (ℝ × ℝ) ↦ ω.floerLinearizationCoeff (fun z ↦ J (q.1, z))
      (fun z ↦ Ks (q.1, z)) (fun z ↦ Kt (q.1, z)) u q.2) p := by
  have hu' : ContDiffAt ℝ (n + 1) (fun q : P × (ℝ × ℝ) ↦ u q.2) p := hu.comp p contDiffAt_snd
  have hun : ContDiffAt ℝ n (fun q : P × (ℝ × ℝ) ↦ u q.2) p := hu'.of_le le_self_add
  have hgraph : ContDiffAt ℝ (n + 1) (fun q : P × (ℝ × ℝ) ↦ (q, u q.2)) p :=
    contDiffAt_id.prodMk hu'
  have h2 : n + 2 = n + 1 + 1 := by rw [add_assoc, one_add_one_eq_two]
  have hXs := ω.contDiffAt_hamiltonianVectorField_uncurry (n := n + 1) (h2 ▸ hKs)
  have hXt := ω.contDiffAt_hamiltonianVectorField_uncurry (n := n + 1) (h2 ▸ hKt)
  have hdJ : ContDiffAt ℝ n (fun q ↦ fderiv ℝ (J q) (u q.2)) p :=
    hJ.fderiv (f := fun q y ↦ J q y) hun le_rfl
  have hdXs : ContDiffAt ℝ n (fun q ↦ fderiv ℝ (ω.hamiltonianVectorField (Ks q)) (u q.2)) p :=
    hXs.fderiv (f := fun q y ↦ ω.hamiltonianVectorField (Ks q) y) hun le_rfl
  have hdXt : ContDiffAt ℝ n (fun q ↦ fderiv ℝ (ω.hamiltonianVectorField (Kt q)) (u q.2)) p :=
    hXt.fderiv (f := fun q y ↦ ω.hamiltonianVectorField (Kt q) y) hun le_rfl
  have hut : ContDiffAt ℝ n (fun q : P × (ℝ × ℝ) ↦ fderiv ℝ u q.2 stdComplexLineImag) p :=
    ((hu.fderiv_right le_rfl).clm_apply contDiffAt_const).comp p contDiffAt_snd
  have hXtu : ContDiffAt ℝ n (fun q ↦ ω.hamiltonianVectorField (Kt q) (u q.2)) p :=
    (hXt.comp (f := fun q : P × (ℝ × ℝ) ↦ (q, u q.2)) p hgraph).of_le le_self_add
  have hJu : ContDiffAt ℝ n (fun q ↦ J q (u q.2)) p :=
    (hJ.comp (f := fun q : P × (ℝ × ℝ) ↦ (q, u q.2)) p hgraph).of_le le_self_add
  have hflip : ContDiffAt ℝ n (fun q ↦ (fderiv ℝ (J q) (u q.2)).flip) p :=
    (flipₗᵢ ℝ V V V).contDiff.contDiffAt.comp p hdJ
  exact ((hflip.clm_apply (hut.sub hXtu)).sub hdXs).sub (hJu.clm_comp hdXt)

/-- **Smoothness of the zeroth-order part.** The zeroth-order part of the linearized Floer operator
is `Cⁿ` at `z` when `J` is `Cⁿ⁺¹` and the Hamiltonians `K_s`, `K_t` are `Cⁿ⁺²` at `(z, u z)`,
jointly in the domain and target point, and `u` is `Cⁿ⁺¹` at `z`. -/
theorem contDiffAt_floerLinearizationCoeff (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V} {z : ℝ × ℝ}
    {n : WithTop ℕ∞} (hJ : ContDiffAt ℝ (n + 1) (Function.uncurry J) (z, u z))
    (hKs : ContDiffAt ℝ (n + 2) (Function.uncurry Ks) (z, u z))
    (hKt : ContDiffAt ℝ (n + 2) (Function.uncurry Kt) (z, u z)) (hu : ContDiffAt ℝ (n + 1) u z) :
    ContDiffAt ℝ n (ω.floerLinearizationCoeff J Ks Kt u) z := by
  -- The data form a constant family over the parameter space `ℝ`.
  have hπ {m : WithTop ℕ∞} :
      ContDiffAt ℝ m (fun x : (ℝ × (ℝ × ℝ)) × V ↦ (x.1.2, x.2)) (((0 : ℝ), z), u z) :=
    (contDiff_fst.snd.prodMk contDiff_snd).contDiffAt
  have h := ω.contDiffAt_floerLinearizationCoeff_family (P := ℝ) (J := fun q ↦ J q.2)
    (Ks := fun q ↦ Ks q.2) (Kt := fun q ↦ Kt q.2) (p := (0, z))
    (hJ.comp (((0 : ℝ), z), u z) hπ) (hKs.comp (((0 : ℝ), z), u z) hπ)
    (hKt.comp (((0 : ℝ), z), u z) hπ) hu
  exact h.comp (f := fun w : ℝ × ℝ ↦ ((0 : ℝ), w)) z (contDiffAt_const.prodMk contDiffAt_id)

/-- The zeroth-order part of the linearized Floer operator is continuous at `z` when the data are
`C¹` (and the Hamiltonians `C²`) at `(z, u z)`, and `u` is `C¹` at `z`. -/
theorem continuousAt_floerLinearizationCoeff (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V} {z : ℝ × ℝ}
    (hJ : ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z)) (hu : ContDiffAt ℝ 1 u z) :
    ContinuousAt (ω.floerLinearizationCoeff J Ks Kt u) z :=
  (ω.contDiffAt_floerLinearizationCoeff (n := 0) (by simpa using hJ) (by simpa using hKs)
    (by simpa using hKt) (by simpa using hu)).continuousAt

/-- **Continuity of the zeroth-order part along a family of data.** For a family of data
`(J_μ, K_{s,μ}, K_{t,μ})` with parameter `μ ∈ P`, the zeroth-order part of the linearized Floer
operator of the data at `μ` along `u`, at `z`, is continuous jointly in `(μ, z)` at `p` when the
family is `C¹` (with `C²` Hamiltonians) jointly in `μ`, `z` and the target point at
`(p, u p.2)`, and `u` is `C¹` at `p.2`. -/
theorem continuousAt_floerLinearizationCoeff_family (ω : SymplecticForm V)
    {J : P × (ℝ × ℝ) → V → V →L[ℝ] V} {Ks Kt : P × (ℝ × ℝ) → V → ℝ} {u : ℝ × ℝ → V}
    {p : P × (ℝ × ℝ)} (hJ : ContDiffAt ℝ 1 (Function.uncurry J) (p, u p.2))
    (hKs : ContDiffAt ℝ 2 (Function.uncurry Ks) (p, u p.2))
    (hKt : ContDiffAt ℝ 2 (Function.uncurry Kt) (p, u p.2)) (hu : ContDiffAt ℝ 1 u p.2) :
    ContinuousAt (fun q : P × (ℝ × ℝ) ↦ ω.floerLinearizationCoeff (fun z ↦ J (q.1, z))
      (fun z ↦ Ks (q.1, z)) (fun z ↦ Kt (q.1, z)) u q.2) p :=
  (ω.contDiffAt_floerLinearizationCoeff_family (n := 0) (by simpa using hJ) (by simpa using hKs)
    (by simpa using hKt) (by simpa using hu)).continuousAt

/-- The zeroth-order part of the linearized Floer operator is continuous on `K` when the data are
`C¹` (and the Hamiltonians `C²`) at the points `(z, u z)` with `z ∈ K`, and `u` is `C¹` on `K`. -/
theorem continuousOn_floerLinearizationCoeff (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V} {K : Set (ℝ × ℝ)}
    (hJ : ∀ z ∈ K, ContDiffAt ℝ 1 (fun p : (ℝ × ℝ) × V ↦ J p.1 p.2) (z, u z))
    (hKs : ∀ z ∈ K, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ K, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z))
    (hu : ∀ z ∈ K, ContDiffAt ℝ 1 u z) :
    ContinuousOn (ω.floerLinearizationCoeff J Ks Kt u) K := fun z hz ↦
  (ω.continuousAt_floerLinearizationCoeff (hJ z hz) (hKs z hz) (hKt z hz)
    (hu z hz)).continuousWithinAt

/-- **Continuity of the linearization.** Let `u` and `ξ` be `C¹` at `z`, and let the
coefficients `J` be `C¹` and the Hamiltonians `K_s`, `K_t` be `C²` at `(z, u z)`, jointly in the
domain and target point. Then the linearized Floer operator along `u` in the direction `ξ` is
continuous at `z`. -/
theorem continuousAt_floerLinearization (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u ξ : ℝ × ℝ → V} {z : ℝ × ℝ}
    (hJ : ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z)) (hu : ContDiffAt ℝ 1 u z)
    (hξ : ContDiffAt ℝ 1 ξ z) :
    ContinuousAt (ω.floerLinearization J Ks Kt u ξ) z := by
  have hdξ (v : ℝ × ℝ) : ContinuousAt (fun w ↦ fderiv ℝ ξ w v) z :=
    (hξ.continuousAt_fderiv one_ne_zero).clm_apply continuousAt_const
  have hJu : ContinuousAt (fun w ↦ J w (u w)) z :=
    ContinuousAt.comp (f := fun w ↦ (w, u w)) hJ.continuousAt
      (continuousAt_id.prodMk hu.continuousAt)
  rw [show ω.floerLinearization J Ks Kt u ξ = _ from
    funext (ω.floerLinearization_eq_add J Ks Kt u ξ)]
  exact ((hdξ _).add (hJu.clm_apply (hdξ _))).add
    ((ω.continuousAt_floerLinearizationCoeff hJ hKs hKt hu).clm_apply hξ.continuousAt)

/-- The linearized Floer operator in a direction `ξ` supported in an open set `U` is continuous
when the data are regular along `u` on `U`. -/
theorem continuous_floerLinearization_of_tsupport_subset (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u ξ : ℝ × ℝ → V} {U : Set (ℝ × ℝ)}
    (hJ : ∀ z ∈ U, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z ∈ U, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ U, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z))
    (hu : ∀ z ∈ U, ContDiffAt ℝ 1 u z) (hξ : ContDiff ℝ 1 ξ) (hξU : tsupport ξ ⊆ U) :
    Continuous (ω.floerLinearization J Ks Kt u ξ) := by
  refine continuous_iff_continuousAt.2 fun z ↦ ?_
  by_cases hz : z ∈ U
  · exact ω.continuousAt_floerLinearization (hJ z hz) (hKs z hz) (hKt z hz) (hu z hz)
      hξ.contDiffAt
  · have h : ω.floerLinearization J Ks Kt u ξ =ᶠ[nhds z] fun _ ↦ 0 :=
      Filter.mem_of_superset ((isClosed_tsupport ξ).isOpen_compl.mem_nhds fun h ↦ hz (hξU h))
        fun w hw ↦ ω.floerLinearization_of_notMem_tsupport J Ks Kt u hw
    exact continuousAt_const.congr h.symm

/-- **Global continuity of the linearization.** Let `u` and `ξ` be `C¹`, and let the coefficients
`J` be `C¹` and the Hamiltonians `K_s`, `K_t` be `C²` at every point `(z, u z)`. Then the linearized
Floer operator along `u` in the direction `ξ` is continuous. -/
theorem continuous_floerLinearization (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u ξ : ℝ × ℝ → V}
    (hJ : ∀ z, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z)) (hu : ContDiff ℝ 1 u)
    (hξ : ContDiff ℝ 1 ξ) : Continuous (ω.floerLinearization J Ks Kt u ξ) :=
  ω.continuous_floerLinearization_of_tsupport_subset (U := Set.univ) (fun z _ ↦ hJ z)
    (fun z _ ↦ hKs z) (fun z _ ↦ hKt z) (fun _ _ ↦ hu.contDiffAt) hξ (Set.subset_univ _)

/-- The linearized Floer operator in a compactly supported direction is compactly supported. -/
theorem hasCompactSupport_floerLinearization (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) {ξ : ℝ × ℝ → V}
    (hξ : HasCompactSupport ξ) : HasCompactSupport (ω.floerLinearization J Ks Kt u ξ) :=
  hξ.mono' fun _ hz ↦ by_contra fun h ↦ hz (ω.floerLinearization_of_notMem_tsupport J Ks Kt u h)

/-- Where the linearized Floer operator in a compactly supported direction is continuous, its
square norm is integrable. -/
theorem integrable_norm_floerLinearization_sq (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u ξ : ℝ × ℝ → V}
    {μ : MeasureTheory.Measure (ℝ × ℝ)} [MeasureTheory.IsFiniteMeasureOnCompacts μ]
    (hD : Continuous (ω.floerLinearization J Ks Kt u ξ)) (hξ : HasCompactSupport ξ) :
    MeasureTheory.Integrable (fun z ↦ ‖ω.floerLinearization J Ks Kt u ξ z‖ ^ 2) μ :=
  Continuous.integrable_of_hasCompactSupport (by fun_prop)
    ((ω.hasCompactSupport_floerLinearization J Ks Kt u hξ).comp_left (g := fun v ↦ ‖v‖ ^ 2)
      (by simp))

/-- **The cost of a cutoff, for data regular on a set.** Let the data be regular along `u` on a
set `U`, and let `β` be a `C¹` function with values in `[0, 1]` whose derivative vanishes off a
compact set `K ⊆ U`. Then multiplying a `C¹` direction `ξ` of compact support in `U` by `β` gives a
direction whose `D_u` has squared `L²` norm at most twice that of `D_u ξ` plus a multiple of the
squared `L²` norm of `ξ` over `K`: `∫ ‖D_u (β ξ)‖² ≤ 2 ∫ ‖D_u ξ‖² + C ∫_K ‖ξ‖²`. -/
theorem exists_integral_norm_floerLinearization_smul_sq_le_of_tsupport_subset
    (ω : SymplecticForm V) {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    {U : Set (ℝ × ℝ)} (hJ : ∀ z ∈ U, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z ∈ U, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ U, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z))
    (hu : ∀ z ∈ U, ContDiffAt ℝ 1 u z)
    {β : ℝ × ℝ → ℝ} (hβ : ContDiff ℝ 1 β) (hβ1 : ∀ z, β z ∈ Set.Icc 0 1) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hKU : K ⊆ U) (hβK : ∀ z ∉ K, fderiv ℝ β z = 0) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 1 ξ → HasCompactSupport ξ → tsupport ξ ⊆ U →
      ∫ z, ‖ω.floerLinearization J Ks Kt u (fun w ↦ β w • ξ w) z‖ ^ 2 ≤
        2 * (∫ z, ‖ω.floerLinearization J Ks Kt u ξ z‖ ^ 2) + C * ∫ z in K, ‖ξ z‖ ^ 2 := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (f := fun z ↦ J z (u z)) fun z hz ↦
    ((hJ z (hKU hz)).continuousAt.comp₂ continuousAt_id
      (hu z (hKU hz)).continuousAt).continuousWithinAt
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hβ.continuous_fderiv one_ne_zero).continuousOn
  refine ⟨2 * (max M 0 * (1 + max B 0)) ^ 2, by positivity, fun ξ hξ hξc hξU ↦ ?_⟩
  have hint {η : ℝ × ℝ → V} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η)
      (hηU : tsupport η ⊆ U) :
      MeasureTheory.Integrable fun z ↦ 1 * ‖ω.floerLinearization J Ks Kt u η z‖ ^ 2 := by
    simpa only [one_mul] using ω.integrable_norm_floerLinearization_sq
      (ω.continuous_floerLinearization_of_tsupport_subset hJ hKs hKt hu hη hηU) hηc
  simpa only [one_mul, mul_one] using integral_mul_norm_fun_smul_sq_le
    (D := ω.floerLinearization J Ks Kt u) (S := Set.univ) (w := fun _ ↦ 1)
    (b := fun z ↦ ‖J z (u z)‖) (fun _ ↦ zero_le_one) hK
    (fun z _ h ↦ by_contra fun hz ↦ h (hβK z hz)) (fun z hz ↦ (hM z hz).trans (le_max_left _ _))
    (fun z hz ↦ (hB z hz).trans (le_max_left _ _)) zero_le_one (fun _ _ ↦ le_rfl) hξ.continuous
    (fun z _ _ _ hM' hB' ↦ ω.norm_floerLinearization_fun_smul_sq_le J Ks Kt u ξ
      (hβ.differentiable one_ne_zero z) (hξ.differentiable one_ne_zero z)
      (abs_le.2 ⟨by linarith [(hβ1 z).1], (hβ1 z).2⟩) hM' hB')
    (fun z hz ↦ (hz (Set.mem_univ z)).elim) (hint hξ hξc hξU)
    (hint (hβ.smul hξ) hξc.smul_left ((tsupport_smul_subset_right _ _).trans hξU))

/-- **The cost of a cutoff.** Let `β` be a `C¹` function with values in `[0, 1]` whose derivative
vanishes off a compact set `K`. Then multiplying a `C¹` direction `ξ` of compact
support by `β` gives a direction whose `D_u` has squared `L²` norm at most twice that of `D_u ξ`
plus a multiple of the squared `L²` norm of `ξ` over `K`:
`∫ ‖D_u (β ξ)‖² ≤ 2 ∫ ‖D_u ξ‖² + C ∫_K ‖ξ‖²`. -/
theorem exists_integral_norm_floerLinearization_smul_sq_le (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ z, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z)) (hu : ContDiff ℝ 1 u)
    {β : ℝ × ℝ → ℝ} (hβ : ContDiff ℝ 1 β) (hβ1 : ∀ z, β z ∈ Set.Icc 0 1) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hβK : ∀ z ∉ K, fderiv ℝ β z = 0) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 1 ξ → HasCompactSupport ξ →
      ∫ z, ‖ω.floerLinearization J Ks Kt u (fun w ↦ β w • ξ w) z‖ ^ 2 ≤
        2 * (∫ z, ‖ω.floerLinearization J Ks Kt u ξ z‖ ^ 2) + C * ∫ z in K, ‖ξ z‖ ^ 2 :=
  (ω.exists_integral_norm_floerLinearization_smul_sq_le_of_tsupport_subset (U := Set.univ)
    (fun z _ ↦ hJ z) (fun z _ ↦ hKs z) (fun z _ ↦ hKt z) (fun _ _ ↦ hu.contDiffAt) hβ hβ1 hK
    (Set.subset_univ K) hβK).imp fun _ ⟨hC, h⟩ ↦
      ⟨hC, fun _ hξ hξc ↦ h hξ hξc (Set.subset_univ _)⟩

/-- **Measurability of the Floer operator.** Let the coefficients `J` be jointly continuous and the
Hamiltonians `Ks`, `Kt` jointly `C¹`. Then the Floer operator of an almost everywhere strongly
measurable map is almost everywhere strongly measurable for the same measure on `ℝ × ℝ`: it is a
continuous function of the point, the value of the map and its two partial derivatives, which are
measurable. -/
theorem aestronglyMeasurable_floerOperator (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} (hJ : Continuous (Function.uncurry J))
    (hKs : ContDiff ℝ 1 (Function.uncurry Ks)) (hKt : ContDiff ℝ 1 (Function.uncurry Kt))
    {u : ℝ × ℝ → V} {μ : MeasureTheory.Measure (ℝ × ℝ)}
    (hu : MeasureTheory.AEStronglyMeasurable u μ) :
    MeasureTheory.AEStronglyMeasurable (ω.floerOperator J Ks Kt u) μ := by
  borelize V
  have hS := (ω.contDiff_hamiltonianVectorField_uncurry (n := 0) hKs).continuous
  have hT := (ω.contDiff_hamiltonianVectorField_uncurry (n := 0) hKt).continuous
  have hpt : Continuous fun q : (ℝ × ℝ) × V × V × V ↦ (q.1, q.2.1) :=
    continuous_fst.prodMk continuous_snd.fst
  have hG : Continuous fun q : (ℝ × ℝ) × V × V × V ↦
      q.2.2.1 - ω.hamiltonianVectorField (Ks q.1) q.2.1 +
        J q.1 q.2.1 (q.2.2.2 - ω.hamiltonianVectorField (Kt q.1) q.2.1) :=
    (continuous_snd.snd.fst.sub (hS.comp hpt)).add
      ((hJ.comp hpt).clm_apply (continuous_snd.snd.snd.sub (hT.comp hpt)))
  have hd (e : ℝ × ℝ) : MeasureTheory.AEStronglyMeasurable (fun z ↦ fderiv ℝ u z e) μ :=
    (measurable_fderiv_apply_const ℝ _ e).aestronglyMeasurable
  rw [funext (ω.floerOperator_def J Ks Kt u)]
  exact hG.comp_aestronglyMeasurable (aestronglyMeasurable_id.prodMk
    (hu.prodMk ((hd stdComplexLineReal).prodMk (hd stdComplexLineImag))))

section Families

variable (ω : SymplecticForm V)
variable (J : P → ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : P → ℝ × ℝ → V → ℝ)
variable (u : P → ℝ × ℝ → V) (p : P) (z : ℝ × ℝ)
variable (hu : ContDiffAt ℝ 2 (Function.uncurry u) (p, z))
variable (hJ : DifferentiableAt ℝ (Function.uncurry fun q y ↦ J q z y) (p, u p z))
variable (hKs : ContDiffAt ℝ 2 (Function.uncurry fun q y ↦ Ks q z y) (p, u p z))
variable (hKt : ContDiffAt ℝ 2 (Function.uncurry fun q y ↦ Kt q z y) (p, u p z))

include hu hJ hKs hKt

private theorem hasFDerivAt_floerOperator_aux :
    let A := fderiv ℝ (fun q ↦ fderiv ℝ (u q) z) p
    HasFDerivAt (fun q ↦ ω.floerOperator (J q) (Ks q) (Kt q) (u q) z)
      (A.flip stdComplexLineReal -
          fderiv ℝ (fun q ↦ ω.hamiltonianVectorField (Ks q z) (u q z)) p +
        ((J p z (u p z)).comp (A.flip stdComplexLineImag -
            fderiv ℝ (fun q ↦ ω.hamiltonianVectorField (Kt q z) (u q z)) p) +
          (fderiv ℝ (fun q ↦ J q z (u q z)) p).flip
            (fderiv ℝ (u p) z stdComplexLineImag -
              ω.hamiltonianVectorField (Kt p z) (u p z)))) p := by
  have hdu := (hu.fderiv (m := 1) contDiffAt_const (by norm_num)).differentiableAt one_ne_zero
  have hF : DifferentiableAt ℝ (Function.uncurry u) (p, z) := hu.differentiableAt (by norm_num)
  have huP : DifferentiableAt ℝ (fun q ↦ u q z) p := by
    simpa only [Function.comp_def, Function.uncurry_def] using
      (hF.hasFDerivAt.comp p (hasFDerivAt_prodMk_left (𝕜 := ℝ) p z)).differentiableAt
  have hX (K : P → ℝ × ℝ → V → ℝ)
      (hK : ContDiffAt ℝ 2 (Function.uncurry fun q y ↦ K q z y) (p, u p z)) :=
    ((ω.contDiffAt_hamiltonianVectorField_uncurry (K := fun q ↦ K q z) (n := 1)
      hK).differentiableAt one_ne_zero).comp p (differentiableAt_id.prodMk huP)
  have hJP := hJ.comp p (differentiableAt_id.prodMk huP)
  simpa only [floerOperator_def, Function.comp_def, Function.uncurry_def, id_eq,
    Pi.sub_def, Pi.add_def, comp_zero, zero_add] using
    ((hdu.hasFDerivAt.clm_apply (hasFDerivAt_const (x := p) stdComplexLineReal)).sub
      (hX Ks hKs).hasFDerivAt).add
      (hJP.hasFDerivAt.clm_apply
        ((hdu.hasFDerivAt.clm_apply (hasFDerivAt_const (x := p) stdComplexLineImag)).sub
          (hX Kt hKt).hasFDerivAt))

/-- The actual nonlinear Floer operator is differentiable along the stated coefficient and
map families. No Floer equation or regularity of a solution is assumed. -/
theorem differentiableAt_floerOperator :
    DifferentiableAt ℝ (fun q ↦ ω.floerOperator (J q) (Ks q) (Kt q) (u q) z) p :=
  (hasFDerivAt_floerOperator_aux ω J Ks Kt u p z hu hJ hKs hKt).differentiableAt

/-- **Universal variation of the inhomogeneous Floer operator.** In addition to the map
linearization, there are the terms `-X_(δKs) - J X_(δKt) + δJ(∂t u - X_Kt)`.
The direction field in the linearization is the actual parameter derivative of `u`. -/
theorem fderiv_floerOperator_apply (h : P) :
    fderiv ℝ (fun q ↦ ω.floerOperator (J q) (Ks q) (Kt q) (u q) z) p h =
      ω.floerLinearization (J p) (Ks p) (Kt p) (u p)
          (fun y ↦ fderiv ℝ (fun q ↦ u q y) p h) z -
        ω.hamiltonianVectorField (fun y ↦ fderiv ℝ (fun q ↦ Ks q z y) p h) (u p z) -
        J p z (u p z)
          (ω.hamiltonianVectorField (fun y ↦ fderiv ℝ (fun q ↦ Kt q z y) p h) (u p z)) +
        fderiv ℝ (fun q ↦ J q z (u p z)) p h
          (fderiv ℝ (u p) z stdComplexLineImag - ω.hamiltonianVectorField (Kt p z) (u p z)) := by
  have hA := hasFDerivAt_spatialFDeriv (𝕜 := ℝ) (F := fun w ↦ u w.1 w.2)
    (p := p) (x := z)
    (by simpa only [minSmoothness_of_isRCLikeNormedField, Function.uncurry_def] using hu)
  have hξ := hasFDerivAt_parameterFDeriv_apply (F := fun w ↦ u w.1 w.2) hu h
  have hF : DifferentiableAt ℝ (Function.uncurry u) (p, z) := hu.differentiableAt (by norm_num)
  have huP : DifferentiableAt ℝ (fun q ↦ u q z) p := by
    simpa only [Function.comp_def, Function.uncurry_def] using
      (hF.hasFDerivAt.comp p (hasFDerivAt_prodMk_left (𝕜 := ℝ) p z)).differentiableAt
  rw [(hasFDerivAt_floerOperator_aux ω J Ks Kt u p z hu hJ hKs hKt).fderiv]
  simp only [hA.fderiv, floerLinearization_def, hξ.fderiv, sub_apply, add_apply, comp_apply,
    flip_apply]
  rw [ω.fderiv_hamiltonianVectorField_comp_apply (K := fun q ↦ Ks q z) hKs huP,
    ω.fderiv_hamiltonianVectorField_comp_apply (K := fun q ↦ Kt q z) hKt huP,
    fderiv_comp_graph_apply (f := fun w : P × V ↦ J w.1 z w.2) huP hJ]
  have hJp := congrArg (fun L : P →L[ℝ] (V →L[ℝ] V) ↦ L h) (fderiv_slice_left hJ)
  simp only [comp_apply, inl_apply, Function.uncurry_def] at hJp
  rw [← hJp]
  simp only [add_apply, map_add, map_sub]
  abel

end Families

end TauCeti.SymplecticForm
