/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev.Operator
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev.Transfer
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Asymptotic
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.UnitaryFrame
import TauCeti.Topology.UniformSpace.UniformConvergence.Comp

/-!
# The linearized operator of a pair of pants along an end chart and its end model

Let `u` be a map of the pair of pants `S = ℂ ∖ {0, 1}` into a finite-dimensional symplectic vector
space `(V, ω)` which, far out on the end `q`, solves the Floer equation for the pair-of-pants
perturbation of period-one Hamiltonians `H_q` and structures `J(φ'_q(s, t), ·) = J_q(t)`, where
`φ'_q` is the positive end chart. Its linearized operator `D_u` acts on `W^{1,2}_0(S, V)` through
the coefficient field `M` on the conformal jets `(√ρ ξ, ∂s ξ, ∂t ξ)` of the cylindrical weight `ρ`
(`TauCeti.SymplecticForm.floerConformalJetCoeff`). Transferring sections of the cylinder to `S`
along `φ'_q` with a cutoff `β` (`TauCeti.Floer.endTransfer`) turns `D_u` into the first-order
operator on the strip whose coefficient field at `ζ` is `M(φ'_q(ζ))` composed with the jet
coefficient of the transfer `TauCeti.Floer.endTransferCoeff q β ζ`
(`TauCeti.Floer.jetOperator_endTransfer`). This file identifies that coefficient field on the end
and shows that it converges to that of a model operator: the stationary cylinder operator at the
asymptotic orbit followed by a pointwise rotation. It then shows that this end model is translation
invariant and, at a nondegenerate orbit, invertible on `W^{1,2}`. This is what the ends contribute
to a parametrix of `D_u` spliced from inverses of its end models.

* **The operator along the end chart.** Where `β = 1` and `dβ = 0`, at a point `ζ = (s, t)` with
  `s ≥ 2`, the coefficient field on the strip is
  `r⁻¹ (a + b J(φ'_q(ζ), u(φ'_q(ζ)))) ∘ M_end(ζ)`
  (`TauCeti.SymplecticForm.floerConformalJetCoeff_positiveEndChart_comp_endTransferCoeff`). Here
  `M_end` is the coefficient field on jets of the linearized operator along `u ∘ φ'_q` of the end
  datum `H'_q(t) dt` with the structures `J(φ'_q(·), ·)`, `(a, b) = dφ'_q (1, 0)` and
  `r = 2π |φ'_q(ζ) - c_q|` is the conformal scale of the chart. Since `φ'_q` is holomorphic,
  `D_end (ξ ∘ φ'_q) = (a - b J) (D_u ξ) ∘ φ'_q`, and `(a - b J)⁻¹ = (a + b J) / r²`; the factor `r`
  of the `L²` isometry `TauCeti.Floer.positiveEndChartLp` leaves `(a + b J) / r`, a rotation by the
  structure `J`.
* **The end model.** For loops `J_t` and `S_t`, the end model `TauCeti.Floer.endModelCoeff` is the
  coefficient field `r⁻¹ (a + b J_t) ∘ M(t)` of the stationary cylinder operator
  `∂s + J_t (∂t - S_t)` followed by the rotation `TauCeti.Floer.endModelRotation`. If the loops of
  `u ∘ φ'_q` converge uniformly to a one-periodic orbit `x_q` of `H'_q` and the slice defect
  `∂t (u ∘ φ'_q) - X_{H'_q}(u ∘ φ'_q)` tends uniformly to zero, then far out on the end the
  coefficient field of `D_u` is uniformly close to the end model of `J_t = J_q(t, x_q(t))` and
  `S_t = dX_{H'_q(t)}(x_q(t))`
  (`eventually_forall_norm_floerConformalJetCoeff_comp_endTransferCoeff_sub_lt`, in the namespace
  `TauCeti.SymplecticForm`).
  The end Floer data enter only through the end model of the cylinder,
  `TauCeti.SymplecticForm.eventually_forall_norm_floerJetCoeff_sub_stationaryJetCoeff_lt`.
* **Translation invariance.** Translating `ζ` along the end multiplies both `dφ'_q(ζ)` and `r` by
  the same positive factor (`TauCeti.Floer.fderiv_positiveEndChart_add_fst`,
  `TauCeti.Floer.positiveEndChartScale_add_fst`), so the unit tangent
  `TauCeti.Floer.endUnitTangent` of the chart and the rotation depend only on `t`
  (`TauCeti.Floer.endModelRotation_eq_of_snd_eq`), and so does the end model
  (`TauCeti.Floer.endModelCoeff_eq_of_snd_eq`).
* **Invertibility.** Since `a² + b² = r²` and `J_t² = -1`, the rotation is invertible with inverse
  `r⁻¹ (a - b J_t)` (`TauCeti.Floer.isInvertible_endModelRotation`, from
  `TauCeti.AlmostComplexStructure.isInvertible_smul_id_add_smul`), and for continuous loops it
  depends continuously on `t` alone. Multiplication by it is therefore an isomorphism of
  `L²(ℝ × S¹, V)` (`TauCeti.CylinderSobolev.isInvertible_operatorMultiplication_comp_snd`). The
  realization `TauCeti.Floer.endModelSobolevOperator` of the end model on `W^{1,2}(ℝ × S¹, V)` is
  this multiplication after the stationary cylinder operator
  (`TauCeti.Floer.endModelSobolevOperator_eq_comp`), so it is an isomorphism exactly when the
  stationary cylinder operator is (`TauCeti.Floer.isInvertible_endModelSobolevOperator_iff`). In
  particular it is an isomorphism at a nondegenerate orbit whose structures have a unitary frame
  (`isInvertible_endModelSobolevOperator_of_isNondegenerateFixedPt_of_frame`, in the namespace
  `TauCeti.SymplecticForm`).

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix B, on real Cauchy–Riemann operators on surfaces with cylindrical ends.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the asymptotic operators at the ends.
-/

public section

noncomputable section

open Set Function Filter Real TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.Floer

open MeasureTheory CylinderSobolev
open StripSobolev (stripMeasure)
open scoped ENNReal

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-! ### The end model and its rotation -/

/-- The **unit tangent of the end chart** `φ'_q` at `ζ`: the image `(a', b') = r⁻¹ dφ'_q(ζ) (1, 0)`
of the unit longitudinal vector under the rotation part of the chart, for the conformal scale `r`
of the chart at `ζ`. It satisfies `a'² + b'² = 1`
(`TauCeti.Floer.fst_endUnitTangent_sq_add_snd_sq`). -/
def endUnitTangent (q : Puncture) (ζ : ℝ × ℝ) : ℝ × ℝ :=
  ((positiveEndChartScale q ζ)⁻¹ • fderiv ℝ (positiveEndChart q) ζ) (1, 0)

theorem endUnitTangent_def (q : Puncture) (ζ : ℝ × ℝ) :
    endUnitTangent q ζ = ((positiveEndChartScale q ζ)⁻¹ • fderiv ℝ (positiveEndChart q) ζ) (1, 0) :=
  (rfl)

/-- The unit tangent of the end chart depends only on the angular coordinate. -/
theorem endUnitTangent_eq_of_snd_eq (q : Puncture) {ζ ζ' : ℝ × ℝ} (h : ζ.2 = ζ'.2) :
    endUnitTangent q ζ = endUnitTangent q ζ' := by
  rw [endUnitTangent, endUnitTangent,
    positiveEndChartScale_inv_smul_fderiv_positiveEndChart_eq_of_snd_eq q h]

/-- The unit tangent of the end chart is continuous. -/
theorem continuous_endUnitTangent (q : Puncture) : Continuous (endUnitTangent q) := by
  have hd : Continuous fun ζ ↦ fderiv ℝ (positiveEndChart q) ζ :=
    (contDiff_positiveEndChart q 1).continuous_fderiv one_ne_zero
  exact (((continuous_positiveEndChartScale q).inv₀
    fun ζ ↦ (positiveEndChartScale_pos q ζ).ne').smul hd).clm_apply continuous_const

/-- **The unit tangent of the end chart is a unit vector**: `a'² + b'² = 1`, since
`a² + b² = r²` for `(a, b) = dφ'_q (1, 0)`. -/
theorem fst_endUnitTangent_sq_add_snd_sq (q : Puncture) (ζ : ℝ × ℝ) :
    (endUnitTangent q ζ).1 ^ 2 + (endUnitTangent q ζ).2 ^ 2 = 1 := by
  have hr : positiveEndChartScale q ζ ≠ 0 := (positiveEndChartScale_pos q ζ).ne'
  simp only [endUnitTangent, smul_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_pow,
    ← mul_add, ← sq_positiveEndChartScale_eq_sq_add_sq, inv_pow]
  exact inv_mul_cancel₀ (pow_ne_zero 2 hr)

/-- The first component of the unit tangent of the end chart is at most one in absolute value. -/
theorem abs_fst_endUnitTangent_le_one (q : Puncture) (ζ : ℝ × ℝ) :
    |(endUnitTangent q ζ).1| ≤ 1 :=
  sq_le_one_iff_abs_le_one _ |>.1 <| by
    linarith [fst_endUnitTangent_sq_add_snd_sq q ζ, sq_nonneg (endUnitTangent q ζ).2]

/-- The second component of the unit tangent of the end chart is at most one in absolute value. -/
theorem abs_snd_endUnitTangent_le_one (q : Puncture) (ζ : ℝ × ℝ) :
    |(endUnitTangent q ζ).2| ≤ 1 :=
  sq_le_one_iff_abs_le_one _ |>.1 <| by
    linarith [fst_endUnitTangent_sq_add_snd_sq q ζ, sq_nonneg (endUnitTangent q ζ).1]

/-- The **rotation of the end model** of the end `q` at `ζ = (s, t)`, for a loop `J_t` of almost
complex structures: `r⁻¹ (a + b J_t)`, where `(a, b) = dφ'_q (1, 0)` is the image of the unit
longitudinal vector under the positive end chart `φ'_q` and `r` is the conformal scale of the chart
at `ζ`. Since `a² + b² = r²`, it is invertible, with inverse `r⁻¹ (a - b J_t)`
(`TauCeti.Floer.isInvertible_endModelRotation`), and it depends only on `t`
(`TauCeti.Floer.endModelRotation_eq_of_snd_eq`). -/
def endModelRotation (q : Puncture) (J : ℝ → AlmostComplexStructure V) (ζ : ℝ × ℝ) :
    V →L[ℝ] V :=
  (positiveEndChartScale q ζ)⁻¹ •
    ((fderiv ℝ (positiveEndChart q) ζ (1, 0)).1 • ContinuousLinearMap.id ℝ V +
      (fderiv ℝ (positiveEndChart q) ζ (1, 0)).2 • (J ζ.2).toLinearMap.toContinuousLinearMap)

theorem endModelRotation_def (q : Puncture) (J : ℝ → AlmostComplexStructure V) (ζ : ℝ × ℝ) :
    endModelRotation q J ζ = (positiveEndChartScale q ζ)⁻¹ •
      ((fderiv ℝ (positiveEndChart q) ζ (1, 0)).1 • ContinuousLinearMap.id ℝ V +
        (fderiv ℝ (positiveEndChart q) ζ (1, 0)).2 • (J ζ.2).toLinearMap.toContinuousLinearMap) :=
  (rfl)

/-- The rotation of the end model is `a' + b' J_t`, where `(a', b')` is the unit tangent
`r⁻¹ dφ'_q (1, 0)` of the end chart (`TauCeti.Floer.endUnitTangent`). -/
theorem endModelRotation_eq (q : Puncture) (J : ℝ → AlmostComplexStructure V) (ζ : ℝ × ℝ) :
    endModelRotation q J ζ = (endUnitTangent q ζ).1 • ContinuousLinearMap.id ℝ V +
      (endUnitTangent q ζ).2 • (J ζ.2).toLinearMap.toContinuousLinearMap := by
  simp [endModelRotation_def, endUnitTangent, smul_add, smul_smul]

theorem endModelRotation_apply (q : Puncture) (J : ℝ → AlmostComplexStructure V) (ζ : ℝ × ℝ)
    (v : V) :
    endModelRotation q J ζ v = (endUnitTangent q ζ).1 • v + (endUnitTangent q ζ).2 • J ζ.2 v := by
  simp [endModelRotation_eq]

/-- **The rotation of the end model is translation invariant**: it depends only on the angular
coordinate, since the rotation part `r⁻¹ dφ'_q` of the chart does. -/
theorem endModelRotation_eq_of_snd_eq (q : Puncture) (J : ℝ → AlmostComplexStructure V)
    {ζ ζ' : ℝ × ℝ} (h : ζ.2 = ζ'.2) : endModelRotation q J ζ = endModelRotation q J ζ' := by
  rw [endModelRotation_eq, endModelRotation_eq, endUnitTangent_eq_of_snd_eq q h, h]

/-- The rotation of the end model is invertible: it is `a' + b' J_t` with `a'² + b'² = 1`, since
`a² + b² = r²` for `(a, b) = dφ'_q (1, 0)`. -/
theorem isInvertible_endModelRotation (q : Puncture) (J : ℝ → AlmostComplexStructure V)
    (ζ : ℝ × ℝ) : (endModelRotation q J ζ).IsInvertible := by
  rw [endModelRotation_eq]
  exact (J ζ.2).isInvertible_smul_id_add_smul <| fst_endUnitTangent_sq_add_snd_sq q ζ ▸ one_ne_zero

/-- For a continuous loop `J_t`, the rotation of the end model is continuous. -/
theorem continuous_endModelRotation (q : Puncture) {J : ℝ → AlmostComplexStructure V}
    (hJ : Continuous fun t ↦ (J t).toLinearMap.toContinuousLinearMap) :
    Continuous (endModelRotation q J) := by
  have hd : Continuous fun ζ ↦ fderiv ℝ (positiveEndChart q) ζ (1, 0) :=
    ((contDiff_positiveEndChart q 1).continuous_fderiv one_ne_zero).clm_apply continuous_const
  exact ((continuous_positiveEndChartScale q).inv₀ fun ζ ↦ (positiveEndChartScale_pos q ζ).ne').smul
    ((hd.fst.smul continuous_const).add (hd.snd.smul (hJ.comp continuous_snd)))

/-- For a continuous loop `J_t`, the rotation of the end model is essentially bounded on the
strip. -/
theorem memLp_endModelRotation (q : Puncture) {J : ℝ → AlmostComplexStructure V}
    (hJ : Continuous fun t ↦ (J t).toLinearMap.toContinuousLinearMap) :
    MemLp (endModelRotation q J) ∞ stripMeasure :=
  memLp_top_of_eq_comp_snd ((continuous_endModelRotation q hJ).comp
    (continuous_const.prodMk continuous_id)) fun _ ↦ endModelRotation_eq_of_snd_eq q J rfl

/-- The **coefficient field of the end model** of the end `q`, for loops `J_t` of almost complex
structures and `S_t` of endomorphisms: at `ζ = (s, t)`, the coefficient field of the stationary
cylinder operator `∂s + J_t (∂t - S_t)` followed by the rotation `r⁻¹ (a + b J_t)` of
`TauCeti.Floer.endModelRotation`. Far out on an end of a Floer pair of pants, the linearized
operator read in the positive end chart converges to it
(`SymplecticForm.eventually_forall_norm_floerConformalJetCoeff_comp_endTransferCoeff_sub_lt`). -/
def endModelCoeff (q : Puncture) (J : ℝ → AlmostComplexStructure V) (S : ℝ → V →L[ℝ] V)
    (ζ : ℝ × ℝ) : V × V × V →L[ℝ] V :=
  (endModelRotation q J ζ).comp (stationaryJetCoeff J S ζ)

theorem endModelCoeff_def (q : Puncture) (J : ℝ → AlmostComplexStructure V)
    (S : ℝ → V →L[ℝ] V) (ζ : ℝ × ℝ) :
    endModelCoeff q J S ζ = (endModelRotation q J ζ).comp (stationaryJetCoeff J S ζ) :=
  (rfl)

/-- **The end model is translation invariant**: its coefficient field depends only on the
angular coordinate. -/
theorem endModelCoeff_eq_of_snd_eq (q : Puncture) (J : ℝ → AlmostComplexStructure V)
    (S : ℝ → V →L[ℝ] V) {ζ ζ' : ℝ × ℝ} (h : ζ.2 = ζ'.2) :
    endModelCoeff q J S ζ = endModelCoeff q J S ζ' := by
  rw [endModelCoeff_def, endModelCoeff_def, endModelRotation_eq_of_snd_eq q J h,
    stationaryJetCoeff_eq_of_snd_eq h]

/-- For continuous loops `J_t` and `S_t`, the coefficient field of the end model is essentially
bounded on the strip. -/
theorem memLp_endModelCoeff (q : Puncture) {J : ℝ → AlmostComplexStructure V}
    {S : ℝ → V →L[ℝ] V} (hJ : Continuous fun t ↦ (J t).toLinearMap.toContinuousLinearMap)
    (hS : Continuous S) : MemLp (endModelCoeff q J S) ∞ stripMeasure :=
  memLp_top_of_eq_comp_snd (((continuous_endModelRotation q hJ).clm_comp
    (continuous_stationaryJetCoeff hJ hS)).comp (continuous_const.prodMk continuous_id))
    fun _ ↦ endModelCoeff_eq_of_snd_eq q J S rfl

variable (q : Puncture) (J : ℝ → AlmostComplexStructure V) (S : ℝ → V →L[ℝ] V) in
/-- The **end model operator** of the end `q`: the first-order operator of
`TauCeti.Floer.endModelCoeff` on the cylinder, realized from `W^{1,2}(ℝ × S¹, V)` to
`L²(ℝ × S¹, V)`. -/
def endModelSobolevOperator : H1 V →L[ℝ] Lp V 2 stripMeasure :=
  (jetOperator 2 stripMeasure (endModelCoeff q J S)).comp (H1 V).subtypeL

variable (q : Puncture) (J : ℝ → AlmostComplexStructure V) (S : ℝ → V →L[ℝ] V) in
theorem endModelSobolevOperator_def :
    endModelSobolevOperator q J S =
      (jetOperator 2 stripMeasure (endModelCoeff q J S)).comp (H1 V).subtypeL :=
  (rfl)

/-- For continuous loops `J_t` and `S_t`, the end model operator acts pointwise on an `L²` jet
`x ∈ H1` by the coefficient field of the end model. -/
theorem coeFn_endModelSobolevOperator (q : Puncture) {J : ℝ → AlmostComplexStructure V}
    {S : ℝ → V →L[ℝ] V} (hJ : Continuous fun t ↦ (J t).toLinearMap.toContinuousLinearMap)
    (hS : Continuous S) (x : H1 V) :
    endModelSobolevOperator q J S x =ᵐ[stripMeasure]
      fun z ↦ endModelCoeff q J S z ((x : Lp (V × V × V) 2 stripMeasure) z) :=
  coeFn_jetOperator (p := 2) (memLp_endModelCoeff q hJ hS) x

/-- **The end model is the stationary cylinder operator followed by a rotation.** For continuous
loops `J_t` and `S_t`, the end model operator is the realization of `∂s + J_t (∂t - S_t)` on
`W^{1,2}` followed by multiplication by the rotation `r⁻¹ (a + b J_t)` on `L²`. -/
theorem endModelSobolevOperator_eq_comp (q : Puncture) {J : ℝ → AlmostComplexStructure V}
    {S : ℝ → V →L[ℝ] V} (hJ : Continuous fun t ↦ (J t).toLinearMap.toContinuousLinearMap)
    (hS : Continuous S) :
    endModelSobolevOperator q J S =
      Lp.operatorMultiplication 2 ((memLp_endModelRotation q hJ).toLp _) ∘L
        stationarySobolevOperator J S := by
  refine ContinuousLinearMap.ext fun x ↦ Lp.ext ?_
  filter_upwards [coeFn_endModelSobolevOperator q hJ hS x,
    Lp.operatorMultiplication_ae ((memLp_endModelRotation q hJ).toLp _)
      (stationarySobolevOperator J S x),
    (memLp_endModelRotation q hJ).coeFn_toLp, coeFn_stationarySobolevOperator hJ hS x]
    with z h₁ h₂ h₃ h₄
  rw [ContinuousLinearMap.comp_apply, h₁, h₂, h₃, h₄, endModelCoeff_def,
    ContinuousLinearMap.comp_apply]

/-- **The end model is invertible exactly when the stationary cylinder operator is.** For
continuous loops `J_t` and `S_t`, the end model operator
`W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)` is an isomorphism if and only if the realization of the
stationary cylinder operator `∂s + J_t (∂t - S_t)` is, since multiplication by the rotation
`r⁻¹ (a + b J_t)`, which depends continuously on `t` alone, is an isomorphism of `L²`. -/
theorem isInvertible_endModelSobolevOperator_iff (q : Puncture)
    {J : ℝ → AlmostComplexStructure V} {S : ℝ → V →L[ℝ] V}
    (hJ : Continuous fun t ↦ (J t).toLinearMap.toContinuousLinearMap) (hS : Continuous S) :
    (endModelSobolevOperator q J S).IsInvertible ↔
      (stationarySobolevOperator J S).IsInvertible := by
  have hR : Continuous fun t ↦ endModelRotation q J (0, t) :=
    (continuous_endModelRotation q hJ).comp (continuous_const.prodMk continuous_id)
  obtain ⟨e, he⟩ := isInvertible_operatorMultiplication_comp_snd (p := 2) hR
    fun t ↦ isInvertible_endModelRotation q J (0, t)
  rw [endModelSobolevOperator_eq_comp q hJ hS,
    toLp_eq_toLp_comp_snd hR fun _ ↦ endModelRotation_eq_of_snd_eq q J rfl, ← he,
    ContinuousLinearMap.isInvertible_equiv_comp]

end TauCeti.Floer

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ}

/-- **The linearized operator of a pair of pants along an end chart.** Let `u` solve the Floer
equation for the pair-of-pants perturbation of period-one `C²` Hamiltonians `H_q` at the point
`w = φ'_q(ζ)` of the end `q`, with `ζ = (s, t)` and `s ≥ 2`, and let the cutoff `β` be `1` with
vanishing derivative at `w`. Then the coefficient field on conformal jets at `w`, composed with the
jet coefficient of the transfer along `φ'_q`, is `r⁻¹ (a + b J)` composed with the coefficient field
on jets at `ζ` of the linearized operator along `u ∘ φ'_q` of the end datum `H'_q(t) dt`, where
`J = J(w, u w)`, `(a, b) = dφ'_q (1, 0)` and `r` is the conformal scale of the chart. -/
theorem floerConformalJetCoeff_positiveEndChart_comp_endTransferCoeff (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) {q : Puncture} (hHs : ∀ t, ContDiff ℝ 2 (H q t))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {u : ℝ × ℝ → V} {β : ℝ × ℝ → ℝ} {ζ : ℝ × ℝ}
    (hζ : 2 ≤ ζ.1) (hu : DifferentiableAt ℝ u (positiveEndChart q ζ))
    (hfl : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (positiveEndChart q ζ) (u (positiveEndChart q ζ)))
      (ω.perturbedFDeriv
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
        (positiveEndChart q ζ) : ℝ × ℝ →ₗ[ℝ] V))
    (hβ : β (positiveEndChart q ζ) = 1) (hdβ : fderiv ℝ β (positiveEndChart q ζ) = 0) :
    (ω.floerConformalJetCoeff cylindricalWeight
        (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
        (positiveEndChart q ζ)).comp (endTransferCoeff q β ζ) =
      ((positiveEndChartScale q ζ)⁻¹ •
          ((fderiv ℝ (positiveEndChart q) ζ (1, 0)).1 • ContinuousLinearMap.id ℝ V +
            (fderiv ℝ (positiveEndChart q) ζ (1, 0)).2 • (J (positiveEndChart q ζ)
              (u (positiveEndChart q ζ))).toLinearMap.toContinuousLinearMap)).comp
        (ω.floerJetCoeff
          (fun ζ' y ↦ (J (positiveEndChart q ζ') y).toLinearMap.toContinuousLinearMap)
          (fun _ _ ↦ 0) (fun ζ' ↦ positiveEndHamiltonian H q ζ'.2) (u ∘ positiveEndChart q) ζ) := by
  have hr := positiveEndChartScale_pos q ζ
  -- The weight is positive at `φ'_q(ζ)`, which is not the center of the end.
  have hρ : 0 < √(cylindricalWeight (positiveEndChart q ζ)) := by
    have hd := norm_pos_iff.2
      (sub_ne_zero.2 (equivRealProdCLM_symm_positiveEndChart_ne_endCenter q ζ))
    exact Real.sqrt_pos.2 ((inv_pos.2 (pow_pos hd 2)).trans_le
      (inv_norm_sub_endCenter_sq_le_cylindricalWeight q _))
  -- The Jacobian of the chart is `a² + b² = r²`.
  have hdet := sq_positiveEndChartScale_eq_sq_add_sq q ζ
  refine ContinuousLinearMap.ext fun v ↦ ?_
  simp only [ContinuousLinearMap.comp_apply, floerConformalJetCoeff_apply, endTransferCoeff_apply,
    floerJetCoeff_apply, Function.comp_apply, smul_apply, add_apply,
    ContinuousLinearMap.id_apply, hβ, hdβ, zero_apply, mul_zero, zero_smul, zero_add, one_mul,
    ω.floerLinearizationCoeff_comp_positiveEndChart_apply hH hHs hζ hu hfl v.1, map_smul,
    LinearMap.coe_toContinuousLinearMap', smul_smul]
  set L := J (positiveEndChart q ζ) (u (positiveEndChart q ζ))
  set a := (fderiv ℝ (positiveEndChart q) ζ (1, 0)).1
  set b := (fderiv ℝ (positiveEndChart q) ζ (1, 0)).2
  set r := positiveEndChartScale q ζ
  set ρ := √(cylindricalWeight (positiveEndChart q ζ))
  -- The zeroth-order term is `(a + b J) (a - b J) c = (a² + b²) c = r² c`.
  rw [map_add L.toLinearMap _ (a • _ - b • L.toLinearMap _), smul_add a, smul_add b,
    add_add_add_comm, L.smul_add_smul_apply_smul_sub_smul, ← hdet]
  -- The weight factor cancels, and `r⁻¹ r² = r`.
  rw [show ρ⁻¹ * (r * (ρ * 1)) = r by field_simp, sq, mul_smul, smul_add r⁻¹,
    inv_smul_smul₀ hr.ne']
  congr 1
  simp only [map_add, map_smul, L.apply_apply]
  module

/-- **Pointwise comparison with an end model.** Let the Floer data at the point `w = φ'_q(ζ)` of the
end `q`, with `ζ = (s, t)` and `s ≥ 2`, be the structures `J_q(t)` and the pair-of-pants
perturbation of period-one `C²` Hamiltonians `H_q`, let `u` be differentiable and solve the Floer
equation at `w`, and let the cutoff `β` be `1` with vanishing derivative at `w`. For a loop `x` and
a loop `S_t` of endomorphisms, the coefficient field on conformal jets at `w`, composed with the jet
coefficient of the transfer along `φ'_q`, differs from the end model
`TauCeti.Floer.endModelCoeff`, `r⁻¹ (a + b J_q(t, x(t)))` composed with the coefficient field `M` of
the stationary cylinder operator `∂s + J_q(t, x(t)) (∂t - S_t)`, by at most
`(1 + ‖J_q(t, u w)‖) ‖F - M‖ + ‖J_q(t, u w) - J_q(t, x(t))‖ ‖M‖`, where `F` is the coefficient field
on jets at `ζ` of the linearized operator along `u ∘ φ'_q` of the end datum `H'_q(t) dt`,
`(a, b) = dφ'_q (1, 0)` and `r` is the conformal scale of the chart. -/
theorem norm_floerConformalJetCoeff_comp_endTransferCoeff_sub_le (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) {q : Puncture} (hHs : ∀ t, ContDiff ℝ 2 (H q t))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Jq : ℝ → V → AlmostComplexStructure V}
    {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V} {β : ℝ × ℝ → ℝ} {ζ : ℝ × ℝ} (hζ : 2 ≤ ζ.1)
    (hJz : J (positiveEndChart q ζ) = Jq ζ.2)
    (hKs : Ks (positiveEndChart q ζ) = fun x ↦ pairOfPantsPerturbation H
      (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) x 1)
    (hKt : Kt (positiveEndChart q ζ) = fun x ↦ pairOfPantsPerturbation H
      (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) x Complex.I)
    (hu : DifferentiableAt ℝ u (positiveEndChart q ζ))
    (hfl : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (positiveEndChart q ζ) (u (positiveEndChart q ζ)))
      (ω.perturbedFDeriv Ks Kt u (positiveEndChart q ζ) : ℝ × ℝ →ₗ[ℝ] V))
    (hβ : β (positiveEndChart q ζ) = 1) (hdβ : fderiv ℝ β (positiveEndChart q ζ) = 0)
    (x : ℝ → V) (S : ℝ → V →L[ℝ] V) :
    ‖(ω.floerConformalJetCoeff cylindricalWeight
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u
          (positiveEndChart q ζ)).comp (endTransferCoeff q β ζ) -
        endModelCoeff q (fun t ↦ Jq t (x t)) S ζ‖ ≤
      (1 + ‖(Jq ζ.2 (u (positiveEndChart q ζ))).toLinearMap.toContinuousLinearMap‖) *
          ‖ω.floerJetCoeff (fun w y ↦ (Jq w.2 y).toLinearMap.toContinuousLinearMap)
              (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) ζ -
            Floer.stationaryJetCoeff (fun t ↦ Jq t (x t)) S ζ‖ +
        ‖(Jq ζ.2 (u (positiveEndChart q ζ))).toLinearMap.toContinuousLinearMap -
            (Jq ζ.2 (x ζ.2)).toLinearMap.toContinuousLinearMap‖ *
          ‖Floer.stationaryJetCoeff (fun t ↦ Jq t (x t)) S ζ‖ := by
  rw [ω.perturbedFDeriv_congr u
    (Ks' := fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
    (Kt' := fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    hKs hKt] at hfl
  rw [ω.floerConformalJetCoeff_congr_data _ u rfl
    (Ks' := fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
    (Kt' := fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    hKs hKt,
    ω.floerConformalJetCoeff_positiveEndChart_comp_endTransferCoeff hH hHs hζ hu hfl hβ hdβ,
    ω.floerJetCoeff_congr_data (u ∘ positiveEndChart q)
      (J' := fun w y ↦ (Jq w.2 y).toLinearMap.toContinuousLinearMap) (Ks' := fun _ _ ↦ 0)
      (Kt' := fun w ↦ positiveEndHamiltonian H q w.2) (by simp only [hJz]) rfl rfl, hJz,
    endModelCoeff_def, endModelRotation_def]
  -- Split the difference into the change of operator and the change of rotation.
  set F := ω.floerJetCoeff (fun w y ↦ (Jq w.2 y).toLinearMap.toContinuousLinearMap)
    (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) ζ
  set M := Floer.stationaryJetCoeff (fun t ↦ Jq t (x t)) S ζ
  set a := (fderiv ℝ (positiveEndChart q) ζ (1, 0)).1
  set b := (fderiv ℝ (positiveEndChart q) ζ (1, 0)).2
  set r := positiveEndChartScale q ζ
  set Lu := (Jq ζ.2 (u (positiveEndChart q ζ))).toLinearMap.toContinuousLinearMap
  set Lx := (Jq ζ.2 (x ζ.2)).toLinearMap.toContinuousLinearMap
  have hr : 0 < r := positiveEndChartScale_pos q ζ
  have ha : |a| ≤ r := abs_fst_fderiv_positiveEndChart_le q ζ
  have hb : |b| ≤ r := abs_snd_fderiv_positiveEndChart_le q ζ
  have hsplit : (r⁻¹ • (a • ContinuousLinearMap.id ℝ V + b • Lu)).comp F -
      (r⁻¹ • (a • ContinuousLinearMap.id ℝ V + b • Lx)).comp M =
        (r⁻¹ • (a • ContinuousLinearMap.id ℝ V + b • Lu)).comp (F - M) +
          ((r⁻¹ * b) • (Lu - Lx)).comp M := by
    simp only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.add_comp, ContinuousLinearMap.sub_comp]
    module
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ((ContinuousLinearMap.opNorm_comp_le _ _).trans ?_)
    ((ContinuousLinearMap.opNorm_comp_le _ _).trans ?_)) <;>
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  · -- The rotation `r⁻¹ (a + b L)` has norm at most `1 + ‖L‖`, since `|a|, |b| ≤ r`.
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hr.le, inv_mul_le_iff₀ hr]
    exact (Jq ζ.2 (u (positiveEndChart q ζ))).norm_smul_add_smul_le ha hb
  · rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hr]
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    rwa [inv_mul_le_iff₀ hr, mul_one]

/-- **The end model of the linearized operator of a pair of pants.** Let `(J, K_s, K_t)` be Floer
data on the pair of pants which beyond a height `T` of the end `q`, read in the positive end chart
`φ'_q`, are the structures `J_q(t)` of a `C¹` family and the pair-of-pants perturbation of
period-one Hamiltonians `H_q` with `H_q` jointly `C²`, and let `u` be differentiable and solve the
Floer equation there. Let the loops of `u ∘ φ'_q` converge uniformly to a continuous loop `x`,
with slice defect `∂t (u ∘ φ'_q) - X_{H'_q}(u ∘ φ'_q)` tending
uniformly to zero, and let the cutoff `β` be `1` with vanishing derivative beyond the height `T`.
Then for every `ε > 0` and every sufficiently large `s`, at every `t ∈ [0, 1]`, the coefficient
field on conformal jets at `φ'_q(s, t)`, composed with the jet coefficient of the transfer along
`φ'_q`, is within `ε` of the end model `TauCeti.Floer.endModelCoeff`: `r⁻¹ (a + b J_q(t, x(t)))`
composed with the coefficient field of the stationary cylinder operator
`∂s + J_q(t, x(t)) (∂t - dX_{H'_q(t)}(x(t)))`, where
`(a, b) = dφ'_q (1, 0)` and `r` is the conformal scale of the chart at `(s, t)`. -/
theorem eventually_forall_norm_floerConformalJetCoeff_comp_endTransferCoeff_sub_lt
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1) {q : Puncture}
    (hHs : ContDiff ℝ 2 (uncurry (H q)))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Jq : ℝ → V → AlmostComplexStructure V}
    (hJq : ContDiff ℝ 1 fun p : ℝ × V ↦ (Jq p.1 p.2).toLinearMap.toContinuousLinearMap)
    {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V} {β : ℝ × ℝ → ℝ} {T : ℝ}
    (hJend : ∀ ζ : ℝ × ℝ, T ≤ ζ.1 → J (positiveEndChart q ζ) = Jq ζ.2)
    (hKend : ∀ ζ : ℝ × ℝ, T ≤ ζ.1 →
      Ks (positiveEndChart q ζ) = (fun x ↦ pairOfPantsPerturbation H
        (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) x 1) ∧
      Kt (positiveEndChart q ζ) = fun x ↦ pairOfPantsPerturbation H
        (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) x Complex.I)
    (hu : ∀ ζ : ℝ × ℝ, T ≤ ζ.1 → DifferentiableAt ℝ u (positiveEndChart q ζ))
    (hfl : ∀ ζ : ℝ × ℝ, T ≤ ζ.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (positiveEndChart q ζ) (u (positiveEndChart q ζ)))
      (ω.perturbedFDeriv Ks Kt u (positiveEndChart q ζ) : ℝ × ℝ →ₗ[ℝ] V))
    (hβ : ∀ ζ : ℝ × ℝ, T ≤ ζ.1 →
      β (positiveEndChart q ζ) = 1 ∧ fderiv ℝ β (positiveEndChart q ζ) = 0)
    {x : ℝ → V} (hxc : Continuous x)
    (hux : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) x atTop (Icc 0 1))
    (hδ : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖(ω.floerConformalJetCoeff cylindricalWeight
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u
          (positiveEndChart q (s, t))).comp (endTransferCoeff q β (s, t)) -
        endModelCoeff q (fun t ↦ Jq t (x t))
          (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (x t))
          (s, t)‖ < ε := by
  set Jc : ℝ × V → V →L[ℝ] V := fun p ↦ (Jq p.1 p.2).toLinearMap.toContinuousLinearMap
  set S : ℝ → V →L[ℝ] V :=
    fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (x t)
  have hJx : Continuous fun t ↦ Jc (t, x t) := hJq.continuous.comp (continuous_id.prodMk hxc)
  have hS : Continuous S := (continuous_fderiv_slice_right
    (f := fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t))
    (ω.contDiff_hamiltonianVectorField_uncurry (n := 1)
      (contDiff_uncurry_positiveEndHamiltonian hHs))).comp (continuous_id.prodMk hxc)
  -- The model and the structure along the orbit are bounded over a period.
  obtain ⟨BM, hBM⟩ := (isCompact_singleton.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := {(0 : ℝ)} ×ˢ Icc (0 : ℝ) 1)
    (Floer.continuous_stationaryJetCoeff hJx hS).continuousOn
  obtain ⟨BJ, hBJ⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) 1)
    hJx.continuousOn
  set B := |BJ| + |BM| + 2
  have hB : 0 < B := by positivity
  -- Far out, the structures along `u ∘ φ'_q` are uniformly close to those along the orbit, and
  -- the operator of the end datum is uniformly close to the stationary model.
  have hJu := Metric.tendstoUniformlyOn_iff.1 ((isCompact_Icc.image
    (continuous_id.prodMk hxc)).comp_tendstoUniformlyOn (g := Jc)
    (fun _ _ ↦ hJq.continuous.continuousAt) hux.graph) (min 1 (ε / (2 * B))) (by positivity)
  have hFM := ω.eventually_forall_norm_floerJetCoeff_sub_stationaryJetCoeff_lt hJq
    (contDiff_uncurry_positiveEndHamiltonian hHs) isCompact_Icc hxc.continuousOn hux hδ
    (by positivity : 0 < ε / (2 * B))
  filter_upwards [eventually_ge_atTop (max T 2), hJu, hFM] with s hs hsJ hsF t ht
  have hsT : T ≤ (s, t).1 := (le_max_left _ _).trans hs
  obtain ⟨hKsq, hKtq⟩ := hKend (s, t) hsT
  obtain ⟨hβ₁, hβ₂⟩ := hβ (s, t) hsT
  refine (ω.norm_floerConformalJetCoeff_comp_endTransferCoeff_sub_le hH
    (fun t ↦ hHs.comp (contDiff_const.prodMk contDiff_id)) ((le_max_right _ _).trans hs)
    (hJend (s, t) hsT) hKsq hKtq (hu (s, t) hsT) (hfl (s, t) hsT) hβ₁ hβ₂ x S).trans_lt ?_
  have hJ' : ‖Jc (t, u (positiveEndChart q (s, t))) - Jc (t, x t)‖ < min 1 (ε / (2 * B)) := by
    simpa only [dist_eq_norm, norm_sub_rev, id_eq] using hsJ t ht
  -- The model at `(s, t)` is the model at `(0, t)`.
  have hM : ‖Floer.stationaryJetCoeff (fun t ↦ Jq t (x t)) S (s, t)‖ ≤ B := by
    rw [Floer.stationaryJetCoeff_eq_of_snd_eq (z := (s, t)) (z' := (0, t)) rfl]
    linarith [hBM (0, t) ⟨rfl, ht⟩, le_abs_self BM, abs_nonneg BJ]
  have hJu : 1 + ‖Jc (t, u (positiveEndChart q (s, t)))‖ ≤ B := by
    linarith [norm_le_norm_add_norm_sub' (Jc (t, u (positiveEndChart q (s, t)))) (Jc (t, x t)),
      hBJ t ht, (lt_min_iff.1 hJ').1, le_abs_self BJ, abs_nonneg BM]
  calc _ ≤ B * ‖_ - _‖ + ε / (2 * B) * B := by
        gcongr
        exact (lt_min_iff.1 hJ').2.le
    _ < B * (ε / (2 * B)) + ε / (2 * B) * B := by
        gcongr
        exact hsF t ht
    _ = ε := by field_simp; ring

section Nondegenerate

open scoped NNReal Manifold

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- **The end model at a nondegenerate orbit is invertible.** Let `x` be a one-periodic orbit of a
one-periodic, jointly `C³` time-dependent Hamiltonian `H` whose suspended vector field is globally
Lipschitz, with `x(0)` a nondegenerate fixed point of the time-one map, and let the structures
`J_t(x(t))` have a unitary frame: a `C²` one-periodic family of invertible maps `Φ_t : F → V` from
a finite-dimensional complex inner product space, carrying `Im ⟪·, ·⟫` to `ω` and `i` to
`J_t(x(t))`. Then for every end `q`, the end model operator of the loops `J_t(x(t))` and
`S_t = dX_{H_t}(x(t))` is an isomorphism `W^{1,2}(ℝ × S¹, V) ≃ L²(ℝ × S¹, V)`. -/
theorem isInvertible_endModelSobolevOperator_of_isNondegenerateFixedPt_of_frame
    (ω : SymplecticForm V) (q : Puncture) {H : ℝ → V → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 3 (Function.uncurry H)) (hHp : Periodic H 1) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    {J : ℝ → V → AlmostComplexStructure V} {Φ : ℝ → F →L[ℝ] V} (hΦ : ContDiff ℝ 2 Φ)
    (hΦp : Periodic Φ 1) (hΦi : ∀ t, (Φ t).IsInvertible)
    (hΦω : ∀ t v w, ω (Φ t v) (Φ t w) = (inner ℂ v w).im)
    (hΦJ : ∀ t v, J t (x t) (Φ t v) = Φ t (Complex.I • v))
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0)) :
    (Floer.endModelSobolevOperator q (fun t ↦ J t (x t))
      fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)).IsInvertible := by
  have hst := ω.isInvertible_floerSobolevOperator_of_isNondegenerateFixedPt_of_frame hX hH hHp hx
    hxp hΦ hΦp hΦi hΦω hΦJ hnd
  rw [floerSobolevOperator_def, floerJetCoeff_eq_stationaryJetCoeff ω J H hx,
    ← Floer.stationarySobolevOperator_def] at hst
  exact (Floer.isInvertible_endModelSobolevOperator_iff q
    (continuous_toContinuousLinearMap_of_frame hΦ hΦi hΦJ)
    (ω.continuous_fderiv_hamiltonianVectorField_comp (hH.of_le (by norm_num))
      (continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt))).2 hst

end Nondegenerate

end TauCeti.SymplecticForm
