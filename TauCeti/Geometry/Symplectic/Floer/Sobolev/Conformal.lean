/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Conformal
public import TauCeti.Geometry.Symplectic.Floer.Linearization.Basic
public import TauCeti.Geometry.Symplectic.Floer.Pullback
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Realization
import TauCeti.Geometry.Symplectic.AlmostComplex.Topology
import TauCeti.Geometry.Symplectic.Floer.Linearization.Pullback
import TauCeti.MeasureTheory.Function.LpSeminorm.Tendsto

/-!
# The linearized Floer operator on the Sobolev space of a conformal metric

Let `U ⊆ ℝ × ℝ` be open with a conformal weight `ρ` (`TauCeti.ConformalSobolev.IsWeight`), such as
the pair of pants `ℂ ∖ {0, 1}` with the weight of its cylindrical metric. The Sobolev space
`W^{1,2}_0(U, V)` of the metric `ρ (ds² + dt²)` is `TauCeti.ConformalSobolev.H1 V U ρ`, the closure
of the jets `(√ρ ξ, ∂s ξ, ∂t ξ)` of test sections in `L²(U, V × V × V)`. This file realizes the
linearized Floer operator

`D_u ξ = ∂s ξ + J(z, u z) ∂t ξ + C(z) ξ`

along a map `u` (`TauCeti.SymplecticForm.floerLinearization`, with zeroth-order part
`C = TauCeti.SymplecticForm.floerLinearizationCoeff`) as an operator from this Sobolev space to
`L²(U, V)` for the Lebesgue measure of the coordinates.

Since the first component of a jet is `√ρ ξ` rather than `ξ`, the operator acts on jets through the
coefficient field

`M(z) (a, b, c) = b + J(z, u z) c + ρ(z)^(-1/2) C(z) a`

(`TauCeti.SymplecticForm.floerConformalJetCoeff`), so that `M(z)` applied to the jet of `ξ` at a
point of `U` is `D_u ξ (z)` (`TauCeti.SymplecticForm.floerConformalJetCoeff_jet`). The operator
realizes `D_u` when `M` is essentially bounded on `U` (and is `0` by convention otherwise). Its
first two terms are bounded where `J` is, so the condition is that `C(z)` grows at most like
`√ρ(z)` (`norm_floerConformalJetCoeff_le`): on a cylindrical end of `U`, where `ρ` is the conformal
factor of the metric `ds² + dt²`, this says that the zeroth-order part of `D_u` in the end
coordinates is bounded
(`norm_floerConformalJetCoeff_le_of_norm_floerJetCoeff_comp_le`). The realization is
`TauCeti.SymplecticForm.floerConformalSobolevOperator`, which agrees with `D_u` on test sections
(`TauCeti.SymplecticForm.floerConformalSobolevOperator_toLp_jet_ae_eq`), so that its norm on the jet
of a test section `ξ` is the `L²` norm of `D_u ξ`
(`TauCeti.SymplecticForm.norm_floerConformalSobolevOperator_sq`). An estimate of the weighted
energy of test sections by `∫ ‖D_u ξ‖²` and an `L²` norm on a compact set then gives the estimate
of Peetre's argument
(`exists_forall_norm_le_mul_norm_floerConformalSobolevOperator_add_of_integral_le`).

The coefficient field is continuous where the data are regular along `u`
(`continuousOn_floerConformalJetCoeff`), and for a family of data `(J_μ, K_{s,μ}, K_{t,μ})` that is
regular jointly in the parameter it is continuous jointly in the parameter and the domain point
(`continuousAt_floerConformalJetCoeff_family`). When the family only changes over a compact set, its
coefficient fields are therefore continuous in the parameter in `L^∞`
(`tendsto_eLpNorm_floerConformalJetCoeff_family`); this is how the operators of a family of data are
compared in operator norm.

The `L²` norm of `D_u ξ` for the Lebesgue measure of the coordinates is the `L²` norm of the
`(0, 1)`-form `(dξ + …)^(0,1)` for the conformal metric, since the conformal factors of a
one-form and of the area cancel; for the pair of pants this is the norm in which the energy and
the semi-Fredholm estimates are stated.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix B, on the Sobolev realization of real Cauchy–Riemann operators on surfaces with
  cylindrical ends.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the Fredholm theory of the pair-of-pants operator.
-/

public section

noncomputable section

open MeasureTheory Set Function ContinuousLinearMap TauCeti.ConformalSobolev
open scoped ENNReal

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The coefficient field of the linearized Floer operator on the jets `(√ρ ξ, ∂s ξ, ∂t ξ)` of a
conformal weight `ρ`: at `z`, the linear map `(a, b, c) ↦ b + J(z, u z) c + ρ(z)^(-1/2) C(z) a`
(`TauCeti.firstOrderJetCoeff`), where `C` is the zeroth-order part
`TauCeti.SymplecticForm.floerLinearizationCoeff`. -/
def floerConformalJetCoeff (ω : SymplecticForm V) (ρ : ℝ × ℝ → ℝ) (J : ℝ × ℝ → V → V →L[ℝ] V)
    (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) (z : ℝ × ℝ) : V × V × V →L[ℝ] V :=
  firstOrderJetCoeff (J z (u z)) ((√(ρ z))⁻¹ • ω.floerLinearizationCoeff J Ks Kt u z)

/-- The definition of the coefficient field of the linearized Floer operator on conformal jets:
the coefficient field `TauCeti.firstOrderJetCoeff` of `∂s + J(z, u z) ∂t + ρ(z)^(-1/2) C(z)`. -/
theorem floerConformalJetCoeff_def (ω : SymplecticForm V) (ρ : ℝ × ℝ → ℝ)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ω.floerConformalJetCoeff ρ J Ks Kt u z =
      firstOrderJetCoeff (J z (u z)) ((√(ρ z))⁻¹ • ω.floerLinearizationCoeff J Ks Kt u z) :=
  (rfl)

/-- The coefficient field of the linearized Floer operator on conformal jets, evaluated on a
jet. -/
theorem floerConformalJetCoeff_apply (ω : SymplecticForm V) (ρ : ℝ × ℝ → ℝ)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) (z : ℝ × ℝ)
    (v : V × V × V) :
    ω.floerConformalJetCoeff ρ J Ks Kt u z v =
      v.2.1 + J z (u z) v.2.2 + (√(ρ z))⁻¹ • ω.floerLinearizationCoeff J Ks Kt u z v.1 :=
  firstOrderJetCoeff_apply _ _ v

/-- The coefficient field on conformal jets at `z` depends on the Floer data `J`, `Ks`, `Kt` only
through their values at `z`, as functions of the target point. -/
theorem floerConformalJetCoeff_congr_data (ω : SymplecticForm V) (ρ : ℝ × ℝ → ℝ)
    {J J' : ℝ × ℝ → V → V →L[ℝ] V} {Ks Ks' Kt Kt' : ℝ × ℝ → V → ℝ} (u : ℝ × ℝ → V)
    {z : ℝ × ℝ} (hJ : J z = J' z) (hKs : Ks z = Ks' z) (hKt : Kt z = Kt' z) :
    ω.floerConformalJetCoeff ρ J Ks Kt u z = ω.floerConformalJetCoeff ρ J' Ks' Kt' u z := by
  rw [floerConformalJetCoeff_def, floerConformalJetCoeff_def,
    ω.floerLinearizationCoeff_congr_data u hJ hKs hKt, hJ]

/-- At a point where the weight is positive, the coefficient field applied to the jet
`(√ρ ξ, ∂s ξ, ∂t ξ)` of a section `ξ` is the linearized Floer operator `D_u ξ`. -/
@[simp]
theorem floerConformalJetCoeff_jet (ω : SymplecticForm V) {ρ : ℝ × ℝ → ℝ}
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u ξ : ℝ × ℝ → V) {z : ℝ × ℝ}
    (hz : 0 < ρ z) :
    ω.floerConformalJetCoeff ρ J Ks Kt u z (jet ρ ξ z) = ω.floerLinearization J Ks Kt u ξ z := by
  rw [floerConformalJetCoeff_apply, jet_apply, floerLinearization_eq_add, map_smul, smul_smul,
    inv_mul_cancel₀ (Real.sqrt_pos.2 hz).ne', one_smul, stdComplexLineReal_eq,
    stdComplexLineImag_eq]

/-- The norm of the coefficient field on conformal jets is at most
`1 + ‖J(z, u z)‖ + ρ(z)^(-1/2) ‖C(z)‖`. -/
theorem norm_floerConformalJetCoeff_le (ω : SymplecticForm V) (ρ : ℝ × ℝ → ℝ)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ‖ω.floerConformalJetCoeff ρ J Ks Kt u z‖ ≤
      1 + ‖J z (u z)‖ + (√(ρ z))⁻¹ * ‖ω.floerLinearizationCoeff J Ks Kt u z‖ := by
  refine (norm_firstOrderJetCoeff_le _ _).trans_eq ?_
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _)]

/-- **The coefficient field on conformal jets on an end.** Let `φ` be a chart of an end with
`J(φ ζ, ·) = J_e(ζ, ·)`, let `C` be the zeroth-order part of `D_u` and let `C_e` be the
zeroth-order part for end data `K'`, with the structures `J ∘ φ`, along `u ∘ φ`. If `B` bounds the
coefficient field on jets of the end data, with the structures `J_e`, along `u ∘ φ` at `ζ`, and if
`r ‖C(φ ζ)‖ ≤ (1 + ‖J(φ ζ, u (φ ζ))‖) ‖C_e(ζ)‖` and `ρ(φ ζ)^(-1/2) ≤ κ r` with `κ ≥ 0`, then the
coefficient field on conformal jets is at most `1 + B + κ (1 + B) B` at `φ ζ`. -/
theorem norm_floerConformalJetCoeff_le_of_norm_floerJetCoeff_comp_le (ω : SymplecticForm V)
    {ρ : ℝ × ℝ → ℝ} {J Je : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt Ks' Kt' : ℝ × ℝ → V → ℝ}
    {u : ℝ × ℝ → V} {φ : ℝ × ℝ → ℝ × ℝ} {ζ : ℝ × ℝ} {B κ r : ℝ} (hJ : J (φ ζ) = Je ζ)
    (hB : ‖ω.floerJetCoeff Je Ks' Kt' (u ∘ φ) ζ‖ ≤ B)
    (hC : r * ‖ω.floerLinearizationCoeff J Ks Kt u (φ ζ)‖ ≤
      (1 + ‖J (φ ζ) (u (φ ζ))‖) * ‖ω.floerLinearizationCoeff (J ∘ φ) Ks' Kt' (u ∘ φ) ζ‖)
    (hρ : (√(ρ (φ ζ)))⁻¹ ≤ κ * r) (hκ : 0 ≤ κ) :
    ‖ω.floerConformalJetCoeff ρ J Ks Kt u (φ ζ)‖ ≤ 1 + B + κ * ((1 + B) * B) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hB
  rw [floerJetCoeff_def] at hB
  -- The leading coefficient `J(φ ζ, u (φ ζ)) = J_e(ζ, u (φ ζ))` and the end coefficient `C_e(ζ)`
  -- are components of the coefficient field on jets of the end data.
  have hJb : ‖J (φ ζ) (u (φ ζ))‖ ≤ B := by
    rw [hJ]
    exact (norm_le_norm_firstOrderJetCoeff_left _ _).trans hB
  have hCe : ‖ω.floerLinearizationCoeff (J ∘ φ) Ks' Kt' (u ∘ φ) ζ‖ ≤ B := by
    have heq : ω.floerLinearizationCoeff (J ∘ φ) Ks' Kt' (u ∘ φ) ζ =
        ω.floerLinearizationCoeff Je Ks' Kt' (u ∘ φ) ζ := by
      ext v
      simp only [floerLinearizationCoeff_apply, Function.comp_apply, hJ]
    rw [heq]
    exact (norm_le_norm_firstOrderJetCoeff_right _ _).trans hB
  refine (ω.norm_floerConformalJetCoeff_le _ _ _ _ _ _).trans ?_
  calc _ ≤ 1 + B + κ * (r * ‖ω.floerLinearizationCoeff J Ks Kt u (φ ζ)‖) := by
        rw [← mul_assoc]
        gcongr
    _ ≤ 1 + B + κ * ((1 + B) * B) := by
        have h1 : 1 + ‖J (φ ζ) (u (φ ζ))‖ ≤ 1 + B := by linarith
        gcongr 1 + B + κ * ?_
        exact hC.trans (mul_le_mul h1 hCe (norm_nonneg _) (by linarith))

/-- **The coefficient field on conformal jets in a holomorphic chart of an end.** Let `ψ` be
holomorphic at `ζ` with Jacobian `r²`, `r > 0`, and let the pulled-back perturbation `ψ^*K` at `ζ`
be the cylindrical datum `H_e(t) dt`, with `K_s` and `K_t` of class `C²` at `ψ ζ`, the structures
`J(ψ ζ, ·) = J_e(t)`, and `u` solve the Floer equation at `ψ ζ`. If `B` bounds the coefficient
field on jets of the end datum, with the structures `J_e`, along `u ∘ ψ` at `ζ`, and
`ρ(ψ ζ)^(-1/2) ≤ κ r` with `κ ≥ 0`, then the coefficient field on conformal jets is at most
`1 + B + κ (1 + B) B` at `ψ ζ`. -/
theorem norm_floerConformalJetCoeff_le_of_perturbationPullback (ω : SymplecticForm V)
    {ρ : ℝ × ℝ → ℝ} {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Je : ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ} {He : ℝ → V → ℝ}
    {u : ℝ × ℝ → V} {ψ : ℝ × ℝ → ℝ × ℝ} {ζ : ℝ × ℝ} {r κ B : ℝ}
    (hψ : DifferentiableAt ℝ ψ ζ)
    (hψJ : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) (fderiv ℝ ψ ζ : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ))
    (hdet : (fderiv ℝ ψ ζ).det = r ^ 2) (hr : 0 < r) (hJζ : J (ψ ζ) = Je ζ.2)
    (hKs : ContDiff ℝ 2 (Ks (ψ ζ))) (hKt : ContDiff ℝ 2 (Kt (ψ ζ)))
    (hKs₀ : Floer.perturbationPullback ψ Ks Kt stdComplexLineReal ζ = 0)
    (hKtH : Floer.perturbationPullback ψ Ks Kt stdComplexLineImag ζ = He ζ.2)
    (hu : DifferentiableAt ℝ u (ψ ζ))
    (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (ψ ζ) (u (ψ ζ)))
      (ω.perturbedFDeriv Ks Kt u (ψ ζ) : ℝ × ℝ →ₗ[ℝ] V))
    (hB : ‖ω.floerJetCoeff (fun w y ↦ (Je w.2 y).toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun w ↦ He w.2) (u ∘ ψ) ζ‖ ≤ B)
    (hρ : (√(ρ (ψ ζ)))⁻¹ ≤ κ * r) (hκ : 0 ≤ κ) :
    ‖ω.floerConformalJetCoeff ρ (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u
      (ψ ζ)‖ ≤ 1 + B + κ * ((1 + B) * B) := by
  have hXs := ((ω.contDiff_hamiltonianVectorField (n := 1) hKs).differentiable one_ne_zero)
    (u (ψ ζ))
  have hXt := ((ω.contDiff_hamiltonianVectorField (n := 1) hKt).differentiable one_ne_zero)
    (u (ψ ζ))
  -- The zeroth-order part of the operator of the pulled-back data is `a C - b J C`, and the
  -- pulled-back data at `ζ` are the end data `(0, H_e(t))`.
  have hcoef := ω.floerLinearizationCoeff_perturbationPullback (J := J) hψ hψJ hu
    (.of_forall fun y ↦ hKs.differentiable two_ne_zero y)
    (.of_forall fun y ↦ hKt.differentiable two_ne_zero y) hXs hXt
    ((floerOperator_eq_zero_iff ω J Ks Kt u (ψ ζ)).2 hF)
  rw [ω.floerLinearizationCoeff_congr_data (u ∘ ψ) (Ks' := fun _ _ ↦ 0) (Kt' := fun w ↦ He w.2)
    rfl hKs₀ hKtH] at hcoef
  have hab : (fderiv ℝ ψ ζ stdComplexLineReal).1 ^ 2 + (fderiv ℝ ψ ζ stdComplexLineReal).2 ^ 2 =
      r ^ 2 := by
    rw [← hdet, ContinuousLinearMap.det, hψJ.det_eq_sq_add_sq, ContinuousLinearMap.coe_coe]
  refine ω.norm_floerConformalJetCoeff_le_of_norm_floerJetCoeff_comp_le
    (Je := fun w y ↦ (Je w.2 y).toLinearMap.toContinuousLinearMap) (by simp only [hJζ]) hB ?_
    hρ hκ
  exact (J (ψ ζ) (u (ψ ζ))).mul_opNorm_le_of_eq_smul_sub_smul
    (fun v ↦ by simpa [Function.comp_def] using congrArg (fun L : V →L[ℝ] V ↦ L v) hcoef) hab hr

/-- The coefficient field on conformal jets of a family of Floer data `(J_μ, K_{s,μ}, K_{t,μ})`
with parameter `μ` in a real normed space `P` along `u` is continuous jointly in `μ` and the
domain point `z` at `(μ, z)` when the family is `C¹` (with `C²` Hamiltonians) jointly in `μ`, `z`
and the target point at `((μ, z), u z)`, `u` is `C¹` at `z`, and the weight is continuous and
positive at `z`. -/
theorem continuousAt_floerConformalJetCoeff_family {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] (ω : SymplecticForm V) {ρ : ℝ × ℝ → ℝ} {J : P × (ℝ × ℝ) → V → V →L[ℝ] V}
    {Ks Kt : P × (ℝ × ℝ) → V → ℝ} {u : ℝ × ℝ → V} {p : P × (ℝ × ℝ)}
    (hJ : ContDiffAt ℝ 1 (uncurry J) (p, u p.2))
    (hKs : ContDiffAt ℝ 2 (uncurry Ks) (p, u p.2)) (hKt : ContDiffAt ℝ 2 (uncurry Kt) (p, u p.2))
    (hu : ContDiffAt ℝ 1 u p.2) (hρ : ContinuousAt ρ p.2) (hρp : 0 < ρ p.2) :
    ContinuousAt (fun q : P × (ℝ × ℝ) ↦ ω.floerConformalJetCoeff ρ (fun z ↦ J (q.1, z))
      (fun z ↦ Ks (q.1, z)) (fun z ↦ Kt (q.1, z)) u q.2) p := by
  have hJu : ContinuousAt (fun q ↦ J q (u q.2)) p :=
    ContinuousAt.comp (f := fun q : P × (ℝ × ℝ) ↦ (q, u q.2)) hJ.continuousAt
      (continuousAt_id.prodMk (hu.continuousAt.comp continuousAt_snd))
  have hρq : ContinuousAt (fun q : P × (ℝ × ℝ) ↦ (√(ρ q.2))⁻¹) p :=
    ((hρ.comp continuousAt_snd).sqrt).inv₀ (Real.sqrt_pos.2 hρp).ne'
  simp only [floerConformalJetCoeff_def]
  exact continuousAt_firstOrderJetCoeff hJu
    (hρq.smul (ω.continuousAt_floerLinearizationCoeff_family hJ hKs hKt hu))

/-- **The coefficient fields of a family of data converge in `L^∞`.** Let
`(J_μ, K_{s,μ}, K_{t,μ})` be a family of Floer data with parameter `μ` in a real normed space `P`
which, for `μ` near `lam`, agrees on `U` off a compact set `K` with the data at `lam`. Suppose that
at every point `z` of `K` the family is `C¹` (with `C²` Hamiltonians) jointly in the parameter, the
domain point and the target point at `((lam, z), u z)`, `u` is `C¹` at `z`, and the weight is
continuous and positive at `z`. If the coefficient fields on conformal jets along `u` are almost
everywhere strongly measurable on `U` for `μ` near `lam`, then they converge in `L^∞(U)` to the
coefficient field at `lam` as `μ → lam`. -/
theorem tendsto_eLpNorm_floerConformalJetCoeff_family {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] (ω : SymplecticForm V) {U K : Set (ℝ × ℝ)} (hU : MeasurableSet U)
    (hK : IsCompact K) {ρ : ℝ × ℝ → ℝ} {J : P × (ℝ × ℝ) → V → V →L[ℝ] V}
    {Ks Kt : P × (ℝ × ℝ) → V → ℝ} {u : ℝ × ℝ → V} {lam : P}
    (hJ : ∀ z ∈ K, ContDiffAt ℝ 1 (uncurry J) ((lam, z), u z))
    (hKs : ∀ z ∈ K, ContDiffAt ℝ 2 (uncurry Ks) ((lam, z), u z))
    (hKt : ∀ z ∈ K, ContDiffAt ℝ 2 (uncurry Kt) ((lam, z), u z))
    (hu : ∀ z ∈ K, ContDiffAt ℝ 1 u z) (hρ : ∀ z ∈ K, ContinuousAt ρ z)
    (hρp : ∀ z ∈ K, 0 < ρ z)
    (heq : ∀ᶠ μ in nhds lam, ∀ z ∈ U, z ∉ K →
      J (μ, z) = J (lam, z) ∧ Ks (μ, z) = Ks (lam, z) ∧ Kt (μ, z) = Kt (lam, z))
    (hmeas : ∀ᶠ μ in nhds lam, AEStronglyMeasurable (ω.floerConformalJetCoeff ρ
      (fun z ↦ J (μ, z)) (fun z ↦ Ks (μ, z)) (fun z ↦ Kt (μ, z)) u) (volume.restrict U)) :
    Filter.Tendsto (fun μ ↦ eLpNorm (ω.floerConformalJetCoeff ρ (fun z ↦ J (μ, z))
      (fun z ↦ Ks (μ, z)) (fun z ↦ Kt (μ, z)) u - ω.floerConformalJetCoeff ρ (fun z ↦ J (lam, z))
        (fun z ↦ Ks (lam, z)) (fun z ↦ Kt (lam, z)) u) ∞ (volume.restrict U)) (nhds lam)
      (nhds 0) :=
  tendsto_eLpNorm_top_sub_of_continuousAt_of_eq
    (M := fun μ ↦ ω.floerConformalJetCoeff ρ (fun z ↦ J (μ, z)) (fun z ↦ Ks (μ, z))
      (fun z ↦ Kt (μ, z)) u) hU hK hmeas
    (fun z hz ↦ ω.continuousAt_floerConformalJetCoeff_family (p := (lam, z)) (hJ z hz) (hKs z hz)
      (hKt z hz) (hu z hz) (hρ z hz) (hρp z hz))
    (heq.mono fun _ hμ z hzU hzK ↦ by
      obtain ⟨hJz, hsz, htz⟩ := hμ z hzU hzK
      exact ω.floerConformalJetCoeff_congr_data ρ u hJz hsz htz)

/-- The coefficient field on conformal jets is continuous on `U` when the weight is a conformal
weight on `U`, the data are `C¹` (and the Hamiltonians `C²`) along the graph of `u` over `U`, and
`u` is `C¹` on `U`. -/
theorem continuousOn_floerConformalJetCoeff (ω : SymplecticForm V) {U : Set (ℝ × ℝ)}
    {ρ : ℝ × ℝ → ℝ} (hρ : IsWeight U ρ) {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ}
    {u : ℝ × ℝ → V} (hJ : ∀ z ∈ U, ContDiffAt ℝ 1 (uncurry J) (z, u z))
    (hKs : ∀ z ∈ U, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ U, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiffOn ℝ 1 u U) :
    ContinuousOn (ω.floerConformalJetCoeff ρ J Ks Kt u) U := by
  intro z hz
  -- The data form a constant family over the parameter space `ℝ`.
  have hπ {m : WithTop ℕ∞} :
      ContDiffAt ℝ m (fun x : (ℝ × (ℝ × ℝ)) × V ↦ (x.1.2, x.2)) (((0 : ℝ), z), u z) :=
    (contDiff_fst.snd.prodMk contDiff_snd).contDiffAt
  have h := ω.continuousAt_floerConformalJetCoeff_family (P := ℝ) (J := fun q ↦ J q.2)
    (Ks := fun q ↦ Ks q.2) (Kt := fun q ↦ Kt q.2) (p := (0, z))
    ((hJ z hz).comp (((0 : ℝ), z), u z) hπ) ((hKs z hz).comp (((0 : ℝ), z), u z) hπ)
    ((hKt z hz).comp (((0 : ℝ), z), u z) hπ) (hu.contDiffAt (hρ.isOpen.mem_nhds hz))
    (hρ.continuousOn.continuousAt (hρ.isOpen.mem_nhds hz)) (hρ.pos z hz)
  exact (h.comp (f := fun w : ℝ × ℝ ↦ ((0 : ℝ), w))
    (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt

/-- **The coefficient field on conformal jets is bounded when the data are constant near
infinity.** Let `ρ` be a conformal weight on the whole plane, and let the Floer data `J`, `K_s`,
`K_t` be a fixed `J₀` and the zero perturbation on `‖w‖ ≥ T`, with `J` `C¹` and `K_s`, `K_t` `C²`
along a `C¹` map `u`. Then the coefficient field of the linearized Floer operator on the conformal
jets of `ρ` is essentially bounded on the plane: on `‖w‖ ≥ T` it is that of `∂s + J₀ ∂t`. -/
theorem memLp_floerConformalJetCoeff_of_eq_base (ω : SymplecticForm V) {ρ : ℝ × ℝ → ℝ}
    (hρ : IsWeight univ ρ) {J : ℝ × ℝ → V → V →L[ℝ] V} {J₀ : V →L[ℝ] V}
    {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V} {T : ℝ}
    (hJ₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, J z y = J₀)
    (hKs₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Ks z y = 0)
    (hKt₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Kt z y = 0)
    (hJ : ∀ z, ContDiffAt ℝ 1 (uncurry J) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiff ℝ 1 u) :
    MemLp (ω.floerConformalJetCoeff ρ J Ks Kt u) ∞ (volume.restrict univ) := by
  have hcont := ω.continuousOn_floerConformalJetCoeff hρ (fun z _ ↦ hJ z) (fun z _ ↦ hKs z)
    (fun z _ ↦ hKt z) hu.contDiffOn
  -- On the compact square `‖w‖ ≤ T` the field is continuous, hence bounded.
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℝ × ℝ) T).exists_bound_of_continuousOn
    (hcont.mono (subset_univ _))
  refine memLp_top_of_bound (hcont.aestronglyMeasurable MeasurableSet.univ) (max B (1 + ‖J₀‖))
    (Filter.Eventually.of_forall fun z ↦ ?_)
  rcases le_or_gt ‖z‖ T with hz | hz
  · exact (hB z (mem_closedBall_zero_iff.2 hz)).trans (le_max_left _ _)
  -- Beyond the square the field is that of the Cauchy–Riemann operator of `J₀`.
  refine le_max_of_le_right ((ω.norm_floerConformalJetCoeff_le _ _ _ _ _ z).trans_eq ?_)
  rw [ω.floerLinearizationCoeff_eq_zero_of_eq_base u (hJ₀ z hz.le) (hKs₀ z hz.le)
    (hKt₀ z hz.le), norm_zero, mul_zero, add_zero, hJ₀ z hz.le]

variable (U : Set (ℝ × ℝ)) (ρ : ℝ × ℝ → ℝ)

/-- The linearized Floer operator `D_u` along `u`, as an operator from the Sobolev space
`W^{1,2}_0(U, V)` of the conformal metric `ρ (ds² + dt²)` (`TauCeti.ConformalSobolev.H1`) to
`L²(U, V)`. It is the first-order operator `TauCeti.jetOperator` of the coefficient
field on conformal jets, and it is `0` by convention when this field is not
essentially bounded on `U`. -/
def floerConformalSobolevOperator (ω : SymplecticForm V) (J : ℝ × ℝ → V → V →L[ℝ] V)
    (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) : H1 V U ρ →L[ℝ] Lp V 2 (volume.restrict U) :=
  (jetOperator 2 (volume.restrict U) (ω.floerConformalJetCoeff ρ J Ks Kt u)).comp
    (H1 V U ρ).subtypeL

/-- The definition of the conformal Sobolev realization of the linearized Floer operator. -/
theorem floerConformalSobolevOperator_def (ω : SymplecticForm V) (J : ℝ × ℝ → V → V →L[ℝ] V)
    (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) :
    ω.floerConformalSobolevOperator U ρ J Ks Kt u =
      (jetOperator 2 (volume.restrict U) (ω.floerConformalJetCoeff ρ J Ks Kt u)).comp
        (H1 V U ρ).subtypeL :=
  (rfl)

variable {U ρ}

/-- When the coefficient field on conformal jets is essentially bounded on `U`, the conformal
Sobolev realization of the linearized Floer operator acts pointwise on an `L²` jet `x ∈ H1` by the
coefficient field. -/
theorem coeFn_floerConformalSobolevOperator (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hM : MemLp (ω.floerConformalJetCoeff ρ J Ks Kt u) ∞ (volume.restrict U)) (x : H1 V U ρ) :
    ω.floerConformalSobolevOperator U ρ J Ks Kt u x =ᵐ[volume.restrict U]
      fun z ↦ ω.floerConformalJetCoeff ρ J Ks Kt u z
        ((x : Lp (V × V × V) 2 (volume.restrict U)) z) :=
  coeFn_jetOperator (p := 2) hM x

/-- On the jet of a test section `ξ`, the conformal Sobolev realization of the linearized Floer
operator is `D_u ξ`, when the coefficient field on conformal jets is essentially bounded on `U`. -/
theorem floerConformalSobolevOperator_toLp_jet_ae_eq (ω : SymplecticForm V) (hρ : IsWeight U ρ)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u ξ : ℝ × ℝ → V}
    (hM : MemLp (ω.floerConformalJetCoeff ρ J Ks Kt u) ∞ (volume.restrict U))
    (hξ : ξ ∈ testSection V U) :
    ω.floerConformalSobolevOperator U ρ J Ks Kt u
        ⟨(memLp_jet hρ hξ).toLp (jet ρ ξ), jetSubmodule_le_H1 (toLp_jet_mem_jetSubmodule hρ hξ)⟩
      =ᵐ[volume.restrict U] ω.floerLinearization J Ks Kt u ξ := by
  filter_upwards [jetOperator_toLp_jet_ae_eq hρ hM hξ,
    ae_restrict_mem hρ.isOpen.measurableSet] with z h hz
  rw [floerConformalSobolevOperator_def, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    h, floerConformalJetCoeff_jet ω J Ks Kt u ξ (hρ.pos z hz)]

/-- On the jet `x ∈ H1` of a test section `ξ`, the squared norm of the conformal Sobolev realization
of the linearized Floer operator is `∫ ‖D_u ξ‖²`, when the coefficient field on conformal jets is
essentially bounded on `U`. -/
theorem norm_floerConformalSobolevOperator_sq (ω : SymplecticForm V) (hρ : IsWeight U ρ)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u ξ : ℝ × ℝ → V}
    (hM : MemLp (ω.floerConformalJetCoeff ρ J Ks Kt u) ∞ (volume.restrict U))
    (hξ : ξ ∈ testSection V U) {x : H1 V U ρ}
    (hx : (x : Lp (V × V × V) 2 (volume.restrict U)) =ᵐ[volume.restrict U] jet ρ ξ) :
    ‖ω.floerConformalSobolevOperator U ρ J Ks Kt u x‖ ^ 2 =
      ∫ z, ‖ω.floerLinearization J Ks Kt u ξ z‖ ^ 2 := by
  have hxe : x = ⟨(memLp_jet hρ hξ).toLp (jet ρ ξ),
      jetSubmodule_le_H1 (toLp_jet_mem_jetSubmodule hρ hξ)⟩ :=
    Subtype.ext (Lp.ext (hx.trans (memLp_jet hρ hξ).coeFn_toLp.symm))
  have hae := floerConformalSobolevOperator_toLp_jet_ae_eq ω hρ hM hξ
  rw [← hxe] at hae
  rw [← Lp.integral_norm_sq_eq_norm_sq, integral_congr_ae (hae.mono fun z hz ↦
    congrArg (‖·‖ ^ 2) hz)]
  -- `D_u ξ` vanishes outside the support of `ξ`, which lies in `U`.
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ by
    rw [ω.floerLinearization_of_notMem_tsupport J Ks Kt u
      fun h ↦ hz ((mem_testSection_iff.1 hξ).2.2 h), norm_zero, zero_pow two_ne_zero]


/-- **Peetre's estimate from an energy estimate.** Let the coefficient field of the linearized
Floer operator `D_u` on the conformal jets of `ρ` be essentially bounded on `U`, let `K ⊆ U` be
compact, and suppose that every test section `ξ` on `U` has weighted energy

`∫_U (ρ ‖ξ‖² + ‖∂s ξ‖² + ‖∂t ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_K ‖ξ‖²)`.

Then there is `A` such that the jet `x ∈ W^{1,2}_0(U, V)` of every test section `ξ` satisfies
`‖x‖ ≤ A (‖D_u x‖ + ‖√ρ ξ‖_{L²(K)})`, the estimate consumed by Peetre's argument
`TauCeti.ConformalSobolev.finiteDimensional_ker_of_estimate`. -/
theorem exists_forall_norm_le_mul_norm_floerConformalSobolevOperator_add_of_integral_le
    (ω : SymplecticForm V) (hρ : IsWeight U ρ) {J : ℝ × ℝ → V → V →L[ℝ] V}
    {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hM : MemLp (ω.floerConformalJetCoeff ρ J Ks Kt u) ∞ (volume.restrict U))
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKU : K ⊆ U) {C : ℝ}
    (hest : ∀ ⦃ξ : ℝ × ℝ → V⦄, ξ ∈ testSection V U →
      ∫ z in U, (ρ z * ‖ξ z‖ ^ 2 + ‖fderiv ℝ ξ z (1, 0)‖ ^ 2 + ‖fderiv ℝ ξ z (0, 1)‖ ^ 2) ≤
        C * ((∫ z, ‖ω.floerLinearization J Ks Kt u ξ z‖ ^ 2) + ∫ z in K, ‖ξ z‖ ^ 2)) :
    ∃ A, ∀ x : H1 V U ρ, (x : Lp (V × V × V) 2 (volume.restrict U)) ∈ jetSubmodule V U ρ →
      ‖x‖ ≤ A * (‖ω.floerConformalSobolevOperator U ρ J Ks Kt u x‖ +
        ‖restrictWeightedValue V U K x‖) := by
  -- On `K` the `L²` norm of a section is controlled by its weighted value.
  obtain ⟨B, hB⟩ :=
    exists_setIntegral_norm_sq_le_mul_norm_restrictWeightedValue_sq (V := V) hρ hK hKU
  set k := max C 0 * (1 + |B|)
  refine ⟨√k, fun x hx ↦ ?_⟩
  obtain ⟨ξ, hξ, hxξ⟩ := mem_jetSubmodule_iff.1 hx
  set D := ω.floerConformalSobolevOperator U ρ J Ks Kt u
  set R := restrictWeightedValue V U K
  have hY : ∫ z in K, ‖ξ z‖ ^ 2 ≤ |B| * ‖R x‖ ^ 2 :=
    (hB (mem_testSection_iff.1 hξ).1.continuous.continuousOn hxξ).trans
      (by gcongr; exact le_abs_self B)
  -- Assemble: `‖x‖² ≤ k (‖D x‖ + ‖R x‖)²`.
  have hx2 : ‖x‖ ^ 2 ≤ k * (‖D x‖ + ‖R x‖) ^ 2 := by
    have h₁ : C * ((∫ z, ‖ω.floerLinearization J Ks Kt u ξ z‖ ^ 2) + ∫ z in K, ‖ξ z‖ ^ 2) ≤
        max C 0 * (‖D x‖ ^ 2 + |B| * ‖R x‖ ^ 2) := by
      rw [← norm_floerConformalSobolevOperator_sq ω hρ hM hξ hxξ]
      exact mul_le_mul (le_max_left C 0) (by linarith)
        (add_nonneg (sq_nonneg _) (setIntegral_nonneg hK.measurableSet fun _ _ ↦ sq_nonneg _))
        (le_max_right C 0)
    have h₂ : ‖D x‖ ^ 2 + |B| * ‖R x‖ ^ 2 ≤ (1 + |B|) * (‖D x‖ + ‖R x‖) ^ 2 := by
      nlinarith [norm_nonneg (D x), norm_nonneg (R x), abs_nonneg B,
        mul_nonneg (norm_nonneg (D x)) (norm_nonneg (R x)),
        mul_nonneg (abs_nonneg B) (mul_nonneg (norm_nonneg (D x)) (norm_nonneg (R x))),
        mul_nonneg (abs_nonneg B) (sq_nonneg ‖D x‖)]
    calc ‖x‖ ^ 2 ≤ max C 0 * (‖D x‖ ^ 2 + |B| * ‖R x‖ ^ 2) :=
          (sq_norm_le_integral hρ hξ hxξ).trans ((hest hξ).trans h₁)
      _ ≤ max C 0 * ((1 + |B|) * (‖D x‖ + ‖R x‖) ^ 2) := by gcongr
      _ = k * (‖D x‖ + ‖R x‖) ^ 2 := by ring
  calc ‖x‖ = √(‖x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ √(k * (‖D x‖ + ‖R x‖) ^ 2) := Real.sqrt_le_sqrt hx2
    _ = √k * (‖D x‖ + ‖R x‖) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

end TauCeti.SymplecticForm
