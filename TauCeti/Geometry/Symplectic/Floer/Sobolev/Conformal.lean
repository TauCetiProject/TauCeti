/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Conformal
public import TauCeti.Geometry.Symplectic.Floer.Linearization.Basic
import Mathlib.Analysis.Normed.Operator.Prod

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
point of `U` is `D_u ξ (z)` (`TauCeti.SymplecticForm.floerConformalJetCoeff_jet`). The operator is
bounded exactly when `M` is essentially bounded on `U`. Its first two terms are bounded where `J`
is, so the condition is that `C(z)` grows at most like `√ρ(z)` (`norm_floerConformalJetCoeff_le`):
on a cylindrical end of `U`, where `ρ` is the conformal factor of the metric `ds² + dt²`, this says
that the zeroth-order part of `D_u` in the end coordinates is bounded. The realization is
`TauCeti.SymplecticForm.floerConformalSobolevOperator`, which agrees with `D_u` on test sections
(`TauCeti.SymplecticForm.floerConformalSobolevOperator_toLp_jet_ae_eq`).

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
conformal weight `ρ`: at `z`, the linear map `(a, b, c) ↦ b + J(z, u z) c + ρ(z)^(-1/2) C(z) a`,
where `C` is the zeroth-order part `TauCeti.SymplecticForm.floerLinearizationCoeff`. -/
def floerConformalJetCoeff (ω : SymplecticForm V) (ρ : ℝ × ℝ → ℝ) (J : ℝ × ℝ → V → V →L[ℝ] V)
    (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) (z : ℝ × ℝ) : V × V × V →L[ℝ] V :=
  (fst ℝ V V).comp (snd ℝ V (V × V)) + (J z (u z)).comp ((snd ℝ V V).comp (snd ℝ V (V × V))) +
    ((√(ρ z))⁻¹ • ω.floerLinearizationCoeff J Ks Kt u z).comp (fst ℝ V (V × V))

/-- The coefficient field of the linearized Floer operator on conformal jets, evaluated on a
jet. -/
theorem floerConformalJetCoeff_apply (ω : SymplecticForm V) (ρ : ℝ × ℝ → ℝ)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) (z : ℝ × ℝ)
    (v : V × V × V) :
    ω.floerConformalJetCoeff ρ J Ks Kt u z v =
      v.2.1 + J z (u z) v.2.2 + (√(ρ z))⁻¹ • ω.floerLinearizationCoeff J Ks Kt u z v.1 :=
  (rfl)

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
  refine norm_add₃_le.trans (add_le_add (add_le_add ?_ ?_) ?_)
  · exact (opNorm_comp_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _)
      (ContinuousLinearMap.norm_fst_le ℝ V V)).trans (ContinuousLinearMap.norm_snd_le ℝ V (V × V)))
  · refine (opNorm_comp_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) ?_)
    exact (opNorm_comp_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _)
      (ContinuousLinearMap.norm_snd_le ℝ V V)).trans (ContinuousLinearMap.norm_snd_le ℝ V (V × V)))
  · refine (opNorm_comp_le _ _).trans ((mul_le_of_le_one_right (norm_nonneg _)
      (ContinuousLinearMap.norm_fst_le ℝ V (V × V))).trans ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _)]

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
  have huz : ContDiffAt ℝ 1 u z := hu.contDiffAt (hρ.isOpen.mem_nhds hz)
  have hJu : ContinuousAt (fun z ↦ J z (u z)) z :=
    (hJ z hz).continuousAt.comp (f := fun z ↦ (z, u z))
      (continuousAt_id.prodMk huz.continuousAt)
  have hA := ω.continuousAt_floerLinearizationCoeff (hJ z hz) (hKs z hz) (hKt z hz) huz
  have hρz : ContinuousAt (fun z ↦ (√(ρ z))⁻¹) z :=
    ((hρ.continuousOn.continuousAt (hρ.isOpen.mem_nhds hz)).sqrt).inv₀
      (Real.sqrt_pos.2 (hρ.pos z hz)).ne'
  exact ((continuousAt_const.add (hJu.clm_comp continuousAt_const)).add
    ((hρz.smul hA).clm_comp continuousAt_const)).continuousWithinAt

variable (U : Set (ℝ × ℝ)) (ρ : ℝ × ℝ → ℝ)

/-- The linearized Floer operator `D_u` along `u`, as an operator from the Sobolev space
`W^{1,2}_0(U, V)` of the conformal metric `ρ (ds² + dt²)` (`TauCeti.ConformalSobolev.H1`) to
`L²(U, V)`. It is the first-order operator `TauCeti.ConformalSobolev.jetOperator` of the
coefficient field on conformal jets, and it is `0` by convention when this field is not
essentially bounded on `U`. -/
def floerConformalSobolevOperator (ω : SymplecticForm V) (J : ℝ × ℝ → V → V →L[ℝ] V)
    (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) : H1 V U ρ →L[ℝ] Lp V 2 (volume.restrict U) :=
  (jetOperator U (ω.floerConformalJetCoeff ρ J Ks Kt u)).comp (H1 V U ρ).subtypeL

/-- The definition of the conformal Sobolev realization of the linearized Floer operator. -/
theorem floerConformalSobolevOperator_def (ω : SymplecticForm V) (J : ℝ × ℝ → V → V →L[ℝ] V)
    (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) :
    ω.floerConformalSobolevOperator U ρ J Ks Kt u =
      (jetOperator U (ω.floerConformalJetCoeff ρ J Ks Kt u)).comp (H1 V U ρ).subtypeL :=
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
  coeFn_jetOperator hM x

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

end TauCeti.SymplecticForm
