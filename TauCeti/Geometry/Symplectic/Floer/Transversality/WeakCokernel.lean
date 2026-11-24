/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Annihilator
public import TauCeti.Analysis.Distribution.TestFunction.LinearEquiv
public import TauCeti.Analysis.Sobolev.Local.Morrey
public import TauCeti.Geometry.Symplectic.Floer.Linearization.Basic
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Sobolev regularity of weak cokernel elements of the linearized Floer operator

Let `u : ℝ × ℝ → V` be a `C¹` map into a finite-dimensional symplectic vector space `V`, and let
`D_u ξ = ∂ₛξ + J(z, u) ∂ₜξ + C(z) ξ` be the linearized Floer operator at `u`
(`TauCeti.SymplecticForm.floerLinearization`, written in this form by
`TauCeti.SymplecticForm.floerLinearization_eq_add`). The transversality argument of
`TauCeti.Geometry.Symplectic.Floer.Transversality.Cokernel` shows that a `C¹` covector field `η`
annihilating the range of the universal linearized operator vanishes. A cokernel element of a
Sobolev realization of `D_u` is a priori only an `L^q` covector field annihilating `D_u ξ` for every
test map `ξ`, so before that argument applies it has to be shown to be regular. This file proves
the first step of that regularity: such an `η` is in `W^{1,r}_loc` for every finite `r > 1`
(`TauCeti.SymplecticForm.memWkpLoc_one_of_forall_integral_apply_floerLinearization_eq_zero`).

The Sobolev classes `W^{k,r}_loc` of Tau Ceti live on `ℂ`, so the statement reads the domain
through `e = Complex.equivRealProdCLM : ℂ ≃L[ℝ] ℝ × ℝ`, `s + i t ↦ (s, t)`, which carries Lebesgue
measure to Lebesgue measure: it is Mathlib's measure-preserving `Complex.measurableEquivRealProd`
(`Complex.coe_measurableEquivRealProd_eq_equivRealProdCLM`).

On an open set `Ω ⊆ ℂ`, a test function `φ` on `Ω` gives the test map `ξ = φ ∘ e⁻¹` on
`ℝ × ℝ`, and `D_u ξ (e w) = ∂ₛφ(w) + J_c(w) ∂ₜφ(w) + S_c(w) φ(w)` with `J_c(w) = J(e w, u(e w))`
and `S_c(w) = C(e w)` (`TauCeti.SymplecticForm.floerLinearization_comp_equivRealProdCLM_symm`).
These coefficients are `C¹` and continuous, so `η ∘ e` annihilates a real Cauchy–Riemann operator
with `C¹` coefficients, and the regularity of such annihilators
(`TauCeti.memWkpLoc_one_of_forall_integral_apply_cauchyRiemann_eq_zero`) applies. No inner
product on `V` is needed.

By Morrey's embedding (`r > 2`), `η ∘ e` then has a continuous representative, which is the
regularity taken by the pointwise detection lemmas of
`TauCeti.Geometry.Symplectic.Floer.Transversality.AlmostComplexVariation`. Higher regularity, and
in particular the `C¹` regularity used by unique continuation in the transversality argument,
follows by the induction on the order of differentiability of McDuff and Salamon
(Proposition B.4.9), from the differentiated equation; it is not carried out here.

## Main results

* `TauCeti.SymplecticForm.floerLinearization_comp_equivRealProdCLM_symm`: the linearized Floer
  operator of `φ ∘ e⁻¹` in the coordinate of `ℂ`.
* `TauCeti.SymplecticForm.memWkpLoc_one_of_forall_integral_apply_floerLinearization_eq_zero`:
  a locally `L^q` (`q > 1`) covector field annihilating `D_u` on test maps is in `W^{1,r}_loc` for
  every finite `r > 1`.
* `continuousOn_preciseRepresentative_of_forall_integral_apply_floerLinearization_eq_zero`, in
  the namespace `TauCeti.SymplecticForm`: by Morrey's embedding, such a covector field has a
  continuous representative.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Proposition 3.2.1 (the cokernel of the universal operator)
  and Appendix B.4 (Proposition B.4.9, elliptic regularity of weak solutions).
* A. Floer, H. Hofer and D. Salamon, *Transversality in elliptic Morse theory for the symplectic
  action*, Duke Math. J. 80 (1995), 251–292.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Complex Set Function
open scoped Distributions ENNReal

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}

/-- **The linearized Floer operator in the coordinate of `ℂ`.** For `φ : ℂ → V` and
`e = Complex.equivRealProdCLM`, the linearized Floer operator of `φ ∘ e⁻¹` at `e w` is the real
Cauchy–Riemann operator `∂ₛ + J(e w, u(e w)) ∂ₜ + C(e w)` applied to `φ` at `w`, where
`∂ₛ φ = dφ(1)`, `∂ₜ φ = dφ(i)` and `C` is `TauCeti.SymplecticForm.floerLinearizationCoeff`. -/
theorem floerLinearization_comp_equivRealProdCLM_symm (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) (φ : ℂ → V) (w : ℂ) :
    ω.floerLinearization J Ks Kt u (φ ∘ equivRealProdCLM.symm) (equivRealProdCLM w) =
      fderiv ℝ φ w 1 + J (equivRealProdCLM w) (u (equivRealProdCLM w)) (fderiv ℝ φ w I) +
        ω.floerLinearizationCoeff J Ks Kt u (equivRealProdCLM w) (φ w) := by
  rw [floerLinearization_eq_add, ContinuousLinearEquiv.comp_right_fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply, comp_apply, equivRealProdCLM_symm_stdComplexLineReal,
    equivRealProdCLM_symm_stdComplexLineImag]

/-- **Weak cokernel elements of the linearized Floer operator are `W^{1,r}_loc`.** Let `Ω ⊆ ℂ`
be open and `e = Complex.equivRealProdCLM`. Suppose that over `e '' Ω` the map `u` is `C¹`, the
almost complex structure `J` is `C¹` and squares to `-1` along `u`, and the Hamiltonians `Ks`,
`Kt` are `C²`. Let `η` be a covector field with `η ∘ e` locally `L^q` on `Ω` for some `q > 1`,
annihilating `D_u ξ` under the pairing `∫ η(·)` for every smooth compactly supported `ξ` supported
over `Ω`. Then `η ∘ e` is in `W^{1,r}_loc(Ω)` for every finite `r > 1`. -/
theorem memWkpLoc_one_of_forall_integral_apply_floerLinearization_eq_zero {Ω : Opens ℂ}
    (hJ : ∀ w ∈ Ω, ContDiffAt ℝ 1 (uncurry J) (equivRealProdCLM w, u (equivRealProdCLM w)))
    (hKs : ∀ w ∈ Ω, ContDiffAt ℝ 2 (uncurry Ks) (equivRealProdCLM w, u (equivRealProdCLM w)))
    (hKt : ∀ w ∈ Ω, ContDiffAt ℝ 2 (uncurry Kt) (equivRealProdCLM w, u (equivRealProdCLM w)))
    (hu : ∀ w ∈ Ω, ContDiffAt ℝ 1 u (equivRealProdCLM w))
    (hJ2 : ∀ w ∈ Ω, J (equivRealProdCLM w) (u (equivRealProdCLM w)) *
      J (equivRealProdCLM w) (u (equivRealProdCLM w)) = -1)
    {η : ℝ × ℝ → V →L[ℝ] ℝ} {q : ℝ≥0∞} (hq : 1 < q)
    (hη : MemLpLoc q Ω fun w ↦ η (equivRealProdCLM w))
    (hηD : ∀ ξ : ℝ × ℝ → V, ContDiff ℝ (⊤ : ℕ∞) ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ equivRealProdCLM.symm ⁻¹' Ω →
        ∫ z, η z (ω.floerLinearization J Ks Kt u ξ z) = 0)
    {r : ℝ≥0∞} (hr : 1 < r) (hr_top : r ≠ ⊤) :
    MemWkpLoc r Ω 1 fun w ↦ η (equivRealProdCLM w) := by
  set e : ℂ ≃L[ℝ] ℝ × ℝ := equivRealProdCLM
  -- The coefficients of `D_u` in the coordinate of `ℂ`.
  have hJc : ContDiffOn ℝ 1 (fun w ↦ J (e w) (u (e w))) Ω := fun w hw ↦ by
    have hg : ContDiffAt ℝ 1 (fun w ↦ (e w, u (e w))) w :=
      e.contDiff.contDiffAt.prodMk ((hu w hw).comp w e.contDiff.contDiffAt)
    exact ((hJ w hw).comp w hg).contDiffWithinAt
  have hSc : ContinuousOn (fun w ↦ ω.floerLinearizationCoeff J Ks Kt u (e w)) Ω := fun w hw ↦
    ((continuousAt_floerLinearizationCoeff ω (hJ w hw) (hKs w hw) (hKt w hw)
      (hu w hw)).comp e.continuous.continuousAt).continuousWithinAt
  refine memWkpLoc_one_of_forall_integral_apply_cauchyRiemann_eq_zero hJc hSc hJ2 hq hη
    (fun φ ↦ ?_) hr hr_top
  -- A test function `φ` on `Ω` gives the test map `φ ∘ e⁻¹` supported over `Ω`.
  set U : Opens (ℝ × ℝ) := ⟨e.symm ⁻¹' Ω, Ω.isOpen.preimage e.symm.continuous⟩
  have hmaps : MapsTo e Ω U := fun w hw ↦ by simpa [U] using hw
  set ψ : 𝓓(U, V) := e.transportTestFunction hmaps φ
  have hψ : (ψ : ℝ × ℝ → V) = (φ : ℂ → V) ∘ e.symm := funext fun y ↦ by simp [ψ]
  have h := hηD ψ ψ.contDiff ψ.hasCompactSupport ψ.tsupport_subset
  rw [← volume_preserving_equiv_real_prod.integral_comp measurableEquivRealProd.measurableEmbedding,
    coe_measurableEquivRealProd_eq_equivRealProdCLM, hψ] at h
  rw [← h]
  exact integral_congr_ae (Filter.Eventually.of_forall fun w ↦ congrArg (η (e w))
    (floerLinearization_comp_equivRealProdCLM_symm ω J Ks Kt u _ w).symm)

/-- **Weak cokernel elements of the linearized Floer operator are continuous.** Under the
hypotheses of
`TauCeti.SymplecticForm.memWkpLoc_one_of_forall_integral_apply_floerLinearization_eq_zero`, the
precise representative of `η ∘ e`, which agrees with `η ∘ e` almost everywhere on `Ω`
(`TauCeti.MemLpLoc.ae_eq_preciseRepresentative`), is continuous on `Ω`. -/
theorem continuousOn_preciseRepresentative_of_forall_integral_apply_floerLinearization_eq_zero
    {Ω : Opens ℂ}
    (hJ : ∀ w ∈ Ω, ContDiffAt ℝ 1 (uncurry J) (equivRealProdCLM w, u (equivRealProdCLM w)))
    (hKs : ∀ w ∈ Ω, ContDiffAt ℝ 2 (uncurry Ks) (equivRealProdCLM w, u (equivRealProdCLM w)))
    (hKt : ∀ w ∈ Ω, ContDiffAt ℝ 2 (uncurry Kt) (equivRealProdCLM w, u (equivRealProdCLM w)))
    (hu : ∀ w ∈ Ω, ContDiffAt ℝ 1 u (equivRealProdCLM w))
    (hJ2 : ∀ w ∈ Ω, J (equivRealProdCLM w) (u (equivRealProdCLM w)) *
      J (equivRealProdCLM w) (u (equivRealProdCLM w)) = -1)
    {η : ℝ × ℝ → V →L[ℝ] ℝ} {q : ℝ≥0∞} (hq : 1 < q)
    (hη : MemLpLoc q Ω fun w ↦ η (equivRealProdCLM w))
    (hηD : ∀ ξ : ℝ × ℝ → V, ContDiff ℝ (⊤ : ℕ∞) ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ equivRealProdCLM.symm ⁻¹' Ω →
        ∫ z, η z (ω.floerLinearization J Ks Kt u ξ z) = 0) :
    ContinuousOn (MeasureTheory.preciseRepresentative volume fun w ↦ η (equivRealProdCLM w)) Ω :=
  (memWkpLoc_one_of_forall_integral_apply_floerLinearization_eq_zero hJ hKs hKt hu hJ2 hq hη hηD
    (r := 3) (by norm_num) (by simp)).continuousOn_preciseRepresentative (by norm_num)

end TauCeti.SymplecticForm
