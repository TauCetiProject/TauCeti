/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Annihilator
public import TauCeti.Analysis.Distribution.TestFunction.LinearEquiv
public import TauCeti.Analysis.Sobolev.Local.Morrey.Higher
public import TauCeti.Geometry.Symplectic.Floer.Transversality.Cokernel
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Regularity and vanishing of weak cokernel elements of the linearized Floer operator

Let `u : ℝ × ℝ → V` be a map into a finite-dimensional symplectic vector space `V`, and let
`D_u ξ = ∂ₛξ + J(z, u) ∂ₜξ + C(z) ξ` be the linearized Floer operator at `u`
(`TauCeti.SymplecticForm.floerLinearization`, written in this form by
`TauCeti.SymplecticForm.floerLinearization_eq_add`). The transversality argument of
`TauCeti.Geometry.Symplectic.Floer.Transversality.Cokernel` shows that a `C¹` covector field `η`
annihilating the range of the universal linearized operator vanishes. A cokernel element of a
Sobolev realization of `D_u` is a priori only an `L^q` covector field annihilating `D_u ξ` for every
test map `ξ`, so before that argument applies it has to be shown to be regular. This file proves
that such an `η` is as regular as the data allow, and then that weak cokernel elements of the
universal operator vanish.

**Regularity.** When `J` and `u` are `C^{k+1}` and the Hamiltonians `C^{k+2}`, the coefficient `C`
is `Cᵏ` (`TauCeti.SymplecticForm.contDiffAt_floerLinearizationCoeff`), and `η` is in
`W^{k+1,r}_loc` for every finite `r`
(`TauCeti.SymplecticForm.memWkpLoc_succ_of_forall_integral_apply_floerLinearization_eq_zero`). By
Morrey's embedding its precise representative is `Cᵏ`
(`contDiffOn_preciseRepresentative_of_forall_integral_apply_floerLinearization_eq_zero`, in the
namespace `TauCeti.SymplecticForm`), so `η` agrees almost everywhere with a covector field that is
`Cᵏ` where the data are regular
(`exists_contDiffOn_ae_eq_of_forall_integral_apply_floerLinearization_eq_zero`). The case `k = 1`
gives the `C¹` regularity used by unique continuation in the transversality argument.

The Sobolev classes `W^{k,r}_loc` of Tau Ceti live on `ℂ`, so the regularity statements read the
domain through `e = Complex.equivRealProdCLM : ℂ ≃L[ℝ] ℝ × ℝ`, `s + i t ↦ (s, t)`, which carries
Lebesgue measure to Lebesgue measure: it is Mathlib's measure-preserving
`Complex.measurableEquivRealProd` (`Complex.coe_measurableEquivRealProd_eq_equivRealProdCLM`).
On an open set `Ω ⊆ ℂ`, a test function `φ` on `Ω` gives the test map `ξ = φ ∘ e⁻¹` on
`ℝ × ℝ`, and `D_u ξ (e w) = ∂ₛφ(w) + J_c(w) ∂ₜφ(w) + S_c(w) φ(w)` with `J_c(w) = J(e w, u(e w))`
and `S_c(w) = C(e w)` (`TauCeti.SymplecticForm.floerLinearization_comp_equivRealProdCLM_symm`).
These coefficients are `C^{k+1}` and `Cᵏ`, so `η ∘ e` annihilates a real Cauchy–Riemann operator
with such coefficients, and the regularity of its annihilators
(`TauCeti.memWkpLoc_succ_of_forall_integral_apply_cauchyRiemann_eq_zero`) applies. No inner product
on `V` is needed.

**Vanishing.** Replacing `η` by its `C¹` representative changes none of the integrals against it, so
each of the three transversality arguments of `Cokernel` applies to a locally `L^q` covector field,
`q > 1`, once the data have one more derivative than there: Hamiltonian variations on a core
(`ae_eq_zero_of_integral_floerLinearization_of_integral_floerOperator_add_sub`), variations of a
frozen almost complex structure
(`ae_eq_zero_of_integral_floerLinearization_of_integral_deriv_floerOperator`), and periodic
variations of `J_t` along a Floer trajectory
(`ae_eq_zero_of_integral_floerLinearization_of_setIntegral_deriv_floerOperator`), all in the
namespace `TauCeti.SymplecticForm`. In each case `η = 0` almost everywhere. The surjectivity of
the universal operator on Banach spaces that follows from this, given closed range, is not treated
here.

## Main results

* `TauCeti.SymplecticForm.floerLinearization_comp_equivRealProdCLM_symm`: the linearized Floer
  operator of `φ ∘ e⁻¹` in the coordinate of `ℂ`.
* `TauCeti.SymplecticForm.memWkpLoc_succ_of_forall_integral_apply_floerLinearization_eq_zero`:
  a locally `L^q` (`q > 1`) covector field annihilating `D_u` on test maps is in `W^{k+1,r}_loc`
  for every finite `r`.
* `contDiffOn_preciseRepresentative_of_forall_integral_apply_floerLinearization_eq_zero` and
  `exists_contDiffOn_ae_eq_of_forall_integral_apply_floerLinearization_eq_zero`, in the namespace
  `TauCeti.SymplecticForm`: such a covector field has a `Cᵏ` representative.
* `ae_eq_zero_of_integral_floerLinearization_of_integral_floerOperator_add_sub`,
  `ae_eq_zero_of_integral_floerLinearization_of_integral_deriv_floerOperator` and
  `ae_eq_zero_of_integral_floerLinearization_of_setIntegral_deriv_floerOperator`, in the namespace
  `TauCeti.SymplecticForm`: weak cokernel elements of the universal operator vanish.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Proposition 3.2.1 (the cokernel of the universal operator)
  and Appendix B.4 (Proposition B.4.9, elliptic regularity of weak solutions).
* A. Floer, H. Hofer and D. Salamon, *Transversality in elliptic Morse theory for the symplectic
  action*, Duke Math. J. 80 (1995), 251–292.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Complex Set Function Filter Topology
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

/-- **Weak cokernel elements of the linearized Floer operator are `W^{k+1,r}_loc`.** Let `Ω ⊆ ℂ`
be open and `e = Complex.equivRealProdCLM`. Suppose that over `e '' Ω` the map `u` is `C^{k+1}`, the
almost complex structure `J` is `C^{k+1}` and squares to `-1` along `u`, and the Hamiltonians `Ks`,
`Kt` are `C^{k+2}`. Let `η` be a covector field with `η ∘ e` locally `L^q` on `Ω` for some `q > 1`,
annihilating `D_u ξ` under the pairing `∫ η(·)` for every smooth compactly supported `ξ` supported
over `Ω`. Then `η ∘ e` is in `W^{k+1,r}_loc(Ω)` for every finite `r`. -/
theorem memWkpLoc_succ_of_forall_integral_apply_floerLinearization_eq_zero {Ω : Opens ℂ}
    {k : ℕ}
    (hJ : ∀ w ∈ Ω, ContDiffAt ℝ (k + 1) (uncurry J) (equivRealProdCLM w, u (equivRealProdCLM w)))
    (hKs : ∀ w ∈ Ω,
      ContDiffAt ℝ (k + 2) (uncurry Ks) (equivRealProdCLM w, u (equivRealProdCLM w)))
    (hKt : ∀ w ∈ Ω,
      ContDiffAt ℝ (k + 2) (uncurry Kt) (equivRealProdCLM w, u (equivRealProdCLM w)))
    (hu : ∀ w ∈ Ω, ContDiffAt ℝ (k + 1) u (equivRealProdCLM w))
    (hJ2 : ∀ w ∈ Ω, J (equivRealProdCLM w) (u (equivRealProdCLM w)) *
      J (equivRealProdCLM w) (u (equivRealProdCLM w)) = -1)
    {η : ℝ × ℝ → V →L[ℝ] ℝ} {q : ℝ≥0∞} (hq : 1 < q)
    (hη : MemLpLoc q Ω fun w ↦ η (equivRealProdCLM w))
    (hηD : ∀ ξ : ℝ × ℝ → V, ContDiff ℝ (⊤ : ℕ∞) ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ equivRealProdCLM.symm ⁻¹' Ω →
        ∫ z, η z (ω.floerLinearization J Ks Kt u ξ z) = 0)
    {r : ℝ≥0∞} (hr_top : r ≠ ⊤) :
    MemWkpLoc r Ω (k + 1) fun w ↦ η (equivRealProdCLM w) := by
  set e : ℂ ≃L[ℝ] ℝ × ℝ := equivRealProdCLM
  -- The coefficients of `D_u` in the coordinate of `ℂ`.
  have hg (w : ℂ) (hw : w ∈ Ω) : ContDiffAt ℝ (k + 1) (fun w ↦ (e w, u (e w))) w :=
    e.contDiff.contDiffAt.prodMk ((hu w hw).comp w e.contDiff.contDiffAt)
  have hJc : ContDiffOn ℝ (k + 1) (fun w ↦ J (e w) (u (e w))) Ω := fun w hw ↦
    ((hJ w hw).comp (f := fun w ↦ (e w, u (e w))) w (hg w hw)).contDiffWithinAt
  have hSc : ContDiffOn ℝ k (fun w ↦ ω.floerLinearizationCoeff J Ks Kt u (e w)) Ω := fun w hw ↦
    ((ω.contDiffAt_floerLinearizationCoeff (hJ w hw) (hKs w hw) (hKt w hw) (hu w hw)).comp w
      e.contDiff.contDiffAt).contDiffWithinAt
  refine memWkpLoc_succ_of_forall_integral_apply_cauchyRiemann_eq_zero hJc hSc hJ2 hq hη
    (fun φ ↦ ?_) hr_top
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

/-- **Weak cokernel elements of the linearized Floer operator are `Cᵏ`.** Under the hypotheses of
`TauCeti.SymplecticForm.memWkpLoc_succ_of_forall_integral_apply_floerLinearization_eq_zero`, the
precise representative of `η ∘ e`, which agrees with `η ∘ e` almost everywhere on `Ω`
(`TauCeti.MemLpLoc.ae_eq_preciseRepresentative`), is `Cᵏ` on `Ω`; for `k = 0` it is continuous. -/
theorem contDiffOn_preciseRepresentative_of_forall_integral_apply_floerLinearization_eq_zero
    {Ω : Opens ℂ} {k : ℕ}
    (hJ : ∀ w ∈ Ω, ContDiffAt ℝ (k + 1) (uncurry J) (equivRealProdCLM w, u (equivRealProdCLM w)))
    (hKs : ∀ w ∈ Ω,
      ContDiffAt ℝ (k + 2) (uncurry Ks) (equivRealProdCLM w, u (equivRealProdCLM w)))
    (hKt : ∀ w ∈ Ω,
      ContDiffAt ℝ (k + 2) (uncurry Kt) (equivRealProdCLM w, u (equivRealProdCLM w)))
    (hu : ∀ w ∈ Ω, ContDiffAt ℝ (k + 1) u (equivRealProdCLM w))
    (hJ2 : ∀ w ∈ Ω, J (equivRealProdCLM w) (u (equivRealProdCLM w)) *
      J (equivRealProdCLM w) (u (equivRealProdCLM w)) = -1)
    {η : ℝ × ℝ → V →L[ℝ] ℝ} {q : ℝ≥0∞} (hq : 1 < q)
    (hη : MemLpLoc q Ω fun w ↦ η (equivRealProdCLM w))
    (hηD : ∀ ξ : ℝ × ℝ → V, ContDiff ℝ (⊤ : ℕ∞) ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ equivRealProdCLM.symm ⁻¹' Ω →
        ∫ z, η z (ω.floerLinearization J Ks Kt u ξ z) = 0) :
    ContDiffOn ℝ k (MeasureTheory.preciseRepresentative volume fun w ↦ η (equivRealProdCLM w))
      Ω := by
  have hW := memWkpLoc_succ_of_forall_integral_apply_floerLinearization_eq_zero hJ hKs hKt hu hJ2
    hq hη hηD (r := 3) (by simp)
  have h3 : (2 : ℝ≥0∞) < 3 := by norm_num
  exact hW.contDiffOn_of_continuousOn h3
    ((hW.of_le le_add_self).continuousOn_preciseRepresentative h3)
    (hW.memLpLoc.ae_eq_preciseRepresentative (by norm_num))

/-- **Weak cokernel elements agree almost everywhere with `Cᵏ` fields.** Let `Ω ⊆ ℝ × ℝ` be open.
Suppose that over `Ω` the map `u` is `C^{k+1}`, the almost complex structure `J` is `C^{k+1}` and
squares to `-1` along `u`, and the Hamiltonians `Ks`, `Kt` are `C^{k+2}`. Let `η` be a locally `L^q`
covector field on `Ω`, `q > 1`, annihilating `D_u ξ` under the pairing `∫ η(·)` for every smooth
compactly supported `ξ` supported in `Ω`. Then `η` agrees almost everywhere on `ℝ × ℝ` with a
covector field that is `Cᵏ` on `Ω`. -/
theorem exists_contDiffOn_ae_eq_of_forall_integral_apply_floerLinearization_eq_zero
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) {k : ℕ}
    (hJ : ∀ z ∈ Ω, ContDiffAt ℝ (k + 1) (uncurry J) (z, u z))
    (hKs : ∀ z ∈ Ω, ContDiffAt ℝ (k + 2) (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ Ω, ContDiffAt ℝ (k + 2) (uncurry Kt) (z, u z))
    (hu : ∀ z ∈ Ω, ContDiffAt ℝ (k + 1) u z) (hJ2 : ∀ z ∈ Ω, J z (u z) * J z (u z) = -1)
    {η : ℝ × ℝ → V →L[ℝ] ℝ} {q : ℝ≥0∞} (hq : 1 < q) (hη : MemLpLoc q Ω η)
    (hηD : ∀ ξ : ℝ × ℝ → V, ContDiff ℝ (⊤ : ℕ∞) ξ → HasCompactSupport ξ → tsupport ξ ⊆ Ω →
      ∫ z, η z (ω.floerLinearization J Ks Kt u ξ z) = 0) :
    ∃ η' : ℝ × ℝ → V →L[ℝ] ℝ, ContDiffOn ℝ k η' Ω ∧ η =ᵐ[volume] η' := by
  classical
  set e : ℂ ≃L[ℝ] ℝ × ℝ := equivRealProdCLM
  set Ωc : Opens ℂ := ⟨e ⁻¹' Ω, hΩ.preimage e.continuous⟩
  -- Instance search does not see `volume` on `ℝ × ℝ` as a product measure.
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  have hηc : MemLpLoc q Ωc fun w ↦ η (e w) := (e.memLpLoc_comp_right_iff volume volume).2 hη
  have hg := contDiffOn_preciseRepresentative_of_forall_integral_apply_floerLinearization_eq_zero
    (Ω := Ωc) (fun w hw ↦ hJ _ hw) (fun w hw ↦ hKs _ hw) (fun w hw ↦ hKt _ hw) (fun w hw ↦ hu _ hw)
    (fun w hw ↦ hJ2 _ hw) hq hηc fun ξ hξ hξc hξΩ ↦
      hηD ξ hξ hξc (hξΩ.trans fun z hz ↦ by simpa [Ωc, e] using hz)
  set g := MeasureTheory.preciseRepresentative volume fun w ↦ η (e w)
  -- On `Ω` the field is the precise representative read through `e⁻¹`, elsewhere it is `η`.
  refine ⟨fun z ↦ if z ∈ Ω then g (e.symm z) else η z, ?_, ?_⟩
  · refine (hg.comp e.symm.contDiff.contDiffOn fun z hz ↦ ?_).congr fun z hz ↦ by simp [hz]
    simpa [Ωc, e] using hz
  · -- `η ∘ e = g` almost everywhere on `e⁻¹ Ω`, read on `ℝ × ℝ` through `e⁻¹`.
    have hae : ∀ᵐ w ∂volume, w ∈ Ωc → η (e w) = g w :=
      (ae_restrict_iff' Ωc.isOpen.measurableSet).1
        (hηc.ae_eq_preciseRepresentative hq.le)
    have he : MeasurePreserving e.symm volume volume :=
      Complex.measurePreserving_equivRealProdCLM_symm
    filter_upwards [he.quasiMeasurePreserving.ae hae] with z hz
    rw [e.apply_symm_apply] at hz
    split_ifs with hzΩ
    · exact hz (by simpa only [Ωc, Opens.mem_mk, Set.mem_preimage, e.apply_symm_apply] using hzΩ)
    · rfl

section Vanishing

/-! ### Weak cokernel elements of the universal operator vanish

The three transversality arguments of `TauCeti.Geometry.Symplectic.Floer.Transversality.Cokernel`
take a `C¹` covector field. Applied to the `C¹` representative of a weak cokernel element, they show
that a locally `L^q` covector field annihilating the range of the universal linearized operator
vanishes almost everywhere, once the data have one more derivative than the classical statements
ask for. -/

variable {U : Set (ℝ × ℝ)} {η : ℝ × ℝ → V →L[ℝ] ℝ} {q : ℝ≥0∞}

omit [FiniteDimensional ℝ V] in
/-- Integrals against two covector fields that agree almost everywhere agree. -/
private theorem integral_apply_congr {η' : ℝ × ℝ → V →L[ℝ] ℝ} {μ : Measure (ℝ × ℝ)}
    (hae : η =ᵐ[μ] η') (X : ℝ × ℝ → V) : ∫ z, η' z (X z) ∂μ = ∫ z, η z (X z) ∂μ :=
  integral_congr_ae (hae.mono fun z hz ↦ congrArg (fun f : V →L[ℝ] ℝ ↦ f (X z)) hz.symm)

/-- The smoothness orders `1 + 1` and `1 + 2` of the regularity results at `k = 1`. -/
private theorem one_add_one_eq_two' : ((1 : ℕ) : WithTop ℕ∞) + 1 = 2 := by norm_num

private theorem one_add_two_eq_three' : ((1 : ℕ) : WithTop ℕ∞) + 2 = 3 := by norm_num

/-- **Hamiltonian variations on a core kill the weak cokernel of the universal operator.** Let `J`
be `C²` and the Hamiltonians `K_s`, `K_t` be `C³` near the graph of a map `u`, `C²` over a connected
open set `Ω`, with `J(z, u z)² = -1` on `Ω`. Let `η` be a locally `L^q` covector field on `Ω`,
`q > 1`, annihilating `D_u ξ` for every smooth test map `ξ` compactly supported in `Ω`, and
annihilating the change of the Floer operator under every smooth compactly supported variation `δK`
of `K_s` supported in a neighbourhood `W` of the graph of `u` over a nonempty open set `U ⊆ Ω`. Then
`η = 0` almost everywhere on `Ω`. This is the weak form of
`TauCeti.SymplecticForm.eqOn_zero_of_integral_floerLinearization_of_integral_floerOperator_add_sub`.
-/
theorem ae_eq_zero_of_integral_floerLinearization_of_integral_floerOperator_add_sub
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hJ : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry J) (z, u z))
    (hJJ : ∀ z ∈ Ω, J z (u z) ∘L J z (u z) = -ContinuousLinearMap.id ℝ V)
    (hKs : ∀ z ∈ Ω, ContDiffAt ℝ 3 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ Ω, ContDiffAt ℝ 3 (uncurry Kt) (z, u z)) (hu : ∀ z ∈ Ω, ContDiffAt ℝ 2 u z)
    (hq : 1 < q) (hη : MemLpLoc q Ω η)
    (hD : ∀ ξ : ℝ × ℝ → V, ContDiff ℝ (⊤ : ℕ∞) ξ → HasCompactSupport ξ → tsupport ξ ⊆ Ω →
      ∫ z, η z (ω.floerLinearization J Ks Kt u ξ z) = 0)
    (hU : IsOpen U) (hUne : U.Nonempty) (hUΩ : U ⊆ Ω) {W : Set ((ℝ × ℝ) × V)}
    (hW : ∀ z ∈ U, W ∈ 𝓝 (z, u z))
    (hK : ∀ δK : ℝ × ℝ → V → ℝ, ContDiff ℝ (⊤ : ℕ∞) (uncurry δK) →
      HasCompactSupport (uncurry δK) → tsupport (uncurry δK) ⊆ W →
        ∫ z, η z (ω.floerOperator J (fun w y ↦ Ks w y + δK w y) Kt u z -
          ω.floerOperator J Ks Kt u z) = 0) :
    η =ᵐ[volume.restrict Ω] 0 := by
  obtain ⟨η', hη', hae⟩ :=
    exists_contDiffOn_ae_eq_of_forall_integral_apply_floerLinearization_eq_zero hΩ (k := 1)
      (one_add_one_eq_two' ▸ hJ) (one_add_two_eq_three' ▸ hKs) (one_add_two_eq_three' ▸ hKt)
      (one_add_one_eq_two' ▸ hu)
    (fun z hz ↦ by rw [ContinuousLinearMap.mul_def, hJJ z hz, ContinuousLinearMap.one_def]) hq hη hD
  have h0 := eqOn_zero_of_integral_floerLinearization_of_integral_floerOperator_add_sub hΩ hΩc
    (fun z hz ↦ (hJ z hz).of_le one_le_two) hJJ (fun z hz ↦ (hKs z hz).of_le (by norm_num))
    (fun z hz ↦ (hKt z hz).of_le (by norm_num))
    (fun z hz ↦ ((hu z hz).of_le one_le_two).contDiffWithinAt) (by simpa using hη')
    (fun ξ hξ hξc hξΩ ↦ (integral_apply_congr hae _).trans (hD ξ hξ hξc hξΩ)) hU hUne hUΩ hW
    fun δK h₁ h₂ h₃ ↦ (integral_apply_congr hae _).trans (hK δK h₁ h₂ h₃)
  filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem hΩ.measurableSet] with z hz hzΩ
  rw [hz, h0 hzΩ, Pi.zero_apply]

/-- **Variations of a frozen almost complex structure kill the weak cokernel of the universal
operator.** Let `J` be a `Cⁿ` family of complex structures preserving `ω`, with `2 ≤ n`, frozen in
the sense that it does not depend on the domain point, and let the Hamiltonians `K_s`, `K_t` be `C³`
near the graph of a map `u`, `C²` over a connected open set `Ω`. Let `η` be a locally `L^q`
covector field on `Ω`, `q > 1`, annihilating `D_u ξ` for every smooth test map `ξ` compactly
supported in `Ω`. Suppose that on a nonempty open set `U ⊆ Ω`, every point `z` is an injective
point of `u`, with `J` tamed by `ω` at `u z` and `∂ₜu - X_{K_t} ≠ 0` at `z`, and that `η`
annihilates the derivative of the Floer operator along `J + τ Y` for every compactly supported `Cⁿ`
field `Y` of compatible variations of `J` supported in a neighbourhood `W` of `u(U)`. Then `η = 0`
almost everywhere on `Ω`. This is the weak form of
`TauCeti.SymplecticForm.eqOn_zero_of_integral_floerLinearization_of_integral_deriv_floerOperator`.
-/
theorem ae_eq_zero_of_integral_floerLinearization_of_integral_deriv_floerOperator {n : ℕ∞}
    {J : V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ n fun x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap) (hn : 2 ≤ n)
    (hJω : ∀ x, ω.Invariant (J x)) {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hKs : ∀ z ∈ Ω, ContDiffAt ℝ 3 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ Ω, ContDiffAt ℝ 3 (uncurry Kt) (z, u z)) (hu : ∀ z ∈ Ω, ContDiffAt ℝ 2 u z)
    (hq : 1 < q) (hη : MemLpLoc q Ω η)
    (hD : ∀ ξ : ℝ × ℝ → V, ContDiff ℝ (⊤ : ℕ∞) ξ → HasCompactSupport ξ → tsupport ξ ⊆ Ω →
      ∫ z, η z (ω.floerLinearization (fun _ x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap)
        Ks Kt u ξ z) = 0)
    (hU : IsOpen U) (hUne : U.Nonempty) (hUΩ : U ⊆ Ω) (hJ₀ : ∀ z ∈ U, ω.Tames (J (u z)))
    (hinj : ∀ z ∈ U, (𝓝 (u z)).comap u ≤ 𝓝 z)
    (hξ₀ : ∀ z ∈ U, fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z) ≠ 0)
    {W : Set V} (hW : ∀ z ∈ U, W ∈ 𝓝 (u z))
    (hY : ∀ Y : V → V →L[ℝ] V, ContDiff ℝ n Y → HasCompactSupport Y → tsupport Y ⊆ W →
      (∀ x, (Y x : Module.End ℝ V) ∈ ω.compatibleTangentSpace (J x)) →
        ∫ z, η z (deriv (fun τ : ℝ ↦ ω.floerOperator
          (fun _ x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap + τ • Y x) Ks Kt u z)
            0) = 0) :
    η =ᵐ[volume.restrict Ω] 0 := by
  have hJ2 : ContDiff ℝ 2
      (uncurry fun (_ : ℝ × ℝ) x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap) :=
    (hJ.of_le (WithTop.coe_le_coe.2 hn)).comp contDiff_snd
  obtain ⟨η', hη', hae⟩ :=
    exists_contDiffOn_ae_eq_of_forall_integral_apply_floerLinearization_eq_zero hΩ (k := 1)
      (fun _ _ ↦ (one_add_one_eq_two' ▸ hJ2).contDiffAt) (one_add_two_eq_three' ▸ hKs)
      (one_add_two_eq_three' ▸ hKt) (one_add_one_eq_two' ▸ hu) (fun z _ ↦ by ext v; simp) hq hη
      hD
  have h0 := eqOn_zero_of_integral_floerLinearization_of_integral_deriv_floerOperator hJ
    (one_le_two.trans hn) hJω hΩ hΩc (fun z hz ↦ (hKs z hz).of_le (by norm_num))
    (fun z hz ↦ (hKt z hz).of_le (by norm_num))
    (fun z hz ↦ ((hu z hz).of_le one_le_two).contDiffWithinAt) (by simpa using hη')
    (fun ξ hξ hξc hξΩ ↦ (integral_apply_congr hae _).trans (hD ξ hξ hξc hξΩ)) hU hUne hUΩ hJ₀
    hinj hξ₀ hW fun Y h₁ h₂ h₃ h₄ ↦ (integral_apply_congr hae _).trans (hY Y h₁ h₂ h₃ h₄)
  filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem hΩ.measurableSet] with z hz hzΩ
  rw [hz, h0 hzΩ, Pi.zero_apply]

/-- **Periodic variations of `J_t` kill the weak cokernel of the universal operator along a Floer
trajectory** (Floer, Hofer and Salamon). Let `J (t, x)` be a `Cⁿ` family of complex structures
preserving `ω`, with `2 ≤ n`, of period one in the time `t` and tamed by `ω` along `u`, and let `u`
be a nonstationary `C²` solution of the Floer equation `∂ₛu + J_t(u)(∂ₜu - X_{H_t}(u)) = 0` for a
`C³` Hamiltonian `H`. Suppose that `u(s, t)` tends to `xm(t₀)` and `xp(t₀)`, for continuous loops
`xm` and `xp`, as `s → -∞` and `s → +∞` and `t → t₀`. Let `η` be a locally `L^q` covector field,
`q > 1`, annihilating `D_u ξ` for every smooth compactly supported test map `ξ`, and annihilating,
over the strip `ℝ × (0, 1)`, the derivative of the Floer operator along `J + τ Y` for every `Cⁿ`
field `Y` of period one in time, vanishing for `x` outside a compact set, with `Y (t, x)` in the
compatible tangent space of `J (t, x)`. Then `η = 0` almost everywhere. This is the weak form of
`TauCeti.SymplecticForm.eq_zero_of_integral_floerLinearization_of_setIntegral_deriv_floerOperator`.
-/
theorem ae_eq_zero_of_integral_floerLinearization_of_setIntegral_deriv_floerOperator {n : ℕ∞}
    {J : ℝ × V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ n fun p ↦ LinearMap.toContinuousLinearMap (J p).toLinearMap) (hn : 2 ≤ n)
    (hJω : ∀ p, ω.Invariant (J p)) (hJper : ∀ t x, J (t + 1, x) = J (t, x))
    (hJ₀ : ∀ z, ω.Tames (J (z.2, u z))) {H : ℝ → V → ℝ} (hH : ContDiff ℝ 3 (uncurry H))
    (hu : ContDiff ℝ 2 u)
    (hF : ∀ z, ω.floerOperator
      (fun z x ↦ LinearMap.toContinuousLinearMap (J (z.2, x)).toLinearMap) (fun _ _ ↦ 0)
        (fun z ↦ H z.2) u z = 0)
    (hne : ∃ z, fderiv ℝ u z stdComplexLineReal ≠ 0) {xm xp : ℝ → V} (hxm : Continuous xm)
    (hxp : Continuous xp) (hm : ∀ t, Tendsto u (atBot ×ˢ 𝓝 t) (𝓝 (xm t)))
    (hp : ∀ t, Tendsto u (atTop ×ˢ 𝓝 t) (𝓝 (xp t))) (hq : 1 < q) (hη : MemLpLoc q univ η)
    (hD : ∀ ξ : ℝ × ℝ → V, ContDiff ℝ (⊤ : ℕ∞) ξ → HasCompactSupport ξ →
      ∫ z, η z (ω.floerLinearization
        (fun z x ↦ LinearMap.toContinuousLinearMap (J (z.2, x)).toLinearMap) (fun _ _ ↦ 0)
          (fun z ↦ H z.2) u ξ z) = 0)
    (hY : ∀ Y : ℝ × V → V →L[ℝ] V, ContDiff ℝ n Y → (∀ t x, Y (t + 1, x) = Y (t, x)) →
      (∀ᶠ p in comap Prod.snd (cocompact V), Y p = 0) →
      (∀ p, (Y p : Module.End ℝ V) ∈ ω.compatibleTangentSpace (J p)) →
        ∫ z in univ ×ˢ Ioo 0 1, η z (deriv (fun τ : ℝ ↦ ω.floerOperator
          (fun z x ↦ LinearMap.toContinuousLinearMap (J (z.2, x)).toLinearMap + τ • Y (z.2, x))
            (fun _ _ ↦ 0) (fun z ↦ H z.2) u z) 0) = 0) :
    η =ᵐ[volume] 0 := by
  have hg : ContDiff ℝ 3 fun p : (ℝ × ℝ) × V ↦ (p.1.2, p.2) :=
    (contDiff_snd.comp contDiff_fst).prodMk contDiff_snd
  have hJ2 : ContDiff ℝ 2
      (uncurry fun (z : ℝ × ℝ) x ↦ LinearMap.toContinuousLinearMap (J (z.2, x)).toLinearMap) :=
    (hJ.of_le (WithTop.coe_le_coe.2 hn)).comp (hg.of_le (by norm_num))
  have hH' : ContDiff ℝ 3 (uncurry fun (z : ℝ × ℝ) ↦ H z.2) := hH.comp hg
  obtain ⟨η', hη', hae⟩ :=
    exists_contDiffOn_ae_eq_of_forall_integral_apply_floerLinearization_eq_zero isOpen_univ
      (k := 1) (fun _ _ ↦ (one_add_one_eq_two' ▸ hJ2).contDiffAt) (fun _ _ ↦ contDiffAt_const)
      (fun _ _ ↦ (one_add_two_eq_three' ▸ hH').contDiffAt)
      (fun _ _ ↦ (one_add_one_eq_two' ▸ hu).contDiffAt) (fun z _ ↦ by ext v; simp) hq hη
      fun ξ hξ hξc _ ↦ hD ξ hξ hξc
  have h0 := eq_zero_of_integral_floerLinearization_of_setIntegral_deriv_floerOperator hJ
    (one_le_two.trans hn) hJω hJper hJ₀ (hH.of_le (by norm_num)) hu hF hne hxm hxp hm hp
    (contDiffOn_univ.1 (by simpa using hη'))
    (fun ξ hξ hξc ↦ (integral_apply_congr hae _).trans (hD ξ hξ hξc))
    fun Y h₁ h₂ h₃ h₄ ↦ (integral_apply_congr (ae_restrict_of_ae hae) _).trans (hY Y h₁ h₂ h₃ h₄)
  exact hae.mono fun z hz ↦ by rw [hz, h0, Pi.zero_apply]

end Vanishing

end TauCeti.SymplecticForm
