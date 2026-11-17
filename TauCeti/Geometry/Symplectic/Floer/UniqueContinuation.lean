/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation.VariableStructure
public import TauCeti.Geometry.Symplectic.Floer.Linearization

/-!
# Unique continuation for the linearized Floer operator

Let `(V, ω)` be a symplectic vector space and `u : ℝ × ℝ → V` a `C¹` map, with domain-dependent
endomorphism fields `J(z, x)` and Hamiltonian perturbation `K = K_s ds + K_t dt`. The linearized
Floer operator at `u` (`TauCeti.SymplecticForm.floerLinearization`) is

`D_u ξ = ∂ₛξ + J(z, u z) ∂ₜξ + C(z) ξ`

(`TauCeti.SymplecticForm.floerLinearization_eq_add`), with a zeroth-order coefficient
`C = TauCeti.SymplecticForm.floerLinearizationCoeff` which is continuous where `J` is `C¹`, the
Hamiltonians are `C²` and `u` is `C¹`. Where `J(z, u z)` is a complex structure, this is a linear
Cauchy–Riemann operator with the variable complex structure `z ↦ J(z, u z)`, so its solutions
have the zero structure of holomorphic maps
(`TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation.VariableStructure`). On a connected
open set `Ω ⊆ ℝ × ℝ`, a `C¹` solution `ξ` of `D_u ξ = 0`:

* vanishes on `Ω` if it vanishes on a nonempty open subset of `Ω`
  (`TauCeti.SymplecticForm.eqOn_zero_of_floerLinearization_eq_zero_of_eqOn_zero`);
* vanishes on `Ω` if it vanishes to infinite order at one point of `Ω`
  (`TauCeti.SymplecticForm.eqOn_zero_of_floerLinearization_eq_zero_of_forall_isBigO`);
* otherwise has isolated zeros in `Ω`
  (`TauCeti.SymplecticForm.setOf_ne_zero_mem_codiscreteWithin_of_floerLinearization_eq_zero`).

In the transversality argument for Floer moduli spaces, an element of the cokernel of the
universal linearized operator is first shown to vanish on an open set: on the compact core of
the domain, where localized Hamiltonian variations detect it
(`TauCeti.SymplecticForm.eqOn_zero_of_forall_integral_apply_floerOperator_add_sub_eq_zero`), or
near injective points, where variations of the almost complex structure detect it
(`TauCeti.SymplecticForm.eq_zero_of_integral_apply_deriv_floerOperator_eq_zero`). Unique
continuation for the equation it satisfies then makes it vanish on the whole connected domain.
The variable-structure theorems themselves apply to every operator `∂ₛ + J ∂ₜ + C` with a `C¹`
field of complex structures `J`, so they also cover operators whose leading part is
`∂ₛ - J ∂ₜ`, the Cauchy–Riemann operator of the complex structure `-J`.

The proofs read `ℝ × ℝ` as `ℂ` through `Complex.equivRealProdCLM`, under which `∂ₛ` and `∂ₜ` are
the derivatives in the directions `1` and `i`
(`TauCeti.fderiv_comp_equivRealProdCLM_one`, `TauCeti.fderiv_comp_equivRealProdCLM_I`).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.3 (unique continuation) and Sections 3.2 and 8.1 (transversality).
* A. Floer, H. Hofer and D. Salamon, *Transversality in elliptic Morse theory for the symplectic
  action*, Duke Math. J. 80 (1995), 251–292.
-/

public section

open Asymptotics Complex Filter Function MeasureTheory Set Topology

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ}
  {u ξ : ℝ × ℝ → V} {Ω : Set (ℝ × ℝ)}

/-- In the complex coordinate `z = Complex.equivRealProdCLM w`, a solution of `D_u ξ = 0` on a
connected open set `Ω` solves the linear Cauchy–Riemann equation for the structure `J(z, u z)` and
the coefficient `floerLinearizationCoeff` on the connected open set `e ⁻¹' Ω`, with the regularity
the variable-structure theorems ask for. -/
private theorem floerLinearization_eq_zero_complexCoordinate (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω)
    (hJ : ∀ z ∈ Ω, ContDiffAt ℝ 1 (fun p : (ℝ × ℝ) × V ↦ J p.1 p.2) (z, u z))
    (hJJ : ∀ z ∈ Ω, J z (u z) ∘L J z (u z) = -ContinuousLinearMap.id ℝ V)
    (hKs : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiffOn ℝ 1 u Ω)
    (hξ : ContDiffOn ℝ 1 ξ Ω) (hD : ∀ z ∈ Ω, ω.floerLinearization J Ks Kt u ξ z = 0) :
    let e := Complex.equivRealProdCLM
    IsOpen (e ⁻¹' Ω) ∧ IsPreconnected (e ⁻¹' Ω) ∧
      ContDiffOn ℝ 1 (fun w ↦ J (e w) (u (e w))) (e ⁻¹' Ω) ∧
      (∀ w ∈ e ⁻¹' Ω, J (e w) (u (e w)) ∘L J (e w) (u (e w)) = -ContinuousLinearMap.id ℝ V) ∧
      ContDiffOn ℝ 1 (ξ ∘ e) (e ⁻¹' Ω) ∧
      AEStronglyMeasurable (fun w ↦ ω.floerLinearizationCoeff J Ks Kt u (e w))
        (volume.restrict (e ⁻¹' Ω)) ∧
      (∀ w ∈ e ⁻¹' Ω, ∃ M, ∀ᶠ w' in 𝓝 w, ‖ω.floerLinearizationCoeff J Ks Kt u (e w')‖ ≤ M) ∧
      ∀ w ∈ e ⁻¹' Ω, fderiv ℝ (ξ ∘ e) w 1 + J (e w) (u (e w)) (fderiv ℝ (ξ ∘ e) w I) +
        ω.floerLinearizationCoeff J Ks Kt u (e w) ((ξ ∘ e) w) = 0 := by
  intro e
  have hΩ' : IsOpen (e ⁻¹' Ω) := hΩ.preimage e.continuous
  have hC : ContinuousOn (fun w ↦ ω.floerLinearizationCoeff J Ks Kt u (e w)) (e ⁻¹' Ω) :=
    (ω.continuousOn_floerLinearizationCoeff hJ hKs hKt
      fun z hz ↦ hu.contDiffAt (hΩ.mem_nhds hz)).comp e.continuous.continuousOn
      (mapsTo_preimage _ _)
  refine ⟨hΩ', (e.toHomeomorph.isPreconnected_preimage).2 hΩc, fun w hw ↦ ?_,
    fun w hw ↦ hJJ (e w) hw, hξ.comp_continuousLinearMap (e : ℂ →L[ℝ] ℝ × ℝ),
    hC.aestronglyMeasurable hΩ'.measurableSet, fun w hw ↦ ?_, fun w hw ↦ ?_⟩
  · have hgraph : ContDiffAt ℝ 1 (fun w ↦ (e w, u (e w))) w :=
      e.contDiff.contDiffAt.prodMk
        ((hu.contDiffAt (hΩ.mem_nhds hw)).comp w e.contDiff.contDiffAt)
    exact ((hJ (e w) hw).comp w hgraph).contDiffWithinAt
  · exact ⟨_, ((hC.continuousAt (hΩ'.mem_nhds hw)).norm.eventually
      (gt_mem_nhds (lt_add_one _))).mono fun _ h ↦ h.le⟩
  · rw [fderiv_comp_equivRealProdCLM_one, fderiv_comp_equivRealProdCLM_I, comp_apply,
      ← floerLinearization_eq_add]
    exact hD (e w) hw

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- A map vanishing on `Ω` in the complex coordinate `Complex.equivRealProdCLM` vanishes on `Ω`. -/
private theorem eqOn_zero_of_eqOn_zero_comp_equivRealProdCLM
    (h : EqOn (ξ ∘ Complex.equivRealProdCLM) 0 (Complex.equivRealProdCLM ⁻¹' Ω)) :
    EqOn ξ 0 Ω := fun z hz ↦ by
  simpa using h (show Complex.equivRealProdCLM.symm z ∈ _ by simpa using hz)

/-- **Unique continuation for the linearized Floer operator.** Let `J` be `C¹` and the
Hamiltonians `K_s`, `K_t` be `C²` near the graph of a `C¹` map `u` over a connected open set
`Ω ⊆ ℝ × ℝ`, with `J(z, u z)² = -1` on `Ω`. A `C¹` solution `ξ` of `D_u ξ = 0` on `Ω` that
vanishes on a nonempty open subset of `Ω` vanishes on `Ω`. -/
theorem eqOn_zero_of_floerLinearization_eq_zero_of_eqOn_zero (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω)
    (hJ : ∀ z ∈ Ω, ContDiffAt ℝ 1 (fun p : (ℝ × ℝ) × V ↦ J p.1 p.2) (z, u z))
    (hJJ : ∀ z ∈ Ω, J z (u z) ∘L J z (u z) = -ContinuousLinearMap.id ℝ V)
    (hKs : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiffOn ℝ 1 u Ω)
    (hξ : ContDiffOn ℝ 1 ξ Ω) (hD : ∀ z ∈ Ω, ω.floerLinearization J Ks Kt u ξ z = 0)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hUne : U.Nonempty) (hUΩ : U ⊆ Ω) (h₀ : EqOn ξ 0 U) :
    EqOn ξ 0 Ω := by
  obtain ⟨hΩ', hΩc', hJ', hJJ', hξ', hCm, hCb, heq⟩ :=
    floerLinearization_eq_zero_complexCoordinate hΩ hΩc hJ hJJ hKs hKt hu hξ hD
  set e := Complex.equivRealProdCLM
  obtain ⟨z₁, hz₁⟩ := hUne
  exact eqOn_zero_of_eqOn_zero_comp_equivRealProdCLM <|
    eqOn_zero_of_contDiffOn_of_eqOn_zero_of_complexStructure hΩ' hΩc' hJ' hJJ' hξ' hCm hCb heq
      (hU.preimage e.continuous) ⟨e.symm z₁, by simpa using hz₁⟩ (preimage_mono hUΩ)
      fun w hw ↦ h₀ hw

/-- **Unique continuation from a zero of infinite order for the linearized Floer operator.** Let
`J` be `C¹` and the Hamiltonians `K_s`, `K_t` be `C²` near the graph of a `C¹` map `u` over a
connected open set `Ω ⊆ ℝ × ℝ`, with `J(z, u z)² = -1` on `Ω`. A `C¹` solution `ξ` of
`D_u ξ = 0` on `Ω` with `ξ = O(‖z - z₀‖ⁿ)` near one point `z₀ ∈ Ω` for every `n` vanishes on
`Ω`. -/
theorem eqOn_zero_of_floerLinearization_eq_zero_of_forall_isBigO (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω)
    (hJ : ∀ z ∈ Ω, ContDiffAt ℝ 1 (fun p : (ℝ × ℝ) × V ↦ J p.1 p.2) (z, u z))
    (hJJ : ∀ z ∈ Ω, J z (u z) ∘L J z (u z) = -ContinuousLinearMap.id ℝ V)
    (hKs : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiffOn ℝ 1 u Ω)
    (hξ : ContDiffOn ℝ 1 ξ Ω) (hD : ∀ z ∈ Ω, ω.floerLinearization J Ks Kt u ξ z = 0)
    {z₀ : ℝ × ℝ} (hz₀ : z₀ ∈ Ω) (h₀ : ∀ n : ℕ, ξ =O[𝓝 z₀] fun z ↦ ‖z - z₀‖ ^ n) :
    EqOn ξ 0 Ω := by
  obtain ⟨hΩ', hΩc', hJ', hJJ', hξ', hCm, hCb, heq⟩ :=
    floerLinearization_eq_zero_complexCoordinate hΩ hΩc hJ hJJ hKs hKt hu hξ hD
  set e := Complex.equivRealProdCLM
  -- In the complex coordinate the vanishing order is measured by `‖e w - e w₀‖ ≤ ‖e‖ ‖w - w₀‖`.
  have hO (n : ℕ) : (ξ ∘ e) =O[𝓝 (e.symm z₀)] fun w ↦ (w - e.symm z₀) ^ n := by
    have h := (h₀ n).comp_tendsto
      ((e.continuous.tendsto (e.symm z₀)).trans_eq (by rw [e.apply_symm_apply]))
    refine h.trans (IsBigO.of_bound (‖(e : ℂ →L[ℝ] ℝ × ℝ)‖ ^ n) (Eventually.of_forall fun w ↦ ?_))
    have hw : e w - z₀ = e (w - e.symm z₀) := by simp
    simp only [comp_apply, hw, norm_pow, norm_norm, ← mul_pow]
    gcongr
    exact (e : ℂ →L[ℝ] ℝ × ℝ).le_opNorm _
  exact eqOn_zero_of_eqOn_zero_comp_equivRealProdCLM <|
    eqOn_zero_of_contDiffOn_of_forall_isBigO_of_complexStructure hΩ' hΩc' hJ' hJJ' hξ' hCm hCb
      heq (show e.symm z₀ ∈ e ⁻¹' Ω by rwa [mem_preimage, e.apply_symm_apply]) hO

/-- **Isolated zeros of solutions of the linearized Floer operator.** Let `J` be `C¹` and the
Hamiltonians `K_s`, `K_t` be `C²` near the graph of a `C¹` map `u` over a connected open set
`Ω ⊆ ℝ × ℝ`, with `J(z, u z)² = -1` on `Ω`. The zeros of a `C¹` solution `ξ` of `D_u ξ = 0` on
`Ω` that is not identically zero on `Ω` form a discrete subset of `Ω`. -/
theorem setOf_ne_zero_mem_codiscreteWithin_of_floerLinearization_eq_zero (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω)
    (hJ : ∀ z ∈ Ω, ContDiffAt ℝ 1 (fun p : (ℝ × ℝ) × V ↦ J p.1 p.2) (z, u z))
    (hJJ : ∀ z ∈ Ω, J z (u z) ∘L J z (u z) = -ContinuousLinearMap.id ℝ V)
    (hKs : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiffOn ℝ 1 u Ω)
    (hξ : ContDiffOn ℝ 1 ξ Ω) (hD : ∀ z ∈ Ω, ω.floerLinearization J Ks Kt u ξ z = 0)
    (hne : ∃ z ∈ Ω, ξ z ≠ 0) : {z | ξ z ≠ 0} ∈ codiscreteWithin Ω := by
  obtain ⟨hΩ', hΩc', hJ', hJJ', hξ', hCm, hCb, heq⟩ :=
    floerLinearization_eq_zero_complexCoordinate hΩ hΩc hJ hJJ hKs hKt hu hξ hD
  set e := Complex.equivRealProdCLM
  obtain ⟨z₁, hz₁, hξz₁⟩ := hne
  have h := setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn_of_complexStructure hΩ' hΩc' hJ'
    hJJ' hξ' hCm hCb heq ⟨e.symm z₁, by simpa using hz₁, by simpa using hξz₁⟩
  -- Transport the codiscrete set back along the homeomorphism `e`.
  have := (e.toHomeomorph.isEmbedding.image_mem_codiscreteWithin
    (s := e ⁻¹' {z | ξ z ≠ 0}) (t := e ⁻¹' Ω)).2 h
  simpa only [ContinuousLinearEquiv.coe_toHomeomorph,
    image_preimage_eq _ e.surjective] using this

end TauCeti.SymplecticForm
