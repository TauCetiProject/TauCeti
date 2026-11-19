/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation.VariableStructure
public import TauCeti.Analysis.Complex.RealChart
public import TauCeti.Geometry.Symplectic.Floer.Linearization.Adjoint

/-!
# Unique continuation for the linearized Floer operator and its formal adjoint

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

The same holds for the formal adjoint
`D_u^* η = -∂ₛη - ∂ₜ(η ∘ J(z, u z)) + η ∘ C(z)`
(`TauCeti.SymplecticForm.floerLinearizationAdjoint`), acting on fields `η` of covectors. By
`TauCeti.SymplecticForm.floerLinearizationAdjoint_eq_neg`, `D_u^* η = 0` is the linear
Cauchy–Riemann equation `∂ₛη + J'(z) ∂ₜη + C'(z) η = 0` on the dual space `V →L[ℝ] ℝ`, for the
structure `J'(z) θ = θ ∘ J(z, u z)`, which squares to `-1` with `J(z, u z)`, and the coefficient
`C'(z) θ = θ ∘ (∂ₜ J(z, u z) - C(z))`. This coefficient is continuous because `z ↦ J(z, u z)` is
`C¹`. So on a connected open set `Ω`, a `C¹` solution `η` of `D_u^* η = 0`:

* vanishes on `Ω` if it vanishes on a nonempty open subset of `Ω`
  (`TauCeti.SymplecticForm.eqOn_zero_of_floerLinearizationAdjoint_eq_zero_of_eqOn_zero`);
* vanishes on `Ω` if it vanishes to infinite order at one point of `Ω`
  (`TauCeti.SymplecticForm.eqOn_zero_of_floerLinearizationAdjoint_eq_zero_of_forall_isBigO`);
* otherwise has isolated zeros in `Ω`
  (`SymplecticForm.setOf_ne_zero_mem_codiscreteWithin_of_floerLinearizationAdjoint_eq_zero`).

`C¹` cokernel elements of `D_u`, the covector fields annihilating `D_u ξ` for every compactly
supported test map `ξ`, are exactly the solutions of `D_u^* η = 0`
(`TauCeti.SymplecticForm.forall_integral_apply_floerLinearization_eq_zero_iff`). In the
transversality argument for Floer moduli spaces, such an element is first shown to vanish on an
open set: on the compact core of the domain, where localized Hamiltonian variations detect it
(`TauCeti.SymplecticForm.eqOn_zero_of_forall_integral_apply_floerOperator_add_sub_eq_zero`), or
near injective points, where variations of the almost complex structure detect it
(`TauCeti.SymplecticForm.eq_zero_of_integral_apply_deriv_floerOperator_eq_zero`). Unique
continuation for the adjoint equation then makes it vanish on the whole connected domain
(`TauCeti.Geometry.Symplectic.Floer.Transversality.Cokernel`).
The variable-structure theorems themselves apply to every operator `∂ₛ + J ∂ₜ + C` with a `C¹`
field of complex structures `J`, so they also cover operators whose leading part is
`∂ₛ - J ∂ₜ`, the Cauchy–Riemann operator of the complex structure `-J`.

The proofs read `ℝ × ℝ` as `ℂ` through `Complex.equivRealProdCLM`, under which `∂ₛ` and `∂ₜ` are
the derivatives in the directions `1` and `i`
(`TauCeti.fderiv_comp_equivRealProdCLM_one`, `TauCeti.fderiv_comp_equivRealProdCLM_I`), and
transport the conclusions back with `TauCeti.eqOn_zero_of_eqOn_zero_comp_equivRealProdCLM`,
`TauCeti.isBigO_comp_equivRealProdCLM_pow` and
`TauCeti.setOf_ne_zero_mem_codiscreteWithin_of_comp_equivRealProdCLM`
(in `TauCeti.Analysis.Complex.RealChart`).

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
  {u ξ : ℝ × ℝ → V} {η : ℝ × ℝ → V →L[ℝ] ℝ} {Ω : Set (ℝ × ℝ)}

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
  exact eqOn_zero_of_eqOn_zero_comp_equivRealProdCLM <|
    eqOn_zero_of_contDiffOn_of_forall_isBigO_of_complexStructure hΩ' hΩc' hJ' hJJ' hξ' hCm hCb
      heq (show Complex.equivRealProdCLM.symm z₀ ∈ Complex.equivRealProdCLM ⁻¹' Ω by
        rwa [mem_preimage, ContinuousLinearEquiv.apply_symm_apply])
      fun n ↦ isBigO_comp_equivRealProdCLM_pow (h₀ n)

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
  obtain ⟨z₁, hz₁, hξz₁⟩ := hne
  exact setOf_ne_zero_mem_codiscreteWithin_of_comp_equivRealProdCLM <|
    setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn_of_complexStructure hΩ' hΩc' hJ'
      hJJ' hξ' hCm hCb heq ⟨Complex.equivRealProdCLM.symm z₁, by simpa using hz₁,
        by simpa using hξz₁⟩

/-! ### Unique continuation for the formal adjoint -/

/-- In the complex coordinate `z = Complex.equivRealProdCLM w`, a solution of `D_u^* η = 0` on a
connected open set `Ω` solves the linear Cauchy–Riemann equation on the dual space for the
structure `θ ↦ θ ∘ J(z, u z)` and the coefficient `θ ↦ θ ∘ (∂ₜ J(z, u z) - C(z))`, on the
connected open set `e ⁻¹' Ω`, with the regularity the variable-structure theorems ask for. -/
private theorem floerLinearizationAdjoint_eq_zero_complexCoordinate (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω)
    (hJ : ∀ z ∈ Ω, ContDiffAt ℝ 1 (fun p : (ℝ × ℝ) × V ↦ J p.1 p.2) (z, u z))
    (hJJ : ∀ z ∈ Ω, J z (u z) ∘L J z (u z) = -ContinuousLinearMap.id ℝ V)
    (hKs : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiffOn ℝ 1 u Ω)
    (hη : ContDiffOn ℝ 1 η Ω) (hD : ∀ z ∈ Ω, ω.floerLinearizationAdjoint J Ks Kt u η z = 0) :
    let e := Complex.equivRealProdCLM
    let P : (V →L[ℝ] V) →L[ℝ] (V →L[ℝ] ℝ) →L[ℝ] V →L[ℝ] ℝ :=
      (ContinuousLinearMap.compL ℝ V V ℝ).flip
    IsOpen (e ⁻¹' Ω) ∧ IsPreconnected (e ⁻¹' Ω) ∧
      ContDiffOn ℝ 1 (fun w ↦ P (J (e w) (u (e w)))) (e ⁻¹' Ω) ∧
      (∀ w ∈ e ⁻¹' Ω,
        P (J (e w) (u (e w))) ∘L P (J (e w) (u (e w))) = -ContinuousLinearMap.id ℝ _) ∧
      ContDiffOn ℝ 1 (η ∘ e) (e ⁻¹' Ω) ∧
      AEStronglyMeasurable (fun w ↦ P (fderiv ℝ (fun z ↦ J z (u z)) (e w) stdComplexLineImag -
        ω.floerLinearizationCoeff J Ks Kt u (e w))) (volume.restrict (e ⁻¹' Ω)) ∧
      (∀ w ∈ e ⁻¹' Ω, ∃ M, ∀ᶠ w' in 𝓝 w, ‖P (fderiv ℝ (fun z ↦ J z (u z)) (e w')
        stdComplexLineImag - ω.floerLinearizationCoeff J Ks Kt u (e w'))‖ ≤ M) ∧
      ∀ w ∈ e ⁻¹' Ω, fderiv ℝ (η ∘ e) w 1 + P (J (e w) (u (e w))) (fderiv ℝ (η ∘ e) w I) +
        P (fderiv ℝ (fun z ↦ J z (u z)) (e w) stdComplexLineImag -
          ω.floerLinearizationCoeff J Ks Kt u (e w)) ((η ∘ e) w) = 0 := by
  intro e P
  have hΩ' : IsOpen (e ⁻¹' Ω) := hΩ.preimage e.continuous
  -- Along `u`, the structure `z ↦ J(z, u z)` is `C¹` on `Ω`.
  have hJu (z : ℝ × ℝ) (hz : z ∈ Ω) : ContDiffAt ℝ 1 (fun z ↦ J z (u z)) z :=
    (hJ z hz).comp₂ contDiffAt_id (hu.contDiffAt (hΩ.mem_nhds hz))
  have hC : ContinuousOn (fun w ↦ P (fderiv ℝ (fun z ↦ J z (u z)) (e w) stdComplexLineImag -
      ω.floerLinearizationCoeff J Ks Kt u (e w))) (e ⁻¹' Ω) := by
    refine P.continuous.comp_continuousOn (ContinuousOn.sub ?_ ?_)
    · exact fun w hw ↦ ((((hJu (e w) hw).continuousAt_fderiv one_ne_zero).clm_apply
        continuousAt_const).comp e.continuous.continuousAt).continuousWithinAt
    · exact (ω.continuousOn_floerLinearizationCoeff hJ hKs hKt
        fun z hz ↦ hu.contDiffAt (hΩ.mem_nhds hz)).comp e.continuous.continuousOn
        (mapsTo_preimage _ _)
  refine ⟨hΩ', (e.toHomeomorph.isPreconnected_preimage).2 hΩc, fun w hw ↦ ?_,
    fun w hw ↦ ?_, hη.comp_continuousLinearMap (e : ℂ →L[ℝ] ℝ × ℝ),
    hC.aestronglyMeasurable hΩ'.measurableSet, fun w hw ↦ ?_, fun w hw ↦ ?_⟩
  · -- The explicit arguments select the normed structures on the spaces of continuous linear
    -- maps, which elaboration from `P` alone leaves undetermined.
    exact ((ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := V →L[ℝ] V)
      (F := (V →L[ℝ] ℝ) →L[ℝ] V →L[ℝ] ℝ) (n := 1) P).contDiffAt.comp w
      ((hJu (e w) hw).comp w e.contDiff.contDiffAt)).contDiffWithinAt
  · have hA (v : V) : J (e w) (u (e w)) (J (e w) (u (e w)) v) = -v := by
      simpa using congr($(hJJ (e w) hw) v)
    ext θ v
    simp [P, hA]
  · -- As above, the explicit space selects the operator norm.
    have hc := (hC.continuousAt (hΩ'.mem_nhds hw)).norm (E := (V →L[ℝ] ℝ) →L[ℝ] V →L[ℝ] ℝ)
    exact ⟨_, (hc.eventually (gt_mem_nhds (lt_add_one _))).mono fun _ h ↦ h.le⟩
  · have hηd : DifferentiableAt ℝ η (e w) :=
      (hη.contDiffAt (hΩ.mem_nhds hw)).differentiableAt one_ne_zero
    have h := hD (e w) hw
    rw [floerLinearizationAdjoint_eq_neg hηd ((hJu (e w) hw).differentiableAt one_ne_zero),
      neg_eq_zero] at h
    rw [fderiv_comp_equivRealProdCLM_one, fderiv_comp_equivRealProdCLM_I, comp_apply]
    simpa only [P, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.comp_sub] using h

/-- **Unique continuation for the formal adjoint of the linearized Floer operator.** Let `J` be
`C¹` and the Hamiltonians `K_s`, `K_t` be `C²` near the graph of a `C¹` map `u` over a connected
open set `Ω ⊆ ℝ × ℝ`, with `J(z, u z)² = -1` on `Ω`. A `C¹` covector field `η` with `D_u^* η = 0`
on `Ω` that vanishes on a nonempty open subset of `Ω` vanishes on `Ω`. -/
theorem eqOn_zero_of_floerLinearizationAdjoint_eq_zero_of_eqOn_zero (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω)
    (hJ : ∀ z ∈ Ω, ContDiffAt ℝ 1 (fun p : (ℝ × ℝ) × V ↦ J p.1 p.2) (z, u z))
    (hJJ : ∀ z ∈ Ω, J z (u z) ∘L J z (u z) = -ContinuousLinearMap.id ℝ V)
    (hKs : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiffOn ℝ 1 u Ω)
    (hη : ContDiffOn ℝ 1 η Ω) (hD : ∀ z ∈ Ω, ω.floerLinearizationAdjoint J Ks Kt u η z = 0)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hUne : U.Nonempty) (hUΩ : U ⊆ Ω) (h₀ : EqOn η 0 U) :
    EqOn η 0 Ω := by
  obtain ⟨hΩ', hΩc', hJ', hJJ', hη', hCm, hCb, heq⟩ :=
    floerLinearizationAdjoint_eq_zero_complexCoordinate hΩ hΩc hJ hJJ hKs hKt hu hη hD
  set e := Complex.equivRealProdCLM
  obtain ⟨z₁, hz₁⟩ := hUne
  exact eqOn_zero_of_eqOn_zero_comp_equivRealProdCLM <|
    eqOn_zero_of_contDiffOn_of_eqOn_zero_of_complexStructure hΩ' hΩc' hJ' hJJ' hη' hCm hCb heq
      (hU.preimage e.continuous) ⟨e.symm z₁, by simpa using hz₁⟩ (preimage_mono hUΩ)
      fun w hw ↦ h₀ hw

/-- **Unique continuation from a zero of infinite order for the formal adjoint.** Let `J` be
`C¹` and the Hamiltonians `K_s`, `K_t` be `C²` near the graph of a `C¹` map `u` over a connected
open set `Ω ⊆ ℝ × ℝ`, with `J(z, u z)² = -1` on `Ω`. A `C¹` covector field `η` with `D_u^* η = 0`
on `Ω` and `η = O(‖z - z₀‖ⁿ)` near one point `z₀ ∈ Ω` for every `n` vanishes on `Ω`. -/
theorem eqOn_zero_of_floerLinearizationAdjoint_eq_zero_of_forall_isBigO (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω)
    (hJ : ∀ z ∈ Ω, ContDiffAt ℝ 1 (fun p : (ℝ × ℝ) × V ↦ J p.1 p.2) (z, u z))
    (hJJ : ∀ z ∈ Ω, J z (u z) ∘L J z (u z) = -ContinuousLinearMap.id ℝ V)
    (hKs : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiffOn ℝ 1 u Ω)
    (hη : ContDiffOn ℝ 1 η Ω) (hD : ∀ z ∈ Ω, ω.floerLinearizationAdjoint J Ks Kt u η z = 0)
    {z₀ : ℝ × ℝ} (hz₀ : z₀ ∈ Ω) (h₀ : ∀ n : ℕ, η =O[𝓝 z₀] fun z ↦ ‖z - z₀‖ ^ n) :
    EqOn η 0 Ω := by
  obtain ⟨hΩ', hΩc', hJ', hJJ', hη', hCm, hCb, heq⟩ :=
    floerLinearizationAdjoint_eq_zero_complexCoordinate hΩ hΩc hJ hJJ hKs hKt hu hη hD
  exact eqOn_zero_of_eqOn_zero_comp_equivRealProdCLM <|
    eqOn_zero_of_contDiffOn_of_forall_isBigO_of_complexStructure hΩ' hΩc' hJ' hJJ' hη' hCm hCb
      heq (show Complex.equivRealProdCLM.symm z₀ ∈ Complex.equivRealProdCLM ⁻¹' Ω by
        rwa [mem_preimage, ContinuousLinearEquiv.apply_symm_apply])
      fun n ↦ isBigO_comp_equivRealProdCLM_pow (h₀ n)

/-- **Isolated zeros of solutions of the formal adjoint equation.** Let `J` be `C¹` and the
Hamiltonians `K_s`, `K_t` be `C²` near the graph of a `C¹` map `u` over a connected open set
`Ω ⊆ ℝ × ℝ`, with `J(z, u z)² = -1` on `Ω`. The zeros of a `C¹` covector field `η` with
`D_u^* η = 0` on `Ω` that is not identically zero on `Ω` form a discrete subset of `Ω`. -/
theorem setOf_ne_zero_mem_codiscreteWithin_of_floerLinearizationAdjoint_eq_zero (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω)
    (hJ : ∀ z ∈ Ω, ContDiffAt ℝ 1 (fun p : (ℝ × ℝ) × V ↦ J p.1 p.2) (z, u z))
    (hJJ : ∀ z ∈ Ω, J z (u z) ∘L J z (u z) = -ContinuousLinearMap.id ℝ V)
    (hKs : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiffOn ℝ 1 u Ω)
    (hη : ContDiffOn ℝ 1 η Ω) (hD : ∀ z ∈ Ω, ω.floerLinearizationAdjoint J Ks Kt u η z = 0)
    (hne : ∃ z ∈ Ω, η z ≠ 0) : {z | η z ≠ 0} ∈ codiscreteWithin Ω := by
  obtain ⟨hΩ', hΩc', hJ', hJJ', hη', hCm, hCb, heq⟩ :=
    floerLinearizationAdjoint_eq_zero_complexCoordinate hΩ hΩc hJ hJJ hKs hKt hu hη hD
  obtain ⟨z₁, hz₁, hηz₁⟩ := hne
  exact setOf_ne_zero_mem_codiscreteWithin_of_comp_equivRealProdCLM <|
    setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn_of_complexStructure hΩ' hΩc' hJ'
      hJJ' hη' hCm hCb heq ⟨Complex.equivRealProdCLM.symm z₁, by simpa using hz₁,
        by simpa using hηz₁⟩

end TauCeti.SymplecticForm
