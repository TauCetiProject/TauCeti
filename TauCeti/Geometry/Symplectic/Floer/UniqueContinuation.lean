/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation.DifferentialInequality
public import TauCeti.Analysis.Complex.EquivRealProd
public import TauCeti.Geometry.Symplectic.Floer.Linearization.Adjoint
import TauCeti.Analysis.Calculus.ContDiff.Prod
import TauCeti.Topology.Codiscrete

/-!
# Unique continuation for the linearized Floer operator, its formal adjoint and Floer solutions

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

The nonlinear Floer equation `∂ₛu - X_{K_s}(u) + J(z, u)(∂ₜu - X_{K_t}(u)) = 0` has the same
unique continuation property for pairs of solutions. The difference `w = u - v` of two solutions
solves no linear equation with a coefficient given in advance, but it satisfies the Cauchy–Riemann
inequality `‖∂ₛw + J(z, u z) ∂ₜw‖ ≤ M ‖w‖` near every coincidence `u z₀ = v z₀`
(`TauCeti.SymplecticForm.exists_eventually_norm_le_of_floerOperator_eq_zero`), by the local
Lipschitz bounds of `J` and of the Hamiltonian vector fields applied to the difference of the two
equations (`TauCeti.SymplecticForm.floerOperator_sub_floerOperator`). By
`TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation.DifferentialInequality`, two `C¹`
solutions on a connected open set `Ω`:

* agree on `Ω` if they agree on a nonempty open subset of `Ω`
  (`TauCeti.SymplecticForm.eqOn_of_floerOperator_eq_zero_of_eqOn`);
* agree on `Ω` if they agree to infinite order at one point of `Ω`
  (`TauCeti.SymplecticForm.eqOn_of_floerOperator_eq_zero_of_forall_isBigO`);
* otherwise agree only on a discrete subset of `Ω`
  (`TauCeti.SymplecticForm.setOf_ne_mem_codiscreteWithin_of_floerOperator_eq_zero`).

The injective-point argument of Floer, Hofer and Salamon applies this to a solution and one of its
`s`-translates when the data do not depend on `s`. Only the structure `J(z, u z)` along the first
solution needs to be a complex structure, and the regularity of the data is only used near the
graph of the first solution.

For the cylindrical datum `K = H_t dt` and `s`-independent `J_t`, the translate
`(s, t) ↦ u(s + c, t)` of a Floer trajectory is again one. So a trajectory on `ℝ × ℝ` that agrees
with such a translate on a nonempty open set is `(c, 0)`-periodic everywhere
(`TauCeti.SymplecticForm.periodic_of_floerOperator_eq_zero_of_eqOn`). Likewise, on a band
`ℝ × T` over an open interval `T`, such as the strip `ℝ × (0, 1)` of Floer trajectories between two
Lagrangians, a solution of the equation on the band agreeing with its translate on a nonempty open
subset agrees with it on the whole band
(`TauCeti.SymplecticForm.eqOn_comp_add_of_floerOperator_eq_zero_of_eqOn`). For `c ≠ 0` a periodic
trajectory is stationary, either because it converges at an end
(`Function.Periodic.eq_of_tendsto_of_tendsto_add_nsmul`) or because it has finite energy
(`TauCeti.SymplecticForm.eq_zero_of_lintegral_floerEnergyDensity_ne_top_of_periodic`). In the
argument of Floer, Hofer and Salamon for the density of the regular points of a nonstationary
trajectory, this excludes a trajectory coinciding with one of its translates on an open set.

The proofs read `ℝ × ℝ` as `ℂ` through `Complex.equivRealProdCLM`, under which `∂ₛ` and `∂ₜ` are
the derivatives in the directions `1` and `i`
(`TauCeti.fderiv_comp_equivRealProdCLM_one`, `TauCeti.fderiv_comp_equivRealProdCLM_I`), and
carry the conclusions back along this homeomorphism.

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
  refine ⟨hΩ', (e.toHomeomorph.isPreconnected_preimage).2 hΩc,
    (contDiffOn_comp_graph hJ hu).comp_continuousLinearMap (e : ℂ →L[ℝ] ℝ × ℝ),
    fun w hw ↦ hJJ (e w) hw,
    hξ.comp_continuousLinearMap (e : ℂ →L[ℝ] ℝ × ℝ), hC.aestronglyMeasurable hΩ'.measurableSet,
    fun w hw ↦ ?_, fun w hw ↦ ?_⟩
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
  exact (eqOn_zero_of_contDiffOn_of_eqOn_zero_of_complexStructure hΩ' hΩc' hJ' hJJ' hξ' hCm hCb
    heq (hU.preimage e.continuous) ⟨e.symm z₁, by simpa using hz₁⟩ (preimage_mono hUΩ)
    fun w hw ↦ h₀ hw).cancel_right e.surjective.surjOn_preimage

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
  exact (eqOn_zero_of_contDiffOn_of_forall_isBigO_of_complexStructure hΩ' hΩc' hJ' hJJ' hξ' hCm
    hCb heq (show e.symm z₀ ∈ e ⁻¹' Ω by rwa [mem_preimage, e.apply_symm_apply])
    fun n ↦ isBigO_comp_equivRealProdCLM (h₀ n)).cancel_right e.surjective.surjOn_preimage

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
  exact e.toHomeomorph.preimage_mem_codiscreteWithin.1 h

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
  exact (eqOn_zero_of_contDiffOn_of_eqOn_zero_of_complexStructure hΩ' hΩc' hJ' hJJ' hη' hCm hCb
    heq (hU.preimage e.continuous) ⟨e.symm z₁, by simpa using hz₁⟩ (preimage_mono hUΩ)
    fun w hw ↦ h₀ hw).cancel_right e.surjective.surjOn_preimage

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
  set e := Complex.equivRealProdCLM
  exact (eqOn_zero_of_contDiffOn_of_forall_isBigO_of_complexStructure hΩ' hΩc' hJ' hJJ' hη' hCm
    hCb heq (show e.symm z₀ ∈ e ⁻¹' Ω by rwa [mem_preimage, e.apply_symm_apply])
    fun n ↦ isBigO_comp_equivRealProdCLM (h₀ n)).cancel_right e.surjective.surjOn_preimage

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
  set e := Complex.equivRealProdCLM
  obtain ⟨z₁, hz₁, hηz₁⟩ := hne
  have h := setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn_of_complexStructure hΩ' hΩc' hJ'
    hJJ' hη' hCm hCb heq ⟨e.symm z₁, by simpa using hz₁, by simpa using hηz₁⟩
  exact e.toHomeomorph.preimage_mem_codiscreteWithin.1 h

/-! ### Unique continuation for Floer solutions -/

section Solutions

variable {v : ℝ × ℝ → V}

/-- **The difference of two Floer solutions obeys a Cauchy–Riemann inequality.** Let `u` and `v` be
`C¹` solutions of the Floer equation `∂ₛu - X_{K_s}(u) + J(z, u)(∂ₜu - X_{K_t}(u)) = 0` on an open
set `Ω ⊆ ℝ × ℝ`, with a coincidence `u z₀ = v z₀` at `z₀ ∈ Ω`, and let `J` be `C¹` and the
Hamiltonians `K_s`, `K_t` be `C²` near `(z₀, u z₀)`. Near `z₀`, the Lipschitz bounds of `J` and
of the Hamiltonian vector fields near the common value give `‖∂ₛw + J(z, u z) ∂ₜw‖ ≤ M ‖w‖` for
the difference `w = u - v` and some constant `M`. -/
theorem exists_eventually_norm_le_of_floerOperator_eq_zero (hΩ : IsOpen Ω) {z₀ : ℝ × ℝ}
    (hz₀ : z₀ ∈ Ω) (hJ : ContDiffAt ℝ 1 (fun p : (ℝ × ℝ) × V ↦ J p.1 p.2) (z₀, u z₀))
    (hKs : ContDiffAt ℝ 2 (uncurry Ks) (z₀, u z₀)) (hKt : ContDiffAt ℝ 2 (uncurry Kt) (z₀, u z₀))
    (hu : ContDiffOn ℝ 1 u Ω) (hv : ContDiffOn ℝ 1 v Ω)
    (hFu : ∀ z ∈ Ω, ω.floerOperator J Ks Kt u z = 0)
    (hFv : ∀ z ∈ Ω, ω.floerOperator J Ks Kt v z = 0) (h : u z₀ = v z₀) :
    ∃ M, ∀ᶠ z in 𝓝 z₀, ‖fderiv ℝ (u - v) z stdComplexLineReal +
      J z (u z) (fderiv ℝ (u - v) z stdComplexLineImag)‖ ≤ M * ‖(u - v) z‖ := by
  have hΩz := hΩ.mem_nhds hz₀
  have huc : ContinuousAt u z₀ := hu.continuousOn.continuousAt hΩz
  have hvc : ContinuousAt v z₀ := hv.continuousOn.continuousAt hΩz
  have hXs := ω.contDiffAt_hamiltonianVectorField_uncurry (n := 1) hKs
  have hXt := ω.contDiffAt_hamiltonianVectorField_uncurry (n := 1) hKt
  -- The data differ along the two graphs by at most a multiple of `‖u - v‖`.
  obtain ⟨LJ, hLJ⟩ := hJ.exists_eventually_norm_sub_le huc hvc h
  obtain ⟨Ls, hLs⟩ := hXs.exists_eventually_norm_sub_le huc hvc h
  obtain ⟨Lt, hLt⟩ := hXt.exists_eventually_norm_sub_le huc hvc h
  -- The structure along `u` and the factor `b = ∂ₜv - X_{K_t}(v)` are bounded near `z₀`.
  have hJu : ContinuousAt (fun z ↦ J z (u z)) z₀ :=
    hJ.continuousAt.comp_of_eq (continuousAt_id.prodMk huc) rfl
  set b : ℝ × ℝ → V := fun z ↦
    fderiv ℝ v z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (v z)
  have hb : ContinuousAt b z₀ :=
    ((((hv.continuousOn_fderiv_of_isOpen hΩ le_rfl).continuousAt hΩz).clm_apply
      continuousAt_const).sub (hXt.continuousAt.comp_of_eq (continuousAt_id.prodMk hvc)
        (by simp [h])))
  refine ⟨Ls + (‖J z₀ (u z₀)‖ + 1) * Lt + LJ * (‖b z₀‖ + 1), ?_⟩
  filter_upwards [hΩz, hLJ, hLs, hLt, hJu.norm.eventually (gt_mem_nhds (lt_add_one _)),
    hb.norm.eventually (gt_mem_nhds (lt_add_one _))] with z hz hJ' hs ht' hJz hbz
  -- Subtracting the two Floer equations expresses the operator through differences of the data.
  have hkey := ω.floerOperator_sub_floerOperator J Ks Kt
    ((hu.differentiableOn one_ne_zero).differentiableAt (hΩ.mem_nhds hz))
    ((hv.differentiableOn one_ne_zero).differentiableAt (hΩ.mem_nhds hz))
  rw [hFu z hz, hFv z hz, sub_zero] at hkey
  have hD : fderiv ℝ (u - v) z stdComplexLineReal +
      J z (u z) (fderiv ℝ (u - v) z stdComplexLineImag) =
        (ω.hamiltonianVectorField (Ks z) (u z) - ω.hamiltonianVectorField (Ks z) (v z)) +
        J z (u z) (ω.hamiltonianVectorField (Kt z) (u z) - ω.hamiltonianVectorField (Kt z) (v z)) -
        (J z (u z) - J z (v z)) (b z) := by
    linear_combination (norm := module) -hkey
  rw [hD, Pi.sub_apply]
  calc _ ≤ ‖ω.hamiltonianVectorField (Ks z) (u z) - ω.hamiltonianVectorField (Ks z) (v z)‖ +
          ‖J z (u z)‖ * ‖ω.hamiltonianVectorField (Kt z) (u z) -
            ω.hamiltonianVectorField (Kt z) (v z)‖ + ‖J z (u z) - J z (v z)‖ * ‖b z‖ :=
        norm_sub_le_of_le (norm_add_le_of_le le_rfl ((J z (u z)).le_opNorm _))
          ((J z (u z) - J z (v z)).le_opNorm _)
    _ ≤ Ls * ‖u z - v z‖ + (‖J z₀ (u z₀)‖ + 1) * (Lt * ‖u z - v z‖) +
          LJ * ‖u z - v z‖ * (‖b z₀‖ + 1) := by
        gcongr
    _ = _ := by ring

/-- In the complex coordinate `z = Complex.equivRealProdCLM w`, the difference of two Floer
solutions on a connected open set `Ω` obeys the Cauchy–Riemann inequality for the structure
`J(z, u z)` near its zeros in the connected open set `e ⁻¹' Ω`, with the regularity the unique
continuation theorems for differential inequalities ask for. -/
private theorem floerOperator_eq_zero_complexCoordinate (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω)
    (hJ : ∀ z ∈ Ω, ContDiffAt ℝ 1 (fun p : (ℝ × ℝ) × V ↦ J p.1 p.2) (z, u z))
    (hKs : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiffOn ℝ 1 u Ω)
    (hv : ContDiffOn ℝ 1 v Ω) (hFu : ∀ z ∈ Ω, ω.floerOperator J Ks Kt u z = 0)
    (hFv : ∀ z ∈ Ω, ω.floerOperator J Ks Kt v z = 0) :
    let e := Complex.equivRealProdCLM
    IsOpen (e ⁻¹' Ω) ∧ IsPreconnected (e ⁻¹' Ω) ∧
      ContDiffOn ℝ 1 (fun w ↦ J (e w) (u (e w))) (e ⁻¹' Ω) ∧
      ContDiffOn ℝ 1 ((u - v) ∘ e) (e ⁻¹' Ω) ∧
      ∀ w ∈ e ⁻¹' Ω, ((u - v) ∘ e) w = 0 → ∃ M, ∀ᶠ w' in 𝓝 w, ‖fderiv ℝ ((u - v) ∘ e) w' 1 +
        J (e w') (u (e w')) (fderiv ℝ ((u - v) ∘ e) w' I)‖ ≤ M * ‖((u - v) ∘ e) w'‖ := by
  intro e
  refine ⟨hΩ.preimage e.continuous, (e.toHomeomorph.isPreconnected_preimage).2 hΩc,
    (contDiffOn_comp_graph hJ hu).comp_continuousLinearMap (e : ℂ →L[ℝ] ℝ × ℝ),
    (hu.sub hv).comp_continuousLinearMap (e : ℂ →L[ℝ] ℝ × ℝ), fun w hw h ↦ ?_⟩
  obtain ⟨M, hM⟩ := exists_eventually_norm_le_of_floerOperator_eq_zero hΩ hw (hJ _ hw)
    (hKs _ hw) (hKt _ hw) hu hv hFu hFv (sub_eq_zero.1 h)
  refine ⟨M, (e.continuous.tendsto w).eventually hM |>.mono fun w' hw' ↦ ?_⟩
  rwa [fderiv_comp_equivRealProdCLM_one, fderiv_comp_equivRealProdCLM_I, comp_apply]

/-- **Unique continuation for Floer solutions.** Let `J` be `C¹` and the Hamiltonians `K_s`, `K_t`
be `C²` near the graph of `u` over a connected open set `Ω ⊆ ℝ × ℝ`, with `J(z, u z)² = -1` on
`Ω`. Two `C¹` solutions `u`, `v` of the Floer equation on `Ω` that agree on a nonempty open subset
of `Ω` agree on `Ω`. -/
theorem eqOn_of_floerOperator_eq_zero_of_eqOn (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hJ : ∀ z ∈ Ω, ContDiffAt ℝ 1 (fun p : (ℝ × ℝ) × V ↦ J p.1 p.2) (z, u z))
    (hJJ : ∀ z ∈ Ω, J z (u z) ∘L J z (u z) = -ContinuousLinearMap.id ℝ V)
    (hKs : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiffOn ℝ 1 u Ω)
    (hv : ContDiffOn ℝ 1 v Ω) (hFu : ∀ z ∈ Ω, ω.floerOperator J Ks Kt u z = 0)
    (hFv : ∀ z ∈ Ω, ω.floerOperator J Ks Kt v z = 0) {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hUne : U.Nonempty) (hUΩ : U ⊆ Ω) (h₀ : EqOn u v U) : EqOn u v Ω := by
  obtain ⟨hΩ', hΩc', hJ', hξ', hb⟩ :=
    floerOperator_eq_zero_complexCoordinate hΩ hΩc hJ hKs hKt hu hv hFu hFv
  set e := Complex.equivRealProdCLM
  obtain ⟨z₁, hz₁⟩ := hUne
  have h : EqOn (u - v) 0 Ω :=
    (eqOn_zero_of_contDiffOn_of_eqOn_zero_of_norm_le hΩ' hΩc' hJ' (fun w hw ↦ hJJ (e w) hw) hξ' hb
      (hU.preimage e.continuous) ⟨e.symm z₁, by simpa using hz₁⟩ (preimage_mono hUΩ)
      fun w hw ↦ sub_eq_zero.2 (h₀ hw)).cancel_right e.surjective.surjOn_preimage
  exact fun z hz ↦ sub_eq_zero.1 (h hz)

/-- **Unique continuation from a coincidence of infinite order for Floer solutions.** Let `J` be
`C¹` and the Hamiltonians `K_s`, `K_t` be `C²` near the graph of `u` over a connected open set
`Ω ⊆ ℝ × ℝ`, with `J(z, u z)² = -1` on `Ω`. Two `C¹` solutions `u`, `v` of the Floer equation on
`Ω` with `u - v = O(‖z - z₀‖ⁿ)` near one point `z₀ ∈ Ω` for every `n` agree on `Ω`. -/
theorem eqOn_of_floerOperator_eq_zero_of_forall_isBigO (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω)
    (hJ : ∀ z ∈ Ω, ContDiffAt ℝ 1 (fun p : (ℝ × ℝ) × V ↦ J p.1 p.2) (z, u z))
    (hJJ : ∀ z ∈ Ω, J z (u z) ∘L J z (u z) = -ContinuousLinearMap.id ℝ V)
    (hKs : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiffOn ℝ 1 u Ω)
    (hv : ContDiffOn ℝ 1 v Ω) (hFu : ∀ z ∈ Ω, ω.floerOperator J Ks Kt u z = 0)
    (hFv : ∀ z ∈ Ω, ω.floerOperator J Ks Kt v z = 0) {z₀ : ℝ × ℝ} (hz₀ : z₀ ∈ Ω)
    (h₀ : ∀ n : ℕ, (u - v) =O[𝓝 z₀] fun z ↦ ‖z - z₀‖ ^ n) : EqOn u v Ω := by
  obtain ⟨hΩ', hΩc', hJ', hξ', hb⟩ :=
    floerOperator_eq_zero_complexCoordinate hΩ hΩc hJ hKs hKt hu hv hFu hFv
  set e := Complex.equivRealProdCLM
  have h : EqOn (u - v) 0 Ω :=
    (eqOn_zero_of_contDiffOn_of_forall_isBigO_of_norm_le hΩ' hΩc' hJ' (fun w hw ↦ hJJ (e w) hw)
      hξ' hb (show e.symm z₀ ∈ e ⁻¹' Ω by rwa [mem_preimage, e.apply_symm_apply])
      fun n ↦ isBigO_comp_equivRealProdCLM (h₀ n)).cancel_right e.surjective.surjOn_preimage
  exact fun z hz ↦ sub_eq_zero.1 (h hz)

/-- **Isolated coincidences of Floer solutions.** Let `J` be `C¹` and the Hamiltonians `K_s`,
`K_t` be `C²` near the graph of `u` over a connected open set `Ω ⊆ ℝ × ℝ`, with `J(z, u z)² = -1`
on `Ω`. If two `C¹` solutions `u`, `v` of the Floer equation on `Ω` differ somewhere in `Ω`, the
points of `Ω` where they agree form a discrete subset of `Ω`. -/
theorem setOf_ne_mem_codiscreteWithin_of_floerOperator_eq_zero (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω)
    (hJ : ∀ z ∈ Ω, ContDiffAt ℝ 1 (fun p : (ℝ × ℝ) × V ↦ J p.1 p.2) (z, u z))
    (hJJ : ∀ z ∈ Ω, J z (u z) ∘L J z (u z) = -ContinuousLinearMap.id ℝ V)
    (hKs : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiffOn ℝ 1 u Ω)
    (hv : ContDiffOn ℝ 1 v Ω) (hFu : ∀ z ∈ Ω, ω.floerOperator J Ks Kt u z = 0)
    (hFv : ∀ z ∈ Ω, ω.floerOperator J Ks Kt v z = 0) (hne : ∃ z ∈ Ω, u z ≠ v z) :
    {z | u z ≠ v z} ∈ codiscreteWithin Ω := by
  obtain ⟨hΩ', hΩc', hJ', hξ', hb⟩ :=
    floerOperator_eq_zero_complexCoordinate hΩ hΩc hJ hKs hKt hu hv hFu hFv
  set e := Complex.equivRealProdCLM
  obtain ⟨z₁, hz₁, hne₁⟩ := hne
  have h := setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn_of_norm_le hΩ' hΩc' hJ'
    (fun w hw ↦ hJJ (e w) hw) hξ' hb
    ⟨e.symm z₁, by simpa using hz₁, by simpa [sub_eq_zero] using hne₁⟩
  simpa only [Pi.sub_apply, ne_eq, sub_eq_zero] using
    (e.toHomeomorph.preimage_mem_codiscreteWithin (s := {z | (u - v) z ≠ 0})).1 h

end Solutions

/-! ### Translates of Floer trajectories -/

/-- **A Floer solution on a band agreeing with a translate on an open set agrees with it on the
band.** Let `T ⊆ ℝ` be open and preconnected, and let `u` be a `C¹` map solving the Floer equation
`∂ₛu + J_t(u)(∂ₜu - X_{H_t}(u)) = 0` on the band `ℝ × T`, for a `C¹` family `J_t` with
`J_t(u)² = -1` along `u` on the band and a `C²` Hamiltonian `H`. If `u(s + c, t) = u(s, t)` on a
nonempty open subset of the band, then `u(s + c, t) = u(s, t)` on the whole band. For `T = (0, 1)`
the band is the strip of Floer trajectories between two Lagrangians. -/
theorem eqOn_comp_add_of_floerOperator_eq_zero_of_eqOn {J : ℝ → V → V →L[ℝ] V} {H : ℝ → V → ℝ}
    {T : Set ℝ} (hT : IsOpen T) (hTc : IsPreconnected T)
    (hJ : ContDiff ℝ 1 (fun p : ℝ × V ↦ J p.1 p.2))
    (hJJ : ∀ z ∈ univ ×ˢ T, J z.2 (u z) ∘L J z.2 (u z) = -ContinuousLinearMap.id ℝ V)
    (hH : ContDiff ℝ 2 (uncurry H)) (hu : ContDiff ℝ 1 u)
    (hF : ∀ z ∈ univ ×ˢ T, ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) u z = 0)
    {c : ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hUne : U.Nonempty) (hUT : U ⊆ univ ×ˢ T)
    (hUc : EqOn u (fun z ↦ u (z + (c, 0))) U) : EqOn u (fun z ↦ u (z + (c, 0))) (univ ×ˢ T) := by
  -- The translate solves the same equation on the band, because the data do not depend on `s`.
  have hFc (z) (hz : z ∈ univ ×ˢ T) : ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0)
      (fun p ↦ H p.2) (fun z ↦ u (z + (c, 0))) z = 0 := by
    have h := ω.floerOperator_comp_sub J H u (-c) z
    have he : (fun w ↦ u (w - (-c, 0))) = fun w ↦ u (w + (c, 0)) := by
      ext w
      rw [sub_eq_add_neg, Prod.neg_mk, neg_neg, neg_zero]
    rw [he] at h
    rw [h]
    exact hF _ ⟨mem_univ _, by simpa using hz.2⟩
  have hJ' : ContDiff ℝ 1 (fun p : (ℝ × ℝ) × V ↦ J p.1.2 p.2) :=
    hJ.comp ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd)
  have hKs : ContDiff ℝ 2 (uncurry fun (_ : ℝ × ℝ) (_ : V) ↦ (0 : ℝ)) := contDiff_const
  have hKt : ContDiff ℝ 2 (uncurry fun (p : ℝ × ℝ) ↦ H p.2) :=
    hH.comp ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd)
  exact eqOn_of_floerOperator_eq_zero_of_eqOn (isOpen_univ.prod hT)
    (isPreconnected_univ.prod hTc) (fun _ _ ↦ hJ'.contDiffAt) hJJ (fun _ _ ↦ hKs.contDiffAt)
    (fun _ _ ↦ hKt.contDiffAt) hu.contDiffOn (hu.comp (contDiff_id.add contDiff_const)).contDiffOn
    hF hFc hU hUne hUT hUc

/-- **A Floer trajectory agreeing with a translate on an open set is periodic.** Let `u` be a
`C¹` solution on `ℝ × ℝ` of the Floer equation `∂ₛu + J_t(u)(∂ₜu - X_{H_t}(u)) = 0`, for a `C¹`
family `J_t` with `J_t(u)² = -1` along `u` and a `C²` Hamiltonian `H`. If `u(s + c, t) = u(s, t)`
on a nonempty open set, then `u(s + c, t) = u(s, t)` everywhere. -/
theorem periodic_of_floerOperator_eq_zero_of_eqOn {J : ℝ → V → V →L[ℝ] V} {H : ℝ → V → ℝ}
    (hJ : ContDiff ℝ 1 (fun p : ℝ × V ↦ J p.1 p.2))
    (hJJ : ∀ z, J z.2 (u z) ∘L J z.2 (u z) = -ContinuousLinearMap.id ℝ V)
    (hH : ContDiff ℝ 2 (uncurry H)) (hu : ContDiff ℝ 1 u)
    (hF : ∀ z, ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) u z = 0)
    {c : ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hUne : U.Nonempty)
    (hUc : EqOn u (fun z ↦ u (z + (c, 0))) U) : Periodic u (c, 0) := fun z ↦
  (eqOn_comp_add_of_floerOperator_eq_zero_of_eqOn isOpen_univ isPreconnected_univ hJ
    (fun z _ ↦ hJJ z) hH hu (fun z _ ↦ hF z) hU hUne (by simp) hUc (by simp)).symm

end TauCeti.SymplecticForm
