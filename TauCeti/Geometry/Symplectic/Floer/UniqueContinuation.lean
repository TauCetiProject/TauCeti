/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation.VariableStructure
public import TauCeti.Geometry.Symplectic.Floer.Linearization.Basic
import TauCeti.Analysis.Calculus.ContDiff.Prod
import TauCeti.MeasureTheory.Function.RankOne

/-!
# Unique continuation for the Floer equation

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

## Pairs of solutions

The same holds for two solutions `u` and `v` of the nonlinear Floer equation
`∂ₛu - X_{K_s}(u) + J(z, u)(∂ₜu - X_{K_t}(u)) = 0` (`TauCeti.SymplecticForm.floerOperator`):
their difference `w = u - v` solves

`∂ₛw + J(z, u z) ∂ₜw = g(z)`, where `‖g(z)‖ ≤ M ‖w(z)‖` near each point where `u = v`,

because `g` collects the differences of `X_{K_s}`, `X_{K_t}` and `J` between the graphs of `u`
and `v`, which are Lipschitz there. A rank-one coefficient
(`MeasureTheory.AEStronglyMeasurable.exists_clm_apply_eq`) writes `g = -C w` with `C`
measurable and locally bounded, so `w` solves a linear Cauchy–Riemann equation as above. Hence on
a connected open set `Ω` two such solutions

* agree on `Ω` if they agree on a nonempty open subset of `Ω`
  (`TauCeti.SymplecticForm.eqOn_of_floerOperator_eq_zero_of_eqOn`);
* agree on `Ω` if they agree to infinite order at one point of `Ω`
  (`TauCeti.SymplecticForm.eqOn_of_floerOperator_eq_zero_of_forall_isBigO`);
* otherwise agree only on a discrete subset of `Ω`
  (`TauCeti.SymplecticForm.setOf_ne_mem_codiscreteWithin_of_floerOperator_eq_zero`).

Only the structure along `u` has to be complex; along `v` the data need only be continuous, with
`C¹` Hamiltonians.

For the cylindrical datum `K = H_t dt` and `s`-independent `J_t`, the translate
`(s, t) ↦ u(s + c, t)` of a Floer trajectory is again one. So a trajectory on `ℝ × ℝ` that agrees
with such a translate on a nonempty open set is `(c, 0)`-periodic everywhere
(`TauCeti.SymplecticForm.periodic_of_floerOperator_eq_zero_of_eqOn`). For `c ≠ 0` a periodic
trajectory is stationary, either because it converges at an end
(`Function.Periodic.eq_of_tendsto_of_tendsto_add_nsmul`) or because it has finite energy
(`TauCeti.SymplecticForm.eq_zero_of_lintegral_floerEnergyDensity_ne_top_of_periodic`). In the
argument of Floer, Hofer and Salamon for the density of the regular points of a nonstationary
trajectory, this excludes a trajectory coinciding with one of its translates on an open set.

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
open scoped NNReal

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ}
  {u ξ : ℝ × ℝ → V} {Ω : Set (ℝ × ℝ)}

omit [FiniteDimensional ℝ V] in
/-- In the complex coordinate `z = Complex.equivRealProdCLM w`, the structure `J(z, u z)` along a
`C¹` map `u` over a connected open set `Ω` is a `C¹` field of complex structures on the connected
open set `e ⁻¹' Ω`, as the variable-structure theorems ask. -/
private theorem complexCoordinate_structure (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hJ : ∀ z ∈ Ω, ContDiffAt ℝ 1 (fun p : (ℝ × ℝ) × V ↦ J p.1 p.2) (z, u z))
    (hJJ : ∀ z ∈ Ω, J z (u z) ∘L J z (u z) = -ContinuousLinearMap.id ℝ V)
    (hu : ContDiffOn ℝ 1 u Ω) :
    let e := Complex.equivRealProdCLM
    IsOpen (e ⁻¹' Ω) ∧ IsPreconnected (e ⁻¹' Ω) ∧
      ContDiffOn ℝ 1 (fun w ↦ J (e w) (u (e w))) (e ⁻¹' Ω) ∧
      ∀ w ∈ e ⁻¹' Ω, J (e w) (u (e w)) ∘L J (e w) (u (e w)) = -ContinuousLinearMap.id ℝ V := by
  intro e
  refine ⟨hΩ.preimage e.continuous, (e.toHomeomorph.isPreconnected_preimage).2 hΩc,
    fun w hw ↦ ?_, fun w hw ↦ hJJ (e w) hw⟩
  have hgraph : ContDiffAt ℝ 1 (fun w ↦ (e w, u (e w))) w :=
    e.contDiff.contDiffAt.prodMk
      ((hu.contDiffAt (hΩ.mem_nhds hw)).comp w e.contDiff.contDiffAt)
  exact ((hJ (e w) hw).comp w hgraph).contDiffWithinAt

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
  obtain ⟨hΩ', hΩc', hJ', hJJ'⟩ := complexCoordinate_structure hΩ hΩc hJ hJJ hu
  have hC : ContinuousOn (fun w ↦ ω.floerLinearizationCoeff J Ks Kt u (e w)) (e ⁻¹' Ω) :=
    (ω.continuousOn_floerLinearizationCoeff hJ hKs hKt
      fun z hz ↦ hu.contDiffAt (hΩ.mem_nhds hz)).comp e.continuous.continuousOn
      (mapsTo_preimage _ _)
  refine ⟨hΩ', hΩc', hJ', hJJ', hξ.comp_continuousLinearMap (e : ℂ →L[ℝ] ℝ × ℝ),
    hC.aestronglyMeasurable hΩ'.measurableSet, fun w hw ↦ ?_, fun w hw ↦ ?_⟩
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

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- In the complex coordinate the vanishing order at `z₀` is measured by
`‖e w - e w₀‖ ≤ ‖e‖ ‖w - w₀‖`, so a zero of infinite order stays one. -/
private theorem isBigO_comp_equivRealProdCLM {z₀ : ℝ × ℝ}
    (h₀ : ∀ n : ℕ, ξ =O[𝓝 z₀] fun z ↦ ‖z - z₀‖ ^ n) (n : ℕ) :
    (ξ ∘ Complex.equivRealProdCLM) =O[𝓝 (Complex.equivRealProdCLM.symm z₀)]
      fun w ↦ (w - Complex.equivRealProdCLM.symm z₀) ^ n := by
  set e := Complex.equivRealProdCLM
  have h := (h₀ n).comp_tendsto
    ((e.continuous.tendsto (e.symm z₀)).trans_eq (by rw [e.apply_symm_apply]))
  refine h.trans (IsBigO.of_bound (‖(e : ℂ →L[ℝ] ℝ × ℝ)‖ ^ n) (Eventually.of_forall fun w ↦ ?_))
  have hw : e w - z₀ = e (w - e.symm z₀) := by simp
  simp only [comp_apply, hw, norm_pow, norm_norm, ← mul_pow]
  gcongr
  exact (e : ℂ →L[ℝ] ℝ × ℝ).le_opNorm _

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- A set whose preimage is codiscrete within `e ⁻¹' Ω` in the complex coordinate
`e = Complex.equivRealProdCLM` is codiscrete within `Ω`. -/
private theorem setOf_ne_zero_mem_codiscreteWithin_of_comp_equivRealProdCLM
    (h : {w | (ξ ∘ Complex.equivRealProdCLM) w ≠ 0} ∈
      codiscreteWithin (Complex.equivRealProdCLM ⁻¹' Ω)) :
    {z | ξ z ≠ 0} ∈ codiscreteWithin Ω := by
  set e := Complex.equivRealProdCLM
  have := (e.toHomeomorph.isEmbedding.image_mem_codiscreteWithin
    (s := e ⁻¹' {z | ξ z ≠ 0}) (t := e ⁻¹' Ω)).2 h
  simpa only [ContinuousLinearEquiv.coe_toHomeomorph,
    image_preimage_eq _ e.surjective] using this

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
  exact eqOn_zero_of_eqOn_zero_comp_equivRealProdCLM <|
    eqOn_zero_of_contDiffOn_of_forall_isBigO_of_complexStructure hΩ' hΩc' hJ' hJJ' hξ' hCm hCb
      heq (show e.symm z₀ ∈ e ⁻¹' Ω by rwa [mem_preimage, e.apply_symm_apply])
      (isBigO_comp_equivRealProdCLM h₀)

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
  exact setOf_ne_zero_mem_codiscreteWithin_of_comp_equivRealProdCLM h

/-! ### Pairs of solutions of the Floer equation -/

section Pair

variable {v : ℝ × ℝ → V}

/-- The zeroth-order part of the difference of the Floer operators of `u` and `v`: the
operator of `u` minus that of `v` is `∂ₛ(u - v) + J(z, u z) ∂ₜ(u - v)` minus this defect
(`floerOperator_sub_floerOperator`). It vanishes where `u` and `v` agree. -/
private noncomputable def pairDefect (ω : SymplecticForm V) (J : ℝ × ℝ → V → V →L[ℝ] V)
    (Ks Kt : ℝ × ℝ → V → ℝ) (u v : ℝ × ℝ → V) (z : ℝ × ℝ) : V :=
  (ω.hamiltonianVectorField (Ks z) (u z) - ω.hamiltonianVectorField (Ks z) (v z)) +
    J z (u z) (ω.hamiltonianVectorField (Kt z) (u z) - ω.hamiltonianVectorField (Kt z) (v z)) -
    (J z (u z) - J z (v z))
      (fderiv ℝ v z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (v z))

/-- The difference of the Floer operators of two maps differentiable at `z`. -/
private theorem floerOperator_sub_floerOperator {z : ℝ × ℝ} (hu : DifferentiableAt ℝ u z)
    (hv : DifferentiableAt ℝ v z) :
    ω.floerOperator J Ks Kt u z - ω.floerOperator J Ks Kt v z =
      fderiv ℝ (u - v) z stdComplexLineReal + J z (u z) (fderiv ℝ (u - v) z stdComplexLineImag) -
        pairDefect ω J Ks Kt u v z := by
  rw [fderiv_sub hu hv]
  simp only [floerOperator_def, pairDefect, _root_.sub_apply, map_sub]
  abel

/-- The defect vanishes where `u` and `v` agree. -/
private theorem pairDefect_eq_zero {z : ℝ × ℝ} (h : u z = v z) :
    pairDefect ω J Ks Kt u v z = 0 := by
  simp [pairDefect, h]

/-- The defect is continuous where the data are continuous along both maps. -/
private theorem continuousAt_pairDefect {z : ℝ × ℝ}
    (hJ : ContinuousAt (fun p : (ℝ × ℝ) × V ↦ J p.1 p.2) (z, u z))
    (hJv : ContinuousAt (fun p : (ℝ × ℝ) × V ↦ J p.1 p.2) (z, v z))
    (hKs : ContDiffAt ℝ 1 (uncurry Ks) (z, u z)) (hKt : ContDiffAt ℝ 1 (uncurry Kt) (z, u z))
    (hKsv : ContDiffAt ℝ 1 (uncurry Ks) (z, v z)) (hKtv : ContDiffAt ℝ 1 (uncurry Kt) (z, v z))
    (hu : ContinuousAt u z) (hv : ContinuousAt v z)
    (hdv : ContinuousAt (fun z' ↦ fderiv ℝ v z' stdComplexLineImag) z) :
    ContinuousAt (pairDefect ω J Ks Kt u v) z := by
  -- The Hamiltonian vector fields along a map are continuous where the Hamiltonians are `C¹`.
  have hX {K : ℝ × ℝ → V → ℝ} {f : ℝ × ℝ → V} (hK : ContDiffAt ℝ 1 (uncurry K) (z, f z))
      (hf : ContinuousAt f z) :
      ContinuousAt (fun z' ↦ ω.hamiltonianVectorField (K z') (f z')) z :=
    (ω.contDiffAt_hamiltonianVectorField_uncurry (n := 0) (by simpa using hK)).continuousAt.comp
      (f := fun z' ↦ (z', f z')) (continuousAt_id.prodMk hf)
  have hJu : ContinuousAt (fun z' ↦ J z' (u z')) z :=
    hJ.comp (f := fun z' ↦ (z', u z')) (continuousAt_id.prodMk hu)
  have hJv' : ContinuousAt (fun z' ↦ J z' (v z')) z :=
    hJv.comp (f := fun z' ↦ (z', v z')) (continuousAt_id.prodMk hv)
  exact (((hX hKs hu).sub (hX hKsv hv)).add (hJu.clm_apply ((hX hKt hu).sub (hX hKtv hv)))).sub
    ((hJu.sub hJv').clm_apply (hdv.sub (hX hKtv hv)))

/-- Near a point where `u` and `v` agree, the defect is bounded by a multiple of `‖u - v‖`. -/
private theorem exists_eventually_norm_pairDefect_le {z : ℝ × ℝ}
    (hJ : ContDiffAt ℝ 1 (fun p : (ℝ × ℝ) × V ↦ J p.1 p.2) (z, u z))
    (hKs : ContDiffAt ℝ 2 (uncurry Ks) (z, u z)) (hKt : ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ContinuousAt u z) (hv : ContinuousAt v z)
    (hdv : ContinuousAt (fun z' ↦ fderiv ℝ v z' stdComplexLineImag) z) (huv : u z = v z) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ z' in 𝓝 z, ‖pairDefect ω J Ks Kt u v z'‖ ≤ M * ‖u z' - v z'‖ := by
  have hd : ContinuousAt (fun z' ↦ fderiv ℝ v z' stdComplexLineImag -
      ω.hamiltonianVectorField (Kt z') (v z')) z :=
    hdv.sub ((ω.contDiffAt_hamiltonianVectorField_uncurry (n := 1) hKt).continuousAt.comp_of_eq
      (f := fun z' ↦ (z', v z')) (continuousAt_id.prodMk hv) (by simp [huv]))
  obtain ⟨Ls, hLs⟩ :=
    (ω.contDiffAt_hamiltonianVectorField_uncurry (n := 1) hKs).exists_eventually_norm_sub_le hu hv
      huv
  obtain ⟨Lt, hLt⟩ :=
    (ω.contDiffAt_hamiltonianVectorField_uncurry (n := 1) hKt).exists_eventually_norm_sub_le hu hv
      huv
  obtain ⟨LJ, hLJ⟩ := hJ.exists_eventually_norm_sub_le hu hv huv
  have hJu : ContinuousAt (fun z' ↦ J z' (u z')) z :=
    hJ.continuousAt.comp (f := fun z' ↦ (z', u z')) (continuousAt_id.prodMk hu)
  set A := ‖J z (u z)‖ + 1
  set B := ‖fderiv ℝ v z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (v z)‖ + 1
  refine ⟨Ls + A * Lt + LJ * B, by positivity, ?_⟩
  filter_upwards [hLs, hLt, hLJ, hJu.norm.eventually (gt_mem_nhds (lt_add_one _)),
    hd.norm.eventually (gt_mem_nhds (lt_add_one _))] with z' hs ht hJd hA hB
  -- The triangle inequality on the three terms of the defect.
  calc ‖pairDefect ω J Ks Kt u v z'‖
      ≤ ‖ω.hamiltonianVectorField (Ks z') (u z') - ω.hamiltonianVectorField (Ks z') (v z')‖ +
          ‖J z' (u z')‖ * ‖ω.hamiltonianVectorField (Kt z') (u z') -
            ω.hamiltonianVectorField (Kt z') (v z')‖ +
          ‖J z' (u z') - J z' (v z')‖ * ‖fderiv ℝ v z' stdComplexLineImag -
            ω.hamiltonianVectorField (Kt z') (v z')‖ := by
        refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans ?_) ?_) <;>
          first | exact add_le_add le_rfl (ContinuousLinearMap.le_opNorm _ _) |
            exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ Ls * ‖u z' - v z'‖ + A * (Lt * ‖u z' - v z'‖) + LJ * ‖u z' - v z'‖ * B := by
        gcongr
    _ = (Ls + A * Lt + LJ * B) * ‖u z' - v z'‖ := by ring

/-- In the complex coordinate `z = Complex.equivRealProdCLM w`, the difference `u - v` of two
solutions of the Floer equation on a connected open set `Ω` solves a linear Cauchy–Riemann
equation for the structure `J(z, u z)`, with a measurable and locally bounded coefficient, on the
connected open set `e ⁻¹' Ω`. -/
private theorem floerOperator_sub_complexCoordinate (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hJ : ∀ z ∈ Ω, ContDiffAt ℝ 1 (fun p : (ℝ × ℝ) × V ↦ J p.1 p.2) (z, u z))
    (hJv : ∀ z ∈ Ω, ContinuousAt (fun p : (ℝ × ℝ) × V ↦ J p.1 p.2) (z, v z))
    (hJJ : ∀ z ∈ Ω, J z (u z) ∘L J z (u z) = -ContinuousLinearMap.id ℝ V)
    (hKs : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hKsv : ∀ z ∈ Ω, ContDiffAt ℝ 1 (uncurry Ks) (z, v z))
    (hKtv : ∀ z ∈ Ω, ContDiffAt ℝ 1 (uncurry Kt) (z, v z)) (hu : ContDiffOn ℝ 1 u Ω)
    (hv : ContDiffOn ℝ 1 v Ω) (hFu : ∀ z ∈ Ω, ω.floerOperator J Ks Kt u z = 0)
    (hFv : ∀ z ∈ Ω, ω.floerOperator J Ks Kt v z = 0) :
    let e := Complex.equivRealProdCLM
    IsOpen (e ⁻¹' Ω) ∧ IsPreconnected (e ⁻¹' Ω) ∧
      ContDiffOn ℝ 1 (fun w ↦ J (e w) (u (e w))) (e ⁻¹' Ω) ∧
      (∀ w ∈ e ⁻¹' Ω, J (e w) (u (e w)) ∘L J (e w) (u (e w)) = -ContinuousLinearMap.id ℝ V) ∧
      ContDiffOn ℝ 1 ((u - v) ∘ e) (e ⁻¹' Ω) ∧
      ∃ C : ℂ → V →L[ℝ] V, AEStronglyMeasurable C (volume.restrict (e ⁻¹' Ω)) ∧
        (∀ w ∈ e ⁻¹' Ω, ∃ M, ∀ᶠ w' in 𝓝 w, ‖C w'‖ ≤ M) ∧
        ∀ w ∈ e ⁻¹' Ω, fderiv ℝ ((u - v) ∘ e) w 1 +
          J (e w) (u (e w)) (fderiv ℝ ((u - v) ∘ e) w I) + C w (((u - v) ∘ e) w) = 0 := by
  intro e
  obtain ⟨hΩ', hΩc', hJ', hJJ'⟩ := complexCoordinate_structure hΩ hΩc hJ hJJ hu
  have huc (z) (hz : z ∈ Ω) : ContinuousAt u z := hu.continuousOn.continuousAt (hΩ.mem_nhds hz)
  have hvc (z) (hz : z ∈ Ω) : ContinuousAt v z := hv.continuousOn.continuousAt (hΩ.mem_nhds hz)
  have hdv (z) (hz : z ∈ Ω) : ContinuousAt (fun z' ↦ fderiv ℝ v z' stdComplexLineImag) z :=
    ((hv.continuousOn_fderiv_of_isOpen hΩ le_rfl).continuousAt (hΩ.mem_nhds hz)).clm_apply
      continuousAt_const
  have hg (z) (hz : z ∈ Ω) : ContinuousAt (pairDefect ω J Ks Kt u v) z :=
    continuousAt_pairDefect (hJ z hz).continuousAt (hJv z hz) ((hKs z hz).of_le one_le_two)
      ((hKt z hz).of_le one_le_two) (hKsv z hz) (hKtv z hz) (huc z hz) (hvc z hz) (hdv z hz)
  -- The ratio `‖g‖ / ‖u - v‖` of the defect is locally bounded: by continuity where `u ≠ v`,
  -- and by the Lipschitz bound of the data where `u = v`.
  have hbd (z) (hz : z ∈ Ω) :
      ∃ M, ∀ᶠ z' in 𝓝 z, ‖pairDefect ω J Ks Kt u v z'‖ / ‖u z' - v z'‖ ≤ M := by
    by_cases huv : u z = v z
    · obtain ⟨M, hM0, hM⟩ := exists_eventually_norm_pairDefect_le (hJ z hz) (hKs z hz)
        (hKt z hz) (huc z hz) (hvc z hz) (hdv z hz) huv
      exact ⟨M, hM.mono fun _ h ↦ div_le_of_le_mul₀ (norm_nonneg _) hM0 h⟩
    · have hc : ContinuousAt (fun z' ↦ ‖pairDefect ω J Ks Kt u v z'‖ / ‖u z' - v z'‖) z :=
        (hg z hz).norm.div ((huc z hz).sub (hvc z hz)).norm
          (norm_ne_zero_iff.2 (sub_ne_zero.2 huv))
      exact ⟨_, (hc.eventually (gt_mem_nhds (lt_add_one _))).mono fun _ h ↦ h.le⟩
  -- The coefficient carries `u - v` to minus the defect.
  have hgm : AEStronglyMeasurable (fun w ↦ -pairDefect ω J Ks Kt u v (e w))
      (volume.restrict (e ⁻¹' Ω)) :=
    (ContinuousOn.neg fun w hw ↦ ((hg (e w) hw).comp e.continuous.continuousAt).continuousWithinAt
      ).aestronglyMeasurable hΩ'.measurableSet
  have hξc : ContinuousOn ((u - v) ∘ e) (e ⁻¹' Ω) :=
    (hu.continuousOn.sub hv.continuousOn).comp e.continuous.continuousOn (mapsTo_preimage _ _)
  obtain ⟨c, hc0, C, hCm, hCx, hCn⟩ := hgm.exists_clm_apply_eq (𝕜 := ℝ)
    (hξc.aestronglyMeasurable hΩ'.measurableSet) fun w h ↦ by
      rw [pairDefect_eq_zero (sub_eq_zero.1 h), neg_zero]
  refine ⟨hΩ', hΩc', hJ', hJJ', (hu.sub hv).comp_continuousLinearMap (e : ℂ →L[ℝ] ℝ × ℝ), C, hCm,
    fun w hw ↦ ?_, fun w hw ↦ ?_⟩
  · obtain ⟨M, hM⟩ := hbd (e w) hw
    refine ⟨c * M, ((e.continuous.tendsto w).eventually hM).mono fun w' h ↦ ?_⟩
    refine (hCn w').trans ?_
    simpa only [norm_neg, comp_apply, Pi.sub_apply] using mul_le_mul_of_nonneg_left h hc0
  · have hd := floerOperator_sub_floerOperator (ω := ω) (J := J) (Ks := Ks) (Kt := Kt)
      ((hu.differentiableOn one_ne_zero (e w) hw).differentiableAt (hΩ.mem_nhds hw))
      ((hv.differentiableOn one_ne_zero (e w) hw).differentiableAt (hΩ.mem_nhds hw))
    rw [hFu (e w) hw, hFv (e w) hw, sub_zero] at hd
    rw [hCx w, fderiv_comp_equivRealProdCLM_one, fderiv_comp_equivRealProdCLM_I, ← sub_eq_add_neg,
      ← hd]

/-- **Unique continuation for pairs of Floer solutions.** Let `u` and `v` be `C¹` solutions of the
Floer equation `∂ₛu - X_{K_s}(u) + J(z, u)(∂ₜu - X_{K_t}(u)) = 0` on a connected open set
`Ω ⊆ ℝ × ℝ`, with `J(z, u z)² = -1` on `Ω`, the field `J` of class `C¹` and the Hamiltonians of
class `C²` near the graph of `u`, and `J` continuous and the Hamiltonians `C¹` near the graph of
`v`. If `u` and `v` agree on a nonempty open subset of `Ω`, they agree on `Ω`. -/
theorem eqOn_of_floerOperator_eq_zero_of_eqOn (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hJ : ∀ z ∈ Ω, ContDiffAt ℝ 1 (fun p : (ℝ × ℝ) × V ↦ J p.1 p.2) (z, u z))
    (hJv : ∀ z ∈ Ω, ContinuousAt (fun p : (ℝ × ℝ) × V ↦ J p.1 p.2) (z, v z))
    (hJJ : ∀ z ∈ Ω, J z (u z) ∘L J z (u z) = -ContinuousLinearMap.id ℝ V)
    (hKs : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hKsv : ∀ z ∈ Ω, ContDiffAt ℝ 1 (uncurry Ks) (z, v z))
    (hKtv : ∀ z ∈ Ω, ContDiffAt ℝ 1 (uncurry Kt) (z, v z)) (hu : ContDiffOn ℝ 1 u Ω)
    (hv : ContDiffOn ℝ 1 v Ω) (hFu : ∀ z ∈ Ω, ω.floerOperator J Ks Kt u z = 0)
    (hFv : ∀ z ∈ Ω, ω.floerOperator J Ks Kt v z = 0) {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hUne : U.Nonempty) (hUΩ : U ⊆ Ω) (huv : EqOn u v U) : EqOn u v Ω := by
  obtain ⟨hΩ', hΩc', hJ', hJJ', hξ', C, hCm, hCb, heq⟩ := floerOperator_sub_complexCoordinate hΩ
    hΩc hJ hJv hJJ hKs hKt hKsv hKtv hu hv hFu hFv
  set e := Complex.equivRealProdCLM
  obtain ⟨z₁, hz₁⟩ := hUne
  have h := eqOn_zero_of_eqOn_zero_comp_equivRealProdCLM (ξ := u - v) <|
    eqOn_zero_of_contDiffOn_of_eqOn_zero_of_complexStructure hΩ' hΩc' hJ' hJJ' hξ' hCm hCb heq
      (hU.preimage e.continuous) ⟨e.symm z₁, by simpa using hz₁⟩ (preimage_mono hUΩ)
      fun w hw ↦ sub_eq_zero.2 (huv hw)
  exact fun z hz ↦ sub_eq_zero.1 (h hz)

/-- **Unique continuation from a point of infinite contact for pairs of Floer solutions.** Under
the hypotheses of `eqOn_of_floerOperator_eq_zero_of_eqOn`, if `u - v = O(‖z - z₀‖ⁿ)` near one
point `z₀ ∈ Ω` for every `n`, then `u` and `v` agree on `Ω`. -/
theorem eqOn_of_floerOperator_eq_zero_of_forall_isBigO (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hJ : ∀ z ∈ Ω, ContDiffAt ℝ 1 (fun p : (ℝ × ℝ) × V ↦ J p.1 p.2) (z, u z))
    (hJv : ∀ z ∈ Ω, ContinuousAt (fun p : (ℝ × ℝ) × V ↦ J p.1 p.2) (z, v z))
    (hJJ : ∀ z ∈ Ω, J z (u z) ∘L J z (u z) = -ContinuousLinearMap.id ℝ V)
    (hKs : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hKsv : ∀ z ∈ Ω, ContDiffAt ℝ 1 (uncurry Ks) (z, v z))
    (hKtv : ∀ z ∈ Ω, ContDiffAt ℝ 1 (uncurry Kt) (z, v z)) (hu : ContDiffOn ℝ 1 u Ω)
    (hv : ContDiffOn ℝ 1 v Ω) (hFu : ∀ z ∈ Ω, ω.floerOperator J Ks Kt u z = 0)
    (hFv : ∀ z ∈ Ω, ω.floerOperator J Ks Kt v z = 0) {z₀ : ℝ × ℝ} (hz₀ : z₀ ∈ Ω)
    (h₀ : ∀ n : ℕ, (u - v) =O[𝓝 z₀] fun z ↦ ‖z - z₀‖ ^ n) : EqOn u v Ω := by
  obtain ⟨hΩ', hΩc', hJ', hJJ', hξ', C, hCm, hCb, heq⟩ := floerOperator_sub_complexCoordinate hΩ
    hΩc hJ hJv hJJ hKs hKt hKsv hKtv hu hv hFu hFv
  set e := Complex.equivRealProdCLM
  have h := eqOn_zero_of_eqOn_zero_comp_equivRealProdCLM (ξ := u - v) <|
    eqOn_zero_of_contDiffOn_of_forall_isBigO_of_complexStructure hΩ' hΩc' hJ' hJJ' hξ' hCm hCb
      heq (show e.symm z₀ ∈ e ⁻¹' Ω by rwa [mem_preimage, e.apply_symm_apply])
      (isBigO_comp_equivRealProdCLM h₀)
  exact fun z hz ↦ sub_eq_zero.1 (h hz)

/-- **Isolated coincidences of Floer solutions.** Under the hypotheses of
`eqOn_of_floerOperator_eq_zero_of_eqOn`, if `u` and `v` differ somewhere on `Ω`, then the points
of `Ω` where they agree form a discrete subset of `Ω`. -/
theorem setOf_ne_mem_codiscreteWithin_of_floerOperator_eq_zero (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω)
    (hJ : ∀ z ∈ Ω, ContDiffAt ℝ 1 (fun p : (ℝ × ℝ) × V ↦ J p.1 p.2) (z, u z))
    (hJv : ∀ z ∈ Ω, ContinuousAt (fun p : (ℝ × ℝ) × V ↦ J p.1 p.2) (z, v z))
    (hJJ : ∀ z ∈ Ω, J z (u z) ∘L J z (u z) = -ContinuousLinearMap.id ℝ V)
    (hKs : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ Ω, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hKsv : ∀ z ∈ Ω, ContDiffAt ℝ 1 (uncurry Ks) (z, v z))
    (hKtv : ∀ z ∈ Ω, ContDiffAt ℝ 1 (uncurry Kt) (z, v z)) (hu : ContDiffOn ℝ 1 u Ω)
    (hv : ContDiffOn ℝ 1 v Ω) (hFu : ∀ z ∈ Ω, ω.floerOperator J Ks Kt u z = 0)
    (hFv : ∀ z ∈ Ω, ω.floerOperator J Ks Kt v z = 0) (hne : ∃ z ∈ Ω, u z ≠ v z) :
    {z | u z ≠ v z} ∈ codiscreteWithin Ω := by
  obtain ⟨hΩ', hΩc', hJ', hJJ', hξ', C, hCm, hCb, heq⟩ := floerOperator_sub_complexCoordinate hΩ
    hΩc hJ hJv hJJ hKs hKt hKsv hKtv hu hv hFu hFv
  set e := Complex.equivRealProdCLM
  obtain ⟨z₁, hz₁, huv⟩ := hne
  have h := setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn_of_complexStructure hΩ' hΩc' hJ'
    hJJ' hξ' hCm hCb heq ⟨e.symm z₁, by simpa using hz₁, by simpa [sub_eq_zero] using huv⟩
  simpa only [Pi.sub_apply, ne_eq, sub_eq_zero] using
    setOf_ne_zero_mem_codiscreteWithin_of_comp_equivRealProdCLM (ξ := u - v) h

end Pair

/-! ### Translates of Floer trajectories -/

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
    (hUc : EqOn u (fun z ↦ u (z + (c, 0))) U) : Periodic u (c, 0) := by
  -- The translate solves the same equation, because the data do not depend on `s`.
  have hFc (z) : ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2)
      (fun z ↦ u (z + (c, 0))) z = 0 := by
    have h := ω.floerOperator_comp_sub J H u (-c) z
    have he : (fun w ↦ u (w - (-c, 0))) = fun w ↦ u (w + (c, 0)) := by
      ext w
      rw [sub_eq_add_neg, Prod.neg_mk, neg_neg, neg_zero]
    rw [he] at h
    rw [h, hF]
  have hJ' : ContDiff ℝ 1 (fun p : (ℝ × ℝ) × V ↦ J p.1.2 p.2) :=
    hJ.comp ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd)
  have hKs : ContDiff ℝ 2 (uncurry fun (_ : ℝ × ℝ) (_ : V) ↦ (0 : ℝ)) := contDiff_const
  have hKt : ContDiff ℝ 2 (uncurry fun (p : ℝ × ℝ) ↦ H p.2) :=
    hH.comp ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd)
  intro z
  exact (eqOn_of_floerOperator_eq_zero_of_eqOn isOpen_univ isPreconnected_univ
    (fun _ _ ↦ hJ'.contDiffAt) (fun _ _ ↦ hJ'.continuous.continuousAt) (fun z _ ↦ hJJ z)
    (fun _ _ ↦ hKs.contDiffAt) (fun _ _ ↦ hKt.contDiffAt)
    (fun _ _ ↦ (hKs.of_le one_le_two).contDiffAt) (fun _ _ ↦ (hKt.of_le one_le_two).contDiffAt)
    hu.contDiffOn (hu.comp (contDiff_id.add contDiff_const)).contDiffOn (fun z _ ↦ hF z)
    (fun z _ ↦ hFc z) hU hUne (subset_univ U) hUc (mem_univ z)).symm

end TauCeti.SymplecticForm
