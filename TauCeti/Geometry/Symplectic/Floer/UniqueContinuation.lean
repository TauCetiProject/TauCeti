/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Linearization
public import TauCeti.Geometry.Symplectic.JHolomorphic.UniqueContinuation
import TauCeti.Analysis.Calculus.Hadamard

/-!
# Unique continuation for the Floer equation

Let `(V, ω)` be a finite-dimensional symplectic vector space, `K = K_s ds + K_t dt` a
domain-dependent Hamiltonian perturbation and `J(z, y)` a family of endomorphisms of `V` on the
domain `ℝ × ℝ`. This file proves unique continuation for the Floer equation and its linearization
on a connected open set `Ω` of the domain. The data `J`, `K_s` and `K_t` are only required to be
regular near the points `(z, u z)` of the graph of the map `u` under consideration, so the results
apply to data defined on an open subset of `(ℝ × ℝ) × V`, as for punctured domains or in charts of
the target.

* **The linearized operator.** Along a map `u`, the linearized Floer operator is
  `D_u ξ = ∂ₛξ + J(z, u z) ∂ₜξ + S(z) ξ` (`TauCeti.SymplecticForm.floerLinearization_eq_add`),
  with a zeroth-order coefficient `S` continuous when the data are `C¹` (the Hamiltonians `C²`).
  If `J(z, u z)² = -1`, a solution of `D_u ξ = 0` on `Ω` vanishing to infinite order at one point
  of `Ω`, or on a nonempty open subset of `Ω`, vanishes on `Ω`
  (`TauCeti.SymplecticForm.eqOn_zero_of_floerLinearization_eq_zero_of_forall_isBigO`,
  `TauCeti.SymplecticForm.eqOn_zero_of_floerLinearization_eq_zero_of_eqOn_zero`), and otherwise
  its zeros are isolated
  (`TauCeti.SymplecticForm.setOf_ne_zero_mem_codiscreteWithin_of_floerLinearization_eq_zero`).
* **The nonlinear equation.** For `C¹` maps `u` and `v`, the difference of their Floer operators is
  `∂ₛξ + J(z, v z) ∂ₜξ + C(z) ξ` for `ξ = v - u` and a coefficient `C` continuous on `Ω`
  (`TauCeti.SymplecticForm.exists_continuousOn_floerOperator_sub_floerOperator_eq`), when the
  data are regular near the segments from `u z` to `v z`. It is assembled from the averaged
  derivatives `∫₀¹ dF(u + τ ξ) dτ` (`hadamardFactor`) of `F = X_{K_s}`, `X_{K_t}` and `J` along
  these segments, which turn the differences `F(v) - F(u)` into linear expressions in `ξ`. Near a
  point where `u` and `v` agree these segments are short, so regularity of the data near the graph
  of `v` suffices for two solutions of the Floer equation on `Ω`: if they agree to infinite order
  at one point of `Ω`, or on a nonempty open subset of `Ω`, they agree on `Ω`
  (`TauCeti.SymplecticForm.eqOn_of_floerOperator_eq_zero_of_forall_isBigO`,
  `TauCeti.SymplecticForm.eqOn_of_floerOperator_eq_zero_of_eqOn`), and otherwise the points where
  they agree are isolated
  (`TauCeti.SymplecticForm.setOf_ne_mem_codiscreteWithin_of_floerOperator_eq_zero`).

Both reduce to unique continuation for linear Cauchy–Riemann equations with a variable complex
structure in the coordinates `(s, t)` of the domain
(`TauCeti.Geometry.Symplectic.JHolomorphic.UniqueContinuation`), a consequence of the Carleman
similarity principle.

In the transversality argument for moduli spaces of Floer solutions, localized Hamiltonian
variations show that an element of the cokernel of the universal linearized operator vanishes on
an open subset of a compact core
(`TauCeti.SymplecticForm.eqOn_zero_of_forall_integral_apply_floerOperator_add_sub_eq_zero`). For an
inner product on `V`, the formal `L²` adjoint of `D_u` is, up to sign, again of the form
`∂ₛ + J' ∂ₜ + C'`, with `J'` the transpose of `J(z, u z)`, also a complex structure. Such cokernel
elements are a priori only weak `L^q` solutions of the adjoint equation. Once elliptic regularity,
which is not proved here, shows that they are `C¹` classical solutions, the unique continuation
theorems in the coordinates `(s, t)` extend that vanishing to the whole connected domain. Unique
continuation and isolated coincidences for the nonlinear equation underlie the reduction of Floer
solutions to their simple images.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.3 (unique continuation) and Section 8.1 (Floer's equation).
* A. Floer, H. Hofer and D. Salamon, *Transversality in elliptic Morse theory for the symplectic
  action*, Duke Math. J. 80 (1995), 251–292.
-/

public section

open Complex ContinuousLinearMap MeasureTheory Metric Set Filter Topology Asymptotics

namespace TauCeti

namespace SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-! ### The linearized operator -/

/-- **Unique continuation for the linearized Floer operator from a zero of infinite order.** Let
`u` and `ξ` be `C¹` on a connected open set `Ω` of the domain, and let the endomorphisms `J` be
`C¹` and the Hamiltonians `K_s`, `K_t` be `C²` at the points `(z, u z)`, `z ∈ Ω`, jointly in the
domain and target point, with `J(z, u z)² = -1`. If `D_u ξ = 0` on `Ω` and
`ξ = O(‖z - z₀‖ⁿ)` near a point `z₀ ∈ Ω` for every `n`, then `ξ` vanishes on `Ω`. -/
theorem eqOn_zero_of_floerLinearization_eq_zero_of_forall_isBigO (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u ξ : ℝ × ℝ → V}
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hJ : ∀ z ∈ Ω, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z ∈ Ω, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ Ω, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z))
    (hu : ContDiffOn ℝ 1 u Ω) (hξ : ContDiffOn ℝ 1 ξ Ω)
    (hJsq : ∀ z ∈ Ω, J z (u z) ∘L J z (u z) = -ContinuousLinearMap.id ℝ V)
    (hD : ∀ z ∈ Ω, ω.floerLinearization J Ks Kt u ξ z = 0) {z₀ : ℝ × ℝ} (hz₀ : z₀ ∈ Ω)
    (h₀ : ∀ n : ℕ, ξ =O[𝓝 z₀] fun z ↦ ‖z - z₀‖ ^ n) : EqOn ξ 0 Ω := by
  have hu' (z : ℝ × ℝ) (hz : z ∈ Ω) : ContDiffAt ℝ 1 u z := hu.contDiffAt (hΩ.mem_nhds hz)
  have hC := ω.continuousOn_floerLinearizationCoeff hJ hKs hKt hu'
  refine eqOn_zero_of_contDiffOn_prod_of_comp_eq_neg_id_of_forall_isBigO
    (J := fun z ↦ J z (u z)) (C := ω.floerLinearizationCoeff J Ks Kt u) hΩ hΩc hξ
    (fun z hz ↦ ?_) hJsq (hC.aestronglyMeasurable hΩ.measurableSet) (fun z hz ↦ ⟨_, (hC.continuousAt
      (hΩ.mem_nhds hz)).norm.eventually (Iic_mem_nhds (lt_add_one _))⟩) (fun z hz ↦ ?_) hz₀ h₀
  · exact ((hJ z hz).comp z (contDiffAt_id.prodMk (hu' z hz))).contDiffWithinAt
  · rw [← floerLinearization_eq_add]
    exact hD z hz

/-- **Unique continuation for the linearized Floer operator.** Let `u` and `ξ` be `C¹` on a
connected open set `Ω` of the domain, and let the endomorphisms `J` be `C¹` and the Hamiltonians
`K_s`, `K_t` be `C²` at the points `(z, u z)`, `z ∈ Ω`, jointly in the domain and target point, with
`J(z, u z)² = -1`. If `D_u ξ = 0` on `Ω` and `ξ` vanishes on a nonempty open subset of `Ω`, then
`ξ` vanishes on `Ω`. -/
theorem eqOn_zero_of_floerLinearization_eq_zero_of_eqOn_zero (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u ξ : ℝ × ℝ → V}
    {Ω U : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hJ : ∀ z ∈ Ω, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z ∈ Ω, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ Ω, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z))
    (hu : ContDiffOn ℝ 1 u Ω) (hξ : ContDiffOn ℝ 1 ξ Ω)
    (hJsq : ∀ z ∈ Ω, J z (u z) ∘L J z (u z) = -ContinuousLinearMap.id ℝ V)
    (hD : ∀ z ∈ Ω, ω.floerLinearization J Ks Kt u ξ z = 0)
    (hU : IsOpen U) (hUne : U.Nonempty) (hUΩ : U ⊆ Ω) (h₀ : EqOn ξ 0 U) : EqOn ξ 0 Ω := by
  obtain ⟨z₀, hz₀⟩ := hUne
  refine ω.eqOn_zero_of_floerLinearization_eq_zero_of_forall_isBigO hΩ hΩc hJ hKs hKt hu hξ hJsq
    hD (hUΩ hz₀) fun n ↦ ?_
  exact (isBigO_zero _ _).congr' (eventuallyEq_of_mem (hU.mem_nhds hz₀) fun z hz ↦ (h₀ hz).symm)
    EventuallyEq.rfl

/-- **Isolated zeros for the linearized Floer operator.** Let `u` and `ξ` be `C¹` on a connected
open set `Ω` of the domain, and let the endomorphisms `J` be `C¹` and the Hamiltonians `K_s`, `K_t`
be `C²` at the points `(z, u z)`, `z ∈ Ω`, jointly in the domain and target point, with
`J(z, u z)² = -1`. If `D_u ξ = 0` on `Ω` and `ξ` is not identically zero on `Ω`, its zeros form a
discrete subset of `Ω`. -/
theorem setOf_ne_zero_mem_codiscreteWithin_of_floerLinearization_eq_zero (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u ξ : ℝ × ℝ → V}
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hJ : ∀ z ∈ Ω, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z ∈ Ω, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ Ω, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z))
    (hu : ContDiffOn ℝ 1 u Ω) (hξ : ContDiffOn ℝ 1 ξ Ω)
    (hJsq : ∀ z ∈ Ω, J z (u z) ∘L J z (u z) = -ContinuousLinearMap.id ℝ V)
    (hD : ∀ z ∈ Ω, ω.floerLinearization J Ks Kt u ξ z = 0) (hne : ∃ z ∈ Ω, ξ z ≠ 0) :
    {z | ξ z ≠ 0} ∈ codiscreteWithin Ω := by
  have hu' (z : ℝ × ℝ) (hz : z ∈ Ω) : ContDiffAt ℝ 1 u z := hu.contDiffAt (hΩ.mem_nhds hz)
  have hC := ω.continuousOn_floerLinearizationCoeff hJ hKs hKt hu'
  refine setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn_prod_of_comp_eq_neg_id
    (J := fun z ↦ J z (u z)) (C := ω.floerLinearizationCoeff J Ks Kt u) hΩ hΩc hξ
    (fun z hz ↦ ?_) hJsq (hC.aestronglyMeasurable hΩ.measurableSet) (fun z hz ↦ ⟨_, (hC.continuousAt
      (hΩ.mem_nhds hz)).norm.eventually (Iic_mem_nhds (lt_add_one _))⟩) (fun z hz ↦ ?_) hne
  · exact ((hJ z hz).comp z (contDiffAt_id.prodMk (hu' z hz))).contDiffWithinAt
  · rw [← floerLinearization_eq_add]
    exact hD z hz

/-! ### The nonlinear equation -/

/-- **The difference of two Floer solutions solves a linear Cauchy–Riemann equation.** Let `u` and
`v` be `C¹` on an open set `Ω`, and let the endomorphisms `J` be `C¹` and the Hamiltonians `K_s`,
`K_t` be `C²`, jointly in the domain and target point, at the points `(z, y)` with `z ∈ Ω` and `y`
on the segment from `u z` to `v z`. There is a field `C` of real-linear maps, continuous on `Ω`,
such that the difference of the Floer operators of `v` and `u` is `∂ₛξ + J(z, v z) ∂ₜξ + C(z) ξ`
for `ξ = v - u` at every point of `Ω`. -/
theorem exists_continuousOn_floerOperator_sub_floerOperator_eq (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u v : ℝ × ℝ → V}
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω)
    (hJ : ∀ z ∈ Ω, ∀ y ∈ segment ℝ (u z) (v z), ContDiffAt ℝ 1 (Function.uncurry J) (z, y))
    (hKs : ∀ z ∈ Ω, ∀ y ∈ segment ℝ (u z) (v z), ContDiffAt ℝ 2 (Function.uncurry Ks) (z, y))
    (hKt : ∀ z ∈ Ω, ∀ y ∈ segment ℝ (u z) (v z), ContDiffAt ℝ 2 (Function.uncurry Kt) (z, y))
    (hu : ContDiffOn ℝ 1 u Ω) (hv : ContDiffOn ℝ 1 v Ω) :
    ∃ C : ℝ × ℝ → V →L[ℝ] V, ContinuousOn C Ω ∧ ∀ z ∈ Ω,
      ω.floerOperator J Ks Kt v z - ω.floerOperator J Ks Kt u z =
        fderiv ℝ (fun w ↦ v w - u w) z stdComplexLineReal +
          J z (v z) (fderiv ℝ (fun w ↦ v w - u w) z stdComplexLineImag) + C z (v z - u z) := by
  have hXs (z : ℝ × ℝ) (hz : z ∈ Ω) (y : V) (hy : y ∈ segment ℝ (u z) (v z)) :
      ContDiffAt ℝ 1 (Function.uncurry fun z ↦ ω.hamiltonianVectorField (Ks z)) (z, y) :=
    ω.contDiffAt_hamiltonianVectorField_uncurry (n := 1) (hKs z hz y hy)
  have hXt (z : ℝ × ℝ) (hz : z ∈ Ω) (y : V) (hy : y ∈ segment ℝ (u z) (v z)) :
      ContDiffAt ℝ 1 (Function.uncurry fun z ↦ ω.hamiltonianVectorField (Kt z)) (z, y) :=
    ω.contDiffAt_hamiltonianVectorField_uncurry (n := 1) (hKt z hz y hy)
  -- the averaged derivatives of `X_{K_s}`, `X_{K_t}` and `J` along the segments from `u` to `v`
  set Gs : ℝ × ℝ → V →L[ℝ] V := fun z ↦
    hadamardFactor (ω.hamiltonianVectorField (Ks z)) (u z) (v z)
  set Gt : ℝ × ℝ → V →L[ℝ] V := fun z ↦
    hadamardFactor (ω.hamiltonianVectorField (Kt z)) (u z) (v z)
  set GJ : ℝ × ℝ → V →L[ℝ] V →L[ℝ] V := fun z ↦ hadamardFactor (J z) (u z) (v z)
  refine ⟨fun z ↦ (GJ z).flip (fderiv ℝ u z stdComplexLineImag -
      ω.hamiltonianVectorField (Kt z) (u z)) - Gs z - J z (v z) ∘L Gt z, ?_, fun z hz ↦ ?_⟩
  · have hut : ContinuousOn (fun z ↦ fderiv ℝ u z stdComplexLineImag) Ω :=
      (hu.continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply continuousOn_const
    have hXtu : ContinuousOn (fun z ↦ ω.hamiltonianVectorField (Kt z) (u z)) Ω := fun z hz ↦
      (hXt z hz (u z) (left_mem_segment ℝ _ _)).continuousAt.comp_continuousWithinAt
        (f := fun z ↦ (z, u z)) (continuousWithinAt_id.prodMk (hu.continuousOn z hz))
    have hJv : ContinuousOn (fun z ↦ J z (v z)) Ω := fun z hz ↦
      (hJ z hz (v z) (right_mem_segment ℝ _ _)).continuousAt.comp_continuousWithinAt
        (f := fun z ↦ (z, v z)) (continuousWithinAt_id.prodMk (hv.continuousOn z hz))
    have hflip : ContinuousOn (fun z ↦ (GJ z).flip) Ω :=
      (flipₗᵢ ℝ V V V).continuous.comp_continuousOn
        (continuousOn_hadamardFactor (f := J) hJ hu.continuousOn hv.continuousOn)
    exact ((hflip.clm_apply (hut.sub hXtu)).sub
      (continuousOn_hadamardFactor (f := fun z ↦ ω.hamiltonianVectorField (Ks z)) hXs
        hu.continuousOn hv.continuousOn)).sub
      (hJv.clm_comp (continuousOn_hadamardFactor (f := fun z ↦ ω.hamiltonianVectorField (Kt z))
        hXt hu.continuousOn hv.continuousOn))
  · have hzΩ : Ω ∈ 𝓝 z := hΩ.mem_nhds hz
    -- `F(z, v z) = F(z, u z) + G(z)(v z - u z)` for the averaged derivative `G` along the segment
    have hpart {G : Type _} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
        {F : ℝ × ℝ → V → G}
        (hF : ∀ y ∈ segment ℝ (u z) (v z), ContDiffAt ℝ 1 (Function.uncurry F) (z, y)) :
        F z (v z) = F z (u z) + hadamardFactor (F z) (u z) (v z) (v z - u z) := by
      rw [← sub_eq_hadamardFactor_apply (F z) fun y hy ↦
        (hF y hy).comp y (contDiffAt_const.prodMk contDiffAt_id)]
      abel
    rw [fderiv_fun_sub ((hv.contDiffAt hzΩ).differentiableAt one_ne_zero)
      ((hu.contDiffAt hzΩ).differentiableAt one_ne_zero), floerOperator_def, floerOperator_def]
    dsimp only [Gs, Gt, GJ]
    rw [hpart (hJ z hz), hpart (F := fun z ↦ ω.hamiltonianVectorField (Ks z)) (hXs z hz),
      hpart (F := fun z ↦ ω.hamiltonianVectorField (Kt z)) (hXt z hz)]
    simp only [add_apply, sub_apply, comp_apply, flip_apply, map_add, map_sub]
    abel

variable {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u v : ℝ × ℝ → V}
  {Ω : Set (ℝ × ℝ)}

/-- Near a point of `Ω` where two solutions `u` and `v` of the Floer equation agree, their
difference solves a linear Cauchy–Riemann equation with measurable, locally bounded coefficients
on a disc, when the data are regular near the graph of `v`. -/
private theorem exists_ball_floerOperator_sub (ω : SymplecticForm V) (hΩ : IsOpen Ω)
    (hJ : ∀ z ∈ Ω, ContDiffAt ℝ 1 (Function.uncurry J) (z, v z))
    (hKs : ∀ z ∈ Ω, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, v z))
    (hKt : ∀ z ∈ Ω, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, v z)) (hu : ContDiffOn ℝ 1 u Ω)
    (hv : ContDiffOn ℝ 1 v Ω) (hFu : ∀ z ∈ Ω, ω.floerOperator J Ks Kt u z = 0)
    (hFv : ∀ z ∈ Ω, ω.floerOperator J Ks Kt v z = 0) {z₀ : ℝ × ℝ} (hz₀ : z₀ ∈ Ω)
    (huv : u z₀ = v z₀) :
    ∃ r > 0, ball z₀ r ⊆ Ω ∧ ∃ C : ℝ × ℝ → V →L[ℝ] V,
      AEStronglyMeasurable C (volume.restrict (ball z₀ r)) ∧
      (∀ z ∈ ball z₀ r, ∃ M, ∀ᶠ w in 𝓝 z, ‖C w‖ ≤ M) ∧ ∀ z ∈ ball z₀ r,
        fderiv ℝ (fun w ↦ v w - u w) z stdComplexLineReal +
          J z (v z) (fderiv ℝ (fun w ↦ v w - u w) z stdComplexLineImag) + C z (v z - u z) = 0 := by
  -- the data are regular on a ball about `(z₀, v z₀)`
  have hN : ∀ᶠ q in 𝓝 (z₀, v z₀), ContDiffAt ℝ 1 (Function.uncurry J) q ∧
      ContDiffAt ℝ 2 (Function.uncurry Ks) q ∧ ContDiffAt ℝ 2 (Function.uncurry Kt) q :=
    ((hJ z₀ hz₀).eventually (by simp)).and
      (((hKs z₀ hz₀).eventually (by simp)).and ((hKt z₀ hz₀).eventually (by simp)))
  obtain ⟨ε, hε, hεN⟩ := Metric.mem_nhds_iff.1 hN
  -- near `z₀`, the segments from `u z` to `v z` stay in the ball of radius `ε` about `v z₀`
  have hB : ball (v z₀) ε ∈ 𝓝 (u z₀) := huv ▸ ball_mem_nhds _ hε
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.1 (inter_mem
    (inter_mem (hΩ.mem_nhds hz₀) (ball_mem_nhds z₀ hε))
    (inter_mem ((hu.continuousOn.continuousAt (hΩ.mem_nhds hz₀)).preimage_mem_nhds hB)
      ((hv.continuousOn.continuousAt (hΩ.mem_nhds hz₀)).preimage_mem_nhds
        (ball_mem_nhds _ hε))))
  have hrΩ : ball z₀ r ⊆ Ω := fun z hz ↦ (hrsub hz).1.1
  have hseg (z : ℝ × ℝ) (hz : z ∈ ball z₀ r) (y : V) (hy : y ∈ segment ℝ (u z) (v z)) :
      ContDiffAt ℝ 1 (Function.uncurry J) (z, y) ∧ ContDiffAt ℝ 2 (Function.uncurry Ks) (z, y) ∧
        ContDiffAt ℝ 2 (Function.uncurry Kt) (z, y) := by
    obtain ⟨⟨-, hzε⟩, hzu, hzv⟩ := hrsub hz
    refine hεN ?_
    rw [← ball_prod_same]
    exact ⟨hzε, (convex_ball (v z₀) ε).segment_subset hzu hzv hy⟩
  obtain ⟨C, hC, heq⟩ := ω.exists_continuousOn_floerOperator_sub_floerOperator_eq isOpen_ball
    (fun z hz y hy ↦ (hseg z hz y hy).1) (fun z hz y hy ↦ (hseg z hz y hy).2.1)
    (fun z hz y hy ↦ (hseg z hz y hy).2.2) (hu.mono hrΩ) (hv.mono hrΩ)
  refine ⟨r, hr, hrΩ, C, hC.aestronglyMeasurable isOpen_ball.measurableSet,
    fun z hz ↦ ⟨_, (hC.continuousAt (isOpen_ball.mem_nhds hz)).norm.eventually
      (Iic_mem_nhds (lt_add_one _))⟩, fun z hz ↦ ?_⟩
  rw [← heq z hz, hFv z (hrΩ hz), hFu z (hrΩ hz), sub_zero]

/-- Two solutions of the Floer equation either agree near a point of `Ω` or differ at every point
of a punctured neighbourhood of it. -/
private theorem eventually_eq_or_eventually_ne_of_floerOperator_eq_zero (ω : SymplecticForm V)
    (hΩ : IsOpen Ω) (hJ : ∀ z ∈ Ω, ContDiffAt ℝ 1 (Function.uncurry J) (z, v z))
    (hKs : ∀ z ∈ Ω, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, v z))
    (hKt : ∀ z ∈ Ω, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, v z)) (hu : ContDiffOn ℝ 1 u Ω)
    (hv : ContDiffOn ℝ 1 v Ω)
    (hJsq : ∀ z ∈ Ω, J z (v z) ∘L J z (v z) = -ContinuousLinearMap.id ℝ V)
    (hFu : ∀ z ∈ Ω, ω.floerOperator J Ks Kt u z = 0)
    (hFv : ∀ z ∈ Ω, ω.floerOperator J Ks Kt v z = 0) {z₀ : ℝ × ℝ} (hz₀ : z₀ ∈ Ω) :
    (∀ᶠ z in 𝓝 z₀, u z = v z) ∨ ∀ᶠ z in 𝓝[≠] z₀, u z ≠ v z := by
  by_cases huv : u z₀ = v z₀
  · obtain ⟨r, hr, hrΩ, C, hCm, hCb, heq⟩ :=
      exists_ball_floerOperator_sub ω hΩ hJ hKs hKt hu hv hFu hFv hz₀ huv
    by_cases hne : ∃ z ∈ ball z₀ r, v z - u z ≠ 0
    · right
      have hJv : ContDiffOn ℝ 1 (fun z ↦ J z (v z)) (ball z₀ r) := fun z hz ↦ by
        have h := (hJ z (hrΩ hz)).comp z (contDiffAt_id.prodMk
          (hv.contDiffAt (hΩ.mem_nhds (hrΩ hz))))
        exact h.contDiffWithinAt
      have h := setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn_prod_of_comp_eq_neg_id
        isOpen_ball (convex_ball z₀ r).isPreconnected ((hv.sub hu).mono hrΩ) hJv
        (fun z hz ↦ hJsq z (hrΩ hz)) hCm hCb heq hne
      filter_upwards [disjoint_principal_right.1 (mem_codiscreteWithin.1 h z₀ (mem_ball_self hr)),
        nhdsWithin_le_nhds (ball_mem_nhds z₀ hr)] with z hz hzB hzuv
      exact hz ⟨hzB, by simp [hzuv]⟩
    · left
      push Not at hne
      filter_upwards [ball_mem_nhds z₀ hr] with z hz
      exact (sub_eq_zero.1 (hne z hz)).symm
  · right
    have h := ((hu.continuousOn.continuousAt (hΩ.mem_nhds hz₀)).sub
      (hv.continuousOn.continuousAt (hΩ.mem_nhds hz₀))).eventually_ne (sub_ne_zero.2 huv)
    exact nhdsWithin_le_nhds (h.mono fun z hz ↦ sub_ne_zero.1 hz)

/-- Two solutions of the Floer equation on a connected open set `Ω` that agree near a point of `Ω`
agree on `Ω`. -/
private theorem eqOn_of_floerOperator_eq_zero_of_eventually_eq (ω : SymplecticForm V)
    (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hJ : ∀ z ∈ Ω, ContDiffAt ℝ 1 (Function.uncurry J) (z, v z))
    (hKs : ∀ z ∈ Ω, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, v z))
    (hKt : ∀ z ∈ Ω, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, v z)) (hu : ContDiffOn ℝ 1 u Ω)
    (hv : ContDiffOn ℝ 1 v Ω)
    (hJsq : ∀ z ∈ Ω, J z (v z) ∘L J z (v z) = -ContinuousLinearMap.id ℝ V)
    (hFu : ∀ z ∈ Ω, ω.floerOperator J Ks Kt u z = 0)
    (hFv : ∀ z ∈ Ω, ω.floerOperator J Ks Kt v z = 0) {z₀ : ℝ × ℝ} (hz₀ : z₀ ∈ Ω)
    (h₀ : ∀ᶠ z in 𝓝 z₀, u z = v z) : EqOn u v Ω := by
  -- the points near which `u = v` and the points of `Ω` near which not are open
  let A : Set (ℝ × ℝ) := {z | ∀ᶠ w in 𝓝 z, u w = v w}
  let B : Set (ℝ × ℝ) := {z | z ∈ Ω ∧ ¬ ∀ᶠ w in 𝓝 z, u w = v w}
  have hA : IsOpen A := isOpen_setOfPred_eventually_nhds
  have hB : IsOpen B := by
    refine isOpen_iff_mem_nhds.2 fun z ⟨hz, hnot⟩ ↦ ?_
    have hne := (eventually_eq_or_eventually_ne_of_floerOperator_eq_zero ω hΩ hJ hKs hKt hu hv
      hJsq hFu hFv hz).resolve_left hnot
    filter_upwards [hΩ.mem_nhds hz, eventually_nhdsWithin_iff.1 hne] with w hw hwne
    refine ⟨hw, fun hw₀ ↦ ?_⟩
    rcases eq_or_ne w z with rfl | hwz
    · exact hnot hw₀
    · exact hwne hwz hw₀.self_of_nhds
  have hsub : Ω ⊆ A := hΩc.subset_left_of_subset_union hA hB
    (disjoint_left.2 fun _ hzA hzB ↦ hzB.2 hzA)
    (fun z hz ↦ (em (z ∈ A)).imp_right fun h ↦ ⟨hz, h⟩) ⟨z₀, hz₀, h₀⟩
  exact fun z hz ↦ (hsub hz).self_of_nhds

/-- **Unique continuation for the Floer equation from a coincidence of infinite order.** Let the
endomorphisms `J` be `C¹` and the Hamiltonians `K_s`, `K_t` be `C²` at the points `(z, v z)`,
`z ∈ Ω`, jointly in the domain and target point, and let `u` and `v` be `C¹` solutions of the
Floer equation `∂ₛu - X_{K_s}(u) + J(u)(∂ₜu - X_{K_t}(u)) = 0` on a connected open set `Ω` of the
domain, with `J(z, v z)² = -1`. If `v - u = O(‖z - z₀‖ⁿ)` near a point `z₀ ∈ Ω` for every `n`,
then `u` and `v` agree on `Ω`. -/
theorem eqOn_of_floerOperator_eq_zero_of_forall_isBigO (ω : SymplecticForm V) (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hJ : ∀ z ∈ Ω, ContDiffAt ℝ 1 (Function.uncurry J) (z, v z))
    (hKs : ∀ z ∈ Ω, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, v z))
    (hKt : ∀ z ∈ Ω, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, v z)) (hu : ContDiffOn ℝ 1 u Ω)
    (hv : ContDiffOn ℝ 1 v Ω)
    (hJsq : ∀ z ∈ Ω, J z (v z) ∘L J z (v z) = -ContinuousLinearMap.id ℝ V)
    (hFu : ∀ z ∈ Ω, ω.floerOperator J Ks Kt u z = 0)
    (hFv : ∀ z ∈ Ω, ω.floerOperator J Ks Kt v z = 0) {z₀ : ℝ × ℝ} (hz₀ : z₀ ∈ Ω)
    (h₀ : ∀ n : ℕ, (fun z ↦ v z - u z) =O[𝓝 z₀] fun z ↦ ‖z - z₀‖ ^ n) : EqOn u v Ω := by
  have huv : u z₀ = v z₀ := by
    obtain ⟨c, hc⟩ := (h₀ 1).bound
    have h : ‖v z₀ - u z₀‖ ≤ 0 := by simpa using hc.self_of_nhds
    exact (sub_eq_zero.1 (norm_le_zero_iff.1 h)).symm
  obtain ⟨r, hr, hrΩ, C, hCm, hCb, heq⟩ :=
    exists_ball_floerOperator_sub ω hΩ hJ hKs hKt hu hv hFu hFv hz₀ huv
  have hJv : ContDiffOn ℝ 1 (fun z ↦ J z (v z)) (ball z₀ r) := fun z hz ↦ by
    have h := (hJ z (hrΩ hz)).comp z (contDiffAt_id.prodMk
      (hv.contDiffAt (hΩ.mem_nhds (hrΩ hz))))
    exact h.contDiffWithinAt
  have h := eqOn_zero_of_contDiffOn_prod_of_comp_eq_neg_id_of_forall_isBigO isOpen_ball
    (convex_ball z₀ r).isPreconnected ((hv.sub hu).mono hrΩ) hJv (fun z hz ↦ hJsq z (hrΩ hz))
    hCm hCb heq (mem_ball_self hr) h₀
  exact eqOn_of_floerOperator_eq_zero_of_eventually_eq ω hΩ hΩc hJ hKs hKt hu hv hJsq hFu hFv hz₀
    (eventually_of_mem (ball_mem_nhds z₀ hr) fun z hz ↦ (sub_eq_zero.1 (h hz)).symm)

/-- **Unique continuation for the Floer equation.** Let the endomorphisms `J` be `C¹` and the
Hamiltonians `K_s`, `K_t` be `C²` at the points `(z, v z)`, `z ∈ Ω`, jointly in the domain and
target point, and let `u` and `v` be `C¹` solutions of the Floer equation
`∂ₛu - X_{K_s}(u) + J(u)(∂ₜu - X_{K_t}(u)) = 0` on a connected open set `Ω` of the domain, with
`J(z, v z)² = -1`. If `u` and `v` agree on a nonempty open subset of `Ω`, they agree on `Ω`. -/
theorem eqOn_of_floerOperator_eq_zero_of_eqOn (ω : SymplecticForm V) {U : Set (ℝ × ℝ)}
    (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hJ : ∀ z ∈ Ω, ContDiffAt ℝ 1 (Function.uncurry J) (z, v z))
    (hKs : ∀ z ∈ Ω, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, v z))
    (hKt : ∀ z ∈ Ω, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, v z)) (hu : ContDiffOn ℝ 1 u Ω)
    (hv : ContDiffOn ℝ 1 v Ω)
    (hJsq : ∀ z ∈ Ω, J z (v z) ∘L J z (v z) = -ContinuousLinearMap.id ℝ V)
    (hFu : ∀ z ∈ Ω, ω.floerOperator J Ks Kt u z = 0)
    (hFv : ∀ z ∈ Ω, ω.floerOperator J Ks Kt v z = 0)
    (hU : IsOpen U) (hUne : U.Nonempty) (hUΩ : U ⊆ Ω) (h₀ : EqOn u v U) : EqOn u v Ω := by
  obtain ⟨z₀, hz₀⟩ := hUne
  exact eqOn_of_floerOperator_eq_zero_of_eventually_eq ω hΩ hΩc hJ hKs hKt hu hv hJsq hFu hFv
    (hUΩ hz₀) (eventually_of_mem (hU.mem_nhds hz₀) h₀)

/-- **Isolated coincidences of Floer solutions.** Let the endomorphisms `J` be `C¹` and the
Hamiltonians `K_s`, `K_t` be `C²` at the points `(z, v z)`, `z ∈ Ω`, jointly in the domain and
target point, and let `u` and `v` be `C¹` solutions of the Floer equation
`∂ₛu - X_{K_s}(u) + J(u)(∂ₜu - X_{K_t}(u)) = 0` on a connected open set `Ω` of the domain, with
`J(z, v z)² = -1`. If `u` and `v` differ somewhere on `Ω`, the points of `Ω` where they agree form
a discrete subset of `Ω`. -/
theorem setOf_ne_mem_codiscreteWithin_of_floerOperator_eq_zero (ω : SymplecticForm V)
    (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hJ : ∀ z ∈ Ω, ContDiffAt ℝ 1 (Function.uncurry J) (z, v z))
    (hKs : ∀ z ∈ Ω, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, v z))
    (hKt : ∀ z ∈ Ω, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, v z)) (hu : ContDiffOn ℝ 1 u Ω)
    (hv : ContDiffOn ℝ 1 v Ω)
    (hJsq : ∀ z ∈ Ω, J z (v z) ∘L J z (v z) = -ContinuousLinearMap.id ℝ V)
    (hFu : ∀ z ∈ Ω, ω.floerOperator J Ks Kt u z = 0)
    (hFv : ∀ z ∈ Ω, ω.floerOperator J Ks Kt v z = 0) (hne : ∃ z ∈ Ω, u z ≠ v z) :
    {z | u z ≠ v z} ∈ codiscreteWithin Ω := by
  refine mem_codiscreteWithin.2 fun z₀ hz₀ ↦ ?_
  rw [disjoint_principal_right]
  rcases eventually_eq_or_eventually_ne_of_floerOperator_eq_zero ω hΩ hJ hKs hKt hu hv hJsq hFu hFv
    hz₀ with h | h
  · obtain ⟨z, hz, huvz⟩ := hne
    exact absurd (eqOn_of_floerOperator_eq_zero_of_eventually_eq ω hΩ hΩc hJ hKs hKt hu hv hJsq hFu
      hFv hz₀ h hz) huvz
  · filter_upwards [h] with z hz hmem
    exact hmem.2 hz

end SymplecticForm

end TauCeti
