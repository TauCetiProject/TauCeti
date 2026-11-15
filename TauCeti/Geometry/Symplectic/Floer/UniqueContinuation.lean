/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Linearization
public import TauCeti.Analysis.Calculus.Hadamard
import TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation.VariableStructure

/-!
# Unique continuation for the Floer equation

Let `(V, ω)` be a finite-dimensional symplectic vector space, `K = K_s ds + K_t dt` a
domain-dependent Hamiltonian perturbation and `J(z, y)` a family of endomorphisms of `V` on the
domain `ℝ × ℝ`. This file proves unique continuation for the Floer equation and its linearization
on a connected open set `Ω` of the domain.

* **The linearized operator.** Along a map `u`, the linearized Floer operator is
  `D_u ξ = ∂ₛξ + J(z, u z) ∂ₜξ + S(z) ξ` (`TauCeti.SymplecticForm.floerLinearization_eq_add`),
  with a zeroth-order coefficient `S` continuous when the data are `C¹` (the Hamiltonians `C²`).
  If `J(z, u z)² = -1`, a solution of `D_u ξ = 0` vanishing on a nonempty open subset of `Ω`
  vanishes on `Ω` (`TauCeti.SymplecticForm.eqOn_zero_of_floerLinearization_eq_zero`).
* **The nonlinear equation.** For `C¹` maps `u` and `v`, the difference of their Floer operators is
  `∂ₛξ + J(z, v z) ∂ₜξ + C(z) ξ` for `ξ = v - u` and a coefficient `C` continuous on `Ω`
  (`TauCeti.SymplecticForm.exists_continuousOn_floerOperator_sub_floerOperator`). It is assembled
  from the averaged derivatives `∫₀¹ dF(u + τ ξ) dτ` (`hadamardFactor`) of `F = X_{K_s}`, `X_{K_t}`
  and `J` along the segment from `u z` to `v z`, which turn the differences `F(v) - F(u)` into
  linear expressions in `ξ`. Consequently two solutions of the Floer equation on `Ω` that agree on
  a nonempty open subset of `Ω` agree on `Ω`
  (`TauCeti.SymplecticForm.eqOn_of_floerOperator_eq_zero`).

Both reduce to unique continuation for linear Cauchy–Riemann equations with a variable complex
structure in the coordinates `(s, t)` of the domain
(`TauCeti.eqOn_zero_of_contDiffOn_prod_of_comp_eq_neg_id_of_eqOn_zero`). In the complex coordinate
`Complex.equivRealProdCLM` this is `TauCeti.eqOn_zero_of_contDiffOn_of_comp_eq_neg_id_of_eqOn_zero`,
a consequence of the Carleman similarity principle.

In the transversality argument for moduli spaces of Floer solutions, localized Hamiltonian
variations show that an element of the cokernel of the universal linearized operator vanishes on
an open subset of a compact core
(`TauCeti.SymplecticForm.eqOn_zero_of_forall_integral_apply_floerOperator_add_sub_eq_zero`). For an
inner product on `V`, the formal `L²` adjoint of `D_u` is, up to sign, again of the form
`∂ₛ + J' ∂ₜ + C'`, with `J'` the transpose of `J(z, u z)`, also a complex structure. Such cokernel
elements are a priori only weak `L^q` solutions of the adjoint equation. Once elliptic regularity,
which is not proved here, shows that they are `C¹` classical solutions, the unique continuation
theorem above extends that vanishing to the whole connected domain. Unique continuation for the
nonlinear equation underlies the reduction of Floer solutions to their simple images.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.3 (unique continuation) and Section 8.1 (Floer's equation).
* A. Floer, H. Hofer and D. Salamon, *Transversality in elliptic Morse theory for the symplectic
  action*, Duke Math. J. 80 (1995), 251–292.
-/

public section

open Complex ContinuousLinearMap MeasureTheory Set Filter Topology

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Unique continuation in the coordinates `(s, t)`.** Let `ξ` be of class `C¹` on a connected
open set `Ω ⊆ ℝ × ℝ`, with values in a finite-dimensional real normed space `V`, and solve
`∂ₛξ + J ∂ₜξ + C ξ = 0` on `Ω`, for a `C¹` field `J` of real-linear maps with `J² = -1` and a
measurable, locally bounded field `C` of real-linear maps. If `ξ` vanishes on a nonempty open
subset of `Ω`, it vanishes on `Ω`. This is
`TauCeti.eqOn_zero_of_contDiffOn_of_comp_eq_neg_id_of_eqOn_zero` read in the complex coordinate
`Complex.equivRealProdCLM`. -/
theorem eqOn_zero_of_contDiffOn_prod_of_comp_eq_neg_id_of_eqOn_zero {Ω U : Set (ℝ × ℝ)}
    {ξ : ℝ × ℝ → V} {J C : ℝ × ℝ → V →L[ℝ] V} (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hξ : ContDiffOn ℝ 1 ξ Ω) (hJ : ContDiffOn ℝ 1 J Ω)
    (hJsq : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V)
    (hCm : AEStronglyMeasurable C (volume.restrict Ω))
    (hCb : ∀ z ∈ Ω, ∃ M, ∀ᶠ w in 𝓝 z, ‖C w‖ ≤ M)
    (heq : ∀ z ∈ Ω, fderiv ℝ ξ z stdComplexLineReal + J z (fderiv ℝ ξ z stdComplexLineImag) +
      C z (ξ z) = 0)
    (hU : IsOpen U) (hUne : U.Nonempty) (hUΩ : U ⊆ Ω) (h₀ : EqOn ξ 0 U) : EqOn ξ 0 Ω := by
  set e : ℂ ≃L[ℝ] ℝ × ℝ := equivRealProdCLM with he
  have hmaps : MapsTo e (e ⁻¹' Ω) Ω := mapsTo_preimage _ _
  have hΩ' : IsOpen (e ⁻¹' Ω) := hΩ.preimage e.continuous
  have hΩc' : IsPreconnected (e ⁻¹' Ω) := by
    rw [← e.image_symm_eq_preimage]
    exact hΩc.image _ e.symm.continuous.continuousOn
  have he' : MeasurePreserving e (volume.restrict (e ⁻¹' Ω)) (volume.restrict Ω) :=
    volume_preserving_equiv_real_prod.restrict_preimage hΩ.measurableSet
  obtain ⟨z₀, hz₀⟩ := hUne
  have h := eqOn_zero_of_contDiffOn_of_comp_eq_neg_id_of_eqOn_zero (ξ := ξ ∘ e) (J := J ∘ e)
    (C := C ∘ e) hΩ' hΩc' (hξ.comp e.contDiff.contDiffOn hmaps)
    (hJ.comp e.contDiff.contDiffOn hmaps) (fun y hy ↦ hJsq (e y) hy)
    (hCm.comp_measurePreserving he')
    (fun y hy ↦ (hCb (e y) hy).imp fun _ hM ↦ e.continuous.continuousAt.eventually hM)
    (fun y hy ↦ by
      simpa only [he, fderiv_comp_equivRealProdCLM_one, fderiv_comp_equivRealProdCLM_I,
        Function.comp_apply] using heq (e y) hy)
    (hU.preimage e.continuous) ⟨e.symm z₀, by simpa using hz₀⟩ (preimage_mono hUΩ)
    (fun y hy ↦ h₀ hy)
  intro z hz
  simpa using h (x := e.symm z) (by simpa using hz)

namespace SymplecticForm

/-- **Unique continuation for the linearized Floer operator.** Let `u` and `ξ` be `C¹` on a
connected open set `Ω` of the domain, and let the endomorphisms `J` be `C¹` and the Hamiltonians
`K_s`, `K_t` be `C²` at the points `(z, u z)`, `z ∈ Ω`, jointly in the domain and target point, with
`J(z, u z)² = -1`. If `D_u ξ = 0` on `Ω` and `ξ` vanishes on a nonempty open subset of `Ω`, then
`ξ` vanishes on `Ω`. -/
theorem eqOn_zero_of_floerLinearization_eq_zero (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u ξ : ℝ × ℝ → V}
    {Ω U : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hJ : ∀ z ∈ Ω, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z ∈ Ω, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ Ω, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z))
    (hu : ContDiffOn ℝ 1 u Ω) (hξ : ContDiffOn ℝ 1 ξ Ω)
    (hJsq : ∀ z ∈ Ω, J z (u z) ∘L J z (u z) = -ContinuousLinearMap.id ℝ V)
    (hD : ∀ z ∈ Ω, ω.floerLinearization J Ks Kt u ξ z = 0)
    (hU : IsOpen U) (hUne : U.Nonempty) (hUΩ : U ⊆ Ω) (h₀ : EqOn ξ 0 U) : EqOn ξ 0 Ω := by
  have hu' (z : ℝ × ℝ) (hz : z ∈ Ω) : ContDiffAt ℝ 1 u z := hu.contDiffAt (hΩ.mem_nhds hz)
  have hC := ω.continuousOn_floerLinearizationCoeff hJ hKs hKt hu'
  refine eqOn_zero_of_contDiffOn_prod_of_comp_eq_neg_id_of_eqOn_zero (J := fun z ↦ J z (u z))
    (C := ω.floerLinearizationCoeff J Ks Kt u) hΩ hΩc hξ (fun z hz ↦ ?_) hJsq
    (hC.aestronglyMeasurable hΩ.measurableSet) (fun z hz ↦ ⟨_, (hC.continuousAt
      (hΩ.mem_nhds hz)).norm.eventually (Iic_mem_nhds (lt_add_one _))⟩) (fun z hz ↦ ?_) hU hUne
    hUΩ h₀
  · exact ((hJ z hz).comp z (contDiffAt_id.prodMk (hu' z hz))).contDiffWithinAt
  · rw [← floerLinearization_eq_add]
    exact hD z hz

/-- **The difference of two Floer solutions solves a linear Cauchy–Riemann equation.** Let the
endomorphisms `J` be `C¹` and the Hamiltonians `K_s`, `K_t` be `C²`, jointly in the domain and
target point, and let `u` and `v` be `C¹` on an open set `Ω`. There is a field `C` of real-linear
maps, continuous on `Ω`, such that the difference of the Floer operators of `v` and `u` is
`∂ₛξ + J(z, v z) ∂ₜξ + C(z) ξ` for `ξ = v - u` at every point of `Ω`. -/
theorem exists_continuousOn_floerOperator_sub_floerOperator (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u v : ℝ × ℝ → V}
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hJ : ContDiff ℝ 1 (Function.uncurry J))
    (hKs : ContDiff ℝ 2 (Function.uncurry Ks)) (hKt : ContDiff ℝ 2 (Function.uncurry Kt))
    (hu : ContDiffOn ℝ 1 u Ω) (hv : ContDiffOn ℝ 1 v Ω) :
    ∃ C : ℝ × ℝ → V →L[ℝ] V, ContinuousOn C Ω ∧ ∀ z ∈ Ω,
      ω.floerOperator J Ks Kt v z - ω.floerOperator J Ks Kt u z =
        fderiv ℝ (fun w ↦ v w - u w) z stdComplexLineReal +
          J z (v z) (fderiv ℝ (fun w ↦ v w - u w) z stdComplexLineImag) + C z (v z - u z) := by
  have hXs := ω.contDiff_hamiltonianVectorField_uncurry (n := 1) hKs
  have hXt := ω.contDiff_hamiltonianVectorField_uncurry (n := 1) hKt
  -- the averaged derivatives of `X_{K_s}`, `X_{K_t}` and `J` along the segments from `u` to `v`
  set Gs : ℝ × ℝ → V →L[ℝ] V := fun z ↦
    hadamardFactor (ω.hamiltonianVectorField (Ks z)) (u z) (v z)
  set Gt : ℝ × ℝ → V →L[ℝ] V := fun z ↦
    hadamardFactor (ω.hamiltonianVectorField (Kt z)) (u z) (v z)
  set GJ : ℝ × ℝ → V →L[ℝ] V →L[ℝ] V := fun z ↦ hadamardFactor (J z) (u z) (v z)
  have hdiffs (z : ℝ × ℝ) : ω.hamiltonianVectorField (Ks z) (v z) -
      ω.hamiltonianVectorField (Ks z) (u z) = Gs z (v z - u z) :=
    ContDiff.sub_eq_hadamardFactor_apply (ω.hamiltonianVectorField (Ks z))
      (hXs.comp (contDiff_const.prodMk contDiff_id)) (u z) (v z)
  have hdifft (z : ℝ × ℝ) : ω.hamiltonianVectorField (Kt z) (v z) -
      ω.hamiltonianVectorField (Kt z) (u z) = Gt z (v z - u z) :=
    ContDiff.sub_eq_hadamardFactor_apply (ω.hamiltonianVectorField (Kt z))
      (hXt.comp (contDiff_const.prodMk contDiff_id)) (u z) (v z)
  have hdiffJ (z : ℝ × ℝ) : J z (v z) - J z (u z) = GJ z (v z - u z) :=
    ContDiff.sub_eq_hadamardFactor_apply (J z) (hJ.comp (contDiff_const.prodMk contDiff_id))
      (u z) (v z)
  refine ⟨fun z ↦ (GJ z).flip (fderiv ℝ u z stdComplexLineImag -
      ω.hamiltonianVectorField (Kt z) (u z)) - Gs z - J z (v z) ∘L Gt z, ?_, fun z hz ↦ ?_⟩
  · have hut : ContinuousOn (fun z ↦ fderiv ℝ u z stdComplexLineImag) Ω :=
      (hu.continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply continuousOn_const
    have hXtu : ContinuousOn (fun z ↦ ω.hamiltonianVectorField (Kt z) (u z)) Ω :=
      hXt.continuous.comp_continuousOn (continuousOn_id.prodMk hu.continuousOn)
    have hJv : ContinuousOn (fun z ↦ J z (v z)) Ω :=
      hJ.continuous.comp_continuousOn (continuousOn_id.prodMk hv.continuousOn)
    have hflip : ContinuousOn (fun z ↦ (GJ z).flip) Ω :=
      (flipₗᵢ ℝ V V V).continuous.comp_continuousOn
        (hJ.continuousOn_hadamardFactor (f := J) hu.continuousOn hv.continuousOn)
    exact ((hflip.clm_apply (hut.sub hXtu)).sub
      (hXs.continuousOn_hadamardFactor (f := fun z ↦ ω.hamiltonianVectorField (Ks z))
        hu.continuousOn hv.continuousOn)).sub
      (hJv.clm_comp (hXt.continuousOn_hadamardFactor
        (f := fun z ↦ ω.hamiltonianVectorField (Kt z)) hu.continuousOn hv.continuousOn))
  · have hzΩ : Ω ∈ 𝓝 z := hΩ.mem_nhds hz
    rw [fderiv_fun_sub ((hv.contDiffAt hzΩ).differentiableAt one_ne_zero)
      ((hu.contDiffAt hzΩ).differentiableAt one_ne_zero), floerOperator_def, floerOperator_def]
    have hJv : J z (v z) = J z (u z) + GJ z (v z - u z) := by rw [← hdiffJ]; abel
    have hXsv : ω.hamiltonianVectorField (Ks z) (v z) =
        ω.hamiltonianVectorField (Ks z) (u z) + Gs z (v z - u z) := by rw [← hdiffs]; abel
    have hXtv : ω.hamiltonianVectorField (Kt z) (v z) =
        ω.hamiltonianVectorField (Kt z) (u z) + Gt z (v z - u z) := by rw [← hdifft]; abel
    dsimp only
    rw [hJv, hXsv, hXtv]
    simp only [add_apply, sub_apply, comp_apply, flip_apply, map_add, map_sub]
    abel

/-- **Unique continuation for the Floer equation.** Let the endomorphisms `J` be `C¹` and the
Hamiltonians `K_s`, `K_t` be `C²`, jointly in the domain and target point, and let `u` and `v` be
`C¹` solutions of the Floer equation `∂ₛu - X_{K_s}(u) + J(u)(∂ₜu - X_{K_t}(u)) = 0` on a connected
open set `Ω` of the domain, with `J(z, v z)² = -1`. If `u` and `v` agree on a nonempty open subset
of `Ω`, they agree on `Ω`. -/
theorem eqOn_of_floerOperator_eq_zero (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u v : ℝ × ℝ → V}
    {Ω U : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hJ : ContDiff ℝ 1 (Function.uncurry J)) (hKs : ContDiff ℝ 2 (Function.uncurry Ks))
    (hKt : ContDiff ℝ 2 (Function.uncurry Kt)) (hu : ContDiffOn ℝ 1 u Ω)
    (hv : ContDiffOn ℝ 1 v Ω)
    (hJsq : ∀ z ∈ Ω, J z (v z) ∘L J z (v z) = -ContinuousLinearMap.id ℝ V)
    (hFu : ∀ z ∈ Ω, ω.floerOperator J Ks Kt u z = 0)
    (hFv : ∀ z ∈ Ω, ω.floerOperator J Ks Kt v z = 0)
    (hU : IsOpen U) (hUne : U.Nonempty) (hUΩ : U ⊆ Ω) (h₀ : EqOn u v U) : EqOn u v Ω := by
  obtain ⟨C, hC, heq⟩ := ω.exists_continuousOn_floerOperator_sub_floerOperator hΩ hJ hKs hKt hu hv
  have hzero := eqOn_zero_of_contDiffOn_prod_of_comp_eq_neg_id_of_eqOn_zero
    (ξ := fun w ↦ v w - u w) (J := fun z ↦ J z (v z)) hΩ hΩc (hv.sub hu)
    (hJ.comp_contDiffOn (contDiffOn_id.prodMk hv)) hJsq (hC.aestronglyMeasurable hΩ.measurableSet)
    (fun z hz ↦ ⟨_, (hC.continuousAt (hΩ.mem_nhds hz)).norm.eventually
      (Iic_mem_nhds (lt_add_one _))⟩)
    (fun z hz ↦ by rw [← heq z hz, hFv z hz, hFu z hz, sub_zero]) hU hUne hUΩ
    (fun z hz ↦ by simp [h₀ hz])
  intro z hz
  exact (sub_eq_zero.1 (hzero hz)).symm

end SymplecticForm

end TauCeti
