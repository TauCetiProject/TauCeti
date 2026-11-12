/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.SynthesisCarrier
public import TauCeti.Geometry.Symplectic.Hamiltonian.Localized.AlongMap
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Hamiltonian variations from a separable Banach carrier

Transversality for the inhomogeneous Cauchy–Riemann operator varies the Hamiltonian perturbation
along a separable Banach space of smooth Hamiltonians, so that the Sard–Smale theorem applies to
the universal moduli space. A variation `δK : P × V → ℝ` of the Hamiltonian, with `P` the domain
of the curves and `V` the symplectic target, enters the linearized operator at a map `u : P → V`
through the field `z ↦ X_{δK(z, ·)}(u z)` of Hamiltonian vectors along `u`.

This file takes the variations from the separable Banach carrier
`TauCeti.SupportedInCarrier (P × V) ℝ n C` of `C^n` functions supported in a compact set `C` of
`P × V` (`TauCeti.Analysis.Distribution.TestFunction.SynthesisCarrier`), for `1 ≤ n`, and shows
that they still detect covector fields: if an integrable field `η` of covectors along `u`
annihilates the Hamiltonian vector fields of every element of the carrier, then `η` vanishes almost
everywhere on each open set `Ω` over which the graph of `u` lies in the interior of `C`
(`SymplecticForm.ae_eq_zero_of_forall_integral_supportedInCarrierMap_eq_zero`).
This is the cokernel-detection step of transversality, with a parameter space to which Sard–Smale
applies. It holds whether `u` is constant or not.

The pairing `δK ↦ ∫ η z (X_{δK(z, ·)}(u z)) dμ` is a continuous linear functional on
`𝓓^{n}_{C}(P × V, ℝ)`, bounded by the `C¹` seminorm, since the Hamiltonian vector field of
`δK(z, ·)` vanishes off `C` and is bounded by the derivative of `δK`
(`SymplecticForm.norm_hamiltonianVectorField_le_seminorm`). The carrier is dense in
`𝓓^{n}_{C}(P × V, ℝ)`, so a functional vanishing on the carrier vanishes on every `C^n` function
supported in `C`, in particular on the smooth Hamiltonians supported in the interior of `C`, which
detect `η` by `SymplecticForm.ae_eq_zero_of_forall_integral_apply_hamiltonianVectorField_eq_zero`.

## Main results

* `SymplecticForm.hamiltonianVectorField_eq_zero_of_notMem`,
  `SymplecticForm.norm_hamiltonianVectorField_le_seminorm`: the Hamiltonian vector field of a
  function supported in `C` vanishes off `C` and is bounded by its `C¹` seminorm.
* `SymplecticForm.ae_eq_zero_of_forall_integral_supportedInCarrierMap_eq_zero`:
  Hamiltonian variations from the carrier detect covector fields along a map.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.2
  (transversality with a separable Banach space of perturbations) and Section 8.1 (Hamiltonian
  variations in the universal inhomogeneous Cauchy–Riemann operator).
* A. Floer, H. Hofer and D. Salamon, *Transversality in elliptic Morse theory for the symplectic
  action*, Duke Math. J. 80 (1995), 251–292.
-/

public section

open Set Topology Filter MeasureTheory TopologicalSpace
open scoped Distributions

namespace TauCeti.SymplecticForm

variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {n : ℕ∞}
  {C : Compacts (P × V)}

/-- The Hamiltonian vector field of a slice of a function supported in `C` vanishes at the points
off `C`, since the function vanishes near them. -/
theorem hamiltonianVectorField_eq_zero_of_notMem (ω : SymplecticForm V)
    (h : 𝓓^{n}_{C}(P × V, ℝ)) {z : P} {y : V} (hzy : (z, y) ∉ C) :
    ω.hamiltonianVectorField (fun y' ↦ h (z, y')) y = 0 := by
  have hC : IsOpen (Prod.mk z ⁻¹' (C : Set (P × V))ᶜ) :=
    C.isCompact.isClosed.isOpen_compl.preimage (Continuous.prodMk_right z)
  have hev : (fun y' ↦ h (z, y')) =ᶠ[𝓝 y] fun _ ↦ 0 :=
    eventually_of_mem (hC.mem_nhds hzy) fun _ hy' ↦ h.zero_on_compl hy'
  rw [ω.hamiltonianVectorField_congr_of_eventuallyEq hev, hamiltonianVectorField_eq_zero_iff]
  exact fderiv_const_apply 0

/-- The Hamiltonian vector field of a slice of a `C^n` function supported in `C`, `1 ≤ n`, is
bounded by the `C¹` seminorm of the function, up to the norm of the inverse of the contraction by
`ω`. -/
theorem norm_hamiltonianVectorField_le_seminorm (ω : SymplecticForm V) (hn : 1 ≤ n)
    (h : 𝓓^{n}_{C}(P × V, ℝ)) (z : P) (y : V) :
    ‖ω.hamiltonianVectorField (fun y' ↦ h (z, y')) y‖ ≤
      ‖ω.toBilinForm.toContinuousBilinearMap.inverse‖ *
        ContDiffMapSupportedIn.seminorm ℝ (P × V) ℝ n C 1 h := by
  have hd : DifferentiableAt ℝ h (z, y) :=
    (h.contDiff.differentiable (by exact_mod_cast (one_ne_zero.bot_lt.trans_le hn).ne')) _
  have hf : fderiv ℝ (fun y' ↦ h (z, y')) y =
      (fderiv ℝ h (z, y)).comp (ContinuousLinearMap.inr ℝ P V) :=
    (hd.hasFDerivAt.comp y (hasFDerivAt_prodMk_right z y)).fderiv
  rw [hamiltonianVectorField_def, hf]
  refine (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  calc ‖(fderiv ℝ h (z, y)).comp (ContinuousLinearMap.inr ℝ P V)‖
      ≤ ‖fderiv ℝ h (z, y)‖ * ‖ContinuousLinearMap.inr ℝ P V‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv ℝ h (z, y)‖ :=
        mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_inr_le_one _ _ _)
    _ = ‖iteratedFDeriv ℝ 1 h (z, y)‖ := (norm_iteratedFDeriv_one ..).symm
    _ ≤ ContDiffMapSupportedIn.seminorm ℝ (P × V) ℝ n C 1 h :=
        ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm ℝ (by exact_mod_cast hn)

/-- The Hamiltonian vector field is additive on the `C^n` functions supported in `C`, `1 ≤ n`. -/
private theorem hamiltonianVectorField_add_of_one_le (ω : SymplecticForm V) (hn : 1 ≤ n)
    (h g : 𝓓^{n}_{C}(P × V, ℝ)) (z : P) (y : V) :
    ω.hamiltonianVectorField (fun y' ↦ (h + g) (z, y')) y =
      ω.hamiltonianVectorField (fun y' ↦ h (z, y')) y +
        ω.hamiltonianVectorField (fun y' ↦ g (z, y')) y := by
  have hn' : (n : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (one_ne_zero.bot_lt.trans_le hn).ne'
  have hd (k : 𝓓^{n}_{C}(P × V, ℝ)) : DifferentiableAt ℝ (fun y' ↦ k (z, y')) y :=
    (k.contDiff.differentiable hn' _).comp y
      ((differentiableAt_const z).prodMk differentiableAt_id)
  simpa using ω.hamiltonianVectorField_const_mul_add_const_mul (hd h) (hd g) 1 1

variable [MeasurableSpace P] [BorelSpace P] {μ : Measure P}

/-- Along a map continuous on the projection of `C`, the pairing of an integrable covector field
with the Hamiltonian vector field of a `C^n` function supported in `C`, `1 ≤ n`, is integrable. -/
private theorem integrable_apply_hamiltonianVectorField (ω : SymplecticForm V) (hn : 1 ≤ n)
    {u : P → V} (hu : ContinuousOn u (Prod.fst '' (C : Set (P × V)))) {η : P → V →L[ℝ] ℝ}
    (hη : IntegrableOn η (Prod.fst '' (C : Set (P × V))) μ) (h : 𝓓^{n}_{C}(P × V, ℝ)) :
    Integrable (fun z ↦ η z (ω.hamiltonianVectorField (fun y ↦ h (z, y)) (u z))) μ := by
  set S : Set P := Prod.fst '' (C : Set (P × V))
  have hS : MeasurableSet S := (C.isCompact.image continuous_fst).isClosed.measurableSet
  -- Off `S` the point `(z, u z)` lies off `C`, so the integrand vanishes.
  refine (integrableOn_iff_integrable_of_support_subset (s := S) fun z hz ↦ ?_).1 ?_
  · by_contra hzS
    refine hz ?_
    simp only [ω.hamiltonianVectorField_eq_zero_of_notMem h fun hC ↦ hzS ⟨_, hC, rfl⟩, map_zero]
  -- On `S` the vector field is continuous and bounded by the `C¹` seminorm of `h`.
  have hX : ContinuousOn (fun z ↦ ω.hamiltonianVectorField (fun y ↦ h (z, y)) (u z)) S :=
    ω.continuousOn_hamiltonianVectorField_comp_of_contDiffOn (K := fun z y ↦ h (z, y)) hu
      ((h.contDiff.of_le (by exact_mod_cast hn)).contDiffOn)
  refine Integrable.mono' (hη.norm.mul_const (‖ω.toBilinForm.toContinuousBilinearMap.inverse‖ *
    ContDiffMapSupportedIn.seminorm ℝ (P × V) ℝ n C 1 h))
    ((ContinuousLinearMap.apply ℝ ℝ).aestronglyMeasurable_comp₂ (hX.aestronglyMeasurable hS)
      hη.aestronglyMeasurable) (Eventually.of_forall fun z ↦ ?_)
  exact ((η z).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (ω.norm_hamiltonianVectorField_le_seminorm hn h z (u z))
      (norm_nonneg _))

/-- The pairing `δK ↦ ∫ η z (X_{δK(z, ·)}(u z)) dμ` of an integrable covector field along `u` with
Hamiltonian variations, as a continuous linear functional on `𝓓^{n}_{C}(P × V, ℝ)`, `1 ≤ n`. -/
private noncomputable def hamiltonianPairing (ω : SymplecticForm V) (hn : 1 ≤ n) {u : P → V}
    (hu : ContinuousOn u (Prod.fst '' (C : Set (P × V)))) {η : P → V →L[ℝ] ℝ}
    (hη : IntegrableOn η (Prod.fst '' (C : Set (P × V))) μ) :
    𝓓^{n}_{C}(P × V, ℝ) →L[ℝ] ℝ :=
  ContDiffMapSupportedIn.mkCLMtoNormedSpace ℝ
    (fun h : 𝓓^{n}_{C}(P × V, ℝ) ↦ ∫ z, η z (ω.hamiltonianVectorField (fun y ↦ h (z, y)) (u z)) ∂μ)
    (fun h g ↦ by
      simp only [ω.hamiltonianVectorField_add_of_one_le hn h g, map_add]
      exact integral_add (ω.integrable_apply_hamiltonianVectorField hn hu hη h)
        (ω.integrable_apply_hamiltonianVectorField hn hu hη g))
    (fun c h ↦ by
      simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
        hamiltonianVectorField_const_mul, map_smul]
      exact integral_smul c _)
    ⟨{1}, ‖ω.toBilinForm.toContinuousBilinearMap.inverse‖ *
      ∫ z in Prod.fst '' (C : Set (P × V)), ‖η z‖ ∂μ, by positivity, fun h ↦ by
      set S : Set P := Prod.fst '' (C : Set (P × V))
      set B := ‖ω.toBilinForm.toContinuousBilinearMap.inverse‖ *
        ContDiffMapSupportedIn.seminorm ℝ (P × V) ℝ n C 1 h
      have hS : MeasurableSet S := (C.isCompact.image continuous_fst).isClosed.measurableSet
      -- The integrand is bounded by `‖η‖ * B` on `S` and vanishes off `S`.
      have hle : ∀ z, ‖η z (ω.hamiltonianVectorField (fun y ↦ h (z, y)) (u z))‖ ≤
          S.indicator (fun z ↦ ‖η z‖ * B) z := by
        intro z
        by_cases hzS : z ∈ S
        · rw [indicator_of_mem hzS]
          exact ((η z).le_opNorm _).trans (mul_le_mul_of_nonneg_left
            (ω.norm_hamiltonianVectorField_le_seminorm hn h z (u z)) (norm_nonneg _))
        · rw [indicator_of_notMem hzS, ω.hamiltonianVectorField_eq_zero_of_notMem h
            fun hC ↦ hzS ⟨_, hC, rfl⟩, map_zero, norm_zero]
      rw [Finset.sup_singleton]
      calc ‖∫ z, η z (ω.hamiltonianVectorField (fun y ↦ h (z, y)) (u z)) ∂μ‖
          ≤ ∫ z, S.indicator (fun z ↦ ‖η z‖ * B) z ∂μ :=
            norm_integral_le_of_norm_le ((integrable_indicator_iff hS).2
              (hη.norm.mul_const B)) (Eventually.of_forall hle)
        _ = ‖ω.toBilinForm.toContinuousBilinearMap.inverse‖ *
              (∫ z in S, ‖η z‖ ∂μ) * ContDiffMapSupportedIn.seminorm ℝ (P × V) ℝ n C 1 h := by
            rw [integral_indicator hS, integral_mul_const]
            ring⟩

variable [FiniteDimensional ℝ P] in
/-- **Hamiltonian variations from the separable Banach carrier detect covector fields.** Let `C`
be a compact set of `P × V`, let `u` be continuous on its projection to `P`, and let `η` be a field
of covectors along `u`, integrable on that projection. If `η` annihilates the Hamiltonian vector
fields `z ↦ X_{δK(z, ·)}(u z)` of every element `δK` of the carrier
`TauCeti.SupportedInCarrier (P × V) ℝ n C`, `1 ≤ n`, in the sense that
`∫ η z (X_{δK(z, ·)}(u z)) dμ = 0`, then `η` vanishes almost everywhere on every open set `Ω` over
which the graph of `u` lies in the interior of `C`. -/
theorem ae_eq_zero_of_forall_integral_supportedInCarrierMap_eq_zero
    (ω : SymplecticForm V) (hn : 1 ≤ n) {u : P → V}
    (hu : ContinuousOn u (Prod.fst '' (C : Set (P × V)))) {Ω : Set P} (hΩ : IsOpen Ω)
    (hΩC : ∀ z ∈ Ω, (z, u z) ∈ interior (C : Set (P × V))) {η : P → V →L[ℝ] ℝ}
    (hη : IntegrableOn η (Prod.fst '' (C : Set (P × V))) μ)
    (h : ∀ x : SupportedInCarrier (P × V) ℝ n C,
      ∫ z, η z (ω.hamiltonianVectorField
        (fun y ↦ supportedInCarrierMap (P × V) ℝ n C x (z, y)) (u z)) ∂μ = 0) :
    ∀ᵐ z ∂μ, z ∈ Ω → η z = 0 := by
  have hΩS : Ω ⊆ Prod.fst '' (C : Set (P × V)) := fun z hz ↦
    ⟨(z, u z), interior_subset (hΩC z hz), rfl⟩
  -- The pairing vanishes on the dense carrier, hence on all of `𝓓^{n}_{C}(P × V, ℝ)`.
  have hL : ⇑(ω.hamiltonianPairing hn hu hη) = 0 :=
    (denseRange_supportedInCarrierMap (P × V) ℝ n C).equalizer
      (ω.hamiltonianPairing hn hu hη).continuous continuous_const (funext h)
  refine ω.ae_eq_zero_of_forall_integral_apply_hamiltonianVectorField_eq_zero hΩ (hu.mono hΩS)
    (fun z hz ↦ isOpen_interior.mem_nhds (hΩC z hz)) (hη.mono_set hΩS).locallyIntegrableOn
    fun K hK _ hKC ↦ ?_
  -- A smooth Hamiltonian supported in the interior of `C` is a `C^n` function supported in `C`.
  exact congrFun hL (ContDiffMapSupportedIn.of_support_subset (hK.of_le (by exact_mod_cast le_top))
    (subset_tsupport _ |>.trans (hKC.trans interior_subset)))

end TauCeti.SymplecticForm
