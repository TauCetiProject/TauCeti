/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Basic
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# Localized Hamiltonian variations along a map

Let `u : P → V` be a map from a finite-dimensional parameter space into a symplectic vector space,
continuous on an open set `Ω`. A Hamiltonian `K : P → V → ℝ` depending on the parameter gives the
field `z ↦ X_{K z}(u z)` of Hamiltonian vectors along `u`. This is how a variation `δK` of the
Hamiltonian perturbation enters the linearized inhomogeneous Cauchy–Riemann operator at a map `u`.

* Every smooth compactly supported field `ξ` along `u` with support in `Ω` is of this form, for a
  smooth compactly supported `K` localized in any prescribed neighborhood `W` of the graph of `u`
  over `Ω` (`SymplecticForm.exists_contDiff_hamiltonianVectorField_comp_eq`). One may take
  `K(z, y) = χ(z, y) ω(ξ z, y)` for a bump function `χ` equal to `1` near the graph of `u` over the
  support of `ξ`, since the Hamiltonian vector field of the linear function `ω(a, ·)` is `a`.
* Consequently these fields detect every locally integrable field `η` of covectors along `u`: if
  `∫ η z (X_{K z}(u z)) dμ = 0` for all such `K`, then `η = 0` almost everywhere on `Ω`
  (`SymplecticForm.ae_eq_zero_of_forall_integral_apply_hamiltonianVectorField_eq_zero`). This is
  the fundamental lemma of the calculus of variations,
  `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`, applied to the components of `η`.

No hypothesis is placed on `u` beyond continuity. In particular `u` may be constant, in contrast
with variations of an almost complex structure, which act through the derivative of `u`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on
  Hamiltonian variations in the universal inhomogeneous Cauchy–Riemann operator.
* A. Floer, H. Hofer and D. Salamon, *Transversality in elliptic Morse theory for the symplectic
  action*, Duke Math. J. 80 (1995), 251–292.
-/

public section

open Set Topology Filter MeasureTheory

namespace TauCeti.SymplecticForm

variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Hamiltonian variations realize every field along a map.** Let `u` be continuous on an open
set `Ω`, and let `W` be a neighborhood of each point `(z, u z)` with `z ∈ Ω`. Every smooth
compactly supported field `ξ` with support in `Ω` is the field `z ↦ X_{K z}(u z)` of Hamiltonian
vectors of a smooth compactly supported Hamiltonian `K` supported in `W`. The identity holds at
every parameter, not only on `Ω`. -/
theorem exists_contDiff_hamiltonianVectorField_comp_eq (ω : SymplecticForm V) {u : P → V}
    {Ω : Set P} (hu : ContinuousOn u Ω) {W : Set (P × V)} (hW : ∀ z ∈ Ω, W ∈ 𝓝 (z, u z))
    {ξ : P → V} (hξ : ContDiff ℝ (⊤ : ℕ∞) ξ) (hξc : HasCompactSupport ξ) (hξΩ : tsupport ξ ⊆ Ω) :
    ∃ K : P → V → ℝ, ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry K) ∧
      HasCompactSupport (Function.uncurry K) ∧ tsupport (Function.uncurry K) ⊆ W ∧
      ∀ z, ω.hamiltonianVectorField (K z) (u z) = ξ z := by
  -- The graph of `u` over the support of `ξ` is a compact subset of the interior of `W`.
  set G : Set (P × V) := (fun z ↦ (z, u z)) '' tsupport ξ
  have hGc : IsCompact G :=
    hξc.isCompact.image_of_continuousOn (continuousOn_id.prodMk (hu.mono hξΩ))
  have hGW : G ⊆ interior W := by
    rintro _ ⟨z, hz, rfl⟩
    exact mem_interior_iff_mem_nhds.mpr (hW z (hξΩ hz))
  -- A bump function equal to `1` near the graph and supported in the interior of `W`.
  obtain ⟨χ, hχ, -, hχ1, hχc, hχW⟩ :=
    hGc.exists_contDiff_cutoff_eventuallyEq_one isOpen_interior hGW
  -- The Hamiltonian is `ω(ξ z, ·)` near the graph and vanishes off the support of `ξ`.
  have hX (z : P) :
      ω.hamiltonianVectorField (fun y ↦ χ (z, y) * ω (ξ z) y) (u z) = ξ z := by
    by_cases hz : z ∈ tsupport ξ
    · have hev : ∀ᶠ y in 𝓝 (u z), χ (z, y) = 1 :=
        (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
          (hχ1 _ (mem_image_of_mem _ hz))
      have hK : (fun y ↦ χ (z, y) * ω (ξ z) y) =ᶠ[𝓝 (u z)] fun y ↦ ω (ξ z) y :=
        hev.mono fun y hy ↦ by simp [hy]
      rw [ω.hamiltonianVectorField_congr_of_eventuallyEq hK, hamiltonianVectorField_apply_left]
    · have hξz : ξ z = 0 := image_eq_zero_of_notMem_tsupport hz
      have hK : (fun y ↦ χ (z, y) * ω (ξ z) y) = fun _ ↦ (0 : ℝ) := by
        ext y
        simp [hξz]
      rw [hK, hamiltonianVectorField_const, hξz, Pi.zero_apply]
  -- The coercion of `ω` to a function agrees definitionally with the continuous bilinear map `B`,
  -- so smoothness of `p ↦ B (ξ p.1) p.2` is smoothness of `p ↦ ω (ξ p.1) p.2`.
  let B := ω.toBilinForm.toContinuousBilinearMap
  refine ⟨fun z y ↦ χ (z, y) * ω (ξ z) y, ?_, ?_, ?_, hX⟩
  · have hB : ContDiff ℝ (⊤ : ℕ∞) fun p : P × V ↦ B (ξ p.1) p.2 :=
      (B.contDiff.comp (hξ.comp contDiff_fst)).clm_apply contDiff_snd
    exact hχ.mul hB
  · exact hχc.mul_right
  · exact tsupport_mul_subset_left.trans (hχW.trans interior_subset)

variable [MeasurableSpace P] [BorelSpace P] {μ : Measure P}

/-- **Localized Hamiltonian variations detect covector fields along a map.** Let `u` be
continuous on an open set `Ω`, let `W` be a neighborhood of each point `(z, u z)` with `z ∈ Ω`,
and let `η` be a locally integrable field of covectors on `Ω`. If `η` annihilates the Hamiltonian
vector fields `z ↦ X_{K z}(u z)` of all smooth compactly supported Hamiltonians `K` supported in
`W`, in the sense that `∫ η z (X_{K z}(u z)) dμ = 0`, then `η` vanishes almost everywhere
on `Ω`. -/
theorem ae_eq_zero_of_forall_integral_apply_hamiltonianVectorField_eq_zero
    (ω : SymplecticForm V) {u : P → V} {Ω : Set P} (hΩ : IsOpen Ω) (hu : ContinuousOn u Ω)
    {W : Set (P × V)} (hW : ∀ z ∈ Ω, W ∈ 𝓝 (z, u z)) {η : P → V →L[ℝ] ℝ}
    (hη : LocallyIntegrableOn η Ω μ)
    (h : ∀ K : P → V → ℝ, ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry K) →
      HasCompactSupport (Function.uncurry K) → tsupport (Function.uncurry K) ⊆ W →
        ∫ z, η z (ω.hamiltonianVectorField (K z) (u z)) ∂μ = 0) :
    ∀ᵐ z ∂μ, z ∈ Ω → η z = 0 := by
  -- Each component `z ↦ η z v` vanishes almost everywhere, by testing against `g • v`.
  have hv (v : V) : ∀ᵐ z ∂μ, z ∈ Ω → η z v = 0 := by
    refine hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((ContinuousLinearMap.apply ℝ ℝ v).locallyIntegrableOn_comp hη) fun g hg hgc hgΩ ↦ ?_
    obtain ⟨K, hK, hKc, hKW, hKξ⟩ := ω.exists_contDiff_hamiltonianVectorField_comp_eq hu hW
      (ξ := fun z ↦ g z • v) (hg.smul contDiff_const) (hgc.smul_right (f' := fun _ ↦ v))
      ((tsupport_smul_subset_left g fun _ ↦ v).trans hgΩ)
    simpa only [hKξ, map_smul, Function.comp_apply, ContinuousLinearMap.apply_apply]
      using h K hK hKc hKW
  -- A basis of `V` turns the component statements into the statement for `η`.
  let b := Module.finBasis ℝ V
  filter_upwards [ae_all_iff.mpr fun i ↦ hv (b i)] with z hz hzΩ
  exact ContinuousLinearMap.coe_injective (b.ext fun i ↦ by simpa using hz i hzΩ)

end TauCeti.SymplecticForm
