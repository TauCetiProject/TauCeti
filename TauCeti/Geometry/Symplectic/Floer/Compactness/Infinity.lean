/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Basic
public import TauCeti.Geometry.Symplectic.JHolomorphic.RealChart
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Function.Jacobian
import TauCeti.Analysis.Normed.Field.Inversion
import TauCeti.Geometry.Symplectic.Floer.Pullback
import TauCeti.MeasureTheory.Function.Jacobian.Plane

/-!
# Compactness at the point at infinity

A domain of Floer theory such as the three-pole sphere of the pair-of-pants/quantum-product
comparison is a Riemann sphere `ℂ ∪ {∞}`, and its maps are written in the plane chart `ℂ ≅ ℝ × ℝ`.
The compactness theorems of `TauCeti.Geometry.Symplectic.Floer.Compactness.Basic` apply on compact
windows of that chart, so they say nothing about a neighbourhood of `∞`. Near `∞` the data of such
problems are usually standard: there is no Hamiltonian perturbation and the almost complex
structure is a fixed `J₀`, so the solutions are `J₀`-holomorphic there. This file proves the
compactness theorem near `∞` in the chart `w ↦ w⁻¹`.

Let `u` be `J₀`-holomorphic at every point `z` with `‖z‖ > T`, in complex coordinates, and let `w`
be its expression `w(y) = u(y⁻¹)` in the chart at infinity, defined and `C¹` on an open set `Ω` of
the disc `‖y‖ < T⁻¹` including possibly its centre `0`, which is the point `∞`.

* `w` is `J₀`-holomorphic on all of `Ω`, the point at infinity included
  (`TauCeti.isComplexLinearMap_fderiv_of_eq_comp_inv`).
* The symplectic area density of `w` is that of `u` pulled back along the inversion, which is
  holomorphic and injective. So if the area density of `u` is integrable outside the disc of radius
  `T`, then that of `w` is integrable on `Ω`, and its integral over `Ω` is at most the area of `u`
  outside the disc (`TauCeti.SymplecticForm.integrableOn_and_setIntegral_le_of_eq_comp_inv`).
  Here `J₀` is tamed by the symplectic form, so the area density of `u` is nonnegative there.
* **Compactness at infinity**
  (`TauCeti.SymplecticForm.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_inv`):
  for a compact `K` there is a threshold `δ > 0` such that every sequence of such maps `uₖ`, with
  areas outside the disc of radius `T` at most `E` and expressions `wₖ` that are `C³` on `Ω` with
  values in `K`, has a subsequence along which the `wₖ` converge locally uniformly on `Ω` off a
  finite set `Z` of bubbling points, with `#Z * δ ≤ E`, and at least `δ` of area concentrating at
  each point of `Z`.

The `C³` regularity of `wₖ` at `0` is a hypothesis: it is the removal of the singularity of `uₖ`
at `∞`, which is not proved here.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 2.2
  (the energy depends only on the conformal structure of the domain), Section 4.5 (removal of
  singularities) and Section 4.6 (bubbling off finitely many points).
-/

public section

open Complex Filter Function MeasureTheory Metric Set Topology
open TauCeti.Complex (realChart equivRealProdCLM_symm_realChart hasFDerivAt_realChart
  det_fderiv_realChart_nonneg realChart_injective)

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {J₀ : AlmostComplexStructure V} {u w : ℝ × ℝ → V} {Ω : Set (ℝ × ℝ)} {T : ℝ}

/-- **The area near infinity in the chart at infinity.** Let `u` be differentiable and
`J₀`-holomorphic at every point `z` with `‖z‖ > T`, in complex coordinates, for a structure `J₀`
tamed by `ω`, with integrable area density `ω(∂ₛu, ∂ₜu)` on that exterior. Let `w` agree with
`y ↦ u(y⁻¹)` on an open set `Ω` of the disc `‖y‖ < T⁻¹`, except possibly at `0`. Then the area
density of `w` is integrable on `Ω`, and its integral over `Ω` is at most the area of `u` outside
the disc of radius `T`. -/
theorem integrableOn_and_setIntegral_le_of_eq_comp_inv (ω : SymplecticForm V) (hJ₀ : ω.Tames J₀)
    (hΩ : IsOpen Ω) (hΩT : Ω ⊆ equivRealProdCLM.symm ⁻¹' ball 0 T⁻¹)
    (hu : ∀ z ∈ equivRealProdCLM.symm ⁻¹' (closedBall 0 T)ᶜ, DifferentiableAt ℝ u z)
    (hhol : ∀ z ∈ equivRealProdCLM.symm ⁻¹' (closedBall 0 T)ᶜ,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) J₀ (fderiv ℝ u z : ℝ × ℝ →ₗ[ℝ] V))
    (hint : IntegrableOn (fun z ↦ ω (fderiv ℝ u z stdComplexLineReal)
      (fderiv ℝ u z stdComplexLineImag)) (equivRealProdCLM.symm ⁻¹' (closedBall 0 T)ᶜ))
    (hwu : ∀ y ∈ Ω, y ≠ 0 → w y = u (realChart (fun ζ ↦ ζ⁻¹) y)) :
    IntegrableOn (fun y ↦ ω (fderiv ℝ w y stdComplexLineReal) (fderiv ℝ w y stdComplexLineImag))
        Ω ∧
      ∫ y in Ω, ω (fderiv ℝ w y stdComplexLineReal) (fderiv ℝ w y stdComplexLineImag) ≤
        ∫ z in equivRealProdCLM.symm ⁻¹' (closedBall 0 T)ᶜ,
          ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag) := by
  set ι : ℝ × ℝ → ℝ × ℝ := realChart fun ζ ↦ ζ⁻¹
  set S : Set (ℝ × ℝ) := equivRealProdCLM.symm ⁻¹' (closedBall 0 T)ᶜ
  set s : Set (ℝ × ℝ) := Ω \ {0}
  have hso : IsOpen s := hΩ.sdiff isClosed_singleton
  -- On the punctured window the inversion `ι` is holomorphic, injective, and lands in `S`.
  have hder (y : ℝ × ℝ) (hy : y ∈ s) : HasDerivAt (fun ζ : ℂ ↦ ζ⁻¹)
      (-((equivRealProdCLM.symm y) ^ 2)⁻¹) (equivRealProdCLM.symm y) :=
    hasDerivAt_inv (by simpa using hy.2)
  have hmaps : MapsTo ι s S := fun y hy ↦ by
    rw [mem_preimage, equivRealProdCLM_symm_realChart]
    exact mapsTo_inv_ball_diff_singleton_compl_closedBall T ⟨hΩT hy.1, by simpa using hy.2⟩
  have hinj : InjOn ι s := (realChart_injective inv_injective).injOn
  -- With zero perturbation the Floer energy density is the area density.
  simp only [← floerEnergyDensity_zero] at hint ⊢
  -- The area density of `w` on the punctured window is that of `u` pulled back along `ι`.
  have hdens (y : ℝ × ℝ) (hy : y ∈ s) :
      ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) w y =
        |(fderiv ℝ ι y).det| • ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u (ι y) := by
    have h := ω.floerEnergyDensity_perturbationPullback (φ := ι) (Ks := fun _ _ ↦ 0)
      (Kt := fun _ _ ↦ 0) (hasFDerivAt_realChart (hder y hy)).differentiableAt
      (hu _ (hmaps hy)) (differentiableAt_const _) (differentiableAt_const _)
    rw [perturbationPullback_zero, perturbationPullback_zero] at h
    have hev : w =ᶠ[𝓝 y] u ∘ ι := by
      filter_upwards [hso.mem_nhds hy] with y' hy' using hwu y' hy'.1 hy'.2
    rw [ω.floerEnergyDensity_congr_of_eventuallyEq _ _ hev, h,
      abs_of_nonneg (det_fderiv_realChart_nonneg (hder y hy)), smul_eq_mul]
  -- Change variables along `ι`; the puncture `0` is a null set.
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  have hnull : s =ᵐ[volume] Ω := sdiff_null_ae_eq_self (measure_singleton 0)
  refine ⟨((integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hso.measurableSet
    (fun y hy ↦ (hasFDerivAt_realChart (hder y hy)).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
      hinj _).1
      (hint.mono_set hmaps.image_subset) |>.congr_fun (fun y hy ↦ (hdens y hy).symm)
        hso.measurableSet).congr_set_ae hnull.symm, ?_⟩
  have hnn : ∀ᵐ z ∂(volume.restrict S),
      0 ≤ ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u z := by
    refine ae_restrict_of_forall_mem ((isClosed_closedBall.isOpen_compl).preimage
      equivRealProdCLM.symm.continuous).measurableSet fun z hz ↦ ?_
    refine ω.floerEnergyDensity_nonneg hJ₀ ?_
    rw [perturbedFDeriv_const ω (fun _ ↦ 0) (fun _ ↦ 0)]
    exact hhol z hz
  rw [← setIntegral_congr_set hnull, ← integral_image_eq_integral_of_eq_abs_det_smul
    hso.measurableSet hinj (fun y hy ↦ (hasFDerivAt_realChart (hder y hy)).differentiableAt) hdens]
  exact setIntegral_mono_set hint hnn (Eventually.of_forall hmaps.image_subset)

/-- **Compactness at infinity.** Let `J₀` be tamed by `ω` and `K ⊆ V` be compact. There is a
threshold `δ > 0` with the following property. Let `uₖ` be differentiable and `J₀`-holomorphic at
every point `z` with `‖z‖ > T`, in complex coordinates, with integrable area density
`ω(∂ₛuₖ, ∂ₜuₖ)` on that exterior and area there at most `E`. Let `wₖ` be `C³` maps on an open set
`Ω` of the disc `‖y‖ < T⁻¹` of the chart at infinity, with `wₖ(y) = uₖ(y⁻¹)` for `y ≠ 0` and
`wₖ(Ω) ⊆ K`. Then there are a subsequence `φ`, a finite set `Z ⊆ Ω` with `#Z * δ ≤ E`, and a
continuous `v : Ω \ Z → K` such that along `φ` every disc about a point of `Z` eventually carries
area of `wₖ` at least `δ`, the differentials of the `wₖ` are uniformly bounded on every compact
subset of `Ω \ Z`, and `w_{φ n} → v` locally uniformly on `Ω \ Z`. The point `0` of `Ω`, the
point at infinity, is treated like any other. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_inv (ω : SymplecticForm V)
    (hJ₀ : ω.Tames J₀) (T : ℝ) {K : Set V} (hK : IsCompact K) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃u w : ℕ → ℝ × ℝ → V⦄ ⦃E : ℝ⦄, IsOpen Ω →
      Ω ⊆ equivRealProdCLM.symm ⁻¹' ball 0 T⁻¹ →
      (∀ k, ∀ z ∈ equivRealProdCLM.symm ⁻¹' (closedBall 0 T)ᶜ, DifferentiableAt ℝ (u k) z) →
      (∀ k, ∀ z ∈ equivRealProdCLM.symm ⁻¹' (closedBall 0 T)ᶜ, IsComplexLinearMap
        (AlmostComplexStructure.product ℝ) J₀ (fderiv ℝ (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k, IntegrableOn (fun z ↦ ω (fderiv ℝ (u k) z stdComplexLineReal)
        (fderiv ℝ (u k) z stdComplexLineImag)) (equivRealProdCLM.symm ⁻¹' (closedBall 0 T)ᶜ)) →
      (∀ k, ∫ z in equivRealProdCLM.symm ⁻¹' (closedBall 0 T)ᶜ,
        ω (fderiv ℝ (u k) z stdComplexLineReal) (fderiv ℝ (u k) z stdComplexLineImag) ≤ E) →
      (∀ k, ContDiffOn ℝ 3 (w k) Ω) →
      (∀ k, ∀ y ∈ Ω, y ≠ 0 → w k y = u k (realChart (fun ζ ↦ ζ⁻¹) y)) →
      (∀ k, MapsTo (w k) Ω K) →
      ∃ (φ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ E ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω,
          ω (fderiv ℝ (w (φ n)) y stdComplexLineReal) (fderiv ℝ (w (φ n)) y stdComplexLineImag)) ∧
        (∀ C, IsCompact C → C ⊆ Ω \ ↑Z →
          ∃ M, ∀ n, ∀ y ∈ C, ‖fderiv ℝ (w (φ n)) y‖ ≤ M) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ w (φ n)) v atTop (Ω \ ↑Z) := by
  -- The compactness theorem for the unperturbed equation of `J₀` on the closed disc of radius
  -- `T⁻¹` of the chart at infinity.
  have hD : IsCompact (equivRealProdCLM.symm ⁻¹' closedBall (0 : ℂ) T⁻¹) :=
    equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2 (isCompact_closedBall _ _)
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset
    (Ks := fun _ _ ↦ 0) (Kt := fun _ _ ↦ 0) (J := fun _ _ ↦ J₀) (W := univ) isOpen_univ
    contDiffOn_const contDiffOn_const contDiffOn_const hD hK (subset_univ _)
    fun _ _ _ _ ↦ hJ₀
  refine ⟨δ, hδ, fun Ω u w E hΩ hΩT hu hhol hint hE hw hwu hwK ↦ ?_⟩
  have hwE (k : ℕ) := ω.integrableOn_and_setIntegral_le_of_eq_comp_inv hJ₀ hΩ hΩT (hu k)
    (hhol k) (hint k) (hwu k)
  obtain ⟨φ, Z, v, hφ, hZΩ, hcard, hconc, hbd, hvc, hvK, hlim⟩ := hconv hΩ
    (hΩT.trans (preimage_mono ball_subset_closedBall)) hw
    (fun k y hy ↦ by
      rw [perturbedFDeriv_const ω (fun _ ↦ 0) (fun _ ↦ 0)]
      exact isComplexLinearMap_fderiv_of_eq_comp_inv hΩ hΩT (hu k) (hhol k)
        ((hw k).of_le (by norm_num)) (hwu k) hy) hwK
    (fun k ↦ by simpa only [← floerEnergyDensity_zero] using (hwE k).1)
    (fun k ↦ by simpa only [← floerEnergyDensity_zero] using (hwE k).2.trans (hE k))
  refine ⟨φ, Z, v, hφ, hZΩ, hcard, fun z hz ε hε ↦ ?_, hbd, hvc, hvK, hlim⟩
  simpa only [floerEnergyDensity_zero] using hconc z hz ε hε

end TauCeti.SymplecticForm
