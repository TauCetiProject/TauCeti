/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Basic
public import TauCeti.Geometry.Symplectic.Floer.Compactness.Closed
public import TauCeti.Geometry.Symplectic.JHolomorphic.RealChart
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Function.Jacobian
import TauCeti.Analysis.Normed.Field.Inversion
import TauCeti.Geometry.Symplectic.Floer.Manifold.Germ
import TauCeti.Geometry.Symplectic.Floer.Pullback
import TauCeti.Geometry.Symplectic.JHolomorphic.RemovableSingularity.Smooth
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

The `C³` regularity of `wₖ` at `0` is the removal of the singularity of `uₖ` at `∞`. When the inner
product of `V` is the metric `⟪v, w⟫ = ω(v, J₀ w)` of `J₀`, it follows from the hypotheses on
`uₖ` alone, once `uₖ` takes values in `K` outside the disc of radius `T`: by the removal of the
singularity at infinity in real coordinates
(`TauCeti.SymplecticForm.exists_tendsto_cocompact_and_contDiffOn_update_comp_inv`, in
`TauCeti.Geometry.Symplectic.JHolomorphic.RemovableSingularity.Smooth`), each `uₖ` has a limit
`qₖ ∈ K` at infinity, and `y ↦ uₖ(y⁻¹)`, filled with `qₖ` at `0`, is smooth on the disc of radius
`T⁻¹`.

* **Compactness at infinity with the singularity removed**
  (`exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_update_inv`, in the namespace
  `TauCeti.SymplecticForm`): the compactness theorem at infinity for these filled maps, with no
  hypothesis on the `wₖ`.

The same holds for maps into a closed manifold `M` with a nondegenerate two-form `ω` and a smooth
almost complex structure `J₀` tamed by `ω`, in the namespace `TauCeti.SmoothTwoForm`. Holomorphy is
the Floer equation with zero perturbation, and sizes in `M` are measured through an injective
differentiable map `e : M → F`, such as the Whitney embedding.

* Holomorphy extends across a single point of a `C¹` map, since both sides of the equation
  `∂ₜv = J₀(v) ∂ₛv` in the chart at its value there are continuous
  (`TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_zero_of_forall_ne`). Hence `w` is
  `J₀`-holomorphic on all of `Ω`, the point at infinity included
  (`TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_zero_of_eq_comp_inv`).
* The area of `w` over `Ω` is at most the area of `u` outside the disc of radius `T`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.integrableOn_and_setIntegral_le_of_eq_comp_inv`).
* **Compactness at infinity in a closed manifold**
  (`IsNondegenerate.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_inv`, in
  the namespace `TauCeti.SmoothTwoForm`): as above, with no condition on where the maps take
  their values; the maps converge locally uniformly after applying `e`, and pointwise in `M`.
  This is the compactness theorem in a closed manifold
  (`TauCeti.Geometry.Symplectic.Floer.Compactness.Closed`) for the unperturbed equation of `J₀` on
  the closed disc of radius `T⁻¹`.

For maps into a closed manifold `M` the `C³` regularity of `wₖ` at `0` remains a hypothesis: the
removal of the singularity at `∞` is not proved here for manifold targets.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 2.2
  (the energy depends only on the conformal structure of the domain), Section 4.5 (removal of
  singularities) and Section 4.6 (bubbling off finitely many points).
-/

public section

open Complex Filter Function MeasureTheory Metric Set Topology
open scoped Manifold
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

/-- **Compactness at infinity with the singularity removed.** Let the inner product of `V` be the
metric `⟪v, w⟫ = ω(v, J₀ w)` of `J₀`, and let `K ⊆ V` be compact. There is a threshold `δ > 0`
with the following property. Let `uₖ` be `C¹` and `J₀`-holomorphic on the exterior `‖z‖ > T` of
a disc, in complex coordinates, with values in `K` there, integrable area density `ω(∂ₛuₖ, ∂ₜuₖ)`
on that exterior and area there at most `E`. Then each `uₖ` has a limit `qₖ ∈ K` at infinity, and
its expression `wₖ(y) = uₖ(y⁻¹)` in the chart at infinity, filled with `qₖ` at `0`, is smooth on
the disc `‖y‖ < T⁻¹`. For every open set `Ω` of that disc there are a subsequence `φ`, a finite set
`Z ⊆ Ω` with `#Z * δ ≤ E`, and a continuous `v : Ω \ Z → K` such that along `φ` every disc about a
point of `Z` eventually carries area of `wₖ` at least `δ`, the differentials of the `wₖ` are
uniformly bounded on every compact subset of `Ω \ Z`, and `w_{φ n} → v` locally uniformly on
`Ω \ Z`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_update_inv
    (ω : SymplecticForm V) (hg : ∀ v w, ω v (J₀ w) = inner ℝ v w) (T : ℝ) {K : Set V}
    (hK : IsCompact K) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃E : ℝ⦄, IsOpen Ω →
      Ω ⊆ equivRealProdCLM.symm ⁻¹' ball 0 T⁻¹ →
      (∀ k, ContDiffOn ℝ 1 (u k) (equivRealProdCLM.symm ⁻¹' (closedBall 0 T)ᶜ)) →
      (∀ k, ∀ z ∈ equivRealProdCLM.symm ⁻¹' (closedBall 0 T)ᶜ, IsComplexLinearMap
        (AlmostComplexStructure.product ℝ) J₀ (fderiv ℝ (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k, IntegrableOn (fun z ↦ ω (fderiv ℝ (u k) z stdComplexLineReal)
        (fderiv ℝ (u k) z stdComplexLineImag)) (equivRealProdCLM.symm ⁻¹' (closedBall 0 T)ᶜ)) →
      (∀ k, ∫ z in equivRealProdCLM.symm ⁻¹' (closedBall 0 T)ᶜ,
        ω (fderiv ℝ (u k) z stdComplexLineReal) (fderiv ℝ (u k) z stdComplexLineImag) ≤ E) →
      (∀ k, MapsTo (u k) (equivRealProdCLM.symm ⁻¹' (closedBall 0 T)ᶜ) K) →
      ∃ (q : ℕ → V) (w : ℕ → ℝ × ℝ → V),
        (∀ k, q k ∈ K ∧ Tendsto (u k) (cocompact (ℝ × ℝ)) (𝓝 (q k))) ∧
        (∀ k, w k = update (fun y ↦ u k (realChart (fun ζ ↦ ζ⁻¹) y)) 0 (q k)) ∧
        (∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (w k) (equivRealProdCLM.symm ⁻¹' ball 0 T⁻¹)) ∧
        ∃ (φ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧
          ↑Z ⊆ Ω ∧ Z.card * δ ≤ E ∧
          (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω,
            ω (fderiv ℝ (w (φ n)) y stdComplexLineReal)
              (fderiv ℝ (w (φ n)) y stdComplexLineImag)) ∧
          (∀ C, IsCompact C → C ⊆ Ω \ ↑Z →
            ∃ M, ∀ n, ∀ y ∈ C, ‖fderiv ℝ (w (φ n)) y‖ ≤ M) ∧
          ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
          TendstoLocallyUniformlyOn (fun n ↦ w (φ n)) v atTop (Ω \ ↑Z) := by
  have hJ₀ : ω.Tames J₀ := fun v hv ↦ by
    rw [hg]
    exact real_inner_self_pos.2 hv
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_inv
    hJ₀ T hK
  refine ⟨δ, hδ, fun Ω u E hΩ hΩT hu hhol hint hE huK ↦ ?_⟩
  choose q hq hlim hmaps hw using fun k ↦
    ω.exists_tendsto_cocompact_and_contDiffOn_update_comp_inv hg hK (hu k) (hhol k) (hint k)
      (huK k)
  have hSo : IsOpen (equivRealProdCLM.symm ⁻¹' (closedBall (0 : ℂ) T)ᶜ) :=
    isClosed_closedBall.isOpen_compl.preimage equivRealProdCLM.symm.continuous
  refine ⟨q, _, fun k ↦ ⟨hq k, hlim k⟩, fun k ↦ rfl, hw, hconv hΩ hΩT
    (fun k z hz ↦ ((hu k).differentiableOn one_ne_zero z hz).differentiableAt (hSo.mem_nhds hz))
    hhol hint hE (fun k ↦ ((hw k).mono hΩT).of_le (WithTop.coe_le_coe.2 le_top))
    (fun k y _ hy ↦ update_of_ne hy _ _) fun k ↦ (hmaps k).mono_left hΩT⟩

end TauCeti.SymplecticForm

namespace TauCeti.SmoothTwoForm

open Floer

variable {E G M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]
  [IsManifold I (⊤ : ℕ∞) M] {ω : SmoothTwoForm I M} {J₀ : SmoothAlmostComplexStructure I M}
  {u w : ℝ × ℝ → M} {Ω : Set (ℝ × ℝ)} {T : ℝ}

/-- **Holomorphy extends across a point.** Let `w` be `C¹` on an open set `Ω` of `ℝ × ℝ`, with
values in a manifold `M`, and holomorphic for a smooth almost complex structure `J₀` on `M` at
every point of `Ω` except possibly `y₀ ∈ Ω`, in the form of the Floer equation with zero
perturbation. Then `w` is `J₀`-holomorphic at `y₀` as well: in the chart at `w y₀`, both sides of
the equation `∂ₜv = J₀(v) ∂ₛv` for `v = φ ∘ w` are continuous. -/
theorem isComplexLinearMap_perturbedMFDeriv_zero_of_forall_ne
    (ω : SmoothTwoForm I M) (J₀ : SmoothAlmostComplexStructure I M) (hΩ : IsOpen Ω)
    (hw : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 w Ω) {y₀ : ℝ × ℝ} (hy₀ : y₀ ∈ Ω)
    (h : ∀ y ∈ Ω, y ≠ y₀ → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J₀.almostComplexStructureAt (w y))
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun _ _ ↦ 0) w y).toLinearMap) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J₀.almostComplexStructureAt (w y₀))
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun _ _ ↦ 0) w y₀).toLinearMap := by
  set α := w y₀
  set φ := extChartAt I α
  set U : Set (ℝ × ℝ) := Ω ∩ w ⁻¹' φ.source
  have hU : IsOpen U := hw.continuousOn.isOpen_inter_preimage hΩ (isOpen_extChartAt_source α)
  have hy₀U : y₀ ∈ U := ⟨hy₀, mem_extChartAt_source α⟩
  have hv : ContDiffOn ℝ 1 (φ ∘ w) U := contMDiffOn_iff_contDiffOn.1 <|
    (contMDiffOn_extChartAt (n := 1)).comp (hw.mono inter_subset_left)
      fun y hy ↦ by rw [mem_preimage, ← extChartAt_source I]; exact hy.2
  have hdv : ContinuousOn (fderiv ℝ (φ ∘ w)) U := hv.continuousOn_fderiv_of_isOpen hU le_rfl
  -- The equation at `y ∈ U` in the chart: `∂ₜv = J₀(v) ∂ₛv`.
  have hiff (y : ℝ × ℝ) (hy : y ∈ U) :
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J₀.almostComplexStructureAt (w y))
        (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun _ _ ↦ 0) w y).toLinearMap ↔
      fderiv ℝ (φ ∘ w) y stdComplexLineImag =
        J₀.inChart α (φ (w y)) (fderiv ℝ (φ ∘ w) y stdComplexLineReal) := by
    have hwy : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I w y :=
      ((hw.mono inter_subset_left).mdifferentiableOn one_ne_zero).mdifferentiableAt (hU.mem_nhds hy)
    simpa only [hamiltonianVectorFieldInChartAt_zero, Pi.zero_apply, sub_zero,
      almostComplexInChartAt_almostComplexStructureAt] using
      ω.isComplexLinearMap_perturbedMFDeriv_iff_fderiv_extChartAt_comp_stdComplexLineImag_sub
      (Ks := fun _ _ ↦ 0) (Kt := fun _ _ ↦ 0) (J := fun _ ↦ J₀.almostComplexStructureAt) hwy hy.2
  -- Both sides are continuous on `U` and agree off `y₀`, hence at `y₀`.
  have hcont₁ : ContinuousAt (fun y ↦ fderiv ℝ (φ ∘ w) y stdComplexLineImag) y₀ :=
    ((hdv.clm_apply continuousOn_const).continuousAt (hU.mem_nhds hy₀U))
  have hcont₂ : ContinuousAt
      (fun y ↦ J₀.inChart α (φ (w y)) (fderiv ℝ (φ ∘ w) y stdComplexLineReal)) y₀ := by
    refine ContinuousOn.continuousAt ?_ (hU.mem_nhds hy₀U)
    refine ContinuousOn.clm_apply ?_ (hdv.clm_apply continuousOn_const)
    exact (J₀.contDiffOn_inChart (x := α)).continuousOn.comp hv.continuousOn
      fun y hy ↦ φ.map_source hy.2
  have hev : (fun y ↦ fderiv ℝ (φ ∘ w) y stdComplexLineImag) =ᶠ[𝓝[≠] y₀]
      fun y ↦ J₀.inChart α (φ (w y)) (fderiv ℝ (φ ∘ w) y stdComplexLineReal) := by
    filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hy₀U), self_mem_nhdsWithin] with y hy hne
    exact (hiff y hy).1 (h y hy.1 hne)
  exact (hiff y₀ hy₀U).2 (tendsto_nhds_unique (hcont₁.tendsto.mono_left nhdsWithin_le_nhds)
    ((hcont₂.tendsto.mono_left nhdsWithin_le_nhds).congr' hev.symm))

/-- **Holomorphy at the point at infinity, in a manifold.** Let `u` be differentiable and
`J₀`-holomorphic at every point `z` with `‖z‖ > T`, in complex coordinates, for a smooth almost
complex structure `J₀` on `M`, in the form of the Floer equation with zero perturbation. Let `w` be
`C¹` on an open set `Ω` of the disc `‖y‖ < T⁻¹`, with `w y = u (y⁻¹)` for `y ≠ 0`. Then `w` is
`J₀`-holomorphic on all of `Ω`, including at `0`, the point at infinity. -/
theorem isComplexLinearMap_perturbedMFDeriv_zero_of_eq_comp_inv
    (ω : SmoothTwoForm I M) (J₀ : SmoothAlmostComplexStructure I M) (hΩ : IsOpen Ω)
    (hΩT : Ω ⊆ equivRealProdCLM.symm ⁻¹' ball 0 T⁻¹)
    (hu : ∀ z ∈ equivRealProdCLM.symm ⁻¹' (closedBall 0 T)ᶜ, MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z)
    (hhol : ∀ z ∈ equivRealProdCLM.symm ⁻¹' (closedBall 0 T)ᶜ,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J₀.almostComplexStructureAt (u z))
        (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun _ _ ↦ 0) u z).toLinearMap)
    (hw : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 w Ω)
    (hwu : ∀ y ∈ Ω, y ≠ 0 → w y = u (realChart (fun ζ ↦ ζ⁻¹) y)) {y : ℝ × ℝ} (hy : y ∈ Ω) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J₀.almostComplexStructureAt (w y))
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun _ _ ↦ 0) w y).toLinearMap := by
  -- Off `0`, `w` agrees near `y` with `u ∘ ι` for the holomorphic inversion `ι`, and `ι y` lies
  -- outside the disc of radius `T`.
  have hoff (y : ℝ × ℝ) (hy : y ∈ Ω) (hy0 : y ≠ 0) : IsComplexLinearMap
      (AlmostComplexStructure.product ℝ) (J₀.almostComplexStructureAt (w y))
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun _ _ ↦ 0) w y).toLinearMap := by
    have hy0' : equivRealProdCLM.symm y ≠ 0 := by simpa using hy0
    have hfar : realChart (fun ζ ↦ ζ⁻¹) y ∈ equivRealProdCLM.symm ⁻¹' (closedBall 0 T)ᶜ := by
      rw [mem_preimage, equivRealProdCLM_symm_realChart]
      exact mapsTo_inv_ball_diff_singleton_compl_closedBall T ⟨hΩT hy, hy0'⟩
    have hev : w =ᶠ[𝓝 y] u ∘ realChart (fun ζ ↦ ζ⁻¹) := by
      filter_upwards [(hΩ.sdiff isClosed_singleton).mem_nhds ⟨hy, hy0⟩] with y' hy'
        using hwu y' hy'.1 hy'.2
    have hι := hasDerivAt_inv hy0'
    refine ω.isComplexLinearMap_perturbedMFDeriv_of_eventuallyEq _ _ hev ?_
    have h := ω.isComplexLinearMap_perturbedMFDeriv_perturbationPullback
      (hasFDerivAt_realChart hι).differentiableAt (hu _ hfar) mdifferentiableAt_const
      mdifferentiableAt_const (isComplexLinearMap_fderiv_realChart hι) (hhol _ hfar)
    rwa [perturbationPullback_zero, perturbationPullback_zero] at h
  by_cases hy0 : y = 0
  · subst hy0
    exact isComplexLinearMap_perturbedMFDeriv_zero_of_forall_ne ω J₀ hΩ hw hy
      fun y' hy' hne ↦ hoff y' hy' hne
  · exact hoff y hy hy0

omit [FiniteDimensional ℝ E] in
/-- **The area near infinity in the chart at infinity, in a manifold.** Let `ω` be a
nondegenerate two-form on `M` taming a smooth almost complex structure `J₀`. Let `u` be
differentiable and `J₀`-holomorphic at every point `z` with `‖z‖ > T`, in complex coordinates,
with integrable area density `ω(∂ₛu, ∂ₜu)` on that exterior. Let `w` agree with `y ↦ u(y⁻¹)` on an
open set `Ω` of the disc `‖y‖ < T⁻¹`, except possibly at `0`. Then the area density of `w` is
integrable on `Ω`, and its integral over `Ω` is at most the area of `u` outside the disc of radius
`T`. -/
theorem IsNondegenerate.integrableOn_and_setIntegral_le_of_eq_comp_inv (hω : ω.IsNondegenerate)
    (hJ₀ : ∀ x, (hω.symplecticFormAt x).Tames (J₀.almostComplexStructureAt x)) (hΩ : IsOpen Ω)
    (hΩT : Ω ⊆ equivRealProdCLM.symm ⁻¹' ball 0 T⁻¹)
    (hu : ∀ z ∈ equivRealProdCLM.symm ⁻¹' (closedBall 0 T)ᶜ, MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z)
    (hhol : ∀ z ∈ equivRealProdCLM.symm ⁻¹' (closedBall 0 T)ᶜ,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J₀.almostComplexStructureAt (u z))
        (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun _ _ ↦ 0) u z).toLinearMap)
    (hint : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ))
      (equivRealProdCLM.symm ⁻¹' (closedBall 0 T)ᶜ))
    (hwu : ∀ y ∈ Ω, y ≠ 0 → w y = u (realChart (fun ζ ↦ ζ⁻¹) y)) :
    IntegrableOn (fun y ↦ (SmoothBundleForm.eval₂ ω (w y)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I w y stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I w y stdComplexLineImag) : ℝ)) Ω ∧
      ∫ y in Ω, (SmoothBundleForm.eval₂ ω (w y) (mfderiv 𝓘(ℝ, ℝ × ℝ) I w y stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I w y stdComplexLineImag) : ℝ) ≤
        ∫ z in equivRealProdCLM.symm ⁻¹' (closedBall 0 T)ᶜ,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ) := by
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
      (hu _ (hmaps hy)) mdifferentiableAt_const mdifferentiableAt_const
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
      0 ≤ ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u z :=
    ae_restrict_of_forall_mem ((isClosed_closedBall.isOpen_compl).preimage
      equivRealProdCLM.symm.continuous).measurableSet fun z hz ↦
        floerEnergyDensity_nonneg hω (hJ₀ _) (hhol z hz)
  rw [← setIntegral_congr_set hnull, ← integral_image_eq_integral_of_eq_abs_det_smul
    hso.measurableSet hinj (fun y hy ↦ (hasFDerivAt_realChart (hder y hy)).differentiableAt) hdens]
  exact setIntegral_mono_set hint hnn (Eventually.of_forall hmaps.image_subset)

section Closed

variable [I.Boundaryless] [CompactSpace M] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Compactness at infinity in a closed manifold.** Let `ω` be a nondegenerate two-form on a
closed manifold `M` taming a smooth almost complex structure `J₀`, let `e : M → F` be injective and
differentiable, such as the Whitney embedding of `M`, with `J₀` uniformly tame with respect to `e`,
`c ‖d e v‖² ≤ ω(v, J₀ v)` with `c > 0`, and let `T` be real. There is a threshold `δ > 0` with the
following property. Let `uₖ` be differentiable and `J₀`-holomorphic at every point `z` with
`‖z‖ > T`, in complex coordinates, with integrable area density `ω(∂ₛuₖ, ∂ₜuₖ)` on that exterior
and area there at most `E`. Let `wₖ` be `C³` maps on an open set `Ω` of the disc `‖y‖ < T⁻¹` of the
chart at infinity, with `wₖ(y) = uₖ(y⁻¹)` for `y ≠ 0`. Then there are a subsequence `φ` and a finite
set `Z ⊆ Ω` with `#Z * δ ≤ E` such that, along `φ`, every disc about a point of `Z` eventually
carries area of `wₖ` at least `δ`, the area densities of the `wₖ` are uniformly bounded on every
compact subset of `Ω \ Z`, and the `wₖ` converge on `Ω \ Z` to a continuous map `v`, locally
uniformly after applying `e` and pointwise in `M`. The point `0` of `Ω`, the point at infinity, is
treated like any other, and no condition is put on where the maps take their values. -/
theorem IsNondegenerate.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_inv
    (hω : ω.IsNondegenerate) (J₀ : SmoothAlmostComplexStructure I M)
    (hJ₀ : ∀ x, (hω.symplecticFormAt x).Tames (J₀.almostComplexStructureAt x)) {e : M → F}
    (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤
      hω.symplecticFormAt x v (J₀.almostComplexStructureAt x v)) (T : ℝ) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃u w : ℕ → ℝ × ℝ → M⦄ ⦃E : ℝ⦄, IsOpen Ω →
      Ω ⊆ equivRealProdCLM.symm ⁻¹' ball 0 T⁻¹ →
      (∀ k, ∀ z ∈ equivRealProdCLM.symm ⁻¹' (closedBall 0 T)ᶜ,
        MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I (u k) z) →
      (∀ k, ∀ z ∈ equivRealProdCLM.symm ⁻¹' (closedBall 0 T)ᶜ,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ)
          (J₀.almostComplexStructureAt (u k z))
          (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun _ _ ↦ 0) (u k) z).toLinearMap) →
      (∀ k, IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u k z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ))
        (equivRealProdCLM.symm ⁻¹' (closedBall 0 T)ᶜ)) →
      (∀ k, ∫ z in equivRealProdCLM.symm ⁻¹' (closedBall 0 T)ᶜ,
        (SmoothBundleForm.eval₂ ω (u k z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ) ≤ E) →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (w k) Ω) →
      (∀ k, ∀ y ∈ Ω, y ≠ 0 → w k y = u k (realChart (fun ζ ↦ ζ⁻¹) y)) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Z : Finset (ℝ × ℝ), ↑Z ⊆ Ω ∧ Z.card * δ ≤ E ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω,
          (SmoothBundleForm.eval₂ ω (w (φ n) y)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I (w (φ n)) y stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I (w (φ n)) y stdComplexLineImag) : ℝ)) ∧
        (∀ C, IsCompact C → C ⊆ Ω \ ↑Z → ∃ A, ∀ n, ∀ y ∈ C,
          (SmoothBundleForm.eval₂ ω (w (φ n) y)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I (w (φ n)) y stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I (w (φ n)) y stdComplexLineImag) : ℝ) ≤ A) ∧
        ∃ v : ℝ × ℝ → M, ContinuousOn v (Ω \ ↑Z) ∧
          TendstoLocallyUniformlyOn (fun n ↦ e ∘ w (φ n)) (e ∘ v) atTop (Ω \ ↑Z) ∧
          ∀ z ∈ Ω \ ↑Z, Tendsto (fun n ↦ w (φ n) z) atTop (𝓝 (v z)) := by
  -- The compactness theorem for the unperturbed equation of `J₀` on the closed disc of radius
  -- `T⁻¹` of the chart at infinity.
  have hD : IsCompact (equivRealProdCLM.symm ⁻¹' closedBall (0 : ℂ) T⁻¹) :=
    equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2 (isCompact_closedBall _ _)
  have hX (α : M) : ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt α
      (fun (_ : ℝ × ℝ) (_ : M) ↦ (0 : ℝ))) (univ ×ˢ (extChartAt I α).target) := by
    rw [hamiltonianVectorFieldInChartAt_zero]
    exact contDiffOn_const
  have hB (x : M) : ‖mvfderiv I e x (ω.hamiltonianVectorField (fun _ ↦ (0 : ℝ)) x)‖ ≤ 0 := by
    rw [hamiltonianVectorField_const, Pi.zero_apply, map_zero]
    exact (norm_zero (E := F)).le
  have hJ (α : M) : ContDiffOn ℝ 2 (almostComplexInChartAt I α
      (fun (_ : ℝ × ℝ) ↦ J₀.almostComplexStructureAt)) (univ ×ˢ (extChartAt I α).target) := by
    refine (((J₀.contDiffOn_inChart α).of_le (by simp)).comp
      (contDiff_snd.contDiffOn (s := univ ×ˢ (extChartAt I α).target))
      fun p hp ↦ hp.2).congr fun p _ ↦ ?_
    simp
  obtain ⟨δ, hδ, hconv⟩ := hω.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset
    (Ks := fun _ _ ↦ 0) (Kt := fun _ _ ↦ 0) (J := fun _ ↦ J₀.almostComplexStructureAt) he he_inj
    isOpen_univ hD (subset_univ _)
    hJ hX hX (fun _ _ x ↦ hJ₀ x) hc (fun _ _ ↦ hJc) (fun _ _ ↦ hB) fun _ _ ↦ hB
  refine ⟨δ, hδ, fun Ω u w E hΩ hΩT hu hhol hint hE hw hwu ↦ ?_⟩
  have hwE (k : ℕ) := hω.integrableOn_and_setIntegral_le_of_eq_comp_inv hJ₀ hΩ hΩT (hu k)
    (hhol k) (hint k) (hwu k)
  simpa only [floerEnergyDensity_zero] using hconv hΩ
    (hΩT.trans (preimage_mono ball_subset_closedBall)) hw
    (fun k y hy ↦ isComplexLinearMap_perturbedMFDeriv_zero_of_eq_comp_inv ω J₀ hΩ hΩT (hu k)
      (hhol k) ((hw k).of_le (by norm_num)) (hwu k) hy)
    (fun k ↦ by simpa only [← floerEnergyDensity_zero] using (hwE k).1)
    (fun k ↦ by simpa only [← floerEnergyDensity_zero] using (hwE k).2.trans (hE k))

end Closed

end TauCeti.SmoothTwoForm
