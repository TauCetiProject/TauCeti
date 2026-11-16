/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.PiTopology
public import TauCeti.NumberTheory.Padics.Measure.CompletedGroupAlgebra
public import TauCeti.NumberTheory.Padics.Measure.PhiPsi
public import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.PowerSeries
import TauCeti.NumberTheory.Padics.Measure.Norm
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# The weak topology in Amice coordinates

The integral Amice equivalence identifies weak convergence of measures on `ℤ_p` with
coefficientwise p-adic convergence of power series. The topology on measures is selected
explicitly as `AbstractMeasure.WeakTopology`; the series topology is
`PowerSeries.WithPiTopology`, not a supremum norm on coefficients.

For the inverse, the density of the Mahler span and the uniform bound `‖μ f‖ ≤ ‖f‖`
pass continuity from finite Mahler combinations to every continuous test. Consequently
psi and the projector onto `pℤ_p`, transported to power series, are continuous in these
coordinates. This permits identities on polynomials to pass to integral power series.

For the multiplicative group `Multiplicative ℤ_p`, the multiplicative Amice transform
`AbstractMeasure.amiceTransformₐ` is likewise weakly continuous
(`AbstractMeasure.continuous_amiceTransformₐ_weak`), and composing it with
`TauCeti.completedGroupAlgebra.powerSeriesCoordinate` at `ofAdd 1` recovers
`AbstractMeasure.toCompletedGroupAlgebra` (`TauCeti.powerSeriesCoordinate_amiceTransformₐ`).

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §II.2.
* Rodrigues Jacinto and Williams, *An introduction to p-adic L-functions*,
  Definitions 3.5 and 3.8, Theorem 3.25 and §3.5.3–5.

The construction uses Mathlib's `AbstractMeasure.amiceTransformEquiv` and
`PadicInt.dense_span_mahler`.
-/

public section

open Topology ContinuousMap PowerSeries
open scoped PowerSeries.WithPiTopology

namespace AbstractMeasure

variable {p : ℕ} [Fact p.Prime]

/-- The integral Amice transform is continuous from the weak measure topology to the
coefficientwise p-adic topology. -/
theorem continuous_amiceTransformEquiv_weak :
    @Continuous _ _ (WeakTopology (X := ℤ_[p]) (R := ℤ_[p]) (E := ℤ_[p])) _
      (amiceTransformEquiv (p := p)) := by
  let : TopologicalSpace D(ℤ_[p], ℤ_[p]) := WeakTopology
  have heval : Continuous (fun μ : D(ℤ_[p], ℤ_[p]) ↦ fun f : C(ℤ_[p], ℤ_[p]) ↦ μ f) :=
    continuous_induced_dom
  apply continuous_iff_continuousAt.mpr
  intro μ
  rw [ContinuousAt, PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  simpa only [coeff_amiceTransformEquiv, ContinuousAt, Function.comp_def] using
    ((continuous_apply (mahler n : C(ℤ_[p], ℤ_[p]))).comp heval).continuousAt (x := μ)

/-- The multiplicative Amice transform is weakly continuous to `PowerSeries.WithPiTopology`. -/
theorem continuous_amiceTransformₐ_weak {R : Type*} [NormedCommRing R] [Algebra ℤ_[p] R]
    [ContinuousSMul ℤ_[p] R] :
    @Continuous _ _ (WeakTopology (X := Multiplicative ℤ_[p]) (R := R) (E := R)) _
      (amiceTransformₐ (p := p) (R := R)) := by
  let : TopologicalSpace D(Multiplicative ℤ_[p], R) := WeakTopology
  refine continuous_iff_continuousAt.mpr fun μ ↦
    (PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto R _ _ _).mpr fun n ↦ ?_
  simpa only [coeff_amiceTransformₐ, ContinuousAt, Function.comp_def] using
    ((continuous_apply (mulMahler n : C(Multiplicative ℤ_[p], R))).comp
      (continuous_induced_dom : Continuous fun ν : D(Multiplicative ℤ_[p], R) ↦ ⇑ν)).continuousAt

/-- Evaluation of the inverse integral Amice transform at a fixed test function is
continuous for the coefficientwise p-adic topology. -/
theorem continuous_amiceTransformEquiv_symm_apply (f : C(ℤ_[p], ℤ_[p])) :
    Continuous fun F : ℤ_[p]⟦X⟧ ↦ amiceTransformEquiv.symm F f := by
  have hspan : ∀ g ∈ Submodule.span ℤ_[p]
      (Set.range fun n ↦ (mahler n : C(ℤ_[p], ℤ_[p])) • (1 : C(ℤ_[p], ℤ_[p]))),
      Continuous fun F : ℤ_[p]⟦X⟧ ↦ amiceTransformEquiv.symm F g := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨n, rfl⟩ := hg
      have h (F : ℤ_[p]⟦X⟧) :
          amiceTransformEquiv.symm F ((mahler n : C(ℤ_[p], ℤ_[p])) • 1) = F.coeff n := by
        rw [← coeff_amiceTransform, ← amiceTransformEquiv_apply,
          LinearEquiv.apply_symm_apply]
      simp_rw [h]
      exact PowerSeries.WithPiTopology.continuous_coeff _ n
    | zero =>
      simpa only [map_zero] using
        (continuous_const : Continuous fun _ : ℤ_[p]⟦X⟧ ↦ (0 : ℤ_[p]))
    | add g h _ _ hg hh =>
      exact (hg.add hh).congr fun F ↦ (map_add (amiceTransformEquiv.symm F) g h).symm
    | smul a g _ hg =>
      exact (hg.const_smul a).congr fun F ↦ (map_smul (amiceTransformEquiv.symm F) a g).symm
  refine continuous_of_uniform_approx_of_continuous fun u hu ↦ ?_
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.mp hu
  obtain ⟨g, hg, hfg⟩ := PadicInt.dense_span_mahler.exists_dist_lt f hε
  refine ⟨_, hspan g hg, fun F ↦ hεu ?_⟩
  rw [dist_eq_norm, ← map_sub]
  exact (norm_apply_le _ _).trans_lt (by rwa [← dist_eq_norm])

/-- The integral Amice equivalence is a homeomorphism from the weak measure topology
to the coefficientwise p-adic topology. -/
theorem isHomeomorph_amiceTransformEquiv_weak :
    @IsHomeomorph _ _ (WeakTopology (X := ℤ_[p]) (R := ℤ_[p]) (E := ℤ_[p])) _
      (amiceTransformEquiv (p := p)) := by
  let : TopologicalSpace D(ℤ_[p], ℤ_[p]) := WeakTopology
  rw [LinearEquiv.isHomeomorph_iff]
  exact ⟨continuous_amiceTransformEquiv_weak,
    continuous_induced_rng.mpr (continuous_pi continuous_amiceTransformEquiv_symm_apply)⟩

end AbstractMeasure

namespace TauCeti

open AbstractMeasure PowerSeries

variable {p : ℕ} [Fact p.Prime]

/-- Integral series psi is continuous for the coefficientwise p-adic topology. -/
theorem continuous_psiSeries : Continuous (psiSeries p) := by
  let : TopologicalSpace D(ℤ_[p], ℤ_[p]) := WeakTopology
  have h := isHomeomorph_amiceTransformEquiv_weak (p := p)
  rw [LinearEquiv.isHomeomorph_iff] at h
  exact (h.1.comp (continuous_psiMeasure_weak.comp h.2)).congr
    fun F ↦ by simp only [Function.comp_apply, amiceTransformEquiv_apply, psiSeries_apply]

/-- Frobenius after psi, the projector onto the multiples of `p`, is continuous for
the coefficientwise p-adic topology. -/
theorem continuous_subst_psiSeries :
    Continuous fun F : ℤ_[p]⟦X⟧ ↦ (psiSeries p F).subst ((1 + X : ℤ_[p]⟦X⟧) ^ p - 1) := by
  let : TopologicalSpace D(ℤ_[p], ℤ_[p]) := WeakTopology
  have h := isHomeomorph_amiceTransformEquiv_weak (p := p)
  rw [LinearEquiv.isHomeomorph_iff] at h
  have hφ := (ContinuousMap.mulLeft (p : ℤ_[p])).continuous_abstractMeasure_map_weak
    (R := ℤ_[p]) (E := ℤ_[p])
  have hcont := h.1.comp (hφ.comp (continuous_psiMeasure_weak.comp h.2))
  exact hcont.congr fun F ↦ by
    simp only [Function.comp_apply, ← phiMeasure_eq_map, amiceTransformEquiv_apply,
      amiceTransform_phiMeasure, psiSeries_apply]

/-- **Compatibility of the Amice transform with `powerSeriesCoordinate`.** On
`D(Multiplicative ℤ_p, ℤ_p)`, `powerSeriesCoordinate` at `ofAdd 1` composed with `amiceTransformₐ`
equals `toCompletedGroupAlgebra`. -/
theorem powerSeriesCoordinate_amiceTransformₐ (μ : D(Multiplicative ℤ_[p], ℤ_[p])) :
    completedGroupAlgebra.powerSeriesCoordinate (isProP_multiplicative_padicInt p)
        (topologicallyGenerates_ofAdd_one_padicInt p) (amiceTransformₐ μ) =
      toCompletedGroupAlgebra μ := by
  let : TopologicalSpace D(Multiplicative ℤ_[p], ℤ_[p]) := WeakTopology
  let coord := completedGroupAlgebra.powerSeriesCoordinate (isProP_multiplicative_padicInt p)
    (topologicallyGenerates_ofAdd_one_padicInt p)
  let e := coord.trans (completedGroupAlgebraEquiv (Γ := Multiplicative ℤ_[p]) (p := p)).symm
  let Ψ : PowerSeries ℤ_[p] →ₐ[ℤ_[p]] PowerSeries ℤ_[p] := amiceTransformₐ.comp e.toAlgHom
  have hΨ_cont : Continuous Ψ := continuous_amiceTransformₐ_weak.comp <|
    (continuous_completedGroupAlgebraEquiv_symm_weak (Γ := Multiplicative ℤ_[p])).comp <|
      completedGroupAlgebra.continuous_powerSeriesCoordinate _ _
  have hb1 : PowerSeries.binomialSeries ℤ_[p] (1 : ℤ_[p]) = 1 + PowerSeries.X := by
    simpa using PowerSeries.binomialSeries_nat (A := ℤ_[p]) (R := ℤ_[p]) 1
  have hΨX : Ψ PowerSeries.X = PowerSeries.X := add_left_cancel (a := (1 : PowerSeries ℤ_[p])) <| by
    conv_lhs => rw [← map_one Ψ, ← map_add, ← hb1]
    dsimp only [Ψ, e, coord, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.trans_apply]
    rw [completedGroupAlgebra.powerSeriesCoordinate_binomialSeries,
      IsProP.padicPow_ofAdd_one_padicInt, completedGroupAlgebraEquiv_symm_of, amiceTransformₐ_dirac,
      toAdd_ofAdd, hb1]
  have heq := congrFun ((PowerSeries.WithPiTopology.denseRange_toPowerSeries ℤ_[p]).equalizer
    hΨ_cont continuous_id <| funext fun P ↦ by
      simp only [Function.comp_apply, id_eq, PowerSeries.algHom_coe_eq_aeval, hΨX]
      exact (PowerSeries.algHom_coe_eq_aeval (AlgHom.id ℤ_[p] _) P).symm) (e.symm μ)
  rw [show amiceTransformₐ μ = e.symm μ by simpa [Ψ] using heq]
  simpa only [e, AlgEquiv.symm_trans_apply, AlgEquiv.symm_symm, completedGroupAlgebraEquiv_apply]
    using coord.apply_symm_apply (toCompletedGroupAlgebra μ)

/-- Inverse `powerSeriesCoordinate` at `ofAdd 1` on `toCompletedGroupAlgebra μ` is
`amiceTransformₐ μ`. -/
@[simp] theorem powerSeriesCoordinate_symm_toCompletedGroupAlgebra
    (μ : D(Multiplicative ℤ_[p], ℤ_[p])) :
    (completedGroupAlgebra.powerSeriesCoordinate (isProP_multiplicative_padicInt p)
      (topologicallyGenerates_ofAdd_one_padicInt p)).symm (toCompletedGroupAlgebra μ) =
        amiceTransformₐ μ :=
  (completedGroupAlgebra.powerSeriesCoordinate _ _).symm_apply_eq.mpr
    (powerSeriesCoordinate_amiceTransformₐ μ).symm

end TauCeti
