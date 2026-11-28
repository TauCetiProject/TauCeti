/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Identity

/-!
# Integrability and finiteness of Floer energy on a compact target

Let `ω` be a nondegenerate two-form on a finite-dimensional manifold `M`, let `K` be a `C¹`
Hamiltonian perturbation datum on `S = ℂ ∖ {0, 1}` equal to `H_q(t) dt` beyond some height `T₀`
on each end `q` for period-one continuous Hamiltonians `H_q`, and let `u : ℝ × ℝ → M` be a `C¹`
map on `S` with image in a compact set `B ⊆ M`, nonnegative Floer energy density, and integrable
symplectic area density and curvature over `S`.

Because `[0, 1] × B` is compact, each `|H_q(t, u(φ_q(±σ, t)))|` is uniformly bounded on the
ends without any global bound on `H_q` or pointwise end limits. By the measurability lemma
`SmoothTwoForm.IsNondegenerate.aestronglyMeasurable_floerEnergyDensity` and the upper bound
`SmoothTwoForm.IsNondegenerate.lintegral_floerEnergyDensity_le_of_eq_smul_endAngularForm`
of `TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Identity`, the Floer energy density of
`u` is integrable over `S`
(`IsNondegenerate.integrableOn_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact`).
-/

public section

open Set Filter Topology MeasureTheory Function TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Manifold

namespace TauCeti.SmoothTwoForm

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I (⊤ : ℕ∞) M]
  [FiniteDimensional ℝ E] {ω : SmoothTwoForm I M} {H : Puncture → ℝ → M → ℝ}

/-- **Automatic integrability of a nonnegative Floer energy density on a compact set.** For `K`
equal to `H_q(t) dt` beyond `T₀` on each end `q`, if `u` maps `S` into a compact set `B` with
nonnegative Floer energy density and integrable symplectic area density and curvature over `S`,
then compactness of `[0, 1] × B` uniformly bounds `∫₀¹ H_q(t, u(φ_q(±σ, t))) dt` for `σ > 0`,
making the Floer energy density integrable over `S` without global bounds on `H_q` or end
convergence. -/
theorem IsNondegenerate.integrableOn_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact
    {K : ℂ → M → ℂ →L[ℝ] ℝ} {T₀ : ℝ} {B : Set M} {u : ℝ × ℝ → M}
    (hω : ω.IsNondegenerate)
    (hK : ∀ (w : ThricePuncturedSphere) x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x))
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHc : ∀ q, Continuous (uncurry (H q))) (hB : IsCompact B)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (he : ∀ z ∈ thricePuncturedSphereReal, 0 ≤ ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))
      thricePuncturedSphereReal) :
    IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      thricePuncturedSphereReal := by
  rw [IntegrableOn, volume_restrict_thricePuncturedSphereReal] at hA hR ⊢
  have hbound : ∀ q, ∃ C : ℝ, ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ B, ‖uncurry (H q) p‖ ≤ C := fun q ↦
    (isCompact_Icc.prod hB).exists_bound_of_continuousOn (hHc q).continuousOn
  choose C hC using hbound
  refine ⟨hω.aestronglyMeasurable_floerEnergyDensity hK hu, ?_⟩
  rw [HasFiniteIntegral, lintegral_congr_ae (ae_mem_thricePuncturedSphereReal.mono fun z hz ↦
    Real.eNorm_eq_ofReal (he z hz))]
  refine lt_of_le_of_lt
    (hω.lintegral_floerEnergyDensity_le_of_eq_smul_endAngularForm hK hKH hH hu he hA hR
      (C := C) fun q s hs ↦ ?_) ENNReal.ofReal_lt_top
  have hmem (t : ℝ) : endChart q (s, t) ∈ thricePuncturedSphereReal :=
    endChart_mem_thricePuncturedSphereReal (lt_of_lt_of_le two_pos ((le_max_left 2 T₀).trans hs)).le
  simpa only [Real.norm_eq_abs, uncurry_apply_pair, sub_zero, abs_one, mul_one] using
    intervalIntegral.norm_integral_le_of_norm_le_const fun t ht ↦
      hC q (t, u (endChart q (s, t)))
        ⟨Ioc_subset_Icc_self (uIoc_of_le (zero_le_one : (0 : ℝ) ≤ 1) ▸ ht), huB _ (hmem t)⟩

end TauCeti.SmoothTwoForm
