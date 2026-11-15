/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Plumbing.Energy
import TauCeti.MeasureTheory.Integral.DominatedConvergence

/-!
# The energy identity on the whole plumbed four-punctured sphere

Plumb the output end at `∞` of a pair of pants `S'`, with bounded period-one `C¹` Hamiltonians
`Ha`, into the input end `q ∈ {0, 1}` of a pair of pants `S`, with bounded period-one `C¹`
Hamiltonians `Hb`, along a neck of length `L > 4`, where `Hb q = Ha ∞`. This gives the
four-punctured sphere `Σ = ℂ ∖ {0, 1, ψ(1)}`, where `ψ` is the plumbing map
`TauCeti.ThricePuncturedSphere.Puncture.plumbingMap q L`, with the plumbed perturbation `K`
(`TauCeti.Floer.plumbedPerturbation`). Its four ends are the two input ends of `S'`, carried into
`Σ` by `ψ`, and the remaining input end and the output end of `S`.

Let `u` be a map into a finite-dimensional manifold `M` with a nondegenerate two-form `ω`, such as
a closed symplectic manifold, which is `C¹` on `Σ`. Suppose that its loops along the four outer
circles at height `R` converge pointwise to loops as `R → ∞`: `ℓ'_r(t) = u(ψ(φ_r(R + i t)))`
to `xa_r` on the inputs `r ≠ ∞` of `S'`, and `ℓ_r(t) = u(φ_r(±R + i t))` to `xb_r` on the ends
`r ≠ q` of `S`. Suppose also that the energy density and the area density of `u` are integrable
over `Σ`. Then the energy identity on the truncations `Σ_R`
(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_plumbedTruncation`) passes to the
limit `R → ∞`:

`∫_Σ E = ∫_Σ u^*ω + ∑_{r ≠ ∞} ∫₀¹ Ha_r(t, xa_r(t)) dt + ∑_{r ≠ q} ±∫₀¹ Hb_r(t, xb_r(t)) dt
  - ∫_Σ R_K(u)`

(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_plumbedPerturbation`), with the sign
`+` on input ends and `-` on the output end. So the energy differs from this topological part by
at most `∑ r, Ba r + ∑ r, Bb r` for bounds `|Ha r| ≤ Ba r` and `|Hb r| ≤ Bb r`, uniformly in the
neck length, and for a solution of the Floer equation with tamed almost complex structures the
topological part is at least `-(∑ r, Ba r + ∑ r, Bb r)`.

The three integrals over `Σ` are the limits of the integrals over the truncations `Σ_R`, which
increase and exhaust `Σ` (`TauCeti.ThricePuncturedSphere.Puncture.iUnion_plumbedTruncation`); the
curvature is integrable over `Σ` because it is integrable over each `Σ_R`
(`TauCeti.SmoothTwoForm.integrableOn_hamiltonianCurvature_plumbedTruncation`) and its absolute
integral over the plane is bounded
(`TauCeti.SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_plumbedPerturbation_le`). The
Hamiltonian terms converge by dominated convergence, since the Hamiltonians are bounded.

The area term depends on the homotopy class of `u` when the target is not symplectically
aspherical. Rewriting it through caps of the four asymptotic orbits is not done here.

## Main results

* `TauCeti.Floer.tendsto_setIntegral_plumbedTruncation`: integrals over `Σ` are the limits of the
  integrals over the truncations `Σ_R`.
* `SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_plumbedPerturbation`: the energy
  identity on the whole plumbed four-punctured sphere.
* `SmoothTwoForm.IsNondegenerate.abs_integral_floerEnergyDensity_plumbedPerturbation_sub_le`: the
  resulting energy bound, uniform in the neck length.
* `SmoothTwoForm`'s
  `IsNondegenerate.neg_sum_add_sum_le_integral_add_sum_add_sum_of_plumbedPerturbation`: the lower
  bound on the topological energy of a Floer solution.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the energy estimates for compositions of pair-of-pants products.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  curvature of Hamiltonian perturbations and the resulting energy bounds.
-/

public section

open Set Real Function MeasureTheory Filter TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Topology Manifold

namespace TauCeti

namespace Floer

variable {q : Puncture} {L : ℝ}

/-- Integrals over the plumbed four-punctured sphere `ℂ ∖ {0, 1, ψ(1)}`, in the real coordinates,
are the limits of the integrals over its truncations `Σ_R`. -/
theorem tendsto_setIntegral_plumbedTruncation (hq : q ≠ inf) (hL : 0 < L) {f : ℝ × ℝ → ℝ}
    (hf : IntegrableOn f {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    Tendsto (fun R : ℝ ↦ ∫ z in Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R, f z)
      atTop (𝓝 (∫ z in {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}, f z)) := by
  have hS : ⋃ R : ℝ, Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R =
      {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1} := by
    rw [← preimage_iUnion, iUnion_plumbedTruncation hq hL]
    rfl
  rw [← hS] at hf ⊢
  exact tendsto_setIntegral_of_monotone (measurableSet_preimage_plumbedTruncation q L)
    (fun _ _ h ↦ preimage_mono (plumbedTruncation_mono q L h)) hf

end Floer

namespace SmoothTwoForm

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M]
  {ω : SmoothTwoForm I M} {Ha Hb : Puncture → ℝ → M → ℝ} {q : Puncture} {L : ℝ}

/-- Along a map continuous on the plumbed four-punctured sphere, the curvature of the plumbed
perturbation of bounded Hamiltonians is integrable over the whole plumbed sphere: it is integrable
over each truncation `Σ_n`, which exhaust the sphere, and its absolute integral over the plane is
finite. -/
private theorem integrableOn_hamiltonianCurvature_plumbedPerturbation (ω : SmoothTwoForm I M)
    (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {Ba Bb : Puncture → ℝ}
    (hBa : ∀ r t x, |Ha r t x| ≤ Ba r) (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) {u : ℝ × ℝ → M}
    (hu : ContinuousOn u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)) {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
          Complex.equivRealProdCLM.symm z ≠ 1) ∧
          Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1} := by
  -- The truncations at the natural heights `n ≥ L/2` already exhaust the plumbed sphere.
  have hS : ⋃ n : ℕ, Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L (n + L / 2) =
      {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1} := by
    refine subset_antisymm (iUnion_subset fun n ↦ preimage_mono
      (plumbedTruncation_subset hq (by linarith) _)) fun z hz ↦ ?_
    obtain ⟨R, hR⟩ := mem_iUnion.1
      ((iUnion_plumbedTruncation hq (by linarith : (0 : ℝ) < L)).symm ▸ hz :
        Complex.equivRealProdCLM.symm z ∈ ⋃ R, q.plumbedTruncation L R)
    obtain ⟨n, hn⟩ := exists_nat_ge R
    exact mem_iUnion.2 ⟨n, plumbedTruncation_mono q L (by linarith) hR⟩
  refine ⟨?_, ?_⟩
  · rw [← hS, aestronglyMeasurable_iUnion_iff]
    exact fun n ↦ (ω.integrableOn_hamiltonianCurvature_plumbedTruncation hq hHa hHb hHas hHbs hab
      hL (by linarith [n.cast_nonneg (α := ℝ)]) hu).aestronglyMeasurable
  · exact ((setLIntegral_le_lintegral _ _).trans
      (ω.lintegral_enorm_hamiltonianCurvature_plumbedPerturbation_le hq hHa hHb hHas hHbs hab hL
        hBa hBb u)).trans_lt (by simp [ENNReal.add_lt_top, ENNReal.sum_lt_top])

variable [FiniteDimensional ℝ E]

/-- **The energy identity on the plumbed four-punctured sphere, for a manifold target.** Plumb the
output end of a pair of pants with bounded period-one `C¹` Hamiltonians `Ha` into the input end
`q ≠ ∞` of one with bounded period-one `C¹` Hamiltonians `Hb`, with `Hb q = Ha ∞`, along a neck of
length `L > 4`, for Hamiltonians on a finite-dimensional manifold with a nondegenerate two-form,
such as a closed symplectic manifold. Let `u` be `C¹` on the four-punctured sphere
`Σ = ℂ ∖ {0, 1, ψ(1)}`, in real coordinates, with integrable Floer energy density and symplectic
area density over `Σ`. Suppose that its loops `t ↦ u(ψ(φ_r(R + i t)))` along the input ends
`r ≠ ∞` of the inserted pair of pants converge pointwise to loops `xa r` as `R → ∞`, and that its
loops `t ↦ u(φ_r(±R + i t))` along the ends `r ≠ q` of the receiving one converge pointwise to
loops `xb r`. Then

`∫_Σ E = ∫_Σ u^*ω + ∑_{r ≠ ∞} ∫₀¹ Ha_r(t, xa_r(t)) dt + ∑_{r ≠ q} ±∫₀¹ Hb_r(t, xb_r(t)) dt
  - ∫_Σ R_K(u)`,

with the sign `+` on the input ends and `-` on the output end `∞` of the receiving pair of pants.
The curvature is integrable over `Σ`. -/
theorem IsNondegenerate.integral_floerEnergyDensity_plumbedPerturbation
    (hω : ω.IsNondegenerate) (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1)
    (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {Ba Bb : Puncture → ℝ}
    (hBa : ∀ r t x, |Ha r t x| ≤ Ba r) (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1})
    {xa xb : Puncture → ℝ → M}
    (hxa : ∀ r ∈ Finset.univ.erase inf, ∀ t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (q.plumbingMap L (r.cylindricalEndLift (↑R + ↑t * Complex.I))))) atTop (𝓝 (xa r t)))
    (hxb : ∀ r ∈ Finset.univ.erase q, ∀ t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (r.cylindricalEndLift (↑(r.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (xb r t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1})
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ))
      {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    ∫ z in {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}, ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      (∫ z in {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
          Complex.equivRealProdCLM.symm z ≠ 1) ∧
          Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1},
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        ((∑ r ∈ Finset.univ.erase inf, ∫ t in (0 : ℝ)..1, Ha r t (xa r t)) +
          ∑ r ∈ Finset.univ.erase q, r.endSign * ∫ t in (0 : ℝ)..1, Hb r t (xb r t)) -
        ∫ z in {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
          Complex.equivRealProdCLM.symm z ≠ 1) ∧
          Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}, ω.hamiltonianCurvature
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  have hL₀ : 0 < L := by linarith
  have hR := integrableOn_hamiltonianCurvature_plumbedPerturbation ω hq hHa hHb hHas hHbs hab hL
    hBa hBb hu.continuousOn
  have hψ : Continuous (q.plumbingMap L) := (q.contDiff_plumbingMap L (n := 0)).continuous
  -- For `R > 0` the outer circles at height `R` lie in `Σ_R`, where `u` is continuous.
  have hloop {γ : ℝ → ℂ} (hγ : Continuous γ) {R : ℝ}
      (hmem : ∀ t, γ t ∈ q.plumbedTruncation L R) :
      ContinuousOn (fun t ↦ u (Complex.equivRealProdCLM (γ t))) (uIcc 0 1) :=
    (hu.continuousOn.comp_continuous (Complex.equivRealProdCLM.continuous.comp hγ) fun t ↦ by
      rw [comp_apply, mem_ofPred_eq, ContinuousLinearEquiv.symm_apply_apply]
      exact plumbedTruncation_subset hq hL₀ R (hmem t)).continuousOn
  -- The Hamiltonian terms of the four outer circles converge by dominated convergence.
  have hHam {H : ℝ → M → ℝ} (hHc : Continuous (uncurry H)) {B : ℝ} (hB : ∀ t x, |H t x| ≤ B)
      {γ : ℝ → ℝ → ℂ} (hγ : ∀ R, Continuous (γ R))
      (hmem : ∀ᶠ R in atTop, ∀ t, γ R t ∈ q.plumbedTruncation L R) {x : ℝ → M}
      (hx : ∀ t, Tendsto (fun R ↦ u (Complex.equivRealProdCLM (γ R t))) atTop (𝓝 (x t))) :
      Tendsto (fun R ↦ ∫ t in (0 : ℝ)..1, H t (u (Complex.equivRealProdCLM (γ R t)))) atTop
        (𝓝 (∫ t in (0 : ℝ)..1, H t (x t))) :=
    tendsto_intervalIntegral_comp_of_tendsto_of_norm_le (Φ := uncurry H) hHc
      (fun p ↦ (Real.norm_eq_abs _).trans_le (hB p.1 p.2))
      (hmem.mono fun R hR ↦ hloop (hγ R) hR) fun t _ ↦ hx t
  have hSa := tendsto_finsetSum (Finset.univ.erase inf) fun r hr ↦ hHam ((hHas r).continuous)
    (hBa r) (γ := fun R t ↦ q.plumbingMap L (r.cylindricalEndLift (↑R + ↑t * Complex.I)))
    (fun R ↦ hψ.comp ((r.contDiff_cylindricalEndLift 0).continuous.comp (by fun_prop)))
    ((eventually_gt_atTop 0).mono fun R hR ↦
      plumbingMap_cylindricalEndLift_mem_plumbedTruncation q (Finset.ne_of_mem_erase hr) hL₀.le hR)
    (hxa r hr)
  have hSb := tendsto_finsetSum (Finset.univ.erase q) fun r hr ↦ (hHam ((hHbs r).continuous)
    (hBb r) (γ := fun R t ↦ r.cylindricalEndLift (↑(r.endSign * R) + ↑t * Complex.I))
    (fun R ↦ (r.contDiff_cylindricalEndLift 0).continuous.comp (by fun_prop))
    ((eventually_gt_atTop 0).mono fun R hR ↦
      cylindricalEndLift_mem_plumbedTruncation hq (Finset.ne_of_mem_erase hr) hL₀.le hR)
    (hxb r hr)).const_mul r.endSign
  -- Pass to the limit in the energy identity on the truncations `Σ_R`, `R ≥ L/2`.
  refine tendsto_nhds_unique ((tendsto_setIntegral_plumbedTruncation hq hL₀ hE).congr' ?_)
    (((tendsto_setIntegral_plumbedTruncation hq hL₀ hA).add (hSa.add hSb)).sub
      (tendsto_setIntegral_plumbedTruncation hq hL₀ hR))
  filter_upwards [eventually_ge_atTop (L / 2)] with R hR
  exact hω.integral_floerEnergyDensity_plumbedTruncation hq hHa hHb hHas hHbs hab hL hR hu

/-- **The energy bound on the plumbed four-punctured sphere, for a manifold target.** Under the
hypotheses of `SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_plumbedPerturbation`, the
Floer energy over `Σ` differs from its topological part, the symplectic area plus the Hamiltonian
terms at the four asymptotic loops, by at most `∑ r, Ba r + ∑ r, Bb r`, whatever the neck length
`L > 4`. -/
theorem IsNondegenerate.abs_integral_floerEnergyDensity_plumbedPerturbation_sub_le
    (hω : ω.IsNondegenerate) (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1)
    (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {Ba Bb : Puncture → ℝ}
    (hBa : ∀ r t x, |Ha r t x| ≤ Ba r) (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1})
    {xa xb : Puncture → ℝ → M}
    (hxa : ∀ r ∈ Finset.univ.erase inf, ∀ t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (q.plumbingMap L (r.cylindricalEndLift (↑R + ↑t * Complex.I))))) atTop (𝓝 (xa r t)))
    (hxb : ∀ r ∈ Finset.univ.erase q, ∀ t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (r.cylindricalEndLift (↑(r.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (xb r t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1})
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ))
      {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    |(∫ z in {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}, ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) -
      (∫ z in {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
          Complex.equivRealProdCLM.symm z ≠ 1) ∧
          Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1},
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) -
        ((∑ r ∈ Finset.univ.erase inf, ∫ t in (0 : ℝ)..1, Ha r t (xa r t)) +
          ∑ r ∈ Finset.univ.erase q, r.endSign * ∫ t in (0 : ℝ)..1, Hb r t (xb r t))| ≤
      ∑ r, Ba r + ∑ r, Bb r := by
  have hsub (a b c : ℝ) : a + b - c - a - b = -c := by ring
  rw [hω.integral_floerEnergyDensity_plumbedPerturbation hq hHa hHb hHas hHbs hab hL hBa hBb hu
    hxa hxb hE hA, hsub, abs_neg]
  exact ω.abs_setIntegral_hamiltonianCurvature_plumbedPerturbation_le hq hHa hHb hHas hHbs hab hL
    hBa hBb u _

/-- **The topological energy of a solution on the plumbed four-punctured sphere is bounded below,
for a manifold target.** Let `u` solve the Floer equation `(du - X_K)^{0,1} = 0` on `Σ` for almost
complex structures `J z` on the tangent spaces `T_{u(z)} M` tamed by the two-form, under the
hypotheses of `SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_plumbedPerturbation`.
Since its energy is nonnegative, its symplectic area over `Σ` plus the Hamiltonian terms at the
four asymptotic loops is at least `-(∑ r, Ba r + ∑ r, Bb r)`, whatever the neck length `L > 4`. -/
theorem IsNondegenerate.neg_sum_add_sum_le_integral_add_sum_add_sum_of_plumbedPerturbation
    (hω : ω.IsNondegenerate) (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1)
    (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {Ba Bb : Puncture → ℝ}
    (hBa : ∀ r t x, |Ha r t x| ≤ Ba r) (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1})
    {xa xb : Puncture → ℝ → M}
    (hxa : ∀ r ∈ Finset.univ.erase inf, ∀ t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (q.plumbingMap L (r.cylindricalEndLift (↑R + ↑t * Complex.I))))) atTop (𝓝 (xa r t)))
    (hxb : ∀ r ∈ Finset.univ.erase q, ∀ t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (r.cylindricalEndLift (↑(r.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (xb r t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1})
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ))
      {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1})
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z ∈ {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1},
      (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1},
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap) :
    -(∑ r, Ba r + ∑ r, Bb r) ≤
      (∫ z in {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
          Complex.equivRealProdCLM.symm z ≠ 1) ∧
          Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1},
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        ((∑ r ∈ Finset.univ.erase inf, ∫ t in (0 : ℝ)..1, Ha r t (xa r t)) +
          ∑ r ∈ Finset.univ.erase q, r.endSign * ∫ t in (0 : ℝ)..1, Hb r t (xb r t)) := by
  have hpos := setIntegral_nonneg (μ := volume) (isOpen_plumbedSphere q L).measurableSet
    fun z hz ↦ floerEnergyDensity_nonneg hω (hJ z hz) (hfloer z hz)
  have h := (abs_le.1 (hω.abs_integral_floerEnergyDensity_plumbedPerturbation_sub_le hq hHa hHb
    hHas hHbs hab hL hBa hBb hu hxa hxb hE hA)).2
  linarith

end SmoothTwoForm

end TauCeti
