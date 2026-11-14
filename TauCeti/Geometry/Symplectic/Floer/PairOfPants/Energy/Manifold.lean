/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Manifold
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Asymptotic

/-!
# The energy identity and topological energy bound for a Floer pair of pants in a manifold

Let `ω` be a nondegenerate two-form on a finite-dimensional manifold `M`, such as a symplectic
manifold, let `K` be a Hamiltonian perturbation on the pair of pants `S = ℂ ∖ {0, 1}`, equal to
`H_q(t) dt` beyond some height `T₀` on each end `q` for `1`-periodic Hamiltonians `H_q`, and let
`u : ℝ × ℝ → M` solve the Floer equation `(du - X_K)^{0,1} = 0` on `S` with image in a compact set
`B ⊆ M` and integrable symplectic area density and curvature along `u`.

Because `[0, 1] × B` is compact, each continuous Hamiltonian `H_q` is automatically bounded along
the end loops of `u`, so the truncated energy identity of
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Identity` implies that `u` has integrable
(in particular finite) Floer energy density on `S` *before* proving end convergence, and without
requiring any global bound on `H_q` outside `B` (see
`IsNondegenerate.integrableOn_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact`
and `lintegral_floerEnergyDensity_of_eq_smul_endAngularForm_ne_top_of_isCompact`).

Combining automatic finite energy with the asymptotic convergence theorems of
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Manifold` and compact-range dominated
convergence along end loops (`TauCeti.Floer.tendsto_intervalIntegral_endChart_of_isCompact`) yields:

* **Energy identity for `C¹` Hamiltonians under isolated subsequential-limit orbits:** without
  assuming `[T2Space M]`, `[BoundarylessManifold I M]`, or finite energy a priori, when
  `e ∘ u ∘ φ'_q` has bounded derivative on some half-cylinder of each end and `1`-periodic orbits of
  `X_{H_q}` in `B` arising as subsequential uniform limits along `endChart q` are isolated at time
  `0`, the map `u` converges along each end `q` to an asymptotic `1`-periodic orbit `y_q` in `B` and
  satisfies `∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt - ∫_S R_K(u)`
  (`exists_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact_of_eventually`,
  specialized to `pairOfPantsPerturbation H` in
  `exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact_of_eventually`).
* **Topological energy lower bound on `B`:** if `|H_q(t, x)| ≤ M_H q` for `x ∈ B`, nonnegativity of
  the Floer energy and the compact-image curvature bound
  `SmoothTwoForm.abs_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_le_of_mapsTo` give
  `-(M_H 0 + M_H 1 + M_H ∞) ≤ ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt`
  (`exists_neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation_of_isCompact_of_eventually`).
* **Corollaries for `C²` Hamiltonians with nondegenerate orbits, and contractible counterparts:**
  on a Hausdorff boundaryless manifold, nondegeneracy of the `1`-periodic orbits in `B` supplies
  isolation (`exists_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact`,
  `exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact`,
  `exists_neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation_of_isCompact`, and their
  closed-manifold specializations). When on each end one loop `t ↦ u(φ_q(±s, t))` (`s > 0`) is
  null-homotopic in `M`, parallel `_of_nullhomotopic` theorems require isolation or nondegeneracy
  only on `contractiblePeriodicSolutions` and produce contractible asymptotic orbits `y_q`.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995).
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1.
-/

public section

open Set Filter Topology MeasureTheory Function TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped ENNReal Manifold

namespace TauCeti.SmoothTwoForm

open Floer

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold I ⊤ M]
  [FiniteDimensional ℝ E] {ω : SmoothTwoForm I M} {K : ℂ → M → ℂ →L[ℝ] ℝ}
  {H : Puncture → ℝ → M → ℝ} {T₀ : ℝ} {B : Set M} {u : ℝ × ℝ → M}

namespace IsNondegenerate

/-! ### Automatic finite energy and energy identity on a compact target set -/

/-- **Automatic integrability of a nonnegative Floer energy density on a compact set.** Let
`K = H_q(t) dt` beyond `T₀` on each end `q` for `1`-periodic continuous functions `H_q`, and let
`u` be `C¹` on `S` with image in a compact set `B ⊆ M`, nonnegative Floer energy density on `S`,
and integrable symplectic area density and curvature over `S`. Because `[0, 1] × B` is compact, the
end-loop integrals `∫₀¹ H_q(t, u(φ_q(±σ, t))) dt` are uniformly bounded for `σ > 0`, so the Floer
energy density of `u` is integrable over `S` without assuming any global bound on `H_q` or end
convergence. -/
theorem integrableOn_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact
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
  have hS : volume.restrict thricePuncturedSphereReal = volume :=
    Measure.restrict_eq_self_of_ae_mem ae_mem_thricePuncturedSphereReal
  rw [IntegrableOn, hS] at hA hR ⊢
  have hbound : ∀ q, ∃ C : ℝ, ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ B, ‖uncurry (H q) p‖ ≤ C := fun q ↦
    (isCompact_Icc.prod hB).exists_bound_of_continuousOn (hHc q).continuousOn
  choose C hC using hbound
  refine hω.integrable_floerEnergyDensity_of_eq_smul_endAngularForm hK hKH hH hu he hA hR
    (C := C) fun q ↦ ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with σ hσ
  have hmem (t : ℝ) : endChart q (q.endSign * σ, t) ∈ thricePuncturedSphereReal :=
    endChart_mem_thricePuncturedSphereReal
      (by simpa only [← mul_assoc, endSign_mul_self, one_mul] using hσ)
  simpa only [Real.norm_eq_abs, uncurry_apply_pair, sub_zero, abs_one, mul_one] using
    intervalIntegral.norm_integral_le_of_norm_le_const fun t ht ↦
      hC q (t, u (endChart q (q.endSign * σ, t)))
        ⟨Ioc_subset_Icc_self (uIoc_of_le (zero_le_one : (0 : ℝ) ≤ 1) ▸ ht), huB _ (hmem t)⟩

/-- **Automatic finiteness of the Lebesgue Floer energy on a compact set.** Under the hypotheses of
`integrableOn_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact`, the Lebesgue integral of
the Floer energy density of `u` over `S` is finite. -/
theorem lintegral_floerEnergyDensity_of_eq_smul_endAngularForm_ne_top_of_isCompact
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
    ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤ := by
  have hS : volume.restrict thricePuncturedSphereReal = volume :=
    Measure.restrict_eq_self_of_ae_mem ae_mem_thricePuncturedSphereReal
  have hEint := hω.integrableOn_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact
    hK hKH hH hHc hB hu huB he hA hR
  rw [IntegrableOn, hS] at hEint
  rw [hS, ← ofReal_integral_eq_lintegral_ofReal hEint (ae_mem_thricePuncturedSphereReal.mono he)]
  exact ENNReal.ofReal_ne_top

/-- **The manifold pair-of-pants energy identity on a compact target set.** Under the hypotheses of
`integrableOn_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact`, if the end loops
`t ↦ u(φ_q(±s, t))` converge pointwise to `y_q` as `s → ∞` on each end `q`, then
`∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt - ∫_S R_K(u)`, without assuming finite energy a
priori or any bound on `H_q` outside `B`. -/
theorem integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact
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
      thricePuncturedSphereReal)
    {y : Puncture → ℝ → M}
    (hy : ∀ q t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) :
    ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      (∫ z in thricePuncturedSphereReal,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
        ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
  have hS : volume.restrict thricePuncturedSphereReal = volume :=
    Measure.restrict_eq_self_of_ae_mem ae_mem_thricePuncturedSphereReal
  have hEint := hω.integrableOn_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact
    hK hKH hH hHc hB hu huB he hA hR
  rw [IntegrableOn, hS] at hEint hA hR
  simp only [hS]
  exact hω.integral_floerEnergyDensity_of_eq_smul_endAngularForm hK hKH hH hu hEint hA hR
    fun q ↦ tendsto_intervalIntegral_endChart_of_isCompact (hHc q) hB hu.continuousOn huB (hy q)

/-! ### Energy identity and topological energy bound at asymptotic periodic orbits -/

section AsymptoticEnergy

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {e : M → F} {c : ℝ}

/-- **The manifold pair-of-pants energy identity at isolated asymptotic periodic orbits.** Let `ω`
be a nondegenerate two-form on `M`, let `K` be `C¹` on `S × M` with `K = H_q(t) dt` beyond `T₀` on
each end `q` for `1`-periodic `C¹` Hamiltonians `H_q`, and let `u` be `C¹` on `S` with image in a
compact set `B ⊆ M`, solving `(du - X_K)^{0,1} = 0` on `S` for almost complex structures uniformly
tame through `e`, with integrable symplectic area density and curvature over `S`. If on each end
`q` the map `e ∘ u ∘ φ'_q` has bounded derivative on some half-cylinder and every `1`-periodic
orbit of `X_{H_q}` in `B` arising as a subsequential uniform limit along `endChart q` is isolated
at time `0` among such orbits, then `u` has integrable Floer energy density on `S`, converges along
each end `q` to a `1`-periodic orbit `y_q` of `X_{H_q}` in `B`, and satisfies
`∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt - ∫_S R_K(u)`. -/
theorem exists_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact_of_eventually
    (hω : ω.IsNondegenerate)
    (hK : ∀ (w : ThricePuncturedSphere) x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x))
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))
      thricePuncturedSphereReal)
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hiso : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) →
      (∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop) →
      ∀ᶠ p in 𝓝 (y 0), ∀ y' ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
        (∀ t, y' t ∈ B) →
        (∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
          TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y') atTop) →
        y' 0 = p → y' = y) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
  have he_nonneg : ∀ z ∈ thricePuncturedSphereReal, 0 ≤ ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z := fun z hz ↦
    floerEnergyDensity_nonneg hω
      (hω.tames_of_tame_mvfderiv (hde _ (huB z hz)) hc (hJc z hz)) (hfloer z hz)
  have hHc : ∀ q, Continuous (uncurry (H q)) := fun q ↦ (hHs q).continuous
  have hE := hω.lintegral_floerEnergyDensity_of_eq_smul_endAngularForm_ne_top_of_isCompact
    hK hKH hH hHc hB hu huB he_nonneg hA hR
  choose b C hbC using hC
  have hmem (q : Puncture) (z : ℝ × ℝ) (hz : max (b q) 0 < z.1) :
      positiveEndChart q z ∈ thricePuncturedSphereReal :=
    positiveEndChart_mem_thricePuncturedSphereReal ((le_max_right (b q) 0).trans_lt hz)
  have hex (q : Puncture) :=
    exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact_of_eventually
      hω hKH hH he hB he_inj hde hu huB J hfloer hE q (hHs q)
      (fun z hz ↦ hbC q z ((le_max_left (b q) 0).trans_lt hz)) hc
      (fun z hz v ↦ hJc _ (hmem q z hz) v) (hiso q)
  choose y hy using hex
  exact ⟨y, hy,
    hω.integrableOn_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact
      hK hKH hH hHc hB hu huB he_nonneg hA hR,
    hω.integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact
      hK hKH hH hHc hB hu huB he_nonneg hA hR fun q ↦ (hy q).2.2.2⟩

/-- **The manifold pair-of-pants energy identity at nondegenerate asymptotic periodic orbits.**
Corollary of
`exists_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact_of_eventually` for `C²`
Hamiltonians `H_q` on a Hausdorff boundaryless manifold `M` whose `1`-periodic orbits in `B` are
nondegenerate fixed points of the time-one flow. No finite-energy hypothesis is needed. -/
theorem exists_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hK : ∀ (w : ThricePuncturedSphere) x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x))
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))
      thricePuncturedSphereReal)
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hnd : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
  have hX (q : Puncture) := hω.contMDiff_hamiltonianVectorField_uncurry (n := 1) (by simp)
    ((hHs q).of_le (by norm_num))
  exact
    exists_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact_of_eventually
      hω hK hKH hH (fun q ↦ (hHs q).of_le one_le_two) he hB he_inj hde hu huB J hc hJc hfloer hA
      hR hC fun q y hy hyB _ ↦
        (eventually_forall_mem_periodicSolutions_eq_of_eventually_not_isFixedPt (hX q)
          (mem_periodicSolutions.1 hy).1 (s := 0) (T := 1)
          (by simpa only [zero_add] using (hnd q y hy hyB).eventually_not_isFixedPt)).mono
          fun p hp y' hy' _ _ hy'p ↦ hp y' hy' hy'p

/-- **The manifold energy identity of the pair-of-pants perturbation at isolated asymptotic
periodic orbits.** Specialization of
`exists_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact_of_eventually` to
`TauCeti.Floer.pairOfPantsPerturbation H` for `C¹` Hamiltonians `H_q`. -/
theorem exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact_of_eventually
    (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hiso : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) →
      (∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop) →
      ∀ᶠ p in 𝓝 (y 0), ∀ y' ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
        (∀ t, y' t ∈ B) →
        (∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
          TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y') atTop) →
        y' 0 = p → y' = y) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z =
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z) :=
  exists_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact_of_eventually
    (K := pairOfPantsPerturbation H) (T₀ := 2) hω
    (fun w x ↦ contMDiffAt_pairOfPantsPerturbation hH hHs w x)
    (fun _ _ x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm hw x) hH hHs he hB he_inj hde
    hu huB J hc hJc hfloer hA
    (integrableOn_hamiltonianCurvature_pairOfPantsPerturbation ω hH hHs hu.continuousOn) hC hiso

/-- **The manifold energy identity of the pair-of-pants perturbation at nondegenerate asymptotic
periodic orbits.** Specialization of
`exists_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact` to
`TauCeti.Floer.pairOfPantsPerturbation H`, for which smoothness and integrability of the curvature
and finiteness of the Floer energy hold automatically. -/
theorem exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hnd : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z =
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z) := by
  have hHs₁ : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)) :=
    fun q ↦ (hHs q).of_le one_le_two
  exact hω.exists_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact
    (K := pairOfPantsPerturbation H) (T₀ := 2)
    (fun w x ↦ contMDiffAt_pairOfPantsPerturbation hH hHs₁ w x)
    (fun _ _ x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm hw x) hH hHs he hB he_inj hde
    hu huB J hc hJc hfloer hA
    (integrableOn_hamiltonianCurvature_pairOfPantsPerturbation ω hH hHs₁ hu.continuousOn) hC hnd

/-- **The manifold energy identity of the pair-of-pants perturbation in a closed manifold.**
Specialization of `exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact` to a
compact Hausdorff boundaryless manifold `M`. -/
theorem exists_integral_floerEnergyDensity_pairOfPantsPerturbation
    [CompactSpace M] [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e) (hde : ∀ p, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hnd : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z =
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z) := by
  obtain ⟨y, hy, hEint, hid⟩ :=
    hω.exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact hH hHs he
      isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) J hc hJc hfloer hA
      hC fun q y hy _ ↦ hnd q y hy
  exact ⟨y, fun q ↦ ⟨(hy q).1, (hy q).2.2⟩, hEint, hid⟩

/-- **Lower bound on the topological energy at isolated asymptotic periodic orbits.** Under the
hypotheses of
`exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact_of_eventually`, if
`|H_q(t, x)| ≤ M_H q` on `B`, then the topological energy
`∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt` at the asymptotic `1`-periodic orbits `y_q` is at least
`-(M_H 0 + M_H 1 + M_H ∞)`. -/
theorem exists_neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation_of_isCompact_of_eventually
    (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {M_H : Puncture → ℝ} (hMH : ∀ q t, ∀ x ∈ B, |H q t x| ≤ M_H q)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hiso : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) →
      (∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop) →
      ∀ᶠ p in 𝓝 (y 0), ∀ y' ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
        (∀ t, y' t ∈ B) →
        (∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
          TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y') atTop) →
        y' 0 = p → y' = y) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      -∑ q, M_H q ≤
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t) := by
  obtain ⟨y, hy, -, hid⟩ :=
    exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact_of_eventually
      hω hH hHs he hB he_inj hde hu huB J hc hJc hfloer hA hC hiso
  have hpos : 0 ≤ ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z :=
    setIntegral_nonneg isOpen_thricePuncturedSphereReal.measurableSet fun z hz ↦
      floerEnergyDensity_nonneg hω
        (hω.tames_of_tame_mvfderiv (hde _ (huB z hz)) hc (hJc z hz)) (hfloer z hz)
  have hcurv := abs_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_le_of_mapsTo ω hH hHs
    hMH huB thricePuncturedSphereReal
  exact ⟨y, hy, by linarith [(abs_le.1 hcurv).1]⟩

/-- **Lower bound on the topological energy at nondegenerate asymptotic periodic orbits.** Under
the hypotheses of `exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact`, if
`|H_q(t, x)| ≤ M_H q` for `x ∈ B`, then the topological energy
`∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt` at the asymptotic `1`-periodic orbits `y_q` is at least
`-(M_H 0 + M_H 1 + M_H ∞)`. -/
theorem exists_neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation_of_isCompact
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    {M_H : Puncture → ℝ} (hMH : ∀ q t, ∀ x ∈ B, |H q t x| ≤ M_H q)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hnd : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      -∑ q, M_H q ≤
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t) := by
  have hX (q : Puncture) := hω.contMDiff_hamiltonianVectorField_uncurry (n := 1) (by simp)
    ((hHs q).of_le (by norm_num))
  exact
    exists_neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation_of_isCompact_of_eventually
      hω hH (fun q ↦ (hHs q).of_le one_le_two) hMH he hB he_inj hde hu huB J hc hJc hfloer hA hC
      fun q y hy hyB _ ↦
        (eventually_forall_mem_periodicSolutions_eq_of_eventually_not_isFixedPt (hX q)
          (mem_periodicSolutions.1 hy).1 (s := 0) (T := 1)
          (by simpa only [zero_add] using (hnd q y hy hyB).eventually_not_isFixedPt)).mono
          fun p hp y' hy' _ _ hy'p ↦ hp y' hy' hy'p

/-- **Lower bound on the topological energy at nondegenerate asymptotic periodic orbits in a closed
manifold.** Specialization of
`exists_neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation_of_isCompact` to a compact Hausdorff
boundaryless manifold `M`. -/
theorem exists_neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation
    [CompactSpace M] [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    {M_H : Puncture → ℝ} (hMH : ∀ q t x, |H q t x| ≤ M_H q)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e) (hde : ∀ p, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hnd : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      -∑ q, M_H q ≤
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t) := by
  obtain ⟨y, hy, hle⟩ :=
    hω.exists_neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation_of_isCompact hH hHs
      (fun q t x _ ↦ hMH q t x) he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu
      (fun _ _ ↦ mem_univ _) J hc hJc hfloer hA hC fun q y hy _ ↦ hnd q y hy
  exact ⟨y, fun q ↦ ⟨(hy q).1, (hy q).2.2⟩, hle⟩

/-! ### Energy identity and topological energy bound at contractible asymptotic periodic orbits -/

/-- **The manifold pair-of-pants energy identity at isolated contractible asymptotic periodic
orbits.** Under the hypotheses of
`exists_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact_of_eventually`, if on
each end `q` one end loop `t ↦ u(φ_q(±s, t))` (`s > 0`) is null-homotopic in `M` and isolation at
time `0` is assumed only among contractible `1`-periodic orbits of `X_{H_q}` in `B` arising as
subsequential uniform limits along `endChart q`, then the asymptotic orbits `y_q` belong to
`contractiblePeriodicSolutions`. -/
theorem exists_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_nullhomotopic_of_eventually
    (hω : ω.IsNondegenerate)
    (hK : ∀ (w : ThricePuncturedSphere) x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x))
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (hnull : ∀ q, ∃ s > 0, ∃ g : C(AddCircle (1 : ℝ), M),
      g.Nullhomotopic ∧ ∀ t : ℝ, g t = u (endChart q (q.endSign * s, t)))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))
      thricePuncturedSphereReal)
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hiso : ∀ q,
      ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
        (∀ t, y t ∈ B) →
        (∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
          TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop) →
        ∀ᶠ p in 𝓝 (y 0),
          ∀ y' ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
            (∀ t, y' t ∈ B) →
            (∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
              TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y') atTop) →
            y' 0 = p → y' = y) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
  have he_nonneg : ∀ z ∈ thricePuncturedSphereReal, 0 ≤ ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z := fun z hz ↦
    floerEnergyDensity_nonneg hω
      (hω.tames_of_tame_mvfderiv (hde _ (huB z hz)) hc (hJc z hz)) (hfloer z hz)
  have hHc : ∀ q, Continuous (uncurry (H q)) := fun q ↦ (hHs q).continuous
  have hE := hω.lintegral_floerEnergyDensity_of_eq_smul_endAngularForm_ne_top_of_isCompact
    hK hKH hH hHc hB hu huB he_nonneg hA hR
  choose b C hbC using hC
  have hmem (q : Puncture) (z : ℝ × ℝ) (hz : max (b q) 0 < z.1) :
      positiveEndChart q z ∈ thricePuncturedSphereReal :=
    positiveEndChart_mem_thricePuncturedSphereReal ((le_max_right (b q) 0).trans_lt hz)
  have hex (q : Puncture) :=
    exists_mem_contractiblePeriodicSolutions_endChart_atTop_of_floer_of_isCompact_of_eventually
      hω hKH hH he hB he_inj hde hu huB J hfloer hE q (hHs q) (hnull q)
      (fun z hz ↦ hbC q z ((le_max_left (b q) 0).trans_lt hz)) hc
      (fun z hz v ↦ hJc _ (hmem q z hz) v) (hiso q)
  choose y hy using hex
  exact ⟨y, hy,
    hω.integrableOn_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact
      hK hKH hH hHc hB hu huB he_nonneg hA hR,
    hω.integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact
      hK hKH hH hHc hB hu huB he_nonneg hA hR fun q ↦ (hy q).2.2.2⟩

/-- **The manifold pair-of-pants energy identity at nondegenerate contractible asymptotic periodic
orbits.** Corollary of
`exists_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_nullhomotopic_of_eventually` for
`C²` Hamiltonians `H_q` on a Hausdorff boundaryless manifold `M` assuming nondegeneracy only on
`contractiblePeriodicSolutions`. -/
theorem exists_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact_of_nullhomotopic
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hK : ∀ (w : ThricePuncturedSphere) x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x))
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (hnull : ∀ q, ∃ s > 0, ∃ g : C(AddCircle (1 : ℝ), M),
      g.Nullhomotopic ∧ ∀ t : ℝ, g t = u (endChart q (q.endSign * s, t)))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))
      thricePuncturedSphereReal)
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hnd : ∀ q,
      ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
        (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
          (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
  have hX (q : Puncture) := hω.contMDiff_hamiltonianVectorField_uncurry (n := 1) (by simp)
    ((hHs q).of_le (by norm_num))
  exact
    exists_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_nullhomotopic_of_eventually
      hω hK hKH hH (fun q ↦ (hHs q).of_le one_le_two) he hB he_inj hde hu huB hnull J hc hJc
      hfloer hA hR hC fun q y hy hyB _ ↦
        (eventually_forall_mem_periodicSolutions_eq_of_eventually_not_isFixedPt (hX q)
          (mem_periodicSolutions.1 (contractiblePeriodicSolutions_subset hy)).1 (s := 0) (T := 1)
          (by simpa only [zero_add] using (hnd q y hy hyB).eventually_not_isFixedPt)).mono
          fun p hp y' hy' _ _ hy'p ↦ hp y' (contractiblePeriodicSolutions_subset hy') hy'p

/-- **The manifold energy identity of the pair-of-pants perturbation at isolated contractible
asymptotic periodic orbits.** Specialization of
`exists_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_nullhomotopic_of_eventually` to
`TauCeti.Floer.pairOfPantsPerturbation H`. -/
theorem exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_nullhomotopic_of_eventually
    (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (hnull : ∀ q, ∃ s > 0, ∃ g : C(AddCircle (1 : ℝ), M),
      g.Nullhomotopic ∧ ∀ t : ℝ, g t = u (endChart q (q.endSign * s, t)))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hiso : ∀ q,
      ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
        (∀ t, y t ∈ B) →
        (∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
          TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop) →
        ∀ᶠ p in 𝓝 (y 0),
          ∀ y' ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
            (∀ t, y' t ∈ B) →
            (∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
              TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y') atTop) →
            y' 0 = p → y' = y) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z =
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z) :=
  exists_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_nullhomotopic_of_eventually
    (K := pairOfPantsPerturbation H) (T₀ := 2) hω
    (fun w x ↦ contMDiffAt_pairOfPantsPerturbation hH hHs w x)
    (fun _ _ x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm hw x) hH hHs he hB he_inj hde
    hu huB hnull J hc hJc hfloer hA
    (integrableOn_hamiltonianCurvature_pairOfPantsPerturbation ω hH hHs hu.continuousOn) hC hiso

/-- **The manifold energy identity of the pair-of-pants perturbation at nondegenerate contractible
asymptotic periodic orbits.** Specialization of
`exists_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact_of_nullhomotopic` to
`TauCeti.Floer.pairOfPantsPerturbation H`. -/
theorem exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact_of_nullhomotopic
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (hnull : ∀ q, ∃ s > 0, ∃ g : C(AddCircle (1 : ℝ), M),
      g.Nullhomotopic ∧ ∀ t : ℝ, g t = u (endChart q (q.endSign * s, t)))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hnd : ∀ q,
      ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
        (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
          (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z =
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z) := by
  have hHs₁ : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)) :=
    fun q ↦ (hHs q).of_le one_le_two
  exact
    exists_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact_of_nullhomotopic
      (K := pairOfPantsPerturbation H) (T₀ := 2) hω
      (fun w x ↦ contMDiffAt_pairOfPantsPerturbation hH hHs₁ w x)
      (fun _ _ x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm hw x) hH hHs he hB he_inj hde
      hu huB hnull J hc hJc hfloer hA
      (integrableOn_hamiltonianCurvature_pairOfPantsPerturbation ω hH hHs₁ hu.continuousOn) hC hnd

/-- **The manifold energy identity of the pair-of-pants perturbation at contractible asymptotic
periodic orbits in a closed manifold.** Specialization of
`exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact_of_nullhomotopic` to a
compact Hausdorff boundaryless manifold `M`. -/
theorem exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_nullhomotopic
    [CompactSpace M] [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e) (hde : ∀ p, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (hnull : ∀ q, ∃ s > 0, ∃ g : C(AddCircle (1 : ℝ), M),
      g.Nullhomotopic ∧ ∀ t : ℝ, g t = u (endChart q (q.endSign * s, t)))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hnd : ∀ q,
      ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
        IsNondegenerateFixedPt I
          (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z =
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z) := by
  obtain ⟨y, hy, hEint, hid⟩ :=
    exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact_of_nullhomotopic hω hH
      hHs he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) hnull J hc hJc
      hfloer hA hC fun q y hy _ ↦ hnd q y hy
  exact ⟨y, fun q ↦ ⟨(hy q).1, (hy q).2.2⟩, hEint, hid⟩

/-- **Lower bound on the topological energy at isolated contractible asymptotic periodic orbits.**
Under the hypotheses of
`exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_nullhomotopic_of_eventually`, if
`|H_q(t, x)| ≤ M_H q` on `B`, then the topological energy at the contractible asymptotic orbits
`y_q` is at least `-(M_H 0 + M_H 1 + M_H ∞)`. -/
theorem exists_neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation_of_nullhomotopic_of_eventually
    (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {M_H : Puncture → ℝ} (hMH : ∀ q t, ∀ x ∈ B, |H q t x| ≤ M_H q)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (hnull : ∀ q, ∃ s > 0, ∃ g : C(AddCircle (1 : ℝ), M),
      g.Nullhomotopic ∧ ∀ t : ℝ, g t = u (endChart q (q.endSign * s, t)))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hiso : ∀ q,
      ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
        (∀ t, y t ∈ B) →
        (∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
          TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop) →
        ∀ᶠ p in 𝓝 (y 0),
          ∀ y' ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
            (∀ t, y' t ∈ B) →
            (∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
              TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y') atTop) →
            y' 0 = p → y' = y) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      -∑ q, M_H q ≤
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t) := by
  obtain ⟨y, hy, -, hid⟩ :=
    exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_nullhomotopic_of_eventually
      hω hH hHs he hB he_inj hde hu huB hnull J hc hJc hfloer hA hC hiso
  have hpos : 0 ≤ ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z :=
    setIntegral_nonneg isOpen_thricePuncturedSphereReal.measurableSet fun z hz ↦
      floerEnergyDensity_nonneg hω
        (hω.tames_of_tame_mvfderiv (hde _ (huB z hz)) hc (hJc z hz)) (hfloer z hz)
  have hcurv := abs_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_le_of_mapsTo ω hH hHs
    hMH huB thricePuncturedSphereReal
  exact ⟨y, hy, by linarith [(abs_le.1 hcurv).1]⟩

/-- **Lower bound on the topological energy at nondegenerate contractible asymptotic periodic
orbits.** Corollary of
`exists_neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation_of_nullhomotopic_of_eventually` for
`C²` Hamiltonians `H_q` on a Hausdorff boundaryless manifold `M` assuming nondegeneracy only on
`contractiblePeriodicSolutions`. -/
theorem exists_neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation_of_isCompact_of_nullhomotopic
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    {M_H : Puncture → ℝ} (hMH : ∀ q t, ∀ x ∈ B, |H q t x| ≤ M_H q)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (hnull : ∀ q, ∃ s > 0, ∃ g : C(AddCircle (1 : ℝ), M),
      g.Nullhomotopic ∧ ∀ t : ℝ, g t = u (endChart q (q.endSign * s, t)))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hnd : ∀ q,
      ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
        (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
          (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      -∑ q, M_H q ≤
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t) := by
  have hX (q : Puncture) := hω.contMDiff_hamiltonianVectorField_uncurry (n := 1) (by simp)
    ((hHs q).of_le (by norm_num))
  exact
    exists_neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation_of_nullhomotopic_of_eventually
      hω hH (fun q ↦ (hHs q).of_le one_le_two) hMH he hB he_inj hde hu huB hnull J hc hJc hfloer
      hA hC fun q y hy hyB _ ↦
        (eventually_forall_mem_periodicSolutions_eq_of_eventually_not_isFixedPt (hX q)
          (mem_periodicSolutions.1 (contractiblePeriodicSolutions_subset hy)).1 (s := 0) (T := 1)
          (by simpa only [zero_add] using (hnd q y hy hyB).eventually_not_isFixedPt)).mono
          fun p hp y' hy' _ _ hy'p ↦ hp y' (contractiblePeriodicSolutions_subset hy') hy'p

/-- **Lower bound on the topological energy at contractible asymptotic periodic orbits in a closed
manifold.** Specialization of
`exists_neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation_of_isCompact_of_nullhomotopic` to a
compact Hausdorff boundaryless manifold `M`. -/
theorem exists_neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation_of_nullhomotopic
    [CompactSpace M] [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
    {M_H : Puncture → ℝ} (hMH : ∀ q t x, |H q t x| ≤ M_H q)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e) (hde : ∀ p, Injective (mvfderiv I e p))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (hnull : ∀ q, ∃ s > 0, ∃ g : C(AddCircle (1 : ℝ), M),
      g.Nullhomotopic ∧ ∀ t : ℝ, g t = u (endChart q (q.endSign * s, t)))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hC : ∀ q, ∃ b C, ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)
    (hnd : ∀ q,
      ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
        IsNondegenerateFixedPt I
          (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
      -∑ q, M_H q ≤
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t) := by
  obtain ⟨y, hy, hle⟩ :=
    exists_neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation_of_isCompact_of_nullhomotopic hω
      hH hHs (fun q t x _ ↦ hMH q t x) he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu
      (fun _ _ ↦ mem_univ _) hnull J hc hJc hfloer hA hC fun q y hy _ ↦ hnd q y hy
  exact ⟨y, fun q ↦ ⟨(hy q).1, (hy q).2.2⟩, hle⟩

end AsymptoticEnergy

end IsNondegenerate

end TauCeti.SmoothTwoForm
