/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Manifold
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Asymptotic
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Integrable
import TauCeti.Geometry.Symplectic.Hamiltonian.PeriodicOrbit
import TauCeti.Order.Filter.Basic

/-!
# The energy identity and topological energy bound for a Floer pair of pants in a manifold

Let `ω` be a nondegenerate two-form on a finite-dimensional manifold `M`, let `K` be a Hamiltonian
perturbation on the pair of pants `S = ℂ ∖ {0, 1}` equal to `H_q(t) dt` beyond `T₀` on each end `q`
for `1`-periodic Hamiltonians `H_q`, and let `u : ℝ × ℝ → M` solve `(du - X_K)^{0,1} = 0` on `S`
with image in a compact set `B ⊆ M` and integrable symplectic area density and curvature along `u`.

In `TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Integrable` and
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Asymptotic`, compactness of `[0, 1] × B`
bounds `H_q` along end loops, giving automatic finite energy once the Floer energy density is
nonnegative on `S` (`integrableOn_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact`)
and the energy identity from pointwise end limits
(`integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact`). Combined with
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Manifold`, this yields:

* **Energy identity (`C¹` with isolated subsequential-limit orbits):** without `[T2Space M]`,
  `[BoundarylessManifold I M]`, or finite energy a priori, assuming pointwise tameness of `J` on
  `S` (giving nonnegative energy density) as well as bounded derivative of `e ∘ u ∘ φ'_q` and
  uniform tameness through `e` on the tail strips `(b_q, ∞) × [0, 1]`, `u` converges along each
  end `q` to an orbit `y_q` in `B` (with convergence of `∫₀¹ H_q(t, u(φ_q(±s, t))) dt`), has
  integrable energy density, and satisfies
  `∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt - ∫_S R_K(u)`
  (`exists_integral_floerEnergyDensity_of_cylindricalEnds_of_isCompact_of_isolated_clusterPt`,
  specialized to `pairOfPantsPerturbation H`).
* **Topological energy lower bound on `B`:** if `|H_q(t, x)| ≤ M_H q` on `B`, then
  `-(M_H 0 + M_H 1 + M_H ∞) ≤ ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt`.
* **Corollaries:** nondegeneracy supplies isolation for `C²` `H_q` on a Hausdorff boundaryless
  manifold (including closed-manifold specializations); when one end loop per end is
  null-homotopic, parallel `_of_nullhomotopic` theorems require isolation or nondegeneracy only on
  `contractiblePeriodicSolutions` and yield contractible `y_q`.

## References

* D. Salamon, *Lectures on Floer homology*, IAS/Park City Math. Ser. 7 (1999), Lecture 1.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis (1995).
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

/-! ### Energy identity and topological energy bound at asymptotic periodic orbits -/

section AsymptoticEnergy

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {e : M → F}

section Compact

variable (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
  (he : ContMDiff I 𝓘(ℝ, F) 1 e) (hB : IsCompact B) (he_inj : InjOn e B)
  (hde : ∀ p ∈ B, Injective (mvfderiv I e p))
  (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
  (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
  (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
  (hJ : ∀ z ∈ thricePuncturedSphereReal, (hω.symplecticFormAt (u z)).Tames (J z))
  (hJc : ∀ q, ∃ b c, 0 < c ∧ ∀ z ∈ Ioi b ×ˢ Icc 0 1, ∀ v,
    c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
      hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v))
  (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
    (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
    (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
  (hC : ∀ q, ∃ b C, ∀ z ∈ Ioi b ×ˢ Icc 0 1,
    ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)

section General

variable
  (hK : ∀ (w : ThricePuncturedSphere) x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
    (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x))
  (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
    K w x = H q (q.endCoord w).im x • q.endAngularForm w)
  (hfloer : ∀ z ∈ thricePuncturedSphereReal,
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
  (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
    (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))
    thricePuncturedSphereReal)

include hω hK hKH hH he hB he_inj hde hu huB J hJ hJc hfloer hA hR hC

omit [NormedSpace ℝ F] [FiniteDimensional ℝ F] he he_inj hde hJc hC in
/-- Shared derivation of integrability, Hamiltonian loop-integral limits, and the energy identity
from an end-by-end convergence package returning orbits in `P q`. -/
private theorem exists_energy_of_endConvergence {P : Puncture → Set (ℝ → M)}
    (hHc : ∀ q, Continuous (uncurry (H q)))
    (hex : (∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) →
      ∀ q, ∃ y ∈ P q, (∀ t, y t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t))) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ P q ∧ (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        (∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
        Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t))))
          atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t)))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
        (∫ z in thricePuncturedSphereReal, (SmoothBundleForm.eval₂ ω (u z)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
  have he₀ : ∀ z ∈ thricePuncturedSphereReal, 0 ≤ ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z := fun z hz ↦
    floerEnergyDensity_nonneg hω (hJ z hz) (hfloer z hz)
  have hEint := hω.integrableOn_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact
    hK hKH hH hHc hB hu huB he₀ hA hR
  have hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hEint
      (ae_restrict_of_forall_mem isOpen_thricePuncturedSphereReal.measurableSet he₀)]
    exact ENNReal.ofReal_ne_top
  choose y hy using hex hE
  have hlim (q : Puncture) := tendsto_intervalIntegral_endChart_of_isCompact (hHc q) hB
    hu.continuousOn huB (hy q).2.2.2
  refine ⟨y, fun q ↦ ⟨(hy q).1, (hy q).2.1, (hy q).2.2.1, (hy q).2.2.2, hlim q⟩, hEint, ?_⟩
  rw [IntegrableOn, volume_restrict_thricePuncturedSphereReal] at hEint hA hR
  simp only [volume_restrict_thricePuncturedSphereReal]
  exact hω.integral_floerEnergyDensity_of_eq_smul_endAngularForm hK hKH hH hu hEint hA hR hlim

/-- **The manifold pair-of-pants energy identity at isolated asymptotic periodic orbits.** Under
compact image `B`, integrable symplectic area density and curvature along `u`, pointwise tameness of
`J`, uniform tameness through `e` and bounded derivative of `e ∘ u ∘ φ'_q` on each end tail strip
`(b_q, ∞) × [0, 1]`, and isolation at time `0` of subsequential uniform-limit orbits in `B`, `u`
has integrable Floer energy density, converges along each end to an orbit `y_q` in `B`, and
satisfies the energy identity. -/
theorem exists_integral_floerEnergyDensity_of_cylindricalEnds_of_isCompact_of_isolated_clusterPt
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hiso : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) →
      (∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop) →
      ∀ᶠ p in 𝓝 (y 0),
        ∀ y' ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
          (∀ t, y' t ∈ B) →
          (∃ τ : ℕ → ℝ, Tendsto τ atTop atTop ∧
            TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * τ n, t))))
              (e ∘ y') atTop) →
          y' 0 = p → y' = y) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        (∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
        Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t))))
          atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t)))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
        (∫ z in thricePuncturedSphereReal, (SmoothBundleForm.eval₂ ω (u z)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
  choose b C hbC using hC
  choose b' c hc hb'c using hJc
  refine exists_energy_of_endConvergence hω hH hB hu huB J hJ hA hK hKH hfloer
    hR (fun q ↦ (hHs q).continuous) fun hE q ↦ ?_
  exact hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_isolated_clusterPt
    q (hKH q) (hH q) he hB he_inj hde hu huB J hfloer hE (b := max (b q) (b' q))
    (fun z hz ↦ hbC q z ⟨(le_max_left _ _).trans_lt hz.1, hz.2⟩) (hc q)
    (fun z hz v ↦ hb'c q z ⟨(le_max_right _ _).trans_lt hz.1, hz.2⟩ v) (hHs q) (hiso q)

/-- **The manifold pair-of-pants energy identity at isolated contractible asymptotic periodic
orbits.** Variant requiring isolation only among `contractiblePeriodicSolutions` when one end loop
per end is null-homotopic in `M`. -/
theorem
    exists_integral_floerEnergyDensity_of_cylindricalEnds_of_nullhomotopic_of_isolated_clusterPt
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hnull : ∀ q, ∃ s > (0 : ℝ), ∃ g : C(AddCircle (1 : ℝ), M),
      g.Nullhomotopic ∧ ∀ t : ℝ, g t = u (endChart q (q.endSign * s, t)))
    (hiso : ∀ q,
      ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) →
      (∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop) →
      ∀ᶠ p in 𝓝 (y 0),
        ∀ y' ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
          (∀ t, y' t ∈ B) →
          (∃ τ : ℕ → ℝ, Tendsto τ atTop atTop ∧
            TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * τ n, t))))
              (e ∘ y') atTop) →
          y' 0 = p → y' = y) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        (∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
        Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t))))
          atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t)))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
        (∫ z in thricePuncturedSphereReal, (SmoothBundleForm.eval₂ ω (u z)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
  choose b C hbC using hC
  choose b' c hc hb'c using hJc
  refine exists_energy_of_endConvergence hω hH hB hu huB J hJ hA hK hKH hfloer
    hR (fun q ↦ (hHs q).continuous) fun hE q ↦
  exists_mem_contractiblePeriodicSolutions_tendstoUniformly_endChart_atTop_of_isolated_clusterPt
    hω q (hKH q) (hH q) he hB he_inj hde hu huB J hfloer hE (b := max (b q) (b' q))
    (fun z hz ↦ hbC q z ⟨(le_max_left _ _).trans_lt hz.1, hz.2⟩) (hc q)
    (fun z hz v ↦ hb'c q z ⟨(le_max_right _ _).trans_lt hz.1, hz.2⟩ v)
    (hHs q) (hnull q) (hiso q)

section Nondegenerate

variable [T2Space M] [BoundarylessManifold I M]
  (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))

include hHs

/-- **The manifold pair-of-pants energy identity at nondegenerate asymptotic periodic orbits.**
Corollary for `C²` Hamiltonians `H_q` on a Hausdorff boundaryless manifold without finite energy a
priori. -/
theorem exists_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact
    (hnd : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        (∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
        Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t))))
          atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t)))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
        (∫ z in thricePuncturedSphereReal, (SmoothBundleForm.eval₂ ω (u z)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) :=
  exists_integral_floerEnergyDensity_of_cylindricalEnds_of_isCompact_of_isolated_clusterPt
    hω hH he hB he_inj hde hu huB J hJ hJc hA hC hK hKH hfloer hR
    (fun q ↦ (hHs q).of_le one_le_two)
    fun q ↦ forall_mem_eventually_eq_of_forall_eventually_eq
      (hω.forall_mem_periodicSolutions_hamiltonianVectorField_eventually_eq
        (hHs q) Subset.rfl (hnd q))

/-- **The manifold pair-of-pants energy identity at nondegenerate contractible asymptotic orbits.**
Corollary for `C²` `H_q` assuming nondegeneracy only on `contractiblePeriodicSolutions`. -/
theorem
    exists_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact_of_nullhomotopic
    (hnull : ∀ q, ∃ s > (0 : ℝ), ∃ g : C(AddCircle (1 : ℝ), M),
      g.Nullhomotopic ∧ ∀ t : ℝ, g t = u (endChart q (q.endSign * s, t)))
    (hnd : ∀ q,
      ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        (∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
        Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t))))
          atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t)))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
        (∫ z in thricePuncturedSphereReal, (SmoothBundleForm.eval₂ ω (u z)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) :=
  exists_integral_floerEnergyDensity_of_cylindricalEnds_of_nullhomotopic_of_isolated_clusterPt
    hω hH he hB he_inj hde hu huB J hJ hJc hA hC hK hKH hfloer hR
    (fun q ↦ (hHs q).of_le one_le_two) hnull
    fun q ↦ forall_mem_eventually_eq_of_forall_eventually_eq
      (hω.forall_mem_periodicSolutions_hamiltonianVectorField_eventually_eq
        (hHs q) contractiblePeriodicSolutions_subset (hnd q))

end Nondegenerate

end General

section PairOfPants

variable
  (hfloer : ∀ z ∈ thricePuncturedSphereReal,
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedMFDeriv
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z).toLinearMap)

include hω hH he hB he_inj hde hu huB J hJ hJc hfloer hA hC

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] hH he hB he_inj hde hu huB hJc hA hC in
/-- Nonnegativity of the integrated Floer energy density under pointwise tameness. -/
private theorem setIntegral_floerEnergyDensity_nonneg :
    0 ≤ ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      u z :=
  setIntegral_nonneg isOpen_thricePuncturedSphereReal.measurableSet fun z hz ↦
    floerEnergyDensity_nonneg hω (hJ z hz) (hfloer z hz)

section PeriodicC1

variable (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
  (hiso : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
    (∀ t, y t ∈ B) →
    (∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
      TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop) →
    ∀ᶠ p in 𝓝 (y 0),
      ∀ y' ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
        (∀ t, y' t ∈ B) →
        (∃ τ : ℕ → ℝ, Tendsto τ atTop atTop ∧
          TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * τ n, t))))
            (e ∘ y') atTop) →
        y' 0 = p → y' = y)

include hHs hiso

/-- Specialization of the general `C¹` energy identity to `pairOfPantsPerturbation H`. -/
theorem exists_integral_floerEnergyDensity_pairOfPants_of_isCompact_of_isolated_clusterPt :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        (∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
        Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t))))
          atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t)))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z =
        (∫ z in thricePuncturedSphereReal, (SmoothBundleForm.eval₂ ω (u z)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z) :=
  exists_integral_floerEnergyDensity_of_cylindricalEnds_of_isCompact_of_isolated_clusterPt
    (K := pairOfPantsPerturbation H) (T₀ := 2) hω hH he hB he_inj hde hu huB J hJ hJc hA hC
    (fun w x ↦ contMDiffAt_pairOfPantsPerturbation hH hHs w x)
    (fun _ _ x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm hw x) hfloer
    (integrableOn_hamiltonianCurvature_pairOfPantsPerturbation ω hH hHs hu.continuousOn) hHs hiso

/-- Lower bound on topological energy at isolated asymptotic periodic orbits for `|H_q| ≤ M_H q`.
-/
theorem exists_neg_sum_le_integral_add_sum_of_pairOfPants_of_isCompact_of_isolated_clusterPt
    {M_H : Puncture → ℝ} (hMH : ∀ q t, ∀ x ∈ B, |H q t x| ≤ M_H q) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        (∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
        Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t))))
          atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t)))) ∧
      -∑ q, M_H q ≤
        (∫ z in thricePuncturedSphereReal, (SmoothBundleForm.eval₂ ω (u z)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t) :=
  let ⟨y, hy, _, hid⟩ :=
    exists_integral_floerEnergyDensity_pairOfPants_of_isCompact_of_isolated_clusterPt
      hω hH he hB he_inj hde hu huB J hJ hJc hA hC hfloer hHs hiso
  ⟨y, hy, ω.neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation_of_mapsTo hH hHs hMH huB
    (setIntegral_floerEnergyDensity_nonneg hω J hJ hfloer) hid⟩

end PeriodicC1

section PeriodicC2

variable [T2Space M] [BoundarylessManifold I M]
  (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
  (hnd : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
    (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
      (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))

include hHs hnd

/-- Specialization of the general `C²` energy identity to `pairOfPantsPerturbation H`. -/
theorem exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        (∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
        Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t))))
          atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t)))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z =
        (∫ z in thricePuncturedSphereReal, (SmoothBundleForm.eval₂ ω (u z)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z) :=
  exists_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact
    (K := pairOfPantsPerturbation H) (T₀ := 2) hω hH he hB he_inj hde hu huB J hJ hJc hA hC
    (fun w x ↦ contMDiffAt_pairOfPantsPerturbation hH (fun q ↦ (hHs q).of_le one_le_two) w x)
    (fun _ _ x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm hw x) hfloer
    (integrableOn_hamiltonianCurvature_pairOfPantsPerturbation ω hH
      (fun q ↦ (hHs q).of_le one_le_two) hu.continuousOn)
    hHs hnd

/-- Lower bound on topological energy at nondegenerate asymptotic orbits for `|H_q| ≤ M_H q`. -/
theorem exists_neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation_of_isCompact
    {M_H : Puncture → ℝ} (hMH : ∀ q t, ∀ x ∈ B, |H q t x| ≤ M_H q) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        (∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
        Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t))))
          atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t)))) ∧
      -∑ q, M_H q ≤
        (∫ z in thricePuncturedSphereReal, (SmoothBundleForm.eval₂ ω (u z)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t) :=
  let ⟨y, hy, _, hid⟩ := exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact
    hω hH he hB he_inj hde hu huB J hJ hJc hA hC hfloer hHs hnd
  ⟨y, hy, ω.neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation_of_mapsTo hH
    (fun q ↦ (hHs q).of_le one_le_two) hMH huB
    (setIntegral_floerEnergyDensity_nonneg hω J hJ hfloer) hid⟩

end PeriodicC2

section ContractibleC1

variable (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
  (hnull : ∀ q, ∃ s > (0 : ℝ), ∃ g : C(AddCircle (1 : ℝ), M),
    g.Nullhomotopic ∧ ∀ t : ℝ, g t = u (endChart q (q.endSign * s, t)))
  (hiso : ∀ q,
    ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
    (∀ t, y t ∈ B) →
    (∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
      TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop) →
    ∀ᶠ p in 𝓝 (y 0),
      ∀ y' ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
        (∀ t, y' t ∈ B) →
        (∃ τ : ℕ → ℝ, Tendsto τ atTop atTop ∧
          TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * τ n, t))))
            (e ∘ y') atTop) →
        y' 0 = p → y' = y)

include hHs hnull hiso

/-- Specialization of the contractible `C¹` energy identity to `pairOfPantsPerturbation H`. -/
theorem
    exists_integral_floerEnergyDensity_pairOfPants_of_nullhomotopic_of_isolated_clusterPt :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        (∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
        Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t))))
          atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t)))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z =
        (∫ z in thricePuncturedSphereReal, (SmoothBundleForm.eval₂ ω (u z)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z) :=
  exists_integral_floerEnergyDensity_of_cylindricalEnds_of_nullhomotopic_of_isolated_clusterPt
    (K := pairOfPantsPerturbation H) (T₀ := 2) hω hH he hB he_inj hde hu huB J hJ hJc hA hC
    (fun w x ↦ contMDiffAt_pairOfPantsPerturbation hH hHs w x)
    (fun _ _ x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm hw x) hfloer
    (integrableOn_hamiltonianCurvature_pairOfPantsPerturbation ω hH hHs hu.continuousOn)
    hHs hnull hiso

/-- Lower bound on topological energy at isolated contractible asymptotic orbits. -/
theorem
    exists_neg_sum_le_integral_add_sum_of_pairOfPants_of_nullhomotopic_of_isolated_clusterPt
    {M_H : Puncture → ℝ} (hMH : ∀ q t, ∀ x ∈ B, |H q t x| ≤ M_H q) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        (∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
        Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t))))
          atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t)))) ∧
      -∑ q, M_H q ≤
        (∫ z in thricePuncturedSphereReal, (SmoothBundleForm.eval₂ ω (u z)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t) :=
  let ⟨y, hy, _, hid⟩ :=
    exists_integral_floerEnergyDensity_pairOfPants_of_nullhomotopic_of_isolated_clusterPt
      hω hH he hB he_inj hde hu huB J hJ hJc hA hC hfloer hHs hnull hiso
  ⟨y, hy, ω.neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation_of_mapsTo hH hHs hMH huB
    (setIntegral_floerEnergyDensity_nonneg hω J hJ hfloer) hid⟩

end ContractibleC1

section ContractibleC2

variable [T2Space M] [BoundarylessManifold I M]
  (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
  (hnull : ∀ q, ∃ s > (0 : ℝ), ∃ g : C(AddCircle (1 : ℝ), M),
    g.Nullhomotopic ∧ ∀ t : ℝ, g t = u (endChart q (q.endSign * s, t)))
  (hnd : ∀ q,
    ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
    (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
      (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))

include hHs hnull hnd

/-- Specialization of the contractible `C²` energy identity to `pairOfPantsPerturbation H`. -/
theorem exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact_of_nullhomotopic :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        (∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
        Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t))))
          atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t)))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z =
        (∫ z in thricePuncturedSphereReal, (SmoothBundleForm.eval₂ ω (u z)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z) :=
  exists_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact_of_nullhomotopic
    (K := pairOfPantsPerturbation H) (T₀ := 2) hω hH he hB he_inj hde hu huB J hJ hJc hA hC
    (fun w x ↦ contMDiffAt_pairOfPantsPerturbation hH (fun q ↦ (hHs q).of_le one_le_two) w x)
    (fun _ _ x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm hw x) hfloer
    (integrableOn_hamiltonianCurvature_pairOfPantsPerturbation ω hH
      (fun q ↦ (hHs q).of_le one_le_two) hu.continuousOn)
    hHs hnull hnd

/-- Lower bound on topological energy at nondegenerate contractible asymptotic orbits. -/
theorem
    exists_neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation_of_isCompact_of_nullhomotopic
    {M_H : Puncture → ℝ} (hMH : ∀ q t, ∀ x ∈ B, |H q t x| ≤ M_H q) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        (∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
        Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t))))
          atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t)))) ∧
      -∑ q, M_H q ≤
        (∫ z in thricePuncturedSphereReal, (SmoothBundleForm.eval₂ ω (u z)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t) :=
  let ⟨y, hy, _, hid⟩ :=
    exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact_of_nullhomotopic
      hω hH he hB he_inj hde hu huB J hJ hJc hA hC hfloer hHs hnull hnd
  ⟨y, hy, ω.neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation_of_mapsTo hH
    (fun q ↦ (hHs q).of_le one_le_two) hMH huB
    (setIntegral_floerEnergyDensity_nonneg hω J hJ hfloer) hid⟩

end ContractibleC2

end PairOfPants

end Compact

section Closed

variable [CompactSpace M] [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
  (hH : ∀ q, Periodic (H q) 1)
  (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (H q)))
  (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e) (hde : ∀ p, Injective (mvfderiv I e p))
  (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
  (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
  (hJ : ∀ z ∈ thricePuncturedSphereReal, (hω.symplecticFormAt (u z)).Tames (J z))
  (hJc : ∀ q, ∃ b c, 0 < c ∧ ∀ z ∈ Ioi b ×ˢ Icc 0 1, ∀ v,
    c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
      hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v))
  (hfloer : ∀ z ∈ thricePuncturedSphereReal,
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedMFDeriv
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z).toLinearMap)
  (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
    (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
    (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
  (hC : ∀ q, ∃ b C, ∀ z ∈ Ioi b ×ˢ Icc 0 1,
    ‖fderiv ℝ (e ∘ u ∘ positiveEndChart q) z‖ ≤ C)

include hω hH hHs he he_inj hde hu J hJ hJc hfloer hA hC

section Periodic

variable (hnd : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
  IsNondegenerateFixedPt I
    (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))

include hnd

/-- Closed-manifold specialization of the `pairOfPantsPerturbation H` energy identity. -/
theorem exists_integral_floerEnergyDensity_pairOfPantsPerturbation :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        (∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
        Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t))))
          atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t)))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z =
        (∫ z in thricePuncturedSphereReal, (SmoothBundleForm.eval₂ ω (u z)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z) :=
  let ⟨y, hy, hEint, hid⟩ :=
    hω.exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact hH he isCompact_univ
      he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) J hJ hJc hA hC hfloer hHs
      fun q y hy _ ↦ hnd q y hy
  ⟨y, fun q ↦ ⟨(hy q).1, (hy q).2.2⟩, hEint, hid⟩

/-- Closed-manifold specialization of the topological energy lower bound. -/
theorem exists_neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation
    {M_H : Puncture → ℝ} (hMH : ∀ q t x, |H q t x| ≤ M_H q) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        (∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
        Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t))))
          atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t)))) ∧
      -∑ q, M_H q ≤
        (∫ z in thricePuncturedSphereReal, (SmoothBundleForm.eval₂ ω (u z)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t) :=
  let ⟨y, hy, hle⟩ :=
    hω.exists_neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation_of_isCompact hH he
      isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) J hJ hJc hA hC
      hfloer hHs (fun q y hy _ ↦ hnd q y hy) (fun q t x _ ↦ hMH q t x)
  ⟨y, fun q ↦ ⟨(hy q).1, (hy q).2.2⟩, hle⟩

end Periodic

section Contractible

variable
  (hnull : ∀ q, ∃ s > (0 : ℝ), ∃ g : C(AddCircle (1 : ℝ), M),
    g.Nullhomotopic ∧ ∀ t : ℝ, g t = u (endChart q (q.endSign * s, t)))
  (hnd : ∀ q,
    ∀ y ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
    IsNondegenerateFixedPt I
      (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0))

include hnull hnd

/-- Closed-manifold specialization of the contractible `pairOfPantsPerturbation H` identity. -/
theorem exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_nullhomotopic :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        (∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
        Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t))))
          atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t)))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z =
        (∫ z in thricePuncturedSphereReal, (SmoothBundleForm.eval₂ ω (u z)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z) :=
  let ⟨y, hy, hEint, hid⟩ :=
    exists_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact_of_nullhomotopic hω hH
      he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) J hJ hJc hA hC
      hfloer hHs hnull fun q y hy _ ↦ hnd q y hy
  ⟨y, fun q ↦ ⟨(hy q).1, (hy q).2.2⟩, hEint, hid⟩

/-- Closed-manifold specialization of the contractible topological energy lower bound. -/
theorem exists_neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation_of_nullhomotopic
    {M_H : Puncture → ℝ} (hMH : ∀ q t x, |H q t x| ≤ M_H q) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ contractiblePeriodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        (∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
        Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t))))
          atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t)))) ∧
      -∑ q, M_H q ≤
        (∫ z in thricePuncturedSphereReal, (SmoothBundleForm.eval₂ ω (u z)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t) :=
  let ⟨y, hy, hle⟩ :=
    exists_neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation_of_isCompact_of_nullhomotopic hω
      hH he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) J hJ hJc hA hC
      hfloer hHs hnull (fun q y hy _ ↦ hnd q y hy) (fun q t x _ ↦ hMH q t x)
  ⟨y, fun q ↦ ⟨(hy q).1, (hy q).2.2⟩, hle⟩

end Contractible

end Closed

end AsymptoticEnergy

end IsNondegenerate

end TauCeti.SmoothTwoForm
