/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Exchange
import TauCeti.Geometry.Symplectic.Floer.Curvature.Continuity

/-!
# The energy of the input-exchange family from the limits of its end terms

Graded commutativity of the pair-of-pants product is proved with the input-exchange family
`K_c = TauCeti.Floer.exchangePerturbation H c`, `0 ≤ c ≤ 1`, of perturbation data on
`S = ℂ ∖ {0, 1}`, whose output end is the end at `∞` recentred at `c`. Let `u` be a map which is
`C¹` on `S`, with values in a finite-dimensional manifold `M` carrying a nondegenerate two-form
`ω`, such as a closed symplectic manifold, and solving the Floer equation `(du - X_{K_c})^{0,1} = 0`
on `S` for almost complex structures tamed by `ω`. Write

`b_q(R) = ∫₀¹ H_q(t, u(φ_q(R + i t))) dt`,  `b_∞(R) = ∫₀¹ H_∞(t, u(c + φ_∞(-R + i t))) dt`

for the Hamiltonian terms along the boundary circles of the input ends `q ∈ {0, 1}` and of the
recentred output end, and suppose that they converge to `h_q` as `R → ∞`, and that the symplectic
area density of `u` is integrable over `S`.

`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Exchange` computes the energy of `u` over
the truncations `T_R` of `S` with recentred output end, and over the whole of `S` under the extra
hypothesis that the energy density is integrable. This file removes that hypothesis. The
truncations exhaust `S`, so by monotone convergence the energy over `S` is the limit of the
energies over `T_R`, and the truncated identity gives

`E(u) = ∫_S u^*ω + h₀ + h₁ - h_∞ - ∫_S R_{K_c}(u)`

(`SmoothTwoForm.IsNondegenerate.lintegral_floerEnergyDensity_exchangePerturbation_eq`). For this
the curvature term must be integrable over `S`: it is continuous on `S`
(`TauCeti.SmoothTwoForm.IsNondegenerate.continuousOn_hamiltonianCurvature_comp`), and the integral
of its absolute value is at most `B₀ + B₁ + B_∞` when `|H_q| ≤ B_q`
(`TauCeti.SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_exchangePerturbation_le`). Hence the
energy is finite, the energy density is integrable over `S`
(`SmoothTwoForm.IsNondegenerate.integrableOn_floerEnergyDensity_exchangePerturbation`), and

`E(u) ≤ ∫_S u^*ω + h₀ + h₁ - h_∞ + B₀ + B₁ + B_∞`

uniformly in `c ∈ [0, 1]`
(`SmoothTwoForm.IsNondegenerate.lintegral_floerEnergyDensity_exchangePerturbation_le`). This is the
energy bound with which Gromov–Floer compactness applies to the solutions of the whole family. In
the other direction, the nonnegativity of the energy over the truncations gives the lower bound

`-(B₀ + B₁ + B_∞) ≤ ∫_S u^*ω + h₀ + h₁ - h_∞`

(`SmoothTwoForm.IsNondegenerate.neg_sum_le_integral_add_sum_of_tendsto_exchangePerturbation`), which
does not use the curvature term at all. Once the area is expressed through the actions of capped
orbits and the class of the solution, this is the lower bound on the valuation of the output
monomials of the commutativity homotopy on a closed symplectic manifold.

These are the manifold versions of the energy bounds
`TauCeti.SymplecticForm.lintegral_floerEnergyDensity_exchangePerturbation_eq`,
`TauCeti.SymplecticForm.lintegral_floerEnergyDensity_exchangePerturbation_le` and
`TauCeti.SymplecticForm.le_add_add_sum_of_tendsto_hamiltonianAction_exchangePerturbation` for a
symplectic vector space target, where the area and the Hamiltonian terms combine into actions.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the graded commutativity of the pair-of-pants product and its energy
  estimate.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  energy identity for Hamiltonian perturbations.
-/

public section

open Set Real Function MeasureTheory Filter TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Topology Manifold

namespace TauCeti

namespace Floer

/-- The truncations with recentred output end exhaust `S`, in real coordinates. -/
private theorem iUnion_preimage_exchangeTruncation (c : ℝ) :
    ⋃ R : ℝ, Complex.equivRealProdCLM.symm ⁻¹' exchangeTruncation c R =
      thricePuncturedSphereReal := by
  ext z
  simp only [← preimage_iUnion, iUnion_exchangeTruncation, mem_preimage, mem_ofPred_eq,
    mem_thricePuncturedSphereReal_iff]

/-- Integrals over `S` are the limits of the integrals over its truncations with output end
recentred at `c`. -/
theorem tendsto_setIntegral_exchangeTruncation (c : ℝ) {f : ℝ × ℝ → ℝ}
    (hf : IntegrableOn f thricePuncturedSphereReal) :
    Tendsto (fun R : ℝ ↦ ∫ z in Complex.equivRealProdCLM.symm ⁻¹' exchangeTruncation c R, f z)
      atTop (𝓝 (∫ z in thricePuncturedSphereReal, f z)) := by
  rw [← iUnion_preimage_exchangeTruncation c] at hf ⊢
  exact tendsto_setIntegral_of_monotone
    (fun R ↦ ((isClosed_exchangeTruncation c R).preimage
      Complex.equivRealProdCLM.symm.continuous).measurableSet)
    (fun _ _ h ↦ preimage_mono (exchangeTruncation_mono c h)) hf

/-- The Hamiltonian terms along the boundary circles of the truncations with output end recentred
at `c` converge to the signed sum of their limits on the three ends. -/
private theorem tendsto_exchangeBoundary {M : Type*} {H : Puncture → ℝ → M → ℝ} {c : ℝ}
    {u : ℝ × ℝ → M} {h : Puncture → ℝ}
    (hh : ∀ q ≠ inf, Tendsto (fun R : ℝ ↦ ∫ t in (0 : ℝ)..1, H q t (u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑R + ↑t * Complex.I))))) atTop (𝓝 (h q)))
    (hhinf : Tendsto (fun R : ℝ ↦ ∫ t in (0 : ℝ)..1, H inf t (u (Complex.equivRealProdCLM
      (↑c + inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I))))) atTop (𝓝 (h inf))) :
    Tendsto (fun R : ℝ ↦ (∫ t in (0 : ℝ)..1, H zero t (u (Complex.equivRealProdCLM
        (zero.cylindricalEndLift (↑R + ↑t * Complex.I))))) +
      (∫ t in (0 : ℝ)..1, H one t (u (Complex.equivRealProdCLM
        (one.cylindricalEndLift (↑R + ↑t * Complex.I))))) -
      ∫ t in (0 : ℝ)..1, H inf t (u (Complex.equivRealProdCLM
        (↑c + inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I))))) atTop
      (𝓝 (∑ q, q.endSign * h q)) := by
  have hsum : ∑ q, q.endSign * h q = h zero + h one - h inf := by
    simp only [Puncture.sum_univ, endSign_zero, endSign_one, endSign_inf, one_mul, neg_one_mul]
    ring
  rw [hsum]
  exact ((hh zero (by decide)).add (hh one (by decide))).sub hhinf

end Floer

namespace SmoothTwoForm

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]
  {H : Puncture → ℝ → M → ℝ} {c : ℝ}

/-- The components of the member `c` of the family in real coordinates are `C¹` on `S × M`. -/
private theorem contMDiffOn_exchangePerturbation_apply (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) (c : ℝ) (v : ℂ) :
    ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1
      (uncurry fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x v)
      (thricePuncturedSphereReal ×ˢ univ) := by
  rintro ⟨z, x⟩ ⟨hz, -⟩
  have hφ : ContMDiffAt (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℂ).prod I)) 1
      (fun p : (ℝ × ℝ) × M ↦ (c, (Complex.equivRealProdCLM.symm p.1, p.2))) (z, x) :=
    contMDiffAt_const.prodMk
      ((Complex.equivRealProdCLM.symm.contDiff.contMDiff.contMDiffAt.comp _ contMDiffAt_fst).prodMk
        contMDiffAt_snd)
  exact (((contMDiffAt_exchangePerturbation hH hHs c
    ⟨_, mem_thricePuncturedSphereReal_iff.1 hz⟩ x).comp (z, x) hφ).clm_apply
      contMDiffAt_const).contMDiffWithinAt

variable [IsManifold I ⊤ M]

/-- The integrated curvature of the member `c ∈ [0, 1]` of the family over `S` is at most
`B₀ + B₁ + B_∞` in absolute value, when `|H_q| ≤ B_q`. -/
private theorem abs_setIntegral_hamiltonianCurvature_exchangePerturbation_le
    (ω : SmoothTwoForm I M) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {B : Puncture → ℝ}
    (hB : ∀ q t x, |H q t x| ≤ B q) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) (u : ℝ × ℝ → M) :
    |∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
      (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
      z (u z)| ≤ ∑ q, B q := by
  have hB₀ (q : Puncture) : 0 ≤ B q := (abs_nonneg _).trans (hB q 0 (u 0))
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_lintegral_norm _).trans ?_
  calc _ ≤ (∑ q, ENNReal.ofReal (B q)).toReal := by
        refine ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun _ _ ↦ ENNReal.ofReal_ne_top)
          ((setLIntegral_le_lintegral _ _).trans ?_)
        simpa only [ofReal_norm] using
          lintegral_enorm_hamiltonianCurvature_exchangePerturbation_le ω hH hHs hB hc₀ hc₁ u
    _ = ∑ q, B q := by
        rw [ENNReal.toReal_sum fun _ _ ↦ ENNReal.ofReal_ne_top]
        exact Finset.sum_congr rfl fun q _ ↦ ENNReal.toReal_ofReal (hB₀ q)

variable [FiniteDimensional ℝ E] {ω : SmoothTwoForm I M}

/-- Along a map continuous on `S`, the curvature of the member `c ∈ [0, 1]` of the family is
integrable over `S`: it is continuous there, and the integral of its absolute value is bounded. -/
private theorem IsNondegenerate.integrableOn_hamiltonianCurvature_exchangePerturbation
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {B : Puncture → ℝ}
    (hB : ∀ q t x, |H q t x| ≤ B q) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {u : ℝ × ℝ → M}
    (hu : ContinuousOn u thricePuncturedSphereReal) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
      z (u z)) thricePuncturedSphereReal :=
  ⟨(hω.continuousOn_hamiltonianCurvature_comp isOpen_thricePuncturedSphereReal hu
      (contMDiffOn_exchangePerturbation_apply hH hHs c 1)
      (contMDiffOn_exchangePerturbation_apply hH hHs c Complex.I)).aestronglyMeasurable
      isOpen_thricePuncturedSphereReal.measurableSet,
    (setLIntegral_le_lintegral _ _).trans_lt
      ((lintegral_enorm_hamiltonianCurvature_exchangePerturbation_le ω hH hHs hB hc₀ hc₁ u).trans_lt
        (ENNReal.sum_lt_top.2 fun _ _ ↦ ENNReal.ofReal_lt_top))⟩

variable {B : Puncture → ℝ} {u : ℝ × ℝ → M} {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
  {h : Puncture → ℝ}

/-- **The energy along the input-exchange family, for a manifold target, from the limits of its
end terms.** Let `K_c` be the member `c ∈ [0, 1]` of the input-exchange family of bounded
period-one `C¹` Hamiltonians `H_q` on a finite-dimensional manifold with a nondegenerate two-form,
and let `u` be a map which is `C¹` on `S` and solves the Floer equation `(du - X_{K_c})^{0,1} = 0`
on `S` for almost complex structures `J z` on the tangent spaces `T_{u(z)} M` tamed by the
two-form. Suppose that its symplectic area density is integrable over `S`, and that the Hamiltonian
terms `∫₀¹ H_q(t, u(φ_q(R + i t))) dt` along the circles of the input ends `q ∈ {0, 1}` and
`∫₀¹ H_∞(t, u(c + φ_∞(-R + i t))) dt` along the circles of the recentred output end converge to
`h_q` as `R → ∞`. Then the energy of `u` over `S` is

`E(u) = ∫_S u^*ω + h₀ + h₁ - h_∞ - ∫_S R_{K_c}(u)`.

In particular the energy is finite. Neither the integrability of the energy density nor the
convergence of the end loops is assumed. -/
theorem IsNondegenerate.lintegral_floerEnergyDensity_exchangePerturbation_eq
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hB : ∀ q t x, |H q t x| ≤ B q) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (hJ : ∀ z ∈ thricePuncturedSphereReal, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hh : ∀ q ≠ inf, Tendsto (fun R : ℝ ↦ ∫ t in (0 : ℝ)..1, H q t (u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑R + ↑t * Complex.I))))) atTop (𝓝 (h q)))
    (hhinf : Tendsto (fun R : ℝ ↦ ∫ t in (0 : ℝ)..1, H inf t (u (Complex.equivRealProdCLM
      (↑c + inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I))))) atTop (𝓝 (h inf))) :
    ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I) u z) =
      ENNReal.ofReal ((∫ z in thricePuncturedSphereReal,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        ∑ q, q.endSign * h q -
        ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z)) := by
  set e : ℝ × ℝ → ℝ := ω.floerEnergyDensity
    (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I) u
  set T : ℝ → Set (ℝ × ℝ) := fun R ↦ Complex.equivRealProdCLM.symm ⁻¹' exchangeTruncation c R
  have hTS (R : ℝ) : T R ⊆ thricePuncturedSphereReal := fun z hz ↦ exchangeTruncation_subset c R hz
  have hTm (R : ℝ) : MeasurableSet (T R) :=
    ((isClosed_exchangeTruncation c R).preimage
      Complex.equivRealProdCLM.symm.continuous).measurableSet
  have hR := hω.integrableOn_hamiltonianCurvature_exchangePerturbation hH hHs hB hc₀ hc₁
    hu.continuousOn
  -- The energies over the truncations increase to the energy over `S`.
  have hlim := tendsto_measure_iUnion_atTop
    (μ := volume.withDensity fun z ↦ ENNReal.ofReal (e z)) (s := T)
    fun R R' hRR' ↦ preimage_mono (exchangeTruncation_mono c hRR')
  rw [iUnion_preimage_exchangeTruncation,
    withDensity_apply _ isOpen_thricePuncturedSphereReal.measurableSet] at hlim
  refine tendsto_nhds_unique hlim ((ENNReal.continuous_ofReal.tendsto _).comp
    ((((tendsto_setIntegral_exchangeTruncation c hA).add (tendsto_exchangeBoundary hh hhinf)).sub
      (tendsto_setIntegral_exchangeTruncation c hR))) |>.congr' ?_)
  -- On `T R`, `R ≥ 2`, the energy density is integrable and the truncated identity applies.
  filter_upwards [eventually_ge_atTop 2] with R hR₂
  have hEint : IntegrableOn e (T R) :=
    hω.integrableOn_floerEnergyDensity isOpen_thricePuncturedSphereReal hu
      (contMDiffOn_exchangePerturbation_apply hH hHs c 1)
      (contMDiffOn_exchangePerturbation_apply hH hHs c Complex.I)
      (Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2
        (isCompact_exchangeTruncation c R)) (hTS R) (hR.mono_set (hTS R))
  simp only [Function.comp_apply]
  rw [eq_comm, withDensity_apply _ (hTm R),
    ← ofReal_integral_eq_lintegral_ofReal hEint
    (ae_restrict_of_forall_mem (hTm R) fun z hz ↦
      floerEnergyDensity_nonneg hω (hJ z (hTS R hz)) (hfloer z (hTS R hz))),
    hω.integral_floerEnergyDensity_exchangePerturbation_exchangeTruncation hH hHs hc₀ hc₁ hu
      (by linarith), smoothTransition.one_of_one_le (by linarith), one_mul]

/-- **The energy bound along the input-exchange family, for a manifold target, from the limits of
its end terms.** Under the hypotheses of
`SmoothTwoForm.IsNondegenerate.lintegral_floerEnergyDensity_exchangePerturbation_eq`, the energy of
`u` over `S` is at most `∫_S u^*ω + h₀ + h₁ - h_∞ + B₀ + B₁ + B_∞`, uniformly in `c ∈ [0, 1]`. -/
theorem IsNondegenerate.lintegral_floerEnergyDensity_exchangePerturbation_le
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hB : ∀ q t x, |H q t x| ≤ B q) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (hJ : ∀ z ∈ thricePuncturedSphereReal, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hh : ∀ q ≠ inf, Tendsto (fun R : ℝ ↦ ∫ t in (0 : ℝ)..1, H q t (u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑R + ↑t * Complex.I))))) atTop (𝓝 (h q)))
    (hhinf : Tendsto (fun R : ℝ ↦ ∫ t in (0 : ℝ)..1, H inf t (u (Complex.equivRealProdCLM
      (↑c + inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I))))) atTop (𝓝 (h inf))) :
    ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≤
      ENNReal.ofReal ((∫ z in thricePuncturedSphereReal,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        ∑ q, q.endSign * h q + ∑ q, B q) := by
  rw [hω.lintegral_floerEnergyDensity_exchangePerturbation_eq hH hHs hB hc₀ hc₁ hu hJ hfloer hA hh
    hhinf]
  refine ENNReal.ofReal_le_ofReal ?_
  linarith [neg_abs_le (∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
      (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
      z (u z)), abs_setIntegral_hamiltonianCurvature_exchangePerturbation_le ω hH hHs hB hc₀ hc₁ u]

/-- **Finite energy along the input-exchange family, for a manifold target.** Under the
hypotheses of `SmoothTwoForm.IsNondegenerate.lintegral_floerEnergyDensity_exchangePerturbation_eq`,
the Floer energy density of `u` is integrable over `S`. So the energy identity
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_exchangePerturbation` in terms of the
asymptotic loops applies to `u` without an integrability hypothesis on its energy density. -/
theorem IsNondegenerate.integrableOn_floerEnergyDensity_exchangePerturbation
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hB : ∀ q t x, |H q t x| ≤ B q) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (hJ : ∀ z ∈ thricePuncturedSphereReal, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hh : ∀ q ≠ inf, Tendsto (fun R : ℝ ↦ ∫ t in (0 : ℝ)..1, H q t (u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑R + ↑t * Complex.I))))) atTop (𝓝 (h q)))
    (hhinf : Tendsto (fun R : ℝ ↦ ∫ t in (0 : ℝ)..1, H inf t (u (Complex.equivRealProdCLM
      (↑c + inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I))))) atTop (𝓝 (h inf))) :
    IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      thricePuncturedSphereReal := by
  set T : ℕ → Set (ℝ × ℝ) := fun n ↦ Complex.equivRealProdCLM.symm ⁻¹' exchangeTruncation c n
  have hTS (n : ℕ) : T n ⊆ thricePuncturedSphereReal := fun z hz ↦ exchangeTruncation_subset c _ hz
  -- The truncations of integer size also exhaust `S`.
  have hU : ⋃ n, T n = thricePuncturedSphereReal := by
    refine Subset.antisymm (iUnion_subset hTS) ?_
    rw [← iUnion_preimage_exchangeTruncation c]
    refine iUnion_subset fun R z hz ↦ ?_
    obtain ⟨n, hn⟩ := exists_nat_ge R
    exact mem_iUnion.2 ⟨n, preimage_mono (exchangeTruncation_mono c hn) hz⟩
  have hR := hω.integrableOn_hamiltonianCurvature_exchangePerturbation hH hHs hB hc₀ hc₁
    hu.continuousOn
  have hmeas : AEStronglyMeasurable (ω.floerEnergyDensity
      (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      (volume.restrict thricePuncturedSphereReal) := by
    rw [← hU, aestronglyMeasurable_iUnion_iff]
    exact fun n ↦ (hω.integrableOn_floerEnergyDensity isOpen_thricePuncturedSphereReal hu
      (contMDiffOn_exchangePerturbation_apply hH hHs c 1)
      (contMDiffOn_exchangePerturbation_apply hH hHs c Complex.I)
      (Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2
        (isCompact_exchangeTruncation c n)) (hTS n) (hR.mono_set (hTS n))).aestronglyMeasurable
  refine ⟨hmeas, (hasFiniteIntegral_iff_ofReal (ae_restrict_of_forall_mem
    isOpen_thricePuncturedSphereReal.measurableSet fun z hz ↦
      floerEnergyDensity_nonneg hω (hJ z hz) (hfloer z hz))).2 ?_⟩
  rw [hω.lintegral_floerEnergyDensity_exchangePerturbation_eq hH hHs hB hc₀ hc₁ hu hJ hfloer hA hh
    hhinf]
  exact ENNReal.ofReal_lt_top

/-- **The topological energy along the input-exchange family is bounded below, for a manifold
target, from the limits of its end terms.** Let `u` be `C¹` on `S` and solve the Floer equation
`(du - X_{K_c})^{0,1} = 0` on `S` for the member `c ∈ [0, 1]` of the family, for almost complex
structures `J z` on the tangent spaces `T_{u(z)} M` tamed by the two-form, with `|H_q| ≤ B_q`.
If its symplectic area density is integrable over `S` and the Hamiltonian terms along the circles
of the input ends and of the recentred output end converge to `h_q`, then

`-(B₀ + B₁ + B_∞) ≤ ∫_S u^*ω + h₀ + h₁ - h_∞`,

uniformly in `c`. Neither the integrability of the energy density nor the convergence of the end
loops is assumed. -/
theorem IsNondegenerate.neg_sum_le_integral_add_sum_of_tendsto_exchangePerturbation
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hB : ∀ q t x, |H q t x| ≤ B q) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (hJ : ∀ z ∈ thricePuncturedSphereReal, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hh : ∀ q ≠ inf, Tendsto (fun R : ℝ ↦ ∫ t in (0 : ℝ)..1, H q t (u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑R + ↑t * Complex.I))))) atTop (𝓝 (h q)))
    (hhinf : Tendsto (fun R : ℝ ↦ ∫ t in (0 : ℝ)..1, H inf t (u (Complex.equivRealProdCLM
      (↑c + inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I))))) atTop (𝓝 (h inf))) :
    -∑ q, B q ≤
      (∫ z in thricePuncturedSphereReal,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        ∑ q, q.endSign * h q := by
  have hTS (R : ℝ) : Complex.equivRealProdCLM.symm ⁻¹' exchangeTruncation c R ⊆
      thricePuncturedSphereReal := fun z hz ↦ exchangeTruncation_subset c R hz
  refine ge_of_tendsto ((tendsto_setIntegral_exchangeTruncation c hA).add
    (tendsto_exchangeBoundary hh hhinf)) ?_
  filter_upwards [eventually_ge_atTop 2] with R hR
  exact hω.neg_sum_le_integral_add_of_exchangePerturbation_exchangeTruncation hH hHs hB hc₀ hc₁ hu
    hR (fun z hz ↦ hJ z (hTS R hz)) (fun z hz ↦ hfloer z (hTS R hz))

end SmoothTwoForm

end TauCeti
