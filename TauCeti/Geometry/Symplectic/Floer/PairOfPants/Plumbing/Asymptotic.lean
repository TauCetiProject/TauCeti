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

Plumbing the output end at `∞` of a pair of pants `S'`, with bounded period-one `C¹` Hamiltonians
`Ha`, into the input end `q ∈ {0, 1}` of a pair of pants `S`, with bounded period-one `C¹`
Hamiltonians `Hb` and `Hb q = Ha ∞`, along a neck of length `L > 4` gives the four-punctured
sphere `P = ℂ ∖ {0, 1, ψ(1)}` with the plumbed perturbation `K`
(`TauCeti.Floer.plumbedPerturbation`), where `ψ` is the plumbing map
`TauCeti.ThricePuncturedSphere.Puncture.plumbingMap q L`. Its four ends are the two inputs of `S'`,
the remaining input `q'` of `S` and the output of `S`.

Let `u` be a map which is `C¹` on `P`, with values in a finite-dimensional manifold `M` carrying a
nondegenerate two-form `ω`, such as a closed symplectic manifold. Suppose that its loops along the
four outer circles at height `R`, `ℓ'_r(t) = u(ψ(φ_r(R + i t)))` for the inputs `r` of `S'` and
`ℓ_r(t) = u(φ_r(±R + i t))` for the ends `r ≠ q` of `S`, converge pointwise to loops `x'_r` and
`x_r` as `R → ∞`, and that the energy density and the area density of `u` are integrable over
`P`. The truncations `Σ_R` of `P` (`TauCeti.ThricePuncturedSphere.Puncture.plumbedTruncation`)
exhaust it (`TauCeti.ThricePuncturedSphere.Puncture.iUnion_plumbedTruncation`), the curvature of
`K` is integrable over `P` (`SmoothTwoForm.integrableOn_hamiltonianCurvature_plumbedPerturbation`),
and by dominated convergence the integrals of the bounded Hamiltonians along the four outer loops
converge to their integrals along the limit loops. Letting `R → ∞` in the energy identity over
`Σ_R` (`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_plumbedTruncation`) gives

`∫_P E = ∫_P u^*ω + ∑_{r ≠ ∞} ∫₀¹ Ha_r(t, x'_r(t)) dt + ∑_{r ≠ q} ±∫₀¹ Hb_r(t, x_r(t)) dt
  - ∫_P R_K(u)`,

with the sign `+` on the input `q'` of `S` and `-` on its output
(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_plumbedPerturbation`). The energy
therefore differs from this topological part by at most `∑ r, Ba r + ∑ r, Bb r` for bounds
`|Ha r| ≤ Ba r` and `|Hb r| ≤ Bb r`, whatever the neck length `L > 4`, and for a solution of the
Floer equation with tamed almost complex structures the topological part is at least
`-(∑ r, Ba r + ∑ r, Bb r)`. The plumbed spheres are the domains of the associativity family
near its two broken-product ends, and these bounds hold over the whole domain. On a target which
is not symplectically aspherical the area term depends on the homotopy class of `u`; caps of the
four asymptotic orbits turn it into capped actions and the area of a sphere, which is not done
here.

## Main results

* `TauCeti.Floer.tendsto_setIntegral_plumbedTruncation`: integrals over the plumbed sphere are
  limits of integrals over its truncations `Σ_R`.
* `SmoothTwoForm.integrableOn_hamiltonianCurvature_plumbedPerturbation`: the curvature of the
  plumbed perturbation is integrable over the whole plumbed sphere.
* `SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_plumbedPerturbation`: the energy
  identity on the whole plumbed sphere, for a map with asymptotic loops at its four ends.
* `SmoothTwoForm.IsNondegenerate.abs_integral_floerEnergyDensity_plumbedPerturbation_sub_le`: the
  resulting energy bound, uniform in the neck length.
* `neg_sum_add_sum_le_integral_add_sum_add_sum_of_isComplexLinearMap_plumbedPerturbation`, in
  the namespace `SmoothTwoForm.IsNondegenerate`: the lower bound on the topological energy of a
  Floer solution.

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

namespace TauCeti.Floer

/-- Integrals over the plumbed four-punctured sphere `ℂ ∖ {0, 1, ψ(1)}`, in real coordinates, are
the limits of the integrals over its truncations `Σ_R`. -/
theorem tendsto_setIntegral_plumbedTruncation {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {q : Puncture} (hq : q ≠ inf) {L : ℝ} (hL : 0 < L) {f : ℝ × ℝ → G}
    (hf : IntegrableOn f {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    Tendsto (fun R : ℝ ↦ ∫ z in Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R, f z)
      atTop (𝓝 (∫ z in {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}, f z)) := by
  have hP : ⋃ R : ℝ, Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R =
      {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1} := by
    rw [← preimage_iUnion, iUnion_plumbedTruncation hq hL]
    rfl
  rw [← hP] at hf ⊢
  exact tendsto_setIntegral_of_monotone (measurableSet_preimage_plumbedTruncation q L)
    (fun _ _ h ↦ preimage_mono (plumbedTruncation_mono q L h)) hf

end TauCeti.Floer

namespace TauCeti.SmoothTwoForm

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M]
  {ω : SmoothTwoForm I M} {Ha Hb : Puncture → ℝ → M → ℝ} {q : Puncture} {L : ℝ}

/-- Along a map continuous on the plumbed four-punctured sphere, the curvature of the plumbed
perturbation of period-one `C¹` Hamiltonians on a manifold is integrable over the whole
four-punctured sphere, for every neck length `L > 4`. It vanishes off the truncation `Σ_{L/2}`
(`SmoothTwoForm.hamiltonianCurvature_plumbedPerturbation_eq_zero_of_notMem_plumbedTruncation`). -/
theorem integrableOn_hamiltonianCurvature_plumbedPerturbation (ω : SmoothTwoForm I M)
    (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {u : ℝ × ℝ → M}
    (hu : ContinuousOn u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z))
      {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1} :=
  (integrableOn_hamiltonianCurvature_plumbedTruncation ω hq hHa hHb hHas hHbs hab hL le_rfl
    hu).of_forall_sdiff_eq_zero (isOpen_plumbedSphere q L).measurableSet fun _ hz ↦
      ω.hamiltonianCurvature_plumbedPerturbation_eq_zero_of_notMem_plumbedTruncation hq hHa hHb
        hHas hHbs hab hL (by linarith) hz.1 hz.2 _

/-- Along a map continuous on the plumbed four-punctured sphere, the loops of `u` along circles
`c R` lying in the truncation `Σ_R` for every `R > 0` are continuous from some height on. -/
private theorem eventually_continuousOn_plumbedLoop {X : Type*} [TopologicalSpace X]
    (hq : q ≠ inf) (hL : 0 < L) {u : ℝ × ℝ → X}
    (hu : ContinuousOn u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1})
    {c : ℝ → ℝ → ℂ} (hc : ∀ R, Continuous (c R))
    (hcR : ∀ R > 0, ∀ t, c R t ∈ q.plumbedTruncation L R) :
    ∀ᶠ R in atTop, ContinuousOn (fun t ↦ u (Complex.equivRealProdCLM (c R t))) (uIoc 0 1) := by
  filter_upwards [eventually_gt_atTop 0] with R hR
  refine (hu.comp_continuous (Complex.equivRealProdCLM.continuous.comp (hc R))
    fun t ↦ ?_).continuousOn
  simpa only [mem_ofPred_eq, comp_apply, ContinuousLinearEquiv.symm_apply_apply] using
    plumbedTruncation_subset hq hL R (hcR R hR t)

variable [FiniteDimensional ℝ E]

/-- **The energy identity on the whole plumbed four-punctured sphere, for a manifold target.**
Plumb the output end of a pair of pants with bounded period-one `C¹` Hamiltonians `Ha` into the
input end `q ≠ ∞` of one with bounded period-one `C¹` Hamiltonians `Hb`, with `Hb q = Ha ∞`,
along a neck of length `L > 4`, for Hamiltonians on a finite-dimensional manifold with a
nondegenerate two-form. Let `u` be `C¹` on the four-punctured sphere `P = ℂ ∖ {0, 1, ψ(1)}`, in
real coordinates, with Floer energy density and symplectic area density integrable over `P`.
Suppose that its loops `t ↦ u(ψ(φ_r(R + i t)))` along the outer circles of the inputs `r ≠ ∞` of
the inserted pair of pants converge pointwise to loops `x'_r`, and its loops
`t ↦ u(φ_r(±R + i t))` along the outer circles of the ends `r ≠ q` of the receiving pair of pants
converge pointwise to loops `x_r`, as `R → ∞`. Then

`∫_P E = ∫_P u^*ω + ∑_{r ≠ ∞} ∫₀¹ Ha_r(t, x'_r(t)) dt + ∑_{r ≠ q} ±∫₀¹ Hb_r(t, x_r(t)) dt
  - ∫_P R_K(u)`,

with the sign `+` on the remaining input of the receiving pair of pants and `-` on its output,
the curvature term being integrable over `P`
(`SmoothTwoForm.integrableOn_hamiltonianCurvature_plumbedPerturbation`). -/
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
    {x' x : Puncture → ℝ → M}
    (hx' : ∀ r ≠ inf, ∀ t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (q.plumbingMap L (r.cylindricalEndLift (↑R + ↑t * Complex.I))))) atTop (𝓝 (x' r t)))
    (hx : ∀ r ≠ q, ∀ t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (r.cylindricalEndLift (↑(r.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (x r t)))
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
        ((∑ r ∈ Finset.univ.erase inf, ∫ t in (0 : ℝ)..1, Ha r t (x' r t)) +
          ∑ r ∈ Finset.univ.erase q, r.endSign * ∫ t in (0 : ℝ)..1, Hb r t (x r t)) -
        ∫ z in {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
          Complex.equivRealProdCLM.symm z ≠ 1) ∧
          Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}, ω.hamiltonianCurvature
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  have hL₀ : 0 < L := by linarith
  set P := {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
    Complex.equivRealProdCLM.symm z ≠ 1) ∧ Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}
  set area := fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
    (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
    (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)
  set curv := fun z ↦ ω.hamiltonianCurvature
    (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
    z (u z)
  -- Each term of the identity over `Σ_R` converges to the corresponding term over `P`.
  have hRHS : Tendsto (fun R : ℝ ↦
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R, area z) +
        ((∑ r ∈ Finset.univ.erase inf, ∫ t in (0 : ℝ)..1, Ha r t (u (Complex.equivRealProdCLM
            (q.plumbingMap L (r.cylindricalEndLift (↑R + ↑t * Complex.I)))))) +
          ∑ r ∈ Finset.univ.erase q, r.endSign * ∫ t in (0 : ℝ)..1, Hb r t (u
            (Complex.equivRealProdCLM
              (r.cylindricalEndLift (↑(r.endSign * R) + ↑t * Complex.I))))) -
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R, curv z) atTop
      (𝓝 ((∫ z in P, area z) +
        ((∑ r ∈ Finset.univ.erase inf, ∫ t in (0 : ℝ)..1, Ha r t (x' r t)) +
          ∑ r ∈ Finset.univ.erase q, r.endSign * ∫ t in (0 : ℝ)..1, Hb r t (x r t)) -
        ∫ z in P, curv z)) := by
    refine ((tendsto_setIntegral_plumbedTruncation hq hL₀ hA).add
      ((tendsto_finsetSum _ fun r hr ↦ ?_).add (tendsto_finsetSum _ fun r hr ↦ ?_))).sub
      (tendsto_setIntegral_plumbedTruncation hq hL₀
        (integrableOn_hamiltonianCurvature_plumbedPerturbation ω hq hHa hHb hHas hHbs hab hL
          hu.continuousOn))
    · have hr := Finset.ne_of_mem_erase hr
      exact tendsto_intervalIntegral_comp_of_tendsto_of_norm_le (hHas r).continuous
        (eventually_continuousOn_plumbedLoop hq hL₀ hu.continuousOn
          (fun R ↦ (q.contDiff_plumbingMap L (n := 0)).continuous.comp
            ((r.contDiff_cylindricalEndLift 0).continuous.comp (by fun_prop)))
          fun R hR t ↦ plumbingMap_cylindricalEndLift_mem_plumbedTruncation q hr hL₀.le hR t)
        (Eventually.of_forall fun R t _ ↦ (Real.norm_eq_abs _).trans_le (hBa r _ _))
        fun t _ ↦ hx' r hr t
    · have hr := Finset.ne_of_mem_erase hr
      exact (tendsto_intervalIntegral_comp_of_tendsto_of_norm_le (hHbs r).continuous
        (eventually_continuousOn_plumbedLoop hq hL₀ hu.continuousOn
          (fun R ↦ (r.contDiff_cylindricalEndLift 0).continuous.comp (by fun_prop))
          fun R hR t ↦ cylindricalEndLift_mem_plumbedTruncation hq hr hL₀.le hR t)
        (Eventually.of_forall fun R t _ ↦ (Real.norm_eq_abs _).trans_le (hBb r _ _))
        fun t _ ↦ hx r hr t).const_mul _
  -- From `R ≥ L/2` on, the identity over `Σ_R` holds.
  refine tendsto_nhds_unique (tendsto_setIntegral_plumbedTruncation hq hL₀ hE) (hRHS.congr' ?_)
  filter_upwards [eventually_ge_atTop (L / 2)] with R hR
  exact (hω.integral_floerEnergyDensity_plumbedTruncation hq hHa hHb hHas hHbs hab hL hR hu).symm

/-- **The energy bound on the whole plumbed four-punctured sphere, for a manifold target.** Under
the hypotheses of `SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_plumbedPerturbation`,
the Floer energy over the four-punctured sphere differs from its topological part, the symplectic
area plus the Hamiltonian terms at the four asymptotic loops, by at most
`∑ r, Ba r + ∑ r, Bb r`, uniformly in the neck length `L > 4`. -/
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
    {x' x : Puncture → ℝ → M}
    (hx' : ∀ r ≠ inf, ∀ t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (q.plumbingMap L (r.cylindricalEndLift (↑R + ↑t * Complex.I))))) atTop (𝓝 (x' r t)))
    (hx : ∀ r ≠ q, ∀ t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (r.cylindricalEndLift (↑(r.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (x r t)))
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
        ((∑ r ∈ Finset.univ.erase inf, ∫ t in (0 : ℝ)..1, Ha r t (x' r t)) +
          ∑ r ∈ Finset.univ.erase q, r.endSign * ∫ t in (0 : ℝ)..1, Hb r t (x r t))| ≤
      ∑ r, Ba r + ∑ r, Bb r := by
  have hsub (a b c : ℝ) : a + b - c - a - b = -c := by ring
  rw [hω.integral_floerEnergyDensity_plumbedPerturbation hq hHa hHb hHas hHbs hab hL hBa hBb hu hx'
    hx hE hA, hsub, abs_neg]
  exact ω.abs_setIntegral_hamiltonianCurvature_plumbedPerturbation_le hq hHa hHb hHas hHbs hab hL
    hBa hBb u _

namespace IsNondegenerate

/-- **The topological energy of a solution on the whole plumbed four-punctured sphere is bounded
below, for a manifold target.** Let `u` solve the Floer equation `(du - X_K)^{0,1} = 0` on the
four-punctured sphere for almost complex structures `J z` on the tangent spaces `T_{u(z)} M`
tamed by the two-form, under the hypotheses of
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_plumbedPerturbation`. Since its energy
is nonnegative, its symplectic area plus the Hamiltonian terms at the four asymptotic loops is at
least `-(∑ r, Ba r + ∑ r, Bb r)`, whatever the neck length `L > 4`. -/
theorem neg_sum_add_sum_le_integral_add_sum_add_sum_of_isComplexLinearMap_plumbedPerturbation
    (hω : ω.IsNondegenerate) (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1)
    (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {Ba Bb : Puncture → ℝ}
    (hBa : ∀ r t x, |Ha r t x| ≤ Ba r) (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1})
    {x' x : Puncture → ℝ → M}
    (hx' : ∀ r ≠ inf, ∀ t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (q.plumbingMap L (r.cylindricalEndLift (↑R + ↑t * Complex.I))))) atTop (𝓝 (x' r t)))
    (hx : ∀ r ≠ q, ∀ t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (r.cylindricalEndLift (↑(r.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (x r t)))
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
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}, (hω.symplecticFormAt (u z)).Tames (J z))
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
        ((∑ r ∈ Finset.univ.erase inf, ∫ t in (0 : ℝ)..1, Ha r t (x' r t)) +
          ∑ r ∈ Finset.univ.erase q, r.endSign * ∫ t in (0 : ℝ)..1, Hb r t (x r t)) := by
  have hpos := setIntegral_nonneg (μ := volume) (isOpen_plumbedSphere q L).measurableSet
    fun z hz ↦ floerEnergyDensity_nonneg hω (hJ z hz) (hfloer z hz)
  have h := (abs_le.1 (hω.abs_integral_floerEnergyDensity_plumbedPerturbation_sub_le hq hHa hHb
    hHas hHbs hab hL hBa hBb hu hx' hx hE hA)).2
  linarith

end IsNondegenerate

end TauCeti.SmoothTwoForm
