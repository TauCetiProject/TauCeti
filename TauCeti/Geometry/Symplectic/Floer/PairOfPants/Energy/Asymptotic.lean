/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Curvature
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Identity
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import TauCeti.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The energy identity on the whole pair of pants

Let `K` be the pair-of-pants perturbation `TauCeti.Floer.pairOfPantsPerturbation` built from
bounded period-one `C¹` Hamiltonians `H_q` on the three ends of `S = ℂ ∖ {0, 1}`, and let `u` be
a map which is `C¹` on `S`, with values in a finite-dimensional manifold `M` carrying a
nondegenerate two-form `ω`, such as a closed symplectic manifold. Suppose that the loops
`t ↦ u(φ_q(±R + i t))` along the circles of the end `q` converge pointwise to loops `x_q` as
`R → ∞`, and that the energy density and the area density of `u` are integrable over `S`. The
curvature is integrable over `S`
(`SmoothTwoForm.integrableOn_hamiltonianCurvature_pairOfPantsPerturbation`), and by dominated
convergence the integrals of the bounded Hamiltonians `H_q` along these loops converge to their
integrals along `x_q`. Since `K` is `H_q(t) dt` beyond the height `2` on each end, the energy
identity for data cylindrical on the ends
(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_of_eq_smul_endAngularForm`) gives

`∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, x_q(t)) dt - ∫_S R_K(u)`,

the identity `E = ∫ u^*ω + ∫_∂ K(u) - ∫ R_K(u)` with the boundary term evaluated at the asymptotic
orbits, with the sign `+` on the input ends `0`, `1` and `-` on the output end `∞`. Hence the
energy differs from this topological part by at most `B₀ + B₁ + B_∞` for bounds `|H_q| ≤ B_q`.
For a solution of the Floer equation with tamed almost complex structures the energy is
nonnegative, so the topological part is at least `-(B₀ + B₁ + B_∞)`. Once the area is expressed
through the actions of capped orbits and the product class, this becomes the lower bound on the
valuation of the output monomials of the pair-of-pants product.

The results are stated for a manifold target, and the vector-space statements are their
specializations to the constant form `SymplecticForm.constSmooth`.

## Main results

* `TauCeti.Floer.tendsto_setIntegral_truncation`,
  `TauCeti.Floer.tendsto_intervalIntegral_endLoop`,
  `TauCeti.Floer.tendsto_intervalIntegral_endChart_of_isCompact`: integrals over `S` are limits of
  integrals over its truncations, and integrals of a continuous Hamiltonian along the end loops
  converge to its integral along their pointwise limits when the Hamiltonian is bounded or the end
  loops eventually stay in a compact set.
* `SmoothTwoForm.IsNondegenerate.lintegral_floerEnergyDensity_le_of_eq_smul_endAngularForm`:
  whole-surface lower Lebesgue energy bound (and finiteness) from eventually bounded end-loop
  integrals and nonnegative energy density.
* `SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation`: the energy
  identity on the whole pair of pants, for a map with asymptotic loops at the ends; the
  vector-space case is `SymplecticForm.integral_floerEnergyDensity_pairOfPantsPerturbation`.
* `SmoothTwoForm.IsNondegenerate.abs_integral_floerEnergyDensity_pairOfPantsPerturbation_sub_le`,
  `SymplecticForm.abs_integral_floerEnergyDensity_pairOfPantsPerturbation_sub_le`: the resulting
  energy bound.
* `SmoothTwoForm.IsNondegenerate.neg_sum_le_integral_add_sum_of_isComplexLinearMap`,
  `SymplecticForm.neg_sum_le_integral_add_sum_of_isComplexLinearMap`: the lower bound on the
  topological energy of a Floer solution.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  curvature of Hamiltonian perturbations and the resulting energy bounds.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the energy estimate for the pair-of-pants product.
-/

public section

open Set Real Function MeasureTheory Filter Manifold TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Topology ENNReal

namespace TauCeti

namespace Floer

/-- Integrals over `S` are the limits of the integrals over its truncations. -/
theorem tendsto_setIntegral_truncation {f : ℝ × ℝ → ℝ}
    (hf : IntegrableOn f thricePuncturedSphereReal) :
    Tendsto (fun R : ℝ => ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, f z) atTop
      (𝓝 (∫ z in thricePuncturedSphereReal, f z)) := by
  have hS : ⋃ R : ℝ, Complex.equivRealProdCLM.symm ⁻¹' truncation R =
      thricePuncturedSphereReal := by
    rw [← preimage_iUnion, iUnion_truncation]
    rfl
  rw [← hS] at hf ⊢
  exact tendsto_setIntegral_of_monotone measurableSet_preimage_truncation
    (fun _ _ h => preimage_mono (truncation_mono h)) hf

/-- If the loops of `u` along the circles `±s = R` of the end `q` converge pointwise to a loop `x`
as `R → ∞`, then the integrals of a bounded continuous Hamiltonian along them converge to its
integral along `x`. -/
theorem tendsto_intervalIntegral_endLoop {M : Type*} [TopologicalSpace M]
    {H : Puncture → ℝ → M → ℝ} (hHc : ∀ q, Continuous (uncurry (H q))) {B : Puncture → ℝ}
    (hB : ∀ q t x, |H q t x| ≤ B q) {u : ℝ × ℝ → M}
    (hu : ContinuousOn u thricePuncturedSphereReal) {q : Puncture} {x : ℝ → M}
    (hx : ∀ t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (x t))) :
    Tendsto (fun R : ℝ ↦ ∫ t in (0 : ℝ)..1, H q t (u (Complex.equivRealProdCLM
        (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))))) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, H q t (x t))) := by
  refine tendsto_intervalIntegral_comp_of_tendsto_of_norm_le (hHc q) ?_
    (Eventually.of_forall fun R t _ ↦ (Real.norm_eq_abs _).trans_le (hB q _ _)) fun t _ ↦ hx t
  -- For `R > 0` the circle `±s = R` lies in `S`, where `u` is continuous.
  filter_upwards [eventually_gt_atTop 0] with R hR
  have hmem (t : ℝ) : Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)) ∈ thricePuncturedSphereReal := by
    rw [mem_thricePuncturedSphereReal_iff, ContinuousLinearEquiv.symm_apply_apply]
    refine cylindricalEndLift_ne_zero_and_ne_one q ?_
    rcases endSign_eq_one_or_eq_neg_one q with h | h <;> simp [h, hR]
  exact (hu.comp_continuous (Complex.equivRealProdCLM.continuous.comp
    ((q.contDiff_cylindricalEndLift 0).continuous.comp (by fun_prop))) hmem).continuousOn

/-- If the end loops `t ↦ u(φ_q(±s, t))` eventually stay in a compact set `B ⊆ M` on `[0, 1]` and
converge pointwise to `y` as `s → ∞`, then the integrals of a jointly continuous family `f` over
`0..1` along them converge to its integral along `y`. -/
theorem tendsto_intervalIntegral_endChart_of_isCompact {M E : Type*} [TopologicalSpace M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → M → E} (hfc : Continuous (uncurry f))
    {B : Set M} (hB : IsCompact B) {u : ℝ × ℝ → M} (hu : ContinuousOn u thricePuncturedSphereReal)
    {q : Puncture} (huB : ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1, u (endChart q (q.endSign * s, t)) ∈ B)
    {y : ℝ → M}
    (hy : ∀ t, Tendsto (fun s : ℝ ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t))) :
    Tendsto (fun s : ℝ ↦ ∫ t in (0 : ℝ)..1, f t (u (endChart q (q.endSign * s, t)))) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, f t (y t))) := by
  obtain ⟨s₀, hs₀⟩ := eventually_atTop.1 (huB.and (eventually_gt_atTop (0 : ℝ)))
  set v : ℝ → ℝ → M := fun s t ↦ u (endChart q (q.endSign * max s s₀, t))
  refine (tendsto_intervalIntegral_comp_of_tendsto hfc hB (y := v) (fun s ↦ ?_) (fun s t ht ↦
      (hs₀ _ (le_max_right s s₀)).1 t (by rwa [uIcc_of_le zero_le_one] at ht))
    fun t _ ↦ (hy t).congr' ((eventually_ge_atTop s₀).mono fun s hs ↦
      by simp only [v, max_eq_left hs])).congr'
    ((eventually_ge_atTop s₀).mono fun s hs ↦ by simp only [v, max_eq_left hs, uncurry_apply_pair])
  exact (hu.comp_continuous ((contDiff_endChart q 0).continuous.comp
    (continuous_const.prodMk continuous_id)) fun _ ↦ endChart_mem_thricePuncturedSphereReal
      (by simpa [← mul_assoc] using (hs₀ _ (le_max_right s s₀)).2)).continuousOn

end Floer

namespace SmoothTwoForm

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M]
  [FiniteDimensional ℝ E] {ω : SmoothTwoForm I M} {H : Puncture → ℝ → M → ℝ}

/-- **The energy identity on the pair of pants, for a manifold target.** Let `K` be the
pair-of-pants perturbation of bounded period-one `C¹` Hamiltonians `H_q` on a finite-dimensional
manifold with a nondegenerate two-form, with components `K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)`
in the global coordinate `z = s + i t` of `ℂ`. Let `u` be a map which is `C¹` on `S`, whose loops
`t ↦ u(φ_q(±R + i t))` along the circles of the end `q` converge pointwise to loops `x_q` as
`R → ∞`, and whose Floer energy density and symplectic area density are integrable over `S`. Then

`∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, x_q(t)) dt - ∫_S R_K(u)`,

with the sign `+` on the input ends `0`, `1` and `-` on the output end `∞`. The middle term is the
boundary integral `∫_∂ K(u)` at the asymptotic orbits, and the curvature term is integrable
(`SmoothTwoForm.integrableOn_hamiltonianCurvature_pairOfPantsPerturbation`). -/
theorem IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {x : Puncture → ℝ → M}
    (hx : ∀ q t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (x q t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      thricePuncturedSphereReal)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal) :
    ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      (∫ z in thricePuncturedSphereReal,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (x q t)) -
        ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  -- The complement of `S` is null, so integrals over `S` are integrals over the plane, and the
  -- datum is `H_q(t) dt` beyond the height `2` on each end.
  have hS : volume.restrict thricePuncturedSphereReal = volume :=
    Measure.restrict_eq_self_of_ae_mem ae_mem_thricePuncturedSphereReal
  have hR := integrableOn_hamiltonianCurvature_pairOfPantsPerturbation ω hH hHs hu.continuousOn
  rw [IntegrableOn, hS] at hE hA hR
  simp only [hS]
  refine hω.integral_floerEnergyDensity_of_eq_smul_endAngularForm
    (fun w x ↦ contMDiffAt_pairOfPantsPerturbation hH hHs w x)
    (fun _ _ x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm hw x) hH hu hE hA hR
    fun q ↦ ?_
  simpa only [endChart_apply, Complex.equivRealProdCLM_symm_apply] using
    tendsto_intervalIntegral_endLoop (fun q ↦ (hHs q).continuous) hB hu.continuousOn (hx q)

/-- **The energy bound on the pair of pants, for a manifold target.** Under the hypotheses of
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation`, the Floer
energy over `S` differs from its topological part, the symplectic area plus the Hamiltonian terms
at the asymptotic orbits, by at most `B₀ + B₁ + B_∞`. -/
theorem IsNondegenerate.abs_integral_floerEnergyDensity_pairOfPantsPerturbation_sub_le
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {x : Puncture → ℝ → M}
    (hx : ∀ q t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (x q t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      thricePuncturedSphereReal)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal) :
    |(∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) -
      (∫ z in thricePuncturedSphereReal,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) -
        ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (x q t)| ≤ ∑ q, B q := by
  have hsub (a b c : ℝ) : a + b - c - a - b = -c := by ring
  rw [hω.integral_floerEnergyDensity_pairOfPantsPerturbation hH hHs hB hu hx hE hA, hsub, abs_neg]
  exact abs_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_le ω hH hHs hB u _

/-- **The topological energy of a pair-of-pants solution is bounded below, for a manifold
target.** Let `u` solve the Floer equation `(du - X_K)^{0,1} = 0` on `S` for almost complex
structures `J z` on the tangent spaces `T_{u(z)} M` tamed by the two-form, under the hypotheses of
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation`. Since its
energy is nonnegative, its symplectic area plus the Hamiltonian terms at the asymptotic orbits is
at least `-(B₀ + B₁ + B_∞)`. -/
theorem IsNondegenerate.neg_sum_le_integral_add_sum_of_isComplexLinearMap
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {x : Puncture → ℝ → M}
    (hx : ∀ q t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (x q t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      thricePuncturedSphereReal)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap) :
    -∑ q, B q ≤
      (∫ z in thricePuncturedSphereReal,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (x q t) := by
  have hpos := setIntegral_nonneg (μ := volume) isOpen_thricePuncturedSphereReal.measurableSet
    fun z hz ↦ floerEnergyDensity_nonneg hω (hJ z hz) (hfloer z hz)
  have h := abs_le.1
    (hω.abs_integral_floerEnergyDensity_pairOfPantsPerturbation_sub_le hH hHs hB hu hx hE hA)
  linarith [h.2]

/-- **Energy bound from bounded end-loop integrals, for a manifold target.** Under the hypotheses of
`SmoothTwoForm.IsNondegenerate.lintegral_floerEnergyDensity_eq_of_eq_smul_endAngularForm`, if
`|∫₀¹ H_q(t, u(φ_q(±σ, t))) dt|` is eventually bounded by `M₀ q` as `σ → ∞` instead of converging,
the lower Lebesgue energy of `u` is bounded by `∫ u^*ω + ∑ q, M₀ q - ∫ R_K(u)` (hence finite). -/
theorem IsNondegenerate.lintegral_floerEnergyDensity_le_of_eq_smul_endAngularForm
    {K : ℂ → M → ℂ →L[ℝ] ℝ} {T₀ : ℝ} {u : ℝ × ℝ → M} (hω : ω.IsNondegenerate)
    (hK : ∀ (w : ThricePuncturedSphere) x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x))
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (he : ∀ z ∈ thricePuncturedSphereReal, 0 ≤ ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z)
    (hA : Integrable fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ))
    (hR : Integrable fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) {M₀ : Puncture → ℝ}
    (hM₀ : ∀ q, ∀ᶠ σ in atTop,
      |∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * σ, t)))| ≤ M₀ q) :
    ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≤
      ENNReal.ofReal ((∫ z, (SmoothBundleForm.eval₂ ω (u z)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) + ∑ q, M₀ q -
        ∫ z, ω.hamiltonianCurvature (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) := by
  obtain ⟨S₀, hS₀⟩ := eventually_atTop.1 (eventually_all.2 hM₀)
  obtain ⟨a, ha, helim⟩ :=
    hω.exists_tendsto_ofReal_floerEnergyDensity_of_eq_smul_endAngularForm hK hKH hH hu he hA hR
  set T : ℕ → ℝ := fun n ↦ n + max 2 T₀
  rw [← sub_add_eq_add_sub]
  refine le_of_tendsto_of_tendsto helim
    ((ENNReal.continuous_ofReal.tendsto _).comp (ha.add tendsto_const_nhds)) ?_
  filter_upwards [(tendsto_atTop_add_const_right _ _
    tendsto_natCast_atTop_atTop).eventually_ge_atTop S₀] with n hn
  refine ENNReal.ofReal_le_ofReal (add_le_add_right (Finset.sum_le_sum fun q _ ↦ ?_) (a n))
  refine (le_abs_self _).trans ?_
  rw [abs_mul, q.abs_endSign, one_mul, ← Real.norm_eq_abs]
  have hw : Integrable fun s ↦ deriv smoothTransition (q.endSign * s - T n) :=
    (smoothTransition.integrable_deriv.comp_sub_right (T n)).comp_mul_left' q.endSign_ne_zero
  refine (norm_integral_le_of_norm_le (hw.mul_const (M₀ q)) (.of_forall fun s ↦ ?_)).trans ?_
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg smoothTransition.monotone.deriv_nonneg]
    by_cases hs : T n ≤ q.endSign * s
    · refine mul_le_mul_of_nonneg_left ?_ smoothTransition.monotone.deriv_nonneg
      simpa only [endSign_mul_endSign_mul] using hS₀ (q.endSign * s) (hn.trans hs) q
    · rw [smoothTransition.deriv_of_neg (by linarith), zero_mul, zero_mul]
  · rw [integral_mul_const, smoothTransition.integral_deriv_mul_sub, q.abs_endSign, inv_one,
      one_mul]

end SmoothTwoForm

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ}

/-- **The energy identity on the pair of pants.** Let `K` be the pair-of-pants perturbation of
bounded period-one `C¹` Hamiltonians `H_q` on the three ends of `S = ℂ ∖ {0, 1}`, with components
`K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)` in the global coordinate `z = s + i t` of `ℂ`. Let `u`
be a map which is `C¹` on `S`, whose loops `t ↦ u(φ_q(±R + i t))` along the circles of the end
`q` converge pointwise to loops `x_q` as `R → ∞`, and whose Floer energy density and symplectic
area density are integrable over `S`. Then

`∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, x_q(t)) dt - ∫_S R_K(u)`,

with the sign `+` on the input ends `0`, `1` and `-` on the output end `∞`. The middle term is the
boundary integral `∫_∂ K(u)` at the asymptotic orbits, and the curvature term is integrable
(`integrableOn_hamiltonianCurvature_pairOfPantsPerturbation`). -/
theorem integral_floerEnergyDensity_pairOfPantsPerturbation (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 1 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1})
    {x : Puncture → ℝ → V}
    (hx : ∀ q t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (x q t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1})
    (hA : IntegrableOn
      (fun z ↦ ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag))
      {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1}) :
    ∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1}, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      (∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
          Complex.equivRealProdCLM.symm z ≠ 1},
          ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) +
        (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (x q t)) -
        ∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
          Complex.equivRealProdCLM.symm z ≠ 1}, ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  have hE' : ω.constSmooth.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u =
      ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u :=
    funext (floerEnergyDensity_constSmooth ω _ _ u)
  have hA' : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω.constSmooth (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V) u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V) u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal := by
    simp only [eval₂_constSmooth_mfderiv_stdComplexLine]
    exact hA
  have h := (isNondegenerate_constSmooth ω).integral_floerEnergyDensity_pairOfPantsPerturbation
    hH (fun q ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHs q).contMDiff) hB
    (contMDiffOn_iff_contDiffOn.mpr hu) hx (by rw [hE']; exact hE) hA'
  simp only [floerEnergyDensity_constSmooth, hamiltonianCurvature_constSmooth,
    eval₂_constSmooth_mfderiv_stdComplexLine] at h
  exact h

/-- **The energy bound on the pair of pants.** Under the hypotheses of
`SymplecticForm.integral_floerEnergyDensity_pairOfPantsPerturbation`, the Floer energy over `S`
differs from its topological part, the symplectic area plus the Hamiltonian terms at the
asymptotic orbits, by at most `B₀ + B₁ + B_∞`. -/
theorem abs_integral_floerEnergyDensity_pairOfPantsPerturbation_sub_le (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 1 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1})
    {x : Puncture → ℝ → V}
    (hx : ∀ q t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (x q t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1})
    (hA : IntegrableOn
      (fun z ↦ ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag))
      {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1}) :
    |(∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1}, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) -
      (∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
          Complex.equivRealProdCLM.symm z ≠ 1},
          ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) -
        ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (x q t)| ≤ ∑ q, B q := by
  have hsub (a b c : ℝ) : a + b - c - a - b = -c := by ring
  rw [integral_floerEnergyDensity_pairOfPantsPerturbation ω hH hHs hB hu hx hE hA, hsub, abs_neg]
  exact abs_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_le ω hH hHs hB u _

/-- **The topological energy of a pair-of-pants solution is bounded below.** Let `u` solve the
Floer equation `(du - X_K)^{0,1} = 0` on `S` for almost complex structures `J z` tamed by `ω`,
under the hypotheses of `SymplecticForm.integral_floerEnergyDensity_pairOfPantsPerturbation`.
Since its energy is nonnegative, its symplectic area plus the Hamiltonian terms at the asymptotic
orbits is at least `-(B₀ + B₁ + B_∞)`. -/
theorem neg_sum_le_integral_add_sum_of_isComplexLinearMap (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 1 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1})
    {x : Puncture → ℝ → V}
    (hx : ∀ q t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (x q t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1})
    (hA : IntegrableOn
      (fun z ↦ ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag))
      {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1})
    {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1}, ω.Tames (J z))
    (hfloer : ∀ z ∈ {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1},
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V)) :
    -∑ q, B q ≤
      (∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
          Complex.equivRealProdCLM.symm z ≠ 1},
          ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) +
        ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (x q t) := by
  have hpos := setIntegral_nonneg (μ := volume) (s := {z : ℝ × ℝ |
      Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1})
    isOpen_thricePuncturedSphereReal.measurableSet
    fun z hz ↦ ω.floerEnergyDensity_nonneg (hJ z hz) (hfloer z hz)
  have h := abs_le.1
    (abs_integral_floerEnergyDensity_pairOfPantsPerturbation_sub_le ω hH hHs hB hu hx hE hA)
  linarith [h.2]

end SymplecticForm

end TauCeti
