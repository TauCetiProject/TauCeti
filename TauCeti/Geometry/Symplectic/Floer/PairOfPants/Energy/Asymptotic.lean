/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Curvature
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Identity
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Integrable
import TauCeti.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set

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
valuation of the output monomials of the pair-of-pants product. By the one-sided curvature bound
`SmoothTwoForm.sum_mul_integral_le_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation`, the
constant `-(B₀ + B₁ + B_∞)` may be replaced by `∫₀¹ h_0 + ∫₀¹ h_1 - ∫₀¹ h_∞` for functions of time
with `h_q ≤ H_q` on the inputs and `H_∞ ≤ h_∞` on the output. Both sides of the resulting bound
change by `∑ q, ±∫₀¹ c_q` under a change of normalization `H_q ↦ H_q + c_q(t)`,
`h_q ↦ h_q + c_q(t)`.

The results are stated for a manifold target, and the vector-space statements are their
specializations to the constant form `SymplecticForm.constSmooth`.

## Main results

* `TauCeti.Floer.tendsto_setIntegral_truncation`,
  `TauCeti.Floer.tendsto_intervalIntegral_endLoop`,
  `TauCeti.Floer.tendsto_intervalIntegral_endChart_of_isCompact`: integrals over `S` are limits of
  integrals over its truncations, and integrals of a Hamiltonian along the end loops converge to
  its integral along their pointwise limits, either when the Hamiltonian is globally bounded or
  when the map takes values in a compact set.
* `SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact`
  gives the manifold pair-of-pants energy identity for maps into a compact set `B` with pointwise
  end limits, without assuming finite energy or global bounds on `H_q` a priori (using
  `TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Integrable` for automatic integrability).
* `SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation`: the energy
  identity on the whole pair of pants, for a map with asymptotic loops at the ends; the
  vector-space case is `SymplecticForm.integral_floerEnergyDensity_pairOfPantsPerturbation`.
* `SmoothTwoForm.IsNondegenerate.abs_integral_floerEnergyDensity_pairOfPantsPerturbation_sub_le`,
  `SymplecticForm.abs_integral_floerEnergyDensity_pairOfPantsPerturbation_sub_le`: the resulting
  energy bound.
* `SmoothTwoForm.IsNondegenerate.neg_sum_le_integral_add_sum_of_isComplexLinearMap`,
  `SmoothTwoForm.neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation_of_mapsTo`,
  `SymplecticForm.neg_sum_le_integral_add_sum_of_isComplexLinearMap`: the lower bound on the
  topological energy of a Floer solution (globally bounded, or on a target subset from the energy
  identity and energy nonnegativity).
* `SmoothTwoForm.IsNondegenerate.setIntegral_floerEnergyDensity_pairOfPantsPerturbation_le`: the
  energy of a Floer solution over any part of the pair of pants is at most its topological energy
  plus `B₀ + B₁ + B_∞`, the energy bound of compactness.
* `SmoothTwoForm.IsNondegenerate.sum_mul_integral_le_integral_add_sum_of_isComplexLinearMap`,
  `SymplecticForm.sum_mul_integral_le_integral_add_sum_of_isComplexLinearMap`: the lower bound
  with the one-sided constant `∫₀¹ h_0 + ∫₀¹ h_1 - ∫₀¹ h_∞` for functions of time `h_q ≤ H_q` on
  the inputs and `H_∞ ≤ h_∞` on the output, which is invariant under a change of normalization
  `H_q ↦ H_q + c_q(t)`, `h_q ↦ h_q + c_q(t)`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  curvature of Hamiltonian perturbations and the resulting energy bounds.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the energy estimate for the pair-of-pants product.
-/

public section

open Set Real Function MeasureTheory Filter Manifold TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Topology

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
  refine tendsto_intervalIntegral_comp_of_continuousOn (hHc q)
    (fun _ ↦ (Real.norm_eq_abs _).trans_le (hB q _ _)) hu
    (y := fun R t ↦ Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))
    (Eventually.of_forall fun R ↦ (Complex.equivRealProdCLM.continuous.comp
      ((q.contDiff_cylindricalEndLift 0).continuous.comp (by fun_prop))).continuousOn) ?_
    fun t _ ↦ hx t
  -- For `R > 0` the circle `±s = R` lies in `S`, where `u` is continuous.
  filter_upwards [eventually_gt_atTop 0] with R hR t _
  rw [mem_thricePuncturedSphereReal_iff, ContinuousLinearEquiv.symm_apply_apply]
  refine cylindricalEndLift_ne_zero_and_ne_one q ?_
  rcases endSign_eq_one_or_eq_neg_one q with h | h <;> simp [h, hR]

/-- If `u` maps `S` into a compact set `B`, `H_q` is continuous, and the end loops
`t ↦ u(φ_q(±s, t))` converge pointwise to `x` as `s → ∞`, then the integrals
`∫₀¹ H_q(t, u(φ_q(±s, t))) dt` converge to `∫₀¹ H_q(t, x(t)) dt`. Unlike
`TauCeti.Floer.tendsto_intervalIntegral_endLoop`, no global bound on `H_q` is needed. -/
theorem tendsto_intervalIntegral_endChart_of_isCompact {M : Type*} [TopologicalSpace M]
    {H : Puncture → ℝ → M → ℝ} {q : Puncture} (hHc : Continuous (uncurry (H q))) {B : Set M}
    (hB : IsCompact B) {u : ℝ × ℝ → M} (hu : ContinuousOn u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B) {x : ℝ → M}
    (hx : ∀ t, Tendsto (fun s : ℝ ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (x t))) :
    Tendsto (fun s : ℝ ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t))))
      atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (x t))) := by
  have hmem {s : ℝ} (hs : 0 < s) (t : ℝ) :
      endChart q (q.endSign * s, t) ∈ thricePuncturedSphereReal := by
    rw [endChart_eq_positiveEndChart]
    exact positiveEndChart_mem_thricePuncturedSphereReal hs
  have hlim : Tendsto (fun s : ℝ ↦ ∫ t in (0 : ℝ)..1,
      H q t (u (endChart q (q.endSign * max s 1, t)))) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, H q t (x t))) := by
    refine tendsto_intervalIntegral_comp_of_tendsto (Φ := uncurry (H q))
      (y := fun s t ↦ u (endChart q (q.endSign * max s 1, t))) hHc hB
      (fun s ↦ (hu.comp_continuous ((contDiff_endChart q 0).continuous.comp
        (continuous_const.prodMk continuous_id))
        (hmem (lt_max_of_lt_right zero_lt_one))).continuousOn)
      (fun s t _ ↦ huB _ (hmem (lt_max_of_lt_right zero_lt_one) t))
      fun t _ ↦ (hx t).congr' ((eventually_ge_atTop (1 : ℝ)).mono fun s hs ↦ by
        simp only [max_eq_left hs])
  exact hlim.congr' ((eventually_ge_atTop (1 : ℝ)).mono fun s hs ↦ by simp only [max_eq_left hs])

end Floer

namespace SmoothTwoForm

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M]
  [FiniteDimensional ℝ E] {ω : SmoothTwoForm I M} {H : Puncture → ℝ → M → ℝ}

/-- **The manifold pair-of-pants energy identity on a compact target set.** If `t ↦ u(φ_q(±s, t))`
converges pointwise to `y_q` as `s → ∞` on each end `q`, then
`∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt - ∫_S R_K(u)` without finite energy a priori. -/
theorem IsNondegenerate.integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact
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
      thricePuncturedSphereReal)
    {y : Puncture → ℝ → M}
    (hy : ∀ q t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) :
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
  have hS : volume.restrict thricePuncturedSphereReal = volume :=
    Measure.restrict_eq_self_of_ae_mem ae_mem_thricePuncturedSphereReal
  have hEint := hω.integrableOn_floerEnergyDensity_of_eq_smul_endAngularForm_of_isCompact
    hK hKH hH hHc hB hu huB he hA hR
  rw [IntegrableOn, hS] at hEint hA hR
  simp only [hS]
  exact hω.integral_floerEnergyDensity_of_eq_smul_endAngularForm hK hKH hH hu hEint hA hR
    fun q ↦ tendsto_intervalIntegral_endChart_of_isCompact (hHc q) hB hu.continuousOn huB (hy q)

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

omit [FiniteDimensional ℝ E] in
/-- **Topological energy lower bound from the energy identity on a target subset.** Let `H_q` be
period-one `C¹` Hamiltonians bounded by `|H_q(t, x)| ≤ B_q` on a subset `S₀ ⊆ M`, and let `u` map
`S` into `S₀` with nonnegative integrated Floer energy for `pairOfPantsPerturbation H`. If `u`
satisfies the pair-of-pants energy identity against loops `y_q`, then
`-(B₀ + B₁ + B_∞) ≤ ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt`. -/
theorem neg_sum_le_integral_add_sum_of_pairOfPantsPerturbation_of_mapsTo
    (ω : SmoothTwoForm I M) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {S₀ : Set M} {B : Puncture → ℝ} (hB : ∀ q t, ∀ x ∈ S₀, |H q t x| ≤ B q)
    {u : ℝ × ℝ → M} (hu : MapsTo u thricePuncturedSphereReal S₀)
    (hpos : 0 ≤ ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z)
    {y : Puncture → ℝ → M}
    (hid : ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      (∫ z in thricePuncturedSphereReal,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
        ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z)) :
    -∑ q, B q ≤
      (∫ z in thricePuncturedSphereReal,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t) := by
  have hcurv := abs_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_le_of_mapsTo ω hH hHs
    hB hu thricePuncturedSphereReal
  linarith [(abs_le.1 hcurv).1]

/-- **The energy of a Floer pair of pants over any part of the domain, for a manifold target.**
Under the hypotheses of
`SmoothTwoForm.IsNondegenerate.neg_sum_le_integral_add_sum_of_isComplexLinearMap`, the energy of
the solution over any part `Ω` of `S` is at most its topological energy plus `B₀ + B₁ + B_∞`:

`∫_Ω ρ(u) ≤ ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, x_q(t)) dt + ∑ q, B_q`.

The energy density is nonnegative, since the structures are tamed, so the energy over `Ω` is at
most the energy over `S`, which the energy identity bounds. This is the energy bound with which
Gromov–Floer compactness applies to the solutions on every part of the domain. -/
theorem IsNondegenerate.setIntegral_floerEnergyDensity_pairOfPantsPerturbation_le
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
          u z).toLinearMap)
    {Ω : Set (ℝ × ℝ)} (hΩ : Ω ⊆ thricePuncturedSphereReal) :
    ∫ z in Ω, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z ≤
      (∫ z in thricePuncturedSphereReal,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (x q t)) + ∑ q, B q := by
  have h := abs_le.1
    (hω.abs_integral_floerEnergyDensity_pairOfPantsPerturbation_sub_le hH hHs hB hu hx hE hA)
  refine (hω.setIntegral_floerEnergyDensity_mono_set hΩ
    isOpen_thricePuncturedSphereReal.measurableSet hE hJ hfloer).trans ?_
  linarith [h.2]

/-- **The one-sided lower bound on the topological energy of a pair-of-pants solution, for a
manifold target.** Under the hypotheses of
`SmoothTwoForm.IsNondegenerate.neg_sum_le_integral_add_sum_of_isComplexLinearMap`, let `h_q` be
functions of time, integrable over one period, with `h_q ≤ H_q` on the input ends and
`H_∞ ≤ h_∞` on the output end, that is `±h_q(t) ≤ ±H_q(t, x)`. Then

`∫₀¹ h_0 + ∫₀¹ h_1 - ∫₀¹ h_∞ ≤ ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, x_q(t)) dt`.

Unlike the constant `-(B₀ + B₁ + B_∞)`, the left side changes by the same amount
`∑ q, ±∫₀¹ c_q` as the right side under a change of normalization `H_q ↦ H_q + c_q(t)`,
`h_q ↦ h_q + c_q(t)`. -/
theorem IsNondegenerate.sum_mul_integral_le_integral_add_sum_of_isComplexLinearMap
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    {h : Puncture → ℝ → ℝ} (hh : ∀ q, IntervalIntegrable (h q) volume 0 1)
    (hhH : ∀ q t x, q.endSign * h q t ≤ q.endSign * H q t x) {u : ℝ × ℝ → M}
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
    ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, h q t ≤
      (∫ z in thricePuncturedSphereReal,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (x q t) := by
  have hpos := setIntegral_nonneg (μ := volume) isOpen_thricePuncturedSphereReal.measurableSet
    fun z hz ↦ floerEnergyDensity_nonneg hω (hJ z hz) (hfloer z hz)
  have hR := ω.sum_mul_integral_le_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation hH hHs
    hh hhH hu.continuousOn
  rw [hω.integral_floerEnergyDensity_pairOfPantsPerturbation hH hHs hB hu hx hE hA] at hpos
  linarith

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

/-- **The one-sided lower bound on the topological energy of a pair-of-pants solution.** Under the
hypotheses of `SymplecticForm.neg_sum_le_integral_add_sum_of_isComplexLinearMap`, let `h_q` be
functions of time, integrable over one period, with `h_q ≤ H_q` on the input ends and
`H_∞ ≤ h_∞` on the output end, that is `±h_q(t) ≤ ±H_q(t, x)`. Then

`∫₀¹ h_0 + ∫₀¹ h_1 - ∫₀¹ h_∞ ≤ ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, x_q(t)) dt`.

This is the vector-space case of
`SmoothTwoForm.IsNondegenerate.sum_mul_integral_le_integral_add_sum_of_isComplexLinearMap`. -/
theorem sum_mul_integral_le_integral_add_sum_of_isComplexLinearMap (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    {h : Puncture → ℝ → ℝ} (hh : ∀ q, IntervalIntegrable (h q) volume 0 1)
    (hhH : ∀ q t x, q.endSign * h q t ≤ q.endSign * H q t x) {u : ℝ × ℝ → V}
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
    ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, h q t ≤
      (∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
          Complex.equivRealProdCLM.symm z ≠ 1},
          ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) +
        ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (x q t) := by
  have hpos := setIntegral_nonneg (μ := volume) (s := {z : ℝ × ℝ |
      Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1})
    isOpen_thricePuncturedSphereReal.measurableSet
    fun z hz ↦ ω.floerEnergyDensity_nonneg (hJ z hz) (hfloer z hz)
  have hR := ω.sum_mul_integral_le_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation hH hHs
    hh hhH hu.continuousOn
  rw [ω.integral_floerEnergyDensity_pairOfPantsPerturbation hH hHs hB hu hx hE hA] at hpos
  linarith

end SymplecticForm

end TauCeti
