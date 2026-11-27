/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.EndLinearization.Chart
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.MovingEnds
import TauCeti.Analysis.Complex.ThricePuncturedSphere.MovingEnds
import TauCeti.Geometry.Symplectic.JHolomorphic.RealChart
import TauCeti.Topology.Instances.Real.TSupport

/-!
# The end estimates of the linearized Floer operator on spheres with moving input ends

The associativity of the pair-of-pants product is proved through a family of spheres with three
moving input ends and an output end at `∞`, carrying the Hamiltonian perturbations
`K = TauCeti.Floer.puncturedSpherePerturbation c a H Hout`. The counts along this family rest on
the Fredholm theory of the linearized Floer operator `D_u` of these data, on a finite-dimensional
symplectic vector space `(V, ω)`, and that theory starts from the estimates of `D_u` on the ends.
This file proves them, for any finite set of input ends whose discs `‖w - c i‖ < ‖a i‖ / 2` are
pairwise disjoint and lie in the disc `‖w‖ ≤ 2 exp (2π)`, with nonzero scales.

* **On an input end.** The input end `i` is read in the chart `z ↦ c i + a i φ₀(z)`, in real
  coordinates, where `φ₀` is the end lift of the input end at `0` of the pair of pants. Far out,
  for `s ≥ 2`, the datum is `H_i(t) dt` there, in the namespace `TauCeti.Floer`:
  `perturbationPullback_realChart_puncturedSpherePerturbation_of_two_le`. If the structures
  are `J_e(t)` far out on the end and `u` solves the Floer equation there, with loops converging
  to a nondegenerate orbit of `H_i`, then the `W^{1,2}` energy beyond `s = 2` in the chart of a
  section supported far out on the end is controlled by `∫ ‖D_u ξ‖²`
  (`exists_forall_setIntegral_comp_realChart_le_mul_integral_floerLinearization_of_movingEnds` in
  the namespace `TauCeti.SymplecticForm`).
* **On the output end.** The output end is read in the positive end chart `φ'_∞` of the pair of
  pants (`TauCeti.Floer.positiveEndChart`), in which far out the datum is `H'(t) dt` for the
  Hamiltonian `H'(t, x) = -Hout(-t, x)`
  (`TauCeti.Floer.perturbationPullback_positiveEndChart_inf_puncturedSpherePerturbation`), and
  the same estimate holds, in the namespace `TauCeti.SymplecticForm`:
  `exists_forall_setIntegral_comp_positiveEndChart_le_mul_integral_floerLinearization_of_movingEnds`

Both are instances of the end estimate in a holomorphic end chart,
`exists_forall_setIntegral_comp_le_mul_integral_floerLinearization_of_chart` in the namespace
`TauCeti.SymplecticForm`.

The same estimates hold for the formal adjoint `D_u^*` of `D_u` on covector fields `η`, whose
kernel is the cokernel of `D_u`. On each end the covector field is read in the chart as the
`(0, 1)`-form `η' = η (ψ ·) ∘ (a + b J)` (`TauCeti.Floer.covectorPullback`), and the `L²` norm of
`D_u^* η` carries the Jacobian of the chart as a weight: `4π² |w - c i|²` on the input end `i`
and `4π² |w|²` on the output end. If the structures are `C²` far out on the end and `u` is `C²`
and `J` compatible along `u` there, the energy of `η'` beyond `s = 2` is controlled by
`∫ |w - c i|² ‖D_u^* η‖²` on the input end `i`, by
`exists_forall_setIntegral_covectorPullback_le_mul_integral_floerLinearizationAdjoint_inputEnd`,
and by `∫ |w|² ‖D_u^* η‖²` on the output end, by
`exists_forall_setIntegral_covectorPullback_le_mul_integral_floerLinearizationAdjoint_outputEnd`,
both in the namespace `TauCeti.SymplecticForm`. Both are instances of the estimate of the adjoint
in a holomorphic end chart,
`exists_forall_setIntegral_covectorPullback_le_mul_integral_floerLinearizationAdjoint_of_chart`.
Only the end matters: `u` and `J` are assumed regular on the part `s > 2` of the end alone, so no
regularity at the other punctures is needed. The sections are compactly supported in the image of
the far part of the end; they vanish in the chart outside a band, because a continuous function of
the point, the distance to the center of an input end or the norm on the output end, reads in the
chart as a strictly monotone function of the longitudinal coordinate
(`HasCompactSupport.exists_forall_notMem_Ioo_comp_eq_zero`). The components of the datum are
`C²` off the centers (`TauCeti.Floer.contDiffAt_uncurry_puncturedSpherePerturbation`), so
`D_u ξ` is continuous.

The patching of the end estimates of `D_u` with the interior estimate into the semi-Fredholm
estimate on the whole sphere is
`exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_add_of_movingEnds`
in `TauCeti.Geometry.Symplectic.Floer.PairOfPants.MovingEnds.SemiFredholm`, and the corresponding
patching for the formal adjoint is
`exists_forall_sum_setIntegral_add_le_mul_integral_floerLinearizationAdjoint_add_of_movingEnds`
there.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the Fredholm theory of the pair-of-pants product and the associativity of
  the product through families of four-punctured spheres.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1,
  on the semi-Fredholm estimate on punctured Riemann surfaces with cylindrical ends.
-/

public section

open Filter Function Set MeasureTheory TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Topology NNReal Manifold Real
open TauCeti.Complex (realChart realChart_mk equivRealProdCLM_symm_realChart contDiff_realChart
  fderiv_realChart_apply fderiv_realChart_ne_zero)

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : Type*} [Fintype ι] {c a : ι → ℂ} {H : ι → ℝ → V → ℝ} {Hout : ℝ → V → ℝ}

/-- Let `ψ` be a chart of an end of a sphere with moving input ends that avoids the centers of the
input ends beyond the height `r`, where `u` and `J` along `u` are `C¹`. Then the linearized
operator of the datum `TauCeti.Floer.puncturedSpherePerturbation c a H Hout`, in the direction of
a `C²` section with compact support in `ψ ((r, ∞) × ℝ)`, has integrable square norm. -/
private theorem integrable_norm_floerLinearization_sq_puncturedSpherePerturbation
    (ω : SymplecticForm V) (hH : ∀ i, Periodic (H i) 1) (hHs : ∀ i, ContDiff ℝ 2 (uncurry (H i)))
    (hHout : Periodic Hout 1) (hHouts : ContDiff ℝ 2 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    {ψ : ℝ × ℝ → ℝ × ℝ} {r : ℝ}
    (hψ : ∀ ζ : ℝ × ℝ, r < ζ.1 → ∀ j, Complex.equivRealProdCLM.symm (ψ ζ) ≠ c j)
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {u : ℝ × ℝ → V}
    (hJ : ∀ ζ : ℝ × ℝ, r < ζ.1 → ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (ψ ζ, u (ψ ζ)))
    (hu : ∀ ζ : ℝ × ℝ, r < ζ.1 → ContDiffAt ℝ 1 u (ψ ζ)) {ξ : ℝ × ℝ → V}
    (hξ : ContDiff ℝ 2 ξ) (hξc : HasCompactSupport ξ) (hξU : tsupport ξ ⊆ ψ '' (Ioi r ×ˢ univ)) :
    Integrable fun z ↦ ‖ω.floerLinearization
      (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
        Complex.I) u ξ z‖ ^ 2 := by
  refine ω.integrable_norm_floerLinearization_sq
    (ω.continuous_floerLinearization_of_tsupport_subset ?_ ?_ ?_ ?_ (hξ.of_le one_le_two) hξU) hξc
  · rintro _ ⟨ζ, hζ, rfl⟩
    exact hJ ζ hζ.1
  · rintro _ ⟨ζ, hζ, rfl⟩
    exact contDiffAt_uncurry_puncturedSpherePerturbation hH hHs hHout hHouts ha (hψ ζ hζ.1) _ 1
  · rintro _ ⟨ζ, hζ, rfl⟩
    exact contDiffAt_uncurry_puncturedSpherePerturbation hH hHs hHout hHouts ha (hψ ζ hζ.1) _
      Complex.I
  · rintro _ ⟨ζ, hζ, rfl⟩
    exact hu ζ hζ.1

/-- A function with compact support in the image of the part `s > R` of the input end with center
`c₀` and scale `a₀ ≠ 0` vanishes in the chart `realChart (z ↦ c₀ + a₀ φ₀(z))` of the end outside
a band `(R, b) × ℝ`: the distance to the center reads in the chart as `‖a₀‖ exp (-2πs) / 2`, a
strictly decreasing function of `s` tending to `0`. -/
private theorem exists_forall_notMem_Ioo_realChart_eq_zero {F : Type*} [Zero F] {c₀ a₀ : ℂ}
    (ha₀ : a₀ ≠ 0) {f : ℝ × ℝ → F} (hf : HasCompactSupport f) {R : ℝ}
    (hfR : tsupport f ⊆
      realChart (fun z ↦ c₀ + a₀ * zero.cylindricalEndLift z) '' (Ioi R ×ˢ univ)) :
    ∃ b, ∀ s t, s ∉ Ioo R b →
      f (realChart (fun z ↦ c₀ + a₀ * zero.cylindricalEndLift z) (s, t)) = 0 := by
  have hdist (s t : ℝ) : ‖Complex.equivRealProdCLM.symm
      (realChart (fun z ↦ c₀ + a₀ * zero.cylindricalEndLift z) (s, t)) - c₀‖ =
        ‖a₀‖ * Real.exp (-(2 * π * s)) / 2 := by
    rw [equivRealProdCLM_symm_realChart, norm_add_mul_cylindricalEndLift_sub]
    simp
  have hapos := norm_pos_iff.2 ha₀
  have hmono : StrictMono fun s ↦ -(‖a₀‖ * Real.exp (-(2 * π * s)) / 2) := fun s s' hss' ↦ by
    have := Real.exp_lt_exp.2 (by nlinarith [Real.pi_pos] : -(2 * π * s') < -(2 * π * s))
    dsimp only
    nlinarith
  have hlim : Tendsto (fun s : ℝ ↦ ‖a₀‖ * Real.exp (-(2 * π * s)) / 2) atTop (𝓝 0) := by
    simpa using ((Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop Real.two_pi_pos)).const_mul ‖a₀‖).div_const 2
  -- The distance to the center is positive on the support, so it exceeds some value along the end.
  refine HasCompactSupport.exists_forall_notMem_Ioo_comp_eq_zero
    (g := fun z ↦ -‖Complex.equivRealProdCLM.symm z - c₀‖) (by fun_prop) hmono
    (fun s t ↦ by rw [hdist]) hf hfR fun z hz ↦ ?_
  obtain ⟨⟨s', t'⟩, -, rfl⟩ := hfR hz
  have hd : 0 < ‖Complex.equivRealProdCLM.symm
      (realChart (fun z ↦ c₀ + a₀ * zero.cylindricalEndLift z) (s', t')) - c₀‖ := by
    rw [hdist]
    positivity
  obtain ⟨s, hs⟩ := (hlim.eventually (gt_mem_nhds hd)).exists
  exact ⟨s, neg_lt_neg hs⟩

/-- A function with compact support in the image of the part `s > R` of the output end vanishes in
the positive end chart `φ'_∞` outside a band `(R, b) × ℝ`: the norm reads in the chart as
`2 exp (2πs)`, a strictly increasing function of `s` tending to `∞`. -/
private theorem exists_forall_notMem_Ioo_positiveEndChart_inf_eq_zero {F : Type*} [Zero F]
    {f : ℝ × ℝ → F} (hf : HasCompactSupport f) {R : ℝ}
    (hfR : tsupport f ⊆ positiveEndChart inf '' (Ioi R ×ˢ univ)) :
    ∃ b, ∀ s t, s ∉ Ioo R b → f (positiveEndChart inf (s, t)) = 0 := by
  have hmono : StrictMono fun s ↦ 2 * Real.exp (2 * π * s) := fun s s' hss' ↦ by
    have := Real.exp_lt_exp.2 (by nlinarith [Real.pi_pos] : 2 * π * s < 2 * π * s')
    dsimp only
    linarith
  have hlim : Tendsto (fun s : ℝ ↦ 2 * Real.exp (2 * π * s)) atTop atTop :=
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop Real.two_pi_pos)).const_mul_atTop
      two_pos
  exact HasCompactSupport.exists_forall_notMem_Ioo_comp_eq_zero
    (g := fun z ↦ ‖Complex.equivRealProdCLM.symm z‖) (by fun_prop) hmono
    norm_equivRealProdCLM_symm_positiveEndChart_inf hf hfR
    fun z _ ↦ (hlim.eventually_gt_atTop _).exists

/-- **The end estimate on an input end of a sphere with moving input ends.** Let the discs
`‖w - c j‖ < ‖a j‖ / 2` be pairwise disjoint and lie in the disc `‖w‖ ≤ 2 exp (2π)`, with nonzero
scales, and let the Hamiltonians be jointly `C²` of period one. Read the input end `i` in the chart
`ψ = realChart (z ↦ c i + a i φ₀(z))`. Let `x` be an orbit of `H_i` starting at a nondegenerate
fixed point of its time-one map, let `J_e(t)` be a `C¹` family of almost complex structures
compatible along `x`, and let `J` be `J_e(t)` beyond `s = 2` in the chart. Let `u` and `J` along `u`
be `C¹` and `u` solve the Floer equation of the datum
`TauCeti.Floer.puncturedSpherePerturbation c a H Hout` beyond `s = 2`, and let the loops of `u ∘ ψ`
converge uniformly to `x` while the slice defect `∂t (u ∘ ψ) - X_{H_i}` tends uniformly to zero.
Then there are `C` and `R > 2` such that every `C²` section `ξ` with compact support in the image
`ψ ((R, ∞) × ℝ)` satisfies

`∫_{(2, ∞) × [0, 1]} (‖∂s (ξ ∘ ψ)‖² + ‖∂t (ξ ∘ ψ)‖² + ‖ξ ∘ ψ‖²) ≤ C ∫ ‖D_u ξ‖²`

for the linearized Floer operator `D_u` of these data. -/
theorem
    exists_forall_setIntegral_comp_realChart_le_mul_integral_floerLinearization_of_movingEnds
    (ω : SymplecticForm V) (hH : ∀ i, Periodic (H i) 1) (hHs : ∀ i, ContDiff ℝ 2 (uncurry (H i)))
    (hHout : Periodic Hout 1) (hHouts : ContDiff ℝ 2 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j ↦ ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) (i : ι) {L : ℝ≥0}
    (hX : LipschitzWith L (ω.timeDependentHamiltonianSuspension (H i))) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H i t) (x t)) t)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow (H i) hX 0 1) (x 0))
    {Je : ℝ → V → AlmostComplexStructure V}
    (hJe : ContDiff ℝ 1 fun p : ℝ × V ↦ (Je p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ t, ω.Compatible (Je t (x t))) {J : ℝ × ℝ → V → AlmostComplexStructure V}
    (hJeq : ∀ ζ : ℝ × ℝ, 2 < ζ.1 →
      J (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ) = Je ζ.2)
    {u : ℝ × ℝ → V}
    (hJ : ∀ ζ : ℝ × ℝ, 2 < ζ.1 → ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
      (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ,
        u (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ)))
    (hu : ∀ ζ : ℝ × ℝ, 2 < ζ.1 →
      ContDiffAt ℝ 1 u (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ))
    (hF : ∀ ζ : ℝ × ℝ, 2 < ζ.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ)
        (u (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ)))
      (ω.perturbedFDeriv
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u
        (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ) : ℝ × ℝ →ₗ[ℝ] V))
    (hux : TendstoUniformlyOn
      (fun s t ↦ u (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) (s, t))) x atTop
      (Icc 0 1))
    (hδ : TendstoUniformlyOn (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H i t))
      (u ∘ realChart fun z ↦ c i + a i * zero.cylindricalEndLift z) (s, t)) 0 atTop
      (Icc 0 1)) :
    ∃ C R : ℝ, 2 < R ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) '' (Ioi R ×ˢ univ) →
      ∫ ζ in Ioi 2 ×ˢ Icc (0 : ℝ) 1,
          sobolevDensity (ξ ∘ realChart fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ ≤
        C * ∫ z, ‖ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
            Complex.I) u ξ z‖ ^ 2 := by
  set ψ := realChart fun z ↦ c i + a i * zero.cylindricalEndLift z with hψ
  have hpb (ζ : ℝ × ℝ) (hζ : 2 < ζ.1) :=
    Floer.perturbationPullback_realChart_puncturedSpherePerturbation_of_two_le (Hout := Hout) hH ha
      hsep hout i hζ.le
  -- Beyond `s = 0` the chart avoids the centers.
  have hψne (ζ : ℝ × ℝ) (hζ : 0 < ζ.1) (j : ι) : Complex.equivRealProdCLM.symm (ψ ζ) ≠ c j := by
    rw [hψ, equivRealProdCLM_symm_realChart]
    exact add_mul_cylindricalEndLift_ne hsep (ha i) (by simpa using hζ) j
  obtain ⟨C, R, hR, hest⟩ :=
    ω.exists_forall_setIntegral_comp_le_mul_integral_floerLinearization_of_chart (R₁ := 2) hX
      (hHs i) hx hnd hJe hJex (fun ζ _ ↦ (contDiff_realChart (by fun_prop)).contDiffAt)
      (fun ζ _ ↦ isComplexLinearMap_fderiv_realChart (hasDerivAt_add_mul_cylindricalEndLift _ _ _))
      (fun ζ _ ↦ fderiv_realChart_ne_zero (hasDerivAt_add_mul_cylindricalEndLift _ _ _)
        (mul_ne_zero (ha i) (zero.deriv_cylindricalEndLift_ne_zero _)))
      (realChart_add_mul_cylindricalEndLift_add_one (c i) (a i))
      ((injOn_realChart_add_mul_cylindricalEndLift (ha i) (S := Ioi 2) (t₀ := 0)).mono
        (prod_mono subset_rfl (by rw [zero_add]; exact Ioo_subset_Ico_self)))
      hJeq (fun ζ hζ ↦ by rw [hpb ζ hζ]; funext y; simp)
      (fun ζ hζ ↦ by rw [hpb ζ hζ]; funext y; simp) hu hF hux hδ
  refine ⟨C, R, hR, fun ξ hξ hξc hξR ↦ ?_⟩
  obtain ⟨b, hb⟩ := exists_forall_notMem_Ioo_realChart_eq_zero (ha i) hξc hξR
  exact hest hξ hb (ω.integrable_norm_floerLinearization_sq_puncturedSpherePerturbation hH hHs
    hHout hHouts ha (fun ζ hζ ↦ hψne ζ (by linarith)) hJ hu hξ hξc
    (hξR.trans (image_mono (prod_mono (Ioi_subset_Ioi hR.le) subset_rfl))))

/-- **The end estimate on the output end of a sphere with moving input ends.** Let the discs
`‖w - c j‖ < ‖a j‖ / 2` lie in the disc `‖w‖ ≤ 2 exp (2π)`, and let the Hamiltonians be jointly
`C²` of period one. Read the output end in the positive end chart `φ'_∞` of the pair of pants,
where far out the datum `TauCeti.Floer.puncturedSpherePerturbation c a H Hout` is `H'(t) dt` for
`H'(t, y) = -Hout(-t, y)`. Let `x` be an orbit of `H'` starting at a nondegenerate fixed point of
its time-one map, let `J_e(t)` be a `C¹` family of almost complex structures compatible along `x`,
and let `J` be `J_e(t)` beyond `s = 2` in the chart. Let `u` and `J` along `u` be `C¹` and `u` solve
the Floer equation beyond `s = 2`, and let the loops of `u ∘ φ'_∞` converge uniformly to `x` while
the slice defect `∂t (u ∘ φ'_∞) - X_{H'}` tends uniformly to zero. Then there are `C` and `R > 2`
such that every `C²` section `ξ` with compact support in the image `φ'_∞ ((R, ∞) × ℝ)` satisfies

`∫_{(2, ∞) × [0, 1]} (‖∂s (ξ ∘ φ'_∞)‖² + ‖∂t (ξ ∘ φ'_∞)‖² + ‖ξ ∘ φ'_∞‖²) ≤ C ∫ ‖D_u ξ‖²`

for the linearized Floer operator `D_u` of these data. -/
theorem
    exists_forall_setIntegral_comp_positiveEndChart_le_mul_integral_floerLinearization_of_movingEnds
    (ω : SymplecticForm V) (hH : ∀ i, Periodic (H i) 1) (hHs : ∀ i, ContDiff ℝ 2 (uncurry (H i)))
    (hHout : Periodic Hout 1) (hHouts : ContDiff ℝ 2 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {L : ℝ≥0}
    (hX : LipschitzWith L (ω.timeDependentHamiltonianSuspension fun t y ↦ -Hout (-t) y))
    {x : ℝ → V} (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (fun y ↦ -Hout (-t) y) (x t)) t)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (fun t y ↦ -Hout (-t) y) hX 0 1) (x 0))
    {Je : ℝ → V → AlmostComplexStructure V}
    (hJe : ContDiff ℝ 1 fun p : ℝ × V ↦ (Je p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ t, ω.Compatible (Je t (x t))) {J : ℝ × ℝ → V → AlmostComplexStructure V}
    (hJeq : ∀ ζ : ℝ × ℝ, 2 < ζ.1 → J (positiveEndChart inf ζ) = Je ζ.2) {u : ℝ × ℝ → V}
    (hJ : ∀ ζ : ℝ × ℝ, 2 < ζ.1 → ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
      (positiveEndChart inf ζ, u (positiveEndChart inf ζ)))
    (hu : ∀ ζ : ℝ × ℝ, 2 < ζ.1 → ContDiffAt ℝ 1 u (positiveEndChart inf ζ))
    (hF : ∀ ζ : ℝ × ℝ, 2 < ζ.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (positiveEndChart inf ζ) (u (positiveEndChart inf ζ)))
      (ω.perturbedFDeriv
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u (positiveEndChart inf ζ) : ℝ × ℝ →ₗ[ℝ] V))
    (hux : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart inf (s, t))) x atTop (Icc 0 1))
    (hδ : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField fun y ↦ -Hout (-t) y) (u ∘ positiveEndChart inf) (s, t))
      0 atTop (Icc 0 1)) :
    ∃ C R : ℝ, 2 < R ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ positiveEndChart inf '' (Ioi R ×ˢ univ) →
      ∫ ζ in Ioi 2 ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart inf) ζ ≤
        C * ∫ z, ‖ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
            Complex.I) u ξ z‖ ^ 2 := by
  obtain ⟨C, R, hR, hest⟩ :=
    ω.exists_forall_setIntegral_comp_le_mul_integral_floerLinearization_of_chart (R₁ := 2) hX
      ((hHouts.comp (contDiff_fst.neg.prodMk contDiff_snd)).neg) hx hnd hJe hJex
      (fun ζ _ ↦ (contDiff_positiveEndChart inf 2).contDiffAt)
      (fun ζ _ ↦ isComplexLinearMap_fderiv_positiveEndChart inf ζ)
      (fun ζ _ ↦ fderiv_positiveEndChart_ne_zero inf ζ) (positiveEndChart_add_one inf)
      ((injOn_positiveEndChart inf 0).mono
        (prod_mono (subset_univ _) (by rw [zero_add]; exact Ioo_subset_Ico_self)))
      hJeq
      (fun ζ hζ ↦ funext fun y ↦ by
        rw [perturbationPullback_positiveEndChart_inf_puncturedSpherePerturbation hHout hout hζ.le]
        simp)
      (fun ζ hζ ↦ funext fun y ↦ by
        rw [perturbationPullback_positiveEndChart_inf_puncturedSpherePerturbation hHout hout hζ.le]
        simp) hu hF hux hδ
  refine ⟨C, R, hR, fun ξ hξ hξc hξR ↦ ?_⟩
  obtain ⟨b, hb⟩ := exists_forall_notMem_Ioo_positiveEndChart_inf_eq_zero hξc hξR
  exact hest hξ hb (ω.integrable_norm_floerLinearization_sq_puncturedSpherePerturbation hH hHs
    hHout hHouts ha (fun ζ hζ ↦ equivRealProdCLM_symm_positiveEndChart_inf_ne hout (by linarith))
    hJ hu hξ hξc (hξR.trans (image_mono (prod_mono (Ioi_subset_Ioi hR.le) subset_rfl))))

/-! ### The formal adjoint -/

/-- Let `ψ` be a chart of an end of a sphere with moving input ends that avoids the centers of the
input ends beyond the height `r`, where `u` and `J` along `u` are `C¹`, and let `g` be continuous.
Then the formal adjoint of the linearized operator of the datum
`TauCeti.Floer.puncturedSpherePerturbation c a H Hout`, on a `C¹` covector field with compact
support in `ψ ((r, ∞) × ℝ)`, has integrable square norm against the weight `g`. -/
private theorem integrable_mul_norm_floerLinearizationAdjoint_sq_puncturedSpherePerturbation
    (ω : SymplecticForm V) (hH : ∀ i, Periodic (H i) 1) (hHs : ∀ i, ContDiff ℝ 2 (uncurry (H i)))
    (hHout : Periodic Hout 1) (hHouts : ContDiff ℝ 2 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    {ψ : ℝ × ℝ → ℝ × ℝ} {r : ℝ}
    (hψ : ∀ ζ : ℝ × ℝ, r < ζ.1 → ∀ j, Complex.equivRealProdCLM.symm (ψ ζ) ≠ c j)
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {u : ℝ × ℝ → V}
    (hJ : ∀ ζ : ℝ × ℝ, r < ζ.1 → ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (ψ ζ, u (ψ ζ)))
    (hu : ∀ ζ : ℝ × ℝ, r < ζ.1 → ContDiffAt ℝ 1 u (ψ ζ)) {g : ℝ × ℝ → ℝ} (hg : Continuous g)
    {η : ℝ × ℝ → V →L[ℝ] ℝ} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η)
    (hηU : tsupport η ⊆ ψ '' (Ioi r ×ˢ univ)) :
    Integrable fun z ↦ g z * ‖ω.floerLinearizationAdjoint
      (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
        Complex.I) u η z‖ ^ 2 := by
  have hD : Continuous (ω.floerLinearizationAdjoint
      (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
        Complex.I) u η) := by
    refine continuous_floerLinearizationAdjoint_of_tsupport_subset ?_ ?_ ?_ ?_ hη hηU
    · rintro _ ⟨ζ, hζ, rfl⟩
      exact hJ ζ hζ.1
    · rintro _ ⟨ζ, hζ, rfl⟩
      exact contDiffAt_uncurry_puncturedSpherePerturbation hH hHs hHout hHouts ha (hψ ζ hζ.1) _ 1
    · rintro _ ⟨ζ, hζ, rfl⟩
      exact contDiffAt_uncurry_puncturedSpherePerturbation hH hHs hHout hHouts ha (hψ ζ hζ.1) _
        Complex.I
    · rintro _ ⟨ζ, hζ, rfl⟩
      exact hu ζ hζ.1
  -- The integrand vanishes off the compact support of `η`.
  refine (hg.mul (hD.norm.pow 2)).integrable_of_hasCompactSupport
    (hηc.mono' fun z hz ↦ by_contra fun hz' ↦ hz ?_)
  simp [floerLinearizationAdjoint_of_notMem_tsupport hz']

/-- **The end estimate of the formal adjoint on an input end of a sphere with moving input ends.**
Let the discs `‖w - c j‖ < ‖a j‖ / 2` be pairwise disjoint and lie in the disc `‖w‖ ≤ 2 exp (2π)`,
with nonzero scales, and let the Hamiltonians be jointly `C²` of period one. Read the input end `i`
in the chart `ψ = realChart (z ↦ c i + a i φ₀(z))`. Let `x` be an orbit of `H_i` starting at a
nondegenerate fixed point of its time-one map, let `J_e(t)` be a `C²` family of almost complex
structures compatible along `x`, and let `J` be `J_e(t)` beyond `s = 2` in the chart. Let `J` along
`u` be `C¹` and compatible there, let `u` be `C²` and solve the Floer equation of the datum
`TauCeti.Floer.puncturedSpherePerturbation c a H Hout` beyond `s = 2`, and let the loops of
`u ∘ ψ` converge uniformly to `x` while the slice defect `∂t (u ∘ ψ) - X_{H_i}` tends uniformly to
zero. Then there are `C` and `R > 2` such that every `C²` covector field `η` with compact support
in the image `ψ ((R, ∞) × ℝ)` satisfies

`∫_{(2, ∞) × [0, 1]} (‖∂s η'‖² + ‖∂t η'‖² + ‖η'‖²) ≤ C ∫ |w - c i|² ‖D_u^* η (w)‖²`

for the formal adjoint `D_u^*` of the linearized Floer operator of these data, where
`η' = η (ψ ·) ∘ (a + b J)` is `η` read in the chart as a `(0, 1)`-form
(`TauCeti.Floer.covectorPullback`). The weight `|w - c i|²` is, up to `4π²`, the Jacobian of the
chart at `w`. -/
theorem
exists_forall_setIntegral_covectorPullback_le_mul_integral_floerLinearizationAdjoint_inputEnd
    (ω : SymplecticForm V) (hH : ∀ i, Periodic (H i) 1) (hHs : ∀ i, ContDiff ℝ 2 (uncurry (H i)))
    (hHout : Periodic Hout 1) (hHouts : ContDiff ℝ 2 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j ↦ ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) (i : ι) {L : ℝ≥0}
    (hX : LipschitzWith L (ω.timeDependentHamiltonianSuspension (H i))) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H i t) (x t)) t)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow (H i) hX 0 1) (x 0))
    {Je : ℝ → V → AlmostComplexStructure V}
    (hJe : ContDiff ℝ 2 fun p : ℝ × V ↦ (Je p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ t, ω.Compatible (Je t (x t))) {J : ℝ × ℝ → V → AlmostComplexStructure V}
    (hJeq : ∀ ζ : ℝ × ℝ, 2 < ζ.1 →
      J (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ) = Je ζ.2)
    {u : ℝ × ℝ → V}
    (hJ : ∀ ζ : ℝ × ℝ, 2 < ζ.1 → ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
      (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ,
        u (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ)))
    (hu : ∀ ζ : ℝ × ℝ, 2 < ζ.1 →
      ContDiffAt ℝ 2 u (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ))
    (hc : ∀ ζ : ℝ × ℝ, 2 < ζ.1 → ω.Compatible
      (J (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ)
        (u (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ))))
    (hF : ∀ ζ : ℝ × ℝ, 2 < ζ.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ)
        (u (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ)))
      (ω.perturbedFDeriv
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u
        (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ζ) : ℝ × ℝ →ₗ[ℝ] V))
    (hux : TendstoUniformlyOn
      (fun s t ↦ u (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) (s, t))) x atTop
      (Icc 0 1))
    (hδ : TendstoUniformlyOn (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H i t))
      (u ∘ realChart fun z ↦ c i + a i * zero.cylindricalEndLift z) (s, t)) 0 atTop
      (Icc 0 1)) :
    ∃ C R : ℝ, 2 < R ∧ ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → HasCompactSupport η →
      tsupport η ⊆ realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) '' (Ioi R ×ˢ univ) →
      ∫ ζ in Ioi 2 ×ˢ Icc (0 : ℝ) 1, sobolevDensity
          (covectorPullback (realChart fun z ↦ c i + a i * zero.cylindricalEndLift z)
            (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ ≤
        C * ∫ z, ‖Complex.equivRealProdCLM.symm z - c i‖ ^ 2 *
          ‖ω.floerLinearizationAdjoint (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
            (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
              Complex.I) u η z‖ ^ 2 := by
  set ψ := realChart fun z ↦ c i + a i * zero.cylindricalEndLift z with hψ
  have hpb (ζ : ℝ × ℝ) (hζ : 2 < ζ.1) :=
    Floer.perturbationPullback_realChart_puncturedSpherePerturbation_of_two_le (Hout := Hout) hH ha
      hsep hout i hζ.le
  -- Beyond `s = 0` the chart avoids the centers.
  have hψne (ζ : ℝ × ℝ) (hζ : 0 < ζ.1) (j : ι) : Complex.equivRealProdCLM.symm (ψ ζ) ≠ c j := by
    rw [hψ, equivRealProdCLM_symm_realChart]
    exact add_mul_cylindricalEndLift_ne hsep (ha i) (by simpa using hζ) j
  -- The weight `4π² |w - c i|²` is the Jacobian of the chart.
  obtain ⟨C, R, hR, hest⟩ :=
    ω.exists_forall_setIntegral_covectorPullback_le_mul_integral_floerLinearizationAdjoint_of_chart
      (R₁ := 2) (w := fun z ↦ 4 * π ^ 2 * ‖Complex.equivRealProdCLM.symm z - c i‖ ^ 2) hX
      (hHs i) hx hnd hJe hJex (fun ζ _ ↦ (contDiff_realChart (by fun_prop)).contDiffAt)
      (fun ζ _ ↦ isComplexLinearMap_fderiv_realChart (hasDerivAt_add_mul_cylindricalEndLift _ _ _))
      (fun ζ _ ↦ fderiv_realChart_ne_zero (hasDerivAt_add_mul_cylindricalEndLift _ _ _)
        (mul_ne_zero (ha i) (zero.deriv_cylindricalEndLift_ne_zero _)))
      (realChart_add_mul_cylindricalEndLift_add_one (c i) (a i))
      ((injOn_realChart_add_mul_cylindricalEndLift (ha i) (S := Ioi 2) (t₀ := 0)).mono
        (prod_mono subset_rfl (by rw [zero_add]; exact Ioo_subset_Ico_self)))
      hJeq (fun ζ hζ ↦ by rw [hpb ζ hζ]; funext y; simp)
      (fun ζ hζ ↦ by rw [hpb ζ hζ]; funext y; simp) hJ hu hc hF hux hδ (fun z ↦ by positivity)
      (fun ζ _ ↦ (det_fderiv_realChart_add_mul_cylindricalEndLift (c i) (a i) ζ).le)
  refine ⟨C * (4 * π ^ 2), R, hR, fun η hη hηc hηR ↦ ?_⟩
  obtain ⟨b, hb⟩ := exists_forall_notMem_Ioo_realChart_eq_zero (ha i) hηc hηR
  refine (hest hη hb (ω.integrable_mul_norm_floerLinearizationAdjoint_sq_puncturedSpherePerturbation
    hH hHs hHout hHouts ha (fun ζ hζ ↦ hψne ζ (by linarith)) (fun ζ hζ ↦ hJ ζ (by linarith))
    (fun ζ hζ ↦ (hu ζ (by linarith)).of_le one_le_two) (by fun_prop) (hη.of_le one_le_two) hηc
    (hηR.trans (image_mono (prod_mono (Ioi_subset_Ioi hR.le) subset_rfl))))).trans_eq ?_
  simp only [mul_assoc, integral_const_mul]

/-- **The end estimate of the formal adjoint on the output end of a sphere with moving input
ends.** Let the discs `‖w - c j‖ < ‖a j‖ / 2` lie in the disc `‖w‖ ≤ 2 exp (2π)`, and let the
Hamiltonians be jointly `C²` of period one. Read the output end in the positive end chart `φ'_∞` of
the pair of pants, where far out the datum `TauCeti.Floer.puncturedSpherePerturbation c a H Hout`
is `H'(t) dt` for `H'(t, y) = -Hout(-t, y)`. Let `x` be an orbit of `H'` starting at a
nondegenerate fixed point of its time-one map, let `J_e(t)` be a `C²` family of almost complex
structures compatible along `x`, and let `J` be `J_e(t)` beyond `s = 2` in the chart. Let `J` along
`u` be `C¹` and compatible there, let `u` be `C²` and solve the Floer equation beyond `s = 2`, and
let the loops of `u ∘ φ'_∞` converge uniformly to `x` while the slice defect
`∂t (u ∘ φ'_∞) - X_{H'}` tends uniformly to zero. Then there are `C` and `R > 2` such that every
`C²` covector field `η` with compact support in the image `φ'_∞ ((R, ∞) × ℝ)` satisfies

`∫_{(2, ∞) × [0, 1]} (‖∂s η'‖² + ‖∂t η'‖² + ‖η'‖²) ≤ C ∫ |w|² ‖D_u^* η (w)‖²`

for the formal adjoint `D_u^*` of the linearized Floer operator of these data, where
`η' = η (φ'_∞ ·) ∘ (a + b J)` is `η` read in the chart as a `(0, 1)`-form
(`TauCeti.Floer.covectorPullback`). The weight `|w|²` is, up to `4π²`, the Jacobian of the chart
at `w`. -/
theorem
exists_forall_setIntegral_covectorPullback_le_mul_integral_floerLinearizationAdjoint_outputEnd
    (ω : SymplecticForm V) (hH : ∀ i, Periodic (H i) 1) (hHs : ∀ i, ContDiff ℝ 2 (uncurry (H i)))
    (hHout : Periodic Hout 1) (hHouts : ContDiff ℝ 2 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {L : ℝ≥0}
    (hX : LipschitzWith L (ω.timeDependentHamiltonianSuspension fun t y ↦ -Hout (-t) y))
    {x : ℝ → V} (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (fun y ↦ -Hout (-t) y) (x t)) t)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (fun t y ↦ -Hout (-t) y) hX 0 1) (x 0))
    {Je : ℝ → V → AlmostComplexStructure V}
    (hJe : ContDiff ℝ 2 fun p : ℝ × V ↦ (Je p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ t, ω.Compatible (Je t (x t))) {J : ℝ × ℝ → V → AlmostComplexStructure V}
    (hJeq : ∀ ζ : ℝ × ℝ, 2 < ζ.1 → J (positiveEndChart inf ζ) = Je ζ.2) {u : ℝ × ℝ → V}
    (hJ : ∀ ζ : ℝ × ℝ, 2 < ζ.1 → ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
      (positiveEndChart inf ζ, u (positiveEndChart inf ζ)))
    (hu : ∀ ζ : ℝ × ℝ, 2 < ζ.1 → ContDiffAt ℝ 2 u (positiveEndChart inf ζ))
    (hc : ∀ ζ : ℝ × ℝ, 2 < ζ.1 →
      ω.Compatible (J (positiveEndChart inf ζ) (u (positiveEndChart inf ζ))))
    (hF : ∀ ζ : ℝ × ℝ, 2 < ζ.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (positiveEndChart inf ζ) (u (positiveEndChart inf ζ)))
      (ω.perturbedFDeriv
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u (positiveEndChart inf ζ) : ℝ × ℝ →ₗ[ℝ] V))
    (hux : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart inf (s, t))) x atTop (Icc 0 1))
    (hδ : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField fun y ↦ -Hout (-t) y) (u ∘ positiveEndChart inf) (s, t))
      0 atTop (Icc 0 1)) :
    ∃ C R : ℝ, 2 < R ∧ ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → HasCompactSupport η →
      tsupport η ⊆ positiveEndChart inf '' (Ioi R ×ˢ univ) →
      ∫ ζ in Ioi 2 ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback (positiveEndChart inf)
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ ≤
        C * ∫ z, ‖Complex.equivRealProdCLM.symm z‖ ^ 2 *
          ‖ω.floerLinearizationAdjoint (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
            (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
              Complex.I) u η z‖ ^ 2 := by
  -- The weight `4π² |w|²` is the Jacobian of the chart.
  obtain ⟨C, R, hR, hest⟩ :=
    ω.exists_forall_setIntegral_covectorPullback_le_mul_integral_floerLinearizationAdjoint_of_chart
      (R₁ := 2) (w := fun z ↦ 4 * π ^ 2 * ‖Complex.equivRealProdCLM.symm z‖ ^ 2) hX
      ((hHouts.comp (contDiff_fst.neg.prodMk contDiff_snd)).neg) hx hnd hJe hJex
      (fun ζ _ ↦ (contDiff_positiveEndChart inf 3).contDiffAt)
      (fun ζ _ ↦ isComplexLinearMap_fderiv_positiveEndChart inf ζ)
      (fun ζ _ ↦ fderiv_positiveEndChart_ne_zero inf ζ) (positiveEndChart_add_one inf)
      ((injOn_positiveEndChart inf 0).mono
        (prod_mono (subset_univ _) (by rw [zero_add]; exact Ioo_subset_Ico_self)))
      hJeq
      (fun ζ hζ ↦ funext fun y ↦ by
        rw [perturbationPullback_positiveEndChart_inf_puncturedSpherePerturbation hHout hout hζ.le]
        simp)
      (fun ζ hζ ↦ funext fun y ↦ by
        rw [perturbationPullback_positiveEndChart_inf_puncturedSpherePerturbation hHout hout hζ.le]
        simp) hJ hu hc hF hux hδ (fun z ↦ by positivity)
      (fun ζ _ ↦ by rw [det_fderiv_positiveEndChart, endCenter_inf, sub_zero])
  refine ⟨C * (4 * π ^ 2), R, hR, fun η hη hηc hηR ↦ ?_⟩
  obtain ⟨b, hb⟩ := exists_forall_notMem_Ioo_positiveEndChart_inf_eq_zero hηc hηR
  refine (hest hη hb (ω.integrable_mul_norm_floerLinearizationAdjoint_sq_puncturedSpherePerturbation
    hH hHs hHout hHouts ha
    (fun ζ hζ ↦ equivRealProdCLM_symm_positiveEndChart_inf_ne hout (by linarith))
    (fun ζ hζ ↦ hJ ζ (by linarith))
    (fun ζ hζ ↦ (hu ζ (by linarith)).of_le one_le_two) (by fun_prop) (hη.of_le one_le_two) hηc
    (hηR.trans (image_mono (prod_mono (Ioi_subset_Ioi hR.le) subset_rfl))))).trans_eq ?_
  simp only [mul_assoc, integral_const_mul]

end TauCeti.SymplecticForm
