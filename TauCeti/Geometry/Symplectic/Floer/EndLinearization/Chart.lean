/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.EndLinearization
public import TauCeti.Geometry.Symplectic.Floer.Linearization.Pullback
import TauCeti.Geometry.Symplectic.Floer.SemiFredholm.Adjoint
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Density
import TauCeti.Algebra.Ring.Periodic
import TauCeti.MeasureTheory.Function.Jacobian.Plane
import TauCeti.Topology.Instances.Real.TSupport
import TauCeti.Topology.UniformSpace.UniformConvergence.Bounded

/-!
# The end estimate of the linearized Floer operator in a holomorphic end chart

Let `(V, ω)` be a finite-dimensional symplectic vector space and let `D_u` be the linearized
Floer operator (`TauCeti.SymplecticForm.floerLinearization`) of Floer data `(J, K_s, K_t)` along a
map `u`, written in real coordinates `ℝ × ℝ` of a punctured Riemann surface. A cylindrical end of
the surface is read in a chart `ψ : ℝ × ℝ → ℝ × ℝ`, holomorphic, of period one in `t` and injective
on `(R₁, ∞) × (0, 1)`, in which the end is the half-cylinder `s > R₁`. Suppose that beyond `R₁`
the pulled-back perturbation `ψ^*K` (`TauCeti.Floer.perturbationPullback`) is `H_e(t) dt`, the
structures are `J_e(t)`, and `u` solves the Floer equation, its loops converging to a nondegenerate
orbit `x` of `H_e`. Then the `W^{1,2}` energy of a section `ξ` supported far out on the end, read
in the chart, is controlled by the `L²` norm of `D_u ξ` on the whole surface
(`exists_forall_setIntegral_comp_le_mul_integral_floerLinearization_of_chart`, in the namespace
`TauCeti.SymplecticForm`):

`∫_{(R₁, ∞) × [0, 1]} (‖∂s (ξ ∘ ψ)‖² + ‖∂t (ξ ∘ ψ)‖² + ‖ξ ∘ ψ‖²) ≤ C ∫ ‖D_u ξ‖²`.

This is the end ingredient of the semi-Fredholm estimate of `D_u` on a surface with cylindrical
ends, for any family of end charts: the ends of the pair of pants, recentred ends, and the moving
ends of the four-punctured spheres along which the associativity of the pair-of-pants product is
proved.

The proof reads the operator in the chart. Beyond `R₁` the operator of the pulled-back data along
`u ∘ ψ` is the operator of the cylindrical datum `(J_e, 0, H_e)`, for which the end estimate on a
half-cylinder holds
(`exists_mem_forall_setIntegral_le_mul_setIntegral_norm_floerLinearization_sq` in the namespace
`TauCeti.SymplecticForm`).
Since `ψ` is holomorphic, the operator of the pulled-back data is `a - b J` times `D_u ξ` at `ψ`
for the complex derivative `a + i b` of `ψ`, and changing variables along `ψ` bounds its `L²` norm
by `1 + B²` times that of `D_u ξ`, where `B` bounds `J` along `u`
(`TauCeti.SymplecticForm.setIntegral_norm_floerLinearization_perturbationPullback_sq_le`). The
transformation law needs the components of `K` at the points of the end to be differentiable in
the target point; they are multiples of `H_e(t)`, since `dψ` is invertible.

The same holds for the formal adjoint `D_u^*` (`TauCeti.SymplecticForm.floerLinearizationAdjoint`)
on covector fields `η`, whose kernel is the cokernel of `D_u`
(`exists_forall_setIntegral_covectorPullback_le_mul_integral_floerLinearizationAdjoint_of_chart`,
in the namespace `TauCeti.SymplecticForm`). A covector field is read in the chart as the
`(0, 1)`-form `η' = η (ψ ·) ∘ (a + b J)` (`TauCeti.Floer.covectorPullback`), on which the adjoint
of the pulled-back data is the Jacobian `det dψ = a² + b²` times `D_u^* η` at `ψ`
(`TauCeti.SymplecticForm.floerLinearizationAdjoint_perturbationPullback`). The end estimate of the
adjoint on a half-cylinder
(`exists_forall_setIntegral_le_mul_setIntegral_floerLinearizationAdjoint` in the namespace
`TauCeti.SymplecticForm`) then bounds the energy of `η'` by `∫ w ‖D_u^* η‖²` for any weight `w`
with `det dψ ≤ w ∘ ψ` on the end: of the two factors of the Jacobian in the square norm, one is
bounded by `w` and the other is absorbed by the change of variables. The natural weight is thus the
Jacobian of the chart, read on the surface, which is comparable to the inverse of the conformal
factor of a metric that is cylindrical on the end. Since the half-cylinder estimate is stated for
`C²` fields, `ψ` is assumed `C³` and `J` and `u` `C²` far out on the end, so that `η'` is `C²`.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the Fredholm theory of Floer operators on surfaces with cylindrical ends.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1,
  on the semi-Fredholm estimate on punctured Riemann surfaces with cylindrical ends.
-/

public section

open Filter Function Set MeasureTheory
open scoped Topology NNReal Manifold

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Where the pullback of `(K_s, K_t)` along a chart with nonzero complex-linear derivative is
`H(t) dt` for a `C²` Hamiltonian `H(t)`, the components of `K` and their Hamiltonian vector fields
are differentiable in the target point. -/
private theorem differentiableAt_of_perturbationPullback (ω : SymplecticForm V) {h : V → ℝ}
    (hh : ContDiff ℝ 2 h) {ψ : ℝ × ℝ → ℝ × ℝ} {ζ : ℝ × ℝ}
    (hψJ : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) (fderiv ℝ ψ ζ : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ))
    (hψ₀ : fderiv ℝ ψ ζ ≠ 0) {Ks Kt : ℝ × ℝ → V → ℝ}
    (hKs : perturbationPullback ψ Ks Kt stdComplexLineReal ζ = 0)
    (hKt : perturbationPullback ψ Ks Kt stdComplexLineImag ζ = h) :
    (∀ y, DifferentiableAt ℝ (Ks (ψ ζ)) y) ∧ (∀ y, DifferentiableAt ℝ (Kt (ψ ζ)) y) ∧
      (∀ y, DifferentiableAt ℝ (ω.hamiltonianVectorField (Ks (ψ ζ))) y) ∧
      ∀ y, DifferentiableAt ℝ (ω.hamiltonianVectorField (Kt (ψ ζ))) y := by
  obtain ⟨c₁, c₂, h₁, h₂⟩ := exists_eq_mul_of_perturbationPullback hψJ hψ₀ hKs hKt
  have hXh : Differentiable ℝ (ω.hamiltonianVectorField h) :=
    (ω.contDiff_hamiltonianVectorField (n := 1) hh).differentiable one_ne_zero
  rw [h₁, h₂, ω.hamiltonianVectorField_const_mul', ω.hamiltonianVectorField_const_mul']
  exact ⟨fun y ↦ ((hh.differentiable two_ne_zero) y).const_mul c₁,
    fun y ↦ ((hh.differentiable two_ne_zero) y).const_mul c₂, fun y ↦ (hXh y).const_smul c₁,
    fun y ↦ (hXh y).const_smul c₂⟩

/-- **The operator of an end, read in a holomorphic chart.** Beyond the height `R₁` of the chart
`ψ`, where the structures are `J_e(t)`, bounded by `B` along `u`, the pulled-back perturbation is
`H_e(t) dt` and `u` solves the Floer equation, the `L²` norm over a band `[a, b] × [0, 1]` of the
operator of the cylindrical datum `(J_e, 0, H_e)` along `u ∘ ψ` on `ξ ∘ ψ` is at most `1 + B²`
times the `L²` norm of `D_u ξ`. -/
private theorem setIntegral_norm_floerLinearization_comp_sq_le_of_chart (ω : SymplecticForm V)
    {He : ℝ → V → ℝ} (hHe : ContDiff ℝ 2 (uncurry He)) {Je : ℝ → V → AlmostComplexStructure V}
    {ψ : ℝ × ℝ → ℝ × ℝ} {R₁ : ℝ} (hψ : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → DifferentiableAt ℝ ψ ζ)
    (hψJ : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) (fderiv ℝ ψ ζ : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ))
    (hψ₀ : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → fderiv ℝ ψ ζ ≠ 0) (hψinj : InjOn ψ (Ioi R₁ ×ˢ Ioo 0 1))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} (hJeq : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → J (ψ ζ) = Je ζ.2)
    {Ks Kt : ℝ × ℝ → V → ℝ}
    (hKs : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → perturbationPullback ψ Ks Kt stdComplexLineReal ζ = 0)
    (hKt : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → perturbationPullback ψ Ks Kt stdComplexLineImag ζ = He ζ.2)
    {u : ℝ × ℝ → V} (hu : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → DifferentiableAt ℝ u (ψ ζ))
    (hF : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (ψ ζ) (u (ψ ζ))) (ω.perturbedFDeriv Ks Kt u (ψ ζ) : ℝ × ℝ →ₗ[ℝ] V)) {a b B : ℝ}
    (ha : R₁ < a) (hB : ∀ ζ : ℝ × ℝ, a ≤ ζ.1 → ζ.2 ∈ Icc (0 : ℝ) 1 →
      ‖(Je ζ.2 (u (ψ ζ))).toLinearMap.toContinuousLinearMap‖ ≤ B)
    {ξ : ℝ × ℝ → V} (hξ : Differentiable ℝ ξ) (hint : Integrable (fun z ↦ ‖ω.floerLinearization
      (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2)) :
    ∫ ζ in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization
        (fun w y ↦ (Je w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
        (fun w ↦ He w.2) (u ∘ ψ) (ξ ∘ ψ) ζ‖ ^ 2 ≤
      (1 + B ^ 2) * ∫ z, ‖ω.floerLinearization
        (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2 := by
  have hpos {ζ : ℝ × ℝ} (hζ : ζ ∈ Ioo a b ×ˢ Ioo (0 : ℝ) 1) : R₁ < ζ.1 := ha.trans hζ.1.1
  have hKd (ζ : ℝ × ℝ) (hζ : R₁ < ζ.1) :=
    ω.differentiableAt_of_perturbationPullback (hHe.comp (contDiff_const.prodMk contDiff_id))
      (hψJ ζ hζ) (hψ₀ ζ hζ) (hKs ζ hζ) (hKt ζ hζ)
  -- The boundary of the band is negligible, and inside it the operator of the end data is the
  -- operator of the pulled-back data.
  rw [setIntegral_congr_set (s := Icc a b ×ˢ Icc (0 : ℝ) 1) (t := Ioo a b ×ˢ Ioo (0 : ℝ) 1) (by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Ioo_ae_eq_Icc.symm Ioo_ae_eq_Icc.symm)]
  rw [setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo) fun ζ hζ ↦ by
    rw [ω.floerLinearization_congr_data (u ∘ ψ) (ξ ∘ ψ)
      (J' := fun w y ↦ (J (ψ w) y).toLinearMap.toContinuousLinearMap)
      (by simp only [hJeq ζ (hpos hζ)]) (hKs ζ (hpos hζ)).symm (hKt ζ (hpos hζ)).symm]]
  -- Changing variables along `ψ` costs the factor `1 + B²`.
  refine (ω.setIntegral_norm_floerLinearization_perturbationPullback_sq_le (M := B)
    (measurableSet_Ioo.prod measurableSet_Ioo)
    (hψinj.mono (prod_mono (fun s hs ↦ ha.trans hs.1) subset_rfl))
    (fun w hw ↦ hψ w (hpos hw)) (fun w hw ↦ hψJ w (hpos hw)) (fun w hw ↦ hu w (hpos hw))
    (fun w _ ↦ hξ _) (fun w hw ↦ .of_forall (hKd w (hpos hw)).1)
    (fun w hw ↦ .of_forall (hKd w (hpos hw)).2.1)
    (fun w hw ↦ (hKd w (hpos hw)).2.2.1 _) (fun w hw ↦ (hKd w (hpos hw)).2.2.2 _)
    (fun w hw ↦ (floerOperator_eq_zero_iff ω J Ks Kt u (ψ w)).2 (hF w (hpos hw)))
    (fun w hw ↦ ?_) hint.integrableOn).trans ?_
  · rw [hJeq w (hpos hw)]
    exact hB w hw.1.1.le (Ioo_subset_Icc_self hw.2)
  · exact mul_le_mul_of_nonneg_left (setIntegral_le_integral hint
      (ae_of_all _ fun _ ↦ sq_nonneg _)) (by positivity)

omit [FiniteDimensional ℝ V] in
/-- The `W^{1,2}` energy over a half-cylinder `(R₁, ∞) × [0, 1]` of a map vanishing outside a band
`(R, b) × ℝ` with `R₁ < R` is its energy over `[R, b] × [0, 1]`. -/
private theorem setIntegral_sobolevDensity_eq_of_forall_notMem_Ioo {f : ℝ × ℝ → V} {R₁ R b : ℝ}
    (hR : R₁ < R) (hvan : ∀ s t, s ∉ Ioo R b → f (s, t) = 0) :
    ∫ ζ in Ioi R₁ ×ˢ Icc (0 : ℝ) 1, sobolevDensity f ζ =
      ∫ ζ in Icc R b ×ˢ Icc (0 : ℝ) 1, sobolevDensity f ζ := by
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (measurableSet_Ioi.prod measurableSet_Icc)
    (prod_mono (fun s hs ↦ hR.trans_le hs.1) subset_rfl) fun ζ hζ ↦ ?_
  rw [sobolevDensity_congr_of_eventuallyEq (eventuallyEq_zero_of_forall_notMem_Ioo_of_fst_notMem_Icc
    hvan fun h ↦ hζ.2 ⟨h, hζ.1.2⟩), sobolevDensity_zero]

/-- **The end estimate in a holomorphic end chart.** Let `x` be an orbit of a jointly `C²`
Hamiltonian `H_e` whose suspended vector field is globally Lipschitz, with `x(0)` a nondegenerate
fixed point of the time-one map, and let `J_e(t)` be a `C¹` family of almost complex structures
compatible along `x`. Let `ψ` be a chart of a cylindrical end, of period one in `t`, injective on
`(R₁, ∞) × (0, 1)` and `C²` with nonzero complex-linear derivative beyond `R₁`. Let
`(J, K_s, K_t)` be Floer data whose structures are `J_e(t)` and whose pulled-back perturbation
`ψ^*K` is `H_e(t) dt` beyond `R₁` in the chart, and let `u` be `C¹` and solve the Floer equation
there, its loops converging uniformly to `x` while the slice defect `∂t (u ∘ ψ) - X_{H_e}` tends
uniformly to zero. Then there are `C` and `R > R₁` such that every `C²` section `ξ` with `ξ ∘ ψ`
vanishing outside a band `(R, b) × ℝ`, and with `‖D_u ξ‖²` integrable, satisfies

`∫_{(R₁, ∞) × [0, 1]} (‖∂s (ξ ∘ ψ)‖² + ‖∂t (ξ ∘ ψ)‖² + ‖ξ ∘ ψ‖²) ≤ C ∫ ‖D_u ξ‖²`

for the linearized Floer operator `D_u` of the data `(J, K_s, K_t)`. -/
theorem exists_forall_setIntegral_comp_le_mul_integral_floerLinearization_of_chart
    (ω : SymplecticForm V) {He : ℝ → V → ℝ} {L : ℝ≥0}
    (hX : LipschitzWith L (ω.timeDependentHamiltonianSuspension He))
    (hHe : ContDiff ℝ 2 (uncurry He)) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (He t) (x t)) t)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow He hX 0 1) (x 0))
    {Je : ℝ → V → AlmostComplexStructure V}
    (hJe : ContDiff ℝ 1 fun p : ℝ × V ↦ (Je p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ t, ω.Compatible (Je t (x t))) {ψ : ℝ × ℝ → ℝ × ℝ} {R₁ : ℝ}
    (hψ : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → ContDiffAt ℝ 2 ψ ζ)
    (hψJ : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) (fderiv ℝ ψ ζ : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ))
    (hψ₀ : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → fderiv ℝ ψ ζ ≠ 0) (hψper : ∀ s t, ψ (s, t + 1) = ψ (s, t))
    (hψinj : InjOn ψ (Ioi R₁ ×ˢ Ioo 0 1)) {J : ℝ × ℝ → V → AlmostComplexStructure V}
    (hJeq : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → J (ψ ζ) = Je ζ.2) {Ks Kt : ℝ × ℝ → V → ℝ}
    (hKs : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → perturbationPullback ψ Ks Kt stdComplexLineReal ζ = 0)
    (hKt : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → perturbationPullback ψ Ks Kt stdComplexLineImag ζ = He ζ.2)
    {u : ℝ × ℝ → V} (hu : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → ContDiffAt ℝ 1 u (ψ ζ))
    (hF : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (ψ ζ) (u (ψ ζ))) (ω.perturbedFDeriv Ks Kt u (ψ ζ) : ℝ × ℝ →ₗ[ℝ] V))
    (hux : TendstoUniformlyOn (fun s t ↦ u (ψ (s, t))) x atTop (Icc 0 1))
    (hδ : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (He t)) (u ∘ ψ) (s, t)) 0 atTop (Icc 0 1)) :
    ∃ C R : ℝ, R₁ < R ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → ∀ ⦃b : ℝ⦄,
      (∀ s t, s ∉ Ioo R b → ξ (ψ (s, t)) = 0) →
      Integrable (fun z ↦ ‖ω.floerLinearization
        (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2) →
      ∫ ζ in Ioi R₁ ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ ψ) ζ ≤
        C * ∫ z, ‖ω.floerLinearization
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2 := by
  -- The end estimate on the half-cylinder, and a bound for `J` far out on the end.
  have huψ : ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 1 (u ∘ ψ) (s, t) :=
    (eventually_gt_atTop R₁).mono fun s hs t _ ↦
      (hu (s, t) hs).comp (s, t) ((hψ (s, t) hs).of_le one_le_two)
  obtain ⟨C₁, -, U, hU, hest⟩ :=
    ω.exists_mem_forall_setIntegral_le_mul_setIntegral_norm_floerLinearization_sq hX hHe hx hnd
      hJe hJex huψ hux hδ
  obtain ⟨R₂, hR₂⟩ := mem_atTop_sets.1 hU
  obtain ⟨B, R₃, hR₃⟩ := (isCompact_Icc.exists_eventually_forall_norm_le_of_tendstoUniformlyOn
    (fun t _ ↦ (hx t).continuousAt.continuousWithinAt) hJe.continuous hux).imp
      fun _ ↦ eventually_atTop.1
  set R := max (max R₂ R₃) (R₁ + 1)
  have hRR₁ : R₁ < R := lt_max_of_lt_right (lt_add_one R₁)
  have hR₂R : R₂ ≤ R := (le_max_left R₂ R₃).trans (le_max_left _ _)
  have hR₃R : R₃ ≤ R := (le_max_right R₂ R₃).trans (le_max_left _ _)
  refine ⟨max C₁ 0 * (1 + B ^ 2), R, hRR₁, fun ξ hξ b hξb hint ↦ ?_⟩
  set b' := max b (R + 1) -- the band `(R, b')` is nonempty
  have hRb : R ≤ b' := by linarith [le_max_right b (R + 1)]
  have hvan (s t : ℝ) (hs : s ∉ Ioo R b') : (ξ ∘ ψ) (s, t) = 0 :=
    hξb s t fun h ↦ hs ⟨h.1, h.2.trans_le (le_max_left _ _)⟩
  calc ∫ ζ in Ioi R₁ ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ ψ) ζ
      = ∫ ζ in Icc R b' ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ ψ) ζ :=
        setIntegral_sobolevDensity_eq_of_forall_notMem_Ioo hRR₁ hvan
    -- The end estimate on the half-cylinder `hest` is stated with the density written out.
    _ ≤ max C₁ 0 * ∫ ζ in Icc R b' ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization
          (fun w y ↦ (Je w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
          (fun w ↦ He w.2) (u ∘ ψ) (ξ ∘ ψ) ζ‖ ^ 2 := by
        simp only [funext (sobolevDensity_apply (ξ ∘ ψ))]
        -- The section read in the chart is `C²`: beyond `R₁` the chart is, and it vanishes
        -- before `R`.
        refine (hest (contDiff_iff_contDiffAt.2 fun ζ ↦ ?_)
          (fun s t ↦ by simp only [comp_apply, hψper]) hRb
          (fun s hs ↦ hR₂ s (hR₂R.trans hs.1)) (fun t ↦ hvan R t fun h ↦ lt_irrefl _ h.1)
          (fun t ↦ hvan b' t fun h ↦ lt_irrefl _ h.2)).trans
          (mul_le_mul_of_nonneg_right (le_max_left C₁ 0) (setIntegral_nonneg
            (measurableSet_Icc.prod measurableSet_Icc) fun _ _ ↦ sq_nonneg _))
        rcases lt_or_ge R₁ ζ.1 with hζ | hζ
        · exact hξ.contDiffAt.comp ζ (hψ ζ hζ)
        · exact (contDiff_const (c := (0 : V))).contDiffAt.congr_of_eventuallyEq
            (eventuallyEq_zero_of_forall_notMem_Ioo_of_fst_notMem_Icc hvan
              fun h ↦ (lt_irrefl _ ((hζ.trans_lt hRR₁).trans_le h.1)))
    _ ≤ max C₁ 0 * ((1 + B ^ 2) * ∫ z, ‖ω.floerLinearization
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (ω.setIntegral_norm_floerLinearization_comp_sq_le_of_chart hHe
          (fun ζ hζ ↦ (hψ ζ hζ).differentiableAt two_ne_zero) hψJ hψ₀ hψinj hJeq hKs hKt
          (fun ζ hζ ↦ (hu ζ hζ).differentiableAt one_ne_zero) hF hRR₁
          (fun ζ hζ ht ↦ hR₃ ζ.1 (hR₃R.trans hζ) ζ.2 ht) (hξ.differentiable two_ne_zero) hint)
          (le_max_right _ _)
    _ = _ := by ring

/-! ### The formal adjoint -/

/-- Far out in the chart `ψ`, where `ψ` is `C³`, `J` is a `C²` family `J_e(t)` and `u` is `C²`, a
`C²` covector field `η` vanishing in the chart outside a band `(R, b) × ℝ` with `R > R₁` reads in
the chart as a `C²` form `η (ψ ·) ∘ (a + b J)` (`TauCeti.Floer.covectorPullback`). -/
private theorem contDiff_covectorPullback_of_chart {Je : ℝ → V → AlmostComplexStructure V}
    (hJe : ContDiff ℝ 2 fun p : ℝ × V ↦ (Je p.1 p.2).toLinearMap.toContinuousLinearMap)
    {ψ : ℝ × ℝ → ℝ × ℝ} {R₁ : ℝ} (hψ : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → ContDiffAt ℝ 3 ψ ζ)
    {J : ℝ × ℝ → V → AlmostComplexStructure V} (hJeq : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → J (ψ ζ) = Je ζ.2)
    {u : ℝ × ℝ → V} (hu : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → ContDiffAt ℝ 2 u (ψ ζ))
    {η : ℝ × ℝ → V →L[ℝ] ℝ} (hη : ContDiff ℝ 2 η) {R b : ℝ} (hR : R₁ < R)
    (hvan : ∀ s t, s ∉ Ioo R b → η (ψ (s, t)) = 0) :
    ContDiff ℝ 2
      (covectorPullback ψ (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) := by
  -- Before the height `R > R₁` the form `η ∘ ψ` vanishes near every point.
  have hvan₀ (ζ : ℝ × ℝ) (hζ : ζ.1 ≤ R₁) : η ∘ ψ =ᶠ[𝓝 ζ] 0 :=
    eventuallyEq_zero_of_forall_notMem_Ioo_of_fst_notMem_Icc (f := η ∘ ψ) hvan
      fun h ↦ lt_irrefl _ ((hζ.trans_lt hR).trans_le h.1)
  refine contDiff_covectorPullback_of_eqOn (U := {ζ | R₁ < ζ.1})
    (Je := fun ζ y ↦ (Je ζ.2 y).toLinearMap.toContinuousLinearMap)
    (isOpen_lt continuous_const continuous_fst) hψ
    (hJe.comp ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd))
    (fun ζ hζ ↦ by simp only [Function.comp_apply, hJeq ζ hζ]) hu
    (contDiff_iff_contDiffAt.2 fun ζ ↦ ?_) fun ζ hζ ↦ not_le.1 fun h ↦
      notMem_tsupport_iff_eventuallyEq.2 (hvan₀ ζ h) hζ
  rcases lt_or_ge R₁ ζ.1 with hζ | hζ
  · exact hη.contDiffAt.comp ζ ((hψ ζ hζ).of_le (by norm_num))
  · exact contDiffAt_const.congr_of_eventuallyEq (hvan₀ ζ hζ)

/-- **The adjoint of an end, read in a holomorphic chart.** Beyond the height `R₁` of the chart
`ψ`, where the structures are `J_e(t)`, the pulled-back perturbation is `H_e(t) dt` and `u` solves
the Floer equation, the formal adjoint of the cylindrical datum `(J_e, 0, H_e)` along `u ∘ ψ` on
the pulled-back form `η (ψ ·) ∘ (a + b J)` is the Jacobian of `ψ` times `D_u^* η` at `ψ ζ`. -/
private theorem floerLinearizationAdjoint_covectorPullback_of_chart (ω : SymplecticForm V)
    {He : ℝ → V → ℝ} (hHe : ContDiff ℝ 2 (uncurry He)) {Je : ℝ → V → AlmostComplexStructure V}
    {ψ : ℝ × ℝ → ℝ × ℝ} {R₁ : ℝ} (hψ : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → ContDiffAt ℝ 2 ψ ζ)
    (hψJ : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) (fderiv ℝ ψ ζ : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ))
    (hψ₀ : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → fderiv ℝ ψ ζ ≠ 0) {J : ℝ × ℝ → V → AlmostComplexStructure V}
    (hJeq : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → J (ψ ζ) = Je ζ.2) {Ks Kt : ℝ × ℝ → V → ℝ}
    (hKs : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → perturbationPullback ψ Ks Kt stdComplexLineReal ζ = 0)
    (hKt : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → perturbationPullback ψ Ks Kt stdComplexLineImag ζ = He ζ.2)
    {u : ℝ × ℝ → V} {η : ℝ × ℝ → V →L[ℝ] ℝ} {ζ : ℝ × ℝ} (hζ : R₁ < ζ.1)
    (hu : DifferentiableAt ℝ u (ψ ζ)) (hη : DifferentiableAt ℝ η (ψ ζ))
    (hJu : DifferentiableAt ℝ (fun z ↦ (J z (u z)).toLinearMap.toContinuousLinearMap) (ψ ζ))
    (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (ψ ζ) (u (ψ ζ)))
      (ω.perturbedFDeriv Ks Kt u (ψ ζ) : ℝ × ℝ →ₗ[ℝ] V)) :
    ω.floerLinearizationAdjoint (fun z y ↦ (Je z.2 y).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun z ↦ He z.2) (u ∘ ψ)
        (covectorPullback ψ (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ =
      (fderiv ℝ ψ ζ).det • ω.floerLinearizationAdjoint
        (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u η (ψ ζ) := by
  have hU : {ζ' : ℝ × ℝ | R₁ < ζ'.1} ∈ 𝓝 ζ :=
    (isOpen_lt continuous_const continuous_fst).mem_nhds hζ
  obtain ⟨hKsd, hKtd, hXs, hXt⟩ := ω.differentiableAt_of_perturbationPullback
    (hHe.comp (contDiff_const.prodMk contDiff_id)) (hψJ ζ hζ) (hψ₀ ζ hζ) (hKs ζ hζ) (hKt ζ hζ)
  refine Eq.trans ?_ (ω.floerLinearizationAdjoint_perturbationPullback (hψ ζ hζ)
    (Filter.mem_of_superset hU fun ζ' hζ' ↦ hψJ ζ' hζ') hu (.of_forall hKsd) (.of_forall hKtd)
    (hXs _) (hXt _) ((floerOperator_eq_zero_iff ω J Ks Kt u (ψ ζ)).2 hF) hη hJu)
  -- The pulled-back data near `ζ` are the cylindrical datum, and the adjoint at `ζ` sees the
  -- perturbation only at `ζ`.
  refine ω.floerLinearizationAdjoint_congr_data _ _ ?_ (hKs ζ hζ).symm (hKt ζ hζ).symm
  filter_upwards [hU] with ζ' hζ'
  simp only [hJeq ζ' hζ']

/-- **The adjoint of an end, read in a holomorphic chart, in `L²`.** Beyond the height `R₁` of the
chart `ψ`, where the structures are `J_e(t)`, the pulled-back perturbation is `H_e(t) dt` and `u`
solves the Floer equation, let `w ≥ 0` be a weight with `det dψ ≤ w ∘ ψ`. Then the `L²` norm over
a band `[a, b] × [0, 1]` of the adjoint of the cylindrical datum `(J_e, 0, H_e)` along `u ∘ ψ` on
the pulled-back form `η (ψ ·) ∘ (a + b J)` is at most the integral of `w ‖D_u^* η‖²`: of the two
factors of the Jacobian in the square norm, one is bounded by `w` and the other is absorbed by the
change of variables. -/
private theorem setIntegral_norm_floerLinearizationAdjoint_covectorPullback_sq_le_of_chart
    (ω : SymplecticForm V) {He : ℝ → V → ℝ} (hHe : ContDiff ℝ 2 (uncurry He))
    {Je : ℝ → V → AlmostComplexStructure V} {ψ : ℝ × ℝ → ℝ × ℝ} {R₁ : ℝ}
    (hψ : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → ContDiffAt ℝ 2 ψ ζ)
    (hψJ : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) (fderiv ℝ ψ ζ : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ))
    (hψ₀ : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → fderiv ℝ ψ ζ ≠ 0) (hψinj : InjOn ψ (Ioi R₁ ×ˢ Ioo 0 1))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} (hJeq : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → J (ψ ζ) = Je ζ.2)
    {Ks Kt : ℝ × ℝ → V → ℝ}
    (hKs : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → perturbationPullback ψ Ks Kt stdComplexLineReal ζ = 0)
    (hKt : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → perturbationPullback ψ Ks Kt stdComplexLineImag ζ = He ζ.2)
    {u : ℝ × ℝ → V} (hu : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → DifferentiableAt ℝ u (ψ ζ))
    (hJu : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 →
      DifferentiableAt ℝ (fun z ↦ (J z (u z)).toLinearMap.toContinuousLinearMap) (ψ ζ))
    (hF : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (ψ ζ) (u (ψ ζ))) (ω.perturbedFDeriv Ks Kt u (ψ ζ) : ℝ × ℝ →ₗ[ℝ] V))
    {w : ℝ × ℝ → ℝ} (hw₀ : ∀ z, 0 ≤ w z)
    (hw : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → (fderiv ℝ ψ ζ).det ≤ w (ψ ζ)) {η : ℝ × ℝ → V →L[ℝ] ℝ}
    (hη : Differentiable ℝ η) (hint : Integrable fun z ↦ w z * ‖ω.floerLinearizationAdjoint
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2)
    {a b : ℝ} (ha : R₁ < a) :
    ∫ ζ in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearizationAdjoint
        (fun z y ↦ (Je z.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
        (fun z ↦ He z.2) (u ∘ ψ)
        (covectorPullback ψ (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ‖ ^ 2 ≤
      ∫ z, w z * ‖ω.floerLinearizationAdjoint
        (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2 := by
  set g : ℝ × ℝ → ℝ := fun z ↦ w z * ‖ω.floerLinearizationAdjoint
    (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2
  have hg (z : ℝ × ℝ) : 0 ≤ g z := mul_nonneg (hw₀ z) (sq_nonneg _)
  have hdet (ζ : ℝ × ℝ) (hζ : R₁ < ζ.1) : 0 ≤ (fderiv ℝ ψ ζ).det := by
    rw [ContinuousLinearMap.det, (hψJ ζ hζ).det_eq_sq_add_sq]
    positivity
  have hs : MeasurableSet (Ioo a b ×ˢ Ioo (0 : ℝ) 1) := measurableSet_Ioo.prod measurableSet_Ioo
  have hpos {ζ : ℝ × ℝ} (hζ : ζ ∈ Ioo a b ×ˢ Ioo (0 : ℝ) 1) : R₁ < ζ.1 := ha.trans hζ.1.1
  -- The dominating density `det (dψ) · g ∘ ψ` is integrable on the open band.
  have hint' : IntegrableOn (fun ζ ↦ (fderiv ℝ ψ ζ).det * g (ψ ζ))
      (Ioo a b ×ˢ Ioo (0 : ℝ) 1) :=
    (integrableOn_image_iff_of_eq_abs_det_smul hs
      (hψinj.mono (prod_mono (fun s hs ↦ ha.trans hs.1) subset_rfl))
      (fun ζ hζ ↦ (hψ ζ (hpos hζ)).differentiableAt two_ne_zero)
      fun ζ hζ ↦ by rw [abs_of_nonneg (hdet ζ (hpos hζ)), smul_eq_mul]).1 hint.integrableOn
  -- The boundary of the band is negligible.
  rw [setIntegral_congr_set (s := Icc a b ×ˢ Icc (0 : ℝ) 1) (t := Ioo a b ×ˢ Ioo (0 : ℝ) 1) (by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Ioo_ae_eq_Icc.symm Ioo_ae_eq_Icc.symm)]
  refine (integral_mono_of_nonneg (ae_of_all _ fun _ ↦ sq_nonneg _) hint'
    ((ae_restrict_iff' hs).2 (ae_of_all _ fun ζ hζ ↦ ?_))).trans
    (setIntegral_det_mul_comp_le_integral hs
      (hψinj.mono (prod_mono (fun s hs ↦ ha.trans hs.1) subset_rfl))
      (fun ζ hζ ↦ (hψ ζ (hpos hζ)).differentiableAt two_ne_zero) (fun ζ hζ ↦ hdet ζ (hpos hζ))
      hg hint)
  -- On the band the adjoint on the pulled-back form is `det (dψ)` times `D_u^* η` at `ψ ζ`, and
  -- `det (dψ)² ≤ det (dψ) · w ∘ ψ`.
  have hζ' := hpos hζ
  rw [floerLinearizationAdjoint_covectorPullback_of_chart ω hHe hψ hψJ hψ₀ hJeq hKs hKt hζ'
    (hu ζ hζ') (hη _) (hJu ζ hζ') (hF ζ hζ'), norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [sq, mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hw ζ hζ') (sq_nonneg _))
    (hdet ζ hζ')

/-- **The end estimate of the formal adjoint in a holomorphic end chart.** Let `x` be an orbit of a
jointly `C²` Hamiltonian `H_e` whose suspended vector field is globally Lipschitz, with `x(0)` a
nondegenerate fixed point of the time-one map, and let `J_e(t)` be a `C²` family of almost complex
structures compatible along `x`. Let `ψ` be a chart of a cylindrical end, of period one in `t`,
injective on `(R₁, ∞) × (0, 1)` and `C³` with nonzero complex-linear derivative beyond `R₁`. Let
`(J, K_s, K_t)` be Floer data whose structures are `J_e(t)` and whose pulled-back perturbation
`ψ^*K` is `H_e(t) dt` beyond `R₁` in the chart, with `J` `C¹` and compatible along `u` there, and
let `u` be `C²` and solve the Floer equation there, its loops converging uniformly to `x` while the
slice defect `∂t (u ∘ ψ) - X_{H_e}` tends uniformly to zero. Let `w ≥ 0` be a weight dominating the
Jacobian of the chart: `det dψ ≤ w ∘ ψ` beyond `R₁`. Then there are `C` and `R > R₁` such that every
`C²` covector field `η` with `η ∘ ψ` vanishing outside a band `(R, b) × ℝ`, and with
`w ‖D_u^* η‖²` integrable, satisfies

`∫_{(R₁, ∞) × [0, 1]} (‖∂s η'‖² + ‖∂t η'‖² + ‖η'‖²) ≤ C ∫ w ‖D_u^* η‖²`

for the formal adjoint `D_u^*` of the linearized Floer operator of the data `(J, K_s, K_t)`, where
`η' = η (ψ ·) ∘ (a + b J)` is `η` read in the chart as a `(0, 1)`-form
(`TauCeti.Floer.covectorPullback`).

The adjoint of the cylindrical datum on `η'` is the Jacobian of `ψ` times `D_u^* η`
(`TauCeti.SymplecticForm.floerLinearizationAdjoint_perturbationPullback`), and one factor of the
Jacobian is absorbed by the change of variables, so the natural weight is the Jacobian itself, read
on the surface. The form `η'` is `C²` because `ψ` is `C³` and `J` and `u` are `C²` far out on the
end. -/
theorem
exists_forall_setIntegral_covectorPullback_le_mul_integral_floerLinearizationAdjoint_of_chart
    (ω : SymplecticForm V) {He : ℝ → V → ℝ} {L : ℝ≥0}
    (hX : LipschitzWith L (ω.timeDependentHamiltonianSuspension He))
    (hHe : ContDiff ℝ 2 (uncurry He)) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (He t) (x t)) t)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow He hX 0 1) (x 0))
    {Je : ℝ → V → AlmostComplexStructure V}
    (hJe : ContDiff ℝ 2 fun p : ℝ × V ↦ (Je p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ t, ω.Compatible (Je t (x t))) {ψ : ℝ × ℝ → ℝ × ℝ} {R₁ : ℝ}
    (hψ : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → ContDiffAt ℝ 3 ψ ζ)
    (hψJ : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) (fderiv ℝ ψ ζ : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ))
    (hψ₀ : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → fderiv ℝ ψ ζ ≠ 0) (hψper : ∀ s t, ψ (s, t + 1) = ψ (s, t))
    (hψinj : InjOn ψ (Ioi R₁ ×ˢ Ioo 0 1)) {J : ℝ × ℝ → V → AlmostComplexStructure V}
    (hJeq : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → J (ψ ζ) = Je ζ.2) {Ks Kt : ℝ × ℝ → V → ℝ}
    (hKs : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → perturbationPullback ψ Ks Kt stdComplexLineReal ζ = 0)
    (hKt : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → perturbationPullback ψ Ks Kt stdComplexLineImag ζ = He ζ.2)
    {u : ℝ × ℝ → V}
    (hJ : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (ψ ζ, u (ψ ζ)))
    (hu : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → ContDiffAt ℝ 2 u (ψ ζ))
    (hc : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → ω.Compatible (J (ψ ζ) (u (ψ ζ))))
    (hF : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (ψ ζ) (u (ψ ζ))) (ω.perturbedFDeriv Ks Kt u (ψ ζ) : ℝ × ℝ →ₗ[ℝ] V))
    (hux : TendstoUniformlyOn (fun s t ↦ u (ψ (s, t))) x atTop (Icc 0 1))
    (hδ : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (He t)) (u ∘ ψ) (s, t)) 0 atTop (Icc 0 1))
    {w : ℝ × ℝ → ℝ} (hw₀ : ∀ z, 0 ≤ w z)
    (hw : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → (fderiv ℝ ψ ζ).det ≤ w (ψ ζ)) :
    ∃ C R : ℝ, R₁ < R ∧ ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → ∀ ⦃b : ℝ⦄,
      (∀ s t, s ∉ Ioo R b → η (ψ (s, t)) = 0) →
      Integrable (fun z ↦ w z * ‖ω.floerLinearizationAdjoint
        (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2) →
      ∫ ζ in Ioi R₁ ×ˢ Icc (0 : ℝ) 1, sobolevDensity
          (covectorPullback ψ (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ ≤
        C * ∫ z, w z * ‖ω.floerLinearizationAdjoint
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2 := by
  -- The end estimate of the adjoint on the half-cylinder of the end data, whose structure has
  -- period one and is compatible along `u ∘ ψ`.
  have hJ1 : Je 1 = Je 0 :=
    (periodic_of_forall_comp_eq (fun t ↦ hψper (R₁ + 1) t)
      fun t ↦ hJeq (R₁ + 1, t) (lt_add_one R₁)).eq
  obtain ⟨C₁, -, R₂, hest⟩ :=
    ω.exists_forall_setIntegral_le_mul_setIntegral_floerLinearizationAdjoint hX hHe hx hnd
      (hJe.of_le one_le_two) hJ1 hJex (u := u ∘ ψ)
      ((eventually_gt_atTop R₁).mono fun s hs t ↦
        ((hu (s, t) hs).of_le one_le_two).comp (s, t) ((hψ (s, t) hs).of_le (by norm_num)))
      ((eventually_gt_atTop R₁).mono fun s hs t ↦ by
        have h := hc (s, t) hs
        rw [hJeq (s, t) hs] at h
        exact h)
      hux hδ
  set R := max R₂ (R₁ + 1)
  have hRR₁ : R₁ < R := lt_max_of_lt_right (lt_add_one R₁)
  have hR₂R : R₂ ≤ R := le_max_left _ _
  refine ⟨max C₁ 0, R, hRR₁, fun η hη b hηb hint ↦ ?_⟩
  set b' := max b (R + 1) -- the band `(R, b')` is nonempty
  have hRb : R ≤ b' := by linarith [le_max_right b (R + 1)]
  set η' := covectorPullback ψ (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η
  have hvan (s t : ℝ) (hs : s ∉ Ioo R b') : η (ψ (s, t)) = 0 :=
    hηb s t fun h ↦ hs ⟨h.1, h.2.trans_le (le_max_left _ _)⟩
  have hvan' (s t : ℝ) (hs : s ∉ Ioo R b') : η' (s, t) = 0 :=
    covectorPullback_eq_zero_of_apply_eq_zero _ _ u (hvan s t hs)
  have hη' : ContDiff ℝ 2 η' := contDiff_covectorPullback_of_chart hJe hψ hJeq hu hη hRR₁ hvan
  calc ∫ ζ in Ioi R₁ ×ˢ Icc (0 : ℝ) 1, sobolevDensity η' ζ
      = ∫ ζ in Icc R b' ×ˢ Icc (0 : ℝ) 1, sobolevDensity η' ζ :=
        setIntegral_sobolevDensity_eq_of_forall_notMem_Ioo hRR₁ hvan'
    -- The end estimate on the half-cylinder `hest` is stated with the density written out.
    _ ≤ max C₁ 0 * ∫ ζ in Icc R b' ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearizationAdjoint
          (fun z y ↦ (Je z.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
          (fun z ↦ He z.2) (u ∘ ψ) η' ζ‖ ^ 2 := by
        simp only [funext (sobolevDensity_apply η')]
        exact (hest hη' (covectorPullback_add_snd_of_periodic_snd hψper _ u η) hRb hR₂R
          hvan').trans (mul_le_mul_of_nonneg_right (le_max_left C₁ 0) (setIntegral_nonneg
            (measurableSet_Icc.prod measurableSet_Icc) fun _ _ ↦ sq_nonneg _))
    _ ≤ _ :=
        mul_le_mul_of_nonneg_left
          (ω.setIntegral_norm_floerLinearizationAdjoint_covectorPullback_sq_le_of_chart hHe
            (fun ζ hζ ↦ (hψ ζ hζ).of_le (by norm_num)) hψJ hψ₀ hψinj hJeq hKs hKt
            (fun ζ hζ ↦ (hu ζ hζ).differentiableAt two_ne_zero)
            (fun ζ hζ ↦ ((hJ ζ hζ).differentiableAt one_ne_zero).comp (f := fun z ↦ (z, u z)) _
              (differentiableAt_id.prodMk ((hu ζ hζ).differentiableAt two_ne_zero)))
            hF hw₀ hw (hη.differentiable two_ne_zero) hint hRR₁)
          (le_max_right _ _)

end TauCeti.SymplecticForm
