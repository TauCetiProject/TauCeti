/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.EndLinearization
public import TauCeti.Geometry.Symplectic.Floer.Linearization.Pullback
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Density
import TauCeti.Algebra.Ring.Periodic
import TauCeti.Geometry.Symplectic.Floer.SemiFredholm.Adjoint
import TauCeti.Geometry.Symplectic.JHolomorphic.Line
import TauCeti.MeasureTheory.Function.Jacobian.Plane
import TauCeti.Topology.Instances.Real.TSupport
import TauCeti.Topology.UniformSpace.UniformConvergence.Bounded

/-!
# The end estimates of the linearized Floer operator in a holomorphic end chart

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

**The formal adjoint.** The cokernel of `D_u` is the kernel of its formal adjoint `D_u^*` on
covector fields, and `D_u^*` satisfies the same kind of end estimate
(`exists_forall_setIntegral_sobolevDensity_le_mul_integral_floerLinearizationAdjoint_of_chart`).
A covector field `η` is read in the chart as the `(0, 1)`-form `η' = η (ψ ·) ∘ (a + b J)`
(`TauCeti.Floer.covectorPullback`), on which the adjoint of the cylindrical datum is the Jacobian
`det dψ = a² + b²` times `D_u^* η` at `ψ`
(`TauCeti.SymplecticForm.floerLinearizationAdjoint_perturbationPullback`). The end estimate of the
adjoint on a half-cylinder
(`TauCeti.SymplecticForm.exists_forall_setIntegral_le_mul_setIntegral_floerLinearizationAdjoint`)
then bounds the energy of `η'`, and changing variables along `ψ` absorbs one factor of the
Jacobian. The other is bounded by a weight `ρ` with `det dψ ≤ ρ ∘ ψ`, so that

`∫_{(R₁, ∞) × [0, 1]} (‖∂s η'‖² + ‖∂t η'‖² + ‖η'‖²) ≤ C ∫ ρ ‖D_u^* η‖²`.

For the end chart `w = c + λ e^{∓2πz}` of a puncture `c` the Jacobian is `4π² |w - c|²`, the weight
of the dual of `W^{1,2}` near the puncture. The adjoint estimate on the half-cylinder needs `η'` to
be `C²`, so here the structures `J_e(t)` and `u` are `C²` far out on the end, `J` is compatible
along `u` there, and `ψ` is `C³`.

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

/-- **The adjoint of an end, read in a holomorphic chart, at a point.** Beyond the height `R₁` of
the chart `ψ`, where the structures are `J_e(t)`, the pulled-back perturbation is `H_e(t) dt` and
`u` solves the Floer equation, the formal adjoint of the cylindrical datum `(J_e, 0, H_e)` along
`u ∘ ψ`, on the covector field `η` read in the chart as the `(0, 1)`-form `η (ψ ·) ∘ (a + b J)`,
is the Jacobian of `ψ` times `D_u^* η` at `ψ ζ`. -/
theorem floerLinearizationAdjoint_covectorPullback_of_chart (ω : SymplecticForm V)
    {He : ℝ → V → ℝ} (hHe : ContDiff ℝ 2 (uncurry He)) {Je : ℝ → V → AlmostComplexStructure V}
    {ψ : ℝ × ℝ → ℝ × ℝ} {R₁ : ℝ}
    (hψJ : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) (fderiv ℝ ψ ζ : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ))
    (hψ₀ : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → fderiv ℝ ψ ζ ≠ 0) {J : ℝ × ℝ → V → AlmostComplexStructure V}
    (hJeq : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → J (ψ ζ) = Je ζ.2) {Ks Kt : ℝ × ℝ → V → ℝ}
    (hKs : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → perturbationPullback ψ Ks Kt stdComplexLineReal ζ = 0)
    (hKt : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → perturbationPullback ψ Ks Kt stdComplexLineImag ζ = He ζ.2)
    {u : ℝ × ℝ → V} {η : ℝ × ℝ → V →L[ℝ] ℝ} {ζ : ℝ × ℝ} (hζ : R₁ < ζ.1)
    (hψ : ContDiffAt ℝ 2 ψ ζ) (hu : DifferentiableAt ℝ u (ψ ζ))
    (hη : DifferentiableAt ℝ η (ψ ζ))
    (hJu : DifferentiableAt ℝ (fun z ↦ (J z (u z)).toLinearMap.toContinuousLinearMap) (ψ ζ))
    (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (ψ ζ) (u (ψ ζ)))
      (ω.perturbedFDeriv Ks Kt u (ψ ζ) : ℝ × ℝ →ₗ[ℝ] V)) :
    ω.floerLinearizationAdjoint (fun w y ↦ (Je w.2 y).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun w ↦ He w.2) (u ∘ ψ)
        (covectorPullback ψ (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ =
      (fderiv ℝ ψ ζ).det • ω.floerLinearizationAdjoint
        (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u η (ψ ζ) := by
  have hKd := ω.differentiableAt_of_perturbationPullback
    (hHe.comp (contDiff_const.prodMk contDiff_id)) (hψJ ζ hζ) (hψ₀ ζ hζ) (hKs ζ hζ) (hKt ζ hζ)
  have hU : {w : ℝ × ℝ | R₁ < w.1} ∈ 𝓝 ζ := (isOpen_lt continuous_const continuous_fst).mem_nhds hζ
  -- Near `ζ` the end data are the pulled-back data, and these transform by the Jacobian.
  refine Eq.trans (ω.floerLinearizationAdjoint_congr_data _ _ ?_ (hKs ζ hζ).symm (hKt ζ hζ).symm)
    (ω.floerLinearizationAdjoint_perturbationPullback hψ (Filter.mem_of_superset hU fun w hw ↦
      hψJ w hw) hu (.of_forall hKd.1) (.of_forall hKd.2.1) (hKd.2.2.1 _) (hKd.2.2.2 _)
      ((floerOperator_eq_zero_iff ω J Ks Kt u _).2 hF) hη hJu)
  filter_upwards [hU] with w hw
  rw [hJeq w hw]

/-- **The adjoint of an end, read in a holomorphic chart.** Beyond the height `R₁` of the chart
`ψ`, where the structures are `J_e(t)`, the pulled-back perturbation is `H_e(t) dt` and `u` solves
the Floer equation, and where the Jacobian of `ψ` is at most a weight `ρ ≥ 0` at the image point,
the `L²` norm over a band `[a, b] × [0, 1]` of the adjoint of the end data along `u ∘ ψ` on the
pulled-back form `η (ψ ·) ∘ (a + b J)` is at most `∫ ρ ‖D_u^* η‖²`: its square norm is the square
of the Jacobian times `‖D_u^* η‖²` at `ψ`, and the change of variables absorbs one Jacobian. -/
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
    {u : ℝ × ℝ → V}
    (hJ : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (ψ ζ, u (ψ ζ)))
    (hu : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → DifferentiableAt ℝ u (ψ ζ))
    (hF : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (ψ ζ) (u (ψ ζ))) (ω.perturbedFDeriv Ks Kt u (ψ ζ) : ℝ × ℝ →ₗ[ℝ] V))
    {ρ : ℝ × ℝ → ℝ} (hρ : ∀ z, 0 ≤ ρ z)
    (hdet : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → (fderiv ℝ ψ ζ).det ≤ ρ (ψ ζ))
    {η : ℝ × ℝ → V →L[ℝ] ℝ} (hη : Differentiable ℝ η)
    (hint : Integrable fun z ↦ ρ z * ‖ω.floerLinearizationAdjoint
      (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2) {a b : ℝ}
    (ha : R₁ < a) :
    ∫ ζ in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearizationAdjoint
        (fun w y ↦ (Je w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
        (fun w ↦ He w.2) (u ∘ ψ)
        (covectorPullback ψ (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ‖ ^ 2 ≤
      ∫ z, ρ z * ‖ω.floerLinearizationAdjoint
        (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2 := by
  set D := ω.floerLinearizationAdjoint (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
    Ks Kt u η
  set s := Ioo a b ×ˢ Ioo (0 : ℝ) 1
  have hs : MeasurableSet s := measurableSet_Ioo.prod measurableSet_Ioo
  have hpos {ζ : ℝ × ℝ} (hζ : ζ ∈ s) : R₁ < ζ.1 := ha.trans hζ.1.1
  have hinj : InjOn ψ s := hψinj.mono (prod_mono (fun _ h ↦ ha.trans h.1) subset_rfl)
  have hψd (ζ : ℝ × ℝ) (hζ : ζ ∈ s) : DifferentiableAt ℝ ψ ζ :=
    (hψ ζ (hpos hζ)).differentiableAt two_ne_zero
  have hdet₀ (ζ : ℝ × ℝ) (hζ : ζ ∈ s) : 0 ≤ (fderiv ℝ ψ ζ).det := by
    rw [ContinuousLinearMap.det]
    exact (hψJ ζ (hpos hζ)).det_nonneg
  -- The weighted integrand, read on the band through `ψ`, is integrable there.
  have hg : IntegrableOn (fun ζ ↦ (fderiv ℝ ψ ζ).det * (ρ (ψ ζ) * ‖D (ψ ζ)‖ ^ 2)) s :=
    (integrableOn_image_iff_of_eq_abs_det_smul hs hinj hψd fun ζ hζ ↦ by
      rw [abs_of_nonneg (hdet₀ ζ hζ), smul_eq_mul]).1 hint.integrableOn
  calc _ = ∫ ζ in s, ‖ω.floerLinearizationAdjoint
        (fun w y ↦ (Je w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
        (fun w ↦ He w.2) (u ∘ ψ)
        (covectorPullback ψ (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ‖ ^ 2 := by
        refine setIntegral_congr_set ?_
        rw [Measure.volume_eq_prod]
        exact (Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc).symm
    _ ≤ ∫ ζ in s, (fderiv ℝ ψ ζ).det * (ρ (ψ ζ) * ‖D (ψ ζ)‖ ^ 2) := by
        refine integral_mono_of_nonneg (.of_forall fun _ ↦ sq_nonneg _) hg
          ((ae_restrict_iff' hs).2 (.of_forall fun ζ hζ ↦ ?_))
        have hJu : DifferentiableAt ℝ (fun z ↦ (J z (u z)).toLinearMap.toContinuousLinearMap)
            (ψ ζ) := ((hJ ζ (hpos hζ)).differentiableAt one_ne_zero).comp (f := fun z ↦ (z, u z))
              _ (differentiableAt_id.prodMk (hu ζ (hpos hζ)))
        dsimp only
        rw [ω.floerLinearizationAdjoint_covectorPullback_of_chart hHe hψJ hψ₀ hJeq hKs hKt
          (hpos hζ) (hψ ζ (hpos hζ)) (hu ζ (hpos hζ)) (hη _) hJu (hF ζ (hpos hζ)), norm_smul,
          mul_pow, Real.norm_eq_abs, sq_abs, sq, mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hdet ζ (hpos hζ))
          (sq_nonneg _)) (hdet₀ ζ hζ)
    _ = ∫ z in ψ '' s, ρ z * ‖D z‖ ^ 2 :=
        (integral_image_eq_integral_of_eq_abs_det_smul hs hinj hψd fun ζ hζ ↦ by
          rw [abs_of_nonneg (hdet₀ ζ hζ), smul_eq_mul]).symm
    _ ≤ _ := setIntegral_le_integral hint (.of_forall fun z ↦ mul_nonneg (hρ z) (sq_nonneg _))

/-- Read in a holomorphic chart `ψ`, beyond whose height `R₁` the chart is `C³`, the structures
are a `C²` family `J_e(t)` and `u` is `C²`, a `C²` covector field `η` vanishing along the chart up
to a height `R > R₁` is a `C²` form `η (ψ ·) ∘ (a + b J)`. -/
private theorem contDiff_covectorPullback_of_chart {Je : ℝ → V → AlmostComplexStructure V}
    (hJe : ContDiff ℝ 2 fun p : ℝ × V ↦ (Je p.1 p.2).toLinearMap.toContinuousLinearMap)
    {ψ : ℝ × ℝ → ℝ × ℝ} {R₁ R : ℝ} (hR : R₁ < R)
    (hψ : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → ContDiffAt ℝ 3 ψ ζ)
    {J : ℝ × ℝ → V → AlmostComplexStructure V} (hJeq : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → J (ψ ζ) = Je ζ.2)
    {u : ℝ × ℝ → V} (hu : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → ContDiffAt ℝ 2 u (ψ ζ))
    {η : ℝ × ℝ → V →L[ℝ] ℝ} (hη : ContDiff ℝ 2 η) (hvan : ∀ s t, s ≤ R → η (ψ (s, t)) = 0) :
    ContDiff ℝ 2
      (covectorPullback ψ (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) := by
  -- `η ∘ ψ` vanishes on the open set `s < R`, which contains every point with `s ≤ R₁`.
  have hzero : EqOn (η ∘ ψ) 0 {ζ | ζ.1 < R} := fun ζ hζ ↦ hvan ζ.1 ζ.2 (le_of_lt hζ)
  refine contDiff_covectorPullback_of_eqOn
    (Je := fun ζ y ↦ (Je ζ.2 y).toLinearMap.toContinuousLinearMap)
    (isOpen_lt continuous_const continuous_fst) hψ
    (hJe.comp ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd))
    (fun ζ hζ ↦ by simp only [Function.comp_apply, hJeq ζ hζ]) hu
    (contDiff_iff_contDiffAt.2 fun ζ ↦ ?_) ?_
  · rcases lt_or_ge R₁ ζ.1 with hζ | hζ
    · exact hη.contDiffAt.comp ζ ((hψ ζ hζ).of_le (by norm_num))
    · exact contDiffAt_const.congr_of_eventuallyEq (Filter.mem_of_superset
        ((isOpen_lt continuous_fst continuous_const).mem_nhds (hζ.trans_lt hR)) hzero)
  · -- The support of `η ∘ ψ` lies in the closed set `s ≥ R`, beyond `R₁`.
    refine (closure_minimal (fun ζ hζ ↦ ?_) (isClosed_le continuous_const continuous_fst)).trans
      fun ζ hζ ↦ hR.trans_le hζ
    by_contra h
    exact hζ (hzero (not_le.1 h))

/-- **The end estimate of the formal adjoint in a holomorphic end chart.** Let `x` be an orbit of a
jointly `C²` Hamiltonian `H_e` whose suspended vector field is globally Lipschitz, with `x(0)` a
nondegenerate fixed point of the time-one map, and let `J_e(t)` be a `C²` family of almost complex
structures compatible along `x`. Let `ψ` be a chart of a cylindrical end, of period one in `t`,
injective on `(R₁, ∞) × (0, 1)` and `C³` with nonzero complex-linear derivative beyond `R₁`, and let
`ρ ≥ 0` be a weight bounding the Jacobian of `ψ` there, `det dψ ≤ ρ ∘ ψ`. Let `(J, K_s, K_t)` be
Floer data whose structures are `J_e(t)`, `C¹` along `u`, and whose pulled-back perturbation
`ψ^*K` is `H_e(t) dt` beyond `R₁` in the chart, and let `u` be `C²` there, solve the Floer equation
and have `J` compatible along it, its loops converging uniformly to `x` while the slice defect
`∂t (u ∘ ψ) - X_{H_e}` tends uniformly to zero. Then there are `C` and `R > R₁` such that every
`C²` covector field `η` with `η ∘ ψ` vanishing outside a band `(R, b) × ℝ`, and with
`ρ ‖D_u^* η‖²` integrable, satisfies

`∫_{(R₁, ∞) × [0, 1]} (‖∂s η'‖² + ‖∂t η'‖² + ‖η'‖²) ≤ C ∫ ρ ‖D_u^* η‖²`

for the formal adjoint `D_u^*` of the linearized Floer operator of the data `(J, K_s, K_t)`, where
`η' = η (ψ ·) ∘ (a + b J)` is `η` read in the chart as a `(0, 1)`-form
(`TauCeti.Floer.covectorPullback`).

This is the adjoint counterpart of
`TauCeti.SymplecticForm.exists_forall_setIntegral_comp_le_mul_integral_floerLinearization_of_chart`.
-/
theorem
    exists_forall_setIntegral_sobolevDensity_le_mul_integral_floerLinearizationAdjoint_of_chart
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
    {ρ : ℝ × ℝ → ℝ} (hρ : ∀ z, 0 ≤ ρ z)
    (hdet : ∀ ζ : ℝ × ℝ, R₁ < ζ.1 → (fderiv ℝ ψ ζ).det ≤ ρ (ψ ζ)) :
    ∃ C R : ℝ, R₁ < R ∧ ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → ∀ ⦃b : ℝ⦄,
      (∀ s t, s ∉ Ioo R b → η (ψ (s, t)) = 0) →
      Integrable (fun z ↦ ρ z * ‖ω.floerLinearizationAdjoint
        (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2) →
      ∫ ζ in Ioi R₁ ×ˢ Icc (0 : ℝ) 1, sobolevDensity
          (covectorPullback ψ (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ ≤
        C * ∫ z, ρ z * ‖ω.floerLinearizationAdjoint
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2 := by
  -- The structures `J_e(t)` have period one, since `ψ` has and `J ∘ ψ = J_e` beyond `R₁`.
  have hJ1 : Je 1 = Je 0 := (periodic_of_forall_comp_eq (a := R₁ + 1) (hψper (R₁ + 1))
    fun t ↦ hJeq (R₁ + 1, t) (lt_add_one R₁)).eq
  -- The end estimate of the adjoint on the half-cylinder of the end data along `u ∘ ψ`.
  obtain ⟨C₁, -, R₂, hest⟩ :=
    ω.exists_forall_setIntegral_le_mul_setIntegral_floerLinearizationAdjoint hX hHe hx hnd
      (hJe.of_le one_le_two) hJ1 hJex (u := u ∘ ψ)
      ((eventually_gt_atTop R₁).mono fun s hs t ↦ ((hu (s, t) hs).of_le one_le_two).comp (s, t)
        ((hψ (s, t) hs).of_le (by norm_num)))
      ((eventually_gt_atTop R₁).mono fun s hs t ↦ by
        simpa only [Function.comp_apply, hJeq (s, t) hs] using hc (s, t) hs)
      hux hδ
  set R := max R₂ (R₁ + 1)
  have hRR₁ : R₁ < R := lt_max_of_lt_right (lt_add_one R₁)
  refine ⟨max C₁ 0, R, hRR₁, fun η hη b hηb hint ↦ ?_⟩
  set b' := max b (R + 1) -- the band `(R, b')` is nonempty
  have hRb : R ≤ b' := by linarith [le_max_right b (R + 1)]
  have hvan (s t : ℝ) (hs : s ∉ Ioo R b') : η (ψ (s, t)) = 0 :=
    hηb s t fun h ↦ hs ⟨h.1, h.2.trans_le (le_max_left _ _)⟩
  set η' := covectorPullback ψ (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η
  have hvan' (s t : ℝ) (hs : s ∉ Ioo R b') : η' (s, t) = 0 :=
    covectorPullback_eq_zero_of_apply_eq_zero _ _ u (hvan s t hs)
  have hη' : ContDiff ℝ 2 η' := contDiff_covectorPullback_of_chart hJe hRR₁ hψ hJeq hu hη
    fun s t hs ↦ hvan s t fun h ↦ (not_lt.2 hs) h.1
  calc ∫ ζ in Ioi R₁ ×ˢ Icc (0 : ℝ) 1, sobolevDensity η' ζ
      = ∫ ζ in Icc R b' ×ˢ Icc (0 : ℝ) 1, sobolevDensity η' ζ :=
        setIntegral_sobolevDensity_eq_of_forall_notMem_Ioo hRR₁ hvan'
    -- The end estimate on the half-cylinder `hest` is stated with the density written out.
    _ ≤ max C₁ 0 * ∫ ζ in Icc R b' ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearizationAdjoint
          (fun w y ↦ (Je w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
          (fun w ↦ He w.2) (u ∘ ψ) η' ζ‖ ^ 2 := by
        simp only [funext (sobolevDensity_apply η')]
        exact (hest hη' (covectorPullback_add_snd_of_periodic_snd hψper _ u η) hRb
          (le_max_left _ _) hvan').trans (mul_le_mul_of_nonneg_right (le_max_left C₁ 0)
            (setIntegral_nonneg (measurableSet_Icc.prod measurableSet_Icc)
              fun _ _ ↦ sq_nonneg _))
    _ ≤ _ := mul_le_mul_of_nonneg_left
        (ω.setIntegral_norm_floerLinearizationAdjoint_covectorPullback_sq_le_of_chart hHe
          (fun ζ hζ ↦ (hψ ζ hζ).of_le (by norm_num)) hψJ hψ₀ hψinj hJeq hKs hKt hJ
          (fun ζ hζ ↦ (hu ζ hζ).differentiableAt two_ne_zero) hF hρ hdet
          (hη.differentiable two_ne_zero) hint hRR₁) (le_max_right _ _)

end TauCeti.SymplecticForm
