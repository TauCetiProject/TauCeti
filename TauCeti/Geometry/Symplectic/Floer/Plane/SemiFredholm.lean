/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Plane.Linearization
public import TauCeti.Geometry.Symplectic.Floer.Plane.Sobolev
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Complex.EquivRealProd
import TauCeti.Geometry.Symplectic.Floer.InteriorEstimate
import TauCeti.Geometry.Symplectic.Floer.Plane.Curvature
import TauCeti.Geometry.Symplectic.Floer.SemiFredholm.Adjoint

/-!
# The semi-Fredholm estimate of the linearized Floer operator on a PSS plane

Let `p` be a PSS plane, with domain the plane `ℂ ≅ ℝ × ℝ` and its end at `∞` read in the cylinder
coordinates of the end lift `φ(s, t) = exp (2π ε (s + i t))`
(`TauCeti.Floer.PSSPlane.cylindricalEndLift`), and let `D_u` be the linearized Floer operator
(`TauCeti.SymplecticForm.floerLinearization`) along a map `u` into a symplectic vector space
`(V, ω)`. The Fredholm theory of `D_u`, on which the counts of PSS planes rest, starts from the
semi-Fredholm estimate

`‖ξ ∘ φ‖²_{W^{1,2}(ε s > R)} + ‖ξ‖²_{W^{1,2}(‖w‖ ≤ e^{2πR})}`
`  ≤ C (‖D_u ξ‖²_{L²} + ‖ξ‖²_{L²(‖w‖ ≤ e^{2π(R+1)})})`

for sections `ξ` of compact support, with `C` and `R` independent of `ξ`. The left side is the
square of a `W^{1,2}` norm for a metric on the plane which is Euclidean on the disc
`‖w‖ ≤ e^{2πR}` and cylindrical on the end beyond it. The error term on the right lives on a
compact disc, which is the form Peetre's compact-error argument
(`ContinuousLinearMap.finiteDimensional_ker_of_compact_estimate`) turns into finite-dimensional
kernel and closed range once `D_u` is realized on Sobolev spaces.

* `exists_forall_le_mul_integral_floerLinearization_add_of_end` is the patching argument: for
  Floer data that are regular along `u`, with `J` compatible along `u` on a large disc, an
  estimate of `D_u` on sections supported far out on the end implies the semi-Fredholm estimate.
  The section is cut into an end piece and a core piece by smooth cutoffs of the plane. On the end
  piece the end estimate applies, on the core piece the estimate of `D_u` on a disc
  (`TauCeti.SymplecticForm.exists_forall_setIntegral_le_mul_integral_floerLinearization_add_of_lt`),
  and the cutoffs cost a factor `2` on `∫ ‖D_u ξ‖²` and `L²` norms of `ξ` on a compact disc, by
  the Leibniz rule
  `D_u (β ξ) = β D_u ξ + (∂s β) ξ + J ((∂t β) ξ)`
  (`TauCeti.SymplecticForm.exists_integral_norm_floerLinearization_smul_sq_le`).
* `exists_forall_le_mul_integral_floerLinearization_add_of_finite_energy` is the semi-Fredholm
  estimate along a finite-energy PSS plane whose ends converge to nondegenerate orbits, with
  structures cylindrical on the end, for which the end estimate is
  `exists_forall_setIntegral_comp_realChart_le_mul_integral_floerLinearization_of_finite_energy`.

The same holds for the formal adjoint `D_u^*` (`TauCeti.SymplecticForm.floerLinearizationAdjoint`)
on covector fields `η`, whose kernel is the cokernel of `D_u`. On the end the covector field is read
as the `(0, 1)`-form `η' = η (φ ·) ∘ (a + b J)` (`TauCeti.Floer.covectorPullback`), and the `L²`
norm of `D_u^* η` carries a weight `σ`, here the inverse `ρ⁻¹(w) = 1 + ‖w‖²` of the cylindrical
weight of the plane (`TauCeti.Floer.PSSPlane.cylindricalWeight`) for the dual of `W^{1,2}`:

`‖η'‖²_{W^{1,2}(ε s > R)} + ‖η‖²_{W^{1,2}(‖w‖ ≤ e^{2πR})}`
`  ≤ C (∫ ρ⁻¹ ‖D_u^* η‖² + ‖η‖²_{L²(‖w‖ ≤ e^{2π(R+1)})})`.

* `exists_forall_le_mul_integral_floerLinearizationAdjoint_add_of_end` is the patching argument
  for `D_u^*`, for any continuous positive weight `σ`: the cutoffs are those of `D_u`, which the
  adjoint differentiates through `-(∂s β) η - (∂t β) η ∘ J`, at a cost controlled by
  `TauCeti.SymplecticForm.exists_integral_mul_norm_floerLinearizationAdjoint_smul_sq_le`; on the
  core the estimate of `D_u^*` on a disc of
  `TauCeti.Geometry.Symplectic.Floer.SemiFredholm.Adjoint` applies, and there the weight is bounded
  below
  (`TauCeti.SymplecticForm.exists_setIntegral_norm_floerLinearizationAdjoint_sq_le_mul_integral`).
* `exists_forall_le_mul_integral_floerLinearizationAdjoint_add_of_finite_energy_positive` is the
  semi-Fredholm estimate of `D_u^*` along a finite-energy positive PSS plane, from the end estimate
  `exists_forall_setIntegral_covectorPullback_le_mul_integral_floerLinearizationAdjoint_positive`,
  whose weight `‖w‖²` is at most `ρ⁻¹`. Every PSS plane is the positive plane for a reflected
  Hamiltonian (`TauCeti.Floer.PSSPlane.perturbation_eq_positive`).

The target is a symplectic vector space. The Sobolev realizations of `D_u` and `D_u^*` on the plane,
the finiteness of the cokernel and the Fredholm property are not treated here.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  Fredholm theory of the perturbed planes of the PSS maps.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 3.1 and Appendix B, on the semi-Fredholm estimate on
  punctured Riemann surfaces with cylindrical ends.
-/

public section

open Filter Function Set MeasureTheory
open TauCeti.Complex (realChart contDiff_realChart)
open scoped Topology NNReal Manifold Real

namespace TauCeti.SymplecticForm

open Floer Floer.PSSPlane

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The cutoff of the end.** There is a `C²` function `β` with values in `[0, 1]`, equal to `1`
near every point with `‖w‖ ≥ exp (2π (Re + 1))`, whose derivative vanishes off the compact disc
`‖w‖ ≤ exp (2π (Re + 1))` and whose topological support lies in the part `‖w‖ > exp (2π Re)` of
the end: `β = 1 - ψ` for a cutoff `ψ` of the disc `‖w‖ ≤ exp (2π Re)`. -/
private theorem exists_contDiff_endCutoff (Re : ℝ) :
    ∃ β : ℝ × ℝ → ℝ, ContDiff ℝ 2 β ∧ (∀ z, β z ∈ Icc 0 1) ∧
      (∀ z, Real.exp (2 * π * (Re + 1)) ≤ ‖Complex.equivRealProdCLM.symm z‖ → β =ᶠ[𝓝 z] 1) ∧
      (∀ z ∉ {z : ℝ × ℝ | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * (Re + 1))},
        fderiv ℝ β z = 0) ∧
      tsupport β ⊆ {z | Real.exp (2 * π * Re) < ‖Complex.equivRealProdCLM.symm z‖} := by
  obtain ⟨ψ, hψ, hψ01, hψ1, hψ0, hψK, -⟩ :=
    (isCompact_setOf_norm_equivRealProdCLM_symm_le _).exists_contDiff_cutoff_sublevel
      Complex.equivRealProdCLM.symm.continuous.norm
      (Real.exp_lt_exp.2 (by nlinarith [Real.pi_pos]) :
        Real.exp (2 * π * Re) < Real.exp (2 * π * (Re + 1)))
  refine ⟨fun z ↦ 1 - ψ z, (contDiff_const.sub hψ).of_le (by simp),
    fun z ↦ ⟨by simp [(hψ01 z).2], by simp [(hψ01 z).1]⟩,
    fun z hz ↦ (hψ0 z hz).mono fun z' h ↦ by simp [show ψ z' = 0 from h],
    fun z hz ↦ by rw [fderiv_const_sub, hψK z (not_le.1 hz), neg_zero], fun z hz ↦ ?_⟩
  -- Near the disc `‖w‖ ≤ exp (2π Re)` the cutoff vanishes.
  rw [mem_ofPred_eq]
  exact not_le.1 fun h ↦ notMem_tsupport_iff_eventuallyEq.2
    ((hψ1 z h).mono fun z' h' ↦ by simp [show ψ z' = 1 from h']) hz

/-- **The end estimate on a cut-off field.** Let `G ξ` be a field `ξ` read in the coordinates of
the end lift `φ`, such that multiplying `ξ` by a function `f` multiplies `G ξ` by `f ∘ φ`: the lift
`ξ ∘ φ` of a section, or the pulled-back form of a covector field. Suppose that `N` controls the
`W^{1,2}` energy of `G ξ` over `ℝ × [0, 1]` for `C²` fields `ξ` of compact support in the part
`‖w‖ > exp (2π Re)` of the end, and let `β` be a `C²` cutoff equal to `1` near the part
`‖w‖ ≥ exp (2π (Re + 1))` and supported in the part `‖w‖ > exp (2π Re)`. Then on the part
`ε s > Re + 1` of the end the energy of `G ξ` is that of `G (β ξ)`, so it is at most `N (β ξ)` up
to the constant, provided `G (β ξ)` has integrable energy. -/
private theorem setIntegral_sobolevDensity_le_of_endCutoff {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (p : PSSPlane)
    {G : (ℝ × ℝ → E) → ℝ × ℝ → F}
    (hG : ∀ (f : ℝ × ℝ → ℝ) (ξ : ℝ × ℝ → E) ζ,
      G (fun z ↦ f z • ξ z) ζ = f (realChart p.cylindricalEndLift ζ) • G ξ ζ)
    {Ce Re : ℝ} {N : (ℝ × ℝ → E) → ℝ}
    (he : ∀ ⦃ξ : ℝ × ℝ → E⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ {z | Real.exp (2 * π * Re) < ‖Complex.equivRealProdCLM.symm z‖} →
      ∫ ζ in univ ×ˢ Icc (0 : ℝ) 1, sobolevDensity (G ξ) ζ ≤ Ce * N ξ)
    {β : ℝ × ℝ → ℝ} (hβ : ContDiff ℝ 2 β)
    (hβ1 : ∀ z, Real.exp (2 * π * (Re + 1)) ≤ ‖Complex.equivRealProdCLM.symm z‖ → β =ᶠ[𝓝 z] 1)
    (hβR : tsupport β ⊆ {z | Real.exp (2 * π * Re) < ‖Complex.equivRealProdCLM.symm z‖})
    {ξ : ℝ × ℝ → E} (hξ : ContDiff ℝ 2 ξ) (hξc : HasCompactSupport ξ)
    (hint : IntegrableOn (sobolevDensity (G fun z ↦ β z • ξ z)) (univ ×ˢ Icc (0 : ℝ) 1))
    (hN : 0 ≤ N fun z ↦ β z • ξ z) :
    ∫ ζ in {s : ℝ | Re + 1 < p.endSign * s} ×ˢ Icc (0 : ℝ) 1, sobolevDensity (G ξ) ζ ≤
      max Ce 0 * N fun z ↦ β z • ξ z := by
  set φ := realChart p.cylindricalEndLift
  have hφ : Continuous φ := (contDiff_realChart (n := 0) p.contDiff_cylindricalEndLift).continuous
  refine (le_of_eq_of_le (setIntegral_congr_fun
    ((measurableSet_lt measurable_const (measurable_id.const_mul _)).prod measurableSet_Icc)
    fun ζ hζ ↦ ?_) (setIntegral_mono_set hint (ae_of_all _ fun _ ↦ sobolevDensity_nonneg _ _)
      (ae_of_all _ (prod_mono (subset_univ _) subset_rfl)))).trans
    ((he (hβ.smul hξ) (HasCompactSupport.smul_left (f := β) hξc)
      ((tsupport_smul_subset_left _ _).trans hβR)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hN))
  -- Far out on the end the cut-off field agrees with `ξ` near every point.
  have hφζ : Real.exp (2 * π * (Re + 1)) ≤ ‖Complex.equivRealProdCLM.symm (φ ζ)‖ := by
    rw [norm_symm_realChart_cylindricalEndLift]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hζ.1.le (by positivity))
  refine sobolevDensity_congr_of_eventuallyEq ?_
  filter_upwards [(hφ.tendsto ζ).eventually (hβ1 _ hφζ)] with ζ' h
  rw [hG, show β (φ ζ') = 1 from h, one_smul]

/-- **The estimate on the end.** Under an estimate of `D_u` on sections supported in the part
`‖w‖ > exp (2π Re)` of the end, `D_u` controls the `W^{1,2}` norm of every section of compact
support on the part `ε s > Re + 1` of the end, up to an `L²` norm on the disc
`‖w‖ ≤ exp (2π (Re + 1))`. -/
private theorem exists_setIntegral_comp_realChart_le_of_end (ω : SymplecticForm V) (p : PSSPlane)
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiff ℝ 1 u) {Ce Re : ℝ}
    (he : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ {z | Real.exp (2 * π * Re) < ‖Complex.equivRealProdCLM.symm z‖} →
      ∫ ζ in univ ×ˢ Icc (0 : ℝ) 1,
          (‖fderiv ℝ (ξ ∘ realChart p.cylindricalEndLift) ζ stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ (ξ ∘ realChart p.cylindricalEndLift) ζ stdComplexLineImag‖ ^ 2 +
            ‖(ξ ∘ realChart p.cylindricalEndLift) ζ‖ ^ 2) ≤
        Ce * ∫ z, ‖ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          Ks Kt u ξ z‖ ^ 2) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      ∫ ζ in {s : ℝ | Re + 1 < p.endSign * s} ×ˢ Icc (0 : ℝ) 1,
          (‖fderiv ℝ (ξ ∘ realChart p.cylindricalEndLift) ζ stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ (ξ ∘ realChart p.cylindricalEndLift) ζ stdComplexLineImag‖ ^ 2 +
            ‖(ξ ∘ realChart p.cylindricalEndLift) ζ‖ ^ 2) ≤
        C * ((∫ z, ‖ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          Ks Kt u ξ z‖ ^ 2) +
          ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * (Re + 1))},
            ‖ξ z‖ ^ 2) := by
  obtain ⟨β, hβ, hβ01, hβ1, hdβ, hβR⟩ := exists_contDiff_endCutoff Re
  obtain ⟨C₁, -, herr⟩ := ω.exists_integral_norm_floerLinearization_smul_sq_le
    (J := fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) hJ hKs hKt hu
    (hβ.of_le one_le_two) hβ01 (isCompact_setOf_norm_equivRealProdCLM_symm_le _) hdβ
  refine ⟨max Ce 0 * max 2 C₁, by positivity, fun ξ hξ hξc ↦ ?_⟩
  have hI₁ : 0 ≤ ∫ z, ‖ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
      Ks Kt u ξ z‖ ^ 2 := integral_nonneg fun _ ↦ by positivity
  have hI₂ : 0 ≤ ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * (Re + 1))},
      ‖ξ z‖ ^ 2 := setIntegral_nonneg_of_ae_restrict (ae_of_all _ fun _ ↦ by positivity)
  -- In end coordinates the cut-off section vanishes off a band, so its energy is integrable.
  obtain ⟨a, b, -, -, -, -, hout⟩ := p.exists_band_of_tsupport_subset
    (HasCompactSupport.smul_left (f := β) hξc) ((tsupport_smul_subset_left _ _).trans hβR)
  have hint : IntegrableOn
      (sobolevDensity ((fun w ↦ β w • ξ w) ∘ realChart p.cylindricalEndLift))
      (univ ×ˢ Icc (0 : ℝ) 1) :=
    (p.integrableOn_comp_realChart_cylindricalEndLift ((hβ.smul hξ).of_le one_le_two)
      MeasurableSet.univ fun ζ _ ↦ hout ζ).congr_fun
        (fun ζ _ ↦ (sobolevDensity_apply _ ζ).symm) (MeasurableSet.univ.prod measurableSet_Icc)
  calc _ ≤ max Ce 0 * ∫ z, ‖ω.floerLinearization
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u
          (fun w ↦ β w • ξ w) z‖ ^ 2 := by
        simpa only [sobolevDensity_apply] using setIntegral_sobolevDensity_le_of_endCutoff p
          (G := fun ξ ↦ ξ ∘ realChart p.cylindricalEndLift) (fun _ _ _ ↦ rfl)
          (fun ξ hξ hξc hξR ↦ by simpa only [sobolevDensity_apply] using he hξ hξc hξR) hβ hβ1 hβR
          hξ hξc hint (integral_nonneg fun _ ↦ sq_nonneg _)
    _ ≤ _ := by
        rw [mul_assoc]
        gcongr
        refine (herr (hξ.of_le one_le_two) hξc).trans ?_
        nlinarith [le_max_left 2 C₁, le_max_right 2 C₁]

/-- **Patching an end estimate into the semi-Fredholm estimate on a PSS plane.** Let `J` be `C¹`
and `K_s`, `K_t` `C²` at the points `(z, u z)`, and `u` `C¹`. Suppose that the linearized Floer
operator `D_u` controls the `W^{1,2}` norm on the end: there are `Ce` and `Re` such that every `C²`
section `ξ` of compact support in the part `‖w‖ > exp (2π Re)` of the plane satisfies
`∫ (‖∂s (ξ ∘ φ)‖² + ‖∂t (ξ ∘ φ)‖² + ‖ξ ∘ φ‖²) ≤ Ce ∫ ‖D_u ξ‖²`, the left integral over
`ℝ × [0, 1]` in the cylinder coordinates of the end lift `φ`. If moreover `J(z)` is compatible along
`u` on the disc `‖w‖ ≤ exp (2π (Re + 2))`, then there are `C ≥ 0` and `R` such that every `C²`
section `ξ` of compact support satisfies

`∫_{ε s > R} (‖∂s (ξ ∘ φ)‖² + ‖∂t (ξ ∘ φ)‖² + ‖ξ ∘ φ‖²) +`
`  ∫_{‖w‖ ≤ e^{2πR}} (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{‖w‖ ≤ e^{2π (R + 1)}} ‖ξ‖²)`,

the first integral over `{s | ε s > R} × [0, 1]` in end coordinates and the other integrals over
the plane. -/
theorem exists_forall_le_mul_integral_floerLinearization_add_of_end (ω : SymplecticForm V)
    (p : PSSPlane) {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ}
    {u : ℝ × ℝ → V}
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiff ℝ 1 u)
    {Ce Re : ℝ}
    (he : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ {z | Real.exp (2 * π * Re) < ‖Complex.equivRealProdCLM.symm z‖} →
      ∫ ζ in univ ×ˢ Icc (0 : ℝ) 1,
          (‖fderiv ℝ (ξ ∘ realChart p.cylindricalEndLift) ζ stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ (ξ ∘ realChart p.cylindricalEndLift) ζ stdComplexLineImag‖ ^ 2 +
            ‖(ξ ∘ realChart p.cylindricalEndLift) ζ‖ ^ 2) ≤
        Ce * ∫ z, ‖ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          Ks Kt u ξ z‖ ^ 2)
    (hc : ∀ z, ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * (Re + 2)) →
      ω.Compatible (J z (u z))) :
    ∃ C, 0 ≤ C ∧ ∃ R : ℝ, ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      (∫ ζ in {s : ℝ | R < p.endSign * s} ×ˢ Icc (0 : ℝ) 1,
          (‖fderiv ℝ (ξ ∘ realChart p.cylindricalEndLift) ζ stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ (ξ ∘ realChart p.cylindricalEndLift) ζ stdComplexLineImag‖ ^ 2 +
            ‖(ξ ∘ realChart p.cylindricalEndLift) ζ‖ ^ 2)) +
        ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * R)},
          (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 +
            ‖ξ z‖ ^ 2) ≤
        C * ((∫ z, ‖ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          Ks Kt u ξ z‖ ^ 2) +
          ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * (R + 1))},
            ‖ξ z‖ ^ 2) := by
  obtain ⟨C₁, hC₁, hend⟩ := exists_setIntegral_comp_realChart_le_of_end ω p hJ hKs hKt hu he
  obtain ⟨C₂, hC₂, hcore⟩ :=
    ω.exists_forall_setIntegral_le_mul_integral_floerLinearization_add_of_lt hJ hKs hKt hu
    (a := Real.exp (2 * π * (Re + 1))) (b := Real.exp (2 * π * (Re + 1 + 1)))
    (by rwa [add_assoc, one_add_one_eq_two]) (Real.exp_lt_exp.2 (by nlinarith [Real.pi_pos]))
  refine ⟨C₁ + C₂, by positivity, Re + 1, fun ξ hξ hξc ↦ ?_⟩
  -- The `L²` error term of the end lies in the larger disc of the core.
  have hmono : ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * (Re + 1))},
      ‖ξ z‖ ^ 2 ≤
      ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * (Re + 1 + 1))},
        ‖ξ z‖ ^ 2 :=
    setIntegral_mono_set ((hξ.continuous.norm.pow 2).continuousOn.integrableOn_compact
        (isCompact_setOf_norm_equivRealProdCLM_symm_le _))
      (ae_of_all _ fun _ ↦ by positivity)
      (ae_of_all _ fun z (hz : _ ≤ _) ↦ (show _ ≤ _ from
        hz.trans (Real.exp_le_exp.2 (by nlinarith [Real.pi_pos]))))
  have hX : 0 ≤ ∫ z, ‖ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
      Ks Kt u ξ z‖ ^ 2 := integral_nonneg fun _ ↦ by positivity
  have hY : 0 ≤ ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * (Re + 1 + 1))},
      ‖ξ z‖ ^ 2 := setIntegral_nonneg_of_ae_restrict (ae_of_all _ fun _ ↦ by positivity)
  nlinarith [hend hξ hξc, hcore hξ hξc, mul_le_mul_of_nonneg_left hmono hC₁,
    mul_nonneg hC₂ hX, mul_nonneg hC₁ hX, mul_nonneg hC₂ hY]

/-! ### The formal adjoint -/

/-- **The adjoint estimate on the end.** Under an estimate of the formal adjoint `D_u^*`, against a
continuous weight `σ ≥ 0`, on covector fields supported in the part `‖w‖ > exp (2π Re)` of the end,
`D_u^*` controls the `W^{1,2}` energy of the pulled-back form of every covector field of compact
support on the part `ε s > Re + 1` of the end, up to an `L²` norm on the disc
`‖w‖ ≤ exp (2π (Re + 1))`. -/
private theorem exists_setIntegral_sobolevDensity_covectorPullback_le_of_end
    (ω : SymplecticForm V) (p : PSSPlane) {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiff ℝ 1 u) {σ : ℝ × ℝ → ℝ}
    (hσ : ∀ z, 0 ≤ σ z) (hσc : Continuous σ) {Ce Re : ℝ}
    (he : ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → HasCompactSupport η →
      tsupport η ⊆ {z | Real.exp (2 * π * Re) < ‖Complex.equivRealProdCLM.symm z‖} →
      ∫ ζ in univ ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback
          (realChart p.cylindricalEndLift)
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ ≤
        Ce * ∫ z, σ z * ‖ω.floerLinearizationAdjoint
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → HasCompactSupport η →
      ∫ ζ in {s : ℝ | Re + 1 < p.endSign * s} ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback
          (realChart p.cylindricalEndLift)
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ ≤
        C * ((∫ z, σ z * ‖ω.floerLinearizationAdjoint
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2) +
          ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * (Re + 1))},
            ‖η z‖ ^ 2) := by
  set J' : ℝ × ℝ → V → V →L[ℝ] V := fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap
  obtain ⟨β, hβ, hβ01, hβ1, hdβ, hβR⟩ := exists_contDiff_endCutoff Re
  obtain ⟨C₁, -, herr⟩ := ω.exists_integral_mul_norm_floerLinearizationAdjoint_smul_sq_le
    (J := J') hJ hKs hKt hu hσ hσc (hβ.of_le one_le_two) hβ01
    (isCompact_setOf_norm_equivRealProdCLM_symm_le _) hdβ
  refine ⟨max Ce 0 * max 2 C₁, by positivity, fun η hη hηc ↦ ?_⟩
  have hI₁ : 0 ≤ ∫ z, σ z * ‖ω.floerLinearizationAdjoint J' Ks Kt u η z‖ ^ 2 :=
    integral_nonneg fun z ↦ mul_nonneg (hσ z) (sq_nonneg _)
  have hI₂ : 0 ≤ ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * (Re + 1))},
      ‖η z‖ ^ 2 := setIntegral_nonneg_of_ae_restrict (ae_of_all _ fun _ ↦ by positivity)
  calc _ ≤ max Ce 0 * ∫ z, σ z * ‖ω.floerLinearizationAdjoint J' Ks Kt u
          (fun x ↦ β x • η x) z‖ ^ 2 :=
        setIntegral_sobolevDensity_le_of_endCutoff p
          (G := covectorPullback (realChart p.cylindricalEndLift) J' u)
          (covectorPullback_fun_smul _ J' u) he hβ hβ1 hβR hη hηc
          (p.integrableOn_sobolevDensity_covectorPullback hJ hu ((hβ.smul hη).of_le one_le_two)
            (HasCompactSupport.smul_left (f := β) hηc) ((tsupport_smul_subset_left _ _).trans hβR))
          (integral_nonneg fun z ↦ mul_nonneg (hσ z) (sq_nonneg _))
    _ ≤ _ := by
        rw [mul_assoc]
        gcongr
        refine (herr (hη.of_le one_le_two) hηc).trans ?_
        nlinarith [le_max_left 2 C₁, le_max_right 2 C₁]

/-- **Patching an end estimate into the semi-Fredholm estimate of the formal adjoint on a PSS
plane.** Let `J` be `C¹` and `K_s`, `K_t` `C²` at the points `(z, u z)`, `u` `C¹`, and let `σ` be a
continuous positive weight. Suppose that the formal adjoint `D_u^*` of the linearized Floer
operator controls the `W^{1,2}` energy on the end: there are `Ce` and `Re` such that every `C²`
covector field `η` of compact support in the part `‖w‖ > exp (2π Re)` of the plane satisfies
`∫ (‖∂s η'‖² + ‖∂t η'‖² + ‖η'‖²) ≤ Ce ∫ σ ‖D_u^* η‖²`, the left integral over `ℝ × [0, 1]` for
the form `η' = η (φ ·) ∘ (a + b J)` read in the cylinder coordinates of the end lift `φ`
(`TauCeti.Floer.covectorPullback`). If moreover `J(z)` is compatible along `u` on the disc
`‖w‖ ≤ exp (2π (Re + 2))`, then there are `C ≥ 0` and `R` such that every `C²` covector field `η`
of compact support satisfies

`∫_{ε s > R} (‖∂s η'‖² + ‖∂t η'‖² + ‖η'‖²) +`
`  ∫_{‖w‖ ≤ e^{2πR}} (‖∂s η‖² + ‖∂t η‖² + ‖η‖²)`
`  ≤ C (∫ σ ‖D_u^* η‖² + ∫_{‖w‖ ≤ e^{2π (R + 1)}} ‖η‖²)`,

the first integral over `{s | ε s > R} × [0, 1]` in end coordinates and the other integrals over
the plane. This is the adjoint counterpart of
`exists_forall_le_mul_integral_floerLinearization_add_of_end`; on the compact disc the weight is
bounded below, and the estimate there is
`exists_forall_setIntegral_sobolevDensity_le_mul_setIntegral_floerLinearizationAdjoint_add_of_lt`.
-/
theorem exists_forall_le_mul_integral_floerLinearizationAdjoint_add_of_end
    (ω : SymplecticForm V) (p : PSSPlane) {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiff ℝ 1 u) {σ : ℝ × ℝ → ℝ}
    (hσ : ∀ z, 0 < σ z) (hσc : Continuous σ) {Ce Re : ℝ}
    (he : ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → HasCompactSupport η →
      tsupport η ⊆ {z | Real.exp (2 * π * Re) < ‖Complex.equivRealProdCLM.symm z‖} →
      ∫ ζ in univ ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback
          (realChart p.cylindricalEndLift)
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ ≤
        Ce * ∫ z, σ z * ‖ω.floerLinearizationAdjoint
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2)
    (hc : ∀ z, ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * (Re + 2)) →
      ω.Compatible (J z (u z))) :
    ∃ C, 0 ≤ C ∧ ∃ R : ℝ, ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → HasCompactSupport η →
      (∫ ζ in {s : ℝ | R < p.endSign * s} ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback
          (realChart p.cylindricalEndLift)
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ) +
        ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * R)},
          sobolevDensity η z ≤
        C * ((∫ z, σ z * ‖ω.floerLinearizationAdjoint
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2) +
          ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * (R + 1))},
            ‖η z‖ ^ 2) := by
  set J' : ℝ × ℝ → V → V →L[ℝ] V := fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap
  obtain ⟨C₁, hC₁, hend⟩ := exists_setIntegral_sobolevDensity_covectorPullback_le_of_end ω p hJ
    hKs hKt hu (fun z ↦ (hσ z).le) hσc he
  obtain ⟨C₂, hC₂, hcore⟩ :=
    exists_forall_setIntegral_sobolevDensity_le_mul_setIntegral_floerLinearizationAdjoint_add_of_lt
      ω (a := Real.exp (2 * π * (Re + 1))) (b := Real.exp (2 * π * (Re + 1 + 1)))
      (Real.exp_lt_exp.2 (by nlinarith [Real.pi_pos])) (fun z _ ↦ hJ z) (fun z _ ↦ hKs z)
      (fun z _ ↦ hKt z) (fun z _ ↦ hu.contDiffAt) (by rwa [add_assoc, one_add_one_eq_two])
  set K := {z : ℝ × ℝ | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * (Re + 1 + 1))}
  have hK : IsCompact K := isCompact_setOf_norm_equivRealProdCLM_symm_le _
  -- On the compact disc `K` the weight is bounded below.
  obtain ⟨Λ, hΛ₀, hΛ⟩ := ω.exists_setIntegral_norm_floerLinearizationAdjoint_sq_le_mul_integral
    (J := J') hJ hKs hKt hu hσ hσc hK
  refine ⟨C₁ + C₂ * (Λ + 1), by positivity, Re + 1, fun η hη hηc ↦ ?_⟩
  set X := ∫ z, σ z * ‖ω.floerLinearizationAdjoint J' Ks Kt u η z‖ ^ 2
  set Y := ∫ z in K, ‖η z‖ ^ 2
  have hX : 0 ≤ X := integral_nonneg fun z ↦ mul_nonneg (hσ z).le (sq_nonneg _)
  have hY : 0 ≤ Y := setIntegral_nonneg hK.measurableSet fun _ _ ↦ sq_nonneg _
  have hDc := continuous_floerLinearizationAdjoint (ω := ω) (J := J') hJ hKs hKt hu
    (hη.of_le one_le_two)
  -- The `L²` error term of the end lies in the larger disc `K`.
  have hmono : ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * (Re + 1))},
      ‖η z‖ ^ 2 ≤ Y :=
    setIntegral_mono_set ((hη.continuous.norm.pow 2).continuousOn.integrableOn_compact hK)
      (ae_of_all _ fun _ ↦ by positivity)
      (ae_of_all _ fun z (hz : _ ≤ _) ↦ (show _ ≤ _ from
        hz.trans (Real.exp_le_exp.2 (by nlinarith [Real.pi_pos]))))
  have hDK := hΛ (hη.of_le one_le_two) hηc
  have hcore' := hcore hη
  have hI₁ : IntegrableOn (fun z ↦ ‖ω.floerLinearizationAdjoint J' Ks Kt u η z‖ ^ 2) K :=
    (hDc.norm.pow 2).continuousOn.integrableOn_compact hK
  have hI₂ : IntegrableOn (fun z ↦ ‖η z‖ ^ 2) K :=
    (hη.continuous.norm.pow 2).continuousOn.integrableOn_compact hK
  rw [integral_add hI₁ hI₂] at hcore'
  nlinarith [hend hη hηc, mul_le_mul_of_nonneg_left hmono hC₁,
    mul_le_mul_of_nonneg_left hDK hC₂, mul_nonneg hC₁ hX, mul_nonneg hC₂ hX,
    mul_nonneg hC₂ hY, mul_nonneg (mul_nonneg hC₂ hΛ₀) hY]

section FiniteEnergy

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
/-- **Compatibility along `u`.** If `J(z)` is compatible along `u` on the disc `‖w‖ ≤ r`, and on
the part `‖w‖ > r` of the end `u` takes values in `K` and `J` is a family `J_q(t)` compatible on
`K`, then `J(z)` is compatible along `u` at every point of the plane. -/
private theorem compatible_of_le_of_endCoord (ω : SymplecticForm V) (p : PSSPlane) {K : Set V}
    {Jq : ℝ → V → AlmostComplexStructure V} (hJqK : ∀ t, ∀ y ∈ K, ω.Compatible (Jq t y))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {r : ℝ} {u : ℝ × ℝ → V}
    (hJr : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      J z = Jq (p.endCoord (Complex.equivRealProdCLM.symm z)).im)
    (hc : ∀ z, ‖Complex.equivRealProdCLM.symm z‖ ≤ r → ω.Compatible (J z (u z)))
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K) (z : ℝ × ℝ) :
    ω.Compatible (J z (u z)) := by
  rcases le_or_gt ‖Complex.equivRealProdCLM.symm z‖ r with hz | hz
  · exact hc z hz
  · rw [hJr z hz]
    exact hJqK _ _ (huK z hz)

/-- **The semi-Fredholm estimate on a finite-energy PSS plane.** Let `u` be a `C¹` map, `C³` on a
part `‖w‖ > r` of the end of the PSS plane `p`, solving there the Floer equation for the
perturbation of a jointly `C³` period-one Hamiltonian `H` with globally Lipschitz suspended vector
field, with finite energy and values in a compact set `K` on which every one-periodic orbit of `H`
is nondegenerate. Let the structures `J` be `C¹` along `u` and compatible along `u` on the disc
`‖w‖ ≤ r`, and on the part `‖w‖ > r` of the end equal to a `C²` period-one family `J_q(t)` read in
the angular coordinate, with `J_q` compatible on `K`. Then there are `C ≥ 0` and `R` such that
every `C²` section `ξ` of compact support satisfies

`∫_{ε s > R} (‖∂s (ξ ∘ φ)‖² + ‖∂t (ξ ∘ φ)‖² + ‖ξ ∘ φ‖²) +`
`  ∫_{‖w‖ ≤ e^{2πR}} (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{‖w‖ ≤ e^{2π (R + 1)}} ‖ξ‖²)`

for the linearized Floer operator `D_u` of the datum `(J, p.perturbation H)`, the first integral
over `{s | ε s > R} × [0, 1]` in the cylinder coordinates of the end lift `φ` and the other
integrals over the plane. -/
theorem exists_forall_le_mul_integral_floerLinearization_add_of_finite_energy
    (ω : SymplecticForm V) (p : PSSPlane) {H : ℝ → V → ℝ} (hH : Periodic H 1)
    (hHs : ContDiff ℝ 3 (uncurry H)) {L : ℝ≥0}
    (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H)) {K : Set V} (hK : IsCompact K)
    {Jq : ℝ → V → AlmostComplexStructure V}
    (hJq : ContDiff ℝ 2 fun q : ℝ × V ↦ (Jq q.1 q.2).toLinearMap.toContinuousLinearMap)
    (hJqper : Periodic Jq 1) (hJqK : ∀ t, ∀ y ∈ K, ω.Compatible (Jq t y))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {r : ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hJr : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      J z = Jq (p.endCoord (Complex.equivRealProdCLM.symm z)).im)
    (hu : ContDiff ℝ 1 u) (hur : ContDiffOn ℝ 3 u {z | r < ‖Complex.equivRealProdCLM.symm z‖})
    (hc : ∀ z, ‖Complex.equivRealProdCLM.symm z‖ ≤ r → ω.Compatible (J z (u z)))
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (hF : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
          z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤)
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0)) :
    ∃ C, 0 ≤ C ∧ ∃ R : ℝ, ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      (∫ ζ in {s : ℝ | R < p.endSign * s} ×ˢ Icc (0 : ℝ) 1,
          (‖fderiv ℝ (ξ ∘ realChart p.cylindricalEndLift) ζ stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ (ξ ∘ realChart p.cylindricalEndLift) ζ stdComplexLineImag‖ ^ 2 +
            ‖(ξ ∘ realChart p.cylindricalEndLift) ζ‖ ^ 2)) +
        ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * R)},
          (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 +
            ‖ξ z‖ ^ 2) ≤
        C * ((∫ z, ‖ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u ξ z‖ ^ 2) +
          ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * (R + 1))},
            ‖ξ z‖ ^ 2) := by
  obtain ⟨Ce, Re, he⟩ :=
    ω.exists_forall_setIntegral_comp_realChart_le_mul_integral_floerLinearization_of_finite_energy
      p hH hHs hL hK hJq hJqper hJqK hJr hur huK hF hE hnd
  have hHs₂ : ContDiff ℝ (2 : ℕ∞) (uncurry H) := hHs.of_le (by norm_num)
  -- On the end, compatibility comes from that of `J_q` on `K`.
  exact ω.exists_forall_le_mul_integral_floerLinearization_add_of_end p hJ
    (fun _ ↦ (contDiff_uncurry_perturbation (p := p) hH hHs₂ 1).contDiffAt)
    (fun _ ↦ (contDiff_uncurry_perturbation (p := p) hH hHs₂ Complex.I).contDiffAt) hu he
    fun z _ ↦ compatible_of_le_of_endCoord ω p hJqK hJr hc huK z

/-- The weight `‖w‖²` of the end estimate of the formal adjoint is at most the inverse
`ρ⁻¹ = 1 + ‖w‖²` of the cylindrical weight, so the weighted `L²` norms of `D^* η` compare. -/
private theorem integral_norm_sq_mul_le_integral_inv_cylindricalWeight_mul
    {ω : SymplecticForm V} {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ z, ContDiffAt ℝ 1 (uncurry J) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiff ℝ 1 u)
    {η : ℝ × ℝ → V →L[ℝ] ℝ} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) :
    ∫ z, ‖Complex.equivRealProdCLM.symm z‖ ^ 2 * ‖ω.floerLinearizationAdjoint J Ks Kt u η z‖ ^ 2 ≤
      ∫ z, (PSSPlane.cylindricalWeight z)⁻¹ * ‖ω.floerLinearizationAdjoint J Ks Kt u η z‖ ^ 2 := by
  refine integral_mono_of_nonneg (ae_of_all _ fun z ↦ by positivity)
    (integrable_mul_norm_floerLinearizationAdjoint_sq_of_continuous
      continuous_inv_cylindricalWeight (continuous_floerLinearizationAdjoint hJ hKs hKt hu hη) hηc)
    (ae_of_all _ fun z ↦ ?_)
  simp only [inv_cylindricalWeight]
  gcongr
  linarith

/-- **The semi-Fredholm estimate of the formal adjoint on a finite-energy positive PSS plane.**
Let `u` be a `C¹` map, `C³` on a part `‖w‖ > r` of the end of the positive PSS plane, solving there
the Floer equation for the perturbation of a jointly `C³` period-one Hamiltonian `H` with globally
Lipschitz suspended vector field, with finite energy and values in a compact set `K` on which every
one-periodic orbit of `H` is nondegenerate. Let the structures `J` be `C¹` along `u` and compatible
along `u` on the disc `‖w‖ ≤ r`, and on the part `‖w‖ > r` of the end equal to a `C²` period-one
family `J_q(t)` read in the angular coordinate, with `J_q` compatible on `K`. Then there are
`C ≥ 0` and `R` such that every `C²` covector field `η` of compact support satisfies

`∫_{s > R} (‖∂s η'‖² + ‖∂t η'‖² + ‖η'‖²) +`
`  ∫_{‖w‖ ≤ e^{2πR}} (‖∂s η‖² + ‖∂t η‖² + ‖η‖²)`
`  ≤ C (∫ ρ⁻¹ ‖D_u^* η‖² + ∫_{‖w‖ ≤ e^{2π (R + 1)}} ‖η‖²)`

for the formal adjoint `D_u^*` of the linearized Floer operator of the datum
`(J, positive.perturbation H)`, where `η' = η (φ ·) ∘ (a + b J)` is `η` read in the cylinder
coordinates of the end lift `φ` (`TauCeti.Floer.covectorPullback`), the first integral is over
`(R, ∞) × [0, 1]` and the other integrals over the plane, and `ρ` is the cylindrical weight
`TauCeti.Floer.PSSPlane.cylindricalWeight` of the Sobolev space of the plane. The weight `ρ⁻¹` on
the right is that of the dual of `W^{1,2}`. The kernel of `D_u^*` is the cokernel of `D_u`. Every
PSS plane is the positive plane for the Hamiltonian `ε H(ε t)`
(`TauCeti.Floer.PSSPlane.perturbation_eq_positive`), so the estimate applies to the negative plane
as well. This is the counterpart for `D_u^*` of
`exists_forall_le_mul_integral_floerLinearization_add_of_finite_energy`; its end estimate is
`exists_forall_setIntegral_covectorPullback_le_mul_integral_floerLinearizationAdjoint_positive`,
whose weight `‖w‖²` is at most `ρ⁻¹ = 1 + ‖w‖²`. -/
theorem exists_forall_le_mul_integral_floerLinearizationAdjoint_add_of_finite_energy_positive
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} (hH : Periodic H 1) (hHs : ContDiff ℝ 3 (uncurry H))
    {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H)) {K : Set V}
    (hK : IsCompact K) {Jq : ℝ → V → AlmostComplexStructure V}
    (hJq : ContDiff ℝ 2 fun q : ℝ × V ↦ (Jq q.1 q.2).toLinearMap.toContinuousLinearMap)
    (hJqper : Periodic Jq 1) (hJqK : ∀ t, ∀ y ∈ K, ω.Compatible (Jq t y))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {r : ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hJr : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      J z = Jq (positive.endCoord (Complex.equivRealProdCLM.symm z)).im)
    (hu : ContDiff ℝ 1 u) (hur : ContDiffOn ℝ 3 u {z | r < ‖Complex.equivRealProdCLM.symm z‖})
    (hc : ∀ z, ‖Complex.equivRealProdCLM.symm z‖ ≤ r → ω.Compatible (J z (u z)))
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (hF : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
          z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤)
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0)) :
    ∃ C, 0 ≤ C ∧ ∃ R : ℝ, ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → HasCompactSupport η →
      (∫ ζ in Ioi R ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback
          (realChart positive.cylindricalEndLift)
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ) +
        ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * R)},
          sobolevDensity η z ≤
        C * ((∫ z, (PSSPlane.cylindricalWeight z)⁻¹ * ‖ω.floerLinearizationAdjoint
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u η z‖ ^ 2) +
          ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * (R + 1))},
            ‖η z‖ ^ 2) := by
  have hΩ : IsOpen {z : ℝ × ℝ | r < ‖Complex.equivRealProdCLM.symm z‖} :=
    isOpen_lt continuous_const (by fun_prop)
  -- The end converges to a nondegenerate orbit `x`, which gives the end estimate of `D_u^*`.
  obtain ⟨x, hxper, hx, hxK, a, hsub, hJeq, hux, hδ⟩ :=
    ω.exists_tendstoUniformlyOn_sliceDefect_of_finite_energy positive hH hHs hL hK hJq hJqper
      (fun t y hy ↦ (hJqK t y hy).tames) hJr hur huK hF hE hnd
  simp only [endSign_positive, one_mul] at hJeq hux hδ
  obtain ⟨Ce, Re, he⟩ :=
    ω.exists_forall_setIntegral_covectorPullback_le_mul_integral_floerLinearizationAdjoint_positive
      hH (hHs.of_le (by norm_num)) hL hx (hnd x hxper hx hxK) (Je := Jq) hJq
      (fun t ↦ hJqK t _ (hxK t)) hJeq
      (fun z hz ↦ (hur.contDiffAt (hΩ.mem_nhds (hsub hz))).of_le (by norm_num))
      (fun z _ ↦ compatible_of_le_of_endCoord ω positive hJqK hJr hc huK z)
      (fun z hz ↦ hF z (hsub hz)) hux hδ
  have hHs₂ : ContDiff ℝ (2 : ℕ∞) (uncurry H) := hHs.of_le (by norm_num)
  have hKs (z : ℝ × ℝ) :=
    (contDiff_uncurry_perturbation (p := positive) hH hHs₂ 1).contDiffAt (x := (z, u z))
  have hKt (z : ℝ × ℝ) :=
    (contDiff_uncurry_perturbation (p := positive) hH hHs₂ Complex.I).contDiffAt (x := (z, u z))
  -- The end estimate with the weight `‖w‖²` implies the one with `ρ⁻¹`.
  have he' : ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → HasCompactSupport η →
      tsupport η ⊆ {z | Real.exp (2 * π * Re) < ‖Complex.equivRealProdCLM.symm z‖} →
      ∫ ζ in univ ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback
          (realChart positive.cylindricalEndLift)
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ ≤
        max Ce 0 * ∫ z, (PSSPlane.cylindricalWeight z)⁻¹ * ‖ω.floerLinearizationAdjoint
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u η z‖ ^ 2 := fun η hη hηc hηR ↦
    (he hη hηc hηR).trans ((mul_le_mul_of_nonneg_right (le_max_left _ _)
      (integral_nonneg fun z ↦ by positivity)).trans (mul_le_mul_of_nonneg_left
        (integral_norm_sq_mul_le_integral_inv_cylindricalWeight_mul (ω := ω)
          (J := fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) hJ hKs hKt hu
          (hη.of_le one_le_two) hηc) (le_max_right _ _)))
  -- Compatibility on the disc, and on the end from that of `J_q` on `K`.
  obtain ⟨C, hC, R, hest⟩ := exists_forall_le_mul_integral_floerLinearizationAdjoint_add_of_end ω
    positive hJ hKs hKt hu (fun z ↦ inv_pos.2 (PSSPlane.isWeight_cylindricalWeight.pos z
      (mem_univ z))) continuous_inv_cylindricalWeight he'
    fun z _ ↦ compatible_of_le_of_endCoord ω positive hJqK hJr hc huK z
  refine ⟨C, hC, R, fun η hη hηc ↦ ?_⟩
  simpa only [endSign_positive, one_mul, Set.Ioi_def] using hest hη hηc

end FiniteEnergy

end TauCeti.SymplecticForm
