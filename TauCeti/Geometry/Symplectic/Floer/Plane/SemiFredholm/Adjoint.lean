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
import TauCeti.Geometry.Symplectic.Floer.Plane.Curvature
import TauCeti.Geometry.Symplectic.Floer.SemiFredholm.Adjoint

/-!
# The semi-Fredholm estimate of the formal adjoint on a PSS plane

Let `p` be a PSS plane, with domain the plane `ℂ ≅ ℝ × ℝ` and its end at `∞` read in the cylinder
coordinates of the end lift `φ(s, t) = exp (2π ε (s + i t))`
(`TauCeti.Floer.PSSPlane.cylindricalEndLift`), and let `D_u^*` be the formal adjoint
(`TauCeti.SymplecticForm.floerLinearizationAdjoint`) of the linearized Floer operator along a map
`u` into a symplectic vector space `(V, ω)`. The kernel of `D_u^*` is the cokernel of `D_u`, so the
finiteness of the cokernel of the linearized operator of a PSS plane, the second half of its
Fredholm property, starts from the semi-Fredholm estimate of `D_u^*`:

`‖η'‖²_{W^{1,2}(ε s > R)} + ‖η‖²_{W^{1,2}(‖z‖ ≤ e^{2πR})}`
`  ≤ C (∫ (1 + ‖z‖²) ‖D_u^* η‖² + ‖η‖²_{L²(‖z‖ ≤ e^{2π(R+1)})})`

for `C²` covector fields `η` of compact support, where `η' = η (φ ·) ∘ (a + b J)` is `η` read in
end coordinates as a `(0, 1)`-form (`TauCeti.Floer.covectorPullback`). The weight `1 + ‖z‖²` is
the inverse of the weight `TauCeti.Floer.PSSPlane.cylindricalWeight` of the Sobolev space of the
plane: on the end, `‖z‖²` is up to `4π²` the Jacobian of the end lift, and the adjoint of the end
data on `η'` is the Jacobian times `D_u^* η`.

* `exists_forall_le_mul_integral_floerLinearizationAdjoint_add_of_end` is the patching argument:
  an estimate of `D_u^*` on covector fields supported far out on the end, with a weight `w`,
  implies the semi-Fredholm estimate with that weight. The field is cut into an end piece and a
  core piece, exactly as for `D_u` in
  `TauCeti.SymplecticForm.exists_forall_le_mul_integral_floerLinearization_add_of_end`. The end
  piece is read in end coordinates, where pulling back commutes with the cutoff
  (`TauCeti.Floer.covectorPullback_fun_smul`), and the cutoff costs an `L²` norm of `η` on a disc
  (`exists_integral_mul_norm_floerLinearizationAdjoint_smul_sq_le`). The core piece is controlled
  by the estimate of `D_u^*` on a disc
  (`exists_forall_setIntegral_sobolevDensity_le_mul_integral_floerLinearizationAdjoint_add_of_lt`).
* `exists_forall_le_mul_integral_floerLinearizationAdjoint_add_positive` is the semi-Fredholm
  estimate of `D_u^*` along a map on the positive PSS plane whose end converges to a nondegenerate
  orbit, with the weight `ρ⁻¹ = 1 + ‖z‖²` for the cylindrical weight `ρ`. The end estimate is
  `exists_forall_setIntegral_covectorPullback_le_mul_integral_floerLinearizationAdjoint_positive`,
  with the weight `‖z‖² ≤ ρ⁻¹`.
* `exists_forall_le_mul_integral_floerLinearizationAdjoint_add_of_finite_energy_positive` is the
  same estimate along a finite-energy positive PSS plane with image in a compact set on which the
  one-periodic orbits are nondegenerate, and structures cylindrical on the end: the end then
  converges to a nondegenerate orbit
  (`TauCeti.SymplecticForm.exists_tendstoUniformlyOn_sliceDefect_of_finite_energy`).

This is the plane counterpart of the semi-Fredholm estimate of the formal adjoint on the pair of
pants,
`exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearizationAdjoint_add`. The
target is a symplectic vector space. The Sobolev realization of `D_u^*`, the regularity of weak
cokernel elements needed to apply the estimate to them, and the finiteness of the cokernel are not
treated here.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  Fredholm theory of the perturbed planes of the PSS maps.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 3.1 and Appendix C.1, on the formal adjoint of a real
  Cauchy–Riemann operator and the semi-Fredholm estimate on punctured Riemann surfaces with
  cylindrical ends.
-/

public section

open Filter Function Set MeasureTheory
open TauCeti.Complex (realChart contDiff_realChart)
open scoped Topology NNReal Manifold Real

namespace TauCeti.SymplecticForm

open Floer Floer.PSSPlane

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
/-- **The end piece agrees with its cut-off.** If `β = 1` near every point with
`‖z‖ ≥ exp (2π (R + 1))`, then on the part `ε s > R + 1` of the end the pulled-back form of `η` has
the energy density of the pulled-back form of `β η`. -/
private theorem setIntegral_sobolevDensity_covectorPullback_eq_smul (p : PSSPlane)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {u : ℝ × ℝ → V} {η : ℝ × ℝ → V →L[ℝ] ℝ} {β : ℝ × ℝ → ℝ}
    {R : ℝ}
    (hβ1 : ∀ z, Real.exp (2 * π * (R + 1)) ≤ ‖Complex.equivRealProdCLM.symm z‖ → β =ᶠ[𝓝 z] 1) :
    ∫ ζ in {s : ℝ | R + 1 < p.endSign * s} ×ˢ Icc (0 : ℝ) 1,
        sobolevDensity (covectorPullback (realChart p.cylindricalEndLift) J u η) ζ =
      ∫ ζ in {s : ℝ | R + 1 < p.endSign * s} ×ˢ Icc (0 : ℝ) 1, sobolevDensity
        (covectorPullback (realChart p.cylindricalEndLift) J u fun z ↦ β z • η z) ζ := by
  set φ := realChart p.cylindricalEndLift
  have hφ : Continuous φ := (contDiff_realChart (n := 0) p.contDiff_cylindricalEndLift).continuous
  refine setIntegral_congr_fun
    ((measurableSet_lt measurable_const (measurable_id.const_mul _)).prod measurableSet_Icc)
    fun ζ hζ ↦ (sobolevDensity_congr_of_eventuallyEq ?_).symm
  -- Far out on the end the cut-off field agrees with `η` near `φ ζ`.
  have hφζ : Real.exp (2 * π * (R + 1)) ≤ ‖Complex.equivRealProdCLM.symm (φ ζ)‖ := by
    rw [norm_symm_realChart_cylindricalEndLift]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hζ.1.le (by positivity))
  filter_upwards [(hφ.tendsto ζ).eventually (hβ1 _ hφζ)] with ζ' h
  rw [covectorPullback_fun_smul, h, Pi.one_apply, one_smul]

/-- **The estimate of the adjoint on the end.** Under an estimate of `D_u^*` with a weight `w` on
covector fields supported in the part `‖z‖ > exp (2π Re)` of the end, `D_u^*` controls the
`W^{1,2}` norm of every covector field of compact support on the part `ε s > Re + 1` of the end,
read in end coordinates, up to an `L²` norm on the disc `‖z‖ ≤ exp (2π (Re + 1))`. -/
private theorem exists_setIntegral_sobolevDensity_covectorPullback_le_of_end
    (ω : SymplecticForm V) (p : PSSPlane) {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiff ℝ 1 u)
    {w : ℝ × ℝ → ℝ} (hw : ∀ z, 0 ≤ w z) (hwc : Continuous w) {Ce Re : ℝ}
    (he : ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → HasCompactSupport η →
      tsupport η ⊆ {z | Real.exp (2 * π * Re) < ‖Complex.equivRealProdCLM.symm z‖} →
      ∫ ζ in univ ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback
          (realChart p.cylindricalEndLift)
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ ≤
        Ce * ∫ z, w z * ‖ω.floerLinearizationAdjoint
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → HasCompactSupport η →
      ∫ ζ in {s : ℝ | Re + 1 < p.endSign * s} ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback
          (realChart p.cylindricalEndLift)
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ ≤
        C * ((∫ z, w z * ‖ω.floerLinearizationAdjoint
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2) +
          ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * (Re + 1))},
            ‖η z‖ ^ 2) := by
  set J' : ℝ × ℝ → V → V →L[ℝ] V := fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap
  -- A cutoff `β` vanishing near `‖z‖ ≤ exp (2π Re)` and equal to `1` near
  -- `‖z‖ ≥ exp (2π (Re + 1))`.
  obtain ⟨β, hβ, hβ01, hβ0, hβ1, hβK⟩ :=
    (isCompact_setOf_norm_equivRealProdCLM_symm_le _).exists_contDiff_cutoff_superlevel
      Complex.equivRealProdCLM.symm.continuous.norm
      (Real.exp_lt_exp.2 (by nlinarith [Real.pi_pos]) :
        Real.exp (2 * π * Re) < Real.exp (2 * π * (Re + 1)))
  replace hβ : ContDiff ℝ 2 β := hβ.of_le (by simp)
  obtain ⟨C₁, -, herr⟩ := ω.exists_integral_mul_norm_floerLinearizationAdjoint_smul_sq_le
    (J := J') hJ hKs hKt hu hw hwc (hβ.of_le one_le_two) hβ01
    (isCompact_setOf_norm_equivRealProdCLM_symm_le _) fun z hz ↦ hβK z (not_le.1 hz)
  refine ⟨max Ce 0 * max 2 C₁, by positivity, fun η hη hηc ↦ ?_⟩
  -- The cut-off field `β η` is supported in the part `‖z‖ > exp (2π Re)` of the end.
  set η₁ : ℝ × ℝ → V →L[ℝ] ℝ := fun z ↦ β z • η z
  have hη₁ : ContDiff ℝ 2 η₁ := hβ.smul hη
  have hη₁c : HasCompactSupport η₁ := hηc.mono (support_smul_subset_right β η)
  have hη₁r : tsupport η₁ ⊆
      {z | Real.exp (2 * π * Re) < ‖Complex.equivRealProdCLM.symm z‖} := fun z hz ↦ by
    rw [mem_ofPred_eq]
    exact not_le.1 fun h ↦
      notMem_tsupport_iff_eventuallyEq.2 (hβ0 z h) (tsupport_smul_subset_left _ _ hz)
  set X := ∫ z, w z * ‖ω.floerLinearizationAdjoint J' Ks Kt u η z‖ ^ 2
  set Y := ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * (Re + 1))},
    ‖η z‖ ^ 2
  have hX : 0 ≤ X := integral_nonneg fun z ↦ by have := hw z; positivity
  have hY : 0 ≤ Y := setIntegral_nonneg_of_ae_restrict (ae_of_all _ fun _ ↦ by positivity)
  have hW : 0 ≤ ∫ z, w z * ‖ω.floerLinearizationAdjoint J' Ks Kt u η₁ z‖ ^ 2 :=
    integral_nonneg fun z ↦ by have := hw z; positivity
  rw [setIntegral_sobolevDensity_covectorPullback_eq_smul p hβ1]
  calc _ ≤ ∫ ζ in univ ×ˢ Icc (0 : ℝ) 1,
        sobolevDensity (covectorPullback (realChart p.cylindricalEndLift) J' u η₁) ζ :=
        setIntegral_mono_set (p.integrableOn_sobolevDensity_covectorPullback
          hJ hu (hη₁.of_le one_le_two) hη₁c hη₁r)
          (ae_of_all _ fun ζ ↦ sobolevDensity_nonneg _ ζ)
          (ae_of_all _ (prod_mono (subset_univ _) subset_rfl))
    _ ≤ Ce * ∫ z, w z * ‖ω.floerLinearizationAdjoint J' Ks Kt u η₁ z‖ ^ 2 := he hη₁ hη₁c hη₁r
    _ ≤ max Ce 0 * ∫ z, w z * ‖ω.floerLinearizationAdjoint J' Ks Kt u η₁ z‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hW
    _ ≤ max Ce 0 * (max 2 C₁ * (X + Y)) := by
        gcongr
        refine (herr (hη.of_le one_le_two) hηc).trans ?_
        nlinarith [le_max_left 2 C₁, le_max_right 2 C₁]
    _ = _ := by ring

/-- **Patching an end estimate into the semi-Fredholm estimate of the formal adjoint on a PSS
plane.** Let `J` be `C¹` and `K_s`, `K_t` `C²` at the points `(z, u z)`, and `u` `C¹`, and let
`w ≥ 0` be a continuous weight. Suppose that the formal adjoint `D_u^*` controls the `W^{1,2}` norm
on the end: there are `Ce` and `Re` such that every `C²` covector field `η` of compact support in
the part `‖z‖ > exp (2π Re)` of the plane satisfies
`∫ (‖∂s η'‖² + ‖∂t η'‖² + ‖η'‖²) ≤ Ce ∫ w ‖D_u^* η‖²`, the left integral over `ℝ × [0, 1]` in the
cylinder coordinates of the end lift `φ`, where `η' = η (φ ·) ∘ (a + b J)` is `η` read in end
coordinates (`TauCeti.Floer.covectorPullback`). If moreover `J(z)` is compatible along `u` and `w`
is positive on the disc `‖z‖ ≤ exp (2π (Re + 2))`, then there are `C ≥ 0` and `R` such that every
`C²` covector field `η` of compact support satisfies

`∫_{ε s > R} (‖∂s η'‖² + ‖∂t η'‖² + ‖η'‖²) + ∫_{‖z‖ ≤ e^{2πR}} (‖∂s η‖² + ‖∂t η‖² + ‖η‖²)`
`  ≤ C (∫ w ‖D_u^* η‖² + ∫_{‖z‖ ≤ e^{2π (R + 1)}} ‖η‖²)`,

the first integral over `{s | ε s > R} × [0, 1]` in end coordinates and the other integrals over
the plane. This is the adjoint counterpart of
`exists_forall_le_mul_integral_floerLinearization_add_of_end`. -/
theorem exists_forall_le_mul_integral_floerLinearizationAdjoint_add_of_end (ω : SymplecticForm V)
    (p : PSSPlane) {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ}
    {u : ℝ × ℝ → V}
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiff ℝ 1 u)
    {w : ℝ × ℝ → ℝ} (hw : ∀ z, 0 ≤ w z) (hwc : Continuous w) {Ce Re : ℝ}
    (he : ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → HasCompactSupport η →
      tsupport η ⊆ {z | Real.exp (2 * π * Re) < ‖Complex.equivRealProdCLM.symm z‖} →
      ∫ ζ in univ ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback
          (realChart p.cylindricalEndLift)
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ ≤
        Ce * ∫ z, w z * ‖ω.floerLinearizationAdjoint
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2)
    (hw₀ : ∀ z, ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * (Re + 2)) → 0 < w z)
    (hc : ∀ z, ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * (Re + 2)) →
      ω.Compatible (J z (u z))) :
    ∃ C, 0 ≤ C ∧ ∃ R : ℝ, ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → HasCompactSupport η →
      (∫ ζ in {s : ℝ | R < p.endSign * s} ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback
          (realChart p.cylindricalEndLift)
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ) +
        ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * R)},
          sobolevDensity η z ≤
        C * ((∫ z, w z * ‖ω.floerLinearizationAdjoint
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2) +
          ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * (R + 1))},
            ‖η z‖ ^ 2) := by
  obtain ⟨C₁, hC₁, hend⟩ :=
    exists_setIntegral_sobolevDensity_covectorPullback_le_of_end ω p hJ hKs hKt hu hw hwc he
  obtain ⟨C₂, hC₂, hcore⟩ :=
    ω.exists_forall_setIntegral_sobolevDensity_le_mul_integral_floerLinearizationAdjoint_add_of_lt
      hJ hKs hKt hu hw hwc (a := Real.exp (2 * π * (Re + 1)))
      (b := Real.exp (2 * π * (Re + 1 + 1))) (by rwa [add_assoc, one_add_one_eq_two])
      (by rwa [add_assoc, one_add_one_eq_two]) (Real.exp_lt_exp.2 (by nlinarith [Real.pi_pos]))
  refine ⟨C₁ + C₂, by positivity, Re + 1, fun η hη hηc ↦ ?_⟩
  -- The `L²` error term of the end lies in the larger disc of the core.
  have hmono : ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * (Re + 1))},
      ‖η z‖ ^ 2 ≤
      ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * (Re + 1 + 1))},
        ‖η z‖ ^ 2 :=
    setIntegral_mono_set ((hη.continuous.norm.pow 2).continuousOn.integrableOn_compact
        (isCompact_setOf_norm_equivRealProdCLM_symm_le _))
      (ae_of_all _ fun _ ↦ by positivity)
      (ofPred_subset_ofPred.2 fun _ hz ↦
        hz.trans (Real.exp_le_exp.2 (by nlinarith [Real.pi_pos]))).eventuallySubset
  have hX : 0 ≤ ∫ z, w z * ‖ω.floerLinearizationAdjoint
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2 :=
    integral_nonneg fun z ↦ by have := hw z; positivity
  have hY : 0 ≤ ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * (Re + 1 + 1))},
      ‖η z‖ ^ 2 := setIntegral_nonneg_of_ae_restrict (ae_of_all _ fun _ ↦ by positivity)
  nlinarith [hend hη hηc, hcore hη hηc, mul_le_mul_of_nonneg_left hmono hC₁,
    mul_nonneg hC₂ hX, mul_nonneg hC₁ hX, mul_nonneg hC₂ hY]

/-- **The semi-Fredholm estimate of the formal adjoint on the positive PSS plane.** Let `u` be a
`C¹` map on the positive PSS plane along which `J` is `C¹` and compatible, and which is `C²` on a
part `‖z‖ > exp (2π r)` of the end and solves there the Floer equation for the perturbation of a
jointly `C²` period-one Hamiltonian `H` with globally Lipschitz suspended vector field. Suppose
that, with `φ(s, t) = exp (2π (s + i t))` the end lift, the loops `t ↦ u(φ(s, t))` converge
uniformly as `s → ∞` to an orbit `x` of `H` starting at a nondegenerate fixed point of the
time-one map, while the slice defect `∂t (u ∘ φ) - X_{H_t}(u ∘ φ)` tends uniformly to zero, and
that from `s > r` on, `J(φ(s, t)) = J_e(t)` for a `C²` family `J_e` compatible along `x`. Then there
are `C ≥ 0` and `R` such that every `C²` covector field `η` of compact support satisfies

`∫_{s > R} (‖∂s η'‖² + ‖∂t η'‖² + ‖η'‖²) + ∫_{‖z‖ ≤ e^{2πR}} (‖∂s η‖² + ‖∂t η‖² + ‖η‖²)`
`  ≤ C (∫ ρ⁻¹ ‖D_u^* η‖² + ∫_{‖z‖ ≤ e^{2π (R + 1)}} ‖η‖²)`

for the formal adjoint `D_u^*` of the linearized Floer operator of the perturbation of the plane,
where `η' = η (φ ·) ∘ (a + b J)` is `η` read in end coordinates (`TauCeti.Floer.covectorPullback`),
the first integral is over `(R, ∞) × [0, 1]` in end coordinates and the other integrals over the
plane, and `ρ⁻¹ = 1 + ‖z‖²` is the inverse of the cylindrical weight
`TauCeti.Floer.PSSPlane.cylindricalWeight`. This is the counterpart, for the operator whose kernel
is the cokernel of `D_u`, of the semi-Fredholm estimate of `D_u` on a finite-energy PSS plane,
`exists_forall_le_mul_integral_floerLinearization_add_of_finite_energy`. -/
theorem exists_forall_le_mul_integral_floerLinearizationAdjoint_add_positive
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} (hH : Periodic H 1) (hHs : ContDiff ℝ 2 (uncurry H))
    {L : ℝ≥0} (hX : LipschitzWith L (ω.timeDependentHamiltonianSuspension H)) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Je : ℝ → V → AlmostComplexStructure V}
    (hJe : ContDiff ℝ 2 fun q : ℝ × V ↦ (Je q.1 q.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ t, ω.Compatible (Je t (x t))) {r : ℝ}
    (hJeq : ∀ ζ : ℝ × ℝ, r < ζ.1 → J (realChart positive.cylindricalEndLift ζ) = Je ζ.2)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ContDiff ℝ 1 u)
    (hu₂ : ∀ z, Real.exp (2 * π * r) < ‖Complex.equivRealProdCLM.symm z‖ → ContDiffAt ℝ 2 u z)
    (hc : ∀ z, ω.Compatible (J z (u z)))
    (hF : ∀ z, Real.exp (2 * π * r) < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
          z : ℝ × ℝ →ₗ[ℝ] V))
    (hux : TendstoUniformlyOn
      (fun s t ↦ u (realChart positive.cylindricalEndLift (s, t))) x atTop (Icc 0 1))
    (hδ : TendstoUniformlyOn (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t))
      (u ∘ realChart positive.cylindricalEndLift) (s, t)) 0 atTop (Icc 0 1)) :
    ∃ C, 0 ≤ C ∧ ∃ R : ℝ, ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → HasCompactSupport η →
      (∫ ζ in Ioi R ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback
          (realChart positive.cylindricalEndLift)
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ) +
        ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * R)},
          sobolevDensity η z ≤
        C * ((∫ z, (cylindricalWeight z)⁻¹ * ‖ω.floerLinearizationAdjoint
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u η z‖ ^ 2) +
          ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * (R + 1))},
            ‖η z‖ ^ 2) := by
  have hHs₂ : ContDiff ℝ (2 : ℕ∞) (uncurry H) := hHs.of_le (by norm_num)
  have hKs := fun z : ℝ × ℝ ↦ (contDiff_uncurry_perturbation (p := positive) hH hHs₂ 1).contDiffAt
    (x := (z, u z))
  have hKt := fun z : ℝ × ℝ ↦
    (contDiff_uncurry_perturbation (p := positive) hH hHs₂ Complex.I).contDiffAt (x := (z, u z))
  -- The inverse of the cylindrical weight is `1 + ‖z‖²`, continuous and at least `‖z‖²`.
  have hρ (z : ℝ × ℝ) :
      (cylindricalWeight z)⁻¹ = 1 + ‖Complex.equivRealProdCLM.symm z‖ ^ 2 := by
    rw [cylindricalWeight_apply, inv_inv]
  have hρc : Continuous fun z ↦ (cylindricalWeight z)⁻¹ := by
    simp only [hρ]
    fun_prop
  have hρ₀ (z : ℝ × ℝ) : 0 < (cylindricalWeight z)⁻¹ := by
    rw [hρ]
    positivity
  obtain ⟨Ce, Re, he⟩ :=
    ω.exists_forall_setIntegral_covectorPullback_le_mul_integral_floerLinearizationAdjoint_positive
      hH hHs hX hx hnd hJe hJex hJeq hu₂ (fun z _ ↦ hc z) hF hux hδ
  -- The end estimate with the weight `‖z‖²` gives the end estimate with the weight `ρ⁻¹`.
  have he' : ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → HasCompactSupport η →
      tsupport η ⊆ {z | Real.exp (2 * π * Re) < ‖Complex.equivRealProdCLM.symm z‖} →
      ∫ ζ in univ ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback
          (realChart positive.cylindricalEndLift)
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ ≤
        max Ce 0 * ∫ z, (cylindricalWeight z)⁻¹ * ‖ω.floerLinearizationAdjoint
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u η z‖ ^ 2 := by
    intro η hη hηc hηR
    have hint {w : ℝ × ℝ → ℝ} (hwc : Continuous w) :=
      ω.integrable_mul_norm_floerLinearizationAdjoint_sq
        (J := fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) isOpen_univ (fun z _ ↦ hJ z)
        (fun z _ ↦ hKs z) (fun z _ ↦ hKt z) (fun z _ ↦ hu.contDiffAt) hwc.continuousOn
        (hη.of_le one_le_two) subset_rfl hηc (subset_univ _)
    have hle := integral_mono
      (hint (w := fun z ↦ ‖Complex.equivRealProdCLM.symm z‖ ^ 2) (by fun_prop))
      (hint hρc) fun z ↦ mul_le_mul_of_nonneg_right
        (by rw [hρ]; linarith) (sq_nonneg _)
    refine (he hη hηc hηR).trans ((mul_le_mul_of_nonneg_right (le_max_left _ _)
      (integral_nonneg fun z ↦ by positivity)).trans
      (mul_le_mul_of_nonneg_left hle (le_max_right _ _)))
  obtain ⟨C, hC, R, hest⟩ := ω.exists_forall_le_mul_integral_floerLinearizationAdjoint_add_of_end
    positive hJ hKs hKt hu (fun z ↦ (hρ₀ z).le) hρc he' (fun z _ ↦ hρ₀ z) fun z _ ↦ hc z
  refine ⟨C, hC, R, fun η hη hηc ↦ ?_⟩
  have hset : {s : ℝ | R < positive.endSign * s} = Ioi R := by
    ext s
    simp
  simpa only [hset] using hest hη hηc


section FiniteEnergy

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The semi-Fredholm estimate of the formal adjoint on a finite-energy positive PSS plane.**
Let `u` be a `C¹` map, `C³` on a part `‖w‖ > r` of the end of the positive PSS plane, solving there
the Floer equation for the perturbation of a jointly `C³` period-one Hamiltonian `H` with globally
Lipschitz suspended vector field, with finite energy and values in a compact set `K` on which every
one-periodic orbit of `H` is nondegenerate. Let the structures `J` be `C¹` along `u` and compatible
along `u` on the disc `‖w‖ ≤ r`, and on the part `‖w‖ > r` of the end equal to a `C²` period-one
family `J_q(t)` read in the angular coordinate, with `J_q` compatible on `K`. Then there are
`C ≥ 0` and `R` such that every `C²` covector field `η` of compact support satisfies

`∫_{s > R} (‖∂s η'‖² + ‖∂t η'‖² + ‖η'‖²) + ∫_{‖w‖ ≤ e^{2πR}} (‖∂s η‖² + ‖∂t η‖² + ‖η‖²)`
`  ≤ C (∫ ρ⁻¹ ‖D_u^* η‖² + ∫_{‖w‖ ≤ e^{2π (R + 1)}} ‖η‖²)`

for the formal adjoint `D_u^*` of the linearized Floer operator of the datum
`(J, positive.perturbation H)`, where `η' = η (φ ·) ∘ (a + b J)` is `η` read in the cylinder
coordinates of the end lift `φ` (`TauCeti.Floer.covectorPullback`) and `ρ⁻¹ = 1 + ‖w‖²` is the
inverse of the cylindrical weight `TauCeti.Floer.PSSPlane.cylindricalWeight`. The end of a
finite-energy plane converges to a nondegenerate orbit
(`exists_tendstoUniformlyOn_sliceDefect_of_finite_energy`), which gives the hypotheses of
`exists_forall_le_mul_integral_floerLinearizationAdjoint_add_positive`. Every PSS plane is the
positive plane for the Hamiltonian `ε H(ε t)` (`TauCeti.Floer.PSSPlane.perturbation_eq_positive`),
so the estimate applies to the negative plane as well. This is the counterpart for `D_u^*` of
`exists_forall_le_mul_integral_floerLinearization_add_of_finite_energy`. -/
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
        C * ((∫ z, (cylindricalWeight z)⁻¹ * ‖ω.floerLinearizationAdjoint
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u η z‖ ^ 2) +
          ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * (R + 1))},
            ‖η z‖ ^ 2) := by
  have hΩ : IsOpen {z : ℝ × ℝ | r < ‖Complex.equivRealProdCLM.symm z‖} :=
    isOpen_lt continuous_const (by fun_prop)
  -- The end converges to a nondegenerate orbit `x`.
  obtain ⟨x, hxper, hx, hxK, a, hsub, hJeq, hux, hδ⟩ :=
    ω.exists_tendstoUniformlyOn_sliceDefect_of_finite_energy positive hH hHs hL hK hJq hJqper
      (fun t y hy ↦ (hJqK t y hy).tames) hJr hur huK hF hE hnd
  simp only [endSign_positive, one_mul] at hJeq hux hδ
  -- Compatibility on the disc `‖w‖ ≤ r`, and on the end from that of `J_q` on `K`.
  have hc' (z : ℝ × ℝ) : ω.Compatible (J z (u z)) := by
    rcases le_or_gt ‖Complex.equivRealProdCLM.symm z‖ r with hz | hz
    · exact hc z hz
    · rw [hJr z hz]
      exact hJqK _ _ (huK z hz)
  exact ω.exists_forall_le_mul_integral_floerLinearizationAdjoint_add_positive hH
    (hHs.of_le (by norm_num)) hL hx (hnd x hxper hx hxK) hJq (fun t ↦ hJqK t _ (hxK t)) hJeq hJ
    hu (fun z hz ↦ (hur.contDiffAt (hΩ.mem_nhds (hsub hz))).of_le (by norm_num)) hc'
    (fun z hz ↦ hF z (hsub hz)) hux hδ

end FiniteEnergy

end TauCeti.SymplecticForm
