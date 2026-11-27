/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Plane.SemiFredholm.Adjoint
public import TauCeti.Geometry.Symplectic.Floer.Plane.Sobolev
public import TauCeti.Analysis.Fredholm.ClosedRange

import TauCeti.Algebra.Order.Floor.Ring
import TauCeti.Analysis.Calculus.BumpFunction.LipschitzCutoff
import TauCeti.Geometry.Symplectic.Floer.Plane.Curvature
import TauCeti.Geometry.Symplectic.Floer.Plane.SemiFredholm
import TauCeti.Topology.Constructions.SumProd
import TauCeti.Geometry.Symplectic.Floer.Transversality.Conformal
import TauCeti.Geometry.Symplectic.Floer.SemiFredholm.Adjoint
import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Integral.DominatedConvergence

/-!
# The linearized operator of a PSS plane is Fredholm

Let `u` be a map of the plane `ℂ ≅ ℝ × ℝ` into a finite-dimensional symplectic inner product
space `(V, ω)`, and let `D_u : W^{1,2}(ℂ, V) → L²(ℂ, V)` be the realization
(`TauCeti.SymplecticForm.floerConformalSobolevOperator` for the cylindrical weight
`TauCeti.Floer.PSSPlane.cylindricalWeight`) of the linearized Floer operator of the perturbed
Cauchy–Riemann equation of a PSS plane. Its finite-dimensional kernel and closed range come from
the semi-Fredholm estimate of `D_u`
(`TauCeti.SymplecticForm.finiteDimensional_ker_floerConformalSobolevOperator_pssPlane`,
`TauCeti.SymplecticForm.isClosed_range_floerConformalSobolevOperator_pssPlane`). This file proves
that its cokernel is finite-dimensional, from the semi-Fredholm estimate of the formal adjoint
`D_u^*`
(`TauCeti.SymplecticForm.exists_forall_le_mul_integral_floerLinearizationAdjoint_add_positive`),
so that `D_u` is Fredholm.

* **Cokernel elements are regular.** An element `h ∈ L²(ℂ, V)` orthogonal to the range of `D_u`
  annihilates `D_u ξ` for every test section `ξ`, so the covector field `⟪h, ·⟫` is a weak
  cokernel element. When the data are regular enough it agrees almost everywhere with a `C²`
  covector field `η` with `D_u^* η = 0`
  (`TauCeti.SymplecticForm.exists_contDiffOn_ae_eq_forall_floerLinearizationAdjoint_eq_zero`, on
  every conformal domain, applied here to the plane).
* **The `L²` norm of a cokernel element lives on a disc.** The adjoint estimate holds for
  covector fields of compact support. Applied to `χ_n η` for the radial cutoffs `χ_n` of the disc
  `‖w‖ ≤ n` (`TauCeti.exists_contDiff_cutoff_comp_continuousLinearMap`), whose derivatives have
  size `O(1/n)` on the annulus `n ≤ ‖w‖ ≤ 2n`, the weighted term
  `∫ (1 + ‖w‖²) ‖D_u^* (χ_n η)‖²` is at most a constant times the tail `∫_{‖w‖ ≥ n} ‖η‖²`,
  which tends to zero. On the end the `W^{1,2}` energy of the pullback
  `η' = η (φ ·) ∘ (a + b J)` controls the `L²` norm of `η`, inverting `a + b J`
  (`TauCeti.AlmostComplexStructure.mul_opNorm_le_opNorm_comp_smul_add_smul`) and changing
  variables along the end lift `φ`. Letting `n → ∞` gives `∫ ‖η‖² ≤ A ∫_{‖w‖ ≤ b} ‖η‖²`.
* **Peetre's argument.** By the adjoint estimate on discs, the jets of the cut-off cokernel
  elements are bounded in `W^{1,2}`, so their restrictions to the disc `‖w‖ ≤ b` form a compact
  family (Rellich's theorem,
  `TauCeti.ConformalSobolev.isCompactOperator_restrictWeightedValue_comp_subtypeL`).
  An infinite-dimensional cokernel would contain a sequence of vectors of norm at most some
  `R > 1` at mutual distance at least one, two of which are close on the disc, hence everywhere:
  so the orthogonal complement of the range is finite-dimensional
  (`finiteDimensional_orthogonal_range_floerConformalSobolevOperator_positive`, in the namespace
  `TauCeti.SymplecticForm`), and `D_u` is Fredholm
  (`TauCeti.SymplecticForm.isFredholm_floerConformalSobolevOperator_positive`).
* **Finite-energy planes.** Along a finite-energy solution of the Floer equation of the positive
  PSS plane with nondegenerate asymptotic orbit, both estimates hold, and `D_u` is Fredholm
  (`TauCeti.SymplecticForm.isFredholm_floerConformalSobolevOperator_of_finite_energy_positive`).
  Every PSS plane is the positive plane for a rescaled Hamiltonian
  (`TauCeti.Floer.PSSPlane.perturbation_eq_positive`).

The target is a symplectic vector space. The index of `D_u` is not treated here.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  Fredholm theory of the perturbed planes of the PSS maps.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 3.1 and Appendices B and C, on the formal adjoint, the
  regularity of its weak solutions and the Fredholm property of real Cauchy–Riemann operators on
  punctured Riemann surfaces.
-/

public section

open Set Function Filter MeasureTheory Real
open scoped ENNReal NNReal Manifold Topology InnerProductSpace
open TauCeti.Complex (realChart contDiff_realChart)

namespace TauCeti

namespace SymplecticForm

open Floer Floer.PSSPlane ConformalSobolev

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-! ### The `L²` norm of a cokernel element is controlled on a disc -/

section Estimate

variable {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}

/-- The pullback `g' = g (φ ·) ∘ (a + b J)` of a `C¹` covector field `g` of compact support to the
end of the positive plane has integrable `W^{1,2}` energy density on every half-cylinder
`s > R`, `0 ≤ t ≤ 1`, when `J` is `C¹` along a `C¹` map `u`. -/
private theorem integrableOn_sobolevDensity_covectorPullback_positive
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ContDiff ℝ 1 u) {g : ℝ × ℝ → V →L[ℝ] ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (R : ℝ) :
    IntegrableOn (sobolevDensity (covectorPullback (realChart positive.cylindricalEndLift)
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u g)) (Ioi R ×ˢ Icc 0 1) := by
  set φ := realChart positive.cylindricalEndLift
  set J' : ℝ × ℝ → V → V →L[ℝ] V := fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap
  have hφ : ContDiff ℝ 2 φ := contDiff_realChart positive.contDiff_cylindricalEndLift
  -- The pulled-back field is `C¹`, since `J` is `C¹` along `u`, and it vanishes far out on the
  -- end.
  have hP : ContDiff ℝ 1 (covectorPullback φ J' u g) := by
    refine contDiff_covectorPullback_of_contDiffOn isOpen_univ (fun ζ _ ↦ ?_)
      (hg.comp (hφ.of_le one_le_two)) (subset_univ _)
    have hdφ : ContDiff ℝ 1 fun ζ ↦ fderiv ℝ φ ζ stdComplexLineReal :=
      (hφ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
    have hJu : ContDiffAt ℝ 1 (fun ζ ↦ J' (φ ζ) (u (φ ζ))) ζ :=
      (hJ (φ ζ)).comp (f := fun ζ ↦ (φ ζ, u (φ ζ))) ζ
        ((hφ.of_le one_le_two).contDiffAt.prodMk (hu.comp (hφ.of_le one_le_two)).contDiffAt)
    exact (((contDiff_fst.comp hdφ).contDiffAt.smul
      (contDiffAt_const (c := (1 : V →L[ℝ] V)))).add
      ((contDiff_snd.comp hdφ).contDiffAt.smul hJu)).contDiffWithinAt
  obtain ⟨N, hN⟩ := positive.exists_eventuallyEq_zero_comp_realChart_cylindricalEndLift hgc
  exact integrableOn_sobolevDensity_of_eventuallyEq_zero (continuous_sobolevDensity hP)
    (N := N) (fun ζ hζ ↦ (hN ζ (by rwa [endSign_positive, one_mul])).mono fun ζ' h ↦
      covectorPullback_eq_zero_of_apply_eq_zero φ J' u h) R

/-- Pointwise on the end of the positive plane, `det (dφ) ‖g (φ ζ)‖² ≤ (1 + B)² ‖g'(ζ)‖²` for the
pullback `g' = g (φ ·) ∘ (a + b J)`, when `‖J‖ ≤ B` at `φ ζ`: invert `a + b J`, with
`a² + b² = det (dφ)`. -/
private theorem det_mul_norm_sq_le_mul_norm_covectorPullback_sq {B : ℝ}
    {g : ℝ × ℝ → V →L[ℝ] ℝ} (ζ : ℝ × ℝ)
    (hB : ‖(J (realChart positive.cylindricalEndLift ζ)
      (u (realChart positive.cylindricalEndLift ζ))).toLinearMap.toContinuousLinearMap‖ ≤ B) :
    (fderiv ℝ (realChart positive.cylindricalEndLift) ζ).det *
        ‖g (realChart positive.cylindricalEndLift ζ)‖ ^ 2 ≤
      (1 + B) ^ 2 * ‖covectorPullback (realChart positive.cylindricalEndLift)
        (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u g ζ‖ ^ 2 := by
  set φ := realChart positive.cylindricalEndLift
  set J' : ℝ × ℝ → V → V →L[ℝ] V := fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap
  set NJ := ‖(J (φ ζ) (u (φ ζ))).toLinearMap.toContinuousLinearMap‖
  have hdet := positive.det_fderiv_realChart_cylindricalEndLift_pos ζ
  have hJζ := (J (φ ζ) (u (φ ζ))).mul_opNorm_le_opNorm_comp_smul_add_smul (g (φ ζ))
    (a := (fderiv ℝ φ ζ stdComplexLineReal).1) (b := (fderiv ℝ φ ζ stdComplexLineReal).2)
    (r := √(fderiv ℝ φ ζ).det)
    (by rw [Real.sq_sqrt hdet.le]; exact positive.sq_add_sq_fderiv_realChart_cylindricalEndLift ζ)
    (Real.sqrt_pos.2 hdet)
  rw [← covectorPullback_apply φ J' u g ζ] at hJζ
  have h3 : 0 ≤ 1 + NJ := by positivity
  calc (fderiv ℝ φ ζ).det * ‖g (φ ζ)‖ ^ 2 =
        (√(fderiv ℝ φ ζ).det * ‖g (φ ζ)‖) * (√(fderiv ℝ φ ζ).det * ‖g (φ ζ)‖) := by
        rw [mul_mul_mul_comm, Real.mul_self_sqrt hdet.le, sq]
    _ ≤ ((1 + NJ) * ‖covectorPullback φ J' u g ζ‖) * ((1 + NJ) * ‖covectorPullback φ J' u g ζ‖) :=
        mul_le_mul hJζ hJζ (by positivity) (by positivity)
    _ = (1 + NJ) ^ 2 * ‖covectorPullback φ J' u g ζ‖ ^ 2 := by ring
    _ ≤ (1 + B) ^ 2 * ‖covectorPullback φ J' u g ζ‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h3 (by linarith) 2) (sq_nonneg _)

/-- **The `L²` norm on the end from the pulled-back field.** If `‖J(z, u z)‖ ≤ B` everywhere, then
for a `C¹` covector field `g` of compact support, the `L²` norm of `g` on the part
`‖w‖ > exp (2π R)` of the plane is at most `(1 + B)²` times the `W^{1,2}` energy of its pullback
`g' = g (φ ·) ∘ (a + b J)` on the half-cylinder `s > R`, `0 ≤ t ≤ 1` of the end of the positive
plane, `φ` its end lift. -/
private theorem setIntegral_norm_sq_le_mul_setIntegral_sobolevDensity_covectorPullback
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ContDiff ℝ 1 u) {B : ℝ}
    (hB : ∀ z, ‖(J z (u z)).toLinearMap.toContinuousLinearMap‖ ≤ B)
    {g : ℝ × ℝ → V →L[ℝ] ℝ} (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (R : ℝ) :
    ∫ z in {z : ℝ × ℝ | Real.exp (2 * π * R) < ‖Complex.equivRealProdCLM.symm z‖}, ‖g z‖ ^ 2 ≤
      (1 + B) ^ 2 * ∫ ζ in Ioi R ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback
        (realChart positive.cylindricalEndLift)
        (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u g) ζ := by
  set φ := realChart positive.cylindricalEndLift
  set J' : ℝ × ℝ → V → V →L[ℝ] V := fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap
  have hS : MeasurableSet (Ioi R ×ˢ Ico (0 : ℝ) 1) := measurableSet_Ioi.prod measurableSet_Ico
  have hφ : ContDiff ℝ 2 φ := contDiff_realChart positive.contDiff_cylindricalEndLift
  have hint' : IntegrableOn (fun ζ ↦ (1 + B) ^ 2 * sobolevDensity (covectorPullback φ J' u g) ζ)
      (Ioi R ×ˢ Icc 0 1) :=
    (integrableOn_sobolevDensity_covectorPullback_positive hJ hu hg hgc R).const_mul _
  -- Change variables along the end lift, which is injective on the half-strip.
  have hIoi : {s : ℝ | R < positive.endSign * s} = Ioi R := by
    ext s
    simp [endSign_positive]
  rw [← positive.image_realChart_cylindricalEndLift_prod_Ico, hIoi,
    integral_image_eq_integral_of_eq_abs_det_smul hS
    ((positive.injOn_realChart_cylindricalEndLift 0).mono
      (prod_mono (subset_univ _) (by rw [zero_add])))
    (fun ζ _ ↦ (hφ.differentiable (by norm_num)) ζ) (fun ζ _ ↦ rfl), ← integral_const_mul]
  refine (integral_mono_of_nonneg (ae_of_all _ fun ζ ↦ by positivity)
    (hint'.mono_set (prod_mono subset_rfl Ico_subset_Icc_self))
    ((ae_restrict_iff' hS).2 (ae_of_all _ fun ζ _ ↦ ?_))).trans
    (setIntegral_mono_set hint' (ae_of_all _ fun ζ ↦ by
      have := sobolevDensity_nonneg (covectorPullback φ J' u g) ζ
      positivity) (ae_of_all _ (prod_mono subset_rfl Ico_subset_Icc_self)))
  rw [smul_eq_mul, abs_of_pos (positive.det_fderiv_realChart_cylindricalEndLift_pos ζ)]
  refine (det_mul_norm_sq_le_mul_norm_covectorPullback_sq ζ (hB _)).trans
    (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rw [sobolevDensity_apply]
  nlinarith [sq_nonneg ‖fderiv ℝ (covectorPullback φ J' u g) ζ stdComplexLineReal‖,
    sq_nonneg ‖fderiv ℝ (covectorPullback φ J' u g) ζ stdComplexLineImag‖]

/-- **The adjoint on a cut-off cokernel element.** Let `D^* η = 0` and `‖J(z, u z)‖ ≤ B`, and let
`χ` be a cutoff whose derivative vanishes off the annulus `n ≤ ‖w‖ ≤ 2n`, `n ≥ 1`, and has norm at
most `M / n`. Then `(1 + ‖w‖²) ‖D^* (χ η)‖² ≤ 5 (M (1 + B))² ‖η‖²`, and the left side vanishes on
the disc `‖w‖ < n`. -/
private theorem inv_mul_norm_floerLinearizationAdjoint_smul_sq_le (ω : SymplecticForm V)
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ContDiff ℝ 1 u) {B : ℝ}
    (hB : ∀ z, ‖(J z (u z)).toLinearMap.toContinuousLinearMap‖ ≤ B)
    {η : ℝ × ℝ → V →L[ℝ] ℝ} (hη : ContDiff ℝ 1 η)
    (hD : ∀ z, ω.floerLinearizationAdjoint (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      Ks Kt u η z = 0)
    {χ : ℝ × ℝ → ℝ} (hχ : ContDiff ℝ 1 χ) {M n : ℝ} (hn : 1 ≤ n)
    (hχ0 : ∀ z, ‖Complex.equivRealProdCLM.symm z‖ < n → fderiv ℝ χ z = 0)
    (hχ2 : ∀ z, 2 * n < ‖Complex.equivRealProdCLM.symm z‖ → fderiv ℝ χ z = 0)
    (hχM : ∀ z, ‖fderiv ℝ χ z‖ ≤ M / n) (z : ℝ × ℝ) :
    (PSSPlane.cylindricalWeight z)⁻¹ * ‖ω.floerLinearizationAdjoint
        (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u
        (fun z ↦ χ z • η z) z‖ ^ 2 ≤
      5 * (M * (1 + B)) ^ 2 *
        {z : ℝ × ℝ | n ≤ ‖Complex.equivRealProdCLM.symm z‖}.indicator (fun z ↦ ‖η z‖ ^ 2) z := by
  set J' : ℝ × ℝ → V → V →L[ℝ] V := fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap
  set ν := ‖Complex.equivRealProdCLM.symm z‖
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB z)
  have hJu : DifferentiableAt ℝ (fun w ↦ J' w (u w)) z :=
    ((hJ z).comp₂ contDiffAt_id hu.contDiffAt).differentiableAt one_ne_zero
  -- `‖D^* (χ η)‖ ≤ ‖dχ‖ (1 + B) ‖η‖`, since `D^* η = 0`.
  have hle : ‖ω.floerLinearizationAdjoint J' Ks Kt u (fun z ↦ χ z • η z) z‖ ≤
      ‖fderiv ℝ χ z‖ * (1 + B) * ‖η z‖ := by
    refine (ω.norm_floerLinearizationAdjoint_fun_smul_le (Ks := Ks) (Kt := Kt)
      ((hχ.differentiable one_ne_zero) z) ((hη.differentiable one_ne_zero) z) hJu).trans ?_
    rw [hD z, norm_zero, mul_zero, zero_add]
    gcongr
    exact hB z
  have hρ : (PSSPlane.cylindricalWeight z)⁻¹ = 1 + ν ^ 2 := inv_cylindricalWeight z
  by_cases hz : n ≤ ν ∧ ν ≤ 2 * n
  · rw [indicator_of_mem (show z ∈ {z : ℝ × ℝ | n ≤ ‖Complex.equivRealProdCLM.symm z‖} from hz.1)]
    have h1 : ‖ω.floerLinearizationAdjoint J' Ks Kt u (fun z ↦ χ z • η z) z‖ ^ 2 ≤
        (M / n * (1 + B) * ‖η z‖) ^ 2 := by
      refine pow_le_pow_left₀ (norm_nonneg _) (hle.trans ?_) 2
      gcongr
      exact hχM z
    have h2 : (PSSPlane.cylindricalWeight z)⁻¹ ≤ 5 * n ^ 2 := by
      rw [hρ]
      nlinarith [hz.2, hz.1]
    calc _ ≤ 5 * n ^ 2 * (M / n * (1 + B) * ‖η z‖) ^ 2 :=
          mul_le_mul h2 h1 (by positivity) (by positivity)
      _ = 5 * (M * (1 + B)) ^ 2 * ‖η z‖ ^ 2 := by field_simp
  · -- Off the annulus the derivative of `χ` vanishes.
    have hd : fderiv ℝ χ z = 0 := by
      rcases not_and_or.1 hz with h | h
      · exact hχ0 z (not_le.1 h)
      · exact hχ2 z (not_le.1 h)
    have h0 : ω.floerLinearizationAdjoint J' Ks Kt u (fun z ↦ χ z • η z) z = 0 := by
      simpa [hd] using hle
    rw [h0, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
    exact mul_nonneg (by positivity) (indicator_nonneg (fun _ _ ↦ by positivity) _)

omit [FiniteDimensional ℝ V] in
/-- If `g = η` on the disc `‖w‖ ≤ n`, then on every measurable set the `L²` norm of `η` is at most
that of `g` plus the `L²` norm of `η` on `‖w‖ ≥ n`. -/
private theorem setIntegral_norm_sq_le_setIntegral_add {η g : ℝ × ℝ → V →L[ℝ] ℝ} {n : ℝ}
    {S : Set (ℝ × ℝ)} (hηi : Integrable fun z ↦ ‖η z‖ ^ 2)
    (hgi : Integrable fun z ↦ ‖g z‖ ^ 2)
    (hgη : ∀ z, ‖Complex.equivRealProdCLM.symm z‖ ≤ n → g z = η z) :
    ∫ z in S, ‖η z‖ ^ 2 ≤ (∫ z in S, ‖g z‖ ^ 2) +
      ∫ z in {z : ℝ × ℝ | n ≤ ‖Complex.equivRealProdCLM.symm z‖}, ‖η z‖ ^ 2 := by
  set T := {z : ℝ × ℝ | n ≤ ‖Complex.equivRealProdCLM.symm z‖}
  have hT : MeasurableSet T :=
    measurableSet_le measurable_const Complex.equivRealProdCLM.symm.continuous.norm.measurable
  have hind : Integrable (T.indicator fun z ↦ ‖η z‖ ^ 2) := hηi.indicator hT
  calc ∫ z in S, ‖η z‖ ^ 2 ≤ ∫ z in S, (‖g z‖ ^ 2 + T.indicator (fun z ↦ ‖η z‖ ^ 2) z) := by
        refine setIntegral_mono hηi.integrableOn (hgi.integrableOn.add hind.integrableOn)
          fun z ↦ ?_
        by_cases hz : z ∈ T
        · rw [indicator_of_mem hz]
          linarith [sq_nonneg ‖g z‖]
        · rw [indicator_of_notMem hz, hgη z (not_le.1 hz).le, add_zero]
    _ = (∫ z in S, ‖g z‖ ^ 2) + ∫ z in S, T.indicator (fun z ↦ ‖η z‖ ^ 2) z :=
        integral_add hgi.integrableOn hind.integrableOn
    _ ≤ (∫ z in S, ‖g z‖ ^ 2) + ∫ z in T, ‖η z‖ ^ 2 := by
        gcongr
        rw [← integral_indicator hT]
        exact setIntegral_le_integral hind (ae_of_all _ (indicator_nonneg fun z _ ↦ by positivity))

/-- **The weighted adjoint of a cut-off cokernel element.** Under the hypotheses of
`inv_mul_norm_floerLinearizationAdjoint_smul_sq_le`, for square-integrable `η`,
`∫ (1 + ‖w‖²) ‖D^* (χ η)‖² ≤ 5 (M (1 + B))² ∫_{‖w‖ ≥ n} ‖η‖²`. -/
private theorem integral_inv_mul_norm_floerLinearizationAdjoint_smul_sq_le (ω : SymplecticForm V)
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ContDiff ℝ 1 u) {B : ℝ}
    (hB : ∀ z, ‖(J z (u z)).toLinearMap.toContinuousLinearMap‖ ≤ B)
    {η : ℝ × ℝ → V →L[ℝ] ℝ} (hη : ContDiff ℝ 1 η)
    (hD : ∀ z, ω.floerLinearizationAdjoint (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      Ks Kt u η z = 0) (hηi : Integrable fun z ↦ ‖η z‖ ^ 2)
    {χ : ℝ × ℝ → ℝ} (hχ : ContDiff ℝ 1 χ) {M n : ℝ} (hn : 1 ≤ n)
    (hχ0 : ∀ z, ‖Complex.equivRealProdCLM.symm z‖ < n → fderiv ℝ χ z = 0)
    (hχ2 : ∀ z, 2 * n < ‖Complex.equivRealProdCLM.symm z‖ → fderiv ℝ χ z = 0)
    (hχM : ∀ z, ‖fderiv ℝ χ z‖ ≤ M / n) :
    ∫ z, (PSSPlane.cylindricalWeight z)⁻¹ * ‖ω.floerLinearizationAdjoint
        (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u
        (fun z ↦ χ z • η z) z‖ ^ 2 ≤
      5 * (M * (1 + B)) ^ 2 *
        ∫ z in {z : ℝ × ℝ | n ≤ ‖Complex.equivRealProdCLM.symm z‖}, ‖η z‖ ^ 2 := by
  have hT : MeasurableSet {z : ℝ × ℝ | n ≤ ‖Complex.equivRealProdCLM.symm z‖} :=
    measurableSet_le measurable_const Complex.equivRealProdCLM.symm.continuous.norm.measurable
  rw [← integral_indicator hT, ← integral_const_mul]
  refine integral_mono_of_nonneg (ae_of_all _ fun z ↦ ?_) ((hηi.indicator hT).const_mul _)
    (ae_of_all _ fun z ↦ inv_mul_norm_floerLinearizationAdjoint_smul_sq_le ω hJ hu hB hη hD hχ hn
      hχ0 hχ2 hχM z)
  have := (PSSPlane.isWeight_cylindricalWeight.pos z (mem_univ z)).le
  positivity

omit [FiniteDimensional ℝ V] in
/-- If `g = η` on the disc `‖w‖ ≤ a`, the `L²` norm of `η` there is at most the `W^{1,2}` energy of
`g` there. -/
private theorem setIntegral_norm_sq_le_setIntegral_sobolevDensity {η g : ℝ × ℝ → V →L[ℝ] ℝ}
    (hηi : Integrable fun z ↦ ‖η z‖ ^ 2) (hg : ContDiff ℝ 1 g) {a : ℝ}
    (hgη : ∀ z, ‖Complex.equivRealProdCLM.symm z‖ ≤ a → g z = η z) :
    ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ a}, ‖η z‖ ^ 2 ≤
      ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ a}, sobolevDensity g z :=
  setIntegral_mono_on hηi.integrableOn
    ((continuous_sobolevDensity hg).continuousOn.integrableOn_compact
      (isCompact_setOf_norm_equivRealProdCLM_symm_le _))
    (isCompact_setOf_norm_equivRealProdCLM_symm_le _).measurableSet fun z hz ↦ by
      rw [sobolevDensity_apply, hgη z hz]
      nlinarith [sq_nonneg ‖fderiv ℝ g z stdComplexLineReal‖,
        sq_nonneg ‖fderiv ℝ g z stdComplexLineImag‖]

/-- The arithmetic closing the `L²` estimate: if `X = X₀ + X₁` with `X₀ ≤ D`,
`X₁ ≤ (1 + B)² E + t`, `E, D, T, P ≥ 0`, `E + D ≤ C (T + P)` and `T ≤ c t`, then
`X ≤ max 1 (1 + B)² max C 0 (c t + P) + t`. -/
private theorem le_max_mul_mul_add_add {X X₀ X₁ D E t T P B C c : ℝ} (hX : X = X₀ + X₁)
    (hX₀ : X₀ ≤ D) (hX₁ : X₁ ≤ (1 + B) ^ 2 * E + t) (hE : 0 ≤ E) (hD : 0 ≤ D) (hT0 : 0 ≤ T)
    (hP : 0 ≤ P) (hest : E + D ≤ C * (T + P)) (hT : T ≤ c * t) :
    X ≤ max 1 ((1 + B) ^ 2) * max C 0 * (c * t + P) + t := by
  set m := max 1 ((1 + B) ^ 2)
  have hm1 : 1 ≤ m := le_max_left _ _
  have hmB : (1 + B) ^ 2 ≤ m := le_max_right _ _
  have hfin : D + (1 + B) ^ 2 * E ≤ m * (E + D) := by nlinarith
  have h1 : C * (T + P) ≤ max C 0 * (T + P) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
  have h2 : max C 0 * (T + P) ≤ max C 0 * (c * t + P) :=
    mul_le_mul_of_nonneg_left (by linarith) (le_max_right _ _)
  nlinarith [mul_le_mul_of_nonneg_left ((hest.trans h1).trans h2) (by linarith : (0 : ℝ) ≤ m)]

/-- **The `L²` norm of a cokernel element is controlled on a disc.** Let `J` be `C¹` and `K_s`,
`K_t` be `C²` along a `C¹` map `u`, with `‖J(z, u z)‖ ≤ B`, and let the formal adjoint `D_u^*` of
the linearized Floer operator satisfy the semi-Fredholm estimate of the positive PSS plane: for some
`C` and `R`, every `C²` covector field `η` of compact support satisfies

`∫_{s > R} (‖∂s η'‖² + ‖∂t η'‖² + ‖η'‖²) + ∫_{‖w‖ ≤ e^{2πR}} (‖∂s η‖² + ‖∂t η‖² + ‖η‖²)`
`  ≤ C (∫ (1 + ‖w‖²) ‖D_u^* η‖² + ∫_{‖w‖ ≤ e^{2π (R + 1)}} ‖η‖²)`,

with `η'` the pullback of `η` to the end (`TauCeti.Floer.covectorPullback`). Then there is `A ≥ 0`
such that every square-integrable `C²` covector field `η` with `D_u^* η = 0` satisfies
`∫ ‖η‖² ≤ A ∫_{‖w‖ ≤ e^{2π (R + 1)}} ‖η‖²`. The estimate is applied to the cut-off fields `χ_n η`,
whose adjoint is supported on the annulus `n ≤ ‖w‖ ≤ 2n` and tends to zero in the weighted `L²`
norm. -/
private theorem exists_integral_norm_sq_le_of_floerLinearizationAdjoint_eq_zero
    (ω : SymplecticForm V)
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ContDiff ℝ 1 u) {B : ℝ}
    (hB : ∀ z, ‖(J z (u z)).toLinearMap.toContinuousLinearMap‖ ≤ B) {C R : ℝ}
    (hadj : ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → HasCompactSupport η →
      (∫ ζ in Ioi R ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback
          (realChart positive.cylindricalEndLift)
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ) +
        ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * R)},
          sobolevDensity η z ≤
        C * ((∫ z, (PSSPlane.cylindricalWeight z)⁻¹ * ‖ω.floerLinearizationAdjoint
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2) +
          ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * (R + 1))},
            ‖η z‖ ^ 2)) :
    ∃ A, 0 ≤ A ∧ ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η →
      (∀ z, ω.floerLinearizationAdjoint (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
        Ks Kt u η z = 0) → Integrable (fun z ↦ ‖η z‖ ^ 2) →
      ∫ z, ‖η z‖ ^ 2 ≤
        A * ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * (R + 1))},
          ‖η z‖ ^ 2 := by
  set J' : ℝ × ℝ → V → V →L[ℝ] V := fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap
  set ν : ℝ × ℝ → ℝ := fun z ↦ ‖Complex.equivRealProdCLM.symm z‖
  set M := 2 * ‖(Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ)‖
  set m := max 1 ((1 + B) ^ 2)
  set c := 5 * (M * (1 + B)) ^ 2
  refine ⟨m * max C 0, mul_nonneg (le_max_of_le_left zero_le_one) (le_max_right _ _),
    fun η hη hD hηi ↦ ?_⟩
  set D₀ := {z : ℝ × ℝ | ν z ≤ Real.exp (2 * π * R)}
  set P := ∫ z in {z | ν z ≤ Real.exp (2 * π * (R + 1))}, ‖η z‖ ^ 2
  set tail : ℕ → ℝ := fun n ↦ ∫ z in {z | (n : ℝ) ≤ ν z}, ‖η z‖ ^ 2
  have htail : Tendsto tail atTop (𝓝 0) :=
    (tendsto_setIntegral_setOf_le hηi
      Complex.equivRealProdCLM.symm.continuous.norm.measurable).comp tendsto_natCast_atTop_atTop
  -- For every `n ≥ e^{2π (R + 1)}`, the estimate of the cut-off field `χ_n η` bounds `∫ ‖η‖²` by
  -- `m C (c tail_n + P) + tail_n`; letting `n → ∞` gives the claim.
  refine ge_of_tendsto
    (by simpa using (((htail.const_mul c).add_const P).const_mul (m * max C 0)).add htail) ?_
  filter_upwards [eventually_ge_atTop (⌈Real.exp (2 * π * (R + 1))⌉₊ + 1)] with n hn
  have hRn : Real.exp (2 * π * (R + 1)) ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast (Nat.le_succ _).trans hn)
  have hR0n : Real.exp (2 * π * R) ≤ n := (Real.exp_le_exp.2 (by nlinarith [pi_pos])).trans hRn
  obtain ⟨χ, hχs, -, hχ1, hχ0, hχd0, hχd2, hχM⟩ :=
    exists_contDiff_cutoff_comp_continuousLinearMap
      (Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ) (Nat.cast_pos.2 (le_of_add_le_right hn))
  set g : ℝ × ℝ → V →L[ℝ] ℝ := fun z ↦ χ z • η z
  have hg : ContDiff ℝ 2 g := (hχs.of_le (by simp)).smul hη
  have hgc : HasCompactSupport g :=
    HasCompactSupport.intro (isCompact_setOf_norm_equivRealProdCLM_symm_le (2 * n)) fun z hz ↦ by
      simp [g, hχ0 z (not_le.1 hz).le]
  have hgη (z : ℝ × ℝ) (hz : ν z ≤ n) : g z = η z := by simp [g, hχ1 z hz]
  have hgi : Integrable fun z ↦ ‖g z‖ ^ 2 :=
    Continuous.integrable_of_hasCompactSupport (f := fun z ↦ ‖g z‖ ^ 2)
      (hg.continuous.norm.pow 2) (hgc.comp_left (g := fun v : V →L[ℝ] ℝ ↦ ‖v‖ ^ 2) (by simp))
  have hP : ∫ z in {z | ν z ≤ Real.exp (2 * π * (R + 1))}, ‖g z‖ ^ 2 = P :=
    setIntegral_congr_fun (isCompact_setOf_norm_equivRealProdCLM_symm_le _).measurableSet
      fun z hz ↦ by simp only [hgη z (le_trans hz hRn)]
  have hest := hadj hg hgc
  rw [hP] at hest
  have hT := integral_inv_mul_norm_floerLinearizationAdjoint_smul_sq_le ω hJ hu hB
    (hη.of_le one_le_two) hD hηi (hχs.of_le (by simp)) (by exact_mod_cast le_of_add_le_right hn)
    hχd0 hχd2 hχM
  -- On the disc `D₀` the cutoff is `1`, and off it the cutoff costs at most the tail.
  have hDisc := setIntegral_norm_sq_le_setIntegral_sobolevDensity hηi (hg.of_le one_le_two)
    fun z hz ↦ hgη z (le_trans hz hR0n)
  have hEnd := setIntegral_norm_sq_le_setIntegral_add (S := D₀ᶜ) hηi hgi hgη
  have hEnd' := setIntegral_norm_sq_le_mul_setIntegral_sobolevDensity_covectorPullback hJ hu hB
    (hg.of_le one_le_two) hgc R
  rw [show {z : ℝ × ℝ | Real.exp (2 * π * R) < ν z} = D₀ᶜ by ext z; simp [D₀]] at hEnd'
  have hE0 : 0 ≤ ∫ ζ in Ioi R ×ˢ Icc (0 : ℝ) 1,
      sobolevDensity (covectorPullback (realChart positive.cylindricalEndLift) J' u g) ζ :=
    setIntegral_nonneg (measurableSet_Ioi.prod measurableSet_Icc) fun ζ _ ↦
      sobolevDensity_nonneg _ ζ
  exact le_max_mul_mul_add_add (integral_add_compl
    (isCompact_setOf_norm_equivRealProdCLM_symm_le (Real.exp (2 * π * R))).measurableSet hηi).symm
    hDisc (hEnd.trans (by linarith)) hE0 (setIntegral_nonneg
      (isCompact_setOf_norm_equivRealProdCLM_symm_le _).measurableSet fun z _ ↦
        sobolevDensity_nonneg _ z) (integral_nonneg fun z ↦ by
          have := (PSSPlane.isWeight_cylindricalWeight.pos z (mem_univ z)).le
          positivity) (setIntegral_nonneg
      (isCompact_setOf_norm_equivRealProdCLM_symm_le _).measurableSet fun z _ ↦ by positivity)
    hest hT

/-- **The weighted energy of a cut-off cokernel element.** Under the hypotheses of the estimate of
`D_u^*` on discs, with `J` compatible along `u` and `‖J(z, u z)‖ ≤ B`, let `χ` be a cutoff vanishing
off the disc `‖w‖ < 2n`, `n ≥ 1`, whose derivative vanishes off the annulus `n ≤ ‖w‖ ≤ 2n` and has
norm at most `M / n`. Then there is `K` such that for every square-integrable `C²` covector field
`η` with `D_u^* η = 0` the weighted `W^{1,2}` energy of `χ η` is at most `K ∫ ‖η‖²`. -/
private theorem exists_integral_weighted_smul_le (ω : SymplecticForm V)
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiff ℝ 1 u)
    (hc : ∀ z, ω.Compatible (J z (u z))) {B : ℝ}
    (hB : ∀ z, ‖(J z (u z)).toLinearMap.toContinuousLinearMap‖ ≤ B)
    {χ : ℝ × ℝ → ℝ} (hχ : ContDiff ℝ 2 χ) (hχ01 : ∀ z, χ z ∈ Icc 0 1) {M n : ℝ} (hn : 1 ≤ n)
    (hχ2n : ∀ z, 2 * n ≤ ‖Complex.equivRealProdCLM.symm z‖ → χ z = 0)
    (hχ0 : ∀ z, ‖Complex.equivRealProdCLM.symm z‖ < n → fderiv ℝ χ z = 0)
    (hχ2 : ∀ z, 2 * n < ‖Complex.equivRealProdCLM.symm z‖ → fderiv ℝ χ z = 0)
    (hχM : ∀ z, ‖fderiv ℝ χ z‖ ≤ M / n) :
    ∃ K, ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η →
      (∀ z, ω.floerLinearizationAdjoint (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
        Ks Kt u η z = 0) → Integrable (fun z ↦ ‖η z‖ ^ 2) →
      ∫ z, (PSSPlane.cylindricalWeight z * ‖χ z • η z‖ ^ 2 +
          ‖fderiv ℝ (fun z ↦ χ z • η z) z (1, 0)‖ ^ 2 +
          ‖fderiv ℝ (fun z ↦ χ z • η z) z (0, 1)‖ ^ 2) ≤ K * ∫ z, ‖η z‖ ^ 2 := by
  set J' : ℝ × ℝ → V → V →L[ℝ] V := fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap
  set ν : ℝ × ℝ → ℝ := fun z ↦ ‖Complex.equivRealProdCLM.symm z‖
  have hwc : Continuous fun z ↦ (PSSPlane.cylindricalWeight z)⁻¹ :=
    PSSPlane.continuous_inv_cylindricalWeight
  have hw0 (z : ℝ × ℝ) : 0 < (PSSPlane.cylindricalWeight z)⁻¹ := by
    rw [inv_cylindricalWeight]
    positivity
  obtain ⟨C', hC', hdisc⟩ :=
    ω.exists_forall_setIntegral_sobolevDensity_le_mul_integral_floerLinearizationAdjoint_add_of_lt
      hJ hKs hKt hu (fun z ↦ (hw0 z).le) hwc (fun z _ ↦ hw0 z) (fun z _ ↦ hc z)
      (show 2 * n < 2 * n + 1 by linarith)
  set c := 5 * (M * (1 + B)) ^ 2
  refine ⟨C' * (c + 1), fun η hη hD hηi ↦ ?_⟩
  set g : ℝ × ℝ → V →L[ℝ] ℝ := fun z ↦ χ z • η z
  have hg : ContDiff ℝ 2 g := hχ.smul hη
  have hg0 (z : ℝ × ℝ) (hz : 2 * n < ν z) : g =ᶠ[𝓝 z] 0 := by
    filter_upwards [(isOpen_lt continuous_const
      Complex.equivRealProdCLM.symm.continuous.norm).mem_nhds hz] with w hw
    simp [g, hχ2n w (le_of_lt hw)]
  have hgc : HasCompactSupport g :=
    HasCompactSupport.intro (isCompact_setOf_norm_equivRealProdCLM_symm_le (2 * n)) fun z hz ↦
      (hg0 z (not_le.1 hz)).self_of_nhds
  have hW := integral_weighted_le_setIntegral_sobolevDensity PSSPlane.continuous_cylindricalWeight
    (fun z ↦ by
      rw [PSSPlane.cylindricalWeight_apply]
      exact inv_le_one_of_one_le₀ (le_add_of_nonneg_right (sq_nonneg _)))
    (hg.of_le one_le_two) (isCompact_setOf_norm_equivRealProdCLM_symm_le (2 * n))
    fun z hz ↦ hg0 z (not_le.1 hz)
  -- The adjoint term and the `L²` term are controlled by `∫ ‖η‖²`.
  have hT : ∫ z, (PSSPlane.cylindricalWeight z)⁻¹ *
      ‖ω.floerLinearizationAdjoint J' Ks Kt u g z‖ ^ 2 ≤ c * ∫ z, ‖η z‖ ^ 2 :=
    (integral_inv_mul_norm_floerLinearizationAdjoint_smul_sq_le ω hJ hu hB (hη.of_le one_le_two)
      hD hηi (hχ.of_le one_le_two) hn hχ0 hχ2 hχM).trans (mul_le_mul_of_nonneg_left
        (setIntegral_le_integral hηi (ae_of_all _ fun z ↦ by positivity)) (by positivity))
  have hL : ∫ z in {z | ν z ≤ 2 * n + 1}, ‖g z‖ ^ 2 ≤ ∫ z, ‖η z‖ ^ 2 := by
    refine (setIntegral_mono_on ((hg.continuous.norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_setOf_norm_equivRealProdCLM_symm_le _)) hηi.integrableOn
      (isCompact_setOf_norm_equivRealProdCLM_symm_le _).measurableSet fun z _ ↦ ?_).trans
      (setIntegral_le_integral hηi (ae_of_all _ fun z ↦ by positivity))
    have h01 := hχ01 z
    simp only [g, Pi.pow_apply, norm_smul, Real.norm_eq_abs]
    rw [mul_pow, sq_abs]
    exact mul_le_of_le_one_left (sq_nonneg _) (by nlinarith [h01.1, h01.2])
  calc _ ≤ ∫ z in {z | ν z ≤ 2 * n}, sobolevDensity g z := hW
    _ ≤ C' * ((∫ z, (PSSPlane.cylindricalWeight z)⁻¹ *
          ‖ω.floerLinearizationAdjoint J' Ks Kt u g z‖ ^ 2) +
        ∫ z in {z | ν z ≤ 2 * n + 1}, ‖g z‖ ^ 2) := hdisc hg hgc
    _ ≤ C' * (c * (∫ z, ‖η z‖ ^ 2) + ∫ z, ‖η z‖ ^ 2) := by gcongr
    _ = C' * (c + 1) * ∫ z, ‖η z‖ ^ 2 := by ring

end Estimate

/-! ### The cokernel is finite-dimensional -/

section Fredholm

variable {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}

omit [FiniteDimensional ℝ V] in
/-- For `A ≥ 0`, `ε = (A |B| + 1)⁻¹` satisfies `A |B| ε² < 1`. -/
private theorem mul_abs_mul_inv_sq_lt_one {A B : ℝ} (hA : 0 ≤ A) :
    A * |B| * ((A * |B| + 1)⁻¹) ^ 2 < 1 := by
  have hpos : 0 < A * |B| + 1 := by positivity
  have hε1 : (A * |B| + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [abs_nonneg B])
  have h1 : A * |B| * (A * |B| + 1)⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one hpos]
    linarith
  calc A * |B| * ((A * |B| + 1)⁻¹) ^ 2 = A * |B| * (A * |B| + 1)⁻¹ * (A * |B| + 1)⁻¹ := by ring
    _ ≤ A * |B| * (A * |B| + 1)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hε1 (by positivity)
    _ < 1 := by linarith

/-- **Two cokernel elements close on a disc are close.** Let `η₁`, `η₂` be `C²` representatives
of `h₁, h₂ ∈ L²(ℂ, V)` annihilated by `D_u^*`, and let the `L²` estimate of cokernel elements on the
disc `K_b` hold with constant `A`. If cutoffs `g_i` of `η_i` agree with them on `K_b` and the `L²`
norm of `g₁ - g₂` on `K_b` is at most `B ε²`, then `‖h₁ - h₂‖² ≤ A |B| ε²`. -/
private theorem norm_sub_sq_le_of_setIntegral_le (ω : SymplecticForm V)
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ContDiff ℝ 1 u) {Kb : Set (ℝ × ℝ)} (hKb : MeasurableSet Kb) {A : ℝ} (hA : 0 ≤ A)
    (hglob : ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η →
      (∀ z, ω.floerLinearizationAdjoint (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
        Ks Kt u η z = 0) → Integrable (fun z ↦ ‖η z‖ ^ 2) →
      ∫ z, ‖η z‖ ^ 2 ≤ A * ∫ z in Kb, ‖η z‖ ^ 2)
    {h₁ h₂ : Lp V 2 (volume.restrict (univ : Set (ℝ × ℝ)))} {η₁ η₂ g₁ g₂ : ℝ × ℝ → V →L[ℝ] ℝ}
    (hη₁ : ContDiff ℝ 2 η₁) (hη₂ : ContDiff ℝ 2 η₂)
    (hae₁ : (fun z ↦ innerSL ℝ (h₁ z)) =ᵐ[volume] η₁)
    (hae₂ : (fun z ↦ innerSL ℝ (h₂ z)) =ᵐ[volume] η₂)
    (hD₁ : ∀ z, ω.floerLinearizationAdjoint (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      Ks Kt u η₁ z = 0)
    (hD₂ : ∀ z, ω.floerLinearizationAdjoint (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      Ks Kt u η₂ z = 0)
    (hg₁ : ∀ z ∈ Kb, g₁ z = η₁ z) (hg₂ : ∀ z ∈ Kb, g₂ z = η₂ z) {B ε : ℝ}
    (hsmall : ∫ z in Kb, ‖(g₁ - g₂) z‖ ^ 2 ≤ B * ε ^ 2) :
    ‖h₁ - h₂‖ ^ 2 ≤ A * |B| * ε ^ 2 := by
  have hJu (z : ℝ × ℝ) : DifferentiableAt ℝ
      (fun w ↦ (J w (u w)).toLinearMap.toContinuousLinearMap) z :=
    ((hJ z).comp₂ contDiffAt_id hu.contDiffAt).differentiableAt one_ne_zero
  -- The difference `h₁ - h₂` is represented by `η₁ - η₂`, annihilated by `D_u^*`.
  have hae : (fun z ↦ innerSL ℝ ((h₁ - h₂) z)) =ᵐ[volume] η₁ - η₂ := by
    have hsub := (ae_restrict_iff' MeasurableSet.univ).1 (Lp.coeFn_sub h₁ h₂)
    filter_upwards [hsub, hae₁, hae₂] with z h1 h2 h3
    rw [h1 (mem_univ z), Pi.sub_apply, map_sub, h2, h3, Pi.sub_apply]
  obtain ⟨hdn, hdi⟩ : ∫ z, ‖(η₁ - η₂) z‖ ^ 2 = ‖h₁ - h₂‖ ^ 2 ∧
      Integrable fun z ↦ ‖(η₁ - η₂) z‖ ^ 2 := by
    simpa only [Measure.restrict_univ] using
      Lp.integral_norm_sq_eq_and_integrable_of_ae_eq_innerSL (ae_restrict_of_ae hae)
  have hdD (z : ℝ × ℝ) : ω.floerLinearizationAdjoint
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u (η₁ - η₂) z = 0 := by
    rw [floerLinearizationAdjoint_sub ((hη₁.differentiable (by norm_num)) z)
      ((hη₂.differentiable (by norm_num)) z) (hJu z), hD₁ z, hD₂ z, sub_zero]
  have hKeq : ∫ z in Kb, ‖(g₁ - g₂) z‖ ^ 2 = ∫ z in Kb, ‖(η₁ - η₂) z‖ ^ 2 :=
    setIntegral_congr_fun hKb fun z hz ↦ by simp [hg₁ z hz, hg₂ z hz]
  rw [← hdn]
  calc _ ≤ A * ∫ z in Kb, ‖(η₁ - η₂) z‖ ^ 2 := hglob (hη₁.sub hη₂) hdD hdi
    _ ≤ A * (|B| * ε ^ 2) := by
        rw [← hKeq]
        exact mul_le_mul_of_nonneg_left (hsmall.trans (mul_le_mul_of_nonneg_right
          (le_abs_self B) (sq_nonneg ε))) hA
    _ = A * |B| * ε ^ 2 := by ring

/-- **The cokernel of the linearized operator of a PSS plane is finite-dimensional.** Let `J` be
`C³` and `K_s`, `K_t` be `C⁴` at the points `(z, u z)` along a `C³` map `u`, with `J` compatible
along `u` and `‖J(z, u z)‖ ≤ B`, and let the coefficient field of `D_u` on conformal jets be
essentially bounded. Suppose that the formal adjoint `D_u^*` satisfies the semi-Fredholm estimate
of the positive PSS plane (as in
`TauCeti.SymplecticForm.exists_forall_le_mul_integral_floerLinearizationAdjoint_add_positive`).
Then the orthogonal complement of the range of the realization
`D_u : W^{1,2}(ℂ, V) → L²(ℂ, V)` is finite-dimensional. -/
theorem finiteDimensional_orthogonal_range_floerConformalSobolevOperator_positive
    (ω : SymplecticForm V)
    (hJ : ∀ z, ContDiffAt ℝ 3
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 4 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 4 (uncurry Kt) (z, u z)) (hu : ContDiff ℝ 3 u)
    (hc : ∀ z, ω.Compatible (J z (u z))) {B : ℝ}
    (hB : ∀ z, ‖(J z (u z)).toLinearMap.toContinuousLinearMap‖ ≤ B)
    (hM : MemLp (ω.floerConformalJetCoeff PSSPlane.cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u) ∞ (volume.restrict univ))
    {C R : ℝ}
    (hadj : ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → HasCompactSupport η →
      (∫ ζ in Ioi R ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback
          (realChart positive.cylindricalEndLift)
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ) +
        ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * R)},
          sobolevDensity η z ≤
        C * ((∫ z, (PSSPlane.cylindricalWeight z)⁻¹ * ‖ω.floerLinearizationAdjoint
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2) +
          ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * (R + 1))},
            ‖η z‖ ^ 2)) :
    FiniteDimensional ℝ (ω.floerConformalSobolevOperator univ PSSPlane.cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u).rangeᗮ := by
  set J' : ℝ × ℝ → V → V →L[ℝ] V := fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap
  set ρ := PSSPlane.cylindricalWeight
  have hρ : IsWeight univ ρ := PSSPlane.isWeight_cylindricalWeight
  have hJ1 (z : ℝ × ℝ) : ContDiffAt ℝ 1 (uncurry J') (z, u z) := (hJ z).of_le (by norm_num)
  have hKs2 (z : ℝ × ℝ) : ContDiffAt ℝ 2 (uncurry Ks) (z, u z) := (hKs z).of_le (by norm_num)
  have hKt2 (z : ℝ × ℝ) : ContDiffAt ℝ 2 (uncurry Kt) (z, u z) := (hKt z).of_le (by norm_num)
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  -- The constants: the `L²` estimate on a disc, the cutoff, the weighted energy of cut-off
  -- cokernel elements, and the compact restriction to the disc `‖w‖ ≤ b`.
  obtain ⟨A, hA0, hglob⟩ :=
    exists_integral_norm_sq_le_of_floerLinearizationAdjoint_eq_zero ω hJ1 hu1 hB hadj
  set b := Real.exp (2 * π * (R + 1))
  set n₁ : ℕ := ⌈b⌉₊ + 1
  have hn₁ : 1 ≤ n₁ := Nat.le_add_left 1 _
  have hbn : b ≤ n₁ := (Nat.le_ceil b).trans (by exact_mod_cast Nat.le_succ _)
  obtain ⟨χ, hχs, hχ01, hχ1, hχ0, hχd0, hχd2, hχM⟩ :=
    exists_contDiff_cutoff_comp_continuousLinearMap
      (Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ) (Nat.cast_pos.2 hn₁)
  have hχ2 : ContDiff ℝ 2 χ := hχs.of_le (by simp)
  obtain ⟨K, hK⟩ := exists_integral_weighted_smul_le ω hJ1 hKs2 hKt2 hu1 hc hB hχ2 hχ01
    (by exact_mod_cast hn₁) hχ0 hχd0 hχd2 hχM
  set Kb := {z : ℝ × ℝ | ‖Complex.equivRealProdCLM.symm z‖ ≤ b}
  have hKb : IsCompact Kb := isCompact_setOf_norm_equivRealProdCLM_symm_le b
  obtain ⟨B', hB'⟩ :=
    exists_setIntegral_norm_sq_le_mul_norm_restrictWeightedValue_sq (V := V →L[ℝ] ℝ) hρ hKb
      (subset_univ _)
  have hcpt := isCompactOperator_restrictWeightedValue_comp_subtypeL (V := V →L[ℝ] ℝ) hρ hKb
    (subset_univ _)
  -- An infinite-dimensional cokernel contains vectors of norm at most `Rr` at mutual distance ≥ 1.
  by_contra hfin
  obtain ⟨Rr, f, -, hfR, hsep⟩ := exists_seq_norm_le_one_le_norm_sub hfin
  have hreg (k : ℕ) : ∃ η : ℝ × ℝ → V →L[ℝ] ℝ, ContDiff ℝ 2 η ∧
      (fun z ↦ innerSL ℝ ((f k : Lp V 2 (volume.restrict (univ : Set (ℝ × ℝ)))) z)) =ᵐ[volume] η ∧
      ∀ z, ω.floerLinearizationAdjoint J' Ks Kt u η z = 0 := by
    obtain ⟨η, hη, hae, hD⟩ := ω.exists_contDiffOn_ae_eq_forall_floerLinearizationAdjoint_eq_zero
      (J := J') (u := u) hρ (fun z _ ↦ hJ z) (fun z _ ↦ (J z (u z)).toContinuousLinearMap_mul_self)
      (fun z _ ↦ hKs z) (fun z _ ↦ hKt z) (fun z _ ↦ hu.contDiffAt) hM (f k).property
    exact ⟨η, contDiffOn_univ.1 hη, ((ae_restrict_iff' MeasurableSet.univ).1 hae).mono
      fun z hz ↦ hz (mem_univ z), fun z ↦ hD z (mem_univ z)⟩
  choose η hηs hηae hηD using hreg
  -- The jets of their cut-offs are bounded in `W^{1,2}`.
  set g : ℕ → ℝ × ℝ → V →L[ℝ] ℝ := fun k z ↦ χ z • η k z
  have hg (k : ℕ) : ContDiff ℝ 2 (g k) := hχ2.smul (hηs k)
  have hgT (k : ℕ) : g k ∈ testSection (V →L[ℝ] ℝ) univ := by
    refine mem_testSection_iff.2 ⟨hg k, HasCompactSupport.intro
      (isCompact_setOf_norm_equivRealProdCLM_symm_le (2 * n₁)) fun z hz ↦ ?_, subset_univ _⟩
    simp [g, hχ0 z (not_le.1 hz).le]
  set x : ℕ → H1 (V →L[ℝ] ℝ) univ ρ := fun k ↦ ⟨(memLp_jet hρ (hgT k)).toLp (jet ρ (g k)),
    jetSubmodule_le_H1 (toLp_jet_mem_jetSubmodule hρ (hgT k))⟩
  have hxb (k : ℕ) : ‖x k‖ ≤ √(max K 0 * Rr ^ 2) := by
    rw [← Submodule.norm_coe]
    exact norm_toLp_jet_le_of_ae_eq hρ (hηae k) (hgT k) (by rw [Submodule.norm_coe]; exact hfR k)
      (hK (hηs k) (hηD k))
  -- By Rellich's theorem two of them are close on the disc, hence close everywhere.
  obtain ⟨k, l, hkl, hdist⟩ := hcpt.exists_dist_lt_of_norm_le hxb
    (by positivity : 0 < (A * |B'| + 1)⁻¹)
  rw [dist_eq_norm, ← map_sub] at hdist
  have hjet := toLp_jet_sub_ae_eq hρ (hgT k) (hgT l)
  have hgη (k : ℕ) (z : ℝ × ℝ) (hz : z ∈ Kb) : g k z = η k z := by
    simp [g, hχ1 z (le_trans hz hbn)]
  have hle := norm_sub_sq_le_of_setIntegral_le ω hJ1 hu1 hKb.measurableSet hA0 hglob (hηs k)
    (hηs l) (hηae k) (hηae l) (hηD k) (hηD l) (hgη k) (hgη l)
    (B := |B'|) ((hB' ((hg k).continuous.sub (hg l).continuous).continuousOn hjet).trans
      ((mul_le_mul_of_nonneg_right (le_abs_self B') (sq_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hdist.le 2) (abs_nonneg _))))
  rw [← Submodule.coe_sub, Submodule.norm_coe, abs_abs] at hle
  have := hsep hkl.ne
  nlinarith [mul_abs_mul_inv_sq_lt_one (B := B') hA0]

/-- **The linearized operator of a PSS plane is Fredholm.** Let `J` be `C³` and `K_s`, `K_t` be
`C⁴` at the points `(z, u z)` along a `C³` map `u`, with `J` compatible along `u` and
`‖J(z, u z)‖ ≤ B`, and let the coefficient field of `D_u` on conformal jets be essentially bounded.
If `D_u` satisfies the semi-Fredholm estimate of the positive PSS plane (as in
`TauCeti.SymplecticForm.exists_forall_le_mul_integral_floerLinearization_add_of_finite_energy`)
and its formal adjoint `D_u^*` satisfies the corresponding estimate (as in
`TauCeti.SymplecticForm.exists_forall_le_mul_integral_floerLinearizationAdjoint_add_positive`),
then the realization `D_u : W^{1,2}(ℂ, V) → L²(ℂ, V)` is Fredholm. The kernel and the closed range
come from the estimate of `D_u`, the finite cokernel from that of `D_u^*`: the orthogonal
complement of the range is finite-dimensional (the theorem
`finiteDimensional_orthogonal_range_floerConformalSobolevOperator_positive` of this namespace). -/
theorem isFredholm_floerConformalSobolevOperator_positive (ω : SymplecticForm V)
    (hJ : ∀ z, ContDiffAt ℝ 3
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 4 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 4 (uncurry Kt) (z, u z)) (hu : ContDiff ℝ 3 u)
    (hc : ∀ z, ω.Compatible (J z (u z))) {B : ℝ}
    (hB : ∀ z, ‖(J z (u z)).toLinearMap.toContinuousLinearMap‖ ≤ B)
    (hM : MemLp (ω.floerConformalJetCoeff PSSPlane.cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u) ∞ (volume.restrict univ))
    {C R : ℝ} (hest : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      (∫ ζ in {s : ℝ | R < positive.endSign * s} ×ˢ Icc (0 : ℝ) 1,
          (‖fderiv ℝ (ξ ∘ realChart positive.cylindricalEndLift) ζ stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ (ξ ∘ realChart positive.cylindricalEndLift) ζ stdComplexLineImag‖ ^ 2 +
            ‖(ξ ∘ realChart positive.cylindricalEndLift) ζ‖ ^ 2)) +
        ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * R)},
          (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 +
            ‖ξ z‖ ^ 2) ≤
        C * ((∫ z, ‖ω.floerLinearization (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
          Ks Kt u ξ z‖ ^ 2) +
          ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * (R + 1))},
            ‖ξ z‖ ^ 2))
    {C' R' : ℝ}
    (hadj : ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → HasCompactSupport η →
      (∫ ζ in Ioi R' ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback
          (realChart positive.cylindricalEndLift)
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ) +
        ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * R')},
          sobolevDensity η z ≤
        C' * ((∫ z, (PSSPlane.cylindricalWeight z)⁻¹ * ‖ω.floerLinearizationAdjoint
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2) +
          ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * (R' + 1))},
            ‖η z‖ ^ 2)) :
    (ω.floerConformalSobolevOperator univ PSSPlane.cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u).IsFredholm := by
  set D := ω.floerConformalSobolevOperator univ PSSPlane.cylindricalWeight
    (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u
  rw [TauCeti.isFredholm_iff_finite_ker_coker]
  refine ⟨finiteDimensional_ker_floerConformalSobolevOperator_pssPlane ω positive hM hest, ?_⟩
  -- The range is closed, so the cokernel is the orthogonal complement of the range.
  have hcl := isClosed_range_floerConformalSobolevOperator_pssPlane ω positive hM hest
  rw [← ContinuousLinearMap.coe_coe, ← LinearMap.coe_range] at hcl
  have : CompleteSpace D.range := hcl.completeSpace_coe
  have := finiteDimensional_orthogonal_range_floerConformalSobolevOperator_positive ω hJ hKs hKt
    hu hc hB hM hadj
  exact (Submodule.quotientEquivOfIsCompl D.range D.rangeᗮ
    (Submodule.isCompl_orthogonal _)).symm.finiteDimensional

/-- On the end of the positive plane, the slice defect of a map `u` read in end coordinates has
period one in the angular coordinate, for a Hamiltonian of period one. -/
private theorem sliceDefect_comp_realChart_positive_add_one (ω : SymplecticForm V)
    {H : ℝ → V → ℝ} (hH : Periodic H 1) (u : ℝ × ℝ → V) (s t : ℝ) :
    sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t))
        (u ∘ realChart positive.cylindricalEndLift) (s, t + 1) =
      sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t))
        (u ∘ realChart positive.cylindricalEndLift) (s, t) := by
  set v := u ∘ realChart positive.cylindricalEndLift
  have hv : (fun ζ : ℝ × ℝ ↦ v (ζ + (0, 1))) = v := funext fun ζ ↦ by
    have h : ζ + (0, 1) = (ζ.1, ζ.2 + 1) := by ext <;> simp
    simp only [v, comp_apply, h]
    exact congrArg u (realChart_positive_add_one ζ.1 ζ.2)
  have hd : fderiv ℝ v ((s, t) + (0, 1)) = fderiv ℝ v (s, t) := by
    rw [← fderiv_comp_add_right, hv]
  have hval : v ((s, t) + (0, 1)) = v (s, t) := congrFun hv (s, t)
  simp only [Prod.mk_add_mk, add_zero] at hd hval
  rw [sliceDefect_def, sliceDefect_def, hd, hval, hH t]

/-- **`J` is bounded along `u`** when it is continuous along a continuous `u`, and equal on the end
`‖w‖ > r` to a continuous family `J_q(t)` of period one while `u` takes values in a compact set. -/
private theorem exists_forall_norm_le_of_end {K : Set V} (hK : IsCompact K)
    {Jq : ℝ → V → AlmostComplexStructure V}
    (hJq : Continuous fun q : ℝ × V ↦ (Jq q.1 q.2).toLinearMap.toContinuousLinearMap)
    (hJqper : Periodic Jq 1) {J : ℝ × ℝ → V → AlmostComplexStructure V} {r : ℝ}
    {u : ℝ × ℝ → V}
    (hJ : ∀ z, ContinuousAt
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : Continuous u)
    (hJr : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      J z = Jq (positive.endCoord (Complex.equivRealProdCLM.symm z)).im)
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K) :
    ∃ B, ∀ z, ‖(J z (u z)).toLinearMap.toContinuousLinearMap‖ ≤ B := by
  obtain ⟨BK, hBK⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    (hJq.continuousOn (s := Icc (0 : ℝ) 1 ×ˢ K))
  obtain ⟨B₀, hB₀⟩ := (isCompact_setOf_norm_equivRealProdCLM_symm_le r).exists_bound_of_continuousOn
    (continuous_comp_prodMk_of_continuousAt hJ hu).continuousOn
  refine ⟨max B₀ BK, fun z ↦ ?_⟩
  rcases le_or_gt ‖Complex.equivRealProdCLM.symm z‖ r with hz | hz
  · exact (hB₀ z hz).trans (le_max_left _ _)
  · -- On the end, `J_q(t) = J_q(t - ⌊t⌋)` with `t - ⌊t⌋ ∈ [0, 1]`.
    set t := (positive.endCoord (Complex.equivRealProdCLM.symm z)).im
    rw [hJr z hz, ← hJqper.apply_fract t]
    exact (hBK (Int.fract t, u z) ⟨⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩,
      huK z hz⟩).trans (le_max_right _ _)

/-- If the slice defects of `u` on the end of the positive plane tend uniformly to zero over
`t ∈ [0, 1]`, they are at most `1` far out on the end, for every `t`, since they have period one
in `t`. -/
private theorem exists_forall_norm_sliceDefect_le_one (ω : SymplecticForm V) {H : ℝ → V → ℝ}
    (hH : Periodic H 1) {u : ℝ × ℝ → V}
    (hδ : TendstoUniformlyOn (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t))
      (u ∘ realChart positive.cylindricalEndLift) (s, t)) 0 atTop (Icc 0 1)) :
    ∃ T₀, ∀ ζ : ℝ × ℝ, T₀ ≤ ζ.1 → ‖sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t))
      (u ∘ realChart positive.cylindricalEndLift) ζ‖ ≤ 1 := by
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 ((Metric.tendstoUniformlyOn_iff.1 hδ) 1 one_pos)
  refine ⟨T₀, ?_⟩
  rintro ⟨s, t⟩ (hs : T₀ ≤ s)
  have hper : Periodic (fun t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t))
      (u ∘ realChart positive.cylindricalEndLift) (s, t)) 1 :=
    fun t ↦ sliceDefect_comp_realChart_positive_add_one ω hH u s t
  have h := hT₀ s hs (Int.fract t) ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  rw [Pi.zero_apply, dist_zero_left] at h
  rw [← hper.apply_fract t]
  exact h.le

/-- **The linearized operator along a finite-energy PSS plane is Fredholm.** Let `H` be a `C⁴`
Hamiltonian of period one in time, with globally Lipschitz suspended vector field, whose
one-periodic orbits in a compact set `K` are nondegenerate. Let `u` be a `C³` map of the plane that
solves the Floer equation of the positive PSS plane for `H` on the end `‖w‖ > r`, with finite
energy there and values in `K`, for almost complex structures `J` that are `C³` along `u`, equal on
the end to a `C²` family `J_q(t)` of period one compatible with `ω` on `K`, and compatible along `u`
on the disc `‖w‖ ≤ r`. Then the realization `D_u : W^{1,2}(ℂ, V) → L²(ℂ, V)` of the linearized
Floer operator is Fredholm. Every PSS plane is the positive plane for a rescaled Hamiltonian
(`TauCeti.Floer.PSSPlane.perturbation_eq_positive`), so this covers the negative plane as well. -/
theorem isFredholm_floerConformalSobolevOperator_of_finite_energy_positive
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} (hH : Periodic H 1) (hHs : ContDiff ℝ 4 (uncurry H))
    {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H)) {K : Set V}
    (hK : IsCompact K) {Jq : ℝ → V → AlmostComplexStructure V}
    (hJq : ContDiff ℝ 2 fun q : ℝ × V ↦ (Jq q.1 q.2).toLinearMap.toContinuousLinearMap)
    (hJqper : Periodic Jq 1) (hJqK : ∀ t, ∀ y ∈ K, ω.Compatible (Jq t y))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {r : ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ z, ContDiffAt ℝ 3
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hJr : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      J z = Jq (positive.endCoord (Complex.equivRealProdCLM.symm z)).im)
    (hu : ContDiff ℝ 3 u)
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
    (ω.floerConformalSobolevOperator univ PSSPlane.cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      u).IsFredholm := by
  set φ := realChart positive.cylindricalEndLift
  have hHs3 : ContDiff ℝ 3 (uncurry H) := hHs.of_le (by norm_num)
  have hJ1 (z : ℝ × ℝ) : ContDiffAt ℝ 1
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z) :=
    (hJ z).of_le (by norm_num)
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  -- The two semi-Fredholm estimates of a finite-energy plane.
  obtain ⟨C, -, R, hest⟩ := ω.exists_forall_le_mul_integral_floerLinearization_add_of_finite_energy
    positive hH hHs3 hL hK hJq hJqper hJqK hJ1 hJr hu1 hu.contDiffOn hc huK hF hE hnd
  obtain ⟨C', -, R', hadj⟩ :=
    ω.exists_forall_le_mul_integral_floerLinearizationAdjoint_add_of_finite_energy_positive hH
      hHs3 hL hK hJq hJqper hJqK hJ1 hJr hu1 hu.contDiffOn hc huK hF hE hnd
  -- Compatibility along `u`: on the disc by hypothesis, on the end from that of `J_q` on `K`.
  have hc' (z : ℝ × ℝ) : ω.Compatible (J z (u z)) := by
    rcases le_or_gt ‖Complex.equivRealProdCLM.symm z‖ r with hz | hz
    · exact hc z hz
    · rw [hJr z hz]
      exact hJqK _ _ (huK z hz)
  -- `J` is bounded along `u`, and the coefficient field on conformal jets is bounded: far out on
  -- the end `u` stays in `K` and its slice defect is small, by the exponential decay of the end.
  obtain ⟨B, hB⟩ := exists_forall_norm_le_of_end hK hJq.continuous hJqper
    (fun z ↦ (hJ1 z).continuousAt) hu1.continuous hJr huK
  obtain ⟨x, -, -, -, a, hsub, hJeq, -, hδ⟩ :=
    ω.exists_tendstoUniformlyOn_sliceDefect_of_finite_energy positive hH hHs3 hL hK hJq hJqper
      (fun t y hy ↦ (hJqK t y hy).tames) hJr hu.contDiffOn huK hF hE hnd
  simp only [endSign_positive, one_mul] at hJeq hδ
  obtain ⟨T₀, hT₀⟩ := exists_forall_norm_sliceDefect_le_one ω hH hδ
  obtain ⟨Cu, hCu⟩ := hK.isBounded.exists_norm_le
  have hend (ζ : ℝ × ℝ) (hζ : max T₀ (a + 1) ≤ positive.endSign * ζ.1) :
      r < ‖Complex.equivRealProdCLM.symm (φ ζ)‖ := by
    rw [endSign_positive, one_mul] at hζ
    exact hsub (exp_lt_norm_realChart_positive (by linarith [le_max_right T₀ (a + 1)]))
  have hM := ω.memLp_floerConformalJetCoeff_pssPlane (p := positive) hH (hHs.of_le (by norm_num))
    hJ1 hu1 (hJq.of_le one_le_two) (T := max T₀ (a + 1))
    (fun ζ hζ ↦ hJeq ζ (by
      rw [endSign_positive, one_mul] at hζ
      linarith [le_max_right T₀ (a + 1)]))
    (fun ζ hζ ↦ hF _ (hend ζ hζ)) (Cu := Cu) (fun ζ hζ ↦ hCu _ (huK _ (hend ζ hζ)))
    (Cδ := 1) fun ζ hζ ↦ hT₀ ζ (by
      rw [endSign_positive, one_mul] at hζ
      exact (le_max_left _ _).trans hζ)
  have hKs (z : ℝ × ℝ) : ContDiffAt ℝ 4 (uncurry fun z x ↦
      positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1) (z, u z) :=
    (contDiff_uncurry_perturbation (p := positive) hH hHs 1).contDiffAt
  have hKt (z : ℝ × ℝ) : ContDiffAt ℝ 4 (uncurry fun z x ↦
      positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) (z, u z) :=
    (contDiff_uncurry_perturbation (p := positive) hH hHs Complex.I).contDiffAt
  exact isFredholm_floerConformalSobolevOperator_positive ω hJ hKs hKt hu hc' hB hM hest hadj

end Fredholm

end SymplecticForm

end TauCeti
