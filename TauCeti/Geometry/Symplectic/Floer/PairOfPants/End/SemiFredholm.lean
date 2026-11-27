/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.EndLinearization
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Linearization
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Density
import TauCeti.Algebra.Ring.Periodic
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Normed.Operator.Basic
import TauCeti.Geometry.Symplectic.Floer.SemiFredholm.Adjoint
import TauCeti.MeasureTheory.Function.Jacobian.Plane
import TauCeti.Topology.Instances.Real.TSupport
import TauCeti.Topology.UniformSpace.UniformConvergence.Bounded

/-!
# The end estimate of the linearized Floer operator on the pair of pants

Let `(V, ω)` be a finite-dimensional symplectic vector space and let `u` be a Floer pair of pants
for the pair-of-pants perturbation `TauCeti.Floer.pairOfPantsPerturbation` of period-one
Hamiltonians `H_q`, on `S = ℂ ∖ {0, 1}` in the real coordinates `ℝ × ℝ ≃ ℂ`. In the positive end
chart `φ'_q` (`TauCeti.Floer.positiveEndChart`) the end `q` is a Floer half-cylinder of the
positive end Hamiltonian `H'_q`, and at a nondegenerate asymptotic orbit the linearized operator
of the half-cylinder controls the whole `W^{1,2}` norm of sections supported far out on the end
(`exists_mem_forall_setIntegral_le_mul_setIntegral_norm_floerLinearization_sq`). This file
transfers that estimate to the linearized operator `D_u` of the pair of pants on `S`
(`exists_forall_setIntegral_comp_positiveEndChart_le_mul_integral_floerLinearization`): the energy
of a section `ξ` supported far out on the end, read in the end chart, is controlled by
`∫_S ‖D_u ξ‖²`. It is the end ingredient of the semi-Fredholm estimate of `D_u` in
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.SemiFredholm`.

Only the end matters: the estimate holds for Floer data whose perturbation agrees with the
pair-of-pants perturbation far out on the end, and for maps solving the Floer equation there. The
linearized operator at a point only depends on the data at that point
(`TauCeti.SymplecticForm.floerLinearization_congr_data`), so on sections supported far out on the
end it is the operator of the pair-of-pants data.

Read in the chart, the operator is `a D_u ξ - b J D_u ξ` for the complex derivative `a + i b` of
`φ'_q` (`floerLinearization_comp_positiveEndChart`), so its square norm is at most
`2 (1 + B)² (a² + b²) ‖D_u ξ‖²` where `‖J‖ ≤ B`; such a bound holds far out on the end because the
loops of `u` converge to the orbit. The factor `a² + b²` is the Jacobian determinant of `φ'_q`,
and changing variables along the chart, which is injective on `ℝ × (0, 1)`, bounds the integral
by `∫_S ‖D_u ξ‖²`.

The same holds for the formal adjoint `D_u^*` on covector fields, whose kernel is the cokernel of
`D_u` (`exists_forall_setIntegral_covectorPullback_le_mul_integral_floerLinearizationAdjoint`),
again for data that agree with the pair-of-pants data only far out on the end: on covector fields
supported there the two adjoints agree (`floerLinearizationAdjoint_congr_data_of_tsupport`). A
covector field `η` is read in the chart as the `(0, 1)`-form `η' = η (φ'_q ·) ∘ (a + b J)`
(`TauCeti.Floer.covectorPullback`), on which the adjoint of the half-cylinder is `a² + b²` times
`D_u^* η` (`floerLinearizationAdjoint_comp_positiveEndChart`). The end estimate of the adjoint on
the half-cylinder
(`TauCeti.SymplecticForm.exists_forall_setIntegral_le_mul_setIntegral_floerLinearizationAdjoint`)
then bounds the energy of `η'` by `∫_S |z - c_q|² ‖D_u^* η‖²`, for the center `c_q` of the end:
of the two factors `a² + b² = 4π² |z - c_q|²`, one is absorbed by the change of variables. The
weight `|z - c_q|²` is comparable to the inverse of the cylindrical weight of
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev` on the end, as for the dual of
`W^{1,2}`. Since the cylinder estimate is stated for `C²` fields, `J` and `u` are assumed `C²` far
out on the end, so that `η'` is `C²`.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the Fredholm theory of the pair-of-pants product.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1,
  on the semi-Fredholm estimate on punctured Riemann surfaces with cylindrical ends.
-/

public section

open Filter Function Set MeasureTheory TauCeti.ThricePuncturedSphere
open scoped Topology NNReal Manifold

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The operator in an end chart, pointwise.** Where `u` solves the Floer equation for the
pair-of-pants perturbation at `φ'_q(ζ)` with `ζ = (s, t)`, `s ≥ 2`, and `‖J‖ ≤ B` there, the
linearized operator read in the positive end chart satisfies
`‖D' (ξ ∘ φ'_q)‖² ≤ 2 (1 + B)² det (dφ'_q) ‖D_u ξ‖²` at `ζ`. -/
private theorem norm_floerLinearization_comp_positiveEndChart_sq_le (ω : SymplecticForm V)
    {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1) {q : Puncture}
    (hHs : ∀ t, ContDiff ℝ 2 (H q t)) {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {u ξ : ℝ × ℝ → V} {ζ : ℝ × ℝ} (hζ : 2 ≤ ζ.1) (hu : DifferentiableAt ℝ u (positiveEndChart q ζ))
    (hξ : DifferentiableAt ℝ ξ (positiveEndChart q ζ))
    (hfl : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (positiveEndChart q ζ) (u (positiveEndChart q ζ)))
      (ω.perturbedFDeriv
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
        (positiveEndChart q ζ) : ℝ × ℝ →ₗ[ℝ] V)) {B : ℝ}
    (hB : ‖(J (positiveEndChart q ζ) (u (positiveEndChart q ζ))).toLinearMap.toContinuousLinearMap‖
      ≤ B) :
    ‖ω.floerLinearization
        (fun ζ' y ↦ (J (positiveEndChart q ζ') y).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun ζ' ↦ positiveEndHamiltonian H q ζ'.2) (u ∘ positiveEndChart q)
        (ξ ∘ positiveEndChart q) ζ‖ ^ 2 ≤
      2 * (1 + B) ^ 2 * ((fderiv ℝ (positiveEndChart q) ζ).det *
        ‖ω.floerLinearization (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u ξ (positiveEndChart q ζ)‖ ^ 2) := by
  rw [ω.floerLinearization_comp_positiveEndChart hH hHs hζ hu hξ hfl, ContinuousLinearMap.det,
    (isComplexLinearMap_fderiv_positiveEndChart q ζ).det_eq_sq_add_sq,
    ContinuousLinearMap.coe_coe]
  set a := (fderiv ℝ (positiveEndChart q) ζ stdComplexLineReal).1
  set b := (fderiv ℝ (positiveEndChart q) ζ stdComplexLineReal).2
  set Jx := J (positiveEndChart q ζ) (u (positiveEndChart q ζ))
  set D := ω.floerLinearization (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
    (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    u ξ (positiveEndChart q ζ)
  have hB₀ : 0 ≤ B := (norm_nonneg _).trans hB
  have h := ContinuousLinearMap.norm_smul_add_smul_apply_sq_le _ hB a (-b) D
  rw [neg_sq, neg_smul, ← sub_eq_add_neg] at h
  refine h.trans ?_
  rw [← mul_assoc]
  gcongr
  nlinarith

/-- **Changing variables along an end chart.** For a nonnegative integrable function `g`, the
integral of `det (dφ'_q) · g ∘ φ'_q` over a finite band `[a, b] × [0, 1]` is at most the integral
of `g`. -/
private theorem setIntegral_det_mul_comp_positiveEndChart_le_integral {g : ℝ × ℝ → ℝ}
    (hg : ∀ z, 0 ≤ g z) (hgi : Integrable g) (q : Puncture) (a b : ℝ) :
    ∫ ζ in Icc a b ×ˢ Icc (0 : ℝ) 1, (fderiv ℝ (positiveEndChart q) ζ).det *
        g (positiveEndChart q ζ) ≤ ∫ z, g z := by
  have hs : MeasurableSet (Ioo a b ×ˢ Ioo (0 : ℝ) 1) := measurableSet_Ioo.prod measurableSet_Ioo
  calc _ = ∫ ζ in Ioo a b ×ˢ Ioo (0 : ℝ) 1, (fderiv ℝ (positiveEndChart q) ζ).det *
        g (positiveEndChart q ζ) := by
        refine setIntegral_congr_set ?_
        rw [Measure.volume_eq_prod]
        exact (Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc).symm
    _ = ∫ z in positiveEndChart q '' (Ioo a b ×ˢ Ioo (0 : ℝ) 1), g z :=
        (integral_image_eq_integral_of_eq_abs_det_smul hs
          ((injOn_positiveEndChart q 0).mono
            (prod_mono (subset_univ _) (by rw [zero_add]; exact Ioo_subset_Ico_self)))
          (fun ζ _ ↦ (contDiff_positiveEndChart q 1).differentiable one_ne_zero ζ)
          fun ζ _ ↦ by rw [abs_of_pos (det_fderiv_positiveEndChart_pos q ζ), smul_eq_mul]).symm
    _ ≤ _ := setIntegral_le_integral hgi (ae_of_all _ hg)

/-- **The operator of an end, read in its chart.** Far out on the end `q`, where `J` is the
cylindrical structure `J_q(t)` bounded by `B` along `u` and `u` solves the Floer equation for the
pair-of-pants perturbation, the `L²` norm over a band `[a, b] × [0, 1]` of the operator of the end
data along `u ∘ φ'_q` on `ξ ∘ φ'_q` is at most `2 (1 + B)²` times the `L²` norm of `D_u ξ` on
`S`. -/
private theorem setIntegral_norm_floerLinearization_comp_positiveEndChart_sq_le
    (ω : SymplecticForm V) {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) {q : Puncture}
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Je : ℝ → V → AlmostComplexStructure V}
    {R₁ : ℝ} (hJe : ContDiff ℝ 1 fun p : ℝ × V ↦ (Je p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJeq : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je ζ.2) {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z) {a b : ℝ}
    (hF : ∀ ζ : ℝ × ℝ, a ≤ ζ.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (positiveEndChart q ζ) (u (positiveEndChart q ζ))) (ω.perturbedFDeriv
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
        (positiveEndChart q ζ) : ℝ × ℝ →ₗ[ℝ] V)) {B R₃ : ℝ}
    (hB : ∀ ζ : ℝ × ℝ, R₃ ≤ ζ.1 → ζ.2 ∈ Icc (0 : ℝ) 1 →
      ‖(Je ζ.2 ((u ∘ positiveEndChart q) ζ)).toLinearMap.toContinuousLinearMap‖ ≤ B)
    {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 2 ξ) (hξc : HasCompactSupport ξ)
    (hξS : tsupport ξ ⊆ thricePuncturedSphereReal) (ha₁ : R₁ ≤ a) (ha₃ : R₃ ≤ a)
    (ha₂ : 2 ≤ a) :
    ∫ ζ in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization
        (fun w y ↦ (Je w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
        (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q)
        (ξ ∘ positiveEndChart q) ζ‖ ^ 2 ≤
      2 * (1 + B) ^ 2 * ∫ z, ‖ω.floerLinearization
        (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u ξ z‖ ^ 2 := by
  have hHt (t : ℝ) : ContDiff ℝ 2 (H q t) := (hHs q).comp (contDiff_const.prodMk contDiff_id)
  have hH' := contDiff_uncurry_positiveEndHamiltonian (hHs q)
  set D := ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
    (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u ξ
  have hDc : Continuous D := ω.continuous_floerLinearization_of_tsupport_subset hJ
    (fun z hz ↦ contDiffAt_uncurry_pairOfPantsPerturbation hH hHs hz (u z) 1)
    (fun z hz ↦ contDiffAt_uncurry_pairOfPantsPerturbation hH hHs hz (u z) Complex.I) hu
    (hξ.of_le one_le_two) hξS
  have hrect : IsCompact (Icc a b ×ˢ Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have hφS {ζ : ℝ × ℝ} (hζ : ζ ∈ Icc a b ×ˢ Icc (0 : ℝ) 1) :=
    positiveEndChart_mem_thricePuncturedSphereReal (q := q) (by linarith [hζ.1.1])
  -- The operator of the end data along `u ∘ φ'_q` is continuous on the band.
  have hDe : ContinuousOn (fun ζ ↦ ‖ω.floerLinearization
      (fun w y ↦ (Je w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
      (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q)
      (ξ ∘ positiveEndChart q) ζ‖ ^ 2) (Icc a b ×ˢ Icc (0 : ℝ) 1) := fun ζ hζ ↦
    ((ω.continuousAt_floerLinearization
      (J := fun w y ↦ (Je w.2 y).toLinearMap.toContinuousLinearMap) (Ks := fun _ _ ↦ 0)
      (Kt := fun w ↦ positiveEndHamiltonian H q w.2)
      (hJe.comp (contDiff_fst.snd.prodMk contDiff_snd)).contDiffAt contDiffAt_const
      (hH'.comp (contDiff_fst.snd.prodMk contDiff_snd)).contDiffAt
      ((hu _ (hφS hζ)).comp _ (contDiff_positiveEndChart q 1).contDiffAt)
      ((hξ.comp (contDiff_positiveEndChart q 2)).contDiffAt.of_le one_le_two)).norm.pow
        2).continuousWithinAt
  have hdet : Continuous fun ζ ↦ (fderiv ℝ (positiveEndChart q) ζ).det :=
    ContinuousLinearMap.continuous_det.comp
      ((contDiff_positiveEndChart q 1).continuous_fderiv one_ne_zero)
  have hφc : Continuous (positiveEndChart q) := (contDiff_positiveEndChart q 0).continuous
  refine le_trans ?_ (mul_le_mul_of_nonneg_left
    (setIntegral_det_mul_comp_positiveEndChart_le_integral (fun _ ↦ sq_nonneg (‖D _‖))
      (ω.integrable_norm_floerLinearization_sq hDc hξc) q a b) (by positivity))
  rw [← integral_const_mul]
  refine setIntegral_mono_on (hDe.integrableOn_compact hrect)
    ((by fun_prop : Continuous fun ζ ↦ 2 * (1 + B) ^ 2 *
      ((fderiv ℝ (positiveEndChart q) ζ).det * ‖D (positiveEndChart q ζ)‖ ^ 2)
      ).continuousOn.integrableOn_compact hrect)
    (measurableSet_Icc.prod measurableSet_Icc) fun ζ hζ ↦ ?_
  -- Beyond `R₁` the structure on the end is `Je`, so the two operators agree at `ζ`.
  rw [ω.floerLinearization_congr_data (J' := fun ζ' y ↦
    (J (positiveEndChart q ζ') y).toLinearMap.toContinuousLinearMap) _ _
    (by simp [hJeq ζ (ha₁.trans hζ.1.1)]) rfl rfl]
  refine ω.norm_floerLinearization_comp_positiveEndChart_sq_le hH hHt (ha₂.trans hζ.1.1)
    ((hu _ (hφS hζ)).differentiableAt one_ne_zero) (hξ.differentiable two_ne_zero _)
    (hF ζ hζ.1.1) ?_
  rw [hJeq ζ (ha₁.trans hζ.1.1)]
  exact hB ζ (ha₃.trans hζ.1.1) hζ.2

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- A section with compact support in the part `±s > R` of the end `q` vanishes in the positive
end chart outside a finite band `(R, b) × ℝ`. -/
private theorem exists_forall_comp_positiveEndChart_eq_zero {q : Puncture} {R : ℝ}
    {ξ : ℝ × ℝ → V} (hξc : HasCompactSupport ξ)
    (hξR : tsupport ξ ⊆ {z | z ∈ thricePuncturedSphereReal ∧ R < (positiveEndCoord q z).1}) :
    ∃ b, R ≤ b ∧ ∀ s t, s ∉ Ioo R b → (ξ ∘ positiveEndChart q) (s, t) = 0 := by
  obtain ⟨N, hN⟩ :=
    exists_forall_comp_positiveEndChart_eventuallyEq_zero hξc fun z hz ↦
      Puncture.ne_endCenter (mem_thricePuncturedSphereReal_iff.1 (hξR hz).1) q
  refine ⟨max N R + 1, by linarith [le_max_right N R], fun s t hs ↦ ?_⟩
  rcases le_or_gt s R with h | h
  · rw [Function.comp_apply]
    refine image_eq_zero_of_notMem_tsupport fun h' ↦ ?_
    have := (hξR h').2
    rw [fst_positiveEndCoord_positiveEndChart] at this
    linarith
  · refine (hN (s, t) ?_).eq_of_nhds
    have : max N R + 1 ≤ s := not_lt.1 fun h' ↦ hs ⟨h, h'⟩
    linarith [le_max_left N R]

/-- Far out on the end `q`, where the perturbation `(K_s, K_t)` is the pair-of-pants
perturbation, a solution of the Floer equation for `(K_s, K_t)` solves it for the pair-of-pants
perturbation. -/
private theorem isComplexLinearMap_perturbedFDeriv_positiveEndChart (ω : SymplecticForm V)
    {H : Puncture → ℝ → V → ℝ} {q : Puncture} {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V} {R₁ R : ℝ}
    (hK : ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      Ks z = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt z = fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    (hF : ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] V))
    (hR₁ : R₁ ≤ R) (hR : 0 < R) (ζ : ℝ × ℝ) (hζ : R ≤ ζ.1) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (positiveEndChart q ζ) (u (positiveEndChart q ζ))) (ω.perturbedFDeriv
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
        (positiveEndChart q ζ) : ℝ × ℝ →ₗ[ℝ] V) := by
  have hS := positiveEndChart_mem_thricePuncturedSphereReal (q := q) (hR.trans_le hζ)
  have hc : R₁ ≤ (positiveEndCoord q (positiveEndChart q ζ)).1 := by
    rw [fst_positiveEndCoord_positiveEndChart]
    exact hR₁.trans hζ
  obtain ⟨hKs, hKt⟩ := hK _ hS hc
  rw [← ω.perturbedFDeriv_congr u hKs hKt]
  exact hF _ hS hc

/-- The end estimate for the pair-of-pants perturbation itself, for a map solving the Floer
equation far out on the end `q`, with a height `R ≥ R₁` beyond which it holds. -/
private theorem exists_forall_setIntegral_comp_positiveEndChart_le_mul_integral_pairOfPants
    (ω : SymplecticForm V) {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) (q : Puncture) {L : ℝ≥0}
    (hX : LipschitzWith L (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H q)))
    {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x t)) t)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H q) hX 0 1) (x 0))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Je : ℝ → V → AlmostComplexStructure V}
    {R₁ : ℝ} (hJe : ContDiff ℝ 1 fun p : ℝ × V ↦ (Je p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ t, ω.Compatible (Je t (x t)))
    (hJeq : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je ζ.2) {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hF : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (positiveEndChart q ζ) (u (positiveEndChart q ζ))) (ω.perturbedFDeriv
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
        (positiveEndChart q ζ) : ℝ × ℝ →ₗ[ℝ] V))
    (hux : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) x atTop (Icc 0 1))
    (hδ : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1)) :
    ∃ C R : ℝ, R₁ ≤ R ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ {z | z ∈ thricePuncturedSphereReal ∧ R < (positiveEndCoord q z).1} →
      ∫ ζ in Ioi 0 ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart q) ζ ≤
        C * ∫ z, ‖ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u ξ z‖ ^ 2 := by
  have hH' := contDiff_uncurry_positiveEndHamiltonian (hHs q)
  have huφ (ζ : ℝ × ℝ) (hζ : 0 < ζ.1) : ContDiffAt ℝ 1 (u ∘ positiveEndChart q) ζ :=
    (hu _ (positiveEndChart_mem_thricePuncturedSphereReal hζ)).comp _
      (contDiff_positiveEndChart q 1).contDiffAt
  -- The end estimate in the positive end chart, and a bound for `J` far out on the end.
  obtain ⟨C₁, -, U, hU, hest⟩ :=
    ω.exists_mem_forall_setIntegral_le_mul_setIntegral_norm_floerLinearization_sq hX hH'
      hx hnd hJe hJex (u := u ∘ positiveEndChart q)
      ((eventually_gt_atTop 0).mono fun s hs t _ ↦ huφ (s, t) hs) hux hδ
  obtain ⟨R₂, hR₂⟩ := mem_atTop_sets.1 hU
  obtain ⟨B, R₃, hR₃⟩ := (isCompact_Icc.exists_eventually_forall_norm_le_of_tendstoUniformlyOn
    (fun t _ ↦ (hx t).continuousAt.continuousWithinAt) hJe.continuous hux).imp
      fun _ ↦ eventually_atTop.1
  set R := max (max R₂ R₃) (max R₁ 2)
  have hR1 : R₁ ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hR2 : 2 ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨max C₁ 0 * (2 * (1 + B) ^ 2), R, hR1, fun ξ hξ hξc hξR ↦ ?_⟩
  have hξS : tsupport ξ ⊆ thricePuncturedSphereReal := fun z hz ↦ (hξR hz).1
  have hξ' : ContDiff ℝ 2 (ξ ∘ positiveEndChart q) := hξ.comp (contDiff_positiveEndChart q 2)
  -- The section vanishes in the end chart outside a finite band `[R, b] × ℝ`.
  obtain ⟨b, hRb, hvan⟩ := exists_forall_comp_positiveEndChart_eq_zero hξc hξR
  calc _ = ∫ ζ in Icc R b ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart q) ζ := by
        refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
          (measurableSet_Ioi.prod measurableSet_Icc)
          (prod_mono (fun s hs ↦ lt_of_lt_of_le (by linarith) hs.1) subset_rfl) fun ζ hζ ↦ ?_
        have h := eventuallyEq_zero_of_forall_notMem_Ioo_of_fst_notMem_Icc hvan
          fun h ↦ hζ.2 ⟨h, hζ.1.2⟩
        rw [sobolevDensity_congr_of_eventuallyEq h, sobolevDensity_zero]
    -- The cylinder estimate `hest` is stated with the density written out.
    _ ≤ C₁ * ∫ ζ in Icc R b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization
          (fun w y ↦ (Je w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
          (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q)
          (ξ ∘ positiveEndChart q) ζ‖ ^ 2 := by
        simp only [funext (sobolevDensity_apply (ξ ∘ positiveEndChart q))]
        exact hest hξ' (fun s t ↦ by simp only [Function.comp_apply, positiveEndChart_add_one]) hRb
          (fun s hs ↦ hR₂ s ((le_max_left _ _).trans ((le_max_left _ _).trans hs.1)))
          (fun t ↦ hvan R t fun h ↦ lt_irrefl _ h.1) (fun t ↦ hvan b t fun h ↦ lt_irrefl _ h.2)
    _ ≤ max C₁ 0 * (2 * (1 + B) ^ 2 * ∫ z, ‖ω.floerLinearization
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u ξ z‖ ^ 2) :=
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (setIntegral_nonneg
          (measurableSet_Icc.prod measurableSet_Icc) fun _ _ ↦ sq_nonneg _)).trans
          (mul_le_mul_of_nonneg_left
            (ω.setIntegral_norm_floerLinearization_comp_positiveEndChart_sq_le hH hHs hJe
              hJeq hJ hu (fun ζ hζ ↦ hF ζ (hR1.trans hζ))
              (fun ζ hζ ht ↦ hR₃ ζ.1 hζ ζ.2 ht) hξ hξc hξS hR1
              ((le_max_right _ _).trans (le_max_left _ _)) hR2) (le_max_right _ _))
    _ = _ := by ring

/-- **The end estimate along a Floer pair of pants.** Let `H` be jointly `C²` period-one
Hamiltonians, and let `(J, K_s, K_t)` be Floer data on `S = ℂ ∖ {0, 1}` whose perturbation agrees
with the pair-of-pants perturbation of `H` far out on the end `q`, beyond the height `R₁`, where `J`
is a `C¹` family `J_q(t)` compatible along `x`. Let `u` be a `C¹` map on `S`, along which `J` is
`C¹`, that solves the Floer equation for these data beyond `R₁` on the end `q`, whose end `q`, read
in the positive end chart `φ'_q`, converges uniformly to an orbit `x` of the positive end
Hamiltonian `H'_q` starting at a nondegenerate fixed point of the time-one map, while the slice
defect `∂t (u ∘ φ'_q) - X_{H'_q}` tends uniformly to zero. Then there are `C` and `R` such that
every `C²` section `ξ` with compact support in the part `±s > R` of the end satisfies

`∫_{(0, ∞) × [0, 1]} (‖∂s (ξ ∘ φ'_q)‖² + ‖∂t (ξ ∘ φ'_q)‖² + ‖ξ ∘ φ'_q‖²) ≤ C ∫ ‖D_u ξ‖²`

for the linearized Floer operator `D_u` of the data `(J, K_s, K_t)`. The data need not agree with
the pair-of-pants data elsewhere, so this applies to every family of data that only modifies the
pair-of-pants perturbation away from the end, such as continuation necks moved in from the end. -/
theorem exists_forall_setIntegral_comp_positiveEndChart_le_mul_integral_floerLinearization
    (ω : SymplecticForm V) {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) (q : Puncture) {L : ℝ≥0}
    (hX : LipschitzWith L (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H q)))
    {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x t)) t)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H q) hX 0 1) (x 0))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Je : ℝ → V → AlmostComplexStructure V}
    {R₁ : ℝ} (hJe : ContDiff ℝ 1 fun p : ℝ × V ↦ (Je p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ t, ω.Compatible (Je t (x t)))
    (hJeq : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je ζ.2)
    {Ks Kt : ℝ × ℝ → V → ℝ}
    (hK : ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      Ks z = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt z = fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hF : ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] V))
    (hux : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) x atTop (Icc 0 1))
    (hδ : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1)) :
    ∃ C R : ℝ, ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ {z | z ∈ thricePuncturedSphereReal ∧ R < (positiveEndCoord q z).1} →
      ∫ ζ in Ioi 0 ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart q) ζ ≤
        C * ∫ z, ‖ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          Ks Kt u ξ z‖ ^ 2 := by
  -- Beyond the height `max R₁ 1` on the end, `u` solves the Floer equation for the
  -- pair-of-pants perturbation, and on sections supported there the two operators agree.
  obtain ⟨C, R, hR, hest⟩ :=
    ω.exists_forall_setIntegral_comp_positiveEndChart_le_mul_integral_pairOfPants hH hHs q hX hx
      hnd hJe hJex (R₁ := max R₁ 1) (fun ζ hζ ↦ hJeq ζ ((le_max_left _ _).trans hζ)) hJ hu
      (ω.isComplexLinearMap_perturbedFDeriv_positiveEndChart hK hF (le_max_left _ _)
        (lt_max_of_lt_right one_pos)) hux hδ
  have hR₁ : R₁ ≤ R := (le_max_left _ _).trans hR
  refine ⟨C, R, fun ξ hξ hξc hξR ↦ ?_⟩
  rw [← ω.floerLinearization_congr_data_of_tsupport
    (J := fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) u ξ fun z hz ↦
      ⟨rfl, (hK z (hξR hz).1 (hR₁.trans (hξR hz).2.le)).1.symm,
        (hK z (hξR hz).1 (hR₁.trans (hξR hz).2.le)).2.symm⟩]
  exact hest hξ hξc hξR

/-! ### The formal adjoint -/

/-- Far out on the end `q`, where `J` is a `C²` family `J_q(t)` and `u` is `C²`, a `C²` covector
field `η` supported there reads in the positive end chart as a `C²` form
`η (φ'_q ·) ∘ (a + b J)`. -/
private theorem contDiff_covectorPullback_positiveEndChart {q : Puncture}
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Je : ℝ → V → AlmostComplexStructure V}
    {R₁ R : ℝ} (hJe : ContDiff ℝ 2 fun p : ℝ × V ↦ (Je p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJeq : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je ζ.2) {u : ℝ × ℝ → V}
    (hu : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → ContDiffAt ℝ 2 u (positiveEndChart q ζ)) (hR : R₁ < R)
    {η : ℝ × ℝ → V →L[ℝ] ℝ} (hη : ContDiff ℝ 2 η)
    (hηR : tsupport η ⊆ {z | z ∈ thricePuncturedSphereReal ∧ R < (positiveEndCoord q z).1}) :
    ContDiff ℝ 2 (covectorPullback (positiveEndChart q)
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) := by
  refine contDiff_covectorPullback_of_eqOn
    (Je := fun ζ y ↦ (Je ζ.2 y).toLinearMap.toContinuousLinearMap)
    (isOpen_lt continuous_const continuous_fst) (contDiff_positiveEndChart q 3)
    (hJe.comp ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd))
    (fun ζ hζ ↦ by simp only [Function.comp_apply, hJeq ζ hζ.le]) (fun ζ hζ ↦ hu ζ hζ.le)
    (hη.comp (contDiff_positiveEndChart q 2)) fun ζ hζ ↦ ?_
  -- The form `η ∘ φ'_q` is supported beyond `R > R₁`.
  obtain ⟨-, hζR⟩ := hηR (tsupport_comp_subset_preimage _
    (contDiff_positiveEndChart q 0).continuous hζ)
  rw [fst_positiveEndCoord_positiveEndChart] at hζR
  exact hR.trans hζR

omit [FiniteDimensional ℝ V] in
/-- An end structure `J_q(t)` that agrees with `J` far out on the end `q` is compatible along
`u ∘ φ'_q` there when `J` is compatible along `u` on `S`. -/
private theorem eventually_compatible_comp_positiveEndChart (ω : SymplecticForm V) {q : Puncture}
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Je : ℝ → V → AlmostComplexStructure V} {R₁ : ℝ}
    (hJeq : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je ζ.2) {u : ℝ × ℝ → V}
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z))) :
    ∀ᶠ s in atTop, ∀ t, ω.Compatible (Je t (u (positiveEndChart q (s, t)))) := by
  refine (eventually_ge_atTop (max R₁ 1)).mono fun s hs t ↦ ?_
  rw [← hJeq (s, t) ((le_max_left _ _).trans hs)]
  exact hc _ (positiveEndChart_mem_thricePuncturedSphereReal (z := (s, t))
    (show 0 < s by linarith [le_max_right R₁ 1]))

/-- Beyond `R₁`, where `J` is the end structure `J_q(t)` and `ζ.1 ≥ 2`, the formal adjoint of the
end data `(J_q(t), 0, H'_q(t))` along `u ∘ φ'_q` on the pulled-back form `η (φ'_q ·) ∘ (a + b J)` is
the Jacobian of `φ'_q` times `D_u^* η` at `φ'_q(ζ)`. -/
private theorem floerLinearizationAdjoint_covectorPullback_positiveEndChart (ω : SymplecticForm V)
    {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1) {q : Puncture}
    (hHs : ∀ t, ContDiff ℝ 2 (H q t)) {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Je : ℝ → V → AlmostComplexStructure V} {R₁ : ℝ}
    (hJeq : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je ζ.2) {u : ℝ × ℝ → V}
    {η : ℝ × ℝ → V →L[ℝ] ℝ} {ζ : ℝ × ℝ} (hζ₁ : R₁ < ζ.1) (hζ₂ : 2 ≤ ζ.1)
    (hu : DifferentiableAt ℝ u (positiveEndChart q ζ))
    (hη : DifferentiableAt ℝ η (positiveEndChart q ζ))
    (hJu : DifferentiableAt ℝ (fun z ↦ (J z (u z)).toLinearMap.toContinuousLinearMap)
      (positiveEndChart q ζ))
    (hfl : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (positiveEndChart q ζ) (u (positiveEndChart q ζ)))
      (ω.perturbedFDeriv
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
        (positiveEndChart q ζ) : ℝ × ℝ →ₗ[ℝ] V)) :
    ω.floerLinearizationAdjoint (fun w y ↦ (Je w.2 y).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q)
        (covectorPullback (positiveEndChart q)
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ =
      (fderiv ℝ (positiveEndChart q) ζ).det • ω.floerLinearizationAdjoint
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u η (positiveEndChart q ζ) := by
  -- Near `ζ` the structures of the end data are those of the pulled-back data.
  refine Eq.trans (ω.floerLinearizationAdjoint_congr_data _ _ ?_ rfl rfl)
    (ω.floerLinearizationAdjoint_comp_positiveEndChart hH hHs hζ₂ hu hη hJu hfl)
  filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hζ₁] with w hw
  rw [hJeq w hw.le]

/-- **The adjoint of an end, read in its chart.** Far out on the end `q`, where `J` is the end
structure `J_q(t)` and `ζ.1 ≥ 2`, the `L²` norm over a band `[a, b] × [0, 1]` of the adjoint of the
end data along `u ∘ φ'_q` on the pulled-back form `η (φ'_q ·) ∘ (a + b J)` is at most `4π²` times
the integral of `|z - c_q|² ‖D_u^* η‖²` over `S`, for the center `c_q` of the end. -/
private theorem setIntegral_norm_floerLinearizationAdjoint_covectorPullback_sq_le
    (ω : SymplecticForm V) {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) {q : Puncture}
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Je : ℝ → V → AlmostComplexStructure V}
    {R₁ : ℝ} (hJeq : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je ζ.2)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    {η : ℝ × ℝ → V →L[ℝ] ℝ} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η)
    (hηS : tsupport η ⊆ thricePuncturedSphereReal) {a b : ℝ} (ha₁ : R₁ < a) (ha₂ : 2 ≤ a)
    (hF : ∀ ζ : ℝ × ℝ, a ≤ ζ.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (positiveEndChart q ζ) (u (positiveEndChart q ζ))) (ω.perturbedFDeriv
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
        (positiveEndChart q ζ) : ℝ × ℝ →ₗ[ℝ] V)) :
    ∫ ζ in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearizationAdjoint
        (fun w y ↦ (Je w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
        (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q)
        (covectorPullback (positiveEndChart q)
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ‖ ^ 2 ≤
      4 * Real.pi ^ 2 * ∫ z, ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ ^ 2 *
        ‖ω.floerLinearizationAdjoint (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u η z‖ ^ 2 := by
  -- `D_u^* η` is continuous and vanishes off the support of `η`, so the weighted integrand is
  -- integrable.
  set D := ω.floerLinearizationAdjoint (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
    (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u η
  have hDc : Continuous D := continuous_floerLinearizationAdjoint_of_tsupport_subset
    (fun z hz ↦ by simpa only [Function.uncurry_def] using hJ z hz)
    (fun z hz ↦ contDiffAt_uncurry_pairOfPantsPerturbation hH hHs hz (u z) 1)
    (fun z hz ↦ contDiffAt_uncurry_pairOfPantsPerturbation hH hHs hz (u z) Complex.I) hu hη hηS
  set g : ℝ × ℝ → ℝ := fun z ↦ ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ ^ 2 * ‖D z‖ ^ 2
  have hg : Integrable fun z ↦ 4 * Real.pi ^ 2 * g z := by
    refine ((continuous_const.mul ((Complex.equivRealProdCLM.symm.continuous.sub
      continuous_const).norm.pow 2 |>.mul (hDc.norm.pow 2))).integrable_of_hasCompactSupport
      (hηc.mono' fun z hz ↦ ?_))
    by_contra hz'
    simp [D, floerLinearizationAdjoint_of_notMem_tsupport hz'] at hz
  -- On the band the adjoint on the pulled-back form is the Jacobian `4π² |φ'_q - c_q|²` times
  -- `D_u^* η`; one factor of the Jacobian is absorbed by the change of variables.
  calc _ = ∫ ζ in Icc a b ×ˢ Icc (0 : ℝ) 1,
        (fderiv ℝ (positiveEndChart q) ζ).det * (4 * Real.pi ^ 2 * g (positiveEndChart q ζ)) := by
        refine setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc) fun ζ hζ ↦ ?_
        have hS := positiveEndChart_mem_thricePuncturedSphereReal (q := q) (z := ζ)
          (by linarith [hζ.1.1])
        rw [floerLinearizationAdjoint_covectorPullback_positiveEndChart ω hH
          (fun t ↦ (hHs q).comp (contDiff_const.prodMk contDiff_id)) hJeq
          (by linarith [hζ.1.1]) (by linarith [hζ.1.1]) ((hu _ hS).differentiableAt one_ne_zero)
          (hη.differentiable one_ne_zero _) (((hJ _ hS).differentiableAt one_ne_zero).comp
            (f := fun z ↦ (z, u z)) _ (differentiableAt_id.prodMk
              ((hu _ hS).differentiableAt one_ne_zero))) (hF ζ hζ.1.1),
          norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
        simp only [g, det_fderiv_positiveEndChart]
        ring
    _ ≤ ∫ z, 4 * Real.pi ^ 2 * g z :=
        setIntegral_det_mul_comp_positiveEndChart_le_integral (fun z ↦ by positivity) hg q a b
    _ = _ := integral_const_mul _ _

/-- **The end estimate of the formal adjoint along a Floer pair of pants.** Let `H` be jointly
`C²` period-one Hamiltonians, and let `(J, K_s, K_t)` be Floer data on `S = ℂ ∖ {0, 1}` whose
perturbation agrees with the pair-of-pants perturbation of `H` far out on the end `q`, beyond the
height `R₁`. Let `u` be a `C¹` map on `S` that solves the Floer equation for these data beyond `R₁`
on the end `q`, whose end `q`, read in the positive end chart `φ'_q`, converges uniformly to an
orbit `x` of the positive end Hamiltonian `H'_q` starting at a nondegenerate fixed point of the
time-one map, while the slice defect `∂t (u ∘ φ'_q) - X_{H'_q}` tends uniformly to zero. Suppose
that `J` is `C¹` and compatible along `u` on `S`, and that far out on the end, where `u` is `C²`,
`J` is a `C²` family `J_q(t)` compatible along `x`. Then there are `C` and `R` such that every `C²`
covector field `η` with compact support in the part `±s > R` of the end satisfies

`∫_{(0, ∞) × [0, 1]} (‖∂s η'‖² + ‖∂t η'‖² + ‖η'‖²) ≤ C ∫ |z - c_q|² ‖D_u^* η (z)‖²`

for the formal adjoint `D_u^*` of the linearized Floer operator of the data `(J, K_s, K_t)`, where
`η' = η (φ'_q ·) ∘ (a + b J)` is `η` read in the chart as a `(0, 1)`-form
(`TauCeti.Floer.covectorPullback`) and `c_q` is the center of the end. The data need not agree with
the pair-of-pants data elsewhere, as for
`exists_forall_setIntegral_comp_positiveEndChart_le_mul_integral_floerLinearization`.

The weight `|z - c_q|²` is, up to `4π²`, the Jacobian of the chart at `z`: the adjoint of the
half-cylinder on `η'` is the Jacobian times `D_u^* η`
(`floerLinearizationAdjoint_comp_positiveEndChart`), and one factor of the Jacobian is absorbed by
the change of variables. The form `η'` is `C²` because `J` and `u` are `C²` far out on the end. -/
theorem exists_forall_setIntegral_covectorPullback_le_mul_integral_floerLinearizationAdjoint
    (ω : SymplecticForm V) {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) (q : Puncture) {L : ℝ≥0}
    (hX : LipschitzWith L (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H q)))
    {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x t)) t)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H q) hX 0 1) (x 0))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Je : ℝ → V → AlmostComplexStructure V}
    {R₁ : ℝ} (hJe : ContDiff ℝ 2 fun p : ℝ × V ↦ (Je p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ t, ω.Compatible (Je t (x t)))
    (hJeq : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je ζ.2)
    {Ks Kt : ℝ × ℝ → V → ℝ}
    (hK : ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      Ks z = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt z = fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hu₂ : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → ContDiffAt ℝ 2 u (positiveEndChart q ζ))
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z)))
    (hF : ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] V))
    (hux : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) x atTop (Icc 0 1))
    (hδ : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1)) :
    ∃ C R : ℝ, ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → HasCompactSupport η →
      tsupport η ⊆ {z | z ∈ thricePuncturedSphereReal ∧ R < (positiveEndCoord q z).1} →
      ∫ ζ in Ioi 0 ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback (positiveEndChart q)
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ ≤
        C * ∫ z, ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ ^ 2 *
          ‖ω.floerLinearizationAdjoint (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
            Ks Kt u η z‖ ^ 2 := by
  set φ := positiveEndChart q
  -- The end estimate of the adjoint on the half-cylinder of the end data, whose structure has
  -- period one and is compatible along `u ∘ φ'_q`.
  obtain ⟨C₁, -, R₂, hest⟩ :=
    ω.exists_forall_setIntegral_le_mul_setIntegral_floerLinearizationAdjoint hX
    (contDiff_uncurry_positiveEndHamiltonian (hHs q)) hx hnd (hJe.of_le one_le_two)
    (periodic_of_forall_comp_eq (positiveEndChart_add_one q R₁)
      fun t ↦ hJeq (R₁, t) le_rfl).eq hJex (u := u ∘ φ)
    ((eventually_gt_atTop 0).mono fun s hs t ↦
      (hu _ (positiveEndChart_mem_thricePuncturedSphereReal (z := (s, t)) hs)).comp _
        (contDiff_positiveEndChart q 1).contDiffAt)
    (eventually_compatible_comp_positiveEndChart ω hJeq hc) hux hδ
  set R := max (max R₂ (R₁ + 1)) 2
  have hR : R₂ ≤ R ∧ R₁ + 1 ≤ R ∧ 2 ≤ R :=
    ⟨(le_max_left _ _).trans (le_max_left _ _), (le_max_right _ _).trans (le_max_left _ _),
      le_max_right _ _⟩
  refine ⟨max C₁ 0 * (4 * Real.pi ^ 2), R, fun η hη hηc hηR ↦ ?_⟩
  set η' := covectorPullback φ (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η
  -- `η` vanishes in the end chart outside a finite band `(R, b) × ℝ`, and so does `η'`, which
  -- is `C²` and has period one in `t`.
  obtain ⟨b, hRb, hvan⟩ := exists_forall_comp_positiveEndChart_eq_zero hηc hηR
  have hvan' : ∀ s t, s ∉ Ioo R b → η' (s, t) = 0 := fun s t hs ↦
    covectorPullback_eq_zero_of_apply_eq_zero _ _ u (hvan s t hs)
  have hη' : ContDiff ℝ 2 η' := contDiff_covectorPullback_positiveEndChart hJe hJeq hu₂
    (by linarith) hη hηR
  calc _ = ∫ ζ in Icc R b ×ˢ Icc (0 : ℝ) 1, sobolevDensity η' ζ := by
        refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
          (measurableSet_Ioi.prod measurableSet_Icc)
          (prod_mono (fun s hs ↦ lt_of_lt_of_le (by linarith) hs.1) subset_rfl) fun ζ hζ ↦ ?_
        have h := eventuallyEq_zero_of_forall_notMem_Ioo_of_fst_notMem_Icc hvan'
          fun h ↦ hζ.2 ⟨h, hζ.1.2⟩
        rw [sobolevDensity_congr_of_eventuallyEq h, sobolevDensity_zero]
    _ ≤ max C₁ 0 * ∫ ζ in Icc R b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearizationAdjoint
          (fun w y ↦ (Je w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
          (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ φ) η' ζ‖ ^ 2 := by
        simp only [funext (sobolevDensity_apply η')]
        exact (hest hη'
          (covectorPullback_add_snd_of_periodic_snd (positiveEndChart_add_one q) _ u η) hRb hR.1
          hvan').trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (setIntegral_nonneg
            (measurableSet_Icc.prod measurableSet_Icc) fun _ _ ↦ sq_nonneg _))
    _ ≤ _ := by
        -- On the support of `η`, beyond `R > R₁`, the data are the pair-of-pants data.
        rw [mul_assoc, ← ω.floerLinearizationAdjoint_congr_data_of_tsupport
          (J := fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) u η fun z hz ↦
            ⟨EventuallyEq.rfl, (hK z (hηR hz).1 (by linarith [(hηR hz).2])).1.symm,
              (hK z (hηR hz).1 (by linarith [(hηR hz).2])).2.symm⟩]
        exact mul_le_mul_of_nonneg_left
          (setIntegral_norm_floerLinearizationAdjoint_covectorPullback_sq_le ω hH hHs hJeq hJ hu
            (hη.of_le one_le_two) hηc (fun z hz ↦ (hηR hz).1) (by linarith) hR.2.2
            (ω.isComplexLinearMap_perturbedFDeriv_positiveEndChart hK hF (by linarith)
              (by linarith)))
          (le_max_right _ _)

end TauCeti.SymplecticForm
