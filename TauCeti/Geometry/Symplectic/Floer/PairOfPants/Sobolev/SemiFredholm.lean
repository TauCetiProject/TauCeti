/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.SemiFredholm
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev.Operator
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Density

/-!
# Finite-dimensional kernel and closed range of the linearized Floer operator on the pair of pants

Let `u` be a Floer pair of pants: a solution of the Floer equation on `S = ℂ ∖ {0, 1}` for the
pair-of-pants perturbation of period-one Hamiltonians `H_q` on the three ends, with values in a
finite-dimensional symplectic vector space, whose ends converge to nondegenerate one-periodic
orbits. Its linearized operator is realized as a bounded operator

`D_u : W^{1,2}_0(S, V) → L²(S, V)`

(`TauCeti.SymplecticForm.floerConformalSobolevOperator`), where `W^{1,2}_0(S, V)` is the Sobolev
space `TauCeti.ConformalSobolev.H1` of the cylindrical weight `ρ = TauCeti.Floer.cylindricalWeight`.
This file proves that `D_u` has finite-dimensional kernel
(`TauCeti.SymplecticForm.finiteDimensional_ker_floerConformalSobolevOperator_pairOfPants`) and
closed range (`TauCeti.SymplecticForm.isClosed_range_floerConformalSobolevOperator_pairOfPants`).
These are the semi-Fredholm half of the Fredholm property of the pair-of-pants operator.

* **The norm.** The squared norm of the jet of a test section `ξ` in `W^{1,2}_0(S, V)` is at most
  `∫_S (ρ ‖ξ‖² + ‖∂s ξ‖² + ‖∂t ξ‖²)`. This weighted energy is controlled by the `W^{1,2}` energy of
  `ξ ∘ φ'_q` on the half-cylinders `(T, ∞) × [0, 1]` of the three positive end charts `φ'_q`, and
  of `ξ` on the truncation `S_T`, for any `T ≥ 0`
  (`TauCeti.Floer.exists_forall_setIntegral_le_mul_sum_setIntegral_sobolevDensity_add`). On the
  ends this is the change of variables `TauCeti.Floer.lintegral_image_positiveEndChart_le`, in
  which the weight times the Jacobian of the chart is at most `20π²`; on the compact core `S_T`
  the weight is bounded; and `S` is covered by `S_T` and the three images of the half-cylinders.
* **The estimate.** The semi-Fredholm estimate in end coordinates
  (`exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_add`)
  bounds this energy by `∫ ‖D_u ξ‖² + ∫_{S_{T + 1}} ‖ξ‖²`. The first term is the squared `L²` norm
  of `D_u` applied to the jet, and the second is at most a multiple of the squared `L²` norm of
  the weighted value `√ρ ξ` on the compact set `S_{T + 1}`, on which `ρ⁻¹` is bounded. So
  `‖x‖ ≤ C (‖D_u x‖ + ‖√ρ ξ‖_{L²(S_{T + 1})})` on the jets `x` of test sections
  (`TauCeti.SymplecticForm.exists_forall_norm_le_floerConformalSobolevOperator_pairOfPants`).
* **Peetre's argument.** By Rellich's theorem on `S_{T + 1}`, this estimate gives
  finite-dimensional kernel and closed range
  (`TauCeti.ConformalSobolev.finiteDimensional_ker_of_estimate`,
  `TauCeti.ConformalSobolev.isClosed_range_of_estimate`).

The boundedness of the coefficient field of `D_u`, which the realization needs, follows from the
convergence of the ends of `u` to its asymptotic orbits
(`TauCeti.SymplecticForm.memLp_floerConformalJetCoeff_pairOfPants_of_tendstoUniformlyOn`, in
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev.Operator`).

The finiteness of the cokernel and the Fredholm index are not treated here.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix B, on the Fredholm theory of real Cauchy–Riemann operators on punctured Riemann
  surfaces with cylindrical ends.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the Fredholm theory of the pair-of-pants operator.
-/

public section

noncomputable section

open Set Function Filter MeasureTheory Real TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture TauCeti.ConformalSobolev
open scoped ENNReal NNReal Manifold

namespace TauCeti

namespace Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- On a compact set of `S` on which the cylindrical weight is at most `c ≥ 0`, the weighted energy
`∫ (ρ ‖ξ‖² + ‖∂s ξ‖² + ‖∂t ξ‖²)` of a `C¹` section is at most `c + 1` times its `W^{1,2}`
energy. -/
private theorem lintegral_weightedDensity_le_of_le {K : Set (ℝ × ℝ)} (hK : IsCompact K) {c : ℝ}
    (hc : 0 ≤ c) (hρK : ∀ z ∈ K, cylindricalWeight z ≤ c) {ξ : ℝ × ℝ → V}
    (hξ : ContDiff ℝ 1 ξ) :
    ∫⁻ z in K, ENNReal.ofReal (cylindricalWeight z * ‖ξ z‖ ^ 2 + ‖fderiv ℝ ξ z (1, 0)‖ ^ 2 +
        ‖fderiv ℝ ξ z (0, 1)‖ ^ 2) ≤
      ENNReal.ofReal ((c + 1) * ∫ z in K, sobolevDensity ξ z) := by
  rw [ENNReal.ofReal_mul (by positivity), ofReal_integral_eq_lintegral_ofReal
    ((continuous_sobolevDensity hξ).continuousOn.integrableOn_compact hK)
    (ae_of_all _ fun z ↦ sobolevDensity_nonneg ξ z),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' hK.measurableSet fun z hz ↦ ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [sobolevDensity_apply, stdComplexLineReal_eq, stdComplexLineImag_eq]
  nlinarith [sq_nonneg ‖ξ z‖, sq_nonneg ‖fderiv ℝ ξ z (1, 0)‖, sq_nonneg ‖fderiv ℝ ξ z (0, 1)‖,
    mul_le_mul_of_nonneg_right ((hρK z hz).trans (le_add_of_nonneg_right zero_le_one))
      (sq_nonneg ‖ξ z‖)]

/-- On the image of the half-cylinder `(T, ∞) × [0, 1)` of the end `q`, for `T ≥ 0`, the weighted
energy of a `C¹` section with compact support in `S` is at most `20π²` times the `W^{1,2}` energy
of `ξ ∘ φ'_q` on `(T, ∞) × [0, 1]`. -/
private theorem lintegral_image_positiveEndChart_le_ofReal (q : Puncture) {T : ℝ} (hT : 0 ≤ T)
    {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 1 ξ) (hξc : HasCompactSupport ξ)
    (hξS : tsupport ξ ⊆ thricePuncturedSphereReal) :
    ∫⁻ z in positiveEndChart q '' (Ioi T ×ˢ Ico 0 1),
        ENNReal.ofReal (cylindricalWeight z * ‖ξ z‖ ^ 2 + ‖fderiv ℝ ξ z (1, 0)‖ ^ 2 +
          ‖fderiv ℝ ξ z (0, 1)‖ ^ 2) ≤
      ENNReal.ofReal (20 * π ^ 2 *
        ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart q) ζ) := by
  rw [ENNReal.ofReal_mul (by positivity), ofReal_integral_eq_lintegral_ofReal
    (integrableOn_sobolevDensity_comp_positiveEndChart hξ hξc hξS q T)
    (ae_of_all _ fun ζ ↦ sobolevDensity_nonneg _ ζ)]
  refine (lintegral_image_positiveEndChart_le q measurableSet_Ioi
    (fun s hs ↦ hT.trans (le_of_lt hs)) fun ζ _ ↦ hξ.differentiable one_ne_zero _).trans ?_
  gcongr ENNReal.ofReal (20 * π ^ 2) * ?_
  calc _ = ∫⁻ ζ in Ioi T ×ˢ Ico (0 : ℝ) 1,
        ENNReal.ofReal (sobolevDensity (ξ ∘ positiveEndChart q) ζ) := by
        simp only [sobolevDensity_apply, stdComplexLineReal_eq, stdComplexLineImag_eq,
          Function.comp_apply]
    _ ≤ _ := lintegral_mono_set (prod_mono subset_rfl Ico_subset_Icc_self)

/-- The weighted energy `∫_S (ρ ‖ξ‖² + ‖∂s ξ‖² + ‖∂t ξ‖²)` of a `C¹` section is at most `r ≥ 0`
when its lower integral is: the weighted density is nonnegative and continuous on `S`. -/
private theorem setIntegral_weightedDensity_le_of_lintegral_le {ξ : ℝ × ℝ → V}
    (hξ : ContDiff ℝ 1 ξ) {r : ℝ} (hr : 0 ≤ r)
    (h : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (cylindricalWeight z * ‖ξ z‖ ^ 2 +
      ‖fderiv ℝ ξ z (1, 0)‖ ^ 2 + ‖fderiv ℝ ξ z (0, 1)‖ ^ 2) ≤ ENNReal.ofReal r) :
    ∫ z in thricePuncturedSphereReal, (cylindricalWeight z * ‖ξ z‖ ^ 2 +
      ‖fderiv ℝ ξ z (1, 0)‖ ^ 2 + ‖fderiv ℝ ξ z (0, 1)‖ ^ 2) ≤ r := by
  have hρ := isWeight_cylindricalWeight
  have hd := hξ.continuous_fderiv one_ne_zero
  refine (integral_eq_lintegral_of_nonneg_ae ?_ ?_).trans_le (ENNReal.toReal_le_of_le_ofReal hr h)
  · filter_upwards [ae_restrict_mem hρ.isOpen.measurableSet] with z hz
    have := hρ.pos z hz
    positivity
  · exact (((hρ.continuousOn.mul (hξ.continuous.norm.pow 2).continuousOn).add
      ((hd.clm_apply continuous_const).norm.pow 2).continuousOn).add
      ((hd.clm_apply continuous_const).norm.pow 2).continuousOn).aestronglyMeasurable
      hρ.isOpen.measurableSet

/-- **The `W^{1,2}` norm of the pair of pants, from the energy on the ends and on a core.** For a
height `T ≥ 0` there is a constant `B ≥ 0` such that every `C¹` section `ξ` with compact support in
`S = ℂ ∖ {0, 1}` satisfies

`∫_S (ρ ‖ξ‖² + ‖∂s ξ‖² + ‖∂t ξ‖²)`
`  ≤ B (∑_q ∫_{(T, ∞) × [0, 1]} (‖∂s (ξ ∘ φ'_q)‖² + ‖∂t (ξ ∘ φ'_q)‖² + ‖ξ ∘ φ'_q‖²)`
`    + ∫_{S_T} (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²))`,

for the cylindrical weight `ρ` of `S`, the positive end charts `φ'_q` and the truncation `S_T`. The
left side bounds the squared norm of the jet of `ξ` in the Sobolev space
`TauCeti.ConformalSobolev.H1` of `ρ` (`TauCeti.ConformalSobolev.sq_norm_le_integral`); the right
side is the energy in which the semi-Fredholm estimate of the linearized Floer operator is stated
in end coordinates. -/
theorem exists_forall_setIntegral_le_mul_sum_setIntegral_sobolevDensity_add {T : ℝ} (hT : 0 ≤ T) :
    ∃ B, 0 ≤ B ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 1 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ thricePuncturedSphereReal →
      ∫ z in thricePuncturedSphereReal, (cylindricalWeight z * ‖ξ z‖ ^ 2 +
          ‖fderiv ℝ ξ z (1, 0)‖ ^ 2 + ‖fderiv ℝ ξ z (0, 1)‖ ^ 2) ≤
        B * ((∑ q, ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart q) ζ) +
          ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation T, sobolevDensity ξ z) := by
  set S := thricePuncturedSphereReal
  set K := Complex.equivRealProdCLM.symm ⁻¹' truncation T
  have hK : IsCompact K := isCompact_preimage_truncation T
  have hKS : K ⊆ S := preimage_truncation_subset_thricePuncturedSphereReal T
  have hρ := isWeight_cylindricalWeight
  -- The weight is bounded on the compact core.
  obtain ⟨Bρ, hBρ⟩ := hK.exists_bound_of_continuousOn (hρ.continuousOn.mono hKS)
  set c := max Bρ 0
  have hρK (z : ℝ × ℝ) (hz : z ∈ K) : cylindricalWeight z ≤ c :=
    (le_abs_self _).trans ((hBρ z hz).trans (le_max_left _ _))
  refine ⟨max (20 * π ^ 2) (c + 1), by positivity, fun ξ hξ hξc hξS ↦ ?_⟩
  set w : ℝ × ℝ → ℝ := fun z ↦ cylindricalWeight z * ‖ξ z‖ ^ 2 + ‖fderiv ℝ ξ z (1, 0)‖ ^ 2 +
    ‖fderiv ℝ ξ z (0, 1)‖ ^ 2
  set E : Puncture → ℝ := fun q ↦
    ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart q) ζ
  set Y := ∫ z in K, sobolevDensity ξ z
  have hE0 (q : Puncture) : 0 ≤ E q :=
    setIntegral_nonneg (measurableSet_Ioi.prod measurableSet_Icc) fun ζ _ ↦
      sobolevDensity_nonneg _ ζ
  have hY0 : 0 ≤ Y := setIntegral_nonneg hK.measurableSet fun z _ ↦ sobolevDensity_nonneg ξ z
  have hsum : 0 ≤ ∑ q, E q := Finset.sum_nonneg fun q _ ↦ hE0 q
  -- Bound the weighted energy on the core and on the three ends beyond `T`, which cover `S`.
  have hlin : ∫⁻ z in S, ENNReal.ofReal (w z) ≤
      ENNReal.ofReal (max (20 * π ^ 2) (c + 1) * ((∑ q, E q) + Y)) := by
    calc ∫⁻ z in S, ENNReal.ofReal (w z)
        ≤ (∫⁻ z in K, ENNReal.ofReal (w z)) +
          ∑ q, ∫⁻ z in positiveEndChart q '' (Ioi T ×ˢ Ico 0 1), ENNReal.ofReal (w z) :=
          lintegral_thricePuncturedSphereReal_le T _
      _ ≤ ENNReal.ofReal ((c + 1) * Y) + ∑ q, ENNReal.ofReal (20 * π ^ 2 * E q) :=
          add_le_add (lintegral_weightedDensity_le_of_le hK (le_max_right _ _) hρK hξ)
            (Finset.sum_le_sum fun q _ ↦
              lintegral_image_positiveEndChart_le_ofReal q hT hξ hξc hξS)
      _ = ENNReal.ofReal ((c + 1) * Y + ∑ q, 20 * π ^ 2 * E q) := by
          rw [ENNReal.ofReal_add (by positivity)
              (Finset.sum_nonneg fun q _ ↦ mul_nonneg (by positivity) (hE0 q)),
            ENNReal.ofReal_sum_of_nonneg fun q _ ↦ mul_nonneg (by positivity) (hE0 q)]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← Finset.mul_sum]
          nlinarith [mul_le_mul_of_nonneg_right (le_max_left (20 * π ^ 2) (c + 1)) hsum,
            mul_le_mul_of_nonneg_right (le_max_right (20 * π ^ 2) (c + 1)) hY0]
  exact setIntegral_weightedDensity_le_of_lintegral_le hξ (by positivity) hlin

end Floer

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The semi-Fredholm estimate on `W^{1,2}_0(S, V)`, from the estimate in end coordinates.** Let
the coefficient field of the linearized Floer operator `D_u` on the jets of the cylindrical weight
`ρ` of `S = ℂ ∖ {0, 1}` be essentially bounded on `S`, so that
`TauCeti.SymplecticForm.floerConformalSobolevOperator` realizes `D_u` on `W^{1,2}_0(S, V)`. Suppose
that for some height `T ≥ 0` every `C²` section `ξ` with compact support in `S` satisfies the
semi-Fredholm estimate in end coordinates

`∑_q ∫_{(T, ∞) × [0, 1]} (‖∂s (ξ ∘ φ'_q)‖² + ‖∂t (ξ ∘ φ'_q)‖² + ‖ξ ∘ φ'_q‖²)`
`  + ∫_{S_T} (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{S_{T + 1}} ‖ξ‖²)`.

Then there is `C'` such that every jet `x` of a test section `ξ` satisfies
`‖x‖ ≤ C' (‖D_u x‖ + ‖√ρ ξ‖_{L²(S_{T + 1})})`, the estimate consumed by Peetre's argument
`TauCeti.ConformalSobolev.finiteDimensional_ker_of_estimate`. -/
theorem exists_forall_norm_le_floerConformalSobolevOperator_of_forall_le (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hM : MemLp (ω.floerConformalJetCoeff cylindricalWeight J Ks Kt u) ∞
      (volume.restrict thricePuncturedSphereReal)) {C T : ℝ} (hT : 0 ≤ T)
    (hest : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ thricePuncturedSphereReal →
      (∑ q, ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart q) ζ) +
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation T, sobolevDensity ξ z ≤
        C * ((∫ z, ‖ω.floerLinearization J Ks Kt u ξ z‖ ^ 2) +
          ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (T + 1), ‖ξ z‖ ^ 2)) :
    ∃ C', ∀ x : H1 V thricePuncturedSphereReal cylindricalWeight,
      (x : Lp (V × V × V) 2 (volume.restrict thricePuncturedSphereReal)) ∈
        jetSubmodule V thricePuncturedSphereReal cylindricalWeight →
      ‖x‖ ≤ C' * (‖ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
        J Ks Kt u x‖ + ‖restrictWeightedValue V thricePuncturedSphereReal
          (Complex.equivRealProdCLM.symm ⁻¹' truncation (T + 1)) x‖) := by
  set S := thricePuncturedSphereReal
  set K := Complex.equivRealProdCLM.symm ⁻¹' truncation (T + 1)
  have hK : IsCompact K := isCompact_preimage_truncation _
  have hKS : K ⊆ S := preimage_truncation_subset_thricePuncturedSphereReal _
  have hρ := isWeight_cylindricalWeight
  obtain ⟨B, hB0, hB⟩ :=
    Floer.exists_forall_setIntegral_le_mul_sum_setIntegral_sobolevDensity_add (V := V) hT
  obtain ⟨Bk, hBk0, hBk⟩ := exists_forall_setIntegral_norm_sq_le_mul (V := V) hρ hK hKS
  refine ⟨√(B * max C 0 * (Bk + 1)), fun x hx ↦ ?_⟩
  obtain ⟨ξ, hξ, hxξ⟩ := mem_jetSubmodule_iff.1 hx
  obtain ⟨hξ2, hξc, hξS⟩ := mem_testSection_iff.1 hξ
  set a := ‖ω.floerConformalSobolevOperator S cylindricalWeight J Ks Kt u x‖
  set b := ‖restrictWeightedValue V S K x‖
  -- `a²` is the `L²` energy of `D_u ξ`, and `b²` the weighted `L²` energy of `ξ` on `K`.
  have hD : a ^ 2 = ∫ z, ‖ω.floerLinearization J Ks Kt u ξ z‖ ^ 2 :=
    (ω.sq_norm_floerConformalSobolevOperator_eq hρ hM hξ hxξ).trans (by
      rw [Measure.restrict_eq_self_of_ae_mem ae_mem_thricePuncturedSphereReal])
  have hR := sq_norm_restrictWeightedValue_eq hρ hK.measurableSet hKS hxξ
  have hX0 : 0 ≤ ∫ z, ‖ω.floerLinearization J Ks Kt u ξ z‖ ^ 2 :=
    integral_nonneg fun _ ↦ sq_nonneg _
  have hY0 : 0 ≤ ∫ z in K, ‖ξ z‖ ^ 2 := setIntegral_nonneg hK.measurableSet fun _ _ ↦ sq_nonneg _
  have hab : 0 ≤ a * b := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have key : ‖x‖ ^ 2 ≤ B * max C 0 * (Bk + 1) * (a + b) ^ 2 := by
    calc ‖x‖ ^ 2 ≤ ∫ z in S, (cylindricalWeight z * ‖ξ z‖ ^ 2 + ‖fderiv ℝ ξ z (1, 0)‖ ^ 2 +
          ‖fderiv ℝ ξ z (0, 1)‖ ^ 2) := sq_norm_le_integral hρ hξ hxξ
      _ ≤ B * ((∑ q, ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart q) ζ) +
          ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation T, sobolevDensity ξ z) :=
          hB (hξ2.of_le one_le_two) hξc hξS
      _ ≤ B * (max C 0 * (a ^ 2 + Bk * b ^ 2)) := by
          rw [hD, hR]
          gcongr
          exact (hest hξ2 hξc hξS).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
            (add_nonneg hX0 hY0)) |>.trans (by gcongr; exact hBk ξ hξ2.continuous.continuousOn)
      _ ≤ B * max C 0 * (Bk + 1) * (a + b) ^ 2 := by
          have : a ^ 2 + Bk * b ^ 2 ≤ (Bk + 1) * (a + b) ^ 2 := by
            nlinarith [sq_nonneg a, sq_nonneg b, mul_nonneg hBk0 hab, mul_nonneg hBk0 (sq_nonneg a)]
          calc B * (max C 0 * (a ^ 2 + Bk * b ^ 2))
              ≤ B * (max C 0 * ((Bk + 1) * (a + b) ^ 2)) := by gcongr
            _ = _ := by ring
  rw [← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_sq (add_nonneg (norm_nonneg _) (norm_nonneg _)),
    ← Real.sqrt_mul (by positivity)]
  exact Real.sqrt_le_sqrt key

/-- **The semi-Fredholm estimate on `W^{1,2}_0(S, V)` along a Floer pair of pants.** Under the
hypotheses of the semi-Fredholm estimate in end coordinates
`exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_add`
(a Floer pair of pants `u` for the pair-of-pants perturbation of period-one Hamiltonians `H_q`,
whose ends converge to nondegenerate one-periodic orbits `x_q`, with almost complex structures
cylindrical far out on the ends), there are `C` and a height `T` such that the realization `D_u` of
the linearized Floer operator on `W^{1,2}_0(S, V)` satisfies
`‖x‖ ≤ C (‖D_u x‖ + ‖√ρ ξ‖_{L²(S_T)})` on the jets `x` of test sections `ξ`, where `S_T` is the
truncation of `S` at height `T`. -/
theorem exists_forall_norm_le_floerConformalSobolevOperator_pairOfPants (ω : SymplecticForm V)
    {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) {L : Puncture → ℝ≥0}
    (hX : ∀ q, LipschitzWith (L q)
      (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H q)))
    {x : Puncture → ℝ → V}
    (hx : ∀ q t, HasDerivAt (x q)
      (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x q t)) t)
    (hnd : ∀ q, IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H q) (hX q) 0 1) (x q 0))
    {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Je : Puncture → ℝ → V → AlmostComplexStructure V} {R₁ : ℝ}
    (hJe : ∀ q, ContDiff ℝ 1 fun p : ℝ × V ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ q t, ω.Compatible (Je q t (x q t)))
    (hJeq : ∀ q (ζ : ℝ × ℝ), R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je q ζ.2)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z)))
    (hF : ∀ z ∈ thricePuncturedSphereReal, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z (u z)) (ω.perturbedFDeriv
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
        z : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ q, TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop
      (Icc 0 1))
    (hδ : ∀ q, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1)) :
    ∃ C T : ℝ, ∀ y : H1 V thricePuncturedSphereReal cylindricalWeight,
      (y : Lp (V × V × V) 2 (volume.restrict thricePuncturedSphereReal)) ∈
        jetSubmodule V thricePuncturedSphereReal cylindricalWeight →
      ‖y‖ ≤ C * (‖ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
        (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u y‖ +
        ‖restrictWeightedValue V thricePuncturedSphereReal
          (Complex.equivRealProdCLM.symm ⁻¹' truncation T) y‖) := by
  obtain ⟨C, -, T, hT, hest⟩ :=
    ω.exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_add hH hHs
      hX hx hnd hJe hJex hJeq hJ hu hc hF hux hδ
  have hM := ω.memLp_floerConformalJetCoeff_pairOfPants_of_tendstoUniformlyOn hH hHs
    (fun q ↦ (continuous_iff_continuousAt.2 fun t ↦ (hx q t).continuousAt).continuousOn) hJe hJeq
    hJ hu hF hux hδ
  obtain ⟨C', hC'⟩ := ω.exists_forall_norm_le_floerConformalSobolevOperator_of_forall_le hM hT hest
  exact ⟨C', T + 1, hC'⟩

/-- **The linearized Floer operator of a Floer pair of pants has finite-dimensional kernel on
`W^{1,2}`.** Under the hypotheses of the semi-Fredholm estimate
`TauCeti.SymplecticForm.exists_forall_norm_le_floerConformalSobolevOperator_pairOfPants` (a Floer
pair of pants `u` whose ends converge to nondegenerate one-periodic orbits, with almost complex
structures cylindrical far out on the ends), the realization
`D_u : W^{1,2}_0(S, V) → L²(S, V)` of the linearized Floer operator on `S = ℂ ∖ {0, 1}`, for the
Sobolev space of the cylindrical metric, has finite-dimensional kernel. -/
theorem finiteDimensional_ker_floerConformalSobolevOperator_pairOfPants (ω : SymplecticForm V)
    {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) {L : Puncture → ℝ≥0}
    (hX : ∀ q, LipschitzWith (L q)
      (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H q)))
    {x : Puncture → ℝ → V}
    (hx : ∀ q t, HasDerivAt (x q)
      (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x q t)) t)
    (hnd : ∀ q, IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H q) (hX q) 0 1) (x q 0))
    {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Je : Puncture → ℝ → V → AlmostComplexStructure V} {R₁ : ℝ}
    (hJe : ∀ q, ContDiff ℝ 1 fun p : ℝ × V ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ q t, ω.Compatible (Je q t (x q t)))
    (hJeq : ∀ q (ζ : ℝ × ℝ), R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je q ζ.2)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z)))
    (hF : ∀ z ∈ thricePuncturedSphereReal, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z (u z)) (ω.perturbedFDeriv
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
        z : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ q, TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop
      (Icc 0 1))
    (hδ : ∀ q, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1)) :
    FiniteDimensional ℝ (ω.floerConformalSobolevOperator thricePuncturedSphereReal
      cylindricalWeight (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u).ker := by
  obtain ⟨C, T, hest⟩ := ω.exists_forall_norm_le_floerConformalSobolevOperator_pairOfPants hH hHs
    hX hx hnd hJe hJex hJeq hJ hu hc hF hux hδ
  exact finiteDimensional_ker_of_estimate isWeight_cylindricalWeight
    (isCompact_preimage_truncation T) (preimage_truncation_subset_thricePuncturedSphereReal T) _
    hest

/-- **The linearized Floer operator of a Floer pair of pants has closed range on `W^{1,2}`.** Under
the hypotheses of
`TauCeti.SymplecticForm.finiteDimensional_ker_floerConformalSobolevOperator_pairOfPants`, the
realization `D_u : W^{1,2}_0(S, V) → L²(S, V)` of the linearized Floer operator on
`S = ℂ ∖ {0, 1}` has closed range. -/
theorem isClosed_range_floerConformalSobolevOperator_pairOfPants (ω : SymplecticForm V)
    {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) {L : Puncture → ℝ≥0}
    (hX : ∀ q, LipschitzWith (L q)
      (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H q)))
    {x : Puncture → ℝ → V}
    (hx : ∀ q t, HasDerivAt (x q)
      (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x q t)) t)
    (hnd : ∀ q, IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H q) (hX q) 0 1) (x q 0))
    {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Je : Puncture → ℝ → V → AlmostComplexStructure V} {R₁ : ℝ}
    (hJe : ∀ q, ContDiff ℝ 1 fun p : ℝ × V ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ q t, ω.Compatible (Je q t (x q t)))
    (hJeq : ∀ q (ζ : ℝ × ℝ), R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je q ζ.2)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z)))
    (hF : ∀ z ∈ thricePuncturedSphereReal, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z (u z)) (ω.perturbedFDeriv
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
        z : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ q, TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop
      (Icc 0 1))
    (hδ : ∀ q, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1)) :
    IsClosed ((ω.floerConformalSobolevOperator thricePuncturedSphereReal
      cylindricalWeight (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u).range :
        Set (Lp V 2 (volume.restrict thricePuncturedSphereReal))) := by
  obtain ⟨C, T, hest⟩ := ω.exists_forall_norm_le_floerConformalSobolevOperator_pairOfPants hH hHs
    hX hx hnd hJe hJex hJeq hJ hu hc hF hux hδ
  exact isClosed_range_of_estimate isWeight_cylindricalWeight
    (isCompact_preimage_truncation T) (preimage_truncation_subset_thricePuncturedSphereReal T) _
    hest

end SymplecticForm

end TauCeti
