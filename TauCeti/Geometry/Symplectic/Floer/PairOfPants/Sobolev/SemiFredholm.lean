/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.SemiFredholm
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev.Operator

/-!
# Linearized Floer operators on the pair of pants are semi-Fredholm on `W^{1,2}`

Let `H_q` be jointly `C²` period-one Hamiltonians on the three ends of the pair of pants
`S = ℂ ∖ {0, 1}`, on a finite-dimensional symplectic vector space `(V, ω)`. Let `(J, K_s, K_t)` be
Floer data on `S` which far out on each end, beyond a height `R₁`, are cylindrical,
`J(φ'_q(s, t)) = J_q(t)` for `C¹` families `J_q`, with `(K_s, K_t)` the components of the
pair-of-pants perturbation of `H` (`TauCeti.Floer.pairOfPantsPerturbation`). Let `u` be `C¹` on
`S`, solve the Floer equation for these data beyond `R₁` on each end, and have ends converging to
nondegenerate one-periodic orbits `x_q` of `H_q`, with `J_q` compatible with `ω` along `x_q`. On
all of `S` the data need only be regular along `u`: `J` is `C¹` and compatible with `ω` along `u`,
and `K_s`, `K_t` are `C²` along `u`. The linearized operator of `u` is realized on the Sobolev
space `W^{1,2}_0(S, V)` of the cylindrical metric, `TauCeti.ConformalSobolev.H1 V S ρ` for the
cylindrical weight `ρ = TauCeti.Floer.cylindricalWeight`, by
`TauCeti.SymplecticForm.floerConformalSobolevOperator`
(`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev.Operator`). This file proves that this
realization `D_u : W^{1,2}_0(S, V) → L²(S, V)` has finite-dimensional kernel and closed range, the
first half of the Fredholm property behind the pair-of-pants product.

A Floer pair of pants, a solution of the Floer equation for the pair-of-pants data on all of `S`,
is the special case where `(K_s, K_t)` are these components everywhere. The pair of pants with
continuation necks (`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Continuation.SemiFredholm`)
is another case: it modifies the pair-of-pants datum away from the ends.

The semi-Fredholm estimate for `C²` sections with compact support in `S`
(`exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_add` in
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.SemiFredholm`) controls the `W^{1,2}` energy of a
section in the coordinates `(s, t)` of the positive end charts `φ'_q` beyond a height `T` and in
the coordinates of `ℂ` on the truncation `S_T`. The norm of `H1` is instead the weighted energy
`∫_S (ρ ‖ξ‖² + ‖∂s ξ‖² + ‖∂t ξ‖²)` in the coordinates of `ℂ`.

* **Comparing the energies.**
  `TauCeti.Floer.exists_forall_setIntegral_le_mul_sum_setIntegral_sobolevDensity_add` bounds the
  weighted energy by the energy of the semi-Fredholm estimate. The pair of pants is
  covered by `S_T` and the images of the bands `(T, ∞) × [0, 1)` under the three positive end
  charts (`TauCeti.Floer.subset_preimage_truncation_union_iUnion_image_positiveEndChart`). On the
  bands, for `T ≥ 0`, the change of variables along `φ'_q` costs a factor `20π²`
  (`TauCeti.Floer.lintegral_image_positiveEndChart_le`), and on the compact set `S_T` the weight is
  bounded.
* **The estimate on `H1`.**
  `SymplecticForm.exists_forall_norm_le_mul_norm_floerConformalSobolevOperator_add_of_estimate`
  turns such an estimate, for any Floer data whose coefficient field on conformal jets is
  essentially bounded, into Peetre's estimate `‖x‖ ≤ C (‖D_u x‖ + ‖√ρ ξ‖_{L²(K)})` on the jets `x`
  of test sections `ξ`, with `K = S_{T + 1}`. The norm of `D_u x` is the `L²` norm of `D_u ξ`
  (`TauCeti.SymplecticForm.norm_floerConformalSobolevOperator_sq`), and on the compact set `K` the
  `L²` norm of `ξ` is controlled by that of `√ρ ξ`, since `ρ` is bounded below there
  (`TauCeti.ConformalSobolev.exists_setIntegral_norm_sq_le_mul_norm_restrictWeightedValue_sq`).
* **Along `u`.** The uniform convergence of the loops of `u` in the end charts
  to the asymptotic orbits, and of the slice defects to zero, bounds `u` and the slice defects far
  out on the ends over a band of angular width one, so the coefficient field is essentially bounded
  (`TauCeti.SymplecticForm.memLp_floerConformalJetCoeff_pairOfPants_of_tendstoUniformlyOn`). With
  the semi-Fredholm estimate this gives Peetre's estimate
  (`TauCeti.SymplecticForm.exists_forall_norm_le_mul_norm_floerConformalSobolevOperator_add`), and
  Peetre's argument (`TauCeti.ConformalSobolev.finiteDimensional_ker_of_estimate`,
  `TauCeti.ConformalSobolev.isClosed_range_of_estimate`) gives finite-dimensional kernel
  (`TauCeti.SymplecticForm.finiteDimensional_ker_floerConformalSobolevOperator_pairOfPants`) and
  closed range (`TauCeti.SymplecticForm.isClosed_range_floerConformalSobolevOperator_pairOfPants`).

The finiteness of the cokernel and the Fredholm index are not treated here.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix B, on the semi-Fredholm estimate and Sobolev spaces on punctured Riemann surfaces
  with cylindrical ends.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the Fredholm theory of the pair-of-pants operator.
-/

public section

open Set Function Filter MeasureTheory Real TauCeti.ThricePuncturedSphere
open scoped ENNReal NNReal Manifold

namespace TauCeti

namespace Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **The weighted energy on the band of an end.** For `T ≥ 0` and a `C¹` section `ξ` whose
`W^{1,2}` energy in the positive end chart `φ'_q` is integrable over `(T, ∞) × [0, 1]`, as it is
for a section with compact support in `S` (`integrableOn_sobolevDensity_comp_positiveEndChart`),
the weighted energy `∫ (ρ ‖ξ‖² + ‖∂s ξ‖² + ‖∂t ξ‖²)` of `ξ` over the image of the band
`(T, ∞) × [0, 1)` under `φ'_q` is at most `20π²` times the `W^{1,2}` energy of `ξ ∘ φ'_q` over
`(T, ∞) × [0, 1]`. -/
theorem setLIntegral_image_positiveEndChart_le {T : ℝ} (hT : 0 ≤ T) {ξ : ℝ × ℝ → V}
    (hξ : ContDiff ℝ 1 ξ) (q : Puncture)
    (hint : IntegrableOn (sobolevDensity (ξ ∘ positiveEndChart q)) (Ioi T ×ˢ Icc 0 1)) :
    ∫⁻ w in positiveEndChart q '' (Ioi T ×ˢ Ico 0 1),
        ENNReal.ofReal (cylindricalWeight w * ‖ξ w‖ ^ 2 + ‖fderiv ℝ ξ w (1, 0)‖ ^ 2 +
          ‖fderiv ℝ ξ w (0, 1)‖ ^ 2) ≤
      ENNReal.ofReal (20 * π ^ 2 *
        ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart q) ζ) := by
  refine (lintegral_image_positiveEndChart_le q measurableSet_Ioi
    (fun s hs ↦ hT.trans (le_of_lt hs))
    fun ζ _ ↦ (hξ.differentiable one_ne_zero).differentiableAt).trans ?_
  rw [ENNReal.ofReal_mul (p := 20 * π ^ 2) (by positivity)]
  gcongr
  refine (le_of_eq ?_).trans ((lintegral_mono_set (prod_mono subset_rfl
    Ico_subset_Icc_self)).trans_eq (ofReal_integral_eq_lintegral_ofReal
      hint (ae_of_all _ fun ζ ↦ sobolevDensity_nonneg _ ζ)).symm)
  simp_rw [sobolevDensity_apply, stdComplexLineReal_eq, stdComplexLineImag_eq, comp_apply]

/-- **The weighted energy, from the energy of the semi-Fredholm estimate.** For `T ≥ 0` there is
`A ≥ 0` such that every `C¹` section `ξ` with compact support in the pair of pants `S` satisfies

`∫_S (ρ ‖ξ‖² + ‖∂s ξ‖² + ‖∂t ξ‖²)`
`  ≤ A (∑_q ∫_{(T, ∞) × [0, 1]} (‖∂s (ξ ∘ φ'_q)‖² + ‖∂t (ξ ∘ φ'_q)‖² + ‖ξ ∘ φ'_q‖²)`
`    + ∫_{S_T} (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²))`

for the cylindrical weight `ρ`, the positive end charts `φ'_q` and the truncation `S_T`: the
square of the norm of the jet of `ξ` in `W^{1,2}_0(S, V)` is controlled by the energy that the
semi-Fredholm estimate of the linearized Floer operator bounds. -/
theorem exists_forall_setIntegral_le_mul_sum_setIntegral_sobolevDensity_add {T : ℝ}
    (hT : 0 ≤ T) :
    ∃ A, 0 ≤ A ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 1 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ thricePuncturedSphereReal →
      ∫ z in thricePuncturedSphereReal, (cylindricalWeight z * ‖ξ z‖ ^ 2 +
          ‖fderiv ℝ ξ z (1, 0)‖ ^ 2 + ‖fderiv ℝ ξ z (0, 1)‖ ^ 2) ≤
        A * ((∑ q, ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart q) ζ) +
          ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation T, sobolevDensity ξ z) := by
  set K := Complex.equivRealProdCLM.symm ⁻¹' truncation T
  have hK : IsCompact K := isCompact_preimage_truncation T
  -- The weight is bounded on the compact truncation `S_T`.
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (isWeight_cylindricalWeight.continuousOn.mono
    (preimage_truncation_subset_thricePuncturedSphereReal T))
  have hBK (z : ℝ × ℝ) (hz : z ∈ K) : cylindricalWeight z ≤ |B| :=
    (Real.le_norm_self _).trans ((hB z hz).trans (le_abs_self B))
  refine ⟨20 * π ^ 2 + |B| + 1, by positivity, fun ξ hξ hξc hξS ↦ ?_⟩
  set f : ℝ × ℝ → ℝ := fun z ↦ cylindricalWeight z * ‖ξ z‖ ^ 2 + ‖fderiv ℝ ξ z (1, 0)‖ ^ 2 +
    ‖fderiv ℝ ξ z (0, 1)‖ ^ 2
  have hf0 (z : ℝ × ℝ) : 0 ≤ f z := by
    have := cylindricalWeight_nonneg z
    positivity
  set E : Puncture → ℝ :=
    fun q ↦ ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart q) ζ
  set E₀ := ∫ z in K, sobolevDensity ξ z
  have hEq (q : Puncture) : 0 ≤ E q :=
    setIntegral_nonneg (measurableSet_Ioi.prod measurableSet_Icc) fun ζ _ ↦
      sobolevDensity_nonneg _ ζ
  have hE0 (q : Puncture) : 0 ≤ 20 * π ^ 2 * E q := mul_nonneg (by positivity) (hEq q)
  have hE₀0 : 0 ≤ E₀ := setIntegral_nonneg hK.measurableSet fun z _ ↦ sobolevDensity_nonneg _ z
  -- `S` is covered by `S_T` and the bands of the three ends, where the energies are compared.
  have hlin : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (f z) ≤
      ENNReal.ofReal ((|B| + 1) * E₀ + ∑ q, 20 * π ^ 2 * E q) := by
    rw [ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg fun q _ ↦ hE0 q),
      ENNReal.ofReal_sum_of_nonneg fun q _ ↦ hE0 q]
    refine (lintegral_mono_set
      (subset_preimage_truncation_union_iUnion_image_positiveEndChart T)).trans
        ((lintegral_union_le _ _ _).trans (add_le_add
          (setLIntegral_le_ofReal_mul_setIntegral_sobolevDensity hK (abs_nonneg B) hBK hξ) ?_))
    exact (lintegral_iUnion_le _ _).trans_eq (tsum_fintype _) |>.trans
      (Finset.sum_le_sum fun q _ ↦ setLIntegral_image_positiveEndChart_le hT hξ q
        (integrableOn_sobolevDensity_comp_positiveEndChart hξ hξc hξS q T))
  have hfm : AEStronglyMeasurable f (volume.restrict thricePuncturedSphereReal) := by
    have := hξ.continuous_fderiv one_ne_zero
    have := hξ.continuous
    exact ((isWeight_cylindricalWeight.continuousOn.mul
      (by fun_prop : Continuous fun z ↦ ‖ξ z‖ ^ 2).continuousOn).add
        (by fun_prop : Continuous fun z ↦ ‖fderiv ℝ ξ z (1, 0)‖ ^ 2).continuousOn |>.add
        (by fun_prop : Continuous fun z ↦ ‖fderiv ℝ ξ z (0, 1)‖ ^ 2).continuousOn)
      |>.aestronglyMeasurable isOpen_thricePuncturedSphereReal.measurableSet
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf0) hfm]
  refine (ENNReal.toReal_le_of_le_ofReal (add_nonneg (by positivity)
    (Finset.sum_nonneg fun q _ ↦ hE0 q)) hlin).trans ?_
  have hsumE : 0 ≤ ∑ q, E q := Finset.sum_nonneg fun q _ ↦ hEq q
  rw [← Finset.mul_sum]
  nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 20 * π ^ 2) hE₀0,
    mul_nonneg (by positivity : (0 : ℝ) ≤ |B| + 1) hsumE]

end Floer

namespace SymplecticForm

open Floer ConformalSobolev

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Peetre's estimate for the linearized Floer operator on the pair of pants, from the
semi-Fredholm estimate.** Let the coefficient field of the linearized Floer operator `D_u` on the
conformal jets of the cylindrical weight `ρ` be essentially bounded on `S`, and suppose that for
some `T ≥ 0` every `C²` section `ξ` with compact support in `S` satisfies

`∑_q ∫_{(T, ∞) × [0, 1]} (‖∂s (ξ ∘ φ'_q)‖² + ‖∂t (ξ ∘ φ'_q)‖² + ‖ξ ∘ φ'_q‖²)`
`  + ∫_{S_T} (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{S_{T + 1}} ‖ξ‖²)`.

Then there is `C'` such that the jet `x ∈ W^{1,2}_0(S, V)` of every test section `ξ` satisfies
`‖x‖ ≤ C' (‖D_u x‖ + ‖√ρ ξ‖_{L²(S_{T + 1})})`, the estimate consumed by Peetre's argument
`TauCeti.ConformalSobolev.finiteDimensional_ker_of_estimate`. -/
theorem exists_forall_norm_le_mul_norm_floerConformalSobolevOperator_add_of_estimate
    (ω : SymplecticForm V) {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ}
    {u : ℝ × ℝ → V}
    (hM : MemLp (ω.floerConformalJetCoeff cylindricalWeight J Ks Kt u) ∞
      (volume.restrict thricePuncturedSphereReal))
    {C T : ℝ} (hT : 0 ≤ T)
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
          J Ks Kt u x‖ +
        ‖restrictWeightedValue V thricePuncturedSphereReal
          (Complex.equivRealProdCLM.symm ⁻¹' truncation (T + 1)) x‖) := by
  obtain ⟨A, hA, hW⟩ :=
    exists_forall_setIntegral_le_mul_sum_setIntegral_sobolevDensity_add (V := V) hT
  -- The weighted energy is at most `A` times the left side of the semi-Fredholm estimate.
  exact ω.exists_forall_norm_le_mul_norm_floerConformalSobolevOperator_add_of_integral_le
    isWeight_cylindricalWeight hM (isCompact_preimage_truncation _)
    (preimage_truncation_subset_thricePuncturedSphereReal _) (C := A * C) fun ξ hξ ↦ by
      obtain ⟨hξ2, hξc, hξS⟩ := mem_testSection_iff.1 hξ
      rw [mul_assoc]
      exact (hW (hξ2.of_le one_le_two) hξc hξS).trans
        (mul_le_mul_of_nonneg_left (hest hξ2 hξc hξS) hA)

/-- **The coefficients of the linearized operator along a pair of pants are bounded on the jets of
`W^{1,2}`.** Let `H_q` be jointly `C²` period-one Hamiltonians on the three ends of `S`, and let
`(J, K_s, K_t)` be Floer data on `S`, with `J` `C¹` and `K_s`, `K_t` `C²` along `u`, which far out
on each end, beyond a height `R₁`, are cylindrical, `J(φ'_q(s, t)) = J_q(t)` for `C¹` families
`J_q`, with perturbation the pair-of-pants perturbation of `H`. Let `u` be `C¹` on `S`, solve the
Floer equation for these data beyond `R₁` on each end, and have loops in each positive end chart
converging uniformly on `[0, 1]` to loops `x_q` continuous on `[0, 1]`, while the slice defects tend
uniformly to zero. Then the coefficient field of the linearized Floer operator on the conformal
jets of the cylindrical weight is essentially bounded on `S`. -/
theorem memLp_floerConformalJetCoeff_pairOfPants_of_tendstoUniformlyOn (ω : SymplecticForm V)
    {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) {x : Puncture → ℝ → V}
    (hx : ∀ q, ContinuousOn (x q) (Icc 0 1)) {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Je : Puncture → ℝ → V → AlmostComplexStructure V} {R₁ : ℝ}
    (hJe : ∀ q, ContDiff ℝ 1 fun p : ℝ × V ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJeq : ∀ q (ζ : ℝ × ℝ), R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je q ζ.2)
    {Ks Kt : ℝ × ℝ → V → ℝ}
    (hK : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      Ks z = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt z = fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hF : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ q, TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop
      (Icc 0 1))
    (hδ : ∀ q, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1)) :
    MemLp (ω.floerConformalJetCoeff cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u) ∞
      (volume.restrict thricePuncturedSphereReal) := by
  have hcont : ContinuousOn (ω.floerConformalJetCoeff cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u) thricePuncturedSphereReal :=
    ω.continuousOn_floerConformalJetCoeff isWeight_cylindricalWeight hJ hKs hKt
      fun z hz ↦ (hu z hz).contDiffWithinAt
  -- Far out on each end, the coefficient field of the end datum along `u ∘ φ'_q` is bounded over
  -- the band `t ∈ [0, 1]`.
  choose Bq hBq using fun q ↦ ω.exists_eventually_norm_floerJetCoeff_le
    (contDiff_uncurry_positiveEndHamiltonian (hHs q)) (hJe q) (hx q) (hux q) (hδ q)
  obtain ⟨T, hT⟩ := eventually_atTop.1 ((eventually_all.2 hBq).and
    (eventually_ge_atTop (max 2 R₁)))
  have hTR : max 2 R₁ ≤ T := (hT T le_rfl).2
  set B := ∑ q, |Bq q|
  have hBqB (q : Puncture) : Bq q ≤ B := (le_abs_self _).trans
    (Finset.single_le_sum (f := fun q' ↦ |Bq q'|) (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ q))
  -- Beyond the height `T` of the end `q`, the data are the pair-of-pants data.
  refine memLp_top_of_continuousOn_of_norm_positiveEndChart_le hcont (T := T)
    (M := 1 + B + (1 + B) * B / (2 * π)) fun q ζ hζ1 hζ2 ↦ ?_
  have h2 : 2 ≤ ζ.1 := by linarith [le_max_left 2 R₁]
  have hR : R₁ ≤ (positiveEndCoord q (positiveEndChart q ζ)).1 := by
    rw [fst_positiveEndCoord_positiveEndChart]
    linarith [le_max_right 2 R₁]
  have hz : positiveEndChart q ζ ∈ thricePuncturedSphereReal :=
    positiveEndChart_mem_thricePuncturedSphereReal (by linarith)
  exact ω.norm_floerConformalJetCoeff_positiveEndChart_le hH
    (fun t ↦ (hHs q).comp (contDiff_const.prodMk contDiff_id)) h2
    (hJeq q ζ (by linarith [le_max_right 2 R₁])) (hK q _ hz hR).1 (hK q _ hz hR).2
    ((hu _ hz).differentiableAt one_ne_zero) (hF q _ hz hR)
    (((hT ζ.1 hζ1.le).1 q ζ.2 (Ico_subset_Icc_self hζ2)).trans (hBqB q))

/-- **Peetre's estimate along a pair of pants.** Under the hypotheses of the semi-Fredholm
estimate `exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_add`
(Floer data `(J, K_s, K_t)` that are cylindrical and equal to the pair-of-pants data far out on the
ends, and a map `u` that solves the Floer equation there and whose ends converge to nondegenerate
one-periodic orbits of the end Hamiltonians), there are a compact set `K ⊆ S` and `C` such that the
jet `x ∈ W^{1,2}_0(S, V)` of every test section `ξ` satisfies
`‖x‖ ≤ C (‖D_u x‖ + ‖√ρ ξ‖_{L²(K)})` for the realization
`D_u = TauCeti.SymplecticForm.floerConformalSobolevOperator` of the linearized Floer operator. -/
theorem exists_forall_norm_le_mul_norm_floerConformalSobolevOperator_add (ω : SymplecticForm V)
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
    {Ks Kt : ℝ × ℝ → V → ℝ}
    (hK : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      Ks z = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt z = fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z)))
    (hF : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ q, TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop
      (Icc 0 1))
    (hδ : ∀ q, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1)) :
    ∃ K, IsCompact K ∧ K ⊆ thricePuncturedSphereReal ∧ ∃ C,
      ∀ y : H1 V thricePuncturedSphereReal cylindricalWeight,
        (y : Lp (V × V × V) 2 (volume.restrict thricePuncturedSphereReal)) ∈
          jetSubmodule V thricePuncturedSphereReal cylindricalWeight →
        ‖y‖ ≤ C * (‖ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
            (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u y‖ +
          ‖restrictWeightedValue V thricePuncturedSphereReal K y‖) := by
  obtain ⟨C, -, T, hT, hest⟩ :=
    ω.exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_add hH hHs
      hX hx hnd hJe hJex hJeq hK hJ hKs hKt hu hc hF hux hδ
  have hM := ω.memLp_floerConformalJetCoeff_pairOfPants_of_tendstoUniformlyOn hH hHs
    (fun q ↦ (continuous_iff_continuousAt.2 fun t ↦ (hx q t).continuousAt).continuousOn) hJe hJeq
    hK hJ hKs hKt hu hF hux hδ
  obtain ⟨C', hC'⟩ :=
    ω.exists_forall_norm_le_mul_norm_floerConformalSobolevOperator_add_of_estimate hM hT hest
  exact ⟨_, isCompact_preimage_truncation _, preimage_truncation_subset_thricePuncturedSphereReal _,
    C', hC'⟩

/-- **The linearized operator along a pair of pants has finite-dimensional kernel on `W^{1,2}`.**
Under the hypotheses of the semi-Fredholm estimate
`exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_add` (Floer data
`(J, K_s, K_t)` that are cylindrical and equal to the pair-of-pants data far out on the ends, and a
map `u` that solves the Floer equation there and whose ends converge to nondegenerate one-periodic
orbits of the end Hamiltonians), the realization `D_u : W^{1,2}_0(S, V) → L²(S, V)` of the
linearized Floer operator for the cylindrical metric has finite-dimensional kernel. A Floer pair of
pants is the case of the pair-of-pants data on all of `S`. -/
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
    {Ks Kt : ℝ × ℝ → V → ℝ}
    (hK : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      Ks z = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt z = fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z)))
    (hF : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ q, TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop
      (Icc 0 1))
    (hδ : ∀ q, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1)) :
    FiniteDimensional ℝ (ω.floerConformalSobolevOperator thricePuncturedSphereReal
      cylindricalWeight (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u).ker := by
  obtain ⟨K, hK, hKS, C, hest⟩ :=
    ω.exists_forall_norm_le_mul_norm_floerConformalSobolevOperator_add hH hHs hX hx hnd hJe hJex
      hJeq hK hJ hKs hKt hu hc hF hux hδ
  exact finiteDimensional_ker_of_estimate isWeight_cylindricalWeight hK hKS _ hest

/-- **The linearized operator along a pair of pants has closed range on `W^{1,2}`.** Under the
hypotheses of `finiteDimensional_ker_floerConformalSobolevOperator_pairOfPants`, the realization
`D_u : W^{1,2}_0(S, V) → L²(S, V)` of the linearized Floer operator for the cylindrical metric has
closed range. -/
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
    {Ks Kt : ℝ × ℝ → V → ℝ}
    (hK : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      Ks z = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt z = fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z)))
    (hF : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ q, TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop
      (Icc 0 1))
    (hδ : ∀ q, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1)) :
    IsClosed ((ω.floerConformalSobolevOperator thricePuncturedSphereReal
      cylindricalWeight (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u).range :
        Set (Lp V 2 (volume.restrict thricePuncturedSphereReal))) := by
  obtain ⟨K, hK, hKS, C, hest⟩ :=
    ω.exists_forall_norm_le_mul_norm_floerConformalSobolevOperator_add hH hHs hX hx hnd hJe hJex
      hJeq hK hJ hKs hKt hu hc hF hux hδ
  exact isClosed_range_of_estimate isWeight_cylindricalWeight hK hKS _ hest

end SymplecticForm

end TauCeti
