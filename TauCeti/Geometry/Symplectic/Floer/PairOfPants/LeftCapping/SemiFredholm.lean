/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Exchange.SemiFredholm
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.LeftCapping
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Complex.EquivRealProd
import TauCeti.MeasureTheory.Integral.Bochner.Multiplier

/-!
# The semi-Fredholm estimate along the input-exchange family capped at `0`

The pair-of-pants product is unital on the left because gluing the negative PSS plane of `H_0`
into the input at `0` of the pair of pants `S = ℂ ∖ {0, 1}` gives a cylinder whose counts compare
with continuation maps. The comparison runs along the input-exchange family capped at `0`,
`K_c = TauCeti.Floer.cappedExchangePerturbation H L c` for `0 ≤ c ≤ 1`. Its domain is the capped
surface `ℂ ∖ {1}`, with one input end at `1`, carrying `H_1`, and the output end recentred at `c`,
carrying `H_∞`; the capped puncture `0` is an interior point. This file proves the estimate behind
the Fredholm property of the linearized operator `D_u` of this family, on a finite-dimensional
symplectic vector space `(V, ω)`: the `W^{1,2}` energy of a section, measured in the end charts on
the two ends and in the coordinates of `ℂ` on a compact core containing `0`, is controlled by the
`L²` norms of `D_u ξ` on `ℂ ∖ {1}` and of `ξ` on a compact part of `ℂ ∖ {1}`.

* **Patching on the capped surface.**
  `exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_add_of_capped`
  derives the estimate for any Floer data regular on `ℂ ∖ {1}` from end estimates on the two
  remaining ends. Let `χ` be a cutoff equal to `1` on the disc `‖w‖ ≤ 1/3` and to `0` off the
  disc `‖w‖ < 2/5`. The section `(1 - χ) ξ` vanishes near `0`, so it is supported in `S` and stays
  below the height `1` on the end at `0`; the patching of the pair of pants for sections supported
  in a set,
  `exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_add_of_subset`,
  then needs no end estimate at `0`, and the operator differentiates the cutoff only on the disc
  `‖w‖ ≤ 1/2` (`exists_integral_norm_floerLinearization_smul_sq_le_of_tsupport_subset`). Off the
  disc `‖w‖ ≤ 2/5` the section `ξ` is `(1 - χ) ξ`, and on that disc, a compact part of `ℂ ∖ {1}`,
  the disc estimate for data regular on a set
  (`exists_forall_setIntegral_le_mul_integral_floerLinearization_add_of_lt_of_tsupport_subset`)
  controls `ξ` by `D_u ξ` and by `ξ` on the disc `‖w‖ ≤ 1/2`.
* **The family.** `exists_forall_le_mul_integral_floerLinearization_cappedExchangePerturbation_add`
  is the estimate along every member of the family, for almost complex structures that are
  cylindrical far out on the two ends and a map `u` that solves the Floer equation there and
  converges to nondegenerate orbits. Far out on the input end at `1` the capped datum is the
  pair-of-pants datum
  (`TauCeti.Floer.cappedExchangePerturbation_eq_of_pos_fst_positiveEndCoord_one`), and far out on
  the output end it is the pair-of-pants datum translated by `c`
  (`TauCeti.Floer.cappedExchangePerturbation_add_eq_of_one_lt_fst_positiveEndCoord`), so the end
  estimates of the pair of pants and of the recentred output end apply.

The Sobolev realization of the operator, the finiteness of its cokernel and its index are not
treated here.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  unit of the pair-of-pants product.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the Fredholm theory of the pair-of-pants product.
-/

public section

open Complex Filter Function MeasureTheory Set TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Topology NNReal Manifold

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-! ### Patching on the capped surface -/

omit [FiniteDimensional ℝ V] in
/-- Beyond the height `0` on the input end at `1` or on the output end, a section agrees with its
cut-off `(1 - χ) ξ` for a cutoff `χ` vanishing off the disc `‖w‖ < 1/2`. -/
private theorem setIntegral_sobolevDensity_comp_positiveEndChart_one_sub_smul {χ : ℝ × ℝ → ℝ}
    (hχ : ∀ z, 1 / 2 ≤ ‖equivRealProdCLM.symm z‖ → χ z = 0) {q : Puncture} (hq : q ≠ zero)
    {T : ℝ} (hT : 0 ≤ T) (ξ : ℝ × ℝ → V) :
    ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart q) ζ =
      ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1,
        sobolevDensity ((fun z ↦ (1 - χ z) • ξ z) ∘ positiveEndChart q) ζ := by
  refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Icc) fun ζ hζ ↦ ?_
  refine sobolevDensity_congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds
    (show (0 : ℝ) < ζ.1 by linarith [mem_Ioi.1 hζ.1])] with ζ' hζ'
  simp [hχ _ (half_le_norm_positiveEndChart hq hζ')]

omit [FiniteDimensional ℝ V] in
/-- **The core of the capped surface.** If `ξ` agrees with `ξ₁` near every point off a compact set
`D ⊇ B`, then the energy of `ξ` on `S ∪ B`, for a compact set `S`, is at most the energy of `ξ₁` on
`S` plus the energy of `ξ` on `D`. -/
private theorem setIntegral_sobolevDensity_union_le {ξ ξ₁ : ℝ × ℝ → V} (hξ : ContDiff ℝ 1 ξ)
    (hξ₁ : ContDiff ℝ 1 ξ₁) {S B D : Set (ℝ × ℝ)} (hS : IsCompact S) (hD : IsCompact D)
    (hBD : B ⊆ D) (hξξ₁ : ∀ z ∉ D, ξ =ᶠ[𝓝 z] ξ₁) :
    ∫ z in S ∪ B, sobolevDensity ξ z ≤
      (∫ z in S, sobolevDensity ξ₁ z) + ∫ z in D, sobolevDensity ξ z := by
  have hsd {g : ℝ × ℝ → V} (hg : ContDiff ℝ 1 g) {s : Set (ℝ × ℝ)} (hs : IsCompact s) :
      IntegrableOn (sobolevDensity g) s :=
    (continuous_sobolevDensity hg).continuousOn.integrableOn_compact hs
  calc _ ≤ ∫ z in S ∪ D, sobolevDensity ξ z :=
        setIntegral_mono_set (hsd hξ (hS.union hD)) (ae_of_all _ fun z ↦ sobolevDensity_nonneg _ z)
          (.of_forall (union_subset_union_right S hBD))
    _ = (∫ z in S \ D, sobolevDensity ξ₁ z) + ∫ z in D, sobolevDensity ξ z := by
        rw [← sdiff_union_self, setIntegral_union disjoint_sdiff_left hD.measurableSet
          ((hsd hξ hS).mono_set sdiff_subset) (hsd hξ hD)]
        congr 1
        exact setIntegral_congr_fun (hS.measurableSet.diff hD.measurableSet) fun z hz ↦
          sobolevDensity_congr_of_eventuallyEq (hξξ₁ z hz.2)
    _ ≤ _ := add_le_add_left (setIntegral_mono_set (hsd hξ₁ hS)
        (ae_of_all _ fun z ↦ sobolevDensity_nonneg _ z)
        (.of_forall fun z (hz : z ∈ S \ D) ↦ hz.1)) _

/-- **Patching away from the capped end.** For sections of `S` that stay below the height `1` on the
end at `0`, the patching of the pair of pants needs end estimates only on the input end at `1` and
on the output end. -/
private theorem exists_forall_sum_setIntegral_add_setIntegral_le_of_fst_positiveEndCoord_zero_le
    (ω : SymplecticForm V) {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z))) {C R : Puncture → ℝ}
    (hend : ∀ q, q ≠ zero → ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ {z | z ∈ thricePuncturedSphereReal ∧ R q < (positiveEndCoord q z).1} →
      ∫ ζ in Ioi 0 ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart q) ζ ≤
        C q * ∫ z, ‖ω.floerLinearization
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2) :
    ∃ C', 0 ≤ C' ∧ ∃ T, 1 ≤ T ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ thricePuncturedSphereReal →
      tsupport ξ ⊆ {z | (positiveEndCoord zero z).1 ≤ 1} →
      (∑ q, ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart q) ζ) +
        ∫ z in equivRealProdCLM.symm ⁻¹' truncation T, sobolevDensity ξ z ≤
        C' * ((∫ z, ‖ω.floerLinearization
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2) +
          ∫ z in equivRealProdCLM.symm ⁻¹' truncation (T + 1), ‖ξ z‖ ^ 2) := by
  refine
    ω.exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_add_of_subset
    hJ hKs hKt hu hc (C := C) (R := update R zero 1) fun q ξ hξ hξc hξR ↦ ?_
  rcases eq_or_ne q zero with rfl | hq
  · -- No section below the height `1` on the end at `0` lies beyond that height.
    have hξ0 : ξ = 0 := funext fun z ↦ by_contra fun h ↦ by
      obtain ⟨-, hzA, hz⟩ := hξR (subset_tsupport _ h)
      rw [update_self] at hz
      exact (not_lt.2 hzA) hz
    subst hξ0
    simp [ω.floerLinearization_of_notMem_tsupport _ Ks Kt u (ξ := 0) (by simp), Pi.zero_comp,
      sobolevDensity_zero]
  · rw [update_of_ne hq] at hξR
    exact hend q hq hξ hξc fun z hz ↦ ⟨(hξR hz).1, (hξR hz).2.2⟩

/-- **Patching end estimates into the semi-Fredholm estimate on the pair of pants capped at `0`.**
Let `J(z)` be compatible along `u` on the capped surface `ℂ ∖ {1}`, with `J` `C¹` and `K_s`, `K_t`
`C²` at the points `(z, u z)`, and `u` `C¹` there. Suppose that on the input end at `1` and on the
output end the linearized Floer operator `D_u` controls the energy in the positive end chart
`φ'_q`: there are `C q` and `R q` such that every `C²` section `ξ` with compact support in the part
`±s > R q` of the end satisfies
`∫_{(0, ∞) × [0, 1]} (‖∂s (ξ ∘ φ'_q)‖² + ‖∂t (ξ ∘ φ'_q)‖² + ‖ξ ∘ φ'_q‖²) ≤ C q ∫ ‖D_u ξ‖²`.
Then there are `C ≥ 0` and `T ≥ 1` such that every `C²` section `ξ` with compact support in
`ℂ ∖ {1}` satisfies

`∑_{q = 1, ∞} ∫_{(T, ∞) × [0, 1]} (‖∂s (ξ ∘ φ'_q)‖² + ‖∂t (ξ ∘ φ'_q)‖² + ‖ξ ∘ φ'_q‖²)`
`  + ∫_{S_T ∪ {‖w‖ ≤ 1/4}} (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²)`
`  ≤ C (∫ ‖D_u ξ‖² + ∫_{S_{T + 1} ∪ {‖w‖ ≤ 1/2}} ‖ξ‖²)`,

where `S_T` is the truncation of `S` at height `T`. Since `T ≥ 1`, the disc `‖w‖ ≤ 1/4` contains
the part of `ℂ ∖ {1}` beyond the height `T` on the capped end at `0`, so the left side is the
`W^{1,2}` energy of `ξ` for a metric on `ℂ ∖ {1}` that is cylindrical on the two ends. -/
theorem
    exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_add_of_capped
    (ω : SymplecticForm V) {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ}
    {u : ℝ × ℝ → V}
    (hJ : ∀ z, equivRealProdCLM.symm z ≠ 1 → ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, equivRealProdCLM.symm z ≠ 1 → ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, equivRealProdCLM.symm z ≠ 1 → ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ∀ z, equivRealProdCLM.symm z ≠ 1 → ContDiffAt ℝ 1 u z)
    (hc : ∀ z, equivRealProdCLM.symm z ≠ 1 → ω.Compatible (J z (u z))) {C R : Puncture → ℝ}
    (hend : ∀ q, q ≠ zero → ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ {z | z ∈ thricePuncturedSphereReal ∧ R q < (positiveEndCoord q z).1} →
      ∫ ζ in Ioi 0 ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart q) ζ ≤
        C q * ∫ z, ‖ω.floerLinearization
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2) :
    ∃ C', 0 ≤ C' ∧ ∃ T, 1 ≤ T ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ {z | equivRealProdCLM.symm z ≠ 1} →
      (∑ q ∈ ({one, inf} : Finset Puncture),
          ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart q) ζ) +
        ∫ z in equivRealProdCLM.symm ⁻¹' truncation T ∪
          {z | ‖equivRealProdCLM.symm z‖ ≤ 1 / 4}, sobolevDensity ξ z ≤
        C' * ((∫ z, ‖ω.floerLinearization
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2) +
          ∫ z in equivRealProdCLM.symm ⁻¹' truncation (T + 1) ∪
            {z | ‖equivRealProdCLM.symm z‖ ≤ 1 / 2}, ‖ξ z‖ ^ 2) := by
  set J' : ℝ × ℝ → V → V →L[ℝ] V := fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap
  set U : Set (ℝ × ℝ) := {z | equivRealProdCLM.symm z ≠ 1}
  set K₀ : Set (ℝ × ℝ) := {z | ‖equivRealProdCLM.symm z‖ ≤ 1 / 2}
  set D : Set (ℝ × ℝ) := {z | ‖equivRealProdCLM.symm z‖ ≤ 2 / 5}
  have hK₀ : IsCompact K₀ := isCompact_setOf_norm_equivRealProdCLM_symm_le _
  have hD : IsCompact D := isCompact_setOf_norm_equivRealProdCLM_symm_le _
  have hK₀U : K₀ ⊆ U := fun z hz h1 ↦ by
    have h : ‖equivRealProdCLM.symm z‖ ≤ 1 / 2 := hz
    rw [h1, norm_one] at h
    norm_num at h
  have hSU : thricePuncturedSphereReal ⊆ U := fun z hz ↦ (mem_thricePuncturedSphereReal_iff.1 hz).2
  -- The constants are fixed before the section: the patching on `S` away from the capped end, a
  -- cutoff `χ` equal to `1` near `‖w‖ ≤ 1/3` and vanishing near `‖w‖ ≥ 2/5`, the cost of the
  -- cutoff `1 - χ`, whose derivative lives on `K₀`, and the estimate on the disc `D` inside `K₀`.
  obtain ⟨C₁, hC₁, T, hT, h₁⟩ :=
    exists_forall_sum_setIntegral_add_setIntegral_le_of_fst_positiveEndCoord_zero_le ω
      (fun z hz ↦ hJ z (hSU hz)) (fun z hz ↦ hKs z (hSU hz)) (fun z hz ↦ hKt z (hSU hz))
      (fun z hz ↦ hu z (hSU hz)) (fun z hz ↦ hc z (hSU hz)) hend
  obtain ⟨χ, hχ, hχ01, hχ1, hχ0, -⟩ :=
    (isCompact_setOf_norm_equivRealProdCLM_symm_le (1 / 3)).exists_contDiff_cutoff_sublevel
      equivRealProdCLM.symm.continuous.norm (by norm_num : (1 / 3 : ℝ) < 2 / 5)
  have hχ2 : ContDiff ℝ 2 χ := hχ.of_le (by simp)
  have h1χ01 (z : ℝ × ℝ) : 1 - χ z ∈ Icc 0 1 := ⟨sub_nonneg.2 (hχ01 z).2, sub_le_self _ (hχ01 z).1⟩
  obtain ⟨C₂, hC₂, h₂⟩ := ω.exists_integral_norm_floerLinearization_smul_sq_le_of_tsupport_subset
    (J := J') (U := U) hJ hKs hKt hu (β := fun z ↦ 1 - χ z)
    (contDiff_const.sub (hχ2.of_le one_le_two)) h1χ01 hK₀ hK₀U fun z hz ↦ by
      rw [(show (fun w ↦ 1 - χ w) =ᶠ[𝓝 z] fun _ ↦ 1 by
        filter_upwards [hχ0 z (by
          linarith [not_le.1 (show ¬‖equivRealProdCLM.symm z‖ ≤ 1 / 2 from hz)])] with w hw
        simp [hw]).fderiv_eq]
      simp
  obtain ⟨C₀, hC₀, h₀⟩ :=
    ω.exists_forall_setIntegral_le_mul_integral_floerLinearization_add_of_lt_of_tsupport_subset
      hJ hKs hKt hu hK₀U (fun z hz ↦ hc z (hK₀U hz)) (by norm_num : (2 / 5 : ℝ) < 1 / 2)
  refine ⟨C₁ * (3 + C₂) + C₀, by positivity, T, hT, fun ξ hξ hξc hξU ↦ ?_⟩
  -- Off the disc `D` the section `ξ` is `(1 - χ) ξ`, supported in `S` below the height `1` of the
  -- end at `0`.
  set ξ₁ : ℝ × ℝ → V := fun z ↦ (1 - χ z) • ξ z
  have hξ₁ : ContDiff ℝ 2 ξ₁ := (contDiff_const.sub hχ2).smul hξ
  have hξ₁0 {z : ℝ × ℝ} (hz : ‖equivRealProdCLM.symm z‖ ≤ 1 / 3) : ξ₁ =ᶠ[𝓝 z] 0 := by
    filter_upwards [hχ1 z hz] with w hw
    simp [ξ₁, hw]
  have hξξ₁ {z : ℝ × ℝ} (hz : z ∉ D) : ξ =ᶠ[𝓝 z] ξ₁ := by
    filter_upwards [hχ0 z (not_le.1 hz).le] with w hw
    simp [ξ₁, hw]
  have h3 {z : ℝ × ℝ} (hz : z ∈ tsupport ξ₁) : 1 / 3 < ‖equivRealProdCLM.symm z‖ :=
    lt_of_not_ge fun h ↦ notMem_tsupport_iff_eventuallyEq.2 (hξ₁0 h) hz
  have hξ₁S : tsupport ξ₁ ⊆ thricePuncturedSphereReal := fun z hz ↦ by
    refine mem_thricePuncturedSphereReal_iff.2
      ⟨fun h0 ↦ ?_, hξU (tsupport_smul_subset_right _ _ hz)⟩
    have h := h3 hz
    rw [h0, norm_zero] at h
    norm_num at h
  have hξ₁A : tsupport ξ₁ ⊆ {z | (positiveEndCoord zero z).1 ≤ 1} := fun z hz ↦ by
    rw [mem_ofPred_eq, fst_positiveEndCoord_zero]
    exact re_endCoord_zero_le_one (by linarith [h3 hz, exp_neg_two_pi_div_two_le_one_third])
  -- The pieces of the estimate, with `X = ∫ ‖D_u ξ‖²` and `Y` the `L²` term of the right side.
  set X := ∫ z, ‖ω.floerLinearization J' Ks Kt u ξ z‖ ^ 2
  set Y := ∫ z in equivRealProdCLM.symm ⁻¹' truncation (T + 1) ∪ K₀, ‖ξ z‖ ^ 2
  set Y₀ := ∫ z in K₀, ‖ξ z‖ ^ 2
  have hX₁ : ∫ z, ‖ω.floerLinearization J' Ks Kt u ξ₁ z‖ ^ 2 ≤ 2 * X + C₂ * Y₀ :=
    h₂ (hξ.of_le one_le_two) hξc hξU
  have e₁ : (∑ q, ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ₁ ∘ positiveEndChart q) ζ) +
      ∫ z in equivRealProdCLM.symm ⁻¹' truncation T, sobolevDensity ξ₁ z ≤
      C₁ * ((∫ z, ‖ω.floerLinearization J' Ks Kt u ξ₁ z‖ ^ 2) +
        ∫ z in equivRealProdCLM.symm ⁻¹' truncation (T + 1), ‖ξ₁ z‖ ^ 2) :=
    h₁ hξ₁ hξc.smul_left hξ₁S hξ₁A
  have e₀ : ∫ z in D, sobolevDensity ξ z ≤ C₀ * (X + Y₀) := by
    simpa only [sobolevDensity_apply] using h₀ hξ hξc hξU
  -- The core: on `S_T` off the disc `D` the section is `(1 - χ) ξ`.
  have h14 : {z | ‖equivRealProdCLM.symm z‖ ≤ 1 / 4} ⊆ D :=
    fun z (hz : ‖equivRealProdCLM.symm z‖ ≤ 1 / 4) ↦
      (show ‖equivRealProdCLM.symm z‖ ≤ 2 / 5 by linarith)
  have hcore := setIntegral_sobolevDensity_union_le (hξ.of_le one_le_two) (hξ₁.of_le one_le_two)
    (isCompact_preimage_truncation T) hD h14 fun z hz ↦ hξξ₁ hz
  -- The ends: beyond the height `T ≥ 1` on the two ends, `ξ` agrees with `(1 - χ) ξ`.
  have hends : (∑ q ∈ ({one, inf} : Finset Puncture),
      ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart q) ζ) ≤
      ∑ q, ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ₁ ∘ positiveEndChart q) ζ := by
    rw [Finset.sum_congr rfl fun q hq ↦
      setIntegral_sobolevDensity_comp_positiveEndChart_one_sub_smul
        (fun z hz ↦ (hχ0 z (by linarith)).eq_of_nhds)
        (by rcases Finset.mem_insert.1 hq with rfl | hq <;> simp_all) (by linarith) ξ]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun q _ _ ↦
      setIntegral_nonneg (measurableSet_Ioi.prod measurableSet_Icc) fun ζ _ ↦
        sobolevDensity_nonneg _ ζ
  -- The `L²` norms of `ξ` and of `(1 - χ) ξ` on the compact sets involved are at most `Y`.
  have hY {s : Set (ℝ × ℝ)} (hs : s ⊆ equivRealProdCLM.symm ⁻¹' truncation (T + 1) ∪ K₀) :
      ∫ z in s, ‖ξ z‖ ^ 2 ≤ Y :=
    setIntegral_mono_set ((hξ.continuous.norm.pow 2).continuousOn.integrableOn_compact
      ((isCompact_preimage_truncation _).union hK₀)) (ae_of_all _ fun _ ↦ sq_nonneg _)
      (.of_forall fun _ hz ↦ hs hz)
  have hb₁ : ∫ z in equivRealProdCLM.symm ⁻¹' truncation (T + 1), ‖ξ₁ z‖ ^ 2 ≤ Y :=
    (integral_norm_smul_sq_le (ae_of_all _ fun z ↦ by
        rw [Real.norm_of_nonneg (h1χ01 z).1]; exact (h1χ01 z).2)
      ((hξ.continuous.norm.pow 2).continuousOn.integrableOn_compact
        (isCompact_preimage_truncation (T + 1)))).trans (hY subset_union_left)
  have hY₀ : Y₀ ≤ Y := hY subset_union_right
  have hY₀0 : 0 ≤ Y₀ := setIntegral_nonneg hK₀.measurableSet fun _ _ ↦ sq_nonneg _
  have hX0 : 0 ≤ X := integral_nonneg fun _ ↦ sq_nonneg _
  have hA : C₁ * ((∫ z, ‖ω.floerLinearization J' Ks Kt u ξ₁ z‖ ^ 2) +
      ∫ z in equivRealProdCLM.symm ⁻¹' truncation (T + 1), ‖ξ₁ z‖ ^ 2) ≤
      C₁ * ((3 + C₂) * (X + Y)) :=
    mul_le_mul_of_nonneg_left (by nlinarith [mul_le_mul_of_nonneg_left hY₀ hC₂]) hC₁
  have hB : C₀ * (X + Y₀) ≤ C₀ * (X + Y) := mul_le_mul_of_nonneg_left (by linarith) hC₀
  linarith

/-! ### The family -/

/-- **The semi-Fredholm estimate along the input-exchange family capped at `0`.** Let `H_q` be
jointly `C²` period-one Hamiltonians, let `L > 4` and `c ∈ [0, 1]`, and let `K_c` be the member `c`
of the input-exchange family capped at `0`, `TauCeti.Floer.cappedExchangePerturbation H L c`, with
components `K_s`, `K_t`, on the capped surface `ℂ ∖ {1}`. Suppose that on the input end at `1` and
on the output end the positive end Hamiltonians `H'_q` have globally Lipschitz suspended vector
fields, and let `x_q` be orbits of `H'_q` starting at nondegenerate fixed points of the time-one
maps. Let `J` be almost complex structures on `ℂ ∖ {1}` that far out on these two ends, beyond a
height `R₁`, are `C¹` families `J_q(t)` compatible along `x_q`: in the positive end chart `φ'_1` on
the input end and in the recentred end chart `c + φ'_∞` on the output end, where `K_c` is
`H_q(t) dt`. Let `u` be a `C¹` map on `ℂ ∖ {1}`, along which `J` is `C¹` and compatible, that
solves the Floer equation for `(J, K_c)` beyond `R₁` on the two ends, and whose ends, read in these
end charts, converge uniformly to the orbits `x_q` while the slice defects tend uniformly to zero.
Then there are `C ≥ 0` and `T ≥ 1` such that every `C²` section `ξ` with compact support in
`ℂ ∖ {1}` satisfies

`∑_{q = 1, ∞} ∫_{(T, ∞) × [0, 1]} (‖∂s (ξ ∘ φ'_q)‖² + ‖∂t (ξ ∘ φ'_q)‖² + ‖ξ ∘ φ'_q‖²)`
`  + ∫_{S_T ∪ {‖w‖ ≤ 1/4}} (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²)`
`  ≤ C (∫ ‖D_u ξ‖² + ∫_{S_{T + 1} ∪ {‖w‖ ≤ 1/2}} ‖ξ‖²)`

for the linearized Floer operator `D_u` of the data `(J, K_c)`. -/
theorem exists_forall_le_mul_integral_floerLinearization_cappedExchangePerturbation_add
    (ω : SymplecticForm V) {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) {L c : ℝ} (hL : 4 < L) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {Λ : Puncture → ℝ≥0}
    (hX : ∀ q (_ : q ≠ zero), LipschitzWith (Λ q)
      (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H q)))
    {x : Puncture → ℝ → V}
    (hx : ∀ q, q ≠ zero → ∀ t, HasDerivAt (x q)
      (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x q t)) t)
    (hnd : ∀ q (hq : q ≠ zero), IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H q) (hX q hq) 0 1) (x q 0))
    {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Je : Puncture → ℝ → V → AlmostComplexStructure V} {R₁ : ℝ}
    (hJe : ∀ q, q ≠ zero →
      ContDiff ℝ 1 fun p : ℝ × V ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ q, q ≠ zero → ∀ t, ω.Compatible (Je q t (x q t)))
    (hJeq : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart one ζ) = Je one ζ.2)
    (hJeq_inf : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart inf ζ + (c, 0)) = Je inf ζ.2)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z, equivRealProdCLM.symm z ≠ 1 → ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z, equivRealProdCLM.symm z ≠ 1 → ContDiffAt ℝ 1 u z)
    (hc : ∀ z, equivRealProdCLM.symm z ≠ 1 → ω.Compatible (J z (u z)))
    (hF : ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord one z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z)) (ω.perturbedFDeriv
        (fun z x ↦ cappedExchangePerturbation H L c (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedExchangePerturbation H L c (equivRealProdCLM.symm z) x I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    (hF_inf : ∀ z : ℝ × ℝ, R₁ ≤ (positiveEndCoord inf z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (z + (c, 0)) (u (z + (c, 0))))
        (ω.perturbedFDeriv
          (fun z x ↦ cappedExchangePerturbation H L c (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedExchangePerturbation H L c (equivRealProdCLM.symm z) x I)
          u (z + (c, 0)) : ℝ × ℝ →ₗ[ℝ] V))
    (hux : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart one (s, t))) (x one) atTop
      (Icc 0 1))
    (hux_inf : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart inf (s, t) + (c, 0))) (x inf)
      atTop (Icc 0 1))
    (hδ : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H one t))
        (u ∘ positiveEndChart one) (s, t)) 0 atTop (Icc 0 1))
    (hδ_inf : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H inf t))
        (fun ζ ↦ u (positiveEndChart inf ζ + (c, 0))) (s, t)) 0 atTop (Icc 0 1)) :
    ∃ C, 0 ≤ C ∧ ∃ T, 1 ≤ T ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ {z | equivRealProdCLM.symm z ≠ 1} →
      (∑ q ∈ ({one, inf} : Finset Puncture),
          ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart q) ζ) +
        ∫ z in equivRealProdCLM.symm ⁻¹' truncation T ∪
          {z | ‖equivRealProdCLM.symm z‖ ≤ 1 / 4}, sobolevDensity ξ z ≤
        C * ((∫ z, ‖ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ cappedExchangePerturbation H L c (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedExchangePerturbation H L c (equivRealProdCLM.symm z) x I)
          u ξ z‖ ^ 2) +
          ∫ z in equivRealProdCLM.symm ⁻¹' truncation (T + 1) ∪
            {z | ‖equivRealProdCLM.symm z‖ ≤ 1 / 2}, ‖ξ z‖ ^ 2) := by
  have hSU : thricePuncturedSphereReal ⊆ {z | equivRealProdCLM.symm z ≠ 1} :=
    fun z hz ↦ (mem_thricePuncturedSphereReal_iff.1 hz).2
  -- Beyond the height `max R₁ 2`, `K_c` is the pair-of-pants datum on the input end at `1` and its
  -- translate by `c` on the output end.
  set R₂ := max R₁ 2
  have hR₁ : R₁ ≤ R₂ := le_max_left _ _
  have h1 {r : ℝ} (hr : R₂ ≤ r) : 1 < r := by linarith [le_max_right R₁ 2]
  have hK (z : ℝ × ℝ) (_ : z ∈ thricePuncturedSphereReal) (hz : R₂ ≤ (positiveEndCoord one z).1) :
      (fun x ↦ cappedExchangePerturbation H L c (equivRealProdCLM.symm z) x 1) =
          (fun x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1) ∧
        (fun x ↦ cappedExchangePerturbation H L c (equivRealProdCLM.symm z) x I) =
          fun x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x I := by
    simp only [cappedExchangePerturbation_eq_of_pos_fst_positiveEndCoord_one (H := H) (L := L)
      (by linarith) hc₀ hc₁ (by linarith [h1 hz] : 0 < (positiveEndCoord one z).1), and_self]
  have hK_inf (z : ℝ × ℝ) (hz : R₂ ≤ (positiveEndCoord inf z).1) :
      (fun x ↦ cappedExchangePerturbation H L c (equivRealProdCLM.symm (z + (c, 0))) x 1) =
          (fun x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1) ∧
        (fun x ↦ cappedExchangePerturbation H L c (equivRealProdCLM.symm (z + (c, 0))) x I) =
          fun x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x I := by
    simp only [cappedExchangePerturbation_add_eq_of_one_lt_fst_positiveEndCoord (H := H) (L := L)
      (by linarith) hc₀ hc₁ (h1 hz), and_self]
  -- The end estimates: on the input end at `1` that of the pair of pants, on the output end that
  -- of the recentred end.
  have hend (q : Puncture) : ∃ C R : ℝ, q ≠ zero → ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ →
      HasCompactSupport ξ →
      tsupport ξ ⊆ {z | z ∈ thricePuncturedSphereReal ∧ R < (positiveEndCoord q z).1} →
      ∫ ζ in Ioi 0 ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart q) ζ ≤
        C * ∫ z, ‖ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ cappedExchangePerturbation H L c (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedExchangePerturbation H L c (equivRealProdCLM.symm z) x I)
          u ξ z‖ ^ 2 := by
    match q with
    | zero => exact ⟨0, 0, fun h ↦ absurd rfl h⟩
    | one =>
      obtain ⟨C, R, h⟩ :=
        ω.exists_forall_setIntegral_comp_positiveEndChart_le_mul_integral_floerLinearization hH
          hHs one (hX one (by decide)) (hx one (by decide)) (hnd one (by decide))
          (hJe one (by decide)) (hJex one (by decide)) (R₁ := R₂)
          (fun ζ hζ ↦ hJeq ζ (hR₁.trans hζ)) hK (fun z hz ↦ hJ z (hSU hz))
          (fun z hz ↦ hu z (hSU hz)) (fun z hz hzR ↦ hF z hz (hR₁.trans hzR)) hux hδ
      exact ⟨C, R, fun _ ↦ h⟩
    | inf =>
      obtain ⟨C, R, h⟩ :=
    exists_forall_setIntegral_comp_positiveEndChart_le_mul_integral_floerLinearization_of_recentered
          ω hH hHs hc₀ hc₁ (hX inf (by decide)) (hx inf (by decide)) (hnd inf (by decide))
          (hJe inf (by decide)) (hJex inf (by decide)) (R₁ := R₂)
          (fun ζ hζ ↦ hJeq_inf ζ (hR₁.trans hζ)) hK_inf (fun z hz ↦ hJ z (hSU hz))
          (fun z hz ↦ hu z (hSU hz)) (fun z hz ↦ hF_inf z (hR₁.trans hz)) hux_inf hδ_inf
      exact ⟨C, R, fun _ ↦ h⟩
  choose C R hest using hend
  exact
  exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_add_of_capped ω
    hJ (fun z hz ↦ contDiffAt_uncurry_cappedExchangePerturbation hH hHs hL c hz (u z) 1)
    (fun z hz ↦ contDiffAt_uncurry_cappedExchangePerturbation hH hHs hL c hz (u z) I) hu hc
    fun q hq ↦ hest q hq

end TauCeti.SymplecticForm
