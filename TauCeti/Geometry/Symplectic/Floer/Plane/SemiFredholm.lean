/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Plane.Linearization
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Complex.EquivRealProd
import TauCeti.Geometry.Symplectic.Floer.InteriorEstimate
import TauCeti.Geometry.Symplectic.Floer.SemiFredholm
import TauCeti.Geometry.Symplectic.Floer.Plane.Curvature

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
  Floer data that are regular along `u`, with `J` compatible along `u`, an estimate of `D_u` on
  sections supported far out on the end implies the semi-Fredholm estimate. The section is cut
  into an end piece and a core piece by smooth cutoffs of the plane. On the end piece the end
  estimate applies, on the core piece the `L²` estimate of a Cauchy–Riemann operator with
  domain-dependent compatible structure on sections supported in a compact set
  (`TauCeti.Geometry.Symplectic.Floer.InteriorEstimate`), and the cutoffs cost only `L²` norms of
  `ξ` on a compact disc, by the Leibniz rule
  `D_u (β ξ) = β D_u ξ + (∂s β) ξ + J ((∂t β) ξ)`
  (`TauCeti.SymplecticForm.exists_integral_norm_floerLinearization_smul_sq_le`).
* `exists_forall_le_mul_integral_floerLinearization_add_of_finite_energy` is the semi-Fredholm
  estimate along a finite-energy PSS plane whose ends converge to nondegenerate orbits, with
  structures cylindrical on the end, for which the end estimate is
  `exists_forall_setIntegral_comp_realChart_le_mul_integral_floerLinearization_of_finite_energy`.

The target is a symplectic vector space. The Sobolev realization of `D_u` on the plane and its
Fredholm property are not treated here.

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

omit [FiniteDimensional ℝ V] in
/-- On the cylinder of the end, the `W^{1,2}` energy density of the lift of a `C¹` section with
compact support in a part `‖w‖ > exp (2π r)` of the end is integrable over `ℝ × [0, 1]`: the lift
vanishes outside a band of finite length. -/
private theorem integrableOn_comp_realChart_cylindricalEndLift (p : PSSPlane)
    {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 1 ξ) (hξc : HasCompactSupport ξ) {r : ℝ}
    (hξr : tsupport ξ ⊆ {z | Real.exp (2 * π * r) < ‖Complex.equivRealProdCLM.symm z‖}) :
    IntegrableOn (fun ζ ↦
      ‖fderiv ℝ (ξ ∘ realChart p.cylindricalEndLift) ζ stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ (ξ ∘ realChart p.cylindricalEndLift) ζ stdComplexLineImag‖ ^ 2 +
        ‖(ξ ∘ realChart p.cylindricalEndLift) ζ‖ ^ 2) (univ ×ˢ Icc (0 : ℝ) 1) := by
  set φ := realChart p.cylindricalEndLift
  have hφ : ContDiff ℝ 1 φ := contDiff_realChart p.contDiff_cylindricalEndLift
  have hξφ : ContDiff ℝ 1 (ξ ∘ φ) := hξ.comp hφ
  have := hξφ.continuous_fderiv one_ne_zero
  have hg : Continuous fun ζ ↦ ‖fderiv ℝ (ξ ∘ φ) ζ stdComplexLineReal‖ ^ 2 +
      ‖fderiv ℝ (ξ ∘ φ) ζ stdComplexLineImag‖ ^ 2 + ‖(ξ ∘ φ) ζ‖ ^ 2 := by fun_prop
  -- The section is bounded by `N` in norm on its support, so its lift lives in a finite band.
  obtain ⟨N, hN⟩ := hξc.exists_bound_of_continuousOn
    (Complex.equivRealProdCLM.symm.continuous.norm.continuousOn (s := tsupport ξ))
  set S := |r| + |Real.log N| / (2 * π)
  refine IntegrableOn.of_forall_sdiff_eq_zero (s := Icc (-S) S ×ˢ Icc 0 1)
    (hg.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))
    (MeasurableSet.univ.prod measurableSet_Icc) fun ζ hζ ↦ ?_
  -- Points outside the band are outside the support of the lift.
  have hζφ : ζ ∉ tsupport (ξ ∘ φ) := fun h ↦ by
    have hmem := tsupport_comp_subset_preimage ξ hφ.continuous h
    have h₁ := hξr hmem
    have h₂ := hN _ hmem
    simp only [mem_ofPred_eq, φ, norm_symm_realChart_cylindricalEndLift] at h₁ h₂
    rw [Real.norm_of_nonneg (Real.exp_pos _).le] at h₂
    have hπ : 0 < 2 * π := by positivity
    have h₃ : 2 * π * (p.endSign * ζ.1) ≤ Real.log N := by
      rw [← Real.log_exp (2 * π * _)]
      exact Real.log_le_log (Real.exp_pos _) h₂
    have h₄ : r < p.endSign * ζ.1 := lt_of_mul_lt_mul_left (Real.exp_lt_exp.1 h₁) hπ.le
    have h₅ : p.endSign * ζ.1 ≤ |Real.log N| / (2 * π) := by
      rw [le_div_iff₀' hπ]
      exact h₃.trans (le_abs_self _)
    have h₆ : |p.endSign * ζ.1| ≤ S := abs_le.2
      ⟨by linarith [neg_abs_le r, div_nonneg (abs_nonneg (Real.log N)) hπ.le],
        by linarith [abs_nonneg r]⟩
    rw [abs_mul, abs_endSign, one_mul] at h₆
    exact hζ.2 ⟨abs_le.1 h₆, hζ.1.2⟩
  have hev := notMem_tsupport_iff_eventuallyEq.1 hζφ
  simp [hev.fderiv_eq, show ξ (φ ζ) = 0 from hev.eq_of_nhds]

omit [FiniteDimensional ℝ V] in
/-- **Comparing with a cut-off section on the end.** If `β = 1` near every point with
`‖w‖ ≥ exp (2π R)`, then on the part `ε s > R` of the end the lift of `ξ` has the energy density
of the lift of `β ξ`, so its `W^{1,2}` energy there is at most that of the lift of `β ξ` over
`ℝ × [0, 1]`, provided the latter is integrable. -/
private theorem setIntegral_comp_realChart_le_of_eventuallyEq_one (p : PSSPlane)
    {ξ : ℝ × ℝ → V} {β : ℝ × ℝ → ℝ} {R : ℝ}
    (hβ1 : ∀ z, Real.exp (2 * π * R) ≤ ‖Complex.equivRealProdCLM.symm z‖ → β =ᶠ[𝓝 z] 1)
    (hint : IntegrableOn (fun ζ ↦
      ‖fderiv ℝ ((fun w ↦ β w • ξ w) ∘ realChart p.cylindricalEndLift) ζ stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ ((fun w ↦ β w • ξ w) ∘ realChart p.cylindricalEndLift) ζ
          stdComplexLineImag‖ ^ 2 +
        ‖((fun w ↦ β w • ξ w) ∘ realChart p.cylindricalEndLift) ζ‖ ^ 2) (univ ×ˢ Icc (0 : ℝ) 1)) :
    ∫ ζ in {s : ℝ | R < p.endSign * s} ×ˢ Icc (0 : ℝ) 1,
        (‖fderiv ℝ (ξ ∘ realChart p.cylindricalEndLift) ζ stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ (ξ ∘ realChart p.cylindricalEndLift) ζ stdComplexLineImag‖ ^ 2 +
          ‖(ξ ∘ realChart p.cylindricalEndLift) ζ‖ ^ 2) ≤
      ∫ ζ in univ ×ˢ Icc (0 : ℝ) 1,
        (‖fderiv ℝ ((fun w ↦ β w • ξ w) ∘ realChart p.cylindricalEndLift) ζ
            stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ ((fun w ↦ β w • ξ w) ∘ realChart p.cylindricalEndLift) ζ
            stdComplexLineImag‖ ^ 2 +
          ‖((fun w ↦ β w • ξ w) ∘ realChart p.cylindricalEndLift) ζ‖ ^ 2) := by
  set φ := realChart p.cylindricalEndLift
  have hφ : Continuous φ := (contDiff_realChart (n := 0) p.contDiff_cylindricalEndLift).continuous
  refine le_of_eq_of_le (setIntegral_congr_fun
    ((measurableSet_lt measurable_const (measurable_id.const_mul _)).prod measurableSet_Icc)
    fun ζ hζ ↦ ?_) (setIntegral_mono_set hint (ae_of_all _ fun _ ↦ by positivity)
      (ae_of_all _ (prod_mono (subset_univ _) subset_rfl)))
  -- Far out on the end the cut-off section agrees with `ξ` near every point.
  have hφζ : Real.exp (2 * π * R) ≤ ‖Complex.equivRealProdCLM.symm (φ ζ)‖ := by
    rw [norm_symm_realChart_cylindricalEndLift]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hζ.1.le (by positivity))
  have hev : (fun w ↦ β w • ξ w) ∘ φ =ᶠ[𝓝 ζ] ξ ∘ φ :=
    ((hφ.tendsto ζ).eventually (hβ1 _ hφζ)).mono fun ζ' h ↦ by
      simp [show β (φ ζ') = 1 from h]
  simp only [← hev.fderiv_eq, ← hev.eq_of_nhds]

omit [FiniteDimensional ℝ V] in
/-- **Comparing with a cut-off section on a disc.** If `β = 1` near every point of the disc
`‖w‖ ≤ a` and `a ≤ b`, then the `W^{1,2}` energy of `ξ` on that disc is at most the energy of
`β ξ` on the disc `‖w‖ ≤ b`, split into its derivative and `L²` parts. -/
private theorem setIntegral_le_of_eventuallyEq_one {ξ : ℝ × ℝ → V} {β : ℝ × ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hβ1 : ∀ z, ‖Complex.equivRealProdCLM.symm z‖ ≤ a → β =ᶠ[𝓝 z] 1)
    (hβξ : ContDiff ℝ 1 fun w ↦ β w • ξ w) :
    ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ a},
        (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 +
          ‖ξ z‖ ^ 2) ≤
      (∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ b},
        (‖fderiv ℝ (fun w ↦ β w • ξ w) z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ (fun w ↦ β w • ξ w) z stdComplexLineImag‖ ^ 2)) +
        ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ b}, ‖β z • ξ z‖ ^ 2 := by
  have hK := isCompact_setOf_norm_equivRealProdCLM_symm_le b
  have hdξ := hβξ.continuous_fderiv one_ne_zero
  have hF : Continuous fun z ↦ ‖fderiv ℝ (fun w ↦ β w • ξ w) z stdComplexLineReal‖ ^ 2 +
      ‖fderiv ℝ (fun w ↦ β w • ξ w) z stdComplexLineImag‖ ^ 2 := by fun_prop
  have hG : Continuous fun z ↦ ‖β z • ξ z‖ ^ 2 := hβξ.continuous.norm.pow 2
  rw [← integral_add (hF.continuousOn.integrableOn_compact hK)
    (hG.continuousOn.integrableOn_compact hK)]
  refine le_of_eq_of_le (setIntegral_congr_fun (measurableSet_le
    Complex.equivRealProdCLM.symm.continuous.norm.measurable measurable_const) fun z hz ↦ ?_)
    (setIntegral_mono_set ((hF.add hG).continuousOn.integrableOn_compact hK)
      (ae_of_all _ fun _ ↦ by positivity)
      (ae_of_all _ fun z (hz : _ ≤ a) ↦ (show _ ≤ b from hz.trans hab)))
  -- Near the disc `‖w‖ ≤ a` the cut-off section agrees with `ξ`.
  have hev : (fun w ↦ β w • ξ w) =ᶠ[𝓝 z] ξ := (hβ1 z hz).mono fun z' h ↦ by
    simp [show β z' = 1 from h]
  simp only [hev.fderiv_eq, show β z • ξ z = ξ z from hev.eq_of_nhds]

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
  have hlt : Real.exp (2 * π * Re) < Real.exp (2 * π * (Re + 1)) :=
    Real.exp_lt_exp.2 (by nlinarith [Real.pi_pos])
  -- A cutoff `β = 1 - ψ` vanishing near `‖w‖ ≤ exp (2π Re)` and equal to `1` near
  -- `‖w‖ ≥ exp (2π (Re + 1))`.
  obtain ⟨ψ, hψ, hψ01, hψ1, hψ0, hψK⟩ :=
    (isCompact_setOf_norm_equivRealProdCLM_symm_le _).exists_contDiff_cutoff_sublevel
      Complex.equivRealProdCLM.symm.continuous.norm hlt
  set β : ℝ × ℝ → ℝ := fun z ↦ 1 - ψ z
  have hβ : ContDiff ℝ 2 β := (contDiff_const.sub hψ).of_le (by simp)
  have hβ01 (z : ℝ × ℝ) : β z ∈ Icc 0 1 := ⟨by simp [β, (hψ01 z).2], by simp [β, (hψ01 z).1]⟩
  have hβ0 (z : ℝ × ℝ) (hz : _ ≤ Real.exp (2 * π * Re)) : β =ᶠ[𝓝 z] 0 :=
    (hψ1 z hz).mono fun z' h ↦ by simp [β, show ψ z' = 1 from h]
  have hβ1 (z : ℝ × ℝ) (hz : Real.exp (2 * π * (Re + 1)) ≤ _) : β =ᶠ[𝓝 z] 1 :=
    (hψ0 z hz).mono fun z' h ↦ by simp [β, show ψ z' = 0 from h]
  have hdβ (z : ℝ × ℝ) : fderiv ℝ β z = -fderiv ℝ ψ z :=
    fderiv_const_sub 1
  obtain ⟨C₁, -, herr⟩ := ω.exists_integral_norm_floerLinearization_smul_sq_le
    (J := fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) hJ hKs hKt hu
    (hβ.of_le one_le_two) hβ01 (isCompact_setOf_norm_equivRealProdCLM_symm_le _)
    fun z hz ↦ by rw [hdβ, hψK z (not_le.1 hz), neg_zero]
  refine ⟨max Ce 0 * max 2 C₁, by positivity, fun ξ hξ hξc ↦ ?_⟩
  -- The cut-off section `β ξ` is supported in the part `‖w‖ > exp (2π Re)` of the end.
  have hξ₁c : HasCompactSupport fun w ↦ β w • ξ w := hξc.smul_left
  have hξ₁r : tsupport (fun w ↦ β w • ξ w) ⊆
      {z | Real.exp (2 * π * Re) < ‖Complex.equivRealProdCLM.symm z‖} := fun z hz ↦ by
    rw [mem_ofPred_eq]
    exact not_le.1 fun h ↦
      notMem_tsupport_iff_eventuallyEq.2 (hβ0 z h) (tsupport_smul_subset_left _ _ hz)
  have hI₁ : 0 ≤ ∫ z, ‖ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
      Ks Kt u ξ z‖ ^ 2 := integral_nonneg fun _ ↦ by positivity
  have hI₂ : 0 ≤ ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * (Re + 1))},
      ‖ξ z‖ ^ 2 := setIntegral_nonneg_of_ae_restrict (ae_of_all _ fun _ ↦ by positivity)
  calc _ ≤ _ := setIntegral_comp_realChart_le_of_eventuallyEq_one p hβ1
        (integrableOn_comp_realChart_cylindricalEndLift p ((hβ.smul hξ).of_le one_le_two) hξ₁c
          hξ₁r)
    _ ≤ _ := he (hβ.smul hξ) hξ₁c hξ₁r
    _ ≤ max Ce 0 * ∫ z, ‖ω.floerLinearization
        (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u (fun w ↦ β w • ξ w) z‖ ^ 2 :=
        by gcongr; exact le_max_left _ _
    _ ≤ _ := by
        rw [mul_assoc]
        gcongr
        refine (herr (hξ.of_le one_le_two) hξc).trans ?_
        nlinarith [le_max_left 2 C₁, le_max_right 2 C₁]

/-- **The estimate on a disc.** If `J` is compatible along `u`, then for `a < b` the operator `D_u`
controls the `W^{1,2}` norm on the disc `‖w‖ ≤ a` of every section of compact support, up to an
`L²` norm on the disc `‖w‖ ≤ b`. -/
private theorem exists_setIntegral_le_of_core (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiff ℝ 1 u)
    (hc : ∀ z, ω.Compatible (J z (u z))) {a b : ℝ} (hab : a < b) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ a},
          (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 +
            ‖ξ z‖ ^ 2) ≤
        C * ((∫ z, ‖ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          Ks Kt u ξ z‖ ^ 2) + ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ b}, ‖ξ z‖ ^ 2) := by
  set K := {z : ℝ × ℝ | ‖Complex.equivRealProdCLM.symm z‖ ≤ b}
  have hK : IsCompact K := isCompact_setOf_norm_equivRealProdCLM_symm_le b
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  obtain ⟨C₀, hC₀, hcore⟩ :=
   exists_forall_setIntegral_norm_fderiv_sq_le_mul_setIntegral_floerLinearization_of_tsupport_subset
      ω (μ := volume) hK (fun z _ ↦ hJ z) (fun z _ ↦ hKs z) (fun z _ ↦ hKt z)
      (fun z _ ↦ hu.contDiffAt) fun z _ ↦ hc z
  set J' : ℝ × ℝ → V → V →L[ℝ] V := fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap
  -- A cutoff `β` equal to `1` near `‖w‖ ≤ a` and vanishing near `‖w‖ ≥ b`.
  obtain ⟨β, hβ, hβ01, hβ1, hβ0, hβK⟩ :=
    (isCompact_setOf_norm_equivRealProdCLM_symm_le a).exists_contDiff_cutoff_sublevel
      Complex.equivRealProdCLM.symm.continuous.norm hab
  obtain ⟨C₁, hC₁, herr⟩ := ω.exists_integral_norm_floerLinearization_smul_sq_le (J := J') hJ hKs
    hKt hu (hβ.of_le (by simp)) hβ01 hK fun z hz ↦ hβK z (not_le.1 hz)
  refine ⟨C₀ * (C₁ + 3) + 1, by positivity, fun ξ hξ hξc ↦ ?_⟩
  set ξ₀ : ℝ × ℝ → V := fun w ↦ β w • ξ w
  have hξ₀ : ContDiff ℝ 2 ξ₀ := (hβ.of_le (by simp)).smul hξ
  have hξ₀K : tsupport ξ₀ ⊆ K := fun z hz ↦ by
    rw [mem_ofPred_eq]
    exact (not_le.1 fun h ↦ notMem_tsupport_iff_eventuallyEq.2 (hβ0 z h)
      (tsupport_smul_subset_left _ _ hz)).le
  -- The cutoff does not increase the `L²` norm on `K`.
  have hξ₀ξ : ∫ z in K, ‖ξ₀ z‖ ^ 2 ≤ ∫ z in K, ‖ξ z‖ ^ 2 :=
    setIntegral_mono_on ((hξ₀.continuous.norm.pow 2).continuousOn.integrableOn_compact hK)
      ((hξ.continuous.norm.pow 2).continuousOn.integrableOn_compact hK) hK.measurableSet
        fun z _ ↦ by
          simp only [ξ₀, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hβ01 z).1, mul_pow]
          exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ (hβ01 z).1 (hβ01 z).2)
  -- Combine the disc comparison, the `L²` estimate of `D` on `K` and the cost of the cutoff.
  have h₁ : ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ a},
        (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 +
          ‖ξ z‖ ^ 2) ≤
      (∫ z in K, (‖fderiv ℝ ξ₀ z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ ξ₀ z stdComplexLineImag‖ ^ 2)) + ∫ z in K, ‖ξ₀ z‖ ^ 2 :=
    setIntegral_le_of_eventuallyEq_one hab.le hβ1 (hξ₀.of_le one_le_two)
  have h₂ : ∫ z, ‖ω.floerLinearization J' Ks Kt u ξ₀ z‖ ^ 2 ≤
      2 * (∫ z, ‖ω.floerLinearization J' Ks Kt u ξ z‖ ^ 2) + C₁ * ∫ z in K, ‖ξ z‖ ^ 2 :=
    herr (hξ.of_le one_le_two) hξc
  have h₃ : ∫ z in K, (‖fderiv ℝ ξ₀ z stdComplexLineReal‖ ^ 2 +
      ‖fderiv ℝ ξ₀ z stdComplexLineImag‖ ^ 2) ≤
      C₀ * ((∫ z, ‖ω.floerLinearization J' Ks Kt u ξ₀ z‖ ^ 2) + ∫ z in K, ‖ξ₀ z‖ ^ 2) := by
    have hD := ω.integrable_norm_floerLinearization_sq (J := J') hJ hKs hKt hu
      (hξ₀.of_le one_le_two) hξc.smul_left
    refine (hcore hξ₀ hξ₀K).trans (mul_le_mul_of_nonneg_left ((integral_add hD.integrableOn
      ((hξ₀.continuous.norm.pow 2).continuousOn.integrableOn_compact hK)).trans_le
        (add_le_add_left (setIntegral_le_integral hD (ae_of_all _ fun _ ↦ by positivity)) _)) hC₀)
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add h₂ hξ₀ξ) hC₀,
    integral_nonneg (μ := volume) fun z ↦ sq_nonneg ‖ω.floerLinearization J' Ks Kt u ξ z‖,
    mul_nonneg hC₀ (by positivity : 0 ≤ (C₁ + 1) *
      (∫ z, ‖ω.floerLinearization J' Ks Kt u ξ z‖ ^ 2) + 2 * ∫ z in K, ‖ξ z‖ ^ 2)]

/-- **Patching an end estimate into the semi-Fredholm estimate on a PSS plane.** Let `J(z)` be
compatible along `u`, with `J` `C¹` and `K_s`, `K_t` `C²` at the points `(z, u z)`, and `u` `C¹`.
Suppose that the linearized Floer operator `D_u` controls the `W^{1,2}` norm on the end: there are
`Ce` and `Re` such that every `C²` section `ξ` of compact support in the part
`‖w‖ > exp (2π Re)` of the plane satisfies `∫ (‖∂s (ξ ∘ φ)‖² + ‖∂t (ξ ∘ φ)‖² + ‖ξ ∘ φ‖²) ≤
Ce ∫ ‖D_u ξ‖²`, the left integral over `ℝ × [0, 1]` in the cylinder coordinates of the end lift
`φ`. Then there are `C ≥ 0` and `R` such that every `C²` section `ξ` of compact support satisfies

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
    (hc : ∀ z, ω.Compatible (J z (u z))) {Ce Re : ℝ}
    (he : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ {z | Real.exp (2 * π * Re) < ‖Complex.equivRealProdCLM.symm z‖} →
      ∫ ζ in univ ×ˢ Icc (0 : ℝ) 1,
          (‖fderiv ℝ (ξ ∘ realChart p.cylindricalEndLift) ζ stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ (ξ ∘ realChart p.cylindricalEndLift) ζ stdComplexLineImag‖ ^ 2 +
            ‖(ξ ∘ realChart p.cylindricalEndLift) ζ‖ ^ 2) ≤
        Ce * ∫ z, ‖ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          Ks Kt u ξ z‖ ^ 2) :
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
  obtain ⟨C₂, hC₂, hcore⟩ := exists_setIntegral_le_of_core ω hJ hKs hKt hu hc
    (a := Real.exp (2 * π * (Re + 1))) (b := Real.exp (2 * π * (Re + 1 + 1)))
    (Real.exp_lt_exp.2 (by nlinarith [Real.pi_pos]))
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

section FiniteEnergy

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The semi-Fredholm estimate on a finite-energy PSS plane.** Let `u` be a `C¹` map, `C³` on a
part `‖w‖ > r` of the end of the PSS plane `p`, solving there the Floer equation for the
perturbation of a jointly `C³` period-one Hamiltonian `H` with globally Lipschitz suspended vector
field, with finite energy and values in a compact set `K` on which every one-periodic orbit of `H`
is nondegenerate. Let the structures `J` be `C¹` along `u` and compatible along `u`, and on that
part of the end equal to a `C²` period-one family `J_q(t)` read in the angular coordinate, with
`J_q` compatible on `K`. Then there are `C ≥ 0` and `R` such that every `C²` section `ξ` of
compact support satisfies

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
    (hc : ∀ z, ω.Compatible (J z (u z)))
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
  exact ω.exists_forall_le_mul_integral_floerLinearization_add_of_end p hJ
    (fun _ ↦ (contDiff_uncurry_perturbation (p := p) hH hHs₂ 1).contDiffAt)
    (fun _ ↦ (contDiff_uncurry_perturbation (p := p) hH hHs₂ Complex.I).contDiffAt) hu hc he

end FiniteEnergy

end TauCeti.SymplecticForm
