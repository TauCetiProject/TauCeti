/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Linearization.Basic
public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.VaryingStructure
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Complex.EquivRealProd
import TauCeti.Topology.Constructions.SumProd

/-!
# The `L²` estimate of the linearized Floer operator on compact parts of the domain

Let `(V, ω)` be a finite-dimensional symplectic vector space, `J(z, y)` a family of almost complex
structures on `V` depending on the domain point `z = (s, t)` and the target point `y`, and
`Ks ds + Kt dt` a Hamiltonian perturbation. The linearized Floer operator along a map `u`
(`TauCeti.SymplecticForm.floerLinearization`) is

`D_u ξ = ∂s ξ - dX_Ks(u) ξ + (dJ(u) ξ)(∂t u - X_Kt(u)) + J(u)(∂t ξ - dX_Kt(u) ξ)`,

that is, `∂s ξ + J(z, u z) ∂t ξ` plus a zeroth-order term in `ξ` with coefficients continuous in
`z` (`TauCeti.SymplecticForm.floerLinearization_eq_add`). When `J(z, u z)` is `ω`-compatible,
the `L²` estimate for Cauchy--Riemann operators with domain-dependent compatible structures applies
(`TauCeti.Geometry.Symplectic.JHolomorphic.Energy.VaryingStructure`): on a compact set `K` of the
domain there is a constant `C`, depending only on the data, the map `u` and `K`, such that

`∫_K (‖∂s ξ‖² + ‖∂t ξ‖²) ≤ C ∫_K (‖D_u ξ‖² + ‖ξ‖²)`

for every `C²` section `ξ` with support in `K`, which is
`exists_forall_setIntegral_norm_fderiv_sq_le_mul_setIntegral_floerLinearization_of_tsupport_subset`,
and on a finite cylinder `[a, b] × [0, 1]` for every `C²` section closing up in `t`,
`ξ(s, 1) = ξ(s, 0)` for `s ∈ [a, b]`, and vanishing on the slices `s = a` and `s = b`
(`exists_forall_setIntegral_norm_fderiv_sq_le_mul_setIntegral_floerLinearization_of_periodic`).
For compatible data on the whole plane, a cutoff between two discs `‖w‖ ≤ a < b` turns the first
estimate into one for every `C²` section of compact support,

`∫_{‖w‖ ≤ a} (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{‖w‖ ≤ b} ‖ξ‖²)`

(`exists_forall_setIntegral_le_mul_integral_floerLinearization_add_of_lt`).

No nondegeneracy, no Floer equation for `u` and no smallness of the data is assumed: the regularity
needed is only at the points of `K`. The estimate controls the derivative of `ξ` and not `ξ`
itself. On the cylindrical ends of a Floer domain the operator converges to a translation
invariant one, and at a nondegenerate orbit the stationary cylinder estimate
(`TauCeti.Floer.exists_forall_setIntegral_le_mul_setIntegral_stationaryCylinderOperator`) controls
`ξ` as well. The estimate here is the one on the compact part of the domain in the semi-Fredholm
estimate of the linearized operator, which bounds the `W^{1,2}` norm of a section by the `L²` norms
of `D_u ξ` and of `ξ` on a compact set.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 3.1
  and Appendix B.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2.
-/

public section

namespace TauCeti.SymplecticForm

open ContinuousLinearMap Filter Function Set MeasureTheory
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The `L²` estimate of the linearized Floer operator on compactly supported sections.** Let
`K ⊆ ℝ × ℝ` be compact, and suppose that at every `z ∈ K` the structure `J(z, u z)` is
`ω`-compatible, `J` is `C¹` and the Hamiltonians `Ks`, `Kt` are `C²` at `(z, u z)`, and `u` is
`C¹` at `z`. Then there is a constant `C ≥ 0` such that every `C²` section `ξ` with support in
`K` satisfies `∫_K (‖∂s ξ‖² + ‖∂t ξ‖²) ≤ C ∫_K (‖D_u ξ‖² + ‖ξ‖²)` for the linearized Floer
operator `D_u`, with respect to an additive Haar measure. -/
theorem
  exists_forall_setIntegral_norm_fderiv_sq_le_mul_setIntegral_floerLinearization_of_tsupport_subset
    (ω : SymplecticForm V) {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ}
    {u : ℝ × ℝ → V} {K : Set (ℝ × ℝ)} {μ : Measure (ℝ × ℝ)} [μ.IsAddHaarMeasure]
    (hK : IsCompact K)
    (hJ : ∀ z ∈ K, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z ∈ K, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ K, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ∀ z ∈ K, ContDiffAt ℝ 1 u z) (hc : ∀ z ∈ K, ω.Compatible (J z (u z))) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → tsupport ξ ⊆ K →
      ∫ z in K, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2) ∂μ ≤
        C * ∫ z in K, (‖ω.floerLinearization
            (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2 +
          ‖ξ z‖ ^ 2) ∂μ := by
  obtain ⟨C, hC, h⟩ := exists_forall_setIntegral_norm_fderiv_sq_le_of_tsupport_subset (μ := μ) hK
    hc (continuousOn_comp_prodMk_of_continuousAt (fun z hz ↦ (hJ z hz).continuousAt)
      fun z hz ↦ (hu z hz).continuousAt.continuousWithinAt)
    (ω.continuousOn_floerLinearizationCoeff
      (J := fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) hJ hKs hKt hu)
  refine ⟨C, hC, fun ξ hξ hξK ↦ (h hξ hξK).trans_eq ?_⟩
  simp only [floerLinearization_eq_add, LinearMap.coe_toContinuousLinearMap']

/-- **The `L²` estimate of the linearized Floer operator on a finite cylinder.** Under the
hypotheses of
`exists_forall_setIntegral_norm_fderiv_sq_le_mul_setIntegral_floerLinearization_of_tsupport_subset`
on the rectangle `[a, b] × [0, 1]`, there is a constant `C ≥ 0` such that every `C²` section `ξ`
with `ξ(s, 1) = ξ(s, 0)` for `s ∈ [a, b]` that vanishes on the slices `s = a` and `s = b` satisfies
`∫ (‖∂s ξ‖² + ‖∂t ξ‖²) ≤ C ∫ (‖D_u ξ‖² + ‖ξ‖²)` over the rectangle. -/
theorem
  exists_forall_setIntegral_norm_fderiv_sq_le_mul_setIntegral_floerLinearization_of_periodic
    (ω : SymplecticForm V) {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ}
    {u : ℝ × ℝ → V} {a b : ℝ} (hab : a ≤ b)
    (hJ : ∀ z ∈ Icc a b ×ˢ Icc 0 1, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z ∈ Icc a b ×ˢ Icc 0 1, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ Icc a b ×ˢ Icc 0 1, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ∀ z ∈ Icc a b ×ˢ Icc 0 1, ContDiffAt ℝ 1 u z)
    (hc : ∀ z ∈ Icc a b ×ˢ Icc 0 1, ω.Compatible (J z (u z))) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s ∈ Icc a b, ξ (s, 1) = ξ (s, 0)) →
      (∀ t, ξ (a, t) = 0) → (∀ t, ξ (b, t) = 0) →
      ∫ z in Icc a b ×ˢ Icc 0 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2) ≤
        C * ∫ z in Icc a b ×ˢ Icc 0 1, (‖ω.floerLinearization
            (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2 +
          ‖ξ z‖ ^ 2) := by
  obtain ⟨C, hC, h⟩ := exists_forall_setIntegral_norm_fderiv_sq_le_of_periodic hab hc
    (continuousOn_comp_prodMk_of_continuousAt (fun z hz ↦ (hJ z hz).continuousAt)
      fun z hz ↦ (hu z hz).continuousAt.continuousWithinAt)
    (ω.continuousOn_floerLinearizationCoeff
      (J := fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) hJ hKs hKt hu)
  refine ⟨C, hC, fun ξ hξ hper ha hb ↦ (h hξ hper ha hb).trans_eq ?_⟩
  simp only [floerLinearization_eq_add, LinearMap.coe_toContinuousLinearMap']

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

/-- **The estimate of the linearized Floer operator on a disc.** Let `J(z, u z)` be `ω`-compatible
for every `z`, with `J` `C¹` and `Ks`, `Kt` `C²` at the points `(z, u z)`, and `u` `C¹`. Then for
`a < b` there is a constant `C ≥ 0` such that every `C²` section `ξ` of compact support satisfies
`∫_{‖w‖ ≤ a} (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{‖w‖ ≤ b} ‖ξ‖²)`, the discs read in
real coordinates. A cutoff between the two discs reduces this to the estimate on compactly
supported sections,
`exists_forall_setIntegral_norm_fderiv_sq_le_mul_setIntegral_floerLinearization_of_tsupport_subset`.
-/
theorem exists_forall_setIntegral_le_mul_integral_floerLinearization_add_of_lt
    (ω : SymplecticForm V)
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

end TauCeti.SymplecticForm
