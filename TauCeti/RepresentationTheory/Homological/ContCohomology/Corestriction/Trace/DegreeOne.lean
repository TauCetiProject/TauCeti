/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Trace.Basic

/-!
# Corestriction through the coinduced trace in degree one

For an open finite-index subgroup `U`, the trace on coinduced coefficients induces the same
map on first cohomology as Shapiro followed by corestriction. Thus degree-one corestriction
can be computed by inverse Shapiro followed by the coefficient map of the trace.

The cochains themselves differ: for a cocycle `c : G → DiscreteCoind G U M` and a transversal
`t`, their difference is the coboundary of `∑ u, t u • c (t u) (t u)⁻¹`.
`cochainsCor1_shapiro_sub_trace` records this identity before passing to classes.

The coinduced construction of corestriction follows Brown, *Cohomology of Groups*, III §9;
the transversal normalization is Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*,
2nd ed., (1.5.7).
-/

public section

namespace TauCeti.ContCohomology

variable {G : Type*} [Group G] [TopologicalSpace G]
  {M : Type*} [AddCommGroup M] [DistribMulAction G M]
  {U : Subgroup G} [U.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

section Cochains

variable [ContinuousMul G]

omit [U.FiniteIndex] in
private theorem trace_shapiro_summand (t : G ⧸ U → G)
    (ht : ∀ u : G ⧸ U, (QuotientGroup.mk (t u) : G ⧸ U) = u)
    {c : G → DiscreteCoind G U M} (hc : groupCohomology.IsCocycle₁ c)
    (γ : G) (u : G ⧸ U) :
    t u • c (lWord U t u γ) 1 - t u • c γ (t u)⁻¹ =
      γ • (t (γ⁻¹ • u) • c (t (γ⁻¹ • u)) (t (γ⁻¹ • u))⁻¹) -
        t u • c (t u) (t u)⁻¹ := by
  have h := congrArg (fun f : DiscreteCoind G U M => f (t u)⁻¹)
    (smul_apply_lWord_of_isCocycle₁ G (DiscreteCoind G U M) U t hc γ (γ⁻¹ • u))
  simp only [smul_inv_smul, DiscreteCoind.coe_smul, inv_mul_cancel,
    DiscreteCoind.coe_add, DiscreteCoind.coe_sub, Pi.add_apply, Pi.sub_apply] at h
  have harg : (t u)⁻¹ * γ = lWord U t u γ * (t (γ⁻¹ • u))⁻¹ := by
    rw [lWord_def]
    group
  rw [harg, DiscreteCoind.apply_mul _ ⟨_, lWord_mem U t ht u γ⟩] at h
  have h' := congrArg (fun m : M => t u • m) h
  simp only [smul_add, smul_sub, Subgroup.smul_def, smul_smul,
    transversal_mul_lWord] at h'
  simpa only [smul_smul] using (sub_eq_iff_eq_add.mpr h')

/-- The corestriction of evaluation at `1` differs from the coinduced trace by an explicit
`0`-coboundary. This identity is valid before imposing continuity on the cocycle. -/
theorem cochainsCor1_shapiro_sub_trace (t : G ⧸ U → G)
    (ht : ∀ u : G ⧸ U, (QuotientGroup.mk (t u) : G ⧸ U) = u)
    {c : G → DiscreteCoind G U M} (hc : groupCohomology.IsCocycle₁ c) :
    cochainsCor1 G M U t ht (fun u : U => c u 1) -
        (fun γ => DiscreteCoind.trace G U M (c γ)) =
      d0 G M (∑ u : G ⧸ U, t u • c (t u) (t u)⁻¹) := by
  funext γ
  rw [Pi.sub_apply, cochainsCor1_apply, DiscreteCoind.trace_eq_sum_transversal t ht,
    ← Finset.sum_sub_distrib]
  simp only [trace_shapiro_summand t ht hc, Finset.sum_sub_distrib, ← Finset.smul_sum,
    d0_apply]
  congr 2
  exact Fintype.sum_equiv (MulAction.toPerm γ⁻¹ : Equiv.Perm (G ⧸ U)) _ _ (fun _ => rfl)

end Cochains

section Cohomology

variable [IsTopologicalGroup G] [CompactSpace G]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  (hU : IsOpen (U : Set G))

/-- In degree one, corestriction after the forward Shapiro map is the coefficient map of
the coinduced trace. -/
theorem explicitCor1_comp_explicitShapiroMap1_eq_explicitCoeff1_trace :
    (explicitCor1 G M U hU).comp (explicitShapiroMap1 G U M) =
      explicitCoeff1 G (DiscreteCoind G U M) (DiscreteCoind.trace G U M)
        DiscreteCoind.continuous_trace := by
  apply AddMonoidHom.ext
  intro x
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
    simp only [AddMonoidHom.comp_apply, explicitShapiroMap1, explicitMap1_mk,
      explicitCor1_mk, explicitCoeff1_mk]
    apply H1pi_eq_iff.mpr
    have hcor := cochainsCor1_shapiro_sub_trace Quotient.out Quotient.out_eq
      (mem_Z1_iff.mp c.property).2
    have hcoe : (cocyclesCor1 G M U Quotient.out Quotient.out_eq hU
        (shapiroCocycles1 G U M c) : G → M) -
        (cocyclesMap1 G (DiscreteCoind G U M) G M (ContinuousMonoidHom.id G)
          (DiscreteCoind.trace G U M) DiscreteCoind.continuous_trace
          (fun g m => (DiscreteCoind.trace G U M).map_smul g m) c : G → M) =
        d0 G M (∑ u : G ⧸ U, u.out • (c : G → DiscreteCoind G U M) u.out u.out⁻¹) := by
      rw [← hcor]
      funext γ
      simp only [Pi.sub_apply, coe_cocyclesCor1, cochainsCor1_apply]
      congr 1
      · apply Finset.sum_congr rfl
        intro u _
        exact congrArg (fun m : M => u.out • m)
          (shapiroCocycles1_apply G U M c ⟨_, lWord_mem U _ Quotient.out_eq u γ⟩)
      · exact cocyclesMap1_apply G (DiscreteCoind G U M) G M
          (ContinuousMonoidHom.id G) (DiscreteCoind.trace G U M)
          DiscreteCoind.continuous_trace
          (fun g m => (DiscreteCoind.trace G U M).map_smul g m) c γ
    rw [hcoe]
    exact d0_mem_B1 _

variable [TotallyDisconnectedSpace G]

/-- Degree-one corestriction is inverse Shapiro followed by the coefficient map of the trace.
The subgroup is open, and the Shapiro isomorphism uses its resulting closedness. -/
theorem explicitCor1_eq_explicitCoeff1_trace :
    explicitCor1 G M U hU =
      (explicitCoeff1 G (DiscreteCoind G U M) (DiscreteCoind.trace G U M)
        DiscreteCoind.continuous_trace).comp
          (explicitShapiro1 G U M (U.isClosed_of_isOpen hU)).symm.toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro x
  have h := DFunLike.congr_fun
    (explicitCor1_comp_explicitShapiroMap1_eq_explicitCoeff1_trace hU)
    ((explicitShapiro1 G U M (U.isClosed_of_isOpen hU)).symm x)
  simpa only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    ← explicitShapiro1_apply _ _ _ (U.isClosed_of_isOpen hU),
    AddEquiv.apply_symm_apply] using h

end Cohomology

end TauCeti.ContCohomology
