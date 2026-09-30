/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Trace.Basic

/-!
# Corestriction through the coinduced trace in degree two

For an open subgroup `U` of a profinite group `G`, the trace `Coind_U^G M → M` induces the same
map on second cohomology as the inverse of Shapiro's isomorphism followed by corestriction. Thus
degree-two corestriction `TauCeti.ContCohomology.explicitCor2` can be computed by inverse Shapiro
followed by the coefficient map of the trace, exactly as in degrees zero and one.

Unlike degree one, no coboundary appears once the transversal is adapted to the inverse Shapiro
cochain. The inverse Shapiro cochain `TauCeti.ContCohomology.coindCochain2` of a `2`-cochain `c`
of `U` is built from a right-coset factorization `w : G → U`, and its value at `(γ, η)` is the
function `y ↦ homogeneous2 c (w y) (w (y γ)) (w (y γ η))`. For the adapted transversal
`t = TauCeti.factorizationTransversal w`, with `w (t x)⁻¹ = 1` for every coset `x`, the
factorization sends `(t x)⁻¹ γ` to the transversal word `ℓᵗ_x(γ)`, so the trace of that value is
the degree-two corestriction cochain `∑ x, t x • c (ℓᵗ_x γ, ℓᵗ_{γ⁻¹ • x} η)` on the nose. The
general statement then follows from the independence of `explicitCor2` of the transversal.

## Main declarations

* `TauCeti.ContCohomology.trace_coindCochain2`: the trace of the inverse Shapiro cochain is the
  corestriction cochain for the transversal adapted to the factorization.
* `TauCeti.ContCohomology.explicitCor2_eq_explicitCoeff2_trace`: degree-two corestriction is
  inverse Shapiro followed by the coefficient map of the trace.

## References

* K. S. Brown, *Cohomology of Groups*, Chapter III, §9, for the coinduced construction of the
  transfer.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.5.7), for the
  transversal normalization of corestriction.
-/

public section

namespace TauCeti.ContCohomology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {U : Subgroup G} [U.FiniteIndex]
  {M : Type*} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

section Cochains

variable (w : G → U) (hw : Continuous w) (hwmul : ∀ (u : U) (g : G), w ((u : G) * g) = u * w g)
  {c : U × U → M} (hc : Continuous c)

/-- **The trace of the inverse Shapiro cochain is the corestriction cochain.** For the transversal
adapted to the factorization `w`, the trace `Coind_U^G M → M` of the inverse Shapiro `2`-cochain
of `c` is, at every pair `(γ, η)`, the degree-two corestriction cochain of `c`. No cocycle
condition on `c` is needed. -/
theorem trace_coindCochain2 (γ η : G) :
    DiscreteCoind.trace G U M (coindCochain2 w c hw hwmul hc (γ, η)) =
      cochainsCor2 G M U (factorizationTransversal w) (factorizationTransversal_mk w) c (γ, η) := by
  rw [DiscreteCoind.trace_eq_sum_transversal _ (factorizationTransversal_mk w),
    cochainsCor2_apply]
  refine Finset.sum_congr rfl fun x _ => congrArg (factorizationTransversal w x • ·) ?_
  have hγη : (factorizationTransversal w x)⁻¹ * γ * η =
      (factorizationTransversal w x)⁻¹ * (γ * η) := mul_assoc _ _ _
  have hword : (⟨lWord U (factorizationTransversal w) x (γ * η),
      lWord_mem U _ (factorizationTransversal_mk w) x (γ * η)⟩ : U) =
      ⟨lWord U (factorizationTransversal w) x γ,
        lWord_mem U _ (factorizationTransversal_mk w) x γ⟩ *
      ⟨lWord U (factorizationTransversal w) (γ⁻¹ • x) η,
        lWord_mem U _ (factorizationTransversal_mk w) (γ⁻¹ • x) η⟩ :=
    Subtype.ext (lWord_mul_lWord U _ x γ η).symm
  rw [coindCochain2_apply, apply_inv_factorizationTransversal w hwmul, hγη,
    apply_inv_factorizationTransversal_mul w hwmul,
    apply_inv_factorizationTransversal_mul w hwmul, hword, homogeneous2_one_left,
    inv_mul_cancel_left]

end Cochains

section Cohomology

variable [CompactSpace G] [TotallyDisconnectedSpace G] (hU : IsOpen (U : Set G))

/-- **Degree-two corestriction is inverse Shapiro followed by the coefficient map of the trace.**
The subgroup is open, and the Shapiro isomorphism uses its resulting closedness. -/
theorem explicitCor2_eq_explicitCoeff2_trace :
    explicitCor2 G M U hU =
      (explicitCoeff2 G (DiscreteCoind G U M) (DiscreteCoind.trace G U M)
        DiscreteCoind.continuous_trace).comp
          (explicitShapiro2 G U M (U.isClosed_of_isOpen hU)).symm.toAddMonoidHom := by
  obtain ⟨w, -, hw, -, -, hwmul, -, -⟩ :=
    exists_continuous_rightCosetFactorization U (U.isClosed_of_isOpen hU)
  refine AddMonoidHom.ext fun x => ?_
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
    rw [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
      explicitShapiro2_symm_apply G U M _ hw hwmul, explicitCoeff2_mk,
      explicitCor2_eq_transversal G M U (factorizationTransversal w)
        (factorizationTransversal_mk w) hU, explicitCor2Transversal_mk]
    congr 1
    refine Subtype.ext (funext fun ⟨γ, η⟩ => ?_)
    rw [coe_cocyclesCor2, ← trace_coindCochain2 w hw hwmul (mem_Z2_iff.1 c.2).1 γ η]
    -- `rw [cocyclesMap2_apply]` fails here: `explicitCoeff2` states its equivariance proof through
    -- the `MulActionHom` coercion of the trace, so the motive is not type-correct at reducible
    -- transparency. Unifying against the lemma instead leaves only the coercions to unfold.
    refine Eq.trans ?_ (cocyclesMap2_apply G (DiscreteCoind G U M) G M _ _ _ _ _ γ η).symm
    simp only [coe_coindCocycle2, ContinuousMonoidHom.id_toFun, AddMonoidHom.coe_ofClass]

end Cohomology

end TauCeti.ContCohomology
