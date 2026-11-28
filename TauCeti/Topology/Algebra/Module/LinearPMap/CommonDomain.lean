/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import Mathlib.Topology.Algebra.Module.LinearPMap
public import TauCeti.LinearAlgebra.LinearPMap.CommonDomain
public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Compact
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# The partial operator of an operator on a common domain

An unbounded operator on a space `H` is often given, as in the analysis of Floer trajectories, by
a bounded operator `A : D →L H` on a smaller space `D` together with a bounded injective inclusion
`ι : D →L H`: the asymptotic operator `J₀ (∂ₜ - S)` of a Floer cylinder is bounded from `H¹(S¹)`
to `L²(S¹)`. Such pairs `(ι, A)` are the input of the trajectory operators
`TauCeti.WeakDerivStep.domainTrajectoryOperator`. The partial linear operator on `H` with domain
`range ι`, acting by `ι x ↦ A x`, is `LinearMap.domainOperator` of the underlying linear maps,
`ι.toLinearMap.domainOperator A.toLinearMap hι`, whose construction and graph API only use
linear maps. This
file translates the conditions usually placed on the pair into the native theory of partial
operators, over topological modules. `A` may take values in a second space `K`, as for the weak
gradient `TauCeti.weakGradientPMap`. The normed closedness criteria and the characterization of
the resolvent set for Banach spaces are in
`TauCeti.Analysis.Normed.Operator.LinearPMap.CommonDomain`; symmetry and self-adjointness on an
inner product space are in `TauCeti.Analysis.InnerProductSpace.LinearPMap.CommonDomain`.

* **Graph.** The graph of the partial operator is the range of `x ↦ (ι x, A x)`
  (`LinearMap.graph_domainOperator`), so the operator is closed exactly when that range is
  (`ContinuousLinearMap.isClosed_domainOperator_iff_isClosed_range`).
* **Resolvent.** If `c • ι - A : D → H` is invertible, `c` is a resolvent point with resolvent
  `ι ∘ (c • ι - A)⁻¹` (`ContinuousLinearMap.resolvent_domainOperator`), and at a resolvent point
  the shift `c • ι - A` is bijective
  (`ContinuousLinearMap.bijective_smul_sub_of_mem_resolventSet`). If moreover `ι` is a compact
  operator, the partial operator has compact resolvent
  (`ContinuousLinearMap.hasCompactResolvent_domainOperator`). If `A` is invertible, `0` is a
  resolvent point (`ContinuousLinearMap.mem_resolventSet_domainOperator_of_isInvertible`).

## References

* T. Kato, *Perturbation Theory for Linear Operators*, Sections III.5.2 and III.6.8.
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1–33, Section 4 (paths of self-adjoint operators on a fixed domain `W ⊂ H`).
-/

public section

noncomputable section

open Function

namespace ContinuousLinearMap

section Closed

variable {R D H K : Type*} [CommRing R] [AddCommGroup D] [Module R D] [TopologicalSpace D]
  [AddCommGroup H] [Module R H] [TopologicalSpace H]
  [AddCommGroup K] [Module R K] [TopologicalSpace K]
  {ι : D →L[R] H} {A : D →L[R] K} {hι : Injective ι}

/-- `LinearMap.domainOperator ι A hι` is closed exactly when the range of `x ↦ (ι x, A x)` is
closed. -/
theorem isClosed_domainOperator_iff_isClosed_range :
    (ι.toLinearMap.domainOperator A.toLinearMap hι).IsClosed ↔
      IsClosed (Set.range (ι.prod A)) := by
  rw [LinearPMap.IsClosed, LinearMap.graph_domainOperator, ← coe_prod, LinearMap.coe_range,
    coe_coe]

end Closed

section Resolvent

variable {R D H : Type*} [CommRing R] [AddCommGroup D] [Module R D] [TopologicalSpace D]
  [AddCommGroup H] [Module R H] [TopologicalSpace H] [IsTopologicalAddGroup H]
  [ContinuousConstSMul R H] {ι A : D →L[R] H} {hι : Injective ι} {c : R}

/-- On the domain of `LinearMap.domainOperator ι A hι`, the shift
`c • I - LinearMap.domainOperator ι A hι` is the shift `c • ι - A` of the pair. -/
theorem smul_sub_domainOperator_apply
    {y : (ι.toLinearMap.domainOperator A.toLinearMap hι).domain} {x : D} (hx : ι x = y) :
    c • (y : H) - ι.toLinearMap.domainOperator A.toLinearMap hι y = (c • ι - A) x := by
  rw [LinearMap.domainOperator_apply _ _ hι hx, ← hx, coe_coe, _root_.sub_apply,
    _root_.smul_apply]

/-- If `c • ι - A` is invertible, then `ι ∘ (c • ι - A)⁻¹` inverts the shift
`c • I - LinearMap.domainOperator ι A hι`. -/
theorem isResolventAt_domainOperator (h : (c • ι - A).IsInvertible) :
    (ι.toLinearMap.domainOperator A.toLinearMap hι).IsResolventAt c
      (ι ∘L (c • ι - A).inverse) := by
  refine LinearPMap.isResolventAt_iff_forall_mem_graph.2 ⟨fun y ↦ ?_, fun p hp ↦ ?_⟩
  · have hx : c • ι ((c • ι - A).inverse y) - A ((c • ι - A).inverse y) = y := by
      simpa using h.self_apply_inverse y
    refine (LinearMap.mem_graph_domainOperator_iff _ _ hι).2
      ⟨(c • ι - A).inverse y, by simp, ?_⟩
    simp only [coe_coe, comp_apply]
    generalize (c • ι - A).inverse y = x at hx ⊢
    rw [← hx, sub_sub_cancel]
  · obtain ⟨x, hx, hAx⟩ := (LinearMap.mem_graph_domainOperator_iff _ _ hι).1 hp
    rw [coe_coe] at hx hAx
    have hshift : c • ι x - A x = (c • ι - A) x := by simp
    rw [← hx, ← hAx, hshift, comp_apply, h.inverse_apply_self]

/-- If `c • ι - A` is invertible, then `c` is a resolvent point of
`LinearMap.domainOperator ι A hι`. -/
theorem mem_resolventSet_domainOperator (h : (c • ι - A).IsInvertible) :
    c ∈ (ι.toLinearMap.domainOperator A.toLinearMap hι).resolventSet :=
  (isResolventAt_domainOperator h).mem_resolventSet

/-- If `A` is invertible, then `0` is a resolvent point of `LinearMap.domainOperator ι A hι`. -/
theorem mem_resolventSet_domainOperator_of_isInvertible (h : A.IsInvertible) :
    0 ∈ (ι.toLinearMap.domainOperator A.toLinearMap hι).resolventSet :=
  mem_resolventSet_domainOperator (by rwa [zero_smul, zero_sub, isInvertible_neg_iff])

/-- If `c • ι - A` is invertible, the resolvent of `LinearMap.domainOperator ι A hι` at `c` is
`ι ∘ (c • ι - A)⁻¹`. -/
theorem resolvent_domainOperator (h : (c • ι - A).IsInvertible) :
    (ι.toLinearMap.domainOperator A.toLinearMap hι).resolvent c = ι ∘L (c • ι - A).inverse :=
  LinearPMap.resolvent_eq_of_isResolventAt (isResolventAt_domainOperator h)

/-- The shift `c • I - LinearMap.domainOperator ι A hι` on its domain is bijective exactly when
the shift `c • ι - A : D → H` is. -/
theorem bijective_smul_sub_domainOperator_iff :
    Bijective (fun y : (ι.toLinearMap.domainOperator A.toLinearMap hι).domain ↦
        c • (y : H) - ι.toLinearMap.domainOperator A.toLinearMap hι y) ↔
      Bijective (c • ι - A) := by
  let e : D ≃ (ι.toLinearMap.domainOperator A.toLinearMap hι).domain :=
    (LinearEquiv.ofInjective (ι : D →ₗ[R] H) hι).toEquiv.trans
      (Equiv.subtypeEquivRight fun y ↦ by rw [LinearMap.domain_domainOperator])
  rw [← e.bijective_comp]
  refine iff_of_eq (congrArg Bijective (funext fun x ↦ ?_))
  exact smul_sub_domainOperator_apply (LinearEquiv.ofInjective_apply (h := hι) _ x).symm

/-- At a resolvent point `c` of `LinearMap.domainOperator ι A hι`, the shift
`c • ι - A : D → H` is bijective. -/
theorem bijective_smul_sub_of_mem_resolventSet
    (h : c ∈ (ι.toLinearMap.domainOperator A.toLinearMap hι).resolventSet) :
    Bijective (c • ι - A) := by
  obtain ⟨R, hR⟩ := LinearPMap.mem_resolventSet_iff.1 h
  exact bijective_smul_sub_domainOperator_iff.1 hR.smul_sub_bijective

/-- If `ι` is a compact operator and `c • ι - A` is invertible for some `c`, then
`LinearMap.domainOperator ι A hι` has compact resolvent. -/
theorem hasCompactResolvent_domainOperator (hcpt : IsCompactOperator ι)
    (h : (c • ι - A).IsInvertible) :
    (ι.toLinearMap.domainOperator A.toLinearMap hι).HasCompactResolvent :=
  .of_isCompactOperator_resolvent (mem_resolventSet_domainOperator h) <| by
    rw [resolvent_domainOperator h]
    exact hcpt.comp_clm _

end Resolvent

end ContinuousLinearMap
