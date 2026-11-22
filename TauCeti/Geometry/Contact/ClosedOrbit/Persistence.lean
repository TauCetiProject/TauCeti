/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.ClosedOrbit.Basic
public import Mathlib.Topology.GDelta.Basic
import TauCeti.Geometry.Contact.Family
import TauCeti.Geometry.Manifold.Flow.Persistence

/-!
# Openness of bounded-action Reeb nondegeneracy

For a family of contact forms on a compact boundaryless phase manifold with jointly `C¹` Reeb
fields, parametrized by a boundaryless manifold, the parameters for which every closed Reeb orbit
of action at most `A` is nondegenerate form an open set. The action is the period, and the
condition includes orbits and covers whose own positive periods are at most `A`, including
equality with `A`. The parameters with nondegenerate closed Reeb orbits at every action form a Gδ
set. Density requires a separate perturbation argument.

The parameter manifold may be modelled on an infinite-dimensional Banach space. A smooth
one-form on the product whose slices are contact provides such a family.

## Main results

* `isOpen_setOf_forall_isNondegenerateOrbit_period_le` and
  `isGδ_setOf_forall_isNondegenerateOrbit` for families with jointly `C¹` Reeb fields.
* `isOpen_setOf_forall_isNondegenerateOrbit_period_le_mpullback_prodMk` and
  `isGδ_setOf_forall_isNondegenerateOrbit_mpullback_prodMk` for slices of a smooth product form.

## References

* F. Bourgeois, Y. Eliashberg, H. Hofer, K. Wysocki, and E. Zehnder,
  *Compactness results in Symplectic Field Theory*, Geom. Topol. 7 (2003), Section 2.3.
-/

public section

noncomputable section

open Function Manifold Set Filter
open scoped ContDiff Manifold Topology

namespace TauCeti.SmoothForm

variable {E H M F G N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M] [CompactSpace M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]
  [T2Space N] [BoundarylessManifold J N]

section C1Family

variable [IsManifold J 1 N]

private theorem eventually_forall_isNondegenerateOrbit_period_le
    {α : N → SmoothForm I M ℝ 1} (hα : ∀ a, (α a).IsContactForm)
    (hv : ContMDiff (J.prod I) I.tangent 1
      (fun z : N × M ↦ (⟨z.2, (α z.1).reebVectorField z.2⟩ : TangentBundle I M)))
    (A : ℝ) {a₀ : N}
    (hnd : ∀ γ : Flow.ClosedOrbit ((hα a₀).reebFlow
      (hα a₀).isCompleteVectorField_reebVectorField), γ.period ≤ A →
      (hα a₀).IsNondegenerateOrbit (hα a₀).isCompleteVectorField_reebVectorField γ) :
    ∀ᶠ a in 𝓝 a₀, ∀ γ : Flow.ClosedOrbit ((hα a).reebFlow
      (hα a).isCompleteVectorField_reebVectorField), γ.period ≤ A →
      (hα a).IsNondegenerateOrbit (hα a).isCompleteVectorField_reebVectorField γ := by
  let hc (a : N) := (hα a).isCompleteVectorField_reebVectorField
  -- The uniform period bound supplies the lower endpoint for compact-window persistence.
  obtain ⟨ε, hε, hbound⟩ :=
    exists_pos_eventually_period_le_of_isCompact_param
      (v := fun a ↦ (α a).reebVectorField) hv (a₀ := a₀) isCompact_univ
      (fun x _ ↦ (hα a₀).reebVectorField_ne_zero x)
  have hsections : ∀ z ∈ Icc ε A ×ˢ (univ : Set M),
      flowOf (α a₀).reebVectorField z.1 z.2 = z.2 → ∃ g : M → ℝ,
      ContMDiffAt I 𝓘(ℝ) 1 g z.2 ∧ mvfderiv I g z.2 ((α a₀).reebVectorField z.2) ≠ 0 ∧
      ¬(returnDerivative (α a₀).reebVectorField g z.1 z.2).HasEigenvalue 1 := by
    rintro ⟨t, x⟩ ⟨⟨htε, htA⟩, _⟩ hp
    let δ := (hα a₀).reebTrajectory (hc a₀) x (hε.trans_le htε)
      (by rwa [(hα a₀).reebFlow_apply])
    have hδ := hnd (Flow.ClosedOrbit.mk δ)
      (by simpa only [Flow.ClosedOrbit.period_mk, δ, (hα a₀).period_reebTrajectory] using htA)
    have hsection :=
      ((hα a₀).isNondegenerateOrbit_mk_iff_exists_not_hasEigenvalue_returnDerivative
        (hc a₀) δ).mp hδ
    rwa [(hα a₀).point_reebTrajectory, (hα a₀).period_reebTrajectory] at hsection
  have hpersist := eventually_subset_flowDomain_and_forall_not_hasEigenvalue_returnDerivative
    (v := fun a ↦ (α a).reebVectorField) hv
    (isCompact_Icc.prod isCompact_univ) (fun z _ ↦ (hc a₀).mem_flowDomain z.1 z.2) hsections
  filter_upwards [hbound, hpersist] with a ha hpa γ hγ
  induction γ using Flow.ClosedOrbit.ind with | h δ => ?_
  rw [Flow.ClosedOrbit.period_mk] at hγ
  rw [(hα a).isNondegenerateOrbit_mk_iff_exists_not_hasEigenvalue_returnDerivative]
  have hp : flowOf (α a).reebVectorField δ.period δ.point = δ.point := by
    rw [← (hα a).reebFlow_apply]; exact δ.apply_period
  exact hpa.2 (δ.period, δ.point)
    ⟨⟨(ha.self_of_nhdsSet δ.point (mem_univ _)) δ.period δ.period_pos
        ((hc a).mem_flowDomain _ _) hp, hγ⟩,
      mem_univ _⟩ hp

/-- For a family of contact forms on a compact boundaryless phase manifold, parametrized by a
boundaryless manifold and with jointly `C¹` Reeb fields, the parameters where all closed Reeb
orbits of action at most `A` are nondegenerate form an open set. The action equals the period.
This includes orbits and covers whose own periods are at most `A`, including equality. -/
theorem isOpen_setOf_forall_isNondegenerateOrbit_period_le
    {α : N → SmoothForm I M ℝ 1} (hα : ∀ a, (α a).IsContactForm)
    (hv : ContMDiff (J.prod I) I.tangent 1
      (fun z : N × M ↦ (⟨z.2, (α z.1).reebVectorField z.2⟩ : TangentBundle I M)))
    (A : ℝ) :
    IsOpen {a | ∀ γ : Flow.ClosedOrbit ((hα a).reebFlow
      (hα a).isCompleteVectorField_reebVectorField), γ.period ≤ A →
      (hα a).IsNondegenerateOrbit (hα a).isCompleteVectorField_reebVectorField γ} :=
  isOpen_iff_mem_nhds.2 fun _ ha ↦ eventually_forall_isNondegenerateOrbit_period_le hα hv A ha

/-- For a family of contact forms on a compact boundaryless phase manifold, parametrized by a
boundaryless manifold and with jointly `C¹` Reeb fields, the parameters where every closed Reeb
orbit is nondegenerate form a Gδ set. This includes all covers. -/
theorem isGδ_setOf_forall_isNondegenerateOrbit
    {α : N → SmoothForm I M ℝ 1} (hα : ∀ a, (α a).IsContactForm)
    (hv : ContMDiff (J.prod I) I.tangent 1
      (fun z : N × M ↦ (⟨z.2, (α z.1).reebVectorField z.2⟩ : TangentBundle I M))) :
    IsGδ {a | ∀ γ : Flow.ClosedOrbit ((hα a).reebFlow
      (hα a).isCompleteVectorField_reebVectorField),
      (hα a).IsNondegenerateOrbit (hα a).isCompleteVectorField_reebVectorField γ} := by
  have heq : {a | ∀ γ : Flow.ClosedOrbit ((hα a).reebFlow
      (hα a).isCompleteVectorField_reebVectorField),
      (hα a).IsNondegenerateOrbit (hα a).isCompleteVectorField_reebVectorField γ} =
      ⋂ n : ℕ, {a | ∀ γ : Flow.ClosedOrbit ((hα a).reebFlow
        (hα a).isCompleteVectorField_reebVectorField), γ.period ≤ (n : ℝ) →
        (hα a).IsNondegenerateOrbit (hα a).isCompleteVectorField_reebVectorField γ} := by
    ext a
    simp only [mem_ofPred_eq, mem_iInter]
    constructor
    · exact fun ha _ γ _ ↦ ha γ
    · intro ha γ
      obtain ⟨n, hn⟩ := exists_nat_ge γ.period
      exact ha n γ hn
  rw [heq]
  exact IsGδ.iInter_of_isOpen fun n : ℕ ↦
    isOpen_setOf_forall_isNondegenerateOrbit_period_le hα hv n

end C1Family

variable [IsManifold J ∞ N]

/-- For the contact slices of a smooth product form on a compact boundaryless phase manifold
and a boundaryless parameter manifold, nondegeneracy of every closed Reeb orbit of action at most
`A` is open in the parameter. This includes orbits and covers whose own periods are at most `A`,
including equality. -/
theorem isOpen_setOf_forall_isNondegenerateOrbit_period_le_mpullback_prodMk
    (α : SmoothForm (J.prod I) (N × M) ℝ 1)
    (hα : ∀ a, (mpullback (Prod.mk a) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm)
    (A : ℝ) :
    IsOpen {a | ∀ γ : Flow.ClosedOrbit ((hα a).reebFlow
      (hα a).isCompleteVectorField_reebVectorField), γ.period ≤ A →
      (hα a).IsNondegenerateOrbit (hα a).isCompleteVectorField_reebVectorField γ} := by
  have hv := (contMDiff_reebVectorField_mpullback_prodMk α hα).of_le (m := 1) (by simp)
  exact isOpen_setOf_forall_isNondegenerateOrbit_period_le hα hv A

/-- For the contact slices of a smooth product form on a compact boundaryless phase manifold
and a boundaryless parameter manifold, the parameters where every closed Reeb orbit is
nondegenerate form a Gδ set. This includes all covers. -/
theorem isGδ_setOf_forall_isNondegenerateOrbit_mpullback_prodMk
    (α : SmoothForm (J.prod I) (N × M) ℝ 1)
    (hα : ∀ a, (mpullback (Prod.mk a) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm) :
    IsGδ {a | ∀ γ : Flow.ClosedOrbit ((hα a).reebFlow
      (hα a).isCompleteVectorField_reebVectorField),
      (hα a).IsNondegenerateOrbit (hα a).isCompleteVectorField_reebVectorField γ} := by
  have hv := (contMDiff_reebVectorField_mpullback_prodMk α hα).of_le (m := 1) (by simp)
  exact isGδ_setOf_forall_isNondegenerateOrbit hα hv

end TauCeti.SmoothForm
