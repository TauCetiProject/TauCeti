/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.ClosedOrbit
public import Mathlib.Topology.GDelta.Basic
import TauCeti.Geometry.Contact.Family
import TauCeti.Dynamics.Flow.PeriodBound
import TauCeti.Geometry.Manifold.Flow.Persistence

/-!
# Openness of bounded-action Reeb nondegeneracy

For a smooth family of contact forms on a compact boundaryless manifold, the parameters for
which every closed Reeb orbit of action at most `A` is nondegenerate form an open set.
The action is the period, and the condition includes every positive period and all covers.
The parameters with nondegenerate closed Reeb orbits at every action form a Gδ set.
Density requires a separate perturbation argument.

The proof combines the compact-window theorem
`TauCeti.eventually_subset_flowDomain_and_forall_not_hasEigenvalue_returnDerivative` with
`Flow.exists_pos_eventually_period_le_of_isCompact`, giving a uniform positive period bound near
the compact slice `{a₀} × M`. The parameter manifold may be modelled on an
infinite-dimensional Banach space: no compact neighborhood of the parameter is required.

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
  [T2Space N] [IsManifold J ∞ N] [BoundarylessManifold J N]

private theorem exists_pos_eventually_period_le {α : N → SmoothForm I M ℝ 1}
    (hα : ∀ a, (α a).IsContactForm)
    (hv : ContMDiff (J.prod I) I.tangent 1
      (fun z : N × M ↦ (⟨z.2, (α z.1).reebVectorField z.2⟩ : TangentBundle I M)))
    (a₀ : N) :
    ∃ ε > 0, ∀ᶠ a in 𝓝 a₀, ∀ x T, 0 < T →
      flowOf (α a).reebVectorField T x = x → ε ≤ T := by
  let V := verticalField J (fun a ↦ (α a).reebVectorField)
  have hV := contMDiff_verticalField (v := fun a ↦ (α a).reebVectorField) hv
  have hc : IsCompleteVectorField V := by
    apply isCompleteVectorField_iff_maximalIntegralCurveInterval.2
    rintro ⟨a, x⟩
    rw [maximalIntegralCurveInterval_verticalField]
    exact (hα a).isCompleteVectorField_reebVectorField.maximalIntegralCurveInterval_eq_univ x
  let ϕ := globalFlow V hV hc
  have hflow (t : ℝ) (a : N) (x : M) :
      ϕ t (a, x) = (a, flowOf (α a).reebVectorField t x) := by
    rw [← flowOf_eq_globalFlow hV hc]
    exact flowOf_verticalField (hv.apply_param a) t x
  obtain ⟨ε, hε, hbound⟩ :=
    ϕ.exists_pos_eventually_period_le_of_isCompact (K := {a₀} ×ˢ univ)
      (isCompact_singleton.prod isCompact_univ) (fun z _ ↦ by
        obtain ⟨t, ht⟩ := (hα z.1).exists_reebFlow_ne
          (hα z.1).isCompleteVectorField_reebVectorField z.2
        refine ⟨t, fun heq ↦ ht ?_⟩
        simpa only [(hα z.1).reebFlow_apply] using
          congrArg Prod.snd ((hflow t z.1 z.2).symm.trans heq))
  refine ⟨ε, hε, ?_⟩
  have hnear : ∀ x ∈ (univ : Set M), ∀ᶠ z : N × M in 𝓝 (a₀, x),
      ∀ T > 0, ϕ T z = z → ε ≤ T := fun x hx ↦
    mem_nhdsSet_iff_forall.1 hbound (a₀, x) ⟨rfl, hx⟩
  filter_upwards [isCompact_univ.eventually_forall_of_forall_eventually
    (P := fun a x ↦ ∀ T > 0, ϕ T (a, x) = (a, x) → ε ≤ T) hnear] with a ha x T hT hp
  exact ha x (mem_univ x) T hT (by rw [hflow, hp])

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
  obtain ⟨ε, hε, hbound⟩ := exists_pos_eventually_period_le hα hv a₀
  have hsections : ∀ z ∈ Icc ε A ×ˢ (univ : Set M),
      flowOf (α a₀).reebVectorField z.1 z.2 = z.2 → ∃ g : M → ℝ,
      ContMDiffAt I 𝓘(ℝ) 1 g z.2 ∧ mvfderiv I g z.2 ((α a₀).reebVectorField z.2) ≠ 0 ∧
      ¬(returnDerivative (α a₀).reebVectorField g z.1 z.2).HasEigenvalue 1 := by
    rintro ⟨t, x⟩ ⟨⟨htε, htA⟩, _⟩ hp
    let δ : Flow.PeriodicTrajectory ((hα a₀).reebFlow (hc a₀)) :=
      ⟨x, t, hε.trans_le htε, by rw [(hα a₀).reebFlow_apply, hp],
        (hα a₀).exists_reebFlow_ne (hc a₀) x⟩
    exact ((hα a₀).isNondegenerateOrbit_mk_iff_exists_returnDerivative (hc a₀) δ).1
      (hnd (Flow.ClosedOrbit.mk δ) (by simpa only [Flow.ClosedOrbit.period_mk] using htA))
  have hpersist := eventually_subset_flowDomain_and_forall_not_hasEigenvalue_returnDerivative
    (v := fun a ↦ (α a).reebVectorField) hv
    (isCompact_Icc.prod isCompact_univ) (fun z _ ↦ (hc a₀).mem_flowDomain z.1 z.2) hsections
  filter_upwards [hbound, hpersist] with a ha hpa γ hγ
  induction γ using Flow.ClosedOrbit.ind with | h δ => ?_
  rw [Flow.ClosedOrbit.period_mk] at hγ
  apply ((hα a).isNondegenerateOrbit_mk_iff_exists_returnDerivative (hc a) δ).2
  have hp : flowOf (α a).reebVectorField δ.period δ.point = δ.point := by
    rw [← (hα a).reebFlow_apply]; exact δ.apply_period
  exact hpa.2 (δ.period, δ.point)
    ⟨⟨ha δ.point δ.period δ.period_pos hp, hγ⟩, mem_univ _⟩ hp

/-- In a smooth family of contact forms on a compact boundaryless manifold, nondegeneracy of
every closed Reeb orbit of action at most `A` is open in the parameter. The action equals the
period; all positive periods and all covers are included. The parameter model may be an
infinite-dimensional Banach space. -/
theorem isOpen_setOf_forall_isNondegenerateOrbit_period_le_mpullback_prodMk
    (α : SmoothForm (J.prod I) (N × M) ℝ 1)
    (hα : ∀ a, (mpullback (Prod.mk a) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm)
    (A : ℝ) :
    IsOpen {a | ∀ γ : Flow.ClosedOrbit ((hα a).reebFlow
      (hα a).isCompleteVectorField_reebVectorField), γ.period ≤ A →
      (hα a).IsNondegenerateOrbit (hα a).isCompleteVectorField_reebVectorField γ} := by
  have hv := (contMDiff_reebVectorField_mpullback_prodMk α hα).of_le (m := 1) (by simp)
  exact isOpen_iff_mem_nhds.2 fun _ ha ↦
    eventually_forall_isNondegenerateOrbit_period_le hα hv A ha

/-- The parameters for which every closed Reeb orbit is nondegenerate form a Gδ set in a
smooth family of contact forms on a compact boundaryless manifold. This includes all covers. -/
theorem isGδ_setOf_forall_isNondegenerateOrbit_mpullback_prodMk
    (α : SmoothForm (J.prod I) (N × M) ℝ 1)
    (hα : ∀ a, (mpullback (Prod.mk a) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm) :
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
    isOpen_setOf_forall_isNondegenerateOrbit_period_le_mpullback_prodMk α hα n

end TauCeti.SmoothForm
