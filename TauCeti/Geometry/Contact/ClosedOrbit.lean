/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Flow.ClosedOrbit
public import TauCeti.Geometry.Contact.Flow
public import TauCeti.Geometry.Manifold.DifferentialForm.AddCircle
public import TauCeti.Geometry.Manifold.VectorField.AddCircle
import TauCeti.Dynamics.Flow.PeriodBound
import TauCeti.Geometry.Manifold.Flow.NondegenerateOrbit
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Closed Reeb orbits, nondegeneracy and finiteness below an action bound

Let `α` be a contact form on a boundaryless smooth manifold `M`, with contact distribution
`ξ = ker α` (`TauCeti.SmoothForm.kerDistribution`, equipped with its pointwise symplectic form
`IsContactForm.kerSymplecticForm` in `TauCeti.Geometry.Contact.Distribution`), Reeb vector field
`R_α` (`TauCeti.SmoothForm.reebVectorField`), and complete Reeb flow `IsContactForm.reebFlow`
(from `TauCeti.Geometry.Contact.Flow`). This file develops the periodic trajectories and
unparametrized closed orbits of `reebFlow`, culminating in finiteness below any action bound `A`:
whenever every closed Reeb orbit of period (equivalently, contact action) at most `A` (meeting a
compact subset `K`, or globally on a compact boundaryless manifold) is nondegenerate, there are
only finitely many such closed Reeb orbits (including multiply covered ones).

## Periodic Reeb trajectories and nondegeneracy

Because `IsContactForm.reebFlow` is a `Flow ℝ M` without rest points, periodic Reeb trajectories,
unparametrized closed orbits, primitive orbits, covering multiplicities `κ_γ`, circle
parametrizations, cyclic reparametrization groups `ℤ/κ_γ` and the `κ_γ` asymptotic markers over a
basepoint are inherited directly from `TauCeti.Dynamics.Flow.ClosedOrbit`.

* **Contact action equals period** (`IsContactForm.pathIntegral_periodicTrajectory`): the contact
  action `∫_0^T γ^* α` of a periodic Reeb trajectory `γ` of period `T` equals `T`.
* **Linearized Reeb return map of a periodic trajectory**
  (`IsContactForm.periodicLinearizedReturn`): specializing `IsContactForm.linearizedReebReturn`
  (from `TauCeti.Geometry.Contact.Flow`) to a periodic trajectory `γ`, the characteristic
  polynomial and eigenvalues are invariant across representatives of the same `ClosedOrbit`
  (`IsContactForm.charpoly_periodicLinearizedReturn_eq_of_mk_eq`,
  `IsContactForm.hasEigenvalue_periodicLinearizedReturn_iff_of_mk_eq`) and satisfy the iterate
  power law (`IsContactForm.charpoly_periodicLinearizedReturn_iterate`,
  `IsContactForm.hasEigenvalue_periodicLinearizedReturn_iterate_iff`).
* **Nondegeneracy** (`IsContactForm.IsNondegenerateOrbit`): an unparametrized closed Reeb orbit is
  nondegenerate when `1` is not an eigenvalue of its linearized Reeb return map on `ξ`
  (`IsContactForm.isNondegenerateOrbit_mk_iff`); its `k`-fold iterate is nondegenerate iff `1` is
  not an eigenvalue of the `k`-th power (`IsContactForm.isNondegenerateOrbit_iterate_mk_iff`).
  In particular, if `-1` is an eigenvalue of the return map of `γ`, then its double cover
  `γ.iterate 2` is degenerate
  (`IsContactForm.not_isNondegenerateOrbit_iterate_two_of_hasEigenvalue_neg_one`).

## Finiteness below an action bound and the circle model

* **Finiteness below an action bound**
  (`IsContactForm.finite_closedOrbit_inter_nonempty_and_period_le`,
  `IsContactForm.finite_closedOrbit_period_le`): for a complete Reeb flow and a compact subset `K`,
  if every closed Reeb orbit meeting `K` of period (equivalently, contact action) at most `A` is
  nondegenerate, there are only finitely many of them (including covers); in particular, on a
  compact boundaryless contact manifold, if every closed Reeb orbit of period at most `A` is
  nondegenerate, then there are only finitely many closed Reeb orbits (including covers) of period
  at most `A`.
* **Circle witness** (`AddCircle.isContactForm_timeForm`,
  `AddCircle.isNondegenerateOrbit_timeForm`, `AddCircle.multiplicity_mk_primitiveTrajectory`): on
  the `1`-dimensional circle `AddCircle p` (`p > 0`), `AddCircle.timeForm p` is a contact form with
  trivial contact hyperplane `⊥`, Reeb field `AddCircle.timeVectorField p`, Reeb flow
  `AddCircle.translationFlow p`, and every closed Reeb orbit (primitive of period `p` and all
  `k`-fold covers of period `k * p`) is nondegenerate.

## References

* F. Bourgeois, Y. Eliashberg, H. Hofer, K. Wysocki, and E. Zehnder,
  *Compactness results in Symplectic Field Theory*, Geom. Topol. 7 (2003), 799–888, Section 2.3.
* Y. Eliashberg, A. Givental, and H. Hofer, *Introduction to Symplectic Field Theory*,
  GAFA 2000, Visions in Mathematics, Part II, 560–673, Section 1.2.
* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Sections 1.1 and 2.3.
-/

public section

noncomputable section

open Function Manifold Module Set Filter
open scoped ContDiff Manifold Topology

namespace TauCeti.SmoothForm

/-! ### Closed Reeb orbits, nondegeneracy and finiteness -/

section ClosedOrbit

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {α : SmoothForm I M ℝ 1}

/-- **Contact action of a periodic Reeb trajectory equals its period.** -/
theorem IsContactForm.pathIntegral_periodicTrajectory (hα : α.IsContactForm)
    (hc : IsCompleteVectorField α.reebVectorField)
    (γ : Flow.PeriodicTrajectory (hα.reebFlow hc)) :
    pathIntegral α.val (fun t ↦ hα.reebFlow hc t γ.point) 0 γ.period = γ.period :=
  hα.pathIntegral_zero_of_isMIntegralCurve (hα.isMIntegralCurve_reebFlow hc γ.point) γ.period

/-- The linearized Reeb return map of a parametrized periodic Reeb trajectory `γ`, acting on the
contact hyperplane `ξ_(γ.point)`. -/
def IsContactForm.periodicLinearizedReturn (hα : α.IsContactForm)
    (hc : IsCompleteVectorField α.reebVectorField)
    (γ : Flow.PeriodicTrajectory (hα.reebFlow hc)) :
    Module.End ℝ (α.kerDistribution γ.point) :=
  hα.linearizedReebReturn (hc.mem_flowDomain γ.period γ.point)
    ((hα.reebFlow_apply hc γ.period γ.point).symm.trans γ.apply_period)

/-- `periodicLinearizedReturn` is `linearizedReebReturn` at the trajectory's period and
basepoint. -/
theorem IsContactForm.periodicLinearizedReturn_def (hα : α.IsContactForm)
    (hc : IsCompleteVectorField α.reebVectorField)
    (γ : Flow.PeriodicTrajectory (hα.reebFlow hc)) :
    hα.periodicLinearizedReturn hc γ =
      hα.linearizedReebReturn (hc.mem_flowDomain γ.period γ.point)
        ((hα.reebFlow_apply hc γ.period γ.point).symm.trans γ.apply_period) := by
  unfold IsContactForm.periodicLinearizedReturn
  rfl

/-- Evaluating `periodicLinearizedReturn` agrees with `mfderiv` of the period-time Reeb flow. -/
@[simp]
theorem IsContactForm.coe_periodicLinearizedReturn_apply (hα : α.IsContactForm)
    (hc : IsCompleteVectorField α.reebVectorField)
    (γ : Flow.PeriodicTrajectory (hα.reebFlow hc))
    (v : α.kerDistribution γ.point) :
    (hα.periodicLinearizedReturn hc γ v : TangentSpace I γ.point) =
      mfderiv I I (flowOf α.reebVectorField γ.period) γ.point v := by
  rw [hα.periodicLinearizedReturn_def, hα.coe_linearizedReebReturn_apply]

/-- The linearized Reeb return map of the `k`-fold iterate `γ.iterate k` has the same
characteristic polynomial as the `k`-th power of that of `γ`. -/
theorem IsContactForm.charpoly_periodicLinearizedReturn_iterate (hα : α.IsContactForm)
    (hc : IsCompleteVectorField α.reebVectorField)
    (γ : Flow.PeriodicTrajectory (hα.reebFlow hc)) (k : ℕ+) :
    (hα.periodicLinearizedReturn hc (γ.iterate k)).charpoly =
      (hα.periodicLinearizedReturn hc γ ^ (k : ℕ)).charpoly := by
  have hpt : flowOf α.reebVectorField 0 (γ.iterate k).point = γ.point :=
    (flowOf_zero _ _).trans (γ.point_iterate k)
  have hper : (γ.iterate k).period = (k : ℕ) * γ.period := γ.period_iterate k
  have hpγ : flowOf α.reebVectorField γ.period γ.point = γ.point := by
    rw [← hα.reebFlow_apply hc]
    exact γ.apply_period
  have hp₂ : flowOf α.reebVectorField (γ.iterate k).period γ.point = γ.point := by
    rw [← γ.point_iterate k, ← hα.reebFlow_apply hc]
    exact (γ.iterate k).apply_period
  have hk₂ : flowOf α.reebVectorField ((k : ℕ) * γ.period) γ.point = γ.point :=
    hper ▸ hp₂
  simp_rw [hα.periodicLinearizedReturn_def]
  refine (hα.charpoly_linearizedReebReturn_eq_of_flowOf (hc.mem_flowDomain 0 _) hpt _ _
    (hc.mem_flowDomain _ γ.point) hp₂).trans ?_
  refine congrArg LinearMap.charpoly ?_
  refine (hα.linearizedReebReturn_congr_time _ hp₂ (hc.mem_flowDomain _ γ.point) hk₂ hper).trans ?_
  exact hα.linearizedReebReturn_natCast_mul (hc.mem_flowDomain γ.period γ.point) hpγ (k : ℕ) _ hk₂

/-- The eigenvalues of `periodicLinearizedReturn` on `γ.iterate k` are those of the `k`-th power of
`periodicLinearizedReturn` on `γ`. -/
theorem IsContactForm.hasEigenvalue_periodicLinearizedReturn_iterate_iff (hα : α.IsContactForm)
    (hc : IsCompleteVectorField α.reebVectorField)
    (γ : Flow.PeriodicTrajectory (hα.reebFlow hc)) (k : ℕ+) (μ : ℝ) :
    (hα.periodicLinearizedReturn hc (γ.iterate k)).HasEigenvalue μ ↔
      (hα.periodicLinearizedReturn hc γ ^ (k : ℕ)).HasEigenvalue μ := by
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Module.End.hasEigenvalue_iff_isRoot_charpoly,
    hα.charpoly_periodicLinearizedReturn_iterate hc γ k]

/-- Two periodic Reeb trajectories representing the same unparametrized `ClosedOrbit` have
linearized Reeb return maps with the same characteristic polynomial. -/
theorem IsContactForm.charpoly_periodicLinearizedReturn_eq_of_mk_eq (hα : α.IsContactForm)
    (hc : IsCompleteVectorField α.reebVectorField)
    {γ₁ γ₂ : Flow.PeriodicTrajectory (hα.reebFlow hc)}
    (h : Flow.ClosedOrbit.mk γ₁ = Flow.ClosedOrbit.mk γ₂) :
    (hα.periodicLinearizedReturn hc γ₁).charpoly =
      (hα.periodicLinearizedReturn hc γ₂).charpoly := by
  obtain ⟨s, hs⟩ := Flow.ClosedOrbit.mk_eq_mk_iff.1 h
  have hpt : flowOf α.reebVectorField s γ₂.point = γ₁.point := by
    rw [← hα.reebFlow_apply hc]
    simpa using congrArg Flow.PeriodicTrajectory.point hs
  have hper : γ₂.period = γ₁.period := by
    simpa using congrArg Flow.PeriodicTrajectory.period hs
  have h₁ : flowOf α.reebVectorField γ₂.period γ₁.point = γ₁.point := by
    rw [hper, ← hα.reebFlow_apply hc]
    exact γ₁.apply_period
  simp_rw [hα.periodicLinearizedReturn_def]
  refine (congrArg LinearMap.charpoly
    (hα.linearizedReebReturn_congr_time _ _ (hc.mem_flowDomain γ₂.period γ₁.point) h₁
      hper.symm)).trans ?_
  exact (hα.charpoly_linearizedReebReturn_eq_of_flowOf (hc.mem_flowDomain s γ₂.point) hpt _ _
    (hc.mem_flowDomain γ₂.period γ₁.point) h₁).symm

/-- Two periodic Reeb trajectories representing the same unparametrized `ClosedOrbit` have the same
eigenvalues for their linearized Reeb return maps. -/
theorem IsContactForm.hasEigenvalue_periodicLinearizedReturn_iff_of_mk_eq (hα : α.IsContactForm)
    (hc : IsCompleteVectorField α.reebVectorField)
    {γ₁ γ₂ : Flow.PeriodicTrajectory (hα.reebFlow hc)}
    (h : Flow.ClosedOrbit.mk γ₁ = Flow.ClosedOrbit.mk γ₂) (μ : ℝ) :
    (hα.periodicLinearizedReturn hc γ₁).HasEigenvalue μ ↔
      (hα.periodicLinearizedReturn hc γ₂).HasEigenvalue μ := by
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Module.End.hasEigenvalue_iff_isRoot_charpoly,
    hα.charpoly_periodicLinearizedReturn_eq_of_mk_eq hc h]

/-- An unparametrized closed Reeb orbit is **nondegenerate** when `1` is not an eigenvalue of the
linearized Reeb return map of its representatives on the contact hyperplane. -/
def IsContactForm.IsNondegenerateOrbit (hα : α.IsContactForm)
    (hc : IsCompleteVectorField α.reebVectorField)
    (γ : Flow.ClosedOrbit (hα.reebFlow hc)) : Prop :=
  ∀ δ : Flow.PeriodicTrajectory (hα.reebFlow hc), Flow.ClosedOrbit.mk δ = γ →
    ¬(hα.periodicLinearizedReturn hc δ).HasEigenvalue 1

/-- Nondegeneracy of `ClosedOrbit.mk γ` is the absence of eigenvalue `1` for
`periodicLinearizedReturn` at `γ`. -/
@[simp]
theorem IsContactForm.isNondegenerateOrbit_mk_iff (hα : α.IsContactForm)
    (hc : IsCompleteVectorField α.reebVectorField)
    (γ : Flow.PeriodicTrajectory (hα.reebFlow hc)) :
    hα.IsNondegenerateOrbit hc (Flow.ClosedOrbit.mk γ) ↔
      ¬(hα.periodicLinearizedReturn hc γ).HasEigenvalue 1 :=
  ⟨fun h ↦ h γ rfl, fun h _ hδ ↦
    mt (hα.hasEigenvalue_periodicLinearizedReturn_iff_of_mk_eq hc hδ 1).1 h⟩

/-- **Nondegeneracy of an iterate.** The `k`-fold iterate of a closed Reeb orbit is nondegenerate
iff `1` is not an eigenvalue of the `k`-th power `(A_γ)^k` of its linearized Reeb return map. -/
theorem IsContactForm.isNondegenerateOrbit_iterate_mk_iff (hα : α.IsContactForm)
    (hc : IsCompleteVectorField α.reebVectorField)
    (γ : Flow.PeriodicTrajectory (hα.reebFlow hc)) (k : ℕ+) :
    hα.IsNondegenerateOrbit hc ((Flow.ClosedOrbit.mk γ).iterate k) ↔
      ¬(hα.periodicLinearizedReturn hc γ ^ (k : ℕ)).HasEigenvalue 1 := by
  rw [Flow.ClosedOrbit.iterate_mk, hα.isNondegenerateOrbit_mk_iff,
    hα.hasEigenvalue_periodicLinearizedReturn_iterate_iff]

/-- **Double covers at eigenvalue `-1` are degenerate.** If `-1` is an eigenvalue of the linearized
Reeb return map of `γ`, then its double cover `(ClosedOrbit.mk γ).iterate 2` is degenerate, even
when `γ` itself is nondegenerate. -/
theorem IsContactForm.not_isNondegenerateOrbit_iterate_two_of_hasEigenvalue_neg_one
    (hα : α.IsContactForm) (hc : IsCompleteVectorField α.reebVectorField)
    {γ : Flow.PeriodicTrajectory (hα.reebFlow hc)}
    (hneg : (hα.periodicLinearizedReturn hc γ).HasEigenvalue (-1)) :
    ¬hα.IsNondegenerateOrbit hc ((Flow.ClosedOrbit.mk γ).iterate 2) := by
  rw [hα.isNondegenerateOrbit_iterate_mk_iff, not_not]
  simpa using hneg.pow 2

/-- **Finiteness of nondegenerate closed Reeb orbits meeting a compact window below an action
bound.** For any complete Reeb flow and compact subset `K ⊆ M`, if every closed Reeb orbit meeting
`K` of period (equivalently, contact action) at most `A` is nondegenerate, then the set of
unparametrized closed Reeb orbits meeting `K` of period at most `A` (including multiply covered
orbits) is finite. -/
theorem IsContactForm.finite_closedOrbit_inter_nonempty_and_period_le (hα : α.IsContactForm)
    (hc : IsCompleteVectorField α.reebVectorField) {K : Set M} (hK : IsCompact K) (A : ℝ)
    (hnd : ∀ γ : Flow.ClosedOrbit (hα.reebFlow hc),
      (γ.support ∩ K).Nonempty → γ.period ≤ A → hα.IsNondegenerateOrbit hc γ) :
    {γ : Flow.ClosedOrbit (hα.reebFlow hc) |
      (γ.support ∩ K).Nonempty ∧ γ.period ≤ A}.Finite := by
  have hv := hα.contMDiff_reebVectorField.of_le (m := 1) (by simp)
  obtain ⟨ε, hε, hlow⟩ :=
    (hα.reebFlow hc).exists_pos_period_le_of_isCompact hK fun x _ ↦ hα.exists_reebFlow_ne hc x
  set S : Set (ℝ × M) := Icc ε A ×ˢ K
  have hS : IsCompact S := isCompact_Icc.prod hK
  have hSD : S ⊆ flowDomain α.reebVectorField := fun x _ ↦ hc.mem_flowDomain x.1 x.2
  have hSnd : ∀ x ∈ S, flowOf α.reebVectorField x.1 x.2 = x.2 →
      ∃ g : M → ℝ, ContMDiffAt I 𝓘(ℝ) 1 g x.2 ∧
        mvfderiv I g x.2 (α.reebVectorField x.2) ≠ 0 ∧
        ¬(returnDerivative α.reebVectorField g x.1 x.2).HasEigenvalue 1 := by
    rintro ⟨t, z⟩ ⟨⟨htε, htA⟩, hzK⟩ htz
    let δ : Flow.PeriodicTrajectory (hα.reebFlow hc) :=
      ⟨z, t, hε.trans_le htε, by rw [hα.reebFlow_apply, htz], hα.exists_reebFlow_ne hc z⟩
    have hmeet : ((Flow.ClosedOrbit.mk δ).support ∩ K).Nonempty :=
      ⟨z, Flow.ClosedOrbit.point_mem_support δ, hzK⟩
    have hδ : ¬(hα.periodicLinearizedReturn hc δ).HasEigenvalue 1 :=
      (hα.isNondegenerateOrbit_mk_iff hc δ).1
        (hnd (Flow.ClosedOrbit.mk δ) hmeet (by rw [Flow.ClosedOrbit.period_mk]; exact htA))
    obtain ⟨g, hg, hgv⟩ :=
      exists_contMDiffAt_mvfderiv_ne_zero (I := I) (hα.reebVectorField_ne_zero z) 1
    exact ⟨g, hg, hgv,
      mt (hα.hasEigenvalue_returnDerivative_iff (hc.mem_flowDomain t z) htz hg hgv one_ne_zero).1
        hδ⟩
  obtain ⟨F, -, hF⟩ := exists_finset_forall_fst_eq_and_exists_flowOf_eq_snd hv hS hSD hSnd
  refine Flow.ClosedOrbit.finite_of_exists_finset (F := F) ?_
  rintro γ ⟨⟨p, hpγ, hpK⟩, hγA⟩
  induction γ using Flow.ClosedOrbit.ind with | h γ => ?_
  rw [Flow.ClosedOrbit.period_mk] at hγA ⊢
  rw [Flow.ClosedOrbit.support_mk] at hpγ
  obtain ⟨r, rfl⟩ := (Flow.mem_orbit_iff _).1 hpγ
  let γ' : Flow.PeriodicTrajectory (hα.reebFlow hc) := r +ᵥ γ
  have hεγ : ε ≤ γ.period := hlow γ'.point hpK γ'.period γ'.period_pos γ'.apply_period
  have hper : flowOf α.reebVectorField γ.period γ'.point = γ'.point := by
    rw [← hα.reebFlow_apply hc]
    exact γ'.apply_period
  obtain ⟨y, hyF, hy1, s, -, hsy⟩ :=
    hF (γ.period, γ'.point) ⟨⟨hεγ, hγA⟩, hpK⟩ hper
  refine ⟨y, hyF, hy1, ?_⟩
  rw [← Flow.ClosedOrbit.mk_vadd r γ, Flow.ClosedOrbit.support_mk, Flow.mem_orbit_iff]
  refine ⟨-s, ?_⟩
  have hsy' : hα.reebFlow hc s y.2 = γ'.point := by rwa [hα.reebFlow_apply]
  rw [← hsy', ← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]

/-- **Finiteness of nondegenerate closed Reeb orbits below an action bound.** On a compact
boundaryless contact manifold, if every closed Reeb orbit of period (equivalently, contact action)
at most `A` is nondegenerate, then the set of unparametrized closed Reeb orbits of period at most
`A` (including multiply covered orbits) is finite. -/
theorem IsContactForm.finite_closedOrbit_period_le [CompactSpace M] (hα : α.IsContactForm)
    (hc : IsCompleteVectorField α.reebVectorField) (A : ℝ)
    (hnd : ∀ γ : Flow.ClosedOrbit (hα.reebFlow hc), γ.period ≤ A →
      hα.IsNondegenerateOrbit hc γ) :
    {γ : Flow.ClosedOrbit (hα.reebFlow hc) | γ.period ≤ A}.Finite := by
  refine (hα.finite_closedOrbit_inter_nonempty_and_period_le hc isCompact_univ A
    fun γ _ ↦ hnd γ).subset fun γ hγ ↦ ⟨?_, hγ⟩
  induction γ using Flow.ClosedOrbit.ind with | h γ => ?_
  exact ⟨γ.point, Flow.ClosedOrbit.point_mem_support γ, mem_univ _⟩

end ClosedOrbit

end TauCeti.SmoothForm

/-! ### Non-vacuity model: the contact circle `AddCircle p` -/

namespace AddCircle

open TauCeti TauCeti.SmoothForm

variable (p : ℝ) [Fact (0 < p)]

/-- On the circle `AddCircle p`, the contact hyperplane `ker (timeForm p)` is trivial (`⊥`). -/
@[simp]
theorem kerDistribution_timeForm (x : AddCircle p) :
    (timeForm p).kerDistribution x = ⊥ :=
  Submodule.ext fun v ↦ by
    rw [mem_kerDistribution, Submodule.mem_bot, timeForm_apply, Matrix.cons_val_zero]
    rfl

/-- The time form `dt_p` on `AddCircle p` (`p > 0`) is a contact form in dimension `1`: it vanishes
nowhere, and `d(dt_p) = 0` is vacuously nondegenerate on `ker (dt_p) = ⊥`. -/
theorem isContactForm_timeForm : (timeForm p).IsContactForm :=
  isContactForm_iff.2 fun x ↦ ⟨⟨(1 : ℝ), by simp⟩, fun v hv _ ↦ by
    have hv0 : v ∈ (timeForm p).kerDistribution x := mem_kerDistribution.2 hv
    rwa [kerDistribution_timeForm, Submodule.mem_bot] at hv0⟩

/-- The Reeb vector field of `AddCircle.timeForm p` is the unit vector field `∂_t`. -/
@[simp]
theorem reebVectorField_timeForm : (timeForm p).reebVectorField = timeVectorField p := by
  funext x
  symm
  rw [(isContactForm_timeForm p).eq_reebVectorField_iff_kerDistribution]
  refine ⟨by simp, fun w hw ↦ ?_⟩
  have hw0 : w = 0 := by
    have hm : w ∈ (timeForm p).kerDistribution x := mem_kerDistribution.2 hw
    rwa [kerDistribution_timeForm, Submodule.mem_bot] at hm
  rw [hw0]
  exact ((mextDeriv (timeForm p).val) x).map_coord_zero 1 rfl

/-- The global Reeb flow of `AddCircle.timeForm p` is the translation flow of `AddCircle p`. -/
@[simp]
theorem reebFlow_timeForm (hc : IsCompleteVectorField (timeForm p).reebVectorField) :
    (isContactForm_timeForm p).reebFlow hc = translationFlow p :=
  Flow.ext fun t x ↦ by
    rw [IsContactForm.reebFlow_apply]
    have hγ : IsMIntegralCurve (fun s ↦ translationFlow p s x) (timeForm p).reebVectorField := by
      rw [reebVectorField_timeForm]
      exact isMIntegralCurve_translationFlow p x
    simpa using flowOf_eq_of_isMIntegralCurve
      ((isContactForm_timeForm p).contMDiff_reebVectorField.of_le (by simp)) hγ t

/-- Every closed Reeb orbit of `AddCircle.timeForm p` (primitive and multiply covered alike) is
nondegenerate, since the contact hyperplane `⊥` has no nonzero vectors. -/
theorem isNondegenerateOrbit_timeForm (hc : IsCompleteVectorField (timeForm p).reebVectorField)
    (γ : Flow.ClosedOrbit ((isContactForm_timeForm p).reebFlow hc)) :
    (isContactForm_timeForm p).IsNondegenerateOrbit hc γ := by
  rintro δ rfl h1
  obtain ⟨v, hv⟩ := h1.exists_hasEigenvector
  have hv0 : v.val ∈ (⊥ : Submodule ℝ (TangentSpace 𝓘(ℝ) δ.point)) :=
    kerDistribution_timeForm p δ.point ▸ v.property
  exact hv.2 (Subtype.ext ((Submodule.mem_bot ℝ).1 hv0))

/-- The canonical primitive periodic trajectory of `AddCircle.translationFlow p` starting at `0`
with period `p`. Together with its iterates `((primitiveTrajectory p).iterate k)`, it witnesses
that closed Reeb orbits of arbitrary multiplicity `k : ℕ+` exist and satisfy
`IsContactForm.finite_closedOrbit_period_le` on `AddCircle p`. -/
def primitiveTrajectory : Flow.PeriodicTrajectory (translationFlow p) where
  point := 0
  period := p
  period_pos := Fact.out
  apply_period := by simp
  exists_apply_ne := ⟨p / 2, by simpa using period_div_two_coe_ne_zero (p := p)⟩

@[simp]
theorem primitiveTrajectory_point : (primitiveTrajectory p).point = 0 := by
  unfold primitiveTrajectory
  rfl

@[simp]
theorem primitiveTrajectory_period : (primitiveTrajectory p).period = p := by
  unfold primitiveTrajectory
  rfl

/-- The canonical trajectory of period `p` on `AddCircle p` has covering multiplicity `1`. -/
@[simp]
theorem multiplicity_mk_primitiveTrajectory :
    (Flow.ClosedOrbit.mk (primitiveTrajectory p)).multiplicity = 1 := by
  have hp0 : (0 : ℝ) < p := Fact.out
  have hmin : (translationFlow p).minimalPeriod (0 : AddCircle p) = p := by
    refine le_antisymm ((translationFlow p).minimalPeriod_le (by simp) hp0) ?_
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1
      ((translationFlow_apply_eq_self_iff p).1 ((translationFlow p).apply_minimalPeriod 0))
    have hmpos : 0 < (translationFlow p).minimalPeriod (0 : AddCircle p) := by
      simpa using (primitiveTrajectory p).minimalPeriod_pos
    have hk1 : 1 ≤ k := by
      by_contra! hk0
      have hk0' : k ≤ 0 := by omega
      have hnonpos := mul_nonpos_of_nonpos_of_nonneg (Int.cast_nonpos.2 hk0') hp0.le
      rw [zsmul_eq_mul] at hk
      linarith
    have hk1' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    rw [zsmul_eq_mul] at hk
    nlinarith
  have hm := (Flow.ClosedOrbit.mk (primitiveTrajectory p)).multiplicity_mul_minimalPeriod
  rw [Flow.ClosedOrbit.minimalPeriod_mk, Flow.ClosedOrbit.period_mk, primitiveTrajectory_point,
    primitiveTrajectory_period, hmin] at hm
  have hcast : (((Flow.ClosedOrbit.mk (primitiveTrajectory p)).multiplicity : ℕ) : ℝ) = 1 := by
    nlinarith
  exact PNat.coe_injective (by exact_mod_cast hcast)

end AddCircle
