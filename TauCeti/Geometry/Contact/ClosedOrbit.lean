/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Flow.ClosedOrbit
public import TauCeti.Geometry.Contact.Flat
public import TauCeti.Geometry.Contact.Flow
public import TauCeti.Geometry.Contact.PeriodBound
public import TauCeti.Geometry.Manifold.Flow.NondegenerateOrbit
public import TauCeti.Geometry.Manifold.Instances.AddCircle

/-!
# Closed Reeb orbits, linearized return maps and finiteness

Let `α` be a contact form on a finite-dimensional boundaryless manifold `M` whose Reeb vector
field `R_α` is complete (which holds automatically when `M` is compact, by
`TauCeti.SmoothForm.IsContactForm.isComplete_reebVectorField`). Its maximal integral curves assemble
into the **Reeb flow** `TauCeti.SmoothForm.IsContactForm.reebFlow`. Since `R_α` vanishes nowhere,
every periodic integral curve has no rest points and gives a periodic trajectory and a closed Reeb
orbit (`Flow.PeriodicTrajectory` and `Flow.ClosedOrbit` of `reebFlow`).

A closed Reeb orbit `γ` of period `T = κ · T₀` over a primitive orbit of minimal period `T₀` has
covering multiplicity `κ = γ.multiplicity`, circle parametrizations
`Flow.PeriodicTrajectory.circleMap`, and finite reparametrization group `ZMod κ`
(`Flow.ClosedOrbit.reparamGroup`), which permutes the `κ` asymptotic markers
`{θ : AddCircle T | c.circleMap θ = x}` above any point `x` on the orbit simply transitively. For
a contact form, `c.circleMap` is smooth and has velocity `R_α` everywhere
(`TauCeti.SmoothForm.IsContactForm.hasMFDerivAt_circleMap`).

Because the time-`t` Reeb flow is a strict contactomorphism
(`TauCeti.SmoothForm.IsContactForm.isStrictContactomorphism_globalFlowDiffeomorph_reebVectorField`),
its differential preserves the contact hyperplane `ξ = ker α` and the two-form `dα`. At a periodic
point `x` of period `T`, restricting `d(φ_T)_x` to `ξ_x` defines the **linearized Reeb return map**
`TauCeti.SmoothForm.IsContactForm.reebReturnMap`, a linear endomorphism of `ξ_x` that preserves
`dα_x|_ξ`. Iterating the period raises `reebReturnMap` to the corresponding power
(`TauCeti.SmoothForm.IsContactForm.reebReturnMap_natCast_mul`), and moving along the orbit
conjugates `reebReturnMap` (`TauCeti.SmoothForm.IsContactForm.reebFlowKerEquiv_conj_reebReturnMap`).
For any local transverse section `{g = g x}`, the projection onto `ξ_x` along `R_α(x)` conjugates
the normal return derivative `TauCeti.normalReturnDerivative` to `reebReturnMap`
(`TauCeti.SmoothForm.IsContactForm.kerSectionEquivKerDistribution_conj_normalReturnDerivative`),
so `1` is an eigenvalue of `reebReturnMap` exactly when `1` is an eigenvalue of `returnDerivative`.

A closed Reeb orbit `γ` is **nondegenerate**
(`TauCeti.SmoothForm.IsContactForm.IsNondegenerateOrbit`) when `1` is not an eigenvalue of
`reebReturnMap`; an iterate `γ.iterate k` is nondegenerate exactly when `1` is not an eigenvalue of
the `k`-th power of `reebReturnMap`
(`TauCeti.SmoothForm.IsContactForm.isNondegenerateOrbit_iterate_iff`). On a compact boundaryless
contact manifold, combining the uniform positive lower bound for Reeb periods
(`TauCeti.SmoothForm.IsContactForm.exists_pos_period_le`) with the isolation of nondegenerate
closed orbits in a compact period window yields finiteness of nondegenerate closed Reeb orbits,
including all covered orbits, below any fixed action bound `T`
(`TauCeti.SmoothForm.IsContactForm.finite_closedOrbit_period_le`).

## Main definitions

* `TauCeti.SmoothForm.IsContactForm.reebFlow`: the global Reeb flow of a contact form with complete
  Reeb vector field.
* `TauCeti.SmoothForm.IsContactForm.reebTrajectory`: a periodic Reeb trajectory from a base point
  and return time.
* `TauCeti.SmoothForm.IsContactForm.reebReturnMap`: the linearized Reeb return map restricted to
  `ξ = α.kerDistribution`.
* `TauCeti.SmoothForm.IsContactForm.IsNondegenerateOrbit`: nondegeneracy of a closed Reeb orbit.

## Main results

* `TauCeti.SmoothForm.IsContactForm.hasMFDerivAt_circleMap`: the circle parametrization of a
  periodic Reeb trajectory is smooth with velocity `R_α`.
* `TauCeti.SmoothForm.IsContactForm.reebReturnMap_natCast_mul`: the linearized return map of a
  `k`-fold iterate is the `k`-th power of the linearized return map.
* `TauCeti.SmoothForm.IsContactForm.reebReturnMap_preserves_mextDeriv`: the linearized return map
  preserves `dα` on `ξ`.
* `TauCeti.SmoothForm.IsContactForm.kerSectionEquivKerDistribution_conj_normalReturnDerivative`:
  for any local transverse section, `reebReturnMap` is conjugate to `normalReturnDerivative`.
* `TauCeti.SmoothForm.IsContactForm.hasEigenvalue_reebReturnMap_iff_hasEigenvalue_returnDerivative`:
  `1` (or any nonzero `μ`) is an eigenvalue of `reebReturnMap` iff it is an eigenvalue of
  `returnDerivative`.
* `TauCeti.SmoothForm.IsContactForm.isNondegenerateOrbit_iterate_iff`: nondegeneracy of the
  `k`-fold cover in terms of the `k`-th power of `reebReturnMap`.
* `TauCeti.SmoothForm.IsContactForm.finite_closedOrbit_period_le`: finitely many closed Reeb orbits
  of period at most `T` when all such orbits are nondegenerate.

## References

* F. Bourgeois, Y. Eliashberg, H. Hofer, K. Wysocki, E. Zehnder,
  *Compactness results in Symplectic Field Theory*, Geom. Topol. 7 (2003), 799–888, Section 2.3.
* Y. Eliashberg, A. Givental, H. Hofer, *Introduction to symplectic field theory*, Geom. Funct.
  Anal. (2000), Special Volume, Part II, 560–673, Section 1.2.
* J. Pardon, *Contact homology and virtual fundamental cycles*, Geom. Topol. 23 (2019), 771–948,
  Sections 1.1–1.2.
-/

public section

noncomputable section

open Set
open scoped ContDiff Manifold

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {α : SmoothForm I M ℝ 1}

namespace IsContactForm

/-! ### The Reeb flow and periodic Reeb trajectories -/

section ReebFlow

/-- On a compact boundaryless contact manifold, the Reeb vector field is complete. -/
theorem isComplete_reebVectorField [CompactSpace M] (hα : α.IsContactForm) :
    IsCompleteVectorField α.reebVectorField :=
  isCompleteVectorField_of_compactSpace (hα.contMDiff_reebVectorField.of_le (by simp))

variable (hα : α.IsContactForm) (hc : IsCompleteVectorField α.reebVectorField)

/-- The **Reeb flow** of a contact form whose Reeb vector field is complete. -/
def reebFlow : Flow ℝ M :=
  globalFlow α.reebVectorField (hα.contMDiff_reebVectorField.of_le (by simp)) hc

/-- The Reeb flow agrees with the maximal flow `TauCeti.flowOf` of `α.reebVectorField`. -/
theorem reebFlow_eq_flowOf (t : ℝ) (x : M) :
    hα.reebFlow hc t x = flowOf α.reebVectorField t x := by
  rw [reebFlow, ← flowOf_eq_globalFlow]

/-- The Reeb flow equals the time-`t` global flow diffeomorphism. -/
theorem reebFlow_eq_globalFlowDiffeomorph (t : ℝ) (x : M) :
    hα.reebFlow hc t x =
      globalFlowDiffeomorph hc le_top hα.contMDiff_reebVectorField t x :=
  (globalFlowDiffeomorph_apply hc le_top hα.contMDiff_reebVectorField t x).symm

/-- Orbits of the Reeb flow are integral curves of the Reeb vector field. -/
theorem isMIntegralCurve_reebFlow (x : M) :
    IsMIntegralCurve (fun t ↦ hα.reebFlow hc t x) α.reebVectorField :=
  isMIntegralCurve_globalFlow _ hc x

/-- The time-`t` map of the Reeb flow is smooth. -/
theorem contMDiff_reebFlow_apply (t : ℝ) :
    ContMDiff I I ∞ (hα.reebFlow hc t) :=
  contMDiff_globalFlow_apply hc le_top hα.contMDiff_reebVectorField t

/-- The differential of the Reeb flow preserves the Reeb vector field. -/
theorem mfderiv_reebFlow_apply_self (t : ℝ) (x : M) :
    mfderiv I I (hα.reebFlow hc t) x (α.reebVectorField x) =
      α.reebVectorField (hα.reebFlow hc t x) :=
  mfderiv_globalFlow_apply_self _ hc t x

/-- No point is stationary under the Reeb flow, since the Reeb vector field vanishes nowhere. -/
theorem exists_reebFlow_ne_self (x : M) : ∃ t : ℝ, hα.reebFlow hc t x ≠ x := by
  by_contra h
  have hfix : ∀ t, hα.reebFlow hc t x = x := by
    simpa only [not_exists, not_not] using h
  exact hα.reebVectorField_ne_zero x ((forall_globalFlow_eq_self_iff _ hc x).1 hfix)

/-- Construct a periodic Reeb trajectory from a base point `x` and a positive return time `T`
with `hα.reebFlow hc T x = x`. Non-stationarity is automatic from `R_α ≠ 0`. -/
def reebTrajectory (x : M) {T : ℝ} (hT : 0 < T) (hfix : hα.reebFlow hc T x = x) :
    Flow.PeriodicTrajectory (hα.reebFlow hc) where
  point := x
  period := T
  period_pos := hT
  apply_period := hfix
  exists_apply_ne := hα.exists_reebFlow_ne_self hc x

@[simp]
theorem point_reebTrajectory (x : M) {T : ℝ} (hT : 0 < T) (hfix : hα.reebFlow hc T x = x) :
    (hα.reebTrajectory hc x hT hfix).point = x :=
  (rfl)

@[simp]
theorem period_reebTrajectory (x : M) {T : ℝ} (hT : 0 < T) (hfix : hα.reebFlow hc T x = x) :
    (hα.reebTrajectory hc x hT hfix).period = T :=
  (rfl)

/-- Construct a periodic Reeb trajectory from a periodic integral curve of `α.reebVectorField`. -/
def reebTrajectoryOfIntegralCurve {γ : ℝ → M} (hγ : IsMIntegralCurve γ α.reebVectorField)
    {T : ℝ} (hT : 0 < T) (hper : Function.Periodic γ T) :
    Flow.PeriodicTrajectory (hα.reebFlow hc) :=
  hα.reebTrajectory hc (γ 0) hT (by
    rw [reebFlow, globalFlow_eq_of_isMIntegralCurve _ hc hγ T]
    simpa using hper 0)

/-- The circle parametrization `AddCircle c.period → M` of a periodic Reeb trajectory is smooth. -/
theorem contMDiff_circleMap (c : Flow.PeriodicTrajectory (hα.reebFlow hc)) :
    ContMDiff 𝓘(ℝ) I ∞ c.circleMap := by
  rw [← (AddCircle.isLocalDiffeomorph_coe c.period ∞).contMDiff_comp_iff
    QuotientAddGroup.mk_surjective le_rfl]
  have hcomp : c.circleMap ∘ ((↑) : ℝ → AddCircle c.period) =
      fun s ↦ hα.reebFlow hc s c.point := funext c.circleMap_coe
  rw [hcomp]
  exact (contMDiff_globalFlow_uncurry hc le_top hα.contMDiff_reebVectorField).comp
    (contMDiff_id.prodMk contMDiff_const)

/-- The circle parametrization `AddCircle c.period → M` of a periodic Reeb trajectory is smooth
with velocity `R_α` everywhere. -/
theorem hasMFDerivAt_circleMap (c : Flow.PeriodicTrajectory (hα.reebFlow hc))
    (θ : AddCircle c.period) :
    HasMFDerivAt 𝓘(ℝ) I c.circleMap θ
      ((1 : ℝ →L[ℝ] ℝ).smulRight (α.reebVectorField (c.circleMap θ))) := by
  induction θ using QuotientAddGroup.induction_on with
  | H t =>
    have hd : MDifferentiableAt 𝓘(ℝ) I c.circleMap t :=
      ((hα.contMDiff_circleMap hc c) t).mdifferentiableAt (by simp)
    have hcomp : c.circleMap ∘ ((↑) : ℝ → AddCircle c.period) =
        fun s ↦ hα.reebFlow hc s c.point := funext c.circleMap_coe
    have hlift : HasMFDerivAt 𝓘(ℝ) I (c.circleMap ∘ ((↑) : ℝ → AddCircle c.period)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (α.reebVectorField (c.circleMap t))) := by
      rw [hcomp, c.circleMap_coe]
      exact hα.isMIntegralCurve_reebFlow hc c.point t
    rw [← AddCircle.mfderiv_comp_coe.symm.trans hlift.mfderiv]
    exact hd.hasMFDerivAt

omit hc in
/-- On a compact boundaryless contact manifold, the periods of all closed Reeb orbits (including
all covered orbits) have a uniform positive lower bound. -/
theorem exists_pos_period_le_closedOrbit [CompactSpace M] :
    ∃ ε > 0, ∀ γ : Flow.ClosedOrbit (hα.reebFlow hα.isComplete_reebVectorField), ε ≤ γ.period := by
  obtain ⟨ε, hε, hbound⟩ := hα.exists_pos_period_le
  refine ⟨ε, hε, fun γ ↦ ?_⟩
  induction γ using Flow.ClosedOrbit.ind with
  | h c =>
    simpa [Flow.ClosedOrbit.period_mk] using
      hbound (fun t ↦ hα.reebFlow hα.isComplete_reebVectorField t c.point)
        (hα.isMIntegralCurve_reebFlow hα.isComplete_reebVectorField c.point)
        c.period c.period_pos fun t ↦ by dsimp only; rw [Flow.map_add, c.apply_period]

end ReebFlow

/-! ### The linearized Reeb return map on `ξ = ker α` -/

section ReturnMap

variable (hα : α.IsContactForm) (hc : IsCompleteVectorField α.reebVectorField)

/-- The differential of the Reeb flow maps the contact distribution `ξ = ker α` to itself. -/
theorem mfderiv_reebFlow_mem_kerDistribution (t : ℝ) {x : M} {v : TangentSpace I x}
    (hv : v ∈ α.kerDistribution x) :
    mfderiv I I (hα.reebFlow hc t) x v ∈ α.kerDistribution (hα.reebFlow hc t x) := by
  let Φ := globalFlowDiffeomorph hc le_top hα.contMDiff_reebVectorField t
  have hstrict : Φ.IsStrictContactomorphism α α :=
    hα.isStrictContactomorphism_globalFlowDiffeomorph_reebVectorField hc t
  have hmem := (Diffeomorph.isContactomorphism_iff.1 hstrict.isContactomorphism x v).2 hv
  have hcoe : (hα.reebFlow hc).toFun t = ⇑Φ :=
    funext fun y ↦ hα.reebFlow_eq_globalFlowDiffeomorph hc t y
  rw [hcoe]
  exact hmem

/-- The Reeb flow preserves the exterior derivative `dα` on tangent vectors. -/
theorem mextDeriv_mfderiv_reebFlow (t : ℝ) (x : M) (v w : TangentSpace I x) :
    mextDeriv α.1 (hα.reebFlow hc t x)
        ![mfderiv I I (hα.reebFlow hc t) x v, mfderiv I I (hα.reebFlow hc t) x w] =
      mextDeriv α.1 x ![v, w] := by
  let Φ := globalFlowDiffeomorph hc le_top hα.contMDiff_reebVectorField t
  have hstrict : SmoothForm.mpullback Φ Φ.contMDiff α = α :=
    Diffeomorph.isStrictContactomorphism_def.1
      (hα.isStrictContactomorphism_globalFlowDiffeomorph_reebVectorField hc t)
  have hcoe : (hα.reebFlow hc).toFun t = ⇑Φ :=
    funext fun y ↦ hα.reebFlow_eq_globalFlowDiffeomorph hc t y
  change mextDeriv α.1 ((hα.reebFlow hc).toFun t x)
      ![mfderiv I I ((hα.reebFlow hc).toFun t) x v,
        mfderiv I I ((hα.reebFlow hc).toFun t) x w] = _
  rw [hcoe, ← SmoothForm.mextDeriv_mpullback_apply_two Φ Φ.contMDiff α x v w, hstrict]

/-- The differential of the time-`t` Reeb flow restricted to `ξ = ker α` as a linear equivalence
`ξ_x ≃ₗ[ℝ] ξ_(φ_t x)`. -/
def reebFlowKerEquiv (t : ℝ) (x : M) :
    α.kerDistribution x ≃ₗ[ℝ] α.kerDistribution (hα.reebFlow hc t x) :=
  let fwd : α.kerDistribution x →ₗ[ℝ] α.kerDistribution (hα.reebFlow hc t x) :=
    (mfderiv I I (hα.reebFlow hc t) x).toLinearMap.restrict
      fun _ hv ↦ hα.mfderiv_reebFlow_mem_kerDistribution hc t hv
  let inv : α.kerDistribution (hα.reebFlow hc t x) →ₗ[ℝ] α.kerDistribution x :=
    (mfderiv I I (hα.reebFlow hc (-t)) (hα.reebFlow hc t x)).toLinearMap.restrict fun v hv ↦ by
      have h := hα.mfderiv_reebFlow_mem_kerDistribution hc (-t) hv
      rwa [(hα.reebFlow hc).map_neg_apply_map t x] at h
  LinearEquiv.ofLinearMap fwd inv
    (LinearMap.ext fun w ↦ Subtype.ext <| by
      have hdiff1 : MDifferentiableAt I I (hα.reebFlow hc t) x :=
        ((hα.contMDiff_reebFlow_apply hc t) x).mdifferentiableAt (by simp)
      have hdiff2 : MDifferentiableAt I I (hα.reebFlow hc (-t)) (hα.reebFlow hc t x) :=
        ((hα.contMDiff_reebFlow_apply hc (-t)) _).mdifferentiableAt (by simp)
      have hcomp : hα.reebFlow hc t ∘ hα.reebFlow hc (-t) = id := by
        funext y
        simp
      have hd := (mfderiv_comp_apply_of_eq (hα.reebFlow hc t x) hdiff1 hdiff2
        ((hα.reebFlow hc).map_neg_apply_map t x) (w : TangentSpace I (hα.reebFlow hc t x))).symm
      rw [hcomp, mfderiv_id, ContinuousLinearMap.id_apply] at hd
      exact hd)
    (LinearMap.ext fun w ↦ Subtype.ext <| by
      have hdiff1 : MDifferentiableAt I I (hα.reebFlow hc (-t)) (hα.reebFlow hc t x) :=
        ((hα.contMDiff_reebFlow_apply hc (-t)) _).mdifferentiableAt (by simp)
      have hdiff2 : MDifferentiableAt I I (hα.reebFlow hc t) x :=
        ((hα.contMDiff_reebFlow_apply hc t) x).mdifferentiableAt (by simp)
      have hcomp : hα.reebFlow hc (-t) ∘ hα.reebFlow hc t = id := by
        funext y
        simp
      have hd := (mfderiv_comp_apply_of_eq x hdiff1 hdiff2 rfl (w : TangentSpace I x)).symm
      rw [hcomp, mfderiv_id, ContinuousLinearMap.id_apply] at hd
      exact hd)

@[simp]
theorem coe_reebFlowKerEquiv_apply (t : ℝ) (x : M) (v : α.kerDistribution x) :
    (hα.reebFlowKerEquiv hc t x v : TangentSpace I (hα.reebFlow hc t x)) =
      mfderiv I I (hα.reebFlow hc t) x v :=
  (rfl)

/-- The **linearized Reeb return map** at a periodic point `x` of period `T`: the restriction of
`d(φ_T)_x` to the contact hyperplane `ξ_x = ker α_x`. -/
def reebReturnMap {T : ℝ} {x : M} (hfix : hα.reebFlow hc T x = x) :
    Module.End ℝ (α.kerDistribution x) :=
  (show TangentSpace I x →L[ℝ] TangentSpace I x from
      mfderiv I I (hα.reebFlow hc T) x).toLinearMap.restrict fun v hv ↦ by
    have hmem := hα.mfderiv_reebFlow_mem_kerDistribution hc T hv
    rwa [hfix] at hmem

@[simp]
theorem coe_reebReturnMap_apply {T : ℝ} {x : M} (hfix : hα.reebFlow hc T x = x)
    (v : α.kerDistribution x) :
    (hα.reebReturnMap hc hfix v : TangentSpace I x) = mfderiv I I (hα.reebFlow hc T) x v :=
  (rfl)

/-- The linearized Reeb return map preserves `dα_x` on `ξ_x`. -/
theorem reebReturnMap_preserves_mextDeriv {T : ℝ} {x : M} (hfix : hα.reebFlow hc T x = x)
    (v w : α.kerDistribution x) :
    mextDeriv α.1 x ![hα.reebReturnMap hc hfix v, hα.reebReturnMap hc hfix w] =
      mextDeriv α.1 x ![v, w] := by
  simp only [coe_reebReturnMap_apply]
  have h := hα.mextDeriv_mfderiv_reebFlow hc T x v w
  have key : ∀ {y : M} (_ : y = x) (a b : TangentSpace I y) (a' b' : TangentSpace I x),
      a = a' → b = b' → mextDeriv α.1 y ![a, b] = mextDeriv α.1 x ![a', b'] := by
    rintro y rfl a b _ _ rfl rfl
    rfl
  exact (key hfix _ _ _ _ rfl rfl).symm.trans h

/-- The linearized Reeb return map at time `0` is the identity on `ξ_x`. -/
@[simp]
theorem reebReturnMap_zero (x : M) :
    hα.reebReturnMap hc ((hα.reebFlow hc).map_zero_apply x) = 1 := by
  ext v
  simp only [coe_reebReturnMap_apply, one_apply_eq_self]
  have h0 : hα.reebFlow hc 0 = id := funext ((hα.reebFlow hc).map_zero_apply)
  rw [h0, mfderiv_id, ContinuousLinearMap.id_apply]

/-- The linearized Reeb return map of a sum of return times is the composition of the return
maps. -/
theorem reebReturnMap_add {T₁ T₂ : ℝ} {x : M} (h₁ : hα.reebFlow hc T₁ x = x)
    (h₂ : hα.reebFlow hc T₂ x = x) :
    hα.reebReturnMap hc (by rw [Flow.map_add, h₂, h₁] : hα.reebFlow hc (T₁ + T₂) x = x) =
      hα.reebReturnMap hc h₁ * hα.reebReturnMap hc h₂ := by
  ext v
  simp only [coe_reebReturnMap_apply, mul_apply_eq_comp]
  have hd₁ : MDifferentiableAt I I (hα.reebFlow hc T₁) x :=
    ((hα.contMDiff_reebFlow_apply hc T₁) x).mdifferentiableAt (by simp)
  have hd₂ : MDifferentiableAt I I (hα.reebFlow hc T₂) x :=
    ((hα.contMDiff_reebFlow_apply hc T₂) x).mdifferentiableAt (by simp)
  have hcomp : hα.reebFlow hc (T₁ + T₂) = hα.reebFlow hc T₁ ∘ hα.reebFlow hc T₂ :=
    funext ((hα.reebFlow hc).map_add T₁ T₂)
  rw [hcomp, mfderiv_comp_apply_of_eq x hd₁ hd₂ h₂ v]

/-- **The linearized Reeb return map of an iterate is the iterate of the linearized return map.**
At a periodic point `x` of period `T`, the linearized return map at period `k * T` on `ξ_x` is the
`k`-th power of the linearized return map at period `T`. -/
theorem reebReturnMap_natCast_mul {T : ℝ} {x : M} (hfix : hα.reebFlow hc T x = x) (k : ℕ) :
    hα.reebReturnMap hc (by
      have h : (k : ℕ) • T ∈ (hα.reebFlow hc).periods x :=
        nsmul_mem ((hα.reebFlow hc).mem_periods.2 hfix) k
      simpa only [nsmul_eq_mul, Flow.mem_periods] using h :
      hα.reebFlow hc (k * T) x = x) = hα.reebReturnMap hc hfix ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : hα.reebFlow hc (k * T) x = x := by
      have h : k • T ∈ (hα.reebFlow hc).periods x :=
        nsmul_mem ((hα.reebFlow hc).mem_periods.2 hfix) k
      simpa only [nsmul_eq_mul, Flow.mem_periods] using h
    have hmul : ((k + 1 : ℕ) : ℝ) * T = k * T + T := by
      push_cast
      ring
    have hadd : hα.reebFlow hc ((k + 1 : ℕ) * T) x = x := by
      rw [hmul, Flow.map_add, hfix, hk]
    have key : ∀ {S : ℝ} (_ : S = k * T + T) (hfixS : hα.reebFlow hc S x = x),
        hα.reebReturnMap hc hfixS =
          hα.reebReturnMap hc
            (by rw [Flow.map_add, hfix, hk] : hα.reebFlow hc (k * T + T) x = x) := by
      rintro _ rfl _
      rfl
    rw [key hmul hadd, reebReturnMap_add hα hc hk hfix, ih, pow_succ]

/-- **Flowing along an orbit conjugates the linearized Reeb return map.** Moving the base point `x`
to `hα.reebFlow hc s x` conjugates `reebReturnMap` by `reebFlowKerEquiv`. -/
theorem reebFlowKerEquiv_conj_reebReturnMap (s : ℝ) {T : ℝ} {x : M}
    (hfix : hα.reebFlow hc T x = x) :
    (hα.reebFlowKerEquiv hc s x).conj (hα.reebReturnMap hc hfix) =
      hα.reebReturnMap hc (by rw [(hα.reebFlow hc).apply_comm, hfix] :
        hα.reebFlow hc T (hα.reebFlow hc s x) = hα.reebFlow hc s x) := by
  ext w
  simp only [LinearEquiv.conj_apply_apply, coe_reebReturnMap_apply, coe_reebFlowKerEquiv_apply]
  have hd_s : MDifferentiableAt I I (hα.reebFlow hc s) x :=
    ((hα.contMDiff_reebFlow_apply hc s) x).mdifferentiableAt (by simp)
  have hd_ns : MDifferentiableAt I I (hα.reebFlow hc (-s)) (hα.reebFlow hc s x) :=
    ((hα.contMDiff_reebFlow_apply hc (-s)) _).mdifferentiableAt (by simp)
  have hd_T : MDifferentiableAt I I (hα.reebFlow hc T) x :=
    ((hα.contMDiff_reebFlow_apply hc T) x).mdifferentiableAt (by simp)
  have hd_Tns : MDifferentiableAt I I (hα.reebFlow hc T ∘ hα.reebFlow hc (-s))
      (hα.reebFlow hc s x) :=
    ((hα.contMDiff_reebFlow_apply hc T).comp
      (hα.contMDiff_reebFlow_apply hc (-s)) _).mdifferentiableAt (by simp)
  have hcomm : hα.reebFlow hc s ∘ hα.reebFlow hc T ∘ hα.reebFlow hc (-s) =
      hα.reebFlow hc T := by
    funext y
    simp only [Function.comp_apply, ← Flow.map_add]
    congr 1
    ring
  have h1 := mfderiv_comp_apply_of_eq (hα.reebFlow hc s x) hd_s hd_Tns
    (by simp [(hα.reebFlow hc).map_neg_apply_map s x, hfix]) w
  have h2 := mfderiv_comp_apply_of_eq (hα.reebFlow hc s x) hd_T hd_ns
    ((hα.reebFlow hc).map_neg_apply_map s x) w
  rw [hcomm] at h1
  exact (h1.trans (by rw [h2]; rfl)).symm

/-- Moving the base point along a closed Reeb orbit preserves the characteristic polynomial of the
linearized Reeb return map on `ξ`. -/
theorem charpoly_reebReturnMap_reebFlow (s : ℝ) {T : ℝ} {x : M} (hfix : hα.reebFlow hc T x = x) :
    (hα.reebReturnMap hc (by rw [(hα.reebFlow hc).apply_comm, hfix] :
        hα.reebFlow hc T (hα.reebFlow hc s x) = hα.reebFlow hc s x)).charpoly =
      (hα.reebReturnMap hc hfix).charpoly := by
  rw [← hα.reebFlowKerEquiv_conj_reebReturnMap hc s hfix, LinearEquiv.charpoly_conj]

/-- Moving the base point along a closed Reeb orbit preserves the eigenvalues of the linearized
Reeb return map on `ξ`. -/
theorem hasEigenvalue_reebReturnMap_reebFlow_iff (s : ℝ) {T : ℝ} {x : M}
    (hfix : hα.reebFlow hc T x = x) (μ : ℝ) :
    (hα.reebReturnMap hc (by rw [(hα.reebFlow hc).apply_comm, hfix] :
        hα.reebFlow hc T (hα.reebFlow hc s x) = hα.reebFlow hc s x)).HasEigenvalue μ ↔
      (hα.reebReturnMap hc hfix).HasEigenvalue μ := by
  refine (Module.End.hasEigenvalue_iff_isRoot_charpoly _ μ).trans
    (Iff.trans ?_ (Module.End.hasEigenvalue_iff_isRoot_charpoly _ μ).symm)
  rw [charpoly_reebReturnMap_reebFlow]

/-! ### Comparison with Poincaré sections and monodromy -/

section SectionComparison

variable {g : M → ℝ} {T : ℝ} {x : M}

/-- The projection along `R_α(x)` gives a linear equivalence between the tangent space `ker dg_x`
of any transverse section at `x` and the contact hyperplane `ξ_x = ker α_x`. -/
def kerSectionEquivKerDistribution (hgv : mvfderiv I g x (α.reebVectorField x) ≠ 0) :
    LinearMap.ker (mvfderiv I g x : TangentSpace I x →ₗ[ℝ] ℝ) ≃ₗ[ℝ] α.kerDistribution x :=
  have hξ : IsCompl (α.kerDistribution x) (ℝ ∙ α.reebVectorField x) :=
    hα.isCompl_kerDistribution_span_reebVectorField x
  have hKg : IsCompl (LinearMap.ker (mvfderiv I g x : TangentSpace I x →ₗ[ℝ] ℝ))
      (ℝ ∙ α.reebVectorField x) :=
    ⟨Submodule.disjoint_span_singleton_of_notMem (LinearMap.mem_ker.not.2 hgv),
      codisjoint_iff.2 (by
        rw [sup_comm]
        exact LinearMap.span_singleton_sup_ker_eq_top _ hgv)⟩
  LinearEquiv.ofLinearMap
    ((α.kerDistribution x).projectionOnto (ℝ ∙ α.reebVectorField x) hξ ∘ₗ
      (LinearMap.ker (mvfderiv I g x : TangentSpace I x →ₗ[ℝ] ℝ)).subtype)
    ((LinearMap.ker (mvfderiv I g x : TangentSpace I x →ₗ[ℝ] ℝ)).projectionOnto
      (ℝ ∙ α.reebVectorField x) hKg ∘ₗ (α.kerDistribution x).subtype)
    (LinearMap.ext fun v ↦ by
      have hsub := Submodule.sub_projection_mem hKg (v : TangentSpace I x)
      rw [← Submodule.coe_projectionOnto_apply] at hsub
      have h0 : (α.kerDistribution x).projectionOnto (ℝ ∙ α.reebVectorField x) hξ
          ((v : TangentSpace I x) - ((LinearMap.ker (mvfderiv I g x :
            TangentSpace I x →ₗ[ℝ] ℝ)).projectionOnto (ℝ ∙ α.reebVectorField x) hKg
            (v : TangentSpace I x) : TangentSpace I x)) = 0 :=
        (Submodule.projectionOnto_apply_eq_zero_iff hξ).2 hsub
      rw [map_sub, sub_eq_zero] at h0
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, LinearMap.id_apply]
      rw [← h0, Submodule.projectionOnto_apply_of_mem_left hξ v.2])
    (LinearMap.ext fun v ↦ by
      have hsub := Submodule.sub_projection_mem hξ (v : TangentSpace I x)
      rw [← Submodule.coe_projectionOnto_apply] at hsub
      have h0 : (LinearMap.ker (mvfderiv I g x : TangentSpace I x →ₗ[ℝ] ℝ)).projectionOnto
          (ℝ ∙ α.reebVectorField x) hKg
          ((v : TangentSpace I x) - ((α.kerDistribution x).projectionOnto
            (ℝ ∙ α.reebVectorField x) hξ (v : TangentSpace I x) : TangentSpace I x)) = 0 :=
        (Submodule.projectionOnto_apply_eq_zero_iff hKg).2 hsub
      rw [map_sub, sub_eq_zero] at h0
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, LinearMap.id_apply]
      rw [← h0, Submodule.projectionOnto_apply_of_mem_left hKg v.2])

/-- **The linearized Reeb return map on `ξ` is conjugate to the normal return derivative.**
For any local transverse section `{g = g x}`, the projection along `R_α(x)` conjugates
`TauCeti.normalReturnDerivative` to `TauCeti.SmoothForm.IsContactForm.reebReturnMap`. -/
theorem kerSectionEquivKerDistribution_conj_normalReturnDerivative
    (hfix : hα.reebFlow hc T x = x) (hg : ContMDiffAt I 𝓘(ℝ) 1 g x)
    (hgv : mvfderiv I g x (α.reebVectorField x) ≠ 0)
    {h : LinearMap.range (returnDerivative α.reebVectorField g T x) ≤
      LinearMap.ker (mvfderiv I g x : TangentSpace I x →ₗ[ℝ] ℝ)} :
    (hα.kerSectionEquivKerDistribution hgv).conj
        (normalReturnDerivative α.reebVectorField g T x h) =
      hα.reebReturnMap hc hfix := by
  have hv : ContMDiff I I.tangent 1
      (fun y ↦ (⟨y, α.reebVectorField y⟩ : TangentBundle I M)) :=
    hα.contMDiff_reebVectorField.of_le (by simp)
  have hP : (T, x) ∈ flowDomain α.reebVectorField := hc.mem_flowDomain T x
  have hfx : flowOf α.reebVectorField T x = x := by
    rwa [← hα.reebFlow_eq_flowOf hc]
  have hξ : IsCompl (α.kerDistribution x) (ℝ ∙ α.reebVectorField x) :=
    hα.isCompl_kerDistribution_span_reebVectorField x
  have hKg : IsCompl (LinearMap.ker (mvfderiv I g x : TangentSpace I x →ₗ[ℝ] ℝ))
      (ℝ ∙ α.reebVectorField x) :=
    ⟨Submodule.disjoint_span_singleton_of_notMem (LinearMap.mem_ker.not.2 hgv),
      codisjoint_iff.2 (by rw [sup_comm]; exact LinearMap.span_singleton_sup_ker_eq_top _ hgv)⟩
  -- Apply both sides to `v ∈ ξ_x`, writing `v = w + c R_α(x)` with `w ∈ ker dg_x`.
  ext v
  let e : LinearMap.ker (mvfderiv I g x : TangentSpace I x →ₗ[ℝ] ℝ) ≃ₗ[ℝ]
      α.kerDistribution x := hα.kerSectionEquivKerDistribution hgv
  let w : LinearMap.ker (mvfderiv I g x : TangentSpace I x →ₗ[ℝ] ℝ) := e.symm v
  have hvw : (v : TangentSpace I x) - (w : TangentSpace I x) ∈ ℝ ∙ α.reebVectorField x := by
    change (v : TangentSpace I x) - ((LinearMap.ker (mvfderiv I g x : TangentSpace I x →ₗ[ℝ]
      ℝ)).projectionOnto (ℝ ∙ α.reebVectorField x) _ (v : TangentSpace I x) : TangentSpace I x) ∈
        ℝ ∙ α.reebVectorField x
    rw [Submodule.coe_projectionOnto_apply]
    exact Submodule.sub_projection_mem hKg (v : TangentSpace I x)
  obtain ⟨c, hcR⟩ := Submodule.mem_span_singleton.1 hvw
  have hform := mfderiv_flowTransition_apply hv hP (by rwa [hfx]) (by rwa [hfx]) w
  have hfl : flowOf α.reebVectorField T = hα.reebFlow hc T :=
    funext fun y ↦ (hα.reebFlow_eq_flowOf hc T y).symm
  rw [← hα.reebFlow_eq_flowOf hc T x, hfl] at hform
  -- By `mfderiv_reebFlow_apply_self`, `d(φ_T)_x (c R_α(x)) = c R_α(φ_T x)`.
  have hReeb0 : mfderiv I I (hα.reebFlow hc T) x (c • α.reebVectorField x) =
      c • α.reebVectorField (hα.reebFlow hc T x) := by
    rw [map_smul, hα.mfderiv_reebFlow_apply_self hc T x]
  have hwv : (w : TangentSpace I x) = (v : TangentSpace I x) - c • α.reebVectorField x := by
    rw [hcR]
    abel
  have h1 : mfderiv I I (hα.reebFlow hc T) x ↑w =
      mfderiv I I (hα.reebFlow hc T) x ↑v - c • α.reebVectorField (hα.reebFlow hc T x) := by
    rw [hwv, map_sub, hReeb0]
  have hdiff0 : @Eq E (normalReturnDerivative α.reebVectorField g T x h w : TangentSpace I x)
      ((mvfderiv I (flowHittingTime α.reebVectorField g T x) x w - c) • α.reebVectorField x +
        (hα.reebReturnMap hc hfix v : TangentSpace I x)) := by
    have hA : @Eq E (normalReturnDerivative α.reebVectorField g T x h w : TangentSpace I x)
        (mfderiv I I (flowTransition α.reebVectorField g T x) x ↑w) := by
      rw [coe_normalReturnDerivative_apply, returnDerivative_apply]
    have hB : @Eq E (mfderiv I I (flowTransition α.reebVectorField g T x) x ↑w)
        (mvfderiv I (flowHittingTime α.reebVectorField g T x) x ↑w •
            α.reebVectorField (hα.reebFlow hc T x) + mfderiv I I (hα.reebFlow hc T) x ↑w) :=
      hform
    have hC : @Eq E (mvfderiv I (flowHittingTime α.reebVectorField g T x) x ↑w •
            α.reebVectorField (hα.reebFlow hc T x) + mfderiv I I (hα.reebFlow hc T) x ↑w)
        ((mvfderiv I (flowHittingTime α.reebVectorField g T x) x w - c) •
            α.reebVectorField (hα.reebFlow hc T x) + mfderiv I I (hα.reebFlow hc T) x ↑v) := by
      rw [h1, sub_smul]
      abel
    have hD : @Eq E ((mvfderiv I (flowHittingTime α.reebVectorField g T x) x w - c) •
            α.reebVectorField (hα.reebFlow hc T x) + mfderiv I I (hα.reebFlow hc T) x ↑v)
        ((mvfderiv I (flowHittingTime α.reebVectorField g T x) x w - c) • α.reebVectorField x +
            (hα.reebReturnMap hc hfix v : TangentSpace I x)) :=
      congrArg₂ (· + ·) (show @Eq E _ _ by rw [hfix]) rfl
    exact hA.trans (hB.trans (hC.trans hD))
  have hdiff : (normalReturnDerivative α.reebVectorField g T x h w : TangentSpace I x) -
      (hα.reebReturnMap hc hfix v : TangentSpace I x) ∈ ℝ ∙ α.reebVectorField x := by
    rw [hdiff0, add_sub_cancel_right]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hproj := (Submodule.projectionOnto_apply_eq_zero_iff hξ).2 hdiff
  rw [map_sub, sub_eq_zero,
    Submodule.projectionOnto_apply_of_mem_left hξ (hα.reebReturnMap hc hfix v).2] at hproj
  simpa [e, kerSectionEquivKerDistribution, w] using congrArg Subtype.val hproj

/-- The characteristic polynomial of `reebReturnMap` agrees with that of
`normalReturnDerivative`. -/
theorem charpoly_reebReturnMap_eq_charpoly_normalReturnDerivative
    (hfix : hα.reebFlow hc T x = x) (hg : ContMDiffAt I 𝓘(ℝ) 1 g x)
    (hgv : mvfderiv I g x (α.reebVectorField x) ≠ 0)
    {h : LinearMap.range (returnDerivative α.reebVectorField g T x) ≤
      LinearMap.ker (mvfderiv I g x : TangentSpace I x →ₗ[ℝ] ℝ)} :
    (hα.reebReturnMap hc hfix).charpoly =
      (normalReturnDerivative α.reebVectorField g T x h).charpoly := by
  rw [← hα.kerSectionEquivKerDistribution_conj_normalReturnDerivative hc hfix hg hgv,
    LinearEquiv.charpoly_conj]

/-- `μ` is an eigenvalue of `reebReturnMap` on `ξ` if and only if it is an eigenvalue of
`normalReturnDerivative` on any transverse section. -/
theorem hasEigenvalue_reebReturnMap_iff_hasEigenvalue_normalReturnDerivative
    (hfix : hα.reebFlow hc T x = x) (hg : ContMDiffAt I 𝓘(ℝ) 1 g x)
    (hgv : mvfderiv I g x (α.reebVectorField x) ≠ 0)
    {h : LinearMap.range (returnDerivative α.reebVectorField g T x) ≤
      LinearMap.ker (mvfderiv I g x : TangentSpace I x →ₗ[ℝ] ℝ)} (μ : ℝ) :
    (hα.reebReturnMap hc hfix).HasEigenvalue μ ↔
      (normalReturnDerivative α.reebVectorField g T x h).HasEigenvalue μ := by
  refine (Module.End.hasEigenvalue_iff_isRoot_charpoly _ μ).trans
    (Iff.trans ?_ (Module.End.hasEigenvalue_iff_isRoot_charpoly _ μ).symm)
  rw [charpoly_reebReturnMap_eq_charpoly_normalReturnDerivative hα hc hfix hg hgv]

/-- For `μ ≠ 0` (in particular `μ = 1`), `μ` is an eigenvalue of `reebReturnMap` on `ξ` if and only
if it is an eigenvalue of `returnDerivative` for any transverse section. -/
theorem hasEigenvalue_reebReturnMap_iff_hasEigenvalue_returnDerivative
    (hfix : hα.reebFlow hc T x = x) (hg : ContMDiffAt I 𝓘(ℝ) 1 g x)
    (hgv : mvfderiv I g x (α.reebVectorField x) ≠ 0) {μ : ℝ} (hμ : μ ≠ 0) :
    (hα.reebReturnMap hc hfix).HasEigenvalue μ ↔
      (returnDerivative α.reebVectorField g T x).HasEigenvalue μ := by
  have hv : ContMDiff I I.tangent 1
      (fun y ↦ (⟨y, α.reebVectorField y⟩ : TangentBundle I M)) :=
    hα.contMDiff_reebVectorField.of_le (by simp)
  have hP : (T, x) ∈ flowDomain α.reebVectorField := hc.mem_flowDomain T x
  have hfx : flowOf α.reebVectorField T x = x := by
    rwa [← hα.reebFlow_eq_flowOf hc]
  have hR := range_returnDerivative_le_ker hv hP hfx hg hgv
  rw [hα.hasEigenvalue_reebReturnMap_iff_hasEigenvalue_normalReturnDerivative hc hfix hg hgv
      (h := hR),
    hasEigenvalue_normalReturnDerivative_iff hμ]

end SectionComparison

end ReturnMap

/-! ### Nondegenerate closed Reeb orbits and finiteness -/

section Nondegenerate

variable (hα : α.IsContactForm) (hc : IsCompleteVectorField α.reebVectorField)

include hα in
omit [I.Boundaryless] [T2Space M] hc in
/-- At any point `x` of a contact manifold, there exists a smooth function `g` with
`dg_x(R_α x) = 1`, whose level `{g = g x}` is a local section transverse to the Reeb vector
field. -/
theorem exists_transverseSection_at (x : M) :
    ∃ g : M → ℝ, ContMDiffAt I 𝓘(ℝ) ∞ g x ∧ mvfderiv I g x (α.reebVectorField x) = 1 := by
  let ℓ : E →L[ℝ] ℝ := degreeOneEquiv α x
  refine ⟨fun y ↦ ℓ (extChartAt I x y),
    ℓ.contDiff.contMDiff.contMDiffAt.comp x contMDiffAt_extChartAt, ?_⟩
  have hmd : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I x) x :=
    (contMDiffAt_extChartAt (I := I) (n := 1) (x := x)).mdifferentiableAt one_ne_zero
  change mvfderiv I (ℓ ∘ extChartAt I x) x (α.reebVectorField x) = 1
  rw [ℓ.mvfderiv_comp_apply hmd]
  have hchart : mvfderiv I (extChartAt I x) x (α.reebVectorField x) = α.reebVectorField x := by
    rw [mvfderiv, mfderiv_extChartAt_self]
    rfl
  rw [hchart]
  change degreeOneEquiv α x (α.reebVectorField x) = 1
  rw [degreeOneEquiv_apply_apply_vec]
  exact hα.apply_reebVectorField x

/-- A closed Reeb orbit `γ` is **nondegenerate** when `1` is not an eigenvalue of the linearized
Reeb return map restricted to `ξ = ker α` along any (equivalently, every) representative
trajectory. -/
def IsNondegenerateOrbit (γ : Flow.ClosedOrbit (hα.reebFlow hc)) : Prop :=
  ∀ c : Flow.PeriodicTrajectory (hα.reebFlow hc), Flow.ClosedOrbit.mk c = γ →
    ¬(hα.reebReturnMap hc c.apply_period).HasEigenvalue 1

/-- Nondegeneracy of a closed Reeb orbit can be tested on any representative trajectory. -/
theorem isNondegenerateOrbit_mk_iff (c : Flow.PeriodicTrajectory (hα.reebFlow hc)) :
    hα.IsNondegenerateOrbit hc (Flow.ClosedOrbit.mk c) ↔
      ¬(hα.reebReturnMap hc c.apply_period).HasEigenvalue 1 := by
  refine ⟨fun h ↦ h c rfl, fun h c' hc' ↦ ?_⟩
  obtain ⟨s, rfl⟩ := Flow.ClosedOrbit.mk_eq_mk_iff.1 hc'
  have h1 := hα.hasEigenvalue_reebReturnMap_reebFlow_iff hc s c.apply_period 1
  have key : ∀ {c'' : Flow.PeriodicTrajectory (hα.reebFlow hc)} (_ : c'' = s +ᵥ c),
      ¬(hα.reebReturnMap hc c''.apply_period).HasEigenvalue 1 := by
    rintro _ rfl h'
    exact h (h1.1 h')
  exact key rfl

/-- **Nondegeneracy of an iterate.** The `k`-fold iterate `γ.iterate k` of a closed Reeb orbit is
nondegenerate if and only if `1` is not an eigenvalue of the `k`-th power of the linearized Reeb
return map restricted to `ξ`. -/
theorem isNondegenerateOrbit_iterate_iff (c : Flow.PeriodicTrajectory (hα.reebFlow hc))
    (k : ℕ+) :
    hα.IsNondegenerateOrbit hc ((Flow.ClosedOrbit.mk c).iterate k) ↔
      ¬((hα.reebReturnMap hc c.apply_period) ^ (k : ℕ)).HasEigenvalue 1 := by
  rw [Flow.ClosedOrbit.iterate_mk, isNondegenerateOrbit_mk_iff]
  have key : ∀ {x : M} (_ : x = c.point) {S : ℝ} (_ : S = (k : ℕ) * c.period)
      (hfixS : hα.reebFlow hc S x = x),
      (hα.reebReturnMap hc hfixS).HasEigenvalue 1 ↔
        (hα.reebReturnMap hc c.apply_period ^ (k : ℕ)).HasEigenvalue 1 := by
    rintro _ rfl _ rfl hfixS
    rw [hα.reebReturnMap_natCast_mul hc c.apply_period k]
  rw [key (Flow.PeriodicTrajectory.point_iterate c k) (Flow.PeriodicTrajectory.period_iterate c k)]

/-- If an iterate `γ.iterate k` of a closed Reeb orbit is nondegenerate, then `γ` itself is
nondegenerate. -/
theorem isNondegenerateOrbit_of_iterate {γ : Flow.ClosedOrbit (hα.reebFlow hc)} {k : ℕ+}
    (hk : hα.IsNondegenerateOrbit hc (γ.iterate k)) :
    hα.IsNondegenerateOrbit hc γ := by
  induction γ using Flow.ClosedOrbit.ind with
  | h c =>
    rw [isNondegenerateOrbit_iterate_iff] at hk
    rw [isNondegenerateOrbit_mk_iff]
    intro h1
    apply hk
    obtain ⟨v, hv⟩ := h1.exists_hasEigenvector
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.2 (by simpa using hv.pow_apply (k : ℕ)), hv.2⟩

omit hc in
/-- **Finiteness of nondegenerate closed Reeb orbits below an action bound.** On a compact
boundaryless contact manifold, if every closed Reeb orbit of period at most `T` is nondegenerate,
then there are only finitely many closed Reeb orbits of period at most `T` (including covered
orbits). -/
theorem finite_closedOrbit_period_le [CompactSpace M] (T : ℝ)
    (hnd : ∀ γ : Flow.ClosedOrbit (hα.reebFlow (hα.isComplete_reebVectorField)),
      γ.period ≤ T → hα.IsNondegenerateOrbit (hα.isComplete_reebVectorField) γ) :
    {γ : Flow.ClosedOrbit (hα.reebFlow (hα.isComplete_reebVectorField)) | γ.period ≤ T}.Finite := by
  let hc' := hα.isComplete_reebVectorField
  obtain ⟨ε, hε, hbound⟩ := hα.exists_pos_period_le_closedOrbit
  by_cases hT : T < ε
  · have hempty :
        {γ : Flow.ClosedOrbit (hα.reebFlow hc') | γ.period ≤ T} = ∅ := by
      ext γ
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact hT.trans_le (hbound γ)
    rw [hempty]
    exact Set.finite_empty
  have hv : ContMDiff I I.tangent 1
      (fun y ↦ (⟨y, α.reebVectorField y⟩ : TangentBundle I M)) :=
    hα.contMDiff_reebVectorField.of_le (by simp)
  let S : Set (ℝ × M) := Icc ε T ×ˢ (univ : Set M)
  have hS : IsCompact S := isCompact_Icc.prod isCompact_univ
  have hSD : S ⊆ flowDomain α.reebVectorField := by
    rw [hc'.flowDomain_eq_univ]
    exact subset_univ _
  have hSnd : ∀ x ∈ S, flowOf α.reebVectorField x.1 x.2 = x.2 →
      ∃ g : M → ℝ, ContMDiffAt I 𝓘(ℝ) 1 g x.2 ∧
        mvfderiv I g x.2 (α.reebVectorField x.2) ≠ 0 ∧
        ¬(returnDerivative α.reebVectorField g x.1 x.2).HasEigenvalue 1 := by
    rintro ⟨t, p⟩ ⟨ht, -⟩ hp
    have ht0 : 0 < t := hε.trans_le ht.1
    have hfix : hα.reebFlow hc' t p = p := by
      rwa [hα.reebFlow_eq_flowOf hc']
    let c := hα.reebTrajectory hc' p ht0 hfix
    have hcnd := hnd (Flow.ClosedOrbit.mk c)
      (by simp only [Flow.ClosedOrbit.period_mk, period_reebTrajectory, c]; exact ht.2)
    rw [isNondegenerateOrbit_mk_iff] at hcnd
    obtain ⟨g, hg, hgv⟩ := hα.exists_transverseSection_at p
    have hgv0 : mvfderiv I g p (α.reebVectorField p) ≠ 0 := by rw [hgv]; exact one_ne_zero
    refine ⟨g, hg.of_le (by simp), hgv0, ?_⟩
    rwa [← hα.hasEigenvalue_reebReturnMap_iff_hasEigenvalue_returnDerivative hc' hfix
      (hg.of_le (by simp)) hgv0 one_ne_zero]
  obtain ⟨F, -, hF⟩ := exists_finset_forall_fst_eq_and_exists_flowOf_eq_snd hv hS hSD hSnd
  refine Set.Finite.of_finite_image (f := fun γ : Flow.ClosedOrbit (hα.reebFlow hc') ↦
      (γ.period, γ.support)) ?_ (fun γ₁ _ γ₂ _ h ↦ ?_)
  · refine ((F.finite_toSet.image fun y : ℝ × M ↦
        (y.1, (hα.reebFlow hc').orbit y.2))).subset ?_
    rintro _ ⟨γ, hγ, rfl⟩
    induction γ using Flow.ClosedOrbit.ind with
    | h c =>
      have hmem : (c.period, c.point) ∈ S :=
        ⟨⟨by simpa [Flow.ClosedOrbit.period_mk] using hbound (Flow.ClosedOrbit.mk c),
          by simpa [Flow.ClosedOrbit.period_mk] using hγ⟩, mem_univ _⟩
      have hfix : flowOf α.reebVectorField c.period c.point = c.point := by
        rw [← hα.reebFlow_eq_flowOf hc']
        exact c.apply_period
      obtain ⟨y, hyF, hfst, s, -, hs⟩ := hF (c.period, c.point) hmem hfix
      refine ⟨y, hyF, Prod.ext ?_ ?_⟩
      · simpa [Flow.ClosedOrbit.period_mk] using hfst.symm
      · simp only [Flow.ClosedOrbit.support_mk]
        dsimp only at hs
        rw [← hα.reebFlow_eq_flowOf hc'] at hs
        rw [← hs, Flow.orbit_apply]
  · exact Flow.ClosedOrbit.ext (congrArg Prod.snd h) (congrArg Prod.fst h)

omit hc in
/-- **Finiteness of primitive nondegenerate closed Reeb orbits below an action bound.** -/
theorem finite_primitive_closedOrbit_period_le [CompactSpace M] (T : ℝ)
    (hnd : ∀ γ : Flow.ClosedOrbit (hα.reebFlow (hα.isComplete_reebVectorField)),
      γ.period ≤ T → hα.IsNondegenerateOrbit (hα.isComplete_reebVectorField) γ) :
    {γ : Flow.ClosedOrbit (hα.reebFlow (hα.isComplete_reebVectorField)) |
      γ.IsPrimitive ∧ γ.period ≤ T}.Finite :=
  (hα.finite_closedOrbit_period_le T hnd).subset fun _ h ↦ h.2

end Nondegenerate

end IsContactForm

end TauCeti.SmoothForm
