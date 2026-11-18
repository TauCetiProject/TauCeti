/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Flow.ClosedOrbit
public import TauCeti.Geometry.Contact.Flow
public import TauCeti.Geometry.Manifold.Flow.ClosedOrbit
public import TauCeti.Geometry.Manifold.Flow.Monodromy
import TauCeti.Geometry.Contact.PeriodBound
import TauCeti.Geometry.Manifold.Flow.NondegenerateOrbit

/-!
# Closed Reeb orbits, linearized return maps and finiteness

Let `α` be a contact form on a finite-dimensional boundaryless manifold `M`. When its Reeb vector
field `R_α` is complete (which holds automatically when `M` is compact, by
`TauCeti.SmoothForm.IsContactForm.isCompleteVectorField_reebVectorField`), its maximal integral
curves assemble into the global Reeb flow `TauCeti.SmoothForm.IsContactForm.reebFlow`. Since `R_α`
vanishes nowhere, every periodic integral curve has no rest points and defines a periodic
trajectory and a closed Reeb orbit (`Flow.PeriodicTrajectory` and `Flow.ClosedOrbit` of `reebFlow`).

Let `γ` be a closed Reeb orbit of period `T = κ · T₀` over a primitive orbit of minimal period
`T₀`, with covering multiplicity `κ = γ.multiplicity`, and let `c` be a representative periodic
trajectory of `γ`. Its circle parametrization `c.circleMap` (`Flow.PeriodicTrajectory.circleMap`)
is smooth (`TauCeti.SmoothForm.IsContactForm.contMDiff_circleMap`) and differentiable at every `θ`
with velocity `R_α` (`TauCeti.SmoothForm.IsContactForm.hasMFDerivAt_circleMap`), while the finite
reparametrization group `ZMod κ` (`Flow.ClosedOrbit.reparamGroup`) permutes the `κ` asymptotic
markers `{θ : AddCircle c.period | c.circleMap θ = x}` above any point `x` on the orbit simply
transitively.

Even without global completeness, wherever the maximal Reeb flow
`φ = TauCeti.flowOf α.reebVectorField` is defined, its differential preserves the contact
hyperplane `ξ = ker α` and the two-form `dα`
(`TauCeti.SmoothForm.IsContactForm.flowOfKerEquiv`). At a local periodic point `x` with
`φ_T x = x`, restricting `d(φ_T)_x` to `ξ_x` defines the **linearized Reeb return map**
`TauCeti.SmoothForm.IsContactForm.reebReturnMap` (packaged as a linear automorphism in
`TauCeti.SmoothForm.IsContactForm.reebReturnEquiv`), which preserves `dα_x|_ξ`
(`TauCeti.SmoothForm.IsContactForm.mextDeriv_reebReturnMap`). Iterating the period raises
`reebReturnMap` to the corresponding power
(`TauCeti.SmoothForm.IsContactForm.reebReturnMap_natCast_mul`), and moving along the orbit
conjugates `reebReturnMap` (`TauCeti.SmoothForm.IsContactForm.flowOfKerEquiv_conj_reebReturnMap`).
For any local transverse section `{g = g x}`, the projection onto `ξ_x` along `R_α(x)`
(`TauCeti.SmoothForm.IsContactForm.kerSectionEquivKerDistribution`) conjugates the normal return
derivative `TauCeti.normalReturnDerivative` to `reebReturnMap`
(`TauCeti.SmoothForm.IsContactForm.kerSectionEquivKerDistribution_conj_normalReturnDerivative`),
so `1` is an eigenvalue of `reebReturnMap` if and only if `1` is an eigenvalue of
`TauCeti.returnDerivative`.

A closed Reeb orbit `γ` is **nondegenerate**
(`TauCeti.SmoothForm.IsContactForm.IsNondegenerateOrbit`) when `1` is not an eigenvalue of
`reebReturnMap`; an iterate `γ.iterate k` is nondegenerate precisely when `1` is not an eigenvalue
of the `k`-th power of `reebReturnMap`
(`TauCeti.SmoothForm.IsContactForm.isNondegenerateOrbit_iterate_iff`). Since `α(R_α) = 1`, the
contact action `∫_γ α` of a closed Reeb orbit equals its period. On a compact boundaryless contact
manifold, combining the uniform positive lower bound for Reeb periods
(`TauCeti.SmoothForm.IsContactForm.exists_pos_period_le_closedOrbit`) with isolation of
nondegenerate closed orbits in a compact period window shows that whenever *every* closed Reeb
orbit (including covered orbits) of period at most `T` is nondegenerate, there are only finitely
many closed Reeb orbits—and in particular only finitely many primitive closed Reeb orbits—of period
at most `T` (`TauCeti.SmoothForm.IsContactForm.finite_setOf_closedOrbit_period_le`,
`TauCeti.SmoothForm.IsContactForm.finite_setOf_closedOrbit_isPrimitive_and_period_le`).

## Main definitions

* `TauCeti.SmoothForm.IsContactForm.reebTrajectory`: a periodic Reeb trajectory from a base point
  and positive return time.
* `TauCeti.SmoothForm.IsContactForm.reebTrajectoryOfIntegralCurve`: a periodic Reeb trajectory from
  a periodic integral curve of `R_α`.
* `TauCeti.SmoothForm.IsContactForm.reebReturnMap`: the local linearized Reeb return map restricted
  to `ξ = α.kerDistribution`.
* `TauCeti.SmoothForm.IsContactForm.reebReturnEquiv`: `reebReturnMap` packaged as a linear
  automorphism of `ξ_x`, with inverse given by the return map at `-T`.
* `TauCeti.SmoothForm.IsContactForm.IsNondegenerateOrbit`: nondegeneracy of a closed Reeb orbit.

## Main results

* `TauCeti.SmoothForm.IsContactForm.contMDiff_circleMap`,
  `TauCeti.SmoothForm.IsContactForm.hasMFDerivAt_circleMap`: the circle parametrization of a
  periodic Reeb trajectory is smooth and differentiable at every `θ` with velocity `R_α`.
* `TauCeti.SmoothForm.IsContactForm.mextDeriv_reebReturnMap`: the linearized return map preserves
  `dα` on `ξ`.
* `TauCeti.SmoothForm.IsContactForm.reebReturnMap_natCast_mul`: the linearized return map of a
  `k`-fold iterate is the `k`-th power of the linearized return map.
* `TauCeti.SmoothForm.IsContactForm.charpoly_mfderiv_flowOf_reebVectorField_eq_X_sub_one_mul`:
  the characteristic polynomial of `d(φ_T)_x` splits as `(X - 1)` times that of `reebReturnMap`.
* `TauCeti.SmoothForm.IsContactForm.kerSectionEquivKerDistribution_conj_normalReturnDerivative`:
  for any local transverse section, `reebReturnMap` is conjugate to `normalReturnDerivative`.
* `TauCeti.SmoothForm.IsContactForm.hasEigenvalue_reebReturnMap_iff_hasEigenvalue_returnDerivative`:
  any nonzero `μ` (in particular `1`) is an eigenvalue of `reebReturnMap` iff it is an eigenvalue
  of `returnDerivative`.
* `TauCeti.SmoothForm.IsContactForm.isNondegenerateOrbit_iterate_iff`: nondegeneracy of the
  `k`-fold cover in terms of the `k`-th power of `reebReturnMap`.
* `TauCeti.SmoothForm.IsContactForm.finite_setOf_closedOrbit_period_le`,
  `TauCeti.SmoothForm.IsContactForm.finite_setOf_closedOrbit_isPrimitive_and_period_le`: finiteness
  of closed (and primitive closed) Reeb orbits of period at most `T` when every closed Reeb orbit
  of period at most `T` is nondegenerate.

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
open scoped ContDiff Manifold Polynomial

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {α : SmoothForm I M ℝ 1}

namespace IsContactForm

/-! ### Periodic Reeb trajectories -/

section PeriodicTrajectories

variable (hα : α.IsContactForm) (hc : IsCompleteVectorField α.reebVectorField)

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

/-- Evaluating the circle parametrization of `reebTrajectory` at `(t : ℝ)` gives the Reeb flow at
time `t`. (`Flow.PeriodicTrajectory.circleMap_coe` already simplifies the left-hand side.) -/
theorem circleMap_reebTrajectory_coe (x : M) {T : ℝ} (hT : 0 < T)
    (hfix : hα.reebFlow hc T x = x) (t : ℝ) :
    (hα.reebTrajectory hc x hT hfix).circleMap t = hα.reebFlow hc t x :=
  Flow.PeriodicTrajectory.circleMap_coe _ t

/-- Construct a periodic Reeb trajectory from a periodic integral curve of `α.reebVectorField`. -/
def reebTrajectoryOfIntegralCurve {γ : ℝ → M} (hγ : IsMIntegralCurve γ α.reebVectorField)
    {T : ℝ} (hT : 0 < T) (hper : Function.Periodic γ T) :
    Flow.PeriodicTrajectory (hα.reebFlow hc) :=
  hα.reebTrajectory hc (γ 0) hT (by
    rw [hα.reebFlow_eq_of_isMIntegralCurve hc hγ T]
    simpa using hper 0)

/-- Unfolds `reebTrajectoryOfIntegralCurve` in terms of `reebTrajectory` at base point `γ 0`. -/
theorem reebTrajectoryOfIntegralCurve_def {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ α.reebVectorField) {T : ℝ} (hT : 0 < T)
    (hper : Function.Periodic γ T) :
    hα.reebTrajectoryOfIntegralCurve hc hγ hT hper =
      hα.reebTrajectory hc (γ 0) hT (by
        rw [hα.reebFlow_eq_of_isMIntegralCurve hc hγ T]
        simpa using hper 0) :=
  (rfl)

@[simp]
theorem point_reebTrajectoryOfIntegralCurve {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ α.reebVectorField) {T : ℝ} (hT : 0 < T)
    (hper : Function.Periodic γ T) :
    (hα.reebTrajectoryOfIntegralCurve hc hγ hT hper).point = γ 0 :=
  (rfl)

@[simp]
theorem period_reebTrajectoryOfIntegralCurve {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ α.reebVectorField) {T : ℝ} (hT : 0 < T)
    (hper : Function.Periodic γ T) :
    (hα.reebTrajectoryOfIntegralCurve hc hγ hT hper).period = T :=
  (rfl)

/-- Evaluating the circle parametrization of `reebTrajectoryOfIntegralCurve` at `(t : ℝ)` recovers
`γ t`. (`Flow.PeriodicTrajectory.circleMap_coe` already simplifies the left-hand side.) -/
theorem circleMap_reebTrajectoryOfIntegralCurve_coe {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ α.reebVectorField) {T : ℝ} (hT : 0 < T)
    (hper : Function.Periodic γ T) (t : ℝ) :
    (hα.reebTrajectoryOfIntegralCurve hc hγ hT hper).circleMap t = γ t := by
  rw [reebTrajectoryOfIntegralCurve, circleMap_reebTrajectory_coe,
    hα.reebFlow_eq_of_isMIntegralCurve hc hγ t]

/-- The circle parametrization `AddCircle c.period → M` of a periodic Reeb trajectory is smooth. -/
theorem contMDiff_circleMap (c : Flow.PeriodicTrajectory (hα.reebFlow hc)) :
    ContMDiff 𝓘(ℝ) I ∞ c.circleMap := by
  revert c
  rw [hα.reebFlow_def hc]
  exact contMDiff_circleMap_globalFlow hc le_top hα.contMDiff_reebVectorField

/-- The circle parametrization `AddCircle c.period → M` of a periodic Reeb trajectory is
differentiable at `θ` with velocity `R_α`. -/
theorem hasMFDerivAt_circleMap (c : Flow.PeriodicTrajectory (hα.reebFlow hc))
    (θ : AddCircle c.period) :
    HasMFDerivAt 𝓘(ℝ) I c.circleMap θ
      ((1 : ℝ →L[ℝ] ℝ).smulRight (α.reebVectorField (c.circleMap θ))) := by
  revert c θ
  rw [hα.reebFlow_def hc]
  exact hasMFDerivAt_circleMap_globalFlow _ hc

end PeriodicTrajectories

/-! ### The local linearized Reeb return map on `ξ = ker α` -/

section ReturnMap

variable (hα : α.IsContactForm)

/-- The **linearized Reeb return map** at a periodic point `x` of period `T`: the restriction of
`d(φ_T)_x` (for `φ = TauCeti.flowOf α.reebVectorField`) to the contact hyperplane
`ξ_x = ker α_x`. -/
def reebReturnMap {T : ℝ} {x : M} (hT : (T, x) ∈ flowDomain α.reebVectorField)
    (hfix : flowOf α.reebVectorField T x = x) :
    Module.End ℝ (α.kerDistribution x) :=
  -- `TangentSpace I (flowOf α.reebVectorField T x)` and `TangentSpace I x` are both definitionally
  -- the model space `E`, matching `TauCeti.returnDerivative`.
  (show TangentSpace I x →L[ℝ] TangentSpace I x from
      mfderiv I I (flowOf α.reebVectorField T) x).toLinearMap.restrict fun _ hv ↦ by
    have hmem := hα.mfderiv_flowOf_reebVectorField_mem_kerDistribution hT hv
    rwa [hfix] at hmem

@[simp]
theorem coe_reebReturnMap_apply {T : ℝ} {x : M} (hT : (T, x) ∈ flowDomain α.reebVectorField)
    (hfix : flowOf α.reebVectorField T x = x) (v : α.kerDistribution x) :
    (hα.reebReturnMap hT hfix v : TangentSpace I x) =
      mfderiv I I (flowOf α.reebVectorField T) x v :=
  (rfl)

/-- `reebReturnMap` depends only on the return time and base point, not on the domain or
periodicity proofs, and respects equalities of the return time. -/
theorem reebReturnMap_congr {T₁ T₂ : ℝ} {x : M} (hT : T₁ = T₂)
    (hT₁ : (T₁, x) ∈ flowDomain α.reebVectorField)
    (hfix₁ : flowOf α.reebVectorField T₁ x = x)
    (hT₂ : (T₂, x) ∈ flowDomain α.reebVectorField)
    (hfix₂ : flowOf α.reebVectorField T₂ x = x) :
    hα.reebReturnMap hT₁ hfix₁ = hα.reebReturnMap hT₂ hfix₂ := by
  subst hT
  rfl

/-- The characteristic polynomial of `reebReturnMap` respects equalities of both the return time
and the base point. -/
theorem charpoly_reebReturnMap_congr {T₁ T₂ : ℝ} {x₁ x₂ : M} (hT : T₁ = T₂) (hx : x₁ = x₂)
    (hT₁ : (T₁, x₁) ∈ flowDomain α.reebVectorField)
    (hfix₁ : flowOf α.reebVectorField T₁ x₁ = x₁)
    (hT₂ : (T₂, x₂) ∈ flowDomain α.reebVectorField)
    (hfix₂ : flowOf α.reebVectorField T₂ x₂ = x₂) :
    (hα.reebReturnMap hT₁ hfix₁).charpoly = (hα.reebReturnMap hT₂ hfix₂).charpoly := by
  subst hT hx
  rfl

/-- Eigenvalues of `reebReturnMap` respect equalities of both the return time and the base
point. -/
theorem hasEigenvalue_reebReturnMap_congr_iff {T₁ T₂ : ℝ} {x₁ x₂ : M}
    (hT : T₁ = T₂) (hx : x₁ = x₂)
    (hT₁ : (T₁, x₁) ∈ flowDomain α.reebVectorField)
    (hfix₁ : flowOf α.reebVectorField T₁ x₁ = x₁)
    (hT₂ : (T₂, x₂) ∈ flowDomain α.reebVectorField)
    (hfix₂ : flowOf α.reebVectorField T₂ x₂ = x₂) (μ : ℝ) :
    (hα.reebReturnMap hT₁ hfix₁).HasEigenvalue μ ↔
      (hα.reebReturnMap hT₂ hfix₂).HasEigenvalue μ := by
  subst hT hx
  rfl

/-- The linearized Reeb return map preserves `dα_x` on `ξ_x`. -/
theorem mextDeriv_reebReturnMap {T : ℝ} {x : M} (hT : (T, x) ∈ flowDomain α.reebVectorField)
    (hfix : flowOf α.reebVectorField T x = x) (v w : α.kerDistribution x) :
    mextDeriv α.1 x ![hα.reebReturnMap hT hfix v, hα.reebReturnMap hT hfix w] =
      mextDeriv α.1 x ![v, w] := by
  simp only [coe_reebReturnMap_apply]
  have h := hα.mextDeriv_mfderiv_flowOf_reebVectorField hT v w
  -- `TangentSpace I y` and `TangentSpace I x` are both definitionally `E`, so rewriting `y = x`
  -- is well typed once abstracted over the base point.
  have key : ∀ {y : M} (_ : y = x) (a b : TangentSpace I y) (a' b' : TangentSpace I x),
      a = a' → b = b' → mextDeriv α.1 y ![a, b] = mextDeriv α.1 x ![a', b'] := by
    rintro y rfl a b _ _ rfl rfl
    rfl
  exact (key hfix _ _ _ _ rfl rfl).symm.trans h

/-- The linearized Reeb return map at time `0` is the identity on `ξ_x`. -/
@[simp]
theorem reebReturnMap_zero {x : M} (h0 : ((0 : ℝ), x) ∈ flowDomain α.reebVectorField)
    (hfix : flowOf α.reebVectorField 0 x = x) :
    hα.reebReturnMap h0 hfix = 1 := by
  ext v
  simp only [coe_reebReturnMap_apply, one_apply_eq_self]
  exact mfderiv_flowOf_zero_apply_eq_self x (v : TangentSpace I x)

/-- The linearized Reeb return map of a sum of return times is the composite of the return maps. -/
theorem reebReturnMap_add {T₁ T₂ : ℝ} {x : M}
    (hT₁ : (T₁, x) ∈ flowDomain α.reebVectorField)
    (hfix₁ : flowOf α.reebVectorField T₁ x = x)
    (hT₂ : (T₂, x) ∈ flowDomain α.reebVectorField)
    (hfix₂ : flowOf α.reebVectorField T₂ x = x)
    {hT₁₂ : (T₁ + T₂, x) ∈ flowDomain α.reebVectorField}
    {hfix₁₂ : flowOf α.reebVectorField (T₁ + T₂) x = x} :
    hα.reebReturnMap hT₁₂ hfix₁₂ =
      hα.reebReturnMap hT₁ hfix₁ * hα.reebReturnMap hT₂ hfix₂ := by
  have hv1 : ContMDiff I I.tangent 1 (fun y ↦ (⟨y, α.reebVectorField y⟩ : TangentBundle I M)) :=
    hα.contMDiff_reebVectorField.of_le (by simp)
  ext v
  simp only [coe_reebReturnMap_apply, mul_apply_eq_comp]
  have hcomm : @Eq E (mfderiv I I (flowOf α.reebVectorField (T₁ + T₂)) x v)
      (mfderiv I I (flowOf α.reebVectorField (T₂ + T₁)) x v) :=
    congrArg (fun f : M → M ↦ (mfderiv I I f x (v : TangentSpace I x) : E)) (by rw [add_comm])
  exact hcomm.trans (mfderiv_flowOf_add_apply_of_eq hv1 hT₂ hT₁ hfix₂ (v : TangentSpace I x))

private theorem reebReturnMap_mul_eq_one_of_add_eq_zero {T₁ T₂ : ℝ} {x : M} (h0 : T₁ + T₂ = 0)
    (hT₁ : (T₁, x) ∈ flowDomain α.reebVectorField)
    (hfix₁ : flowOf α.reebVectorField T₁ x = x)
    (hT₂ : (T₂, x) ∈ flowDomain α.reebVectorField)
    (hfix₂ : flowOf α.reebVectorField T₂ x = x) :
    hα.reebReturnMap hT₁ hfix₁ * hα.reebReturnMap hT₂ hfix₂ = 1 := by
  have hv1 := hα.contMDiff_reebVectorField.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)
  have hd : (T₁ + T₂, x) ∈ flowDomain α.reebVectorField := h0 ▸ mem_flowDomain_zero hv1 x
  have hf : flowOf α.reebVectorField (T₁ + T₂) x = x := h0 ▸ flowOf_zero α.reebVectorField x
  rw [← hα.reebReturnMap_add hT₁ hfix₁ hT₂ hfix₂ (hT₁₂ := hd) (hfix₁₂ := hf),
    hα.reebReturnMap_congr h0 hd hf (mem_flowDomain_zero hv1 x) (flowOf_zero _ x),
    hα.reebReturnMap_zero]

/-- The linearized Reeb return map at a periodic point packaged as a linear automorphism of `ξ_x`,
with inverse given by the linearized return map at `-T`. -/
def reebReturnEquiv {T : ℝ} {x : M} (hT : (T, x) ∈ flowDomain α.reebVectorField)
    (hfix : flowOf α.reebVectorField T x = x) :
    α.kerDistribution x ≃ₗ[ℝ] α.kerDistribution x :=
  let hv1 := hα.contMDiff_reebVectorField.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)
  let hnt : (-T, x) ∈ flowDomain α.reebVectorField := hfix ▸ neg_mem_flowDomain_flowOf hv1 hT
  let hfix_neg : flowOf α.reebVectorField (-T) x = x := by
    nth_rw 1 [← hfix]
    exact flowOf_neg_flowOf hv1 hT
  LinearEquiv.ofLinearMap (hα.reebReturnMap hT hfix) (hα.reebReturnMap hnt hfix_neg)
    (hα.reebReturnMap_mul_eq_one_of_add_eq_zero (add_neg_cancel T) hT hfix hnt hfix_neg)
    (hα.reebReturnMap_mul_eq_one_of_add_eq_zero (neg_add_cancel T) hnt hfix_neg hT hfix)

@[simp]
theorem reebReturnEquiv_apply {T : ℝ} {x : M} (hT : (T, x) ∈ flowDomain α.reebVectorField)
    (hfix : flowOf α.reebVectorField T x = x) (v : α.kerDistribution x) :
    hα.reebReturnEquiv hT hfix v = hα.reebReturnMap hT hfix v :=
  (rfl)

/-- The underlying linear map of `reebReturnEquiv` is `reebReturnMap`. -/
theorem toLinearMap_reebReturnEquiv {T : ℝ} {x : M} (hT : (T, x) ∈ flowDomain α.reebVectorField)
    (hfix : flowOf α.reebVectorField T x = x) :
    (hα.reebReturnEquiv hT hfix).toLinearMap = hα.reebReturnMap hT hfix :=
  (rfl)

/-- The inverse of `reebReturnEquiv` acts as `mfderiv I I (flowOf α.reebVectorField (-T)) x`. -/
@[simp]
theorem coe_reebReturnEquiv_symm_apply {T : ℝ} {x : M}
    (hT : (T, x) ∈ flowDomain α.reebVectorField)
    (hfix : flowOf α.reebVectorField T x = x) (v : α.kerDistribution x) :
    ((hα.reebReturnEquiv hT hfix).symm v : TangentSpace I x) =
      mfderiv I I (flowOf α.reebVectorField (-T)) x v :=
  (rfl)

/-- The underlying linear map of `(reebReturnEquiv ...).symm` is `reebReturnMap` at period `-T`. -/
theorem toLinearMap_reebReturnEquiv_symm {T : ℝ} {x : M}
    (hT : (T, x) ∈ flowDomain α.reebVectorField)
    (hfix : flowOf α.reebVectorField T x = x)
    {hnt : (-T, x) ∈ flowDomain α.reebVectorField}
    {hfix_neg : flowOf α.reebVectorField (-T) x = x} :
    (hα.reebReturnEquiv hT hfix).symm.toLinearMap = hα.reebReturnMap hnt hfix_neg :=
  (rfl)

/-- The linearized Reeb return map at any periodic point is bijective. -/
theorem reebReturnMap_bijective {T : ℝ} {x : M} (hT : (T, x) ∈ flowDomain α.reebVectorField)
    (hfix : flowOf α.reebVectorField T x = x) :
    Function.Bijective (hα.reebReturnMap hT hfix) :=
  (hα.reebReturnEquiv hT hfix).bijective

/-- **The linearized Reeb return map of an iterate is the iterate of the linearized return map.**
At a periodic point `x` of period `T`, the linearized return map at period `k * T` on `ξ_x` is the
`k`-th power of the linearized return map at period `T`. -/
theorem reebReturnMap_natCast_mul {T : ℝ} {x : M} (hT : (T, x) ∈ flowDomain α.reebVectorField)
    (hfix : flowOf α.reebVectorField T x = x) (k : ℕ)
    {hkT : ((k : ℝ) * T, x) ∈ flowDomain α.reebVectorField}
    {hfix_k : flowOf α.reebVectorField ((k : ℝ) * T) x = x} :
    hα.reebReturnMap hkT hfix_k = hα.reebReturnMap hT hfix ^ k := by
  have hv1 := hα.contMDiff_reebVectorField.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)
  induction k with
  | zero =>
    rw [pow_zero, hα.reebReturnMap_congr (by simp) hkT hfix_k
      (mem_flowDomain_zero hv1 x) (flowOf_zero _ x), hα.reebReturnMap_zero]
  | succ k ih =>
    obtain ⟨hk, hfk⟩ := flowOf_natCast_mul_of_flowOf_eq hv1 hT hfix k
    obtain ⟨hadd, hfadd⟩ := flowOf_add hv1 hk (hfk.symm ▸ hT)
    rw [hfk, hfix] at hfadd
    rw [hα.reebReturnMap_congr (by push_cast; ring) hkT hfix_k hadd hfadd.symm,
      hα.reebReturnMap_add hk hfk hT hfix, ih, pow_succ]

/-- **Flowing along an orbit conjugates the linearized Reeb return map.** Whenever `flowOf` is
defined at `(s, x)` and `x` has period `T`, moving the base point `x` to
`flowOf α.reebVectorField s x` conjugates `reebReturnMap` by `flowOfKerEquiv`. -/
theorem flowOfKerEquiv_conj_reebReturnMap {s T : ℝ} {x : M}
    (hs : (s, x) ∈ flowDomain α.reebVectorField)
    (hT : (T, x) ∈ flowDomain α.reebVectorField)
    (hfix : flowOf α.reebVectorField T x = x)
    {hTs : (T, flowOf α.reebVectorField s x) ∈ flowDomain α.reebVectorField}
    {hfix_s : flowOf α.reebVectorField T (flowOf α.reebVectorField s x) =
      flowOf α.reebVectorField s x} :
    (hα.flowOfKerEquiv hs).conj (hα.reebReturnMap hT hfix) =
      hα.reebReturnMap hTs hfix_s := by
  have hv1 : ContMDiff I I.tangent 1 (fun z ↦ (⟨z, α.reebVectorField z⟩ : TangentBundle I M)) :=
    hα.contMDiff_reebVectorField.of_le (by simp)
  set y := flowOf α.reebVectorField s x
  have hns : (-s, y) ∈ flowDomain α.reebVectorField := neg_mem_flowDomain_flowOf hv1 hs
  have hns_eq : flowOf α.reebVectorField (-s) y = x := flowOf_neg_flowOf hv1 hs
  obtain ⟨hnsT, hf_nsT⟩ := flowOf_add hv1 hns (hns_eq.symm ▸ hT)
  rw [hns_eq, hfix] at hf_nsT
  ext w
  simp only [LinearEquiv.conj_apply_apply, coe_flowOfKerEquiv_apply, coe_reebReturnMap_apply,
    coe_flowOfKerEquiv_symm_apply]
  have h1 := mfderiv_flowOf_add_apply_of_eq hv1 hns hT hns_eq (w : TangentSpace I y)
  have h2 := mfderiv_flowOf_add_apply_of_eq hv1 hnsT hs hf_nsT.symm (w : TangentSpace I y)
  have h3 : @Eq E (mfderiv I I (flowOf α.reebVectorField T) y w)
      (mfderiv I I (flowOf α.reebVectorField ((-s + T) + s)) y w) :=
    congrArg (fun f : M → M ↦ (mfderiv I I f y (w : TangentSpace I y) : E)) (by congr 1; ring)
  exact (h3.trans (h2.trans (congrArg (mfderiv I I (flowOf α.reebVectorField s) x) h1))).symm

/-- Moving the base point along a closed Reeb orbit preserves the characteristic polynomial of the
linearized Reeb return map on `ξ`. -/
theorem charpoly_reebReturnMap_flowOf {s T : ℝ} {x : M}
    (hs : (s, x) ∈ flowDomain α.reebVectorField)
    (hT : (T, x) ∈ flowDomain α.reebVectorField)
    (hfix : flowOf α.reebVectorField T x = x)
    {hTs : (T, flowOf α.reebVectorField s x) ∈ flowDomain α.reebVectorField}
    {hfix_s : flowOf α.reebVectorField T (flowOf α.reebVectorField s x) =
      flowOf α.reebVectorField s x} :
    (hα.reebReturnMap hTs hfix_s).charpoly = (hα.reebReturnMap hT hfix).charpoly := by
  rw [← hα.flowOfKerEquiv_conj_reebReturnMap hs hT hfix, LinearEquiv.charpoly_conj]

/-- Moving the base point along a closed Reeb orbit preserves the eigenvalues of the linearized
Reeb return map on `ξ`. -/
theorem hasEigenvalue_reebReturnMap_flowOf_iff {s T : ℝ} {x : M}
    (hs : (s, x) ∈ flowDomain α.reebVectorField)
    (hT : (T, x) ∈ flowDomain α.reebVectorField)
    (hfix : flowOf α.reebVectorField T x = x)
    {hTs : (T, flowOf α.reebVectorField s x) ∈ flowDomain α.reebVectorField}
    {hfix_s : flowOf α.reebVectorField T (flowOf α.reebVectorField s x) =
      flowOf α.reebVectorField s x} (μ : ℝ) :
    (hα.reebReturnMap hTs hfix_s).HasEigenvalue μ ↔
      (hα.reebReturnMap hT hfix).HasEigenvalue μ := by
  simp only [Module.End.hasEigenvalue_iff_isRoot_charpoly,
    hα.charpoly_reebReturnMap_flowOf hs hT hfix]

/-- At a periodic point `x` of period `T`, the characteristic polynomial of the full tangent
monodromy `d(φ_T)_x` splits as `(X - 1)` times the characteristic polynomial of `reebReturnMap` on
`ξ_x`. -/
theorem charpoly_mfderiv_flowOf_reebVectorField_eq_X_sub_one_mul {T : ℝ} {x : M}
    (hT : (T, x) ∈ flowDomain α.reebVectorField)
    (hfix : flowOf α.reebVectorField T x = x) :
    (mfderiv I I (flowOf α.reebVectorField T) x).toLinearMap.charpoly =
      (Polynomial.X - 1) * (hα.reebReturnMap hT hfix).charpoly :=
  charpoly_mfderiv_flowOf_eq_X_sub_one_mul_of_isCompl
    (hα.contMDiff_reebVectorField.of_le (by simp)) hT hfix
    (hα.reebVectorField_ne_zero x)
    (hα.isCompl_kerDistribution_span_reebVectorField x)
    (hα.coe_reebReturnMap_apply hT hfix)

/-! ### Comparison with Poincaré sections and monodromy -/

section SectionComparison

variable {g : M → ℝ} {T : ℝ} {x : M}

/-- **The linearized Reeb return map on `ξ` is conjugate to the normal return derivative.**
For any local transverse section `{g = g x}`, the projection along `R_α(x)` conjugates
`TauCeti.normalReturnDerivative` to `TauCeti.SmoothForm.IsContactForm.reebReturnMap`. -/
theorem kerSectionEquivKerDistribution_conj_normalReturnDerivative
    (hT : (T, x) ∈ flowDomain α.reebVectorField)
    (hfix : flowOf α.reebVectorField T x = x)
    (hg : ContMDiffAt I 𝓘(ℝ) 1 g x)
    (hgv : mvfderiv I g x (α.reebVectorField x) ≠ 0)
    {h : LinearMap.range (returnDerivative α.reebVectorField g T x) ≤
      LinearMap.ker (mvfderiv I g x : TangentSpace I x →ₗ[ℝ] ℝ)} :
    (hα.kerSectionEquivKerDistribution hgv).conj
        (normalReturnDerivative α.reebVectorField g T x h) =
      hα.reebReturnMap hT hfix := by
  rw [hα.kerSectionEquivKerDistribution_def hgv]
  exact equivOfIsCompl_conj_normalReturnDerivative
    (hα.contMDiff_reebVectorField.of_le (by simp)) hT hfix hg hgv
    (hα.isCompl_kerDistribution_span_reebVectorField x)
    (hα.coe_reebReturnMap_apply hT hfix)

/-- The characteristic polynomial of `reebReturnMap` agrees with that of
`normalReturnDerivative`. -/
theorem charpoly_reebReturnMap_eq_charpoly_normalReturnDerivative
    (hT : (T, x) ∈ flowDomain α.reebVectorField)
    (hfix : flowOf α.reebVectorField T x = x)
    (hg : ContMDiffAt I 𝓘(ℝ) 1 g x)
    (hgv : mvfderiv I g x (α.reebVectorField x) ≠ 0)
    {h : LinearMap.range (returnDerivative α.reebVectorField g T x) ≤
      LinearMap.ker (mvfderiv I g x : TangentSpace I x →ₗ[ℝ] ℝ)} :
    (hα.reebReturnMap hT hfix).charpoly =
      (normalReturnDerivative α.reebVectorField g T x h).charpoly := by
  rw [← hα.kerSectionEquivKerDistribution_conj_normalReturnDerivative hT hfix hg hgv,
    LinearEquiv.charpoly_conj]

/-- `μ` is an eigenvalue of `reebReturnMap` on `ξ` if and only if it is an eigenvalue of
`normalReturnDerivative` on any transverse section. -/
theorem hasEigenvalue_reebReturnMap_iff_hasEigenvalue_normalReturnDerivative
    (hT : (T, x) ∈ flowDomain α.reebVectorField)
    (hfix : flowOf α.reebVectorField T x = x)
    (hg : ContMDiffAt I 𝓘(ℝ) 1 g x)
    (hgv : mvfderiv I g x (α.reebVectorField x) ≠ 0)
    {h : LinearMap.range (returnDerivative α.reebVectorField g T x) ≤
      LinearMap.ker (mvfderiv I g x : TangentSpace I x →ₗ[ℝ] ℝ)} (μ : ℝ) :
    (hα.reebReturnMap hT hfix).HasEigenvalue μ ↔
      (normalReturnDerivative α.reebVectorField g T x h).HasEigenvalue μ := by
  simp only [Module.End.hasEigenvalue_iff_isRoot_charpoly,
    hα.charpoly_reebReturnMap_eq_charpoly_normalReturnDerivative hT hfix hg hgv (h := h)]

/-- For `μ ≠ 0` (in particular `μ = 1`), `μ` is an eigenvalue of `reebReturnMap` on `ξ` if and only
if it is an eigenvalue of `returnDerivative` for any transverse section. -/
theorem hasEigenvalue_reebReturnMap_iff_hasEigenvalue_returnDerivative
    (hT : (T, x) ∈ flowDomain α.reebVectorField)
    (hfix : flowOf α.reebVectorField T x = x)
    (hg : ContMDiffAt I 𝓘(ℝ) 1 g x)
    (hgv : mvfderiv I g x (α.reebVectorField x) ≠ 0) {μ : ℝ} (hμ : μ ≠ 0) :
    (hα.reebReturnMap hT hfix).HasEigenvalue μ ↔
      (returnDerivative α.reebVectorField g T x).HasEigenvalue μ := by
  have hR := range_returnDerivative_le_ker
    (hα.contMDiff_reebVectorField.of_le (by simp)) hT hfix hg hgv
  rw [hα.hasEigenvalue_reebReturnMap_iff_hasEigenvalue_normalReturnDerivative hT hfix hg hgv
      (h := hR),
    hasEigenvalue_normalReturnDerivative_iff hμ]

/-- At a local periodic point `x` of period `T` where `1` is not an eigenvalue of `reebReturnMap`,
there exists a function `g : M → ℝ`, `C¹` at `x` and transverse to `R_α(x)`, whose
`returnDerivative` at `(T, x)` does not have `1` as an eigenvalue. -/
theorem exists_contMDiffAt_and_not_hasEigenvalue_returnDerivative
    (hT : (T, x) ∈ flowDomain α.reebVectorField)
    (hfix : flowOf α.reebVectorField T x = x)
    (hnd : ¬(hα.reebReturnMap hT hfix).HasEigenvalue 1) :
    ∃ g : M → ℝ, ContMDiffAt I 𝓘(ℝ) 1 g x ∧
      mvfderiv I g x (α.reebVectorField x) ≠ 0 ∧
      ¬(returnDerivative α.reebVectorField g T x).HasEigenvalue 1 := by
  have : IsManifold I 1 M := .of_le (by simp : (1 : ℕ∞ω) ≤ ∞)
  obtain ⟨g, hg, hgv⟩ := hα.exists_contMDiffAt_and_mvfderiv_reebVectorField_eq_one le_rfl x
  have hgv0 : mvfderiv I g x (α.reebVectorField x) ≠ 0 := hgv ▸ one_ne_zero
  exact ⟨g, hg, hgv0, mt (hα.hasEigenvalue_reebReturnMap_iff_hasEigenvalue_returnDerivative
    hT hfix hg hgv0 one_ne_zero).2 hnd⟩

end SectionComparison

end ReturnMap

/-! ### Nondegenerate closed Reeb orbits and finiteness -/

section Nondegenerate

variable (hα : α.IsContactForm) (hc : IsCompleteVectorField α.reebVectorField)

/-- Every periodic trajectory `c` of `reebFlow` fixes `c.point` at `c.period` under `flowOf`. -/
theorem flowOf_period_eq_point (c : Flow.PeriodicTrajectory (hα.reebFlow hc)) :
    flowOf α.reebVectorField c.period c.point = c.point := by
  rw [← hα.reebFlow_eq_flowOf hc]
  exact c.apply_period

/-- A closed Reeb orbit `γ` is **nondegenerate** when `1` is not an eigenvalue of the linearized
Reeb return map restricted to `ξ = ker α` along any (equivalently, every) representative
trajectory. -/
def IsNondegenerateOrbit (γ : Flow.ClosedOrbit (hα.reebFlow hc)) : Prop :=
  ∀ c : Flow.PeriodicTrajectory (hα.reebFlow hc), Flow.ClosedOrbit.mk c = γ →
    ¬(hα.reebReturnMap (hc.mem_flowDomain c.period c.point)
      (hα.flowOf_period_eq_point hc c)).HasEigenvalue 1

/-- Unfolds `IsContactForm.IsNondegenerateOrbit` in terms of representative periodic
trajectories. -/
theorem isNondegenerateOrbit_def (γ : Flow.ClosedOrbit (hα.reebFlow hc)) :
    hα.IsNondegenerateOrbit hc γ ↔
      ∀ c : Flow.PeriodicTrajectory (hα.reebFlow hc), Flow.ClosedOrbit.mk c = γ →
        ¬(hα.reebReturnMap (hc.mem_flowDomain c.period c.point)
          (hα.flowOf_period_eq_point hc c)).HasEigenvalue 1 :=
  Iff.rfl

/-- Nondegeneracy of a closed Reeb orbit can be tested on any representative trajectory. -/
@[simp]
theorem isNondegenerateOrbit_mk_iff (c : Flow.PeriodicTrajectory (hα.reebFlow hc)) :
    hα.IsNondegenerateOrbit hc (Flow.ClosedOrbit.mk c) ↔
      ¬(hα.reebReturnMap (hc.mem_flowDomain c.period c.point)
        (hα.flowOf_period_eq_point hc c)).HasEigenvalue 1 := by
  refine ⟨fun h ↦ h c rfl, fun h c' hc' ↦ ?_⟩
  obtain ⟨s, rfl⟩ := Flow.ClosedOrbit.mk_eq_mk_iff.1 hc'
  have hpt : (s +ᵥ c).point = flowOf α.reebVectorField s c.point := by
    rw [Flow.PeriodicTrajectory.point_vadd, hα.reebFlow_eq_flowOf hc]
  rw [hα.hasEigenvalue_reebReturnMap_congr_iff (Flow.PeriodicTrajectory.period_vadd s c) hpt _ _
      (hc.mem_flowDomain c.period (flowOf α.reebVectorField s c.point))
      (by rw [← hα.reebFlow_eq_flowOf hc, ← hα.reebFlow_eq_flowOf hc,
        (hα.reebFlow hc).apply_comm, c.apply_period]),
    hα.hasEigenvalue_reebReturnMap_flowOf_iff
      (hc.mem_flowDomain s c.point) (hc.mem_flowDomain c.period c.point)
      (hα.flowOf_period_eq_point hc c)]
  exact h

/-- For the `k`-fold iterate `c.iterate k` of a periodic Reeb trajectory `c`, the characteristic
polynomial of `reebReturnMap` equals that of the `k`-th power of `reebReturnMap` along `c`. -/
theorem charpoly_reebReturnMap_iterate (c : Flow.PeriodicTrajectory (hα.reebFlow hc)) (k : ℕ+) :
    (hα.reebReturnMap (hc.mem_flowDomain (c.iterate k).period (c.iterate k).point)
        (hα.flowOf_period_eq_point hc (c.iterate k))).charpoly =
      ((hα.reebReturnMap (hc.mem_flowDomain c.period c.point)
        (hα.flowOf_period_eq_point hc c)) ^ (k : ℕ)).charpoly := by
  obtain ⟨hkT, hfix_k⟩ := flowOf_natCast_mul_of_flowOf_eq
    (hα.contMDiff_reebVectorField.of_le (by simp))
    (hc.mem_flowDomain c.period c.point) (hα.flowOf_period_eq_point hc c) k
  rw [hα.charpoly_reebReturnMap_congr (Flow.PeriodicTrajectory.period_iterate c k)
      (Flow.PeriodicTrajectory.point_iterate c k) _ _ hkT hfix_k,
    hα.reebReturnMap_natCast_mul (hc.mem_flowDomain c.period c.point)
      (hα.flowOf_period_eq_point hc c) k]

/-- `μ` is an eigenvalue of `reebReturnMap` along `c.iterate k` if and only if `μ` is an eigenvalue
of the `k`-th power of `reebReturnMap` along `c`. -/
theorem hasEigenvalue_reebReturnMap_iterate_iff (c : Flow.PeriodicTrajectory (hα.reebFlow hc))
    (k : ℕ+) (μ : ℝ) :
    (hα.reebReturnMap (hc.mem_flowDomain (c.iterate k).period (c.iterate k).point)
        (hα.flowOf_period_eq_point hc (c.iterate k))).HasEigenvalue μ ↔
      ((hα.reebReturnMap (hc.mem_flowDomain c.period c.point)
        (hα.flowOf_period_eq_point hc c)) ^ (k : ℕ)).HasEigenvalue μ := by
  simp only [Module.End.hasEigenvalue_iff_isRoot_charpoly,
    hα.charpoly_reebReturnMap_iterate hc c k]

/-- **Nondegeneracy of an iterate.** The `k`-fold iterate `γ.iterate k` of a closed Reeb orbit is
nondegenerate if and only if `1` is not an eigenvalue of the `k`-th power of the linearized Reeb
return map restricted to `ξ`. -/
theorem isNondegenerateOrbit_iterate_iff (c : Flow.PeriodicTrajectory (hα.reebFlow hc))
    (k : ℕ+) :
    hα.IsNondegenerateOrbit hc ((Flow.ClosedOrbit.mk c).iterate k) ↔
      ¬((hα.reebReturnMap (hc.mem_flowDomain c.period c.point)
        (hα.flowOf_period_eq_point hc c)) ^ (k : ℕ)).HasEigenvalue 1 := by
  rw [Flow.ClosedOrbit.iterate_mk, isNondegenerateOrbit_mk_iff,
    hα.hasEigenvalue_reebReturnMap_iterate_iff hc c k 1]

/-- If an iterate `γ.iterate k` of a closed Reeb orbit is nondegenerate, then `γ` itself is
nondegenerate. -/
theorem isNondegenerateOrbit_of_iterate {γ : Flow.ClosedOrbit (hα.reebFlow hc)} {k : ℕ+}
    (hk : hα.IsNondegenerateOrbit hc (γ.iterate k)) :
    hα.IsNondegenerateOrbit hc γ := by
  induction γ using Flow.ClosedOrbit.ind with
  | h c =>
    rw [isNondegenerateOrbit_iterate_iff] at hk
    exact (isNondegenerateOrbit_mk_iff hα hc c).2 fun h1 ↦ hk (by simpa using h1.pow (k : ℕ))

omit hc in
/-- **Finiteness of nondegenerate closed Reeb orbits below a period bound.** On a compact
boundaryless contact manifold, if every closed Reeb orbit (including covered orbits) of period at
most `T` is nondegenerate, then there are only finitely many closed Reeb orbits of period at most
`T`. -/
theorem finite_setOf_closedOrbit_period_le [CompactSpace M] (T : ℝ)
    (hnd : ∀ γ : Flow.ClosedOrbit (hα.reebFlow hα.isCompleteVectorField_reebVectorField),
      γ.period ≤ T → hα.IsNondegenerateOrbit hα.isCompleteVectorField_reebVectorField γ) :
    {γ : Flow.ClosedOrbit (hα.reebFlow hα.isCompleteVectorField_reebVectorField) |
      γ.period ≤ T}.Finite := by
  let hc' := hα.isCompleteVectorField_reebVectorField
  obtain ⟨ε, hε, hbound⟩ := hα.exists_pos_period_le_closedOrbit
  have hv := hα.contMDiff_reebVectorField.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)
  -- Cover all periodic pairs `(t, p)` in the compact window `[ε, T] × M` by finitely many orbits.
  let S : Set (ℝ × M) := Icc ε T ×ˢ (univ : Set M)
  have hSnd : ∀ x ∈ S, flowOf α.reebVectorField x.1 x.2 = x.2 →
      ∃ g : M → ℝ, ContMDiffAt I 𝓘(ℝ) 1 g x.2 ∧
        mvfderiv I g x.2 (α.reebVectorField x.2) ≠ 0 ∧
        ¬(returnDerivative α.reebVectorField g x.1 x.2).HasEigenvalue 1 := by
    rintro ⟨t, p⟩ ⟨ht, -⟩ hp
    apply hα.exists_contMDiffAt_and_not_hasEigenvalue_returnDerivative (hc'.mem_flowDomain t p) hp
    have hnd' := (hα.isNondegenerateOrbit_mk_iff hc'
      (hα.reebTrajectory hc' p (hε.trans_le ht.1) ((hα.reebFlow_eq_flowOf hc' t p).trans hp))).1
      (hnd _ (by simpa only [Flow.ClosedOrbit.period_mk, period_reebTrajectory] using ht.2))
    rwa [hα.hasEigenvalue_reebReturnMap_congr_iff
      (hα.period_reebTrajectory hc' p _ _) (hα.point_reebTrajectory hc' p _ _) _ _
      (hc'.mem_flowDomain t p) hp] at hnd'
  obtain ⟨F, -, hF⟩ := exists_finset_forall_fst_eq_and_exists_flowOf_eq_snd hv
    (isCompact_Icc.prod isCompact_univ) (hc'.flowDomain_eq_univ ▸ subset_univ _) hSnd
  -- Inject closed orbits of period `≤ T` into the finite image of `F` via `(t, p) ↦ (t, orbit p)`.
  refine Set.Finite.of_finite_image (f := fun γ : Flow.ClosedOrbit (hα.reebFlow hc') ↦
      (γ.period, γ.support))
    (((F.finite_toSet.image fun y : ℝ × M ↦ (y.1, (hα.reebFlow hc').orbit y.2))).subset ?_)
    fun _ _ _ _ h ↦ Flow.ClosedOrbit.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
  rintro _ ⟨γ, hγ, rfl⟩
  induction γ using Flow.ClosedOrbit.ind with
  | h c =>
    obtain ⟨y, hyF, hfst, s, -, hs⟩ := hF (c.period, c.point)
      ⟨⟨by simpa only [Flow.ClosedOrbit.period_mk] using hbound (Flow.ClosedOrbit.mk c),
        by simpa only [Flow.ClosedOrbit.period_mk] using hγ.out⟩, mem_univ _⟩
      (hα.flowOf_period_eq_point hc' c)
    refine ⟨y, hyF, Prod.ext (by simpa only [Flow.ClosedOrbit.period_mk] using hfst.symm) ?_⟩
    dsimp only at hs ⊢
    rw [Flow.ClosedOrbit.support_mk, ← (hα.reebFlow_eq_flowOf hc' s y.2).trans hs,
      Flow.orbit_apply]

omit hc in
/-- **Finiteness of primitive closed Reeb orbits below a period bound.** On a compact boundaryless
contact manifold, if every closed Reeb orbit (including covered orbits) of period at most `T` is
nondegenerate, then there are only finitely many primitive closed Reeb orbits of period at most
`T`. -/
theorem finite_setOf_closedOrbit_isPrimitive_and_period_le [CompactSpace M] (T : ℝ)
    (hnd : ∀ γ : Flow.ClosedOrbit (hα.reebFlow hα.isCompleteVectorField_reebVectorField),
      γ.period ≤ T → hα.IsNondegenerateOrbit hα.isCompleteVectorField_reebVectorField γ) :
    {γ : Flow.ClosedOrbit (hα.reebFlow hα.isCompleteVectorField_reebVectorField) |
      γ.IsPrimitive ∧ γ.period ≤ T}.Finite :=
  (hα.finite_setOf_closedOrbit_period_le T hnd).subset fun _ h ↦ h.2

end Nondegenerate

end IsContactForm

end TauCeti.SmoothForm
