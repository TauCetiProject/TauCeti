/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Related
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Topology.Covering.Basic
import TauCeti.Geometry.Manifold.MFDeriv.OfCompLeft
import TauCeti.Topology.ContinuousOn.Extension
import TauCeti.Topology.Covering.Convex

/-!
# Integral curves and maximal flows on smooth coverings

A covering map which is a local diffeomorphism lifts integral curves of related vector fields
through any prescribed point above their initial point. The maximal existence intervals agree,
so completeness of the base field implies completeness of the lifted field.

The lifting construction follows the continuous-lift and extension argument in
`TauCeti.Geometry.Manifold.Riemannian.Covering.Complete`. Its first-order differential step uses
`HasMFDerivWithinAt.of_comp_of_leftInverse` with the inverse of the covering differential.
Neither uniqueness of the vector fields' integral curves nor completeness of their model spaces
is needed for the interval equality.
-/

public section

open Function Set TauCeti
open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {p : M → N} {X : (x : M) → TangentSpace I x} {Y : (y : N) → TangentSpace J y}
  {n : ℕ∞ω}

/-- A continuous lift of an integral curve through a local diffeomorphism is an integral curve
of the related field. Continuity on the parameter set suffices, even at its boundary. -/
theorem IsLocalDiffeomorph.isMIntegralCurveOn_of_comp
    (hp : IsLocalDiffeomorph I J n p) (hn : n ≠ 0) {Γ : ℝ → M} {s : Set ℝ}
    (hXY : ∀ t ∈ s, mfderiv I J p (Γ t) (X (Γ t)) = Y (p (Γ t)))
    (hΓ : ContinuousOn Γ s) (hγ : IsMIntegralCurveOn (p ∘ Γ) Y s) :
    IsMIntegralCurveOn Γ X s := by
  intro t ht
  let e := (hp (Γ t)).mfderivToContinuousLinearEquiv hn
  refine (HasMFDerivWithinAt.of_comp_of_leftInverse
    (L := e.symm.toContinuousLinearMap) ((hp (Γ t)).mdifferentiableAt hn).hasMFDerivAt
    (hΓ t ht) (hγ t ht) e.left_inv).congr_mfderiv ?_
  ext
  -- The parameter tangent space is definitionally `ℝ`; expose evaluation at `1` so that the
  -- inverse law applies without changing either manifold tangent-space carrier.
  change e.symm ((1 : ℝ) • Y (p (Γ t))) = (1 : ℝ) • X (Γ t)
  rw [one_smul, one_smul, ← hXY t ht]
  exact e.symm_apply_apply (X (Γ t))

namespace IsCoveringMap

/-- An integral curve on an interval lifts through a smooth covering with prescribed initial
point. Its projection agrees with the original curve throughout the parameter set. -/
theorem exists_isMIntegralCurveOn_lift (hcov : IsCoveringMap p)
    (hp : IsLocalDiffeomorph I J n p) (hn : n ≠ 0)
    (hXY : ∀ x, mfderiv I J p x (X x) = Y (p x)) {γ : ℝ → N} {s : Set ℝ}
    (hs : s.OrdConnected) {t₀ : ℝ} (ht₀ : t₀ ∈ s) (hγ : IsMIntegralCurveOn γ Y s)
    (x : M) (hx : γ t₀ = p x) :
    ∃ Γ : ℝ → M, Γ t₀ = x ∧ IsMIntegralCurveOn Γ X s ∧ EqOn (p ∘ Γ) γ s := by
  obtain ⟨L, ⟨hL₀, hL⟩, -⟩ := hcov.existsUnique_continuousMap_lifts_of_convex hs.convex
    ⟨s.domRestrict γ, hγ.continuousOn.domRestrict⟩ ⟨t₀, ht₀⟩ x hx.symm
  have : Nonempty M := ⟨x⟩
  obtain ⟨Γ, hΓc, hΓL⟩ := L.continuous.exists_continuousOn_eq (A := s)
  have hΓ₀ : Γ t₀ = x := (hΓL ⟨t₀, ht₀⟩).trans hL₀
  have hΓγ : EqOn (p ∘ Γ) γ s := by
    intro t ht
    simpa only [Function.comp_apply, hΓL ⟨t, ht⟩, ContinuousMap.coe_mk, Set.domRestrict] using
      congrFun hL ⟨t, ht⟩
  exact ⟨Γ, hΓ₀, hp.isMIntegralCurveOn_of_comp hn (fun t _ ↦ hXY (Γ t)) hΓc
    (hγ.congr hΓγ), hΓγ⟩

/-- A global integral curve lifts uniquely through a smooth covering once its initial point is
specified. Uniqueness here is uniqueness of lifts of the specified curve, requiring no regularity
of either vector field. -/
theorem existsUnique_isMIntegralCurve_lift (hcov : IsCoveringMap p)
    (hp : IsLocalDiffeomorph I J n p) (hn : n ≠ 0)
    (hXY : ∀ x, mfderiv I J p x (X x) = Y (p x)) {γ : ℝ → N}
    (hγ : IsMIntegralCurve γ Y) {t₀ : ℝ} (x : M) (hx : γ t₀ = p x) :
    ∃! Γ : ℝ → M, Γ t₀ = x ∧ IsMIntegralCurve Γ X ∧ p ∘ Γ = γ := by
  obtain ⟨Γ, hΓ0, hΓ, hΓγ⟩ := hcov.exists_isMIntegralCurveOn_lift hp hn hXY
    ordConnected_univ (mem_univ t₀) (hγ.isMIntegralCurveOn univ) x hx
  have hΓγ' : p ∘ Γ = γ := funext fun t ↦ hΓγ (mem_univ t)
  have hΓ' : IsMIntegralCurve Γ X := isMIntegralCurve_iff_isMIntegralCurveOn.2 hΓ
  refine ⟨Γ, ⟨hΓ0, hΓ', hΓγ'⟩, ?_⟩
  intro Γ' ⟨hΓ'0, hΓ'int, hΓ'γ⟩
  exact hcov.eq_of_comp_eq hΓ'int.continuous hΓ'.continuous
    (hΓ'γ.trans hΓγ'.symm) t₀ (hΓ'0.trans hΓ0.symm)

/-- A smooth covering preserves the maximal interval of related integral curves through
corresponding points. No uniqueness or field regularity assumptions are needed. -/
theorem maximalIntegralCurveInterval_eq_of_isLocalDiffeomorph (hcov : IsCoveringMap p)
    (hp : IsLocalDiffeomorph I J n p) (hn : n ≠ 0)
    (hXY : ∀ x, mfderiv I J p x (X x) = Y (p x)) (x : M) :
    maximalIntegralCurveInterval X x = maximalIntegralCurveInterval Y (p x) := by
  refine Subset.antisymm ((hp.mdifferentiable hn).maximalIntegralCurveInterval_subset hXY x) ?_
  intro t ht
  obtain ⟨γ, a, b, hγ, hγ0, h0, ht, -⟩ :=
    exists_isMIntegralCurveOn_maximalIntegralCurve_eq ht
  obtain ⟨Γ, hΓ0, hΓ, -⟩ := hcov.exists_isMIntegralCurveOn_lift hp hn hXY
    ordConnected_Ioo h0 hγ x hγ0
  exact hΓ.subset_maximalIntegralCurveInterval h0 hΓ0 ht

/-- Completeness ascends along smooth covering maps relating the vector fields. -/
theorem isCompleteVectorField_of_isLocalDiffeomorph (hcov : IsCoveringMap p)
    (hp : IsLocalDiffeomorph I J n p) (hn : n ≠ 0)
    (hXY : ∀ x, mfderiv I J p x (X x) = Y (p x)) (hY : IsCompleteVectorField Y) :
    IsCompleteVectorField X := by
  rw [isCompleteVectorField_iff_maximalIntegralCurveInterval]
  intro x
  rw [hcov.maximalIntegralCurveInterval_eq_of_isLocalDiffeomorph hp hn hXY,
    hY.maximalIntegralCurveInterval_eq_univ]

end IsCoveringMap
