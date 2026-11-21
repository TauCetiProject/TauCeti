/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import Mathlib.Topology.Algebra.Module.LinearPMap
public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Compact
import Mathlib.Analysis.Normed.Operator.Banach
import TauCeti.Analysis.Normed.Operator.Banach

/-!
# The partial operator of an operator on a common domain

An unbounded operator on a Banach space `H` is often given, as in the analysis of Floer
trajectories, by a bounded operator `A : D →L H` on a smaller space `D` together with a bounded
injective inclusion `ι : D →L H`: the asymptotic operator `J₀ (∂ₜ - S)` of a Floer cylinder is
bounded from `H¹(S¹)` to `L²(S¹)`. Such pairs `(ι, A)` are the input of the trajectory operators
`TauCeti.WeakDerivStep.domainTrajectoryOperator`. This file attaches to `(ι, A)` the partial linear
operator `ContinuousLinearMap.domainOperator ι A hι` on `H` with domain `range ι`, acting by
`ι x ↦ A x`, and translates the conditions usually placed on the pair into the native theory of
partial operators. The construction and its graph and closedness API allow `A` to take values in
a second space `K`, as for the weak gradient `TauCeti.weakGradientPMap`. Symmetry and
self-adjointness on an inner product space are in
`TauCeti.Analysis.InnerProductSpace.LinearPMap.CommonDomain`.

* **Graph.** The graph of the partial operator is the range of `x ↦ (ι x, A x)`
  (`ContinuousLinearMap.graph_domainOperator`). If `D` is complete it is closed when the norm of
  `D` is bounded by the graph norm, `‖x‖ ≤ C (‖ι x‖ + ‖A x‖)`
  (`ContinuousLinearMap.isClosed_domainOperator_of_norm_le`), and if `H` and `K` are complete as
  well, only then (`ContinuousLinearMap.isClosed_domainOperator_iff`).
* **Resolvent.** If `c • ι - A : D → H` is invertible, `c` is a resolvent point with resolvent
  `ι ∘ (c • ι - A)⁻¹` (`ContinuousLinearMap.resolvent_domainOperator`); for complete `D` and `H`
  this characterizes the resolvent points
  (`ContinuousLinearMap.mem_resolventSet_domainOperator_iff`). If moreover `ι` is a compact
  operator, the partial operator has compact resolvent
  (`ContinuousLinearMap.hasCompactResolvent_domainOperator`). The shift at `c = 0` is invertible
  exactly when `A` is (`ContinuousLinearMap.isInvertible_zero_smul_sub_iff`), so `0` is then a
  resolvent point (`ContinuousLinearMap.mem_resolventSet_domainOperator_of_isInvertible`).

When `ι` is the identity, the partial operator is the everywhere defined operator `A`
(`ContinuousLinearMap.domainOperator_id`).

## Main definitions

* `ContinuousLinearMap.domainOperator`: the partial operator `ι x ↦ A x` with domain `range ι`.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, Sections III.5.2 and III.6.8.
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1–33, Section 4 (paths of self-adjoint operators on a fixed domain `W ⊂ H`).
-/

public section

noncomputable section

open Function

namespace ContinuousLinearMap

section Basic

variable {R D H K : Type*} [Ring R] [AddCommGroup D] [Module R D] [TopologicalSpace D]
  [AddCommGroup H] [Module R H] [TopologicalSpace H]
  [AddCommGroup K] [Module R K] [TopologicalSpace K]
  (ι : D →L[R] H) (A : D →L[R] K) (hι : Injective ι)

/-- The partial linear operator from `H` to `K` with domain the range of an injective map
`ι : D →L H`, acting by `ι x ↦ A x`. For `K = H`, this is the unbounded operator on `H` described
by a bounded operator `A : D →L H` on the common domain `D`. -/
def domainOperator : H →ₗ.[R] K where
  domain := LinearMap.range (ι : D →ₗ[R] H)
  toFun := (A : D →ₗ[R] K) ∘ₗ (LinearEquiv.ofInjective (ι : D →ₗ[R] H) hι).symm.toLinearMap

/-- The domain of `domainOperator ι A hι` is the range of `ι`. -/
@[simp]
theorem domain_domainOperator :
    (domainOperator ι A hι).domain = LinearMap.range (ι : D →ₗ[R] H) := (rfl)

/-- A vector lies in the domain of `domainOperator ι A hι` exactly when it is in the range of
`ι`. -/
theorem mem_domain_domainOperator_iff {y : H} :
    y ∈ (domainOperator ι A hι).domain ↔ ∃ x, ι x = y :=
  LinearMap.mem_range

/-- Every `ι x` lies in the domain of `domainOperator ι A hι`. -/
theorem apply_mem_domain_domainOperator (x : D) : ι x ∈ (domainOperator ι A hι).domain :=
  (mem_domain_domainOperator_iff ι A hι).2 ⟨x, rfl⟩

/-- `domainOperator ι A hι` sends `ι x` to `A x`. -/
theorem domainOperator_apply {y : (domainOperator ι A hι).domain} {x : D} (hx : ι x = y) :
    domainOperator ι A hι y = A x := by
  have hy : y = LinearEquiv.ofInjective (ι : D →ₗ[R] H) hι x :=
    Subtype.ext (hx.symm.trans (LinearEquiv.ofInjective_apply _ x).symm)
  -- This lemma is where the definition of `domainOperator` is deliberately unfolded: its value at
  -- `ofInjective ι hι x` is `A ((ofInjective ι hι).symm (ofInjective ι hι x))`.
  rw [hy]
  exact congrArg A ((LinearEquiv.ofInjective (ι : D →ₗ[R] H) hι).symm_apply_apply x)

/-- `domainOperator ι A hι` sends `ι x` to `A x`. -/
@[simp]
theorem domainOperator_apply_mk (x : D) (hx : ι x ∈ (domainOperator ι A hι).domain) :
    domainOperator ι A hι ⟨ι x, hx⟩ = A x :=
  domainOperator_apply ι A hι rfl

/-- A pair `(y, z)` lies on the graph of `domainOperator ι A hι` exactly when `y = ι x` and
`z = A x` for some `x : D`. -/
theorem mem_graph_domainOperator_iff {p : H × K} :
    p ∈ (domainOperator ι A hι).graph ↔ ∃ x, ι x = p.1 ∧ A x = p.2 := by
  rw [LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨⟨y, hy⟩, hy₁, hy₂⟩
    obtain ⟨x, rfl⟩ := (mem_domain_domainOperator_iff ι A hι).1 hy
    exact ⟨x, hy₁, (domainOperator_apply_mk ι A hι x hy).symm.trans hy₂⟩
  · rintro ⟨x, hx₁, hx₂⟩
    exact ⟨⟨ι x, apply_mem_domain_domainOperator ι A hι x⟩, hx₁,
      (domainOperator_apply_mk ι A hι x _).trans hx₂⟩

/-- The graph of `domainOperator ι A hι` is the range of `x ↦ (ι x, A x)`. -/
theorem graph_domainOperator :
    (domainOperator ι A hι).graph = LinearMap.range ((ι : D →ₗ[R] H).prod (A : D →ₗ[R] K)) := by
  ext p
  rw [mem_graph_domainOperator_iff]
  simp [Prod.ext_iff]

/-- For the identity inclusion, `domainOperator` is the everywhere defined operator `A`. -/
theorem domainOperator_id (A : H →L[R] K) :
    domainOperator (.id R H) A (by intro x y h; simpa using h) =
      (A : H →ₗ[R] K).toPMap ⊤ := by
  refine LinearPMap.ext ?_ fun y hy hy' ↦ ?_
  · rw [domain_domainOperator, LinearMap.toPMap_domain, coe_id, LinearMap.range_id]
  · -- `rw [LinearMap.toPMap_apply]` does not find the coercion of `LinearMap.toPMap`, so the two
    -- formulas are composed as terms.
    exact (domainOperator_apply _ A _ (x := y) (by simp)).trans
      (LinearMap.toPMap_apply (A : H →ₗ[R] K) ⊤ ⟨y, hy'⟩).symm

end Basic

section Closed

variable {R D H K : Type*} [CommRing R] [AddCommGroup D] [Module R D] [TopologicalSpace D]
  [AddCommGroup H] [Module R H] [TopologicalSpace H]
  [AddCommGroup K] [Module R K] [TopologicalSpace K]
  {ι : D →L[R] H} {A : D →L[R] K} {hι : Injective ι}

/-- `domainOperator ι A hι` is closed exactly when the range of `x ↦ (ι x, A x)` is closed. -/
theorem isClosed_domainOperator_iff_isClosed_range :
    (domainOperator ι A hι).IsClosed ↔ IsClosed (Set.range (ι.prod A)) := by
  rw [LinearPMap.IsClosed, graph_domainOperator, ← coe_prod, LinearMap.coe_range, coe_coe]

end Closed

section Resolvent

variable {R D H : Type*} [CommRing R] [AddCommGroup D] [Module R D] [TopologicalSpace D]
  [AddCommGroup H] [Module R H] [TopologicalSpace H] [IsTopologicalAddGroup H]
  [ContinuousConstSMul R H] {ι A : D →L[R] H} {hι : Injective ι} {c : R}

/-- On the domain of `domainOperator ι A hι`, the shift `c • I - domainOperator ι A hι` is the
shift `c • ι - A` of the pair. -/
theorem smul_sub_domainOperator_apply {y : (domainOperator ι A hι).domain} {x : D}
    (hx : ι x = y) : c • (y : H) - domainOperator ι A hι y = (c • ι - A) x := by
  rw [domainOperator_apply ι A hι hx, ← hx, _root_.sub_apply, _root_.smul_apply]

/-- If `c • ι - A` is invertible, then `ι ∘ (c • ι - A)⁻¹` inverts the shift
`c • I - domainOperator ι A hι`. -/
theorem isResolventAt_domainOperator (h : (c • ι - A).IsInvertible) :
    (domainOperator ι A hι).IsResolventAt c (ι ∘L (c • ι - A).inverse) := by
  refine LinearPMap.isResolventAt_iff_forall_mem_graph.2 ⟨fun y ↦ ?_, fun p hp ↦ ?_⟩
  · have hx : c • ι ((c • ι - A).inverse y) - A ((c • ι - A).inverse y) = y := by
      simpa using h.self_apply_inverse y
    refine (mem_graph_domainOperator_iff ι A hι).2 ⟨(c • ι - A).inverse y, by simp, ?_⟩
    simp only [comp_apply]
    generalize (c • ι - A).inverse y = x at hx ⊢
    rw [← hx, sub_sub_cancel]
  · obtain ⟨x, hx, hAx⟩ := (mem_graph_domainOperator_iff ι A hι).1 hp
    have hshift : c • ι x - A x = (c • ι - A) x := by simp
    rw [← hx, ← hAx, hshift, comp_apply, h.inverse_apply_self]

/-- If `c • ι - A` is invertible, then `c` is a resolvent point of `domainOperator ι A hι`. -/
theorem mem_resolventSet_domainOperator (h : (c • ι - A).IsInvertible) :
    c ∈ (domainOperator ι A hι).resolventSet :=
  (isResolventAt_domainOperator h).mem_resolventSet

/-- The shift `0 • ι - A` of the pair is invertible exactly when `A` is. -/
theorem isInvertible_zero_smul_sub_iff : ((0 : R) • ι - A).IsInvertible ↔ A.IsInvertible := by
  have h : (0 : R) • ι - A = (ContinuousLinearEquiv.neg R : H ≃L[R] H) ∘L A := by ext; simp
  rw [h, isInvertible_equiv_comp]

/-- If `A` is invertible, then `0` is a resolvent point of `domainOperator ι A hι`. -/
theorem mem_resolventSet_domainOperator_of_isInvertible (h : A.IsInvertible) :
    0 ∈ (domainOperator ι A hι).resolventSet :=
  mem_resolventSet_domainOperator (isInvertible_zero_smul_sub_iff.2 h)

/-- If `c • ι - A` is invertible, the resolvent of `domainOperator ι A hι` at `c` is
`ι ∘ (c • ι - A)⁻¹`. -/
theorem resolvent_domainOperator (h : (c • ι - A).IsInvertible) :
    (domainOperator ι A hι).resolvent c = ι ∘L (c • ι - A).inverse :=
  LinearPMap.resolvent_eq_of_isResolventAt (isResolventAt_domainOperator h)

/-- The shift `c • I - domainOperator ι A hι` on its domain is bijective exactly when the shift
`c • ι - A : D → H` is. -/
theorem bijective_smul_sub_domainOperator_iff :
    Bijective (fun y : (domainOperator ι A hι).domain ↦ c • (y : H) - domainOperator ι A hι y) ↔
      Bijective (c • ι - A) := by
  let e : D ≃ (domainOperator ι A hι).domain :=
    (LinearEquiv.ofInjective (ι : D →ₗ[R] H) hι).toEquiv
  rw [← e.bijective_comp]
  refine iff_of_eq (congrArg Bijective (funext fun x ↦ ?_))
  exact smul_sub_domainOperator_apply (LinearEquiv.ofInjective_apply (h := hι) _ x).symm

/-- At a resolvent point `c` of `domainOperator ι A hι`, the shift `c • ι - A : D → H` is
bijective. -/
theorem bijective_smul_sub_of_mem_resolventSet (h : c ∈ (domainOperator ι A hι).resolventSet) :
    Bijective (c • ι - A) := by
  obtain ⟨R, hR⟩ := LinearPMap.mem_resolventSet_iff.1 h
  exact bijective_smul_sub_domainOperator_iff.1 hR.smul_sub_bijective

/-- If `ι` is a compact operator and `c • ι - A` is invertible for some `c`, then
`domainOperator ι A hι` has compact resolvent. -/
theorem hasCompactResolvent_domainOperator (hcpt : IsCompactOperator ι)
    (h : (c • ι - A).IsInvertible) : (domainOperator ι A hι).HasCompactResolvent :=
  .of_isCompactOperator_resolvent (mem_resolventSet_domainOperator h) <| by
    rw [resolvent_domainOperator h]
    exact hcpt.comp_clm _

end Resolvent

section Normed

variable {𝕜 D H K : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup D] [NormedSpace 𝕜 D] [NormedAddCommGroup H] [NormedSpace 𝕜 H]
  [NormedAddCommGroup K] [NormedSpace 𝕜 K]

/-- For complete `D` and `H`, a scalar `c` is a resolvent point of `domainOperator ι A hι` exactly
when `c • ι - A : D → H` is invertible. -/
theorem mem_resolventSet_domainOperator_iff [CompleteSpace D] [CompleteSpace H]
    {ι A : D →L[𝕜] H} {hι : Injective ι} {c : 𝕜} :
    c ∈ (domainOperator ι A hι).resolventSet ↔ (c • ι - A).IsInvertible :=
  ⟨fun h ↦ isInvertible_iff_bijective.2 (bijective_smul_sub_of_mem_resolventSet h),
    mem_resolventSet_domainOperator⟩

/-- If `D` is complete and its norm is bounded by the graph norm, `‖x‖ ≤ C (‖ι x‖ + ‖A x‖)`, then
`domainOperator ι A hι` is closed. -/
theorem isClosed_domainOperator_of_norm_le [CompleteSpace D] {ι : D →L[𝕜] H} {A : D →L[𝕜] K}
    {hι : Injective ι} {C : ℝ} (hC : ∀ x, ‖x‖ ≤ C * (‖ι x‖ + ‖A x‖)) :
    (domainOperator ι A hι).IsClosed := by
  rw [isClosed_domainOperator_iff_isClosed_range]
  have hbound : ∀ x, ‖x‖ ≤ (2 * max C 0).toNNReal * ‖ι.prod A x‖ := fun x ↦ by
    have h₁ : ‖ι x‖ ≤ ‖ι.prod A x‖ := norm_fst_le (ι.prod A x)
    have h₂ : ‖A x‖ ≤ ‖ι.prod A x‖ := norm_snd_le (ι.prod A x)
    rw [Real.coe_toNNReal _ (by positivity)]
    calc ‖x‖ ≤ C * (‖ι x‖ + ‖A x‖) := hC x
      _ ≤ max C 0 * (‖ι x‖ + ‖A x‖) := by gcongr; exact le_max_left _ _
      _ ≤ max C 0 * (2 * ‖ι.prod A x‖) := by gcongr; linarith
      _ = 2 * max C 0 * ‖ι.prod A x‖ := by ring
  exact ((ι.prod A).antilipschitz_of_bound hbound).isClosed_range (ι.prod A).uniformContinuous

/-- For complete `D`, `H` and `K`, `domainOperator ι A hι` is closed exactly when the norm of `D`
is bounded by the graph norm, `‖x‖ ≤ C (‖ι x‖ + ‖A x‖)` for some `C`. -/
theorem isClosed_domainOperator_iff [CompleteSpace D] [CompleteSpace H] [CompleteSpace K]
    {ι : D →L[𝕜] H} {A : D →L[𝕜] K} {hι : Injective ι} :
    (domainOperator ι A hι).IsClosed ↔ ∃ C, ∀ x, ‖x‖ ≤ C * (‖ι x‖ + ‖A x‖) := by
  refine ⟨fun h ↦ ?_, fun ⟨C, hC⟩ ↦ isClosed_domainOperator_of_norm_le hC⟩
  obtain ⟨K, hK⟩ := (ι.prod A).antilipschitz_of_injective_of_isClosed_range
    (fun x x' hxx' ↦ hι (by simpa using congrArg Prod.fst hxx'))
    (isClosed_domainOperator_iff_isClosed_range.1 h)
  refine ⟨K, fun x ↦ (hK.le_mul_norm (map_zero _) x).trans ?_⟩
  rw [prod_apply, Prod.norm_def]
  gcongr
  exact max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)

end Normed

end ContinuousLinearMap
