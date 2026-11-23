/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Periodic
public import TauCeti.Topology.PathSpace.Seamed.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Translation
import TauCeti.Geometry.Manifold.Topology
import TauCeti.Topology.PathSpace.Seamed.Component

/-!
# Seamed solutions of time-dependent vector fields

Let `X` be a time-dependent vector field on a manifold `M` and `f : M → M` a map. A **seamed
solution** of `X` with seam `f` (`TauCeti.seamedSolutions X f`) is a curve `γ : ℝ → M` defined for
all time, with `γ' t = X t (γ t)` and `γ 1 = f (γ 0)`. Its restriction to `[0, 1]` is an `f`-seamed
path (`TauCeti.seamedSolutionPath`). For a symplectomorphism `f` and the Hamiltonian or symplectic
vector field `X` of a perturbation, the seamed solutions are the zeros of the action one-form on
the space of `f`-seamed paths, and they generate the Floer complex of `f`; the seamed paths take
the place of the free loops of Hamiltonian Floer theory, which are the case `f = id`. For the
identity seam and a `1`-periodic field the seamed solutions are the `1`-periodic solutions
(`TauCeti.seamedSolutions_id_eq_periodicSolutions`).

When the suspension of `X` is complete, for instance on a compact manifold, every solution is a
trajectory of the time-dependent flow `φ_t = timeDependentFlowOf X 0 t`. So evaluation at time `0`
identifies the seamed solutions with the points at which the time-one map agrees with the seam,
`φ_1 x = f x` (`TauCeti.seamedSolutionsEquiv`). When `f` is a homeomorphism these are the fixed
points of `f⁻¹ ∘ φ_1`, and a seamed solution is called nondegenerate when its start is a
nondegenerate fixed point of `f⁻¹ ∘ φ_1`.

Seamed solutions are sorted by the path component of their seamed path in `SeamedPath f`. On a
manifold these components are clopen (`TauCeti.SeamedPath.isClopen_pathComponent`), and the seamed
path of the trajectory of `x` depends continuously on `x`. So the starts of the seamed solutions in
a given component form a clopen subset of the set where `φ_1 = f`
(`TauCeti.isClopen_setOf_seamedSolutionPath_mem_pathComponent`). On a compact manifold this subset
is compact, so if the seamed solutions in that component are nondegenerate there are only finitely
many of them (`TauCeti.finite_setOf_seamedSolutionPath_mem_pathComponent`); solutions in other
components may be degenerate, and there may be infinitely many of them. If all seamed solutions are
nondegenerate, there are finitely many in all (`TauCeti.finite_seamedSolutions`).

This is the seamed counterpart of `TauCeti.finite_contractiblePeriodicSolutions` in
`TauCeti.Geometry.Manifold.Flow.Periodic`.

## Main definitions

* `TauCeti.seamedSolutions X f`: the solutions `γ` of `γ' t = X t (γ t)` with `γ 1 = f (γ 0)`.
* `TauCeti.seamedSolutionPath`: the restriction of a seamed solution to `[0, 1]`, an `f`-seamed
  path.
* `TauCeti.seamedSolutionsEquiv`: for a complete suspension, seamed solutions correspond to the
  points where the time-one map agrees with the seam.

## Main results

* `TauCeti.seamedSolutions_id_eq_periodicSolutions`: for the identity seam and a `1`-periodic
  field, the seamed solutions are the `1`-periodic solutions.
* `TauCeti.continuous_seamedSolutionPath_seamedSolutionsEquiv_symm`: the seamed path of the
  trajectory of a point depends continuously on the point.
* `TauCeti.isClopen_setOf_seamedSolutionPath_mem_pathComponent`: the starts of the seamed
  solutions in a path component of `SeamedPath f` form a clopen subset of the set where the
  time-one map agrees with the seam.
* `TauCeti.finite_setOf_seamedSolutionPath_mem_pathComponent`: on a compact manifold, a path
  component of `SeamedPath f` contains only finitely many seamed solutions if they are all
  nondegenerate.
* `TauCeti.finite_seamedSolutions`: on a compact manifold, there are only finitely many seamed
  solutions if they are all nondegenerate.

## References

* A. Floer, *Symplectic fixed points and holomorphic spheres*, Comm. Math. Phys. 120 (1989),
  575–611.
* S. Dostoglou and D. A. Salamon, *Self-dual instantons and holomorphic curves*, Ann. of Math. 139
  (1994), 581–640.
-/

public section

noncomputable section

open Function Set
open scoped Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {X : ℝ → (x : M) → TangentSpace I x} {f : M → M}

/-- The **seamed solutions** of a time-dependent vector field `X` with seam `f`: the curves `γ`
defined for all time, with `γ' t = X t (γ t)` for every `t` and `γ 1 = f (γ 0)`. -/
def seamedSolutions (X : ℝ → (x : M) → TangentSpace I x) (f : M → M) : Set (ℝ → M) :=
  {γ | (∀ t, HasMFDerivAt 𝓘(ℝ, ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t)))) ∧
    γ 1 = f (γ 0)}

/-- The defining characterization of a seamed solution. -/
@[simp]
theorem mem_seamedSolutions {γ : ℝ → M} :
    γ ∈ seamedSolutions X f ↔
      (∀ t, HasMFDerivAt 𝓘(ℝ, ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t)))) ∧
        γ 1 = f (γ 0) :=
  Iff.rfl

/-- A seamed solution is continuous. -/
theorem continuous_of_mem_seamedSolutions {γ : ℝ → M} (hγ : γ ∈ seamedSolutions X f) :
    Continuous γ :=
  continuous_iff_continuousAt.2 fun t ↦ (hγ.1 t).continuousAt

/-- The `f`-seamed path of a seamed solution: its restriction to `[0, 1]`. -/
def seamedSolutionPath (γ : seamedSolutions X f) : SeamedPath f :=
  ⟨⟨fun t ↦ γ.val t, (continuous_of_mem_seamedSolutions γ.property).comp continuous_subtypeVal⟩,
    γ.property.2⟩

@[simp]
theorem seamedSolutionPath_apply (γ : seamedSolutions X f) (t : unitInterval) :
    (seamedSolutionPath γ).val t = γ.val t :=
  (rfl)

section Flow

variable [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M]
  (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
    (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
include hX

/-- **For the identity seam, seamed solutions are periodic solutions.** If the jointly `C¹` field
`X` is `1`-periodic in time, the seamed solutions of `X` with seam `id`, the solutions returning to
their start at time `1`, are exactly its `1`-periodic solutions. -/
theorem seamedSolutions_id_eq_periodicSolutions (hT : Periodic X 1) :
    seamedSolutions X id = periodicSolutions X 1 := by
  ext γ
  rw [mem_periodicSolutions]
  refine ⟨fun hγ ↦ ⟨hγ.1, fun t ↦ ?_⟩, fun hγ ↦ ⟨hγ.1, by simpa using hγ.2 0⟩⟩
  -- Since `X` is `1`-periodic, the shift `u ↦ γ (u + 1)` solves the same equation as `γ`, and the
  -- two agree at time `0` because `γ 1 = γ 0`; by uniqueness they agree at time `t`.
  have hshift (u : ℝ) : HasMFDerivAt 𝓘(ℝ, ℝ) I (fun u ↦ γ (u + 1)) u
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X u (γ (u + 1)))) := by
    simpa only [hT u] using HasMFDerivAt.comp_add_right (hγ.1 (u + 1))
  have h₁ := timeDependentFlowOf_eq_of_forall_hasMFDerivAt hX hγ.1 0 t
  have h₂ := timeDependentFlowOf_eq_of_forall_hasMFDerivAt hX hshift 0 t
  simp only [zero_add, hγ.2, id] at h₂
  exact h₂.symm.trans h₁

variable (hc : IsCompleteVectorField (timeDependentSuspensionField X))
include hc

/-- **Seamed solutions are the points where the time-one map agrees with the seam.** For a jointly
`C¹` time-dependent field `X` with complete suspension, evaluation at time `0` identifies the
seamed solutions of `X` with seam `f` with the points `x` at which the time-one map
`timeDependentFlowOf X 0 1` agrees with `f`. The inverse sends such a point to its trajectory under
the flow from time `0`. -/
def seamedSolutionsEquiv (f : M → M) :
    seamedSolutions X f ≃ {x | timeDependentFlowOf X 0 1 x = f x} where
  toFun γ := ⟨γ.val 0,
    (timeDependentFlowOf_eq_of_forall_hasMFDerivAt hX γ.property.1 0 1).trans γ.property.2⟩
  invFun x := ⟨fun t ↦ timeDependentFlowOf X 0 t x,
    fun t ↦ hasMFDerivAt_timeDependentFlowOf hX
      (by rw [timeDependentFlowDomain_eq_univ hc]; exact mem_univ _), by
      simp only [timeDependentFlowOf_self]
      exact x.property⟩
  left_inv γ := Subtype.ext <| funext <|
    timeDependentFlowOf_eq_of_forall_hasMFDerivAt hX γ.property.1 0
  right_inv x := Subtype.ext (timeDependentFlowOf_self X 0 x)

/-- The correspondence from seamed solutions to points evaluates at time `0`. -/
@[simp]
theorem seamedSolutionsEquiv_apply (f : M → M) (γ : seamedSolutions X f) :
    (seamedSolutionsEquiv hX hc f γ : M) = γ.val 0 :=
  (rfl)

/-- The seamed solution of a point where the time-one map agrees with the seam is its trajectory
under the flow. -/
@[simp]
theorem seamedSolutionsEquiv_symm_apply (f : M → M)
    (x : {x | timeDependentFlowOf X 0 1 x = f x}) (t : ℝ) :
    ((seamedSolutionsEquiv hX hc f).symm x).val t = timeDependentFlowOf X 0 t x :=
  (rfl)

variable [FiniteDimensional ℝ E]

/-- **The seamed path of a trajectory depends continuously on its start.** -/
theorem continuous_seamedSolutionPath_seamedSolutionsEquiv_symm (f : M → M) :
    Continuous fun x ↦ seamedSolutionPath ((seamedSolutionsEquiv hX hc f).symm x) := by
  refine continuous_induced_rng.2 <| ContinuousMap.continuous_of_continuous_uncurry _ ?_
  simp only [Function.comp_def, seamedSolutionPath_apply, seamedSolutionsEquiv_symm_apply,
    Function.uncurry_def]
  exact (contMDiff_timeDependentFlowOf hc le_rfl hX).continuous.comp (by fun_prop :
    Continuous fun p : {x | timeDependentFlowOf X 0 1 x = f x} × unitInterval ↦
      (((0 : ℝ), (p.2 : ℝ)), (p.1 : M)))

/-- **The seamed solutions in a path component start in a clopen set.** For a jointly `C¹`
time-dependent field with complete suspension on a manifold modelled on a finite-dimensional space,
and a continuous seam `f`, the starts of the seamed solutions whose seamed path lies in the path
component of a given `f`-seamed path `δ` form a clopen subset of the set where the time-one map
agrees with `f`. -/
theorem isClopen_setOf_seamedSolutionPath_mem_pathComponent (hf : Continuous f)
    (δ : SeamedPath f) :
    IsClopen {x : {x | timeDependentFlowOf X 0 1 x = f x} |
      seamedSolutionPath ((seamedSolutionsEquiv hX hc f).symm x) ∈ pathComponent δ} :=
  let _ : LocallyPathConnectedSpace M := I.locallyPathConnectedSpace_of_chartedSpace M
  let _ : SemilocallySimplyConnectedSpace M := I.semilocallySimplyConnectedSpace M
  (SeamedPath.isClopen_pathComponent hf δ).preimage
    (continuous_seamedSolutionPath_seamedSolutionsEquiv_symm hX hc f)

end Flow

section Compact

variable [CompactSpace M] [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M]
  (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
    (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
include hX

/-- **Finiteness of nondegenerate seamed solutions in a path component.** Let `X` be a jointly
`C¹` time-dependent vector field on a compact boundaryless manifold, `f` a homeomorphism and `δ` an
`f`-seamed path. If every seamed solution of `X` with seam `f` whose seamed path lies in the path
component of `δ` is nondegenerate, in the sense that its start is a nondegenerate fixed point of
`f⁻¹ ∘ timeDependentFlowOf X 0 1`, then there are only finitely many such seamed solutions. Seamed
solutions in other path components may be degenerate, and there may be infinitely many of them. -/
theorem finite_setOf_seamedSolutionPath_mem_pathComponent (f : M ≃ₜ M) (δ : SeamedPath f)
    (h : ∀ γ : seamedSolutions X f, seamedSolutionPath γ ∈ pathComponent δ →
      IsNondegenerateFixedPt I (f.symm ∘ timeDependentFlowOf X 0 1) (γ.val 0)) :
    {γ : seamedSolutions X f | seamedSolutionPath γ ∈ pathComponent δ}.Finite := by
  -- Without points there are no solutions; otherwise compactness forces `E` finite-dimensional.
  rcases isEmpty_or_nonempty M with hM | hM
  · have : IsEmpty (seamedSolutions X f) := ⟨fun γ ↦ hM.false (γ.val 0)⟩
    exact Set.toFinite _
  have := FiniteDimensional.of_locallyCompact_manifold M I
  have hc := isCompleteVectorField_timeDependentSuspensionField_of_compactSpace hX
  set e := seamedSolutionsEquiv hX hc f
  -- The starts of the solutions in the component form a closed subset of a closed set.
  set S := {x : {x | timeDependentFlowOf X 0 1 x = f x} |
    seamedSolutionPath (e.symm x) ∈ pathComponent δ}
  have hS : IsClosed (Subtype.val '' S) :=
    (isClosed_eq (continuous_timeDependentFlowOf hc le_rfl hX 0 1)
      f.continuous).isClosedMap_subtypeVal _
      (isClopen_setOf_seamedSolutionPath_mem_pathComponent hX hc f.continuous δ).isClosed
  -- They are nondegenerate fixed points of `f⁻¹ ∘ φ₁`, hence finitely many.
  have hfin := hS.isCompact.finite_of_isNondegenerateFixedPt (I := I) <| by
    rintro _ ⟨x, hx, rfl⟩
    simpa [e] using h (e.symm x) hx
  refine ((hfin.of_finite_image Subtype.val_injective.injOn).image e.symm).subset fun γ hγ ↦ ?_
  exact ⟨e γ, by simpa [S] using hγ, e.symm_apply_apply γ⟩

/-- **Finiteness of nondegenerate seamed solutions.** Let `X` be a jointly `C¹` time-dependent
vector field on a compact boundaryless manifold and `f` a homeomorphism. If every seamed solution
of `X` with seam `f` is nondegenerate, in the sense that its start is a nondegenerate fixed point
of `f⁻¹ ∘ timeDependentFlowOf X 0 1`, then there are only finitely many seamed solutions. -/
theorem finite_seamedSolutions (f : M ≃ₜ M)
    (h : ∀ γ ∈ seamedSolutions X f,
      IsNondegenerateFixedPt I (f.symm ∘ timeDependentFlowOf X 0 1) (γ 0)) :
    (seamedSolutions X f).Finite := by
  rcases isEmpty_or_nonempty M with hM | hM
  · have : IsEmpty (ℝ → M) := ⟨fun γ ↦ hM.false (γ 0)⟩
    exact Set.toFinite _
  have := FiniteDimensional.of_locallyCompact_manifold M I
  have hc := isCompleteVectorField_timeDependentSuspensionField_of_compactSpace hX
  set e := seamedSolutionsEquiv hX hc f
  -- The points where `φ₁ = f` are the fixed points of `f⁻¹ ∘ φ₁`, all nondegenerate.
  have hfix : {x | timeDependentFlowOf X 0 1 x = f x} = fixedPoints (f.symm ∘
      timeDependentFlowOf X 0 1) := by
    ext x
    simp [IsFixedPt, Homeomorph.symm_apply_eq]
  have hfin := finite_fixedPoints_of_isNondegenerateFixedPt (I := I)
    (f.symm.continuous.comp (continuous_timeDependentFlowOf hc le_rfl hX 0 1)) fun x hx ↦ by
      have hx' : x ∈ {x | timeDependentFlowOf X 0 1 x = f x} := hfix ▸ hx
      simpa [e] using h _ (e.symm ⟨x, hx'⟩).property
  have : Finite {x | timeDependentFlowOf X 0 1 x = f x} := (hfix ▸ hfin).to_subtype
  exact Set.finite_coe_iff.1 (Finite.of_equiv _ e.symm)

end Compact

end TauCeti
