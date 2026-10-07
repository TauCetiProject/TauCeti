/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Resolvent.Unbounded
public import TauCeti.LinearAlgebra.LinearPMap.RestrictScalars

/-!
# Resolvents and restriction of scalars

An unbounded operator `A : X →ₗ.[𝕜'] X` over a normed field extension `𝕜'` can also be read over a
smaller field `𝕜`, as `A.restrictScalars 𝕜`. This file shows that the two resolvent notions
agree at the points of `𝕜`: for `mu : 𝕜`,

`mu ∈ resolventSet (A.restrictScalars 𝕜) ↔ algebraMap 𝕜 𝕜' mu ∈ resolventSet A`,

and the resolvents themselves correspond under `ContinuousLinearMap.restrictScalars`.
The actions on `X` form a scalar tower; no norm compatibility between the two fields is required.

Only the forward direction has content. A bounded `𝕜`-linear inverse `R` of `mu • I - A` is
automatically `𝕜'`-homogeneous: `z • R y` and `R (z • y)` have the same image under
`mu • I - A`, because `A` is `𝕜'`-linear, so they agree. This homogeneity statement also works
over an arbitrary ring algebra, without a norm or topology on the larger algebra.

This is what lets a real-variable theorem about an operator on a complex Banach space — such as
the Laplace-transform resolvent of a C₀-semigroup, which is built over `ℝ` — be read as a
statement about the genuinely complex resolvent set.

## Main results

* `TauCeti.LinearPMap.IsResolventAt.restrictScalars`: restricting scalars in an inverse of
  `lambda • I - A`.
* `TauCeti.LinearPMap.map_smul_of_isResolventAt_restrictScalars`: a bounded inverse over `𝕜` is
  `𝕜'`-homogeneous.
* `TauCeti.LinearPMap.exists_isResolventAt_of_isResolventAt_restrictScalars`: it therefore comes
  from an inverse over `𝕜'`.
* `TauCeti.LinearPMap.mem_resolventSet_restrictScalars_iff`: the resolvent sets agree at the
  points of `𝕜`.
* `TauCeti.LinearPMap.restrictScalars_resolvent`: the resolvents agree there.
-/

public section

noncomputable section

namespace TauCeti.LinearPMap

section Algebra

variable {𝕜 𝕜' X : Type*} [NontriviallyNormedField 𝕜] [Ring 𝕜'] [Algebra 𝕜 𝕜']
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [Module 𝕜' X] [IsScalarTower 𝕜 𝕜' X]
  {A : X →ₗ.[𝕜'] X} {mu : 𝕜} {R₀ : X →L[𝕜] X}

/-- A bounded `𝕜`-linear inverse of `mu • I - A` respects the action of the larger algebra
`𝕜'`. No norm or topology on `𝕜'` is needed. -/
theorem map_smul_of_isResolventAt_restrictScalars
    (h : IsResolventAt (A.restrictScalars 𝕜) mu R₀) (z : 𝕜') (y : X) :
    R₀ (z • y) = z • R₀ y := by
  obtain ⟨hgraph, hleft⟩ := isResolventAt_iff_forall_mem_graph.mp h
  rw [LinearPMap.restrictScalars_graph] at hgraph hleft
  simp only [Submodule.restrictScalars_mem] at hgraph hleft
  have hz : (z • R₀ y, z • (mu • R₀ y - y)) ∈ A.graph := by
    simpa only [Prod.smul_mk] using A.graph.smul_mem z (hgraph y)
  simpa only [smul_sub, smul_comm mu z, sub_sub_cancel] using hleft _ hz

end Algebra

variable {𝕜 𝕜' X : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [Algebra 𝕜 𝕜'] [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedSpace 𝕜' X]
  [IsScalarTower 𝕜 𝕜' X] {A : X →ₗ.[𝕜'] X} {mu : 𝕜} {R : X →L[𝕜'] X} {R₀ : X →L[𝕜] X}

/-- An inverse of `algebraMap 𝕜 𝕜' mu • I - A` restricts to an inverse of `mu • I - A` for the
restriction of scalars. -/
theorem IsResolventAt.restrictScalars (h : IsResolventAt A (algebraMap 𝕜 𝕜' mu) R) :
    IsResolventAt (A.restrictScalars 𝕜) mu (R.restrictScalars 𝕜) := by
  simpa only [isResolventAt_iff_forall_mem_graph, ContinuousLinearMap.coe_restrictScalars',
    LinearPMap.restrictScalars_graph, Submodule.restrictScalars_mem, algebraMap_smul 𝕜'] using h

/-- A bounded inverse of `mu • I - A` over the smaller field is the restriction of scalars of a
bounded inverse over the larger one. -/
theorem exists_isResolventAt_of_isResolventAt_restrictScalars
    (h : IsResolventAt (A.restrictScalars 𝕜) mu R₀) :
    ∃ R : X →L[𝕜'] X, R.restrictScalars 𝕜 = R₀ ∧
      IsResolventAt A (algebraMap 𝕜 𝕜' mu) R := by
  refine ⟨{ toFun := R₀
            map_add' := R₀.map_add
            map_smul' := map_smul_of_isResolventAt_restrictScalars h
            cont := R₀.continuous }, ContinuousLinearMap.ext fun _ => rfl, ?_⟩
  simpa only [isResolventAt_iff_forall_mem_graph, LinearPMap.restrictScalars_graph,
    Submodule.restrictScalars_mem, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
    AddHom.coe_mk, algebraMap_smul 𝕜'] using h

/-- The resolvent sets of an operator and of its restriction of scalars agree at the points of the
smaller field. -/
@[simp]
theorem mem_resolventSet_restrictScalars_iff :
    mu ∈ resolventSet (A.restrictScalars 𝕜) ↔ algebraMap 𝕜 𝕜' mu ∈ resolventSet A := by
  rw [mem_resolventSet_iff, mem_resolventSet_iff]
  constructor
  · rintro ⟨R₀, hR₀⟩
    obtain ⟨R, -, hR⟩ := exists_isResolventAt_of_isResolventAt_restrictScalars hR₀
    exact ⟨R, hR⟩
  · rintro ⟨R, hR⟩
    exact ⟨R.restrictScalars 𝕜, hR.restrictScalars⟩

/-- The resolvent of the restriction of scalars is the restriction of scalars of the resolvent. -/
@[simp]
theorem restrictScalars_resolvent (h : mu ∈ resolventSet (A.restrictScalars 𝕜)) :
    (resolvent A (algebraMap 𝕜 𝕜' mu)).restrictScalars 𝕜 = resolvent (A.restrictScalars 𝕜) mu :=
  (resolvent_eq_of_isResolventAt
    (IsResolventAt.restrictScalars
      (isResolventAt_resolvent (mem_resolventSet_restrictScalars_iff.mp h)))).symm

end TauCeti.LinearPMap

end
