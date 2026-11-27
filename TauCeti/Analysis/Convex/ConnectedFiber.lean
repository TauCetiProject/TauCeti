/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.Topology.Order.IntermediateValue

/-!
# Convex images from connected fibres over hyperplanes

Let `f : X → V*` be a map from a topological space to the dual of a real vector space whose
components `x ↦ f x v` are continuous. This file gives Atiyah's criterion for the image of `f` to
be convex: it suffices that for every hyperplane `W = ker φ ⊆ V` (`φ ≠ 0`) and every `ν ∈ V*`, the
set of points `x` where `f x` agrees with `ν` on `W` is preconnected
(`TauCeti.convex_range_of_isPreconnected_setOf_forall_mem_ker`).

Indeed, for two values `a = f x` and `b = f y`, the points of the image agreeing with `a` on the
hyperplane `W = ker (b - a)` form the affine line through `a` and `b`. The set of `z` with `f z`
agreeing with `a` on `W` contains `x` and `y` and is preconnected, so by the intermediate value
theorem, applied to `z ↦ f z η` for some `η` with `(b - a) η ≠ 0`, the image contains every point
of the segment from `a` to `b`.

When `V` has dimension at most two, every hyperplane of `V` is spanned by one vector `ξ`, and the
condition reads: every level set `{x | f x ξ = c}` of a component of `f` is preconnected
(`TauCeti.convex_range_of_isPreconnected_setOf_apply_eq`). For moment maps of Hamiltonian torus
actions this is how Atiyah deduces convexity of the image from the connectedness of the fibres of
the moment maps of subtori of codimension one.

## Main results

* `TauCeti.convex_range_of_isPreconnected_setOf_forall_mem_ker`: Atiyah's criterion.
* `TauCeti.convex_range_of_isPreconnected_setOf_apply_eq`: in dimension at most two, connected
  levels of the components give a convex image.

## References

* M. F. Atiyah, *Convexity and commuting Hamiltonians*, Bull. London Math. Soc. 14 (1982), 1–15,
  § 2 (the deduction of convexity from connected fibres of the moment maps of subtori).
-/

public section

open Set

namespace TauCeti

variable {X V : Type*} [TopologicalSpace X] [AddCommGroup V] [Module ℝ V]
  {f : X → Module.Dual ℝ V}

/-- **Atiyah's convexity criterion.** Let `f : X → V*` have continuous components
`x ↦ f x v`. If, for every nonzero `φ ∈ V*` and every `ν ∈ V*`, the set of points `x` at which
`f x` agrees with `ν` on the hyperplane `ker φ` is preconnected, then the image of `f` is
convex. -/
theorem convex_range_of_isPreconnected_setOf_forall_mem_ker (hf : ∀ v, Continuous fun x ↦ f x v)
    (h : ∀ φ : Module.Dual ℝ V, φ ≠ 0 → ∀ ν : Module.Dual ℝ V,
      IsPreconnected {x | ∀ v ∈ LinearMap.ker φ, f x v = ν v}) :
    Convex ℝ (range f) := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ s t hs ht hst
  by_cases hxy : f y = f x
  · exact ⟨x, by rw [hxy, ← add_smul, hst, one_smul]⟩
  -- Pick `η` with `(f y - f x) η ≠ 0`; the hyperplane is `W = ker (f y - f x)`.
  obtain ⟨η, hη⟩ : ∃ η, (f y - f x) η ≠ 0 := by
    by_contra! H
    exact hxy (sub_eq_zero.1 (LinearMap.ext H))
  have hF := h (f y - f x) (sub_ne_zero.2 hxy) (f x)
  -- Both `x` and `y` lie in the set where `f` agrees with `f x` on `W`.
  have hxF : x ∈ {z | ∀ v ∈ LinearMap.ker (f y - f x), f z v = f x v} := fun _ _ ↦ rfl
  have hyF : y ∈ {z | ∀ v ∈ LinearMap.ker (f y - f x), f z v = f x v} := fun v hv ↦
    sub_eq_zero.1 hv
  -- The intermediate value theorem for `z ↦ f z η` on that preconnected set.
  have hmem : s * f x η + t * f y η ∈ uIcc (f x η) (f y η) := by
    rw [← segment_eq_uIcc]
    exact ⟨s, t, hs, ht, hst, rfl⟩
  obtain ⟨z, hz, hzη⟩ :=
    ((hF.image _ (hf η).continuousOn).ordConnected).uIcc_subset ⟨x, hxF, rfl⟩ ⟨y, hyF, rfl⟩ hmem
  refine ⟨z, LinearMap.ext fun v ↦ ?_⟩
  -- Decompose `v = w + c η` with `w ∈ W`, and compare both sides on `w` and on `η`.
  set c := (f y - f x) v / (f y - f x) η
  have hw : (f y - f x) (v - c • η) = 0 := by
    simp only [map_sub, map_smul, smul_eq_mul, c]
    field_simp
    ring
  have h₁ := hz (v - c • η) hw
  have h₂ := sub_eq_zero.1 hw
  simp only [map_sub, map_smul, smul_eq_mul] at h₁ h₂ hzη
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  linear_combination h₁ + c * hzη - t * h₂ - (f x v - c * f x η) * hst

/-- **Convexity from connected component levels, in dimension at most two.** Let `V` be a real
vector space of dimension at most two and let `f : X → V*` have continuous components. If every
level set `{x | f x ξ = c}` of every component of `f` is preconnected, then the image of `f` is
convex. -/
theorem convex_range_of_isPreconnected_setOf_apply_eq [FiniteDimensional ℝ V]
    (hV : Module.finrank ℝ V ≤ 2) (hf : ∀ v, Continuous fun x ↦ f x v)
    (h : ∀ ξ c, IsPreconnected {x | f x ξ = c}) :
    Convex ℝ (range f) := by
  refine convex_range_of_isPreconnected_setOf_forall_mem_ker hf fun φ hφ ν ↦ ?_
  -- A hyperplane of `V` has dimension at most one, so it is spanned by one vector `ξ`.
  have hker : Module.finrank ℝ (LinearMap.ker φ) ≤ 1 := by
    have := Module.Dual.finrank_ker_add_one_of_ne_zero hφ
    omega
  obtain ⟨ξ, hξ⟩ := ((LinearMap.ker φ).finrank_le_one_iff_isPrincipal.1 hker).principal
  convert h ξ (ν ξ) using 1
  ext x
  simp only [hξ, mem_ofPred_eq, Submodule.mem_span_singleton, forall_exists_index,
    forall_apply_eq_imp_iff, map_smul, smul_eq_mul]
  exact ⟨fun H ↦ by simpa using H 1, fun H a ↦ by rw [H]⟩

end TauCeti
