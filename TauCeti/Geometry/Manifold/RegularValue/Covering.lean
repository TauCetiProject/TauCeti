/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import TauCeti.Geometry.Manifold.RegularValue.Fibre
public import TauCeti.Geometry.Manifold.RegularValue.Open
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Covering
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Smooth sheets over regular values

A proper `C^n` map, `1 ≤ n`, between finite-dimensional manifolds of the same dimension is a
finite covering over its regular values, provided its source has no boundary. Near an attained
regular value, one can choose a single trivialization whose inverse branches all have the
regularity of the map. The sheets are labeled by the finite fibre over that value, and the
trivialization can be chosen to contain only regular values in its base set.

These are the local sheets used to compare integrals of pulled-back top forms with signed
counts of fibres. Properness prevents additional sheets from entering near the chosen value;
invertibility of the differentials gives the smooth inverse branches. No compactness of the
whole source, surjectivity, orientation, or connectedness is assumed. Values outside the image
are evenly covered with empty fibre; a nonempty fibre is needed only to totalize a trivialization.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 17, Degree Theory.
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, §1, regular values and inverse
  branches.
-/

public section

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜]
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [FiniteDimensional 𝕜 E']
  [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]
  {f : M → N} {x : M} {y : N}

/-- At an interior regular point, a `C^n` map between finite-dimensional manifolds of equal
dimension is a `C^n` local diffeomorphism, provided `1 ≤ n`. -/
theorem IsRegularPoint.isLocalDiffeomorphAt
    (hx : IsRegularPoint I J f x) (hdim : Module.finrank 𝕜 E = Module.finrank 𝕜 E')
    (hf : ContMDiff I J n f) (hn : 1 ≤ n) (hIx : I.IsInteriorPoint x) :
    IsLocalDiffeomorphAt I J n f x := by
  let := FiniteDimensional.complete 𝕜 E
  obtain ⟨e, he⟩ := (isRegularPoint_iff_isInvertible_mfderiv hdim).mp hx
  exact isLocalDiffeomorphAt_of_mfderiv_eq hf.contMDiffOn isOpen_univ (mem_univ _)
    hIx hn he

variable [T2Space M] [BoundarylessManifold I M]

/-- A proper `C^n` map between finite-dimensional manifolds of equal dimension covers its
regular values. The covering need not be surjective: values outside the image have empty fibre.
The source is boundaryless; the target may have boundary or corners. -/
theorem isCoveringMapOn_setOf_isRegularValue
    (hdim : Module.finrank 𝕜 E = Module.finrank 𝕜 E') (hf : ContMDiff I J n f) (hn : 1 ≤ n)
    (hp : IsProperMap f) : IsCoveringMapOn f {y | IsRegularValue I J f y} := by
  have hn0 : n ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hn)
  refine hp.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
    (fun _ hy ↦ hy.finite_preimage_of_isProperMap hdim hf hn0 hp) ?_
  have hloc : IsLocalDiffeomorphOn I J n f (f ⁻¹' {y | IsRegularValue I J f y}) :=
    fun x ↦ (x.2.isRegularPoint rfl).isLocalDiffeomorphAt hdim hf hn
      BoundarylessManifold.isInteriorPoint
  exact hloc.isLocalHomeomorphOn

/-- Near an attained regular value of a proper `C^n` map, all sheets are `C^n` on one common
neighbourhood consisting of regular values. The sheets are labeled by their values in the finite
fibre at the centre. -/
theorem IsRegularValue.exists_trivialization_contMDiffOn_symm
    (hy : IsRegularValue I J f y) (hdim : Module.finrank 𝕜 E = Module.finrank 𝕜 E')
    (hf : ContMDiff I J n f) (hn : 1 ≤ n) (hp : IsProperMap f) (hyf : y ∈ range f) :
    ∃ t : Bundle.Trivialization (f ⁻¹' {y}) f,
      y ∈ t.baseSet ∧ t.baseSet ⊆ {z | IsRegularValue I J f z} ∧
      (∀ a : f ⁻¹' {y}, t.toOpenPartialHomeomorph.symm (y, a) = a) ∧
      ∀ a : f ⁻¹' {y},
        ContMDiffOn J I n (fun z ↦ t.toOpenPartialHomeomorph.symm (z, a)) t.baseSet := by
  classical
  have : IsManifold I 1 M := IsManifold.of_le hn
  have : IsManifold J 1 N := IsManifold.of_le hn
  have : Nonempty (f ⁻¹' {y}) := by
    obtain ⟨x, hx⟩ := hyf
    exact ⟨⟨x, hx⟩⟩
  let h := isCoveringMapOn_setOf_isRegularValue hdim hf hn hp y hy
  let t := h.toTrivialization.restrOpen {z | IsRegularValue I J f z}
    (isOpen_setOf_isRegularValue_of_isClosedMap hf hn hp.isClosedMap)
  have hyt : y ∈ t.baseSet := ⟨h.mem_toTrivialization_baseSet, hy⟩
  refine ⟨t, hyt, inter_subset_right, ?_, fun a ↦ t.contMDiffOn_symm_prodMk_left ?_ a⟩
  · rintro ⟨a, ha⟩
    have ha : f a = y := ha
    subst y
    -- Restricting the base set leaves the forward and inverse functions unchanged.
    have hlabel : (t a).2 = ⟨a, rfl⟩ := h.toTrivialization_apply
    simpa only [hlabel] using t.symm_apply_mk_proj (t.mem_source.mpr hyt)
  · intro x
    have hx : IsRegularValue I J f (f x) := (t.mem_source.mp x.2).2
    exact (hx.isRegularPoint rfl).isLocalDiffeomorphAt hdim hf hn
      BoundarylessManifold.isInteriorPoint

end TauCeti
