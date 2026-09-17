/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Pseudo-inverses of linear maps of vector spaces

A **pseudo-inverse** of a linear map `f` is a linear map `g` in the opposite direction with
`f ∘ g ∘ f = f`. Every linear map of vector spaces has one: the range of `f` is a projective
module, so the corestriction of `f` to its range splits, and a section of it extends to the whole
target.

A pseudo-inverse concretely splits the exact sequence from `ker f` through the range of `f`:
`1 - g ∘ f` takes values in `ker f` and fixes it. Additive functors preserve split exact
sequences; in particular, extension of scalars carries this splitting along.
-/

public section

namespace TauCeti

/-- **Every linear map of vector spaces has a pseudo-inverse**: a linear map `g` in the opposite
direction with `f ∘ g ∘ f = f`. -/
theorem _root_.LinearMap.exists_comp_comp_eq_self {K V V' : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V'] (f : V →ₗ[K] V') :
    ∃ g : V' →ₗ[K] V, f ∘ₗ g ∘ₗ f = f := by
  obtain ⟨s, hs⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  obtain ⟨g, hg⟩ := s.exists_extend
  refine ⟨g, LinearMap.ext fun x ↦ ?_⟩
  have hgx : g (f x) = s (f.rangeRestrict x) := by
    simpa using LinearMap.congr_fun hg (f.rangeRestrict x)
  have hsx : f (s (f.rangeRestrict x)) = f x := by
    simpa using congrArg Subtype.val (LinearMap.congr_fun hs (f.rangeRestrict x))
  simpa only [LinearMap.comp_apply, hgx] using hsx

end TauCeti
