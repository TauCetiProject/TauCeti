/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import TauCeti.Analysis.Fredholm.LevelSet.Manifold

/-!
# The inclusion of a regular level set

Let `f : E → F` be a map between Banach spaces which, along the level set `{x | f x = c}`, is
strictly differentiable with surjective Fredholm derivative `D x` of constant index `n`.
`TauCeti.levelSetChartedSpace` makes the level set a charted space modelled on `Fin n → 𝕜`, and
`TauCeti.isManifold_levelSet` makes it a `C^m` manifold when `f` is `C^m` along the level set.

`TauCeti.hasMFDerivAt_coe_levelSet` computes the differential of the inclusion of the level set
into `E` for that atlas: at `z` it is the inclusion of `ker (D z)`, read in the model space through
`ContinuousLinearMap.kerModelEquiv`. This file deduces that the inclusion is an immersion, and that
its tangent space at `z` is `ker (D z)`. These are the facts needed to restrict functions on `E`
to the level set and to compare their differentials, for instance to pull back a function along
the inclusion and compute its critical points.

## Main results

* `TauCeti.injective_mfderiv_coe_levelSet` and `TauCeti.range_mfderiv_coe_levelSet`: the
  differential of the inclusion is injective, with range `ker (D z)`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd edition (2013), Corollary 5.14 and
  Proposition 5.38, for regular level sets and their tangent spaces.
-/

public section

namespace TauCeti

open Set
open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {f : E → F} {c : F} {D : E → E →L[𝕜] F} {n : ℕ}
  (hf : ∀ x ∈ {x | f x = c}, HasStrictFDerivAt f (D x) x)
  (hFred : ∀ x ∈ {x | f x = c}, ContinuousLinearMap.IsFredholm (D x))
  (hsurj : ∀ x ∈ {x | f x = c}, Function.Surjective (D x))
  (hindex : ∀ x ∈ {x | f x = c}, ContinuousLinearMap.index (D x) = n)

/-- The differential of the inclusion of a regular level set is injective: the inclusion is an
immersion. -/
theorem injective_mfderiv_coe_levelSet (z : ↥{x | f x = c}) :
    letI := levelSetChartedSpace hf hFred hsurj hindex
    Function.Injective
      (mfderiv 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, E) (Subtype.val : ↥{x | f x = c} → E) z) := by
  let _ := levelSetChartedSpace hf hFred hsurj hindex
  rw [(hasMFDerivAt_coe_levelSet hf hFred hsurj hindex z).mfderiv]
  exact Subtype.val_injective.comp (ContinuousLinearEquiv.injective _ :
    Function.Injective ((D z.1).kerModelEquiv (hFred z.1 z.2).finite_ker
      ((ContinuousLinearMap.finrank_ker_eq_iff_index_eq (D z.1) (hsurj z.1 z.2)).2
        (hindex z.1 z.2))).symm)

/-- **The tangent space of a regular level set is the kernel of the derivative.** The range of
the differential at `z` of the inclusion of a regular level set is `ker (D z)`. -/
theorem range_mfderiv_coe_levelSet (z : ↥{x | f x = c}) :
    letI := levelSetChartedSpace hf hFred hsurj hindex
    (mfderiv 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, E) (Subtype.val : ↥{x | f x = c} → E) z).range =
      (D z.1).ker := by
  let _ := levelSetChartedSpace hf hFred hsurj hindex
  set K := (D z.1).kerModelEquiv (hFred z.1 z.2).finite_ker
    ((ContinuousLinearMap.finrank_ker_eq_iff_index_eq (D z.1) (hsurj z.1 z.2)).2
      (hindex z.1 z.2))
  rw [(hasMFDerivAt_coe_levelSet hf hFred hsurj hindex z).mfderiv]
  exact (LinearMap.range_comp_of_range_eq_top (D z.1).ker.subtype
    K.symm.toLinearEquiv.range).trans (D z.1).ker.range_subtype

end TauCeti
