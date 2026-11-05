/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Quotient
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm

/-!
# Symplectic forms on quotients by discrete groups

Let a group `G` act freely and properly discontinuously by smooth maps on a Hausdorff, locally
compact smooth manifold `M`. The orbit space `M ⧸ G` is then a smooth manifold and the orbit
projection `q : M → M ⧸ G` is a surjective smooth local diffeomorphism
(`TauCeti.isLocalDiffeomorph_quotientMk`). It is Hausdorff by Mathlib's
`t2Space_of_properlyDiscontinuousSMul_of_t2Space`, and second countable when `M` is, by
`ContinuousConstSMul.secondCountableTopology`.

If `G` acts by symplectomorphisms of a symplectic form `σ`, that is `g^* σ = σ` for every `g`, then
`σ` descends: the descent `TauCeti.SmoothForm.descend σ hσ` of
`TauCeti.Geometry.Manifold.DifferentialForm.Quotient` is the unique two-form `ω` on `M ⧸ G` with
`q^* ω = σ` (`TauCeti.SmoothForm.eq_descend_iff`). This file proves that `ω` is symplectic exactly
when `σ` is (`TauCeti.SmoothTwoForm.isSymplectic_descend_iff`). Closedness is
`TauCeti.SmoothForm.isClosed_descend_iff`; nondegeneracy holds because `q` is a surjective local
diffeomorphism, so its differentials identify the tangent spaces of `M` with those of `M ⧸ G`
(`IsLocalDiffeomorph.isNondegenerate_mpullback_iff`).

The same criterion is stated for an arbitrary surjective local diffeomorphism, such as a covering
map (`IsLocalDiffeomorph.isSymplectic_mpullback_iff`).

## Main results

* `TauCeti.SmoothTwoForm.isNondegenerate_descend_iff`,
  `TauCeti.SmoothTwoForm.isSymplectic_descend_iff`: the descent of an invariant two-form to the
  orbit space is nondegenerate, respectively symplectic, exactly when the form is.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 21 (quotients by discrete group actions) and
  Chapter 22 (symplectic manifolds).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 1.2 (symplectic manifolds) and Homework 1 (symplectic tori).
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section Quotient

variable {G : Type*} [Group G] [MulAction G M] [ProperlyDiscontinuousSMul G M]
  [ContinuousConstSMul G M] [IsCancelSMul G M] [T2Space M] [LocallyCompactSpace M]
  [ContMDiffConstSMul I ∞ G M] {σ : SmoothTwoForm I M}
  {hσ : ∀ g : G, SmoothForm.mpullback (g • ·) (contMDiff_const_smul g) σ = σ}

/-- The descent of a `G`-invariant two-form to the orbit space of `G` is nondegenerate exactly when
the form is. -/
@[simp]
theorem isNondegenerate_descend_iff :
    SmoothTwoForm.IsNondegenerate (SmoothForm.descend σ hσ) ↔ σ.IsNondegenerate := by
  rw [← isLocalDiffeomorph_quotientMk.isNondegenerate_mpullback_iff
    Quotient.mk_surjective, SmoothForm.mpullback_quotientMk_descend]

/-- **Symplectic quotients by discrete groups.** The descent of a two-form invariant under a free,
properly discontinuous group of diffeomorphisms is a symplectic form on the orbit space exactly
when the form is symplectic. -/
@[simp]
theorem isSymplectic_descend_iff :
    SmoothTwoForm.IsSymplectic (SmoothForm.descend σ hσ) ↔ σ.IsSymplectic := by
  rw [← isLocalDiffeomorph_quotientMk.isSymplectic_mpullback_iff
    Quotient.mk_surjective, SmoothForm.mpullback_quotientMk_descend]

end Quotient

end SmoothTwoForm

end TauCeti
